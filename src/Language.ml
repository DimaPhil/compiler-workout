(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let toBool value = value <> 0;;
    let toInt value = if value then 1 else 0;;

    let calculateExpression operation x y = match operation with
      | "!!" -> toInt (toBool x || toBool y)
      | "&&" -> toInt (toBool x && toBool y)
      | "==" -> toInt (x == y)
      | "!=" -> toInt (x <> y)
      | "<=" -> toInt (x <= y)
      | "<"  -> toInt (x < y)
      | ">=" -> toInt (x >= y)
      | ">"  -> toInt (x > y)
      | "+"  -> x + y
      | "-"  -> x - y
      | "*"  -> x * y
      | "/"  -> x / y
      | "%"  -> x mod y
      | _    -> failwith (Printf.sprintf "Unsupported binary operator %s" operation);;

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let rec eval state expression = match expression with
      | Const value -> value
      | Var name -> state name
      | Binop(operation, left, right) ->
        let x = eval state left in
        let y = eval state right in
        calculateExpression operation x y    

    let identity x = x
    let make_operation operation = (ostap ($(operation)), fun x y -> Binop (operation, x, y))

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (
      parse: expression;
      expression:
        !(Ostap.Util.expr identity
          [|
            `Lefta, [make_operation "!!"];
            `Lefta, [make_operation "&&"];
            `Nona,  [make_operation "<="; make_operation ">="; make_operation "<"; make_operation ">"; make_operation "=="; make_operation "!="];
            `Lefta, [make_operation "+"; make_operation "-"];
            `Lefta, [make_operation "*"; make_operation "/"; make_operation "%"]
          |]
          operations
        );
      operations: x:IDENT {Var x} | n:DECIMAL {Const n} | -"(" expression -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Until of t * Expr.t with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((st, i, o) as conf) stmt = match stmt with
      | Read    x       -> (match i with z::i' -> (Expr.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write   e       -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (Expr.update x (Expr.eval st e) st, i, o)
      | Seq    (s1, s2) -> eval (eval conf s1) s2
      | Skip            -> conf 
      | If (cond, t, e) -> eval conf (if (Expr.eval st cond) <> 0 then t else e)
      | While (cond, body) -> (if (Expr.eval st cond) = 0 then conf else eval (eval conf body) stmt)
      | Until (body, cond) -> 
        let (st, i, o)  = eval conf stmt in 
          if (Expr.eval st cond) = 0 then eval (st, i, o) stmt else (st, i, o)
                          
    let rec parseElifs elifs els =  match elifs with
      | [] -> els
      | (cond, body)::elifs' -> If (cond, body, parseElifs elifs' els)
                               
    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        %"read" "(" x:IDENT ")"          {Read x}
      | %"write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
      | %"skip" {Skip}
      | %"if" cond:!(Expr.parse) %"then" th:parse 
        elif:(%"elif" !(Expr.parse) %"then" parse)*
        els:(%"else" parse)?
        %"fi" { 
        If (
            cond,
            th, 
            match els with
              | None -> parseElifs elif Skip
              | Some body -> parseElifs elif body
          )}
      | %"while" cond: !(Expr.parse) %"do" body:parse %"od"  { While (cond, body) }
      | %"repeat" body:parse %"until" cond: !(Expr.parse)    { Until (body, cond) }
      | %"for" init:parse "," cond:!(Expr.parse) "," inc:parse %"do" body:parse %"od" { Seq (init, While (cond, Seq (body, inc))) } 
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
