(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open List

(* Opening a library for combinator-based syntax analysis *)
open Ostap
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

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let toBool value = value <> 0;;
    let toInt value = if value then 1 else 0;;

    let rec eval state expression = match expression with
      | Const value -> value
      | Var name -> state name
      | Binop(operation, left, right) ->
        let x = eval state left in
        let y = eval state right in
        match operation with
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

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    let identity x = x
    let make_operation operation = (ostap ($(operation)), fun x y -> Binop (operation, x, y))

    ostap (
      parse: expression;
      expression:
        !(Util.expr identity
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
   let rec eval (s, i, o) expression = match expression with
     | Read x           -> let (h :: rest) = i in (Expr.update x h s, rest, o)
     | Write e          -> (s, i, o @ [(Expr.eval s e)])
     | Assign (x, expr) -> (Expr.update x (Expr.eval s expr) s, i, o)
     | Seq (s_, t_)     -> eval (eval (s, i, o) s_) t_
     | _                -> failwith (Printf.sprintf "Unsupported expression")

    (* Statement parser *)
    ostap (
      parse: statements;
      statements: <s1::s2> : !(Util.listBy)[ostap (";")][stmt] {List.fold_left (fun x y -> Seq (x, y)) s1 s2};
      stmt:
          x:IDENT ":=" e:!(Expr.parse) {Assign (x, e)}
        | "write" "(" e:!(Expr.parse) ")" {Write e}
        | "read" "(" x:IDENT ")" {Read x}
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
