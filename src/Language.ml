(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
open List
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let undefined x = failwith (Printf.sprintf "Variable %s is undefined" x)
    let empty = {g = undefined; l = undefined; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = 
      let update' x v sf = fun q -> if q = x then v else sf q in 
      if mem x s.scope then {g = s.g; l = update' x v s.l; scope = s.scope} else {g = update' x v s.g; l = s.l; scope = s.scope}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if mem x s.scope then s.l x else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {g = st.g; l = undefined; scope = xs}

    (* Drops a scope *)
    let leave st st' = {g = st.g; l = st'.l; scope = st'.scope}

  end
    
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
      | Var name -> State.eval state name
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
      parse:
        !(Ostap.Util.expr identity
           (Array.map (fun (a, s) -> a, 
                             List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                          ) 
                [|                
                    `Lefta, ["!!"];
                    `Lefta, ["&&"];
                    `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
                    `Lefta, ["+" ; "-"];
                    `Lefta, ["*" ; "/"; "%"];
                |] 
           )
           primary);
        
        primary:
          n:DECIMAL {Const n}
        | x:IDENT   {Var x}
        | -"(" parse -")"
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
     let rec eval env ((state, i, o) as conf) statement =
      match statement with
        | Read    x           -> (match i with z::i' -> (State.update x z state, i', o) | _ -> failwith "Expected symbol, but end of input found")
        | Write   e           -> (state, i, o @ [Expr.eval state e])
        | Assign (x, e)       -> (State.update x (Expr.eval state e) state, i, o)
        | Seq    (s1, s2)     -> eval env (eval env conf s1) s2
        | Skip                -> conf 
        | If (cond, t, e)     -> eval env conf (if (Expr.eval state cond) <> 0 then t else e)
        | While (cond, body)  -> (if (Expr.eval state cond) = 0 then conf else eval env (eval env conf body) statement)
        | Repeat (body, cond) -> 
          let (state', i, o)  = eval env conf statement in 
            if (Expr.eval state cond) = 0 then eval env (state', i, o) statement else (state', i, o)
        | Call (f, args) -> 
          let params, locals, body = env#definition f in
          let evaluatedArgs = combine params (map (Expr.eval state) args) in 
          let initState = State.enter state (params @ locals) in 
          let state = fold_left (fun state' (x, v) -> State.update x v state') initState evaluatedArgs in
          let resST, resI, resO = eval env (state, i, o) body in
          (State.leave resST state, resI, resO)
                          

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
      | %"repeat" body:parse %"until" cond: !(Expr.parse)    { Repeat (body, cond) }
      | %"for" init:parse "," cond:!(Expr.parse) "," inc:parse %"do" body:parse %"od" { Seq (init, While (cond, Seq (body, inc))) }
    )
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg: IDENT;
      parse: %"fun" name:IDENT "(" args: !(Util.list0 arg) ")"
        locals: (%"local" !(Util.list arg))?
        "{" body: !(Stmt.parse) "}" 
        { (name, (args, (match locals with None -> [] | Some l -> l), body))}    
    )
  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = 
  let module FMap = Map.Make(String) in
  let definitions = fold_left (fun m ((name, _) as def) -> FMap.add name def m) FMap.empty defs in
  let env = (object method definition name = snd (FMap.find name definitions) end) in
  let _, _, output = Stmt.eval env (State.empty, i, []) body
  in output
                                   
(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
