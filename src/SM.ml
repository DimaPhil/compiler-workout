open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env ((stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: prg' ->
       (match insn wsith
          | BINOP op -> let y::x::stack' = stack in eval env (Expr.calculateExpression operation x y :: stack', c) prg'
          | READ     -> let z::i' = i     in eval env (z::stack, (st, i', o)) prg'
          | WRITE    -> let z::stack' = stack in eval env (stack', (st, i, o @ [z])) prg'
          | CONST i  -> eval env (i::stack, c) prg'
          | LD x     -> eval env (st x :: stack, c) prg'
          | ST x     -> let z::stack' = stack in eval env (stack', (Expr.update x z st, i, o)) prg'
          | LABEL s  -> eval env conf prg'
          | JMP name -> eval env conf (env#labeled name)
          | CJMP (cond, name) -> let x::stack' = stack in eval env (stack', c) (if ( (if cond = "nz" then x <> 0 else x = 0)) then (env#labeled name) else prg')
       )

class labels = 
  object (self)
    val counter = 0
    method new_label = "label_" ^ string_of_int counter, {<counter = counter + 1>}
  end

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

let rec compile' labels =
  let rec expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
   function
    | Stmt.Seq (s1, s2)  -> 
        let labels1, res1 = compile' labels s1 in
        let labels2, res2 = compile' labels1 s2 in
        labels2, res1 @ res2
    | Stmt.Read x        -> labels, [READ; ST x]
    | Stmt.Write e       -> labels, expr e @ [WRITE]
    | Stmt.Assign (x, e) -> labels, expr e @ [ST x]
    | Stmt.Skip          -> labels, []
    | Stmt.If (cond, body, els) ->
        let cond' = expr cond in
        let jumpElse, labels1 = labels#new_label in
        let jumpEndIf, labels2 = labels1#new_label in
        let labels3, body' = compile' labels2 body in
        let labels4, els' = compile' labels3 els in
        labels4, cond' @ [CJMP ("z", jumpElse)] @ body' @ [JMP jumpEndIf] @ [LABEL jumpElse] @ els' @ [LABEL jumpEndIf]
    | Stmt.While (cond, body) ->
        let cond' = expr cond in
        let labelBegin, labels1 = labels#new_label in
        let labelEnd, labels2 = labels1#new_label in
        let labels3, body' = compile' labels2 body in
        labels3, [LABEL labelBegin] @ cond' @ [CJMP ("z", labelEnd)] @ body' @ [JMP labelBegin] @ [LABEL labelEnd] 
    | Stmt.Until (body, cond) ->
        let cond' = expr cond in
        let labelBegin, labels1 = labels#new_label in
        let labels2, body' = compile' labels1 body in
        labels2, [LABEL labelBegin] @ body' @ cond' @ [CJMP ("z", labelBegin)]

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile program = let resLabels, result = compile' (new labels) program in result