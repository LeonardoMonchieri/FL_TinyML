(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

//Active pattern for Litterals evaluation

//VInt
let (|VInt|_|) =
    function
    | VLit(LInt i) -> Some i
    | _ -> None

let VInt x = VLit(LInt x)

//VFloat
let (|VFloat|_|) =
    function
    | VLit(LFloat f) -> Some f
    | _ -> None

let VFloat x = VLit(LFloat x)

//VBool 
let (|VBool|_|) =
    function
    | VLit(LBool b) -> Some b
    | _ -> None

let VBool x = VLit(LBool x)

//Evaluation rules
let rec eval_expr (env: value env) (e: expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x ->
        let _, v = List.find (fun (y, _) -> x = y) env
        v

    | Lambda(x, _, e) -> Closure(env, x, e)

    | App(e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2

        match v1 with
        | Closure(env1, x, e) -> eval_expr ((x, v2) :: env1) e
        | RecClosure(env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
    //Added Tuple evaluation
    | Tuple tv ->
        VTuple <| List.map(eval_expr env) tv

    | IfThenElse(e1, e2, None) ->
        let v1 = eval_expr env e1

        match v1 with
        | VLit(LBool true) -> eval_expr env e2
        | VLit(LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)


    | IfThenElse(e1, e2, Some e3) ->
        let v1 = eval_expr env e1

        eval_expr
            env
            (match v1 with
             | VLit(LBool true) -> e2
             | VLit(LBool false) -> e3
             | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1))

    | Let(x, _, e1, e2) ->
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    // TODO: test this is ok or fix it
    | LetRec(f, _, e1, e2) ->
        let v1 = eval_expr env e1
      
        match v1 with
        //Keep find the closure
        | Closure(venv1, x, e) -> 
            let rec_clsr = RecClosure(venv1, f, x, e)
            eval_expr ((f, rec_clsr) :: env) e2
        //Find the final evaluation of
        | v->v 
        | _-> unexpected_error "eval_expr: can't reach the closure in rec binding: %s" (pretty_value v1)
   
    // TODO finish this implementation
    //CHECKED
    | BinOp(e1, op, e2) ->
        match op with
        | "+" -> aritm_binop (+) (+) "+" env e1 e2
        | "-" -> aritm_binop (-) (-) "-" env e1 e2
        | "*" -> aritm_binop ( * ) ( * ) "*" env e1 e2
        // TODO: implement other binary ops
        | "/" -> aritm_binop (/) (/) "/" env e1 e2
        | "%" -> aritm_binop (%) (%) "/" env e1 e2
        //Comparing operator
        | ">" -> comp_binop (>) ">" env e1 e2
        | ">=" -> comp_binop (>=) "<=" env e1 e2
        | "=" -> comp_binop (=) "==" env e1 e2
        | "<=" -> comp_binop (<=) "<=" env e1 e2
        | "<" -> comp_binop (<) "<" env e1 e2
        | "<>" -> comp_binop (<>) "<>" env e1 e2
        //Boolean operator
        | "and" -> bool_binop (&&) "and" env e1 e2
        | "or" -> bool_binop (||) "or" env e1 e2
        | any -> unexpected_error "eval_expr: unsupported operator: %s" op
    //ADD UNIOP
    | UnOp(op, e) ->
        let v = eval_expr env e

        match op with
        | "not" ->
            match v with
            | VBool b -> VBool(not b)
            | _ -> unexpected_error "eval_expre: unsoppreted expression: not %s" (pretty_value v)
        | "-" ->
            match v with
            | VInt i -> VInt(-i)
            | VFloat f -> VFloat(-f)
            | _ -> unexpected_error "eval_expre: unsoppreted expression: -%s" (pretty_value v)
        | _ -> unexpected_error "eval_expre: illegal operands in unary operator: %s %s" op (pretty_expr e)
    | any -> unexpected_error "eval_expre: illegal expression %s [AST: %A]" (pretty_expr e) e



//Arithmetic operators( +, -, /, *, %)
and aritm_binop op_int op_float str_op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2

    match v1, v2 with
    | VInt x, VInt y -> VInt(op_int x y)
    | VFloat x, VFloat y -> VFloat(op_float x y)
    | VInt x, VFloat y -> VFloat(op_float (float x) y)
    | VFloat x, VInt y -> VFloat(op_float x (float y))
    | _ ->
        unexpected_error
            "eval_expr: illegal operands in binary operator: %s %s %s"
            (pretty_value v1)
            str_op
            (pretty_value v2)

//Comparing operators ( <, <=, =, >=, >, <> )
and comp_binop op str_op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2

    match v1, v2 with
    | VInt x, VInt y -> VBool(op x y)
    | _ ->
        unexpected_error
            "eval_expr: illegal operands in binary comparison operator: %s %s %s"
            (pretty_value v1)
            str_op
            (pretty_value v2)


//Boolean operators ( and, or )
and bool_binop op_bool str_op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2

    match v1, v2 with
    | VBool x, VBool y -> VBool(op_bool x y)
    | _ ->
        unexpected_error
            "eval_expr: illegal operands in binary operator: %s %s %s"
            (pretty_value v1)
            ("add op")
            (pretty_value v2)



