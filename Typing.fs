(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt
let type_infer_error fmt = throw_formatted TypeInferError fmt
let unfy_error fmt = throw_formatted UnifyError fmt
let sub_error fmt = throw_formatted SubstitutionError fmt

//θ
type subst = (tyvar * ty) list

// TODO implement this 
// CHECKED

let rec apply_subst (t : ty) (s : subst) : ty =         // θ(τ) -> τ'
    match t with
    | TyName _ -> t
    | TyArrow (t1, t2) -> TyArrow(apply_subst t1 s, apply_subst t2 s)
    | TyVar tv ->
        try
            let _,sub_t = s|>List.find(fun(x,_)->x = tv) 
            sub_t
        with
            | :? System.Collections.Generic.KeyNotFoundException -> t
    | TyTuple ts -> TyTuple(List.map(fun t-> apply_subst t s) ts)



// TODO implement this
// CHECKED

let compose_subst (s1 : subst) (s2 : subst) : subst =   //θ1∘θ2 -> θ3

    s1 |> List.iter(fun (tv1, t1)->
        match List.tryFind(fun(tv2,_)-> tv2 = tv1) s2 with
            | Some (_, t2)-> 
                if( t1 <> t2 ) then sub_error "Undisjoined set"
            | None-> ())
    s1@s2
        

//Apply the subst to all the var in the type schema
let apply_subst_in_scheme (Forall(tyvars, ty)) subst =  //θ1(σ)-> θ2
    Forall(tyvars, apply_subst ty subst)

//Apply the subst to all the schema inside the environment 
let apply_subst_in_env env subst = //θ1(Γ)-> θ2
    List.map(fun (id, schema) -> (id, apply_subst_in_scheme schema subst)) env
    

//Create a free vars for a type τ
let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

// Include in the schema the freevars
let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

// type inference

// Define the freevars schema in the environment
let freevars_schema_env env =
    List.fold(fun r (_, sch) -> r + freevars_scheme sch) Set.empty env


// TODO implement this
// CHECKED

// Unification operation
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match t1, t2 with
    | t1, t2 when t1=t2 -> []                                   //U
    | TyName t1, TyName t2 when t1 = t2-> []                    //U(c1; c2)
    | TyArrow (ta1,ta2), TyArrow (ta3,ta4)->                    //U(τ1->τ2; τ3->τ4)
        compose_subst  (unify ta1 ta3) 
                       (unify ta2 ta4)
    | TyTuple tt1,TyTuple tt2 when tt1.Length = tt2.Length->    //U(τ1* ...* τn; τ1'* ...* τn')
        let app subst (x,y) = compose_subst (unify (apply_subst x subst) 
                                                   (apply_subst y subst)) subst
        List.fold app []<| List.zip tt1 tt2
    | TyVar tv1, tv2 when Set.contains tv1 <| freevars_ty tv2 ->
        //If the TyVar is a freevars of t2 we found a situation where is required the implementation of inifite derivation tree
        type_error "Unification error: unifying %d with %s requires infinite types"
            tv1 (pretty_ty tv2)
    | TyVar tv1, _->[(tv1,t2)]                                  //U(α; τ)
    | _,TyVar _-> unify t2 t1                                   //U(τ; α)
    | _, _-> unfy_error "unification error: types '%s' and '%s' are not unifiable" (pretty_ty t1)(pretty_ty t2)

//Definenig an α as integer we can define new free vars incrementing fv_num ensuring it's unicity

let mutable private fv_num = 0
let fresh_var()=
    let v = fv_num
    fv_num<-fv_num + 1
    TyVar v
 
// Instantiation 
// Given a type schema σ we are going to refresh all x instance in σ
let instantiate(Forall(tyvars, ty))=
    let toRefresh = Set.intersect (freevars_ty ty) (Set tyvars)
    let sub = List.map (fun v->v,fresh_var()) <| Set.toList toRefresh
    apply_subst ty sub

// Generalization
// Given α make ∀ free(α) . α(free(α)) 
let generalization env ty =
    let free = freevars_ty ty
    let scheme = Set.unionMany <| List.map (freevars_scheme << snd) env
    Forall (Set.toList <| Set.difference free scheme, ty)

// Add to the env the x:∀ø.α
let extend_env (name, ty) env=
    (name, Forall ([], ty)) :: env

// binary arithmetic operators
let aritm_binOps = List.fold( fun acc op->[  
    (op, TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    (op, TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    (op, TyArrow (TyInt, TyArrow (TyFloat, TyFloat)))
    (op, TyArrow (TyFloat, TyArrow (TyInt, TyFloat)))]@acc) [] ["+"; "-"; "*"; "/"; "%"]
// binary comparison operators
let comp_binOps =  List.fold( fun acc op->[  
    (op, TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    (op, TyArrow (TyFloat, TyArrow (TyFloat, TyBool)))
    (op, TyArrow (TyInt, TyArrow (TyFloat, TyBool)))
    (op, TyArrow (TyFloat, TyArrow (TyInt, TyBool)))]@acc) [] ["<"; "<="; "="; ">="; "<>"]

// binary boolean operators
let bool_binOps = [
    ("and", TyArrow (TyBool, TyArrow(TyBool, TyBool)))
    ("or", TyArrow (TyBool, TyArrow(TyBool, TyBool))) 
]

// unary operators
let unary_op =[
  
    ("not", TyArrow (TyBool, TyBool))
    ("neg", TyArrow (TyInt, TyInt))
    ("neg", TyArrow (TyFloat, TyFloat))  
]

//Build the initial type schema
let init_ty_schema = List.map (fun (x, y) -> (x, Forall([], y)))<|unary_op@aritm_binOps@comp_binOps@bool_binOps

// TODO for exam
// CHECKED
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    |   Lit (LInt _)        -> TyInt, []        //const Int
    |   Lit (LBool _)       -> TyBool, []       //const Bool
    |   Lit (LFloat _)      -> TyFloat, []      //const Float
    |   Lit (LString _)     ->  TyString, []    //const String
    |   Lit (LChar _)       -> TyChar, []       //const Char
    |   Lit LUnit           -> TyUnit, []       //Unit
    |   Var x->                                 //Var
            match List.tryFind( fun(tv,_)-> tv = x ) env with
                | Some (_, ty) -> instantiate ty,[]
                | None  -> type_error "Undefined variable %s" x

    |   Lambda (f, t1, e) ->                                //Lambda

            //If present t1 present return it otherwise let it a freevar
            let t1_ty =       
                match t1 with 
                    | Some t1 -> t1
                    | None -> fresh_var() 

            // extend the environment with ty_1
            let env = extend_env (f, t1_ty) env              //Γ,(x:∀ø.α)
            
            //infer expression e
            let e_ty, e_subst = typeinfer_expr env e        //Γ,(x:∀ø.α) ⊢ e: τ_1; θ_1

            //Update t1 
            let t1_ty = apply_subst t1_ty e_subst
           
            TyArrow(t1_ty, e_ty), e_subst                    //Γ ⊢ λx.e : α-> τ_1; θ_1

    |   App (e1, e2) ->                                 //App
        //Infer e1
        let e1_ty, e1_subst = typeinfer_expr env e1     // Γ ⊦ e1:τ1 ⊳ θ1 

        //Infer e2 
        let env  = apply_subst_in_env env e1_subst      // θ1(Γ)
        let e2_ty, e2_subst = typeinfer_expr env e2     // Γ ⊦ e2:τ2 ⊳ θ2
        
        //Update e1
        let e1_ty = apply_subst e1_ty e2_subst          
        
        //Unify
                                                        // U(τ1; τ2-> α) = θ3
        let fv_ty = fresh_var()
        let app_ty = TyArrow(e2_ty, fv_ty)

        let subst_3 = unify e1_ty app_ty

        //Compse the new subst
        let subst_4 = compose_subst subst_3 e2_subst    // θ4 = θ3 ∘ θ2 

        apply_subst fv_ty subst_3, subst_4              //Γ ⊦ e1 e2: τ ⊳ θ4
    //Did in class
    |   Let (x, _ , e1, e2)->                              //Let
            //Infer e1 
            let t1, s1 = typeinfer_expr env e1              //Γ ⊦ e1: τ1 ⊳ θ1
            
            //Create the type schema
                                                            // σ1 = gen^{θ1,Γ} (τ1)
            let tvs = Set.toList(freevars_ty t1 - freevars_schema_env env)
            let sch = Forall (tvs, t1)
            
            //Infer e2 
            let t2, s2= typeinfer_expr((x, sch) :: env) e2  //θ1(Γ),(x,σ1) ⊦ e2:τ2 ⊳ θ2
            
            t2, compose_subst s2 s1                         //Γ ⊦ let x=e1 in e2: τ2 ⊳ θ3 = θ2 ∘ θ1 
    
    |   IfThenElse (cond, thenBranch, o_elseBranch) ->                  //IfThenEls
         
        //Infer guard type
    
        let cond_ty, cond_subst = typeinfer_expr env cond               //Γ ⊦ e1: τ1 ⊳ θ1 
        let cond_subst= compose_subst cond_subst (unify cond_ty TyBool) // θ3 = θ1 ∘ U(τ1, bool)
        let env = apply_subst_in_env env cond_subst                     // θ3(Γ)

        //Infer type of then branch
        let then_ty, then_subst = typeinfer_expr env thenBranch         // Γ ⊦ e2: τ2 ⊳ θ4 
        let then_subst = compose_subst then_subst cond_subst            // θ5 = θ3 ∘ θ4 
        let env = apply_subst_in_env env then_subst                     // θ5(Γ)
            
        //Check if we have an else branch
        match o_elseBranch with
            | Some o_elseBranch ->
                //infer else branch type
                let else_ty, else_subst = typeinfer_expr env o_elseBranch // Γ ⊦ e3: τ3 ⊳ θ6

                //update then_ty
                let then_ty = apply_subst then_ty else_subst             // θ7 = θ5 ∘ θ6

                //get new subs                                           // θ8 = U( θ7(τ2) ∘ θ7(τ3))
                let else_subst = compose_subst (unify else_ty then_ty) (compose_subst else_subst then_subst)

                apply_subst then_ty else_subst, else_subst              // θ8(τ2), θ9 = θ7 ∘ θ8

            | None ->
                TyUnit, then_subst 

    |   Tuple tp->                                                  //Tuple
        //Accumulator function to apply the substitution to all the elements inside the tuple
        let acc_sub(env, subst, ty) t =
            
            let env = apply_subst_in_env env subst                  // θ(Γ)
            
            let t_i, subst_i = typeinfer_expr env t                 // θ(Γ) ⊦ ei+1 : τi+1 ⊳ θi+1

            //update accumulators
            let ty = List.map (fun t -> apply_subst t subst_i) ty   // θi+1(τi)  ∀i<i+1
           
            let subst = compose_subst subst_i subst                 // θ= θ ∘ θi+1
            
            env, subst, ty @ [ t_i ]

        //Apply the substitutions to the tuple
        let _, subst, ty = List.fold acc_sub (env, [], []) tp
        TyTuple ty, subst

    |   LetRec (f, _, e1, e2) ->                            //Let rec   
                                                            // (f:∀ø.α)
            let fv_ty = fresh_var() 

            let env = extend_env (f, fv_ty) env
        
            //infer e1
            let e1_ty, e1_subst = typeinfer_expr env e1     // Γ, (f:∀ø.α) ⊦ e1: τ1 ⊳ θ1
           
            //Update fv_ty and subst_fv 
            let fv_ty = apply_subst fv_ty e1_subst 
            let fv_subst = unify fv_ty e1_ty

            //Update e1_ty and subst_1 
            let e1_ty = apply_subst e1_ty fv_subst
            let e1_subst = compose_subst fv_subst e1_subst 
         
            let env = apply_subst_in_env env e1_subst       // θ1(Γ)
            let env = (f, generalization env e1_ty)::env    // Γ, (f: σ1) with σ1 = gen^{θ1(Γ)} (τ1)

            //infer e2
            let e2_ty, e2_subst_2 = typeinfer_expr env e2   // Γ, (f: σ1) ⊦ e2: τ2 ⊳ θ2

            let subst = compose_subst e1_subst e2_subst_2   //θ3 = θ2 ∘ θ1

            e2_ty, subst
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" | "<" | "<=" | ">" | ">=" | "=" | "<>"  as op), e2) ->
        //Infer e1
        let e1_ty, e1_subst = typeinfer_expr env e1

        let subst = match e1_ty with
        | TyInt   ->  unify e1_ty TyInt
        | TyFloat ->  unify e1_ty TyFloat
        |   _     -> type_infer_error "BinOp expression: unexpected type inside binary operation: %s" (pretty_ty e1_ty)

        let subst = compose_subst e1_subst subst

        let env = apply_subst_in_env env subst

        //Infer e2
        let e2_ty, e2_subst = typeinfer_expr env e2

        let subst = match e2_ty with
            | TyInt   ->  unify e2_ty TyInt
            | TyFloat ->  unify e2_ty TyFloat
            | _ -> type_infer_error "BinOp expression: unexpected type inside binary operation: %s"(pretty_ty e2_ty)

                
        let subst = compose_subst subst e2_subst

        if(List.contains op ["+" | "-" | "/" | "%" | "*"]) then
            match e1_ty, e2_ty with
            | TyInt, TyInt -> TyInt, subst
            | TyFloat, TyFloat
            | TyFloat, TyInt
            | TyInt, TyFloat -> TyFloat, subst
            | _ -> type_infer_error "BinOp expression: unsupported type in binary operators: %s %s %s"(pretty_ty e1_ty) op (pretty_ty e2_ty)
        if(List.contains op ["<" | "<=" | ">" | ">=" | "=" | "<>"]) then
            match e1_ty, e2_ty with
            | TyInt, TyInt
            | TyFloat, TyFloat
            | TyFloat, TyInt
            | TyInt, TyFloat -> TyBool, subst
            | _ -> type_infer_error "BinOp expression: unsupported binary operators: %s" op
        type_infer_error "BinOp expression: unsupported binary operators: %s" op
(*
    | BinOp (e1, ( "<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        //Infer e1
        let e1_ty, e1_subst = typeinfer_expr env e1

        let subst = match e1_ty with
        | TyInt   ->  unify e1_ty TyInt
        | TyFloat ->  unify e1_ty TyFloat
        |   _     -> type_infer_error "BinOp expression: unexpected type inside binary operation: %s" (pretty_ty e1_ty)

        let subst = compose_subst e1_subst subst

        let env = apply_subst_in_env env subst

        //Infer e2
        let e2_ty, e2_subst = typeinfer_expr env e2

        let subst = match e2_ty with
            | TyInt   ->  unify e2_ty TyInt
            | TyFloat ->  unify e2_ty TyFloat
            | _ -> type_infer_error "BinOp expression: unexpected type inside binary operation: %s"(pretty_ty e2_ty)

                
        let subst = compose_subst subst e2_subst

        match e1_ty, e2_ty with
        | TyInt, TyInt
        | TyFloat, TyFloat
        | TyFloat, TyInt
        | TyInt, TyFloat -> TyBool, subst
        | _ -> type_infer_error "BinOp expression: unsupported binary operators: %s" op
*)
    | BinOp (e1, ("and" | "or" as op), e2) ->
         //Infer e1
        let e1_ty, e1_subst = typeinfer_expr env e1

        let subst = match e1_ty with
        | TyBool   ->  unify e1_ty TyBool
        |   _     -> type_infer_error "BinOp expression: unexpected type inside binary operation: %s" (pretty_ty e1_ty)

        let subst = compose_subst e1_subst subst

        let env = apply_subst_in_env env subst

        //Infer e2
        let e2_ty, e2_subst = typeinfer_expr env e2

        let subst = match e2_ty with
            | TyBool   ->  unify e2_ty TyBool
            | _ -> type_infer_error "BinOp expression: unexpected type inside binary operation: %s"(pretty_ty e2_ty)

                
        let subst = compose_subst subst e2_subst

        match e1_ty, e2_ty with
        | TyBool, TyBool -> TyBool, subst
        | _ ->  type_infer_error "BinOp expression: unexpected type inside binary operation: %s"(pretty_ty e2_ty)
    
    | BinOp (_, op, _) -> unexpected_error "unsupported binary operator (%s)" op
   

    | UnOp (op, e)->                                                        //UnOp   
        let e_ty, e_subst = typeinfer_expr env e
        
        if ((not(e_ty=TyInt || e_ty=TyFloat) && op="-")) then type_infer_error "UnOp expression: unsupported unary operand, expecting numeric got: %s" (pretty_ty e_ty)
        if (not(e_ty=TyBool && op="not")) then type_infer_error "UnOp expression: unsupported unary operand, expecting boolean got: %s" (pretty_ty e_ty)

        e_ty, e_subst
        

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
 

// type checker
//
(*
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
*)