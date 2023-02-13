(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

exception SubstitutionError of string

exception UnifyError of string

//θ
type subst = (tyvar * ty) list

// TODO implement this 
// CHECKED
// θ(τ) -> τ
let rec apply_subst (t : ty) (s : subst) : ty =
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


// θ1∘θ2 -> θ3
// TODO implement this
// CHECKED
let compose_subst (s1 : subst) (s2 : subst) : subst = (*
    let sDis s = List.fold( fun  (sCom : subst) (tv1, t1)->
            //Looking if s1 share some tvar with s2
            match List.tryFind(fun(tv2,_)-> tv2 = tv1) s2 with
                | Some (_, t2)-> 
                    //if they have the same type add to the partial composition otherwise rise an exception
                    if( t1 = t2 ) then (tv1, t2)::sCom
                    else raise (SubstitutionError("Undisjoined set"))
                //If there is no match simply add to the accumulator list
                | None -> (tv1,t1)::sCom) [] s
    (sDis s1)@s2
    *)

    s1 |> List.iter(fun (tv1, t1)->
        match List.tryFind(fun(tv2,_)-> tv2 = tv1) s2 with
            | Some (_, t2)-> 
                if( t1 <> t2 ) then raise (SubstitutionError("Undisjoined set"))
            | None-> ())

(*
    let rec chk_disj s =
        match s with
        | []->()
        | (tv1,t1)::s_tail-> 
            match List.tryFind(fun(tv2,_)-> tv2 = tv1) s2 with
                | Some (_, t2)-> 
                    if( t1 <> t2 ) then raise (SubstitutionError("Undisjoined set"))
                | None-> ()
            iter s_tail
    chk_disj 
    *)
    s1@s2
        
        //Esiste controllo il tipo
        //Non esiste aggiungo

//θ1(σ)-> θ2
let apply_subst_in_scheme (Forall(tyvars, ty)) subst =
    Forall(tyvars, apply_subst ty subst)
//θ1(Γ)-> θ2
let apply_subst_in_env env subst =
    List.map(fun (id, schema) -> (id, apply_subst_in_scheme schema subst)) env
    

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

// type inference
//

let freevars_schema_env env =
    List.fold(fun r (_, sch) -> r + freevars_scheme sch) Set.empty env


// TODO implement this
// CHECKED
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
        type_error "Unification error: unifying %d with %s requires infinite types"
            tv1 (pretty_ty tv2)
    | TyVar tv1, _->[(tv1,t2)]                                  //U(α; τ)
    | _,TyVar _-> unify t2 t1                                   //U(τ; α)
    | _, _-> raise(UnifyError("unification error: types '%s' and '%s' are not unifiable")) (pretty_ty t1)(pretty_ty t2)

//Definenig an 'a as integer we can define in this way new type vars incrementing fv_num
//ensuring it's unicity
let mutable private fv_num = 0
let fresh_var()=
    let v = fv_num
    fv_num<-fv_num + 1
    TyVar v
 
// Instantiation 
// Given ∀ x . t(x)
// refresh all x in t(x)
let instantiate(Forall(tyvars, ty))=
    let toRefresh = Set.intersect (freevars_ty ty) (Set tyvars)
    let sub = List.map (fun v->v,fresh_var()) <| Set.toList toRefresh
    apply_subst ty sub

//Generalization
// Given α make ∀ free(α) . α(free(α)) 
let generalization env ty =
    let free = freevars_ty ty
    let scheme = Set.unionMany <| List.map (freevars_scheme << snd) env
    Forall (Set.toList <| Set.difference free scheme, ty)

//Add to the env the x:∀ø.α
let extend_env (name, ty) env=
    (name, Forall ([], ty)) :: env

let gamma0 = [
    //Integer op
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))  //'a + 'a => int->int
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))  //'a - 'a => int->int
    ("*", TyArrow (TyInt, TyArrow (TyInt, TyInt)))  //'a + 'a => int->int
    ("/", TyArrow (TyInt, TyArrow (TyInt, TyInt)))  //'a - 'a => int->int
    ("%", TyArrow (TyInt, TyArrow (TyInt, TyInt)))  //'a + 'a => int->int
    //Flaota op
    ("+", TyArrow (TyInt, TyArrow (TyFloat, TyFloat)))  //'b + 'b => float->float
    ("-", TyArrow (TyInt, TyArrow (TyFloat, TyFloat))) 

    
]



// TODO for exam
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    |   Lit (LInt _)        -> TyInt, []        //const Int
    |   Lit (LBool _)       -> TyBool, []       //const Bool
    |   Lit (LFloat _)      -> TyFloat, []      //const Float
    |   Lit (LString _)     ->  TyString, []    //const String
    |   Lit (LChar _)       -> TyChar, []       //const Char
    |   Lit LUnit           -> TyUnit, []        //Luni
    |   Var x->                                 //Var
        match List.tryFind( fun(tv,_)-> tv = x ) env with
            | Some (_, ty) -> instantiate ty,[]
            | None  -> type_error "Undefined variable %s" x

    |   Lambda (args_name, t1, body) ->               //Lambda
            //If present infer t1 or let it a freevar
            let args_ty =       
                match t1 with 
                    | Some t1 -> t1
                    | None -> fresh_var() 

            // extend the environment
            let env = extend_env (args_name, args_ty) env   //Γ,(x:∀ø.α)
            
            //infer expression e
            let body_ty, body_subs = typeinfer_expr env body //Γ,(x:∀ø.α) ⊢ e: τ_1; θ_1

            //Update t1 
            let args_ty = apply_subst args_ty body_subs
           
            TyArrow(args_ty, body_ty), body_subs             //Γ ⊢ λx.e : α-> τ_1; θ_1

    |   App (e1, e2) ->                         //App
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

    
        apply_subst fv_ty subst_4, subst_4              //Γ ⊦ e1 e2: τ ⊳ θ4

    |   Let (x, tyo, e1, e2)->                  //Let
            //Infer e1 
            let t1, s1 = typeinfer_expr env e1              //Γ ⊦ e1: τ1 ⊳ θ1
            
            //Create the type schema
                                                            // σ1 = gen^{θ1,Γ} (τ1)
            let tvs = Set.toList(freevars_ty t1 - freevars_schema_env env)
            let sch = Forall (tvs, t1)
            
            //Infer e2 
            let t2, s2= typeinfer_expr((x, sch) :: env) e2  //θ1(Γ),(x,σ1) ⊦ e2:τ2 ⊳ θ2
            
            t2, compose_subst s2 s1                         //Γ ⊦ let x=e1 in e2: τ2 ⊳ θ3 = θ2 ∘ θ1 
    
    |   IfThenElse (cond, thenBranch, o_elseBranch) ->             //IfThenEls
         
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



    |   Tuple tp->                              //Tuple
        //Accumulator function to apply the substitution to all the elements inside the tuple
        let acc_sub(env, subst, ty) t =
            //θ(Γ)
            let env = apply_subst_in_env env subst
            // θ(Γ) ⊦ ei+1 : τi+1 ⊳ θi+1
            let t_i, subst_i = typeinfer_expr env t

            //update accumulators

            //θi+1(τi)  ∀i<i+1
            let ty = List.map (fun t -> apply_subst t subst_i) ty
            //θ= θ ∘ θi+1
            let subst = compose_subst subst_i subst
            
            env, subst, ty @ [ t_i ]

        //Apply the substitutions to the tuple
        let _, subst, ty = List.fold acc_sub (env, [], []) tp
        TyTuple ty, subst

    (*
    |   LetRec (f, _, e1, e2) ->                //Let rec
    |   BinOp (e1, "+", e2) ->                  //BinOp +      
    |   BinOp (e1, "-", e2) ->                  //BinOp -
    |   BinOp (e1, "*", e2) ->                  //BinOp *
    |   BinOp (e1, "/", e2) ->                  //BinOp /    
    |   BinOp (e1, "%", e2) ->                  //BinOp %
    |   BinOp (e1, "<", e2) ->                  //BinOp <
    |   BinOp (e1, "<=", e2) ->                 //BinOp <=    
    |   BinOp (e1, "==", e2) ->                 //BinOp ==
    |   BinOp (e1, ">=", e2) ->                 //BinOp >=
    |   BinOp (e1, ">", e2) ->                  //BinOp > 
    |   BinOp (e1, "<>", e2) ->                 //BinOp <>
    |   BinOp (e1, "and", e2) ->                //BinOp and
    |   BinOp (e1, "or", e2) ->                 //BinOp or    
    |   UnOp ("not", e) ->                      //UnOp not
    |   UnOp ("-", e) ->                        //UnOp -
    |   
    *)

// type checker
//
    
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
