include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | prog -> Some prog
  | exception _ -> None

let free_vars ty =
  let rec go = function
    | TUnit | TInt | TFloat | TBool -> VarSet.empty
    | TVar a -> VarSet.singleton a
    | TList t -> go t
    | TOption t -> go t
    | TPair (t1, t2) -> VarSet.union (go t1) (go t2)
    | TFun (t1, t2) -> VarSet.union (go t1) (go t2)
  in go ty

let ty_subst t_sub a =
  let rec go = function
    | TUnit -> TUnit
    | TInt -> TInt
    | TFloat -> TFloat
    | TBool -> TBool
    | TVar b -> if a = b then t_sub else TVar b
    | TList t -> TList (go t)
    | TOption t -> TOption (go t)
    | TPair (t1, t2) -> TPair (go t1, go t2)
    | TFun (t1, t2) -> TFun (go t1, go t2)
  in go

let apply_subst subst ty =
  List.fold_left (fun ty (var, repl) -> ty_subst repl var ty) ty (List.rev subst)

let unify cs =
  let rec unify_loop subst = function
    | [] -> Some subst
    | (t1, t2) :: cs ->
      if t1 = t2 then
        unify_loop subst cs
      else
        match (t1, t2) with
        | TFun (s1, t1'), TFun (s2, t2') ->
          unify_loop subst ((s1, s2) :: (t1', t2') :: cs)
        | TList t1', TList t2' ->
          unify_loop subst ((t1', t2') :: cs)
        | TOption t1', TOption t2' ->
          unify_loop subst ((t1', t2') :: cs)
        | TPair (t1a, t1b), TPair (t2a, t2b) ->
          unify_loop subst ((t1a, t2a) :: (t1b, t2b) :: cs)
        | TVar a, t when not (VarSet.mem a (free_vars t)) ->
          let t' = apply_subst subst t in
          let new_subst = (a, t') :: subst in
          let apply_subst_to_type ty =
            List.fold_left (fun ty (var, repl) -> ty_subst repl var ty) ty (List.rev new_subst)
          in
          let new_cs = List.map (fun (t1, t2) -> (apply_subst_to_type t1, apply_subst_to_type t2)) cs in
          unify_loop new_subst new_cs
        | t, TVar a ->
          unify_loop subst ((TVar a, t) :: cs)
        | _ -> None
  in
  unify_loop [] cs

let principle_type ty cs =
  match unify cs with
  | None -> None
  | Some subst ->
    let ty' = apply_subst subst ty in
    let constrained_vars = List.fold_left
      (fun acc (var, _) -> VarSet.add var acc)
      VarSet.empty subst
    in
    let fv_ty = free_vars ty' in
    let quantified = VarSet.diff fv_ty constrained_vars in
    Some (Forall (quantified, ty'))

let type_of (_ctxt: stc_env) (_e : expr) : ty_scheme option = assert false

let is_well_typed (_p : prog) : bool = assert false

exception AssertFail
exception DivByZero
exception CompareFunVals

let eval_expr (_env : dyn_env) (_e : expr) : value = assert false

let eval p =
  let rec nest = function
    | [] -> Unit
    | [{is_rec;name;binding}] -> Let {is_rec;name;binding;body = Var name}
    | {is_rec;name;binding} :: ls -> Let {is_rec;name;binding;body = nest ls}
  in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog ->
    if is_well_typed prog
    then Ok (eval prog)
    else Error TypeError
  | None -> Error ParseError
