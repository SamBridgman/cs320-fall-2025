include Utils

let parse (input_string : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string input_string) with
  | parsed_program -> Some parsed_program
  | exception _ -> None

let rec curry_arguments arg_list function_body =
  match arg_list with
  | [] -> function_body
  | (param_name, param_type) :: remaining_args ->
      Fun (param_name, param_type, curry_arguments remaining_args function_body)

let rec make_function_type arg_list return_type =
  match arg_list with
  | [] -> return_type
  | (_, arg_type) :: remaining_args ->
      FunTy (arg_type, make_function_type remaining_args return_type)

let rec desugar_sfexpr (surface_expr : sfexpr) : expr =
  match surface_expr with
  | SUnit -> Unit
  | SBool bool_val -> Bool bool_val
  | SNum num_val -> Num num_val
  | SVar var_name -> Var var_name
  | SIf (cond_expr, then_expr, else_expr) ->
      If
        ( desugar_sfexpr cond_expr
        , desugar_sfexpr then_expr
        , desugar_sfexpr else_expr )
  | SBop (op, left_expr, right_expr) ->
      Bop (op, desugar_sfexpr left_expr, desugar_sfexpr right_expr)
  | SFun { args; body } ->
      curry_arguments args (desugar_sfexpr body)
  | SApp expr_list ->
      let desugared_exprs = List.map desugar_sfexpr expr_list in
      (match desugared_exprs with
       | [] -> failwith "SApp expects at least one expression"
       | first_expr :: remaining_exprs ->
           List.fold_left
             (fun function_expr arg_expr -> App (function_expr, arg_expr))
             first_expr
             remaining_exprs)
  | SLet { is_rec; name; args; ty; binding; body } ->
      Let
        {
          is_rec;
          name;
          ty = make_function_type args ty;
          binding = curry_arguments args (desugar_sfexpr binding);
          body = desugar_sfexpr body;
        }
  | SAssert assert_expr -> Assert (desugar_sfexpr assert_expr)

let desugar (program : prog) : expr =
  match program with
  | [] -> Unit
  | _ ->
      let rec build_nested_lets let_statements result_expr =
        match let_statements with
        | [] -> result_expr
        | { is_rec; name; args; ty; binding } :: remaining_lets ->
            Let
              {
                is_rec;
                name;
                ty = make_function_type args ty;
                binding = curry_arguments args (desugar_sfexpr binding);
                body = build_nested_lets remaining_lets result_expr;
              }
      in
      let last_var_name = (List.hd (List.rev program)).name in
      build_nested_lets program (Var last_var_name)

let type_of (e : expr) : (ty, error) result =
  let rec go (env : ty Env.t) (e : expr) : (ty, error) result =
    match e with
    | Unit -> Ok UnitTy
    | Bool _ -> Ok BoolTy
    | Num _ -> Ok IntTy
    | Var x -> (
        match Env.find_opt x env with
        | Some ty -> Ok ty
        | None -> Error (UnknownVar x)
      )
    | Bop (op, e1, e2) -> (
        match go env e1 with
        | Error err -> Error err
        | Ok ty1 -> (
            match go env e2 with
            | Error err -> Error err
            | Ok ty2 -> (
                match op with
                | Add | Sub | Mul | Div | Mod ->
                    if ty1 <> IntTy then Error (OpTyErrL (op, IntTy, ty1))
                    else if ty2 <> IntTy then Error (OpTyErrR (op, IntTy, ty2))
                    else Ok IntTy
                | Lt | Lte | Gt | Gte | Eq | Neq ->
                    if ty1 <> IntTy then Error (OpTyErrL (op, IntTy, ty1))
                    else if ty2 <> IntTy then Error (OpTyErrR (op, IntTy, ty2))
                    else Ok BoolTy
                | And | Or ->
                    if ty1 <> BoolTy then Error (OpTyErrL (op, BoolTy, ty1))
                    else if ty2 <> BoolTy then Error (OpTyErrR (op, BoolTy, ty2))
                    else Ok BoolTy
              )
          )
      )
    | If (e1, e2, e3) -> (
        match go env e1 with
        | Error err -> Error err
        | Ok ty1 -> (
            if ty1 <> BoolTy then Error (IfCondTyErr ty1)
            else
              match go env e2 with
              | Error err -> Error err
              | Ok ty2 -> (
                  match go env e3 with
                  | Error err -> Error err
                  | Ok ty3 -> (
                      if ty2 <> ty3 then Error (IfTyErr (ty2, ty3))
                      else Ok ty2
                    )
                )
          )
      )
    | Fun (x, ty1, e) -> (
        let env = Env.add x ty1 env in
        match go env e with
        | Error err -> Error err
        | Ok ty2 -> Ok (FunTy (ty1, ty2))
      )
    | App (e1, e2) -> (
        match go env e1 with
        | Error err -> Error err
        | Ok ty1 -> (
            match ty1 with
            | FunTy (ty_arg, ty_ret) -> (
                match go env e2 with
                | Error err -> Error err
                | Ok ty2 -> (
                    if ty2 <> ty_arg then Error (FunArgTyErr (ty_arg, ty2))
                    else Ok ty_ret
                  )
              )
            | _ -> Error (FunAppTyErr ty1)
          )
      )
    | Let { is_rec; name; ty; binding; body } -> (
        if is_rec then (
          match binding with
          | Fun _ -> (
              let env = Env.add name ty env in
              match go env binding with
              | Error err -> Error err
              | Ok binding_ty -> (
                  if binding_ty <> ty then Error (LetTyErr (ty, binding_ty))
                  else
                    match go env body with
                    | Error err -> Error err
                    | Ok body_ty -> Ok body_ty
                )
            )
          | _ -> Error (LetRecErr name)
        )
        else (
          match go env binding with
          | Error err -> Error err
          | Ok binding_ty -> (
              if binding_ty <> ty then Error (LetTyErr (ty, binding_ty))
              else
                let env = Env.add name ty env in
                match go env body with
                | Error err -> Error err
                | Ok body_ty -> Ok body_ty
            )
        )
      )
    | Assert e -> (
        match go env e with
        | Error err -> Error err
        | Ok ty -> (
            if ty <> BoolTy then Error (AssertTyErr ty)
            else Ok UnitTy
          )
      )
  in
  go Env.empty e

exception AssertFail
exception DivByZero

let eval (e : expr) : value =
  let rec go (env : dyn_env) (e : expr) : value =
    match e with
    | Unit -> VUnit
    | Bool b -> VBool b
    | Num n -> VNum n
    | Var x -> Env.find x env
    | Bop (op, e1, e2) -> (
        let v1 = go env e1 in
        let v2 = go env e2 in
        match op with
        | Add -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VNum (n1 + n2)
            | _ -> assert false
          )
        | Sub -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VNum (n1 - n2)
            | _ -> assert false
          )
        | Mul -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VNum (n1 * n2)
            | _ -> assert false
          )
        | Div -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> (
                if n2 = 0 then raise DivByZero
                else VNum (n1 / n2)
              )
            | _ -> assert false
          )
        | Mod -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> (
                if n2 = 0 then raise DivByZero
                else VNum (n1 mod n2)
              )
            | _ -> assert false
          )
        | Lt -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VBool (n1 < n2)
            | _ -> assert false
          )
        | Lte -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VBool (n1 <= n2)
            | _ -> assert false
          )
        | Gt -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VBool (n1 > n2)
            | _ -> assert false
          )
        | Gte -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VBool (n1 >= n2)
            | _ -> assert false
          )
        | Eq -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VBool (n1 = n2)
            | _ -> assert false
          )
        | Neq -> (
            match (v1, v2) with
            | VNum n1, VNum n2 -> VBool (n1 <> n2)
            | _ -> assert false
          )
        | And -> (
            match v1 with
            | VBool false -> VBool false
            | VBool true -> v2
            | _ -> assert false
          )
        | Or -> (
            match v1 with
            | VBool true -> VBool true
            | VBool false -> v2
            | _ -> assert false
          )
      )
    | If (e1, e2, e3) -> (
        match go env e1 with
        | VBool true -> go env e2
        | VBool false -> go env e3
        | _ -> assert false
      )
    | Fun (x, _, e) -> VClos { arg = x; body = e; env = env; name = None }
    | App (e1, e2) -> (
        match go env e1 with
        | VClos { arg; body; env = clos_env; name } -> (
            let v2 = go env e2 in
            let env = Env.add arg v2 clos_env in
            let env = (
              match name with
              | Some f -> Env.add f (VClos { arg; body; env = clos_env; name }) env
              | None -> env
            ) in
            go env body
          )
        | _ -> assert false
      )
    | Let { is_rec; name; ty = _; binding; body } -> (
        if is_rec then (
          match go env binding with
          | VClos { arg; body = fun_body; env = clos_env; name = _ } -> (
              let temp_clos = VClos { arg; body = fun_body; env = clos_env; name = Some name } in
              let clos_env = Env.add name temp_clos clos_env in
              let clos = VClos { arg; body = fun_body; env = clos_env; name = Some name } in
              let env = Env.add name clos env in
              go env body
            )
          | _ -> assert false
        )
        else (
          let v1 = go env binding in
          let env = Env.add name v1 env in
          go env body
        )
      )
    | Assert e -> (
        match go env e with
        | VBool true -> VUnit
        | _ -> raise AssertFail
      )
  in
  go Env.empty e

let interp (s : string) : (value, error) result =
  match parse s with
  | None -> Error ParseErr
  | Some prog -> (
      let e = desugar prog in
      match type_of e with
      | Error err -> Error err
      | Ok _ -> Ok (eval e)
    )
