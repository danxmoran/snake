open Types
open Printf
open Instruction
open Expr
open Pretty
open BatUref
open Optimize

(* Add or change these constants as needed *)
let err_COMP_NOT_NUM   = 1
let err_ARITH_NOT_NUM  = 2
let err_LOGIC_NOT_BOOL = 3
let err_IF_NOT_BOOL    = 4
let err_OVERFLOW       = 5
let err_GET_NOT_TUPLE  = 6
let err_GET_LOW_INDEX  = 7
let err_GET_HIGH_INDEX = 8
let err_INDEX_NOT_NUM  = 9
let err_CALL_NOT_FUNC  = 10
let err_CALL_BAD_ARITY = 11
let err_SET_NOT_TUPLE  = 12

let const_true  = HexConst(0xFFFFFFFF)
let const_false = HexConst(0x7FFFFFFF)
let bool_mask   = HexConst(0x80000000)

let bool_tag    = 0b111
let tuple_tag   = 0b001
let closure_tag = 0b101

type 'a envt = (string * 'a) list

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, _, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | _ -> false

let rec find (ls : 'a envt) (x : string) =
  match ls with
  | [] -> failwith (sprintf "%s not found in environment" x)
  | (y,v)::rest ->
    if y = x then v else find rest x

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))
;;

let rec free_typ_tyvars (typ : typ) : string list =
  match typ with
  | TyCon _ -> []
  | TyVar(name) -> [name]
  | TyArr(args, ret) -> List.concat (List.map free_typ_tyvars (args @ [ret]))
  | TyTup(elts) -> List.concat (List.map free_typ_tyvars elts)

let free_scheme_tyvars (scm : scheme) : string list =
  let (args, typ) = scm in
  List.fold_left
    ExtList.List.remove
    (List.sort_uniq String.compare (free_typ_tyvars typ))
    args

let well_formed_type (scm : scheme) : bool =
  (free_scheme_tyvars scm) = []

let well_formed (p : (Lexing.position * Lexing.position) program) builtins (check_types : bool) : exn list =
  let rec wf_E (e : sourcespan expr) (env : sourcespan envt) : exn list =
    let check_bindings (binds : sourcespan bind list)
                       (env : sourcespan envt)
                       (funs_only : bool)
                       : exn list =
      List.rev (snd (List.fold_left
        (fun (env_acc, err_acc) (x, sopt, expr, where_used) ->
          let expr_errs = wf_E expr (env_acc @ env) in
          let maybe_dup_err =
            try
              let where_def = find env_acc x in
              [DuplicateId(x, where_used, where_def)]
            with | Failure _ -> [] in
          let maybe_shadow_err =
            try
              let where_def = find env x in
              if where_used = where_def
              then []
              else [ShadowId(x, where_used, where_def)]
            with | Failure _ -> [] in
          let maybe_not_fun_err =
            match expr with
            | ELambda(_, _, _) -> []
            | EBool(_, where_used)
            | EId(_, where_used)
            | ENumber(_, where_used)
            | EPrim1(_, _, where_used)
            | EPrim2(_, _, _, where_used)
            | EIf(_, _, _, where_used)
            | ETuple(_, where_used)
            | EGetItem(_, _, where_used)
            | ESetItem(_, _, _, where_used)
            | EGetItemExact(_, _, where_used)
            | ESetItemExact(_, _, _, where_used)
            | EApp(_, _, where_used)
            | ELet(_, _, where_used)
            | ELetRec(_, _, where_used)
            | ESeq(_, where_used) ->
              if funs_only then [LetRecNonFunction(x, where_used)] else [] in
          let maybe_bad_type_err =
            if check_types
            then match sopt with
            | None -> []
            | Some(scm) ->
              if well_formed_type scm
              then []
              else [InvalidType(scm, where_used)]
            else [] in
          ((x, where_used)::env_acc,
           maybe_dup_err
           @ maybe_shadow_err
           @ maybe_not_fun_err
           @ maybe_bad_type_err
           @ expr_errs
           @ err_acc))
        ([], [])
        binds)) in
    match e with
    | EBool(_, _) -> []
    | EId(x, where_used) ->
      (try ignore(find env x); []
       with | Failure _ -> [UnboundId(x, where_used)])
    | ENumber(i, where_used) ->
      if i > max_int || i < min_int
      then [Overflow(i, where_used)]
      else []
    | EPrim1(_, exp, _) -> (wf_E exp env)
    | EPrim2(_, exp1, exp2, _) -> (wf_E exp1 env) @ (wf_E exp2 env)
    | EIf(c, t, f, _) -> (wf_E c env) @ (wf_E t env) @ (wf_E f env)
    | ETuple(elts, _) ->
      List.fold_right (fun elt acc -> (wf_E elt env) @ acc) elts []
    | EGetItem(tup, idx, _) -> (wf_E tup env) @ (wf_E idx env)
    | ESetItem(tup, idx, rhs, _) -> (wf_E tup env) @ (wf_E idx env) @ (wf_E rhs env)
    | EGetItemExact(tup, idx, _) -> wf_E tup env
    | ESetItemExact(tup, idx, rhs, _) -> wf_E tup env @ wf_E rhs env
    | EApp(funexpr, args, _) ->
      (wf_E funexpr env)
      @ (List.fold_right (fun arg acc -> (wf_E arg env) @ acc) args [])
    | ELambda(args, body, _) ->
      let arg_errs = List.rev (snd (List.fold_left
        (fun (env_acc, err_acc) (x, where_used) ->
          let maybe_dup_err =
            try
              let where_def = find env_acc x in
              [DuplicateId(x, where_used, where_def)]
            with | Failure _ -> [] in
          let maybe_shadow_err =
            try
              let where_def = find env x in
              [ShadowId(x, where_used, where_def)]
            with | Failure _ -> [] in
          ((x, where_used)::env_acc,
           maybe_dup_err @ maybe_shadow_err @ err_acc))
        ([], [])
        args)) in
      arg_errs @ (wf_E body (args @ env))
    | ELet(binds, body, _) ->
      let new_env =
        List.map (fun bind -> let (x, _, _, where_def) = bind in (x, where_def)) binds
        @ env in
      (check_bindings binds env false) @ (wf_E body new_env)
    | ELetRec(binds, body, _) ->
      let new_env =
        List.map (fun bind -> let (x, _, _, where_def) = bind in (x, where_def)) binds
        @ env in
      (check_bindings binds new_env true) @ (wf_E body new_env)
    | ESeq(stmts, _) ->
      List.fold_right (fun stmt acc -> (wf_E stmt env) @ acc) stmts [] in
  wf_E p []
;;

type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram = helpA p
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) =
    match e with
    | EPrim1(op, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ESeq([], _) -> failwith "Impossible by syntax"
    | ESeq([stmt], _) -> helpC stmt
    | ESeq(fst :: rest, tag) ->
       let (fst_ans, fst_setup) = helpC fst in
       let (rest_ans, rest_setup) = helpC (ESeq(rest, tag)) in
       (rest_ans, fst_setup @ [BSeq fst_ans] @ rest_setup)
    | ELet([], body, _) -> helpC body
    | ELet((bind, _, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, _) ->
       let (names, new_binds_setup) = List.split (List.map (fun (name, _, rhs, _) -> (name, helpC rhs)) binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (body_ans, (BLetRec (List.combine names new_binds)) :: body_setup)
    | ELambda(args, body, _) ->
       (CLambda(List.map fst args, helpA body, ()), [])
    | EApp(func, args, _) ->
       let (new_func, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CApp(new_func, new_args, ()), func_setup @ List.concat new_setup)
    | ETuple(args, _) ->
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CTuple(new_args, ()), List.concat new_setup)
    | EGetItem(tup, idx, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (CGetItem(tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem(tup, idx, rhs, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (rhs_imm, rhs_setup) = helpI rhs in
       (CSetItem(tup_imm, idx_imm, rhs_imm, ()), tup_setup @ idx_setup @ rhs_setup)
    | EGetItemExact(tup, idx, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       (CGetItem(tup_imm, ImmNum(idx, ()), ()), tup_setup)
    | ESetItemExact(tup, idx, rhs, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (rhs_imm, rhs_setup) = helpI rhs in
       (CSetItem(tup_imm, ImmNum(idx, ()), rhs_imm, ()), tup_setup @ rhs_setup)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])

    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "$unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [BLet(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "$binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [BLet(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "$if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [BLet(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args, tag) ->
       let tmp = sprintf "$app_%d" tag in
       let (new_func, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (func_setup @ List.concat new_setup) @ [BLet(tmp, CApp(new_func, new_args, ()))])
    | ESeq([], _) -> failwith "Impossible by syntax"
    | ESeq([stmt], _) -> helpI stmt
    | ESeq(fst :: rest, tag) ->
       let (fst_ans, fst_setup) = helpC fst in
       let (rest_ans, rest_setup) = helpI (ESeq(rest, tag)) in
       (rest_ans, fst_setup @ [BSeq fst_ans] @ rest_setup)
    | ELet([], body, _) -> helpI body
    | ELet((bind, _, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, tag) ->
       let tmp = sprintf "$lam_%d" tag in
       let (names, new_binds_setup) = List.split (List.map (fun (name, _, rhs, _) -> (name, helpC rhs)) binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (ImmId(tmp, ()), (List.concat new_setup)
                        @ [BLetRec (List.combine names new_binds)]
                        @ body_setup
                        @ [BLet(tmp, body_ans)])
    | ELambda(args, body, tag) ->
       let tmp = sprintf "$lam_%d" tag in
       (ImmId(tmp, ()), [BLet(tmp, CLambda(List.map fst args, helpA body, ()))])
    | ETuple(args, tag) ->
       let tmp = sprintf "$tup_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [BLet(tmp, CTuple(new_args, ()))])
    | EGetItem(tup, idx, tag) ->
       let tmp = sprintf "$get_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ [BLet(tmp, CGetItem(tup_imm, idx_imm, ()))])
    | ESetItem(tup, idx, rhs, tag) ->
       let tmp = sprintf "$set_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (rhs_imm, rhs_setup) = helpI rhs in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ rhs_setup @ [BLet(tmp, CSetItem(tup_imm, idx_imm, rhs_imm, ()))])
    | EGetItemExact(tup, idx, tag) ->
       let tmp = sprintf "$get_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       (ImmId(tmp, ()), tup_setup @ [BLet(tmp, CGetItem(tup_imm, ImmNum(idx, ()), ()))])
    | ESetItemExact(tup, idx, rhs, tag) ->
       let tmp = sprintf "$set_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (rhs_imm, rhs_setup) = helpI rhs in
       (ImmId(tmp, ()), tup_setup @ rhs_setup @ [BLet(tmp, CSetItem(tup_imm, ImmNum(idx, ()), rhs_imm, ()))])
  and helpA e : unit aexpr =
    let (ans, ans_setup) = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq(exp) -> ASeq(exp, body, ())
        | BLet(name, exp) -> ALet(name, exp, body, ())
        | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ACExpr ans)
  in
  helpP p
;;

(* A unification is a dictionary mapping type variable names to
   unifiables (from the BatUref library) containing types. *)
type unification = (string, (typ uref)) Hashtbl.t

(* Global type unification mutated while type-checking the program.
   It's easier to make this global than to properly pass it around everywhere. *)
let global_unif : unification = Hashtbl.create 0

(* The function bind ensures that we can't have infinite types (e.g., by trying to equate
   X with [X -> Y]), and updates the global unification environment to include the new
   type variable, if this occurs check passes. *)
exception OccursCheck of string
let bind (tyvarname : string) (t : typ) : unit =
  match t with
  | TyVar name when tyvarname = name -> () (* nothing to be done *)
  | _ ->
     if List.mem tyvarname (free_typ_tyvars t)
     then raise (OccursCheck (sprintf "Infinite types: %s occurs in %s" tyvarname (string_of_typ t)))
     else Hashtbl.add global_unif tyvarname (uref t)

(* Try to unify two types based on the known type equalities.
   Mutates the global unifcation environment to record the new equality.
   Returns the resulting unified type. *)
exception TypeError of string
let rec unify (t1 : typ) (t2 : typ) : typ =
  let rec choose_new_representative (t1 : typ) (t2 : typ) : typ =
    match t1, t2 with
    | TyCon(c1), TyCon(c2) when c1 = c2 -> t1
    | TyArr(args1, ret1), TyArr(args2, ret2) when (List.length args1) = (List.length args2) ->
      TyArr(List.map2 choose_new_representative args1 args2,
            choose_new_representative ret1 ret2)
    | TyTup(elts1), TyTup(elts2) when (List.length elts1) = (List.length elts2) ->
      TyTup(List.map2 choose_new_representative elts1 elts2)
    | _, TyVar(_) -> t1
    | TyVar(_), _ -> t2
    | _ ->
      raise (TypeError(sprintf "no common representative exists for %s and %s"
                         (string_of_typ t1)
                         (string_of_typ t2))) in
  match t1, t2 with
  (* If both types are constants, they need to be the same constant for
     unification to succeed. *)
  | TyCon(n1), TyCon(n2) when n1 = n2 -> t1

  (* If both are functions of the same arity, recur on the pieces and unify them. *)
  | TyArr(args1, ret1), TyArr(args2, ret2) when (List.length args1) = (List.length args2) ->
    TyArr(List.map2 unify args1 args2, unify ret1 ret2)

  (* If both are tuples of the same arity, recur on the pieces and unify them. *)
  | TyTup(elts1), TyTup(elts2) when (List.length elts1) = (List.length elts2) ->
    TyTup(List.map2 unify elts1 elts2)

  (* If both types are variables, find a representative for both of them. *)
  | TyVar(n1), TyVar(n2) ->
    if not (Hashtbl.mem global_unif n1)
    then (bind n1 t2; t2)
    else if not (Hashtbl.mem global_unif n2)
    then (bind n2 t1; t1)
    else
      let n1_ref = Hashtbl.find global_unif n1 in
      let n2_ref = Hashtbl.find global_unif n2 in
      unite ~sel:choose_new_representative n1_ref n2_ref;
      uget n1_ref

  (* If one type is a variable, it gets unified with the other type. *)
    | TyVar(n), t | t, TyVar(n) ->
    if not (Hashtbl.mem global_unif n)
    then (bind n t; t)
    else
      let n_ref = Hashtbl.find global_unif n in
      unite ~sel:choose_new_representative n_ref (uref t);
      uget n_ref

  (* All other scenarios are a type error. *)
  | _ ->
    raise (TypeError(sprintf "cannot unify type %s with type %s"
                            (string_of_typ t1)
                            (string_of_typ t2)))

(* assumes type variables are never given as numbers) *)
let gensym =
  let cnt = ref 0 in
  fun () ->
    cnt := !cnt + 1;
    sprintf "$tau_%d" !cnt

(* Return the substitution for the given symbol, or return the symbol if there isn't one *)
let apply_subst_symbol (subst : typ envt) (sym : string) : typ =
  let a = List.filter (fun (x, y) -> sym = x) subst in
  match a with
  | [] -> TyVar(sym)
  | (_, b)::_ -> b
;;

(* Rewrites all types in the given type based on the definitions we have in the substitution *)
let rec apply_subst_type (subst : typ envt) (typ : typ) : typ =
  match typ with
  | TyCon _ -> typ
  | TyVar(str) -> (apply_subst_symbol subst str)
  | TyArr(args, ret) -> TyArr((List.map (apply_subst_type subst) args),
                              (apply_subst_type subst ret))
  | TyTup(args) -> TyTup((List.map (apply_subst_type subst) args))
;;

(* Given a polymorphic type scheme, create some instantiation of it
   by making up brand new (gensym'ed) type variables for it,
   and substituting them where needed *)
let instantiate (scm : scheme) : typ =
  let (vars, typ) = scm in
  apply_subst_type (List.map (fun v -> (v, TyVar(gensym()))) vars) typ

(* Produce a TypeScheme that binds the free variables in the type
   (that do not appear in the TypeEnv) *)
let generalize (typ : typ) : scheme =
  let free_types = free_typ_tyvars typ in
  (List.filter (fun tv -> not (Hashtbl.mem global_unif tv)) free_types, typ)

let rec type_infer (gamma : scheme envt) (exp : 'a expr) : typ =
  match exp with
  | ENumber(_, _) -> TyCon("int")
  | EBool(_, _) -> TyCon("bool")
  | EId(name, _) -> instantiate (find gamma name)
  | ETuple(exps, _) -> TyTup(List.map (type_infer gamma) exps)

  | EPrim1(op, exp, _) ->
    let in_type = unify
        (type_infer gamma exp)
        (match op with
         | Add1 | Sub1 -> TyCon("int")
         | Not -> TyCon("bool")
         | Print | PrintStack | IsNum | IsBool | IsTuple -> TyVar(gensym())) in
    (match op with
     | Add1 | Sub1 -> TyCon("int")
     | Not | IsNum | IsBool | IsTuple -> TyCon("bool")
     | Print | PrintStack -> in_type)

  | EPrim2(op, left, right, _) ->
    let left_typ = unify
        (type_infer gamma left)
        (match op with
         | Plus | Minus | Times | Less | Greater | LessEq | GreaterEq -> TyCon("int")
         | And | Or -> TyCon("bool")
         | Eq -> TyVar(gensym())) in
    ignore(
      (* check the right type *)
      unify
        (type_infer gamma right)
        (match op with
         | Eq -> TyVar(gensym())
         | _ -> left_typ));
    (match op with
     | Plus | Minus | Times -> TyCon("int")
     | _ -> TyCon("bool"))

  | EIf(cond, thn, els, _) ->
    ignore(unify (type_infer gamma cond) (TyCon("bool")));
    unify (type_infer gamma thn) (type_infer gamma els)

  | EGetItem(tup, idx, _) ->
    let tup_typ = type_infer gamma tup in
    let elems =
      match tup_typ with
      | TyTup(elems) -> elems
      | _ -> raise (TypeError(sprintf "get expected tuple, given %s" (string_of_typ tup_typ))) in
    ignore(unify (type_infer gamma idx) (TyCon("int")));
    List.fold_left unify (TyVar(gensym())) elems

  | EGetItemExact(tup, idx, _) ->
    let tup_typ = type_infer gamma tup in
    let elems =
      match tup_typ with
      | TyTup(elems) -> elems
      | _ -> raise (TypeError(sprintf "get expected tuple, given %s" (string_of_typ tup_typ))) in
    if idx < 0 || idx > (List.length elems)
    then raise (TypeError(sprintf "invalid index %d for type %s" idx (string_of_typ tup_typ)))
    else List.nth elems idx

  | ESetItem(tup, idx, value, _) ->
    let tup_typ = type_infer gamma tup in
    let elems =
      match tup_typ with
      | TyTup(elems) -> elems
      | _ -> raise (TypeError(sprintf "set expected tuple, given %s" (string_of_typ tup_typ))) in
    ignore(unify (type_infer gamma idx) (TyCon("int")));
    List.fold_left unify (type_infer gamma value) elems

  | ESetItemExact(tup, idx, value, _) ->
    let tup_typ = type_infer gamma tup in
    let elems =
      match tup_typ with
      | TyTup(elems) -> elems
      | _ -> raise (TypeError(sprintf "set expected tuple, given %s" (string_of_typ tup_typ))) in
    if idx < 0 || idx > (List.length elems)
    then raise (TypeError(sprintf "invalid index %d for type %s" idx (string_of_typ tup_typ)))
    else unify (type_infer gamma value) (List.nth elems idx)

  | EApp(func, args, _) ->
    let func_typ = type_infer gamma func in
    let args_typ = List.map (type_infer gamma) args in
    (match unify func_typ (TyArr(args_typ, TyVar(gensym()))) with
     | TyArr(_, res_typ) -> res_typ
     | _ -> failwith "impossible")

  | ELambda(args, body, _) ->
    let arg_typs = List.map (fun (x, t) -> TyVar(x)) args in
    let new_gamma =
      List.fold_left2 (fun g (x, _) typ -> (x, ([], typ)) :: g) gamma args arg_typs in
    let body_typ = type_infer new_gamma body in
    TyArr(arg_typs, body_typ)

  | ELet([], body, _) -> type_infer gamma body
  | ELet((x, sopt, expr, _)::binds, body, t) ->
    let expected_type = match sopt with
      | None -> TyVar(x)
      | Some(scm) -> instantiate scm in
    let inferred_type = type_infer gamma expr in
    let annotated_type = unify inferred_type expected_type in
    type_infer ((x, generalize annotated_type) :: gamma) (ELet(binds, body, t))

  | ELetRec(binds, body, _) ->
    let new_gamma =
      List.fold_left (fun g (x, sopt, _, _) ->
          let x_scm = match sopt with
            | None -> ([x], TyVar(x))
            | Some(scm) -> scm in
          (x, x_scm) :: g)
        gamma
        binds in
    List.iter (fun (_, _, func, _) -> ignore(type_infer new_gamma func)) binds;
    type_infer new_gamma body

  | ESeq([], _) -> failwith "Impossible by syntax"
  | ESeq([exp], _) -> type_infer gamma exp
  | ESeq(exp::exps, t) ->
    ignore(type_infer gamma exp);
    type_infer gamma (ESeq(exps, t))
;;



let mov_if_needed dest src =
  if dest = src then []
  else [IMov(dest, src)]

(* To run on OSX, stack frames must be 16-byte aligned before making a `call` *)
let is_osx =
  (* Courtesy of http://stackoverflow.com/a/23003342 *)
  (let ic = Unix.open_process_in "uname" in
   let uname = input_line ic in
   let () = close_in ic in
   uname = "Darwin")

let esp_store = Reg(EDX)

let call (label : arg) args =
  let num_args = List.length args in
  let align_stack =
    if is_osx
    then [
      (* Note: this assumes arguments to a call will never be in EDX
         This fits our convention, which either leaves evaluated "answers" in
         EAX or immediately moves them onto the stack *)
      IInstrComment(IMov(esp_store, Reg(ESP)), "Saving ESP before 16-byte alignment");
      ISub(Reg(ESP), Const((num_args + 1) * word_size));
      IAnd(Reg(ESP), HexConst(0xFFFFFFF0));
    ]
    else [] in
  let push_args =
    if is_osx
    then
      List.flatten
        (List.mapi
           (fun i arg -> [
                IMov(Reg(ECX), arg);
                IMov(RegOffset(i * word_size, ESP), Reg(ECX));
              ])
           (args @ [esp_store]))
    else List.rev_map
        (fun arg ->
           match arg with
           | Sized _ -> IPush(arg)
           | _ -> IPush(Sized(DWORD_PTR, arg)))
        args in
  let unalign_stack =
    if is_osx
    then [IInstrComment(IPop(Reg(ESP)), "Restoring pre-aligned ESP")]
    else [] in
  let pop_args =
    if num_args = 0 then []
    else [IInstrComment(IAdd(Reg(ESP), Const(num_args * word_size)),
                        sprintf "Popping %d arguments" num_args)] in
  align_stack @ push_args @ [ ICall(label) ] @ pop_args @ unalign_stack

let reserve nwords tag =
  let ok = sprintf "memcheck_%d" tag in
  let size = Const((nwords + (nwords mod 2)) * word_size) in
  (* On OSX, ESP will get 16-byte aligned before the call to `try_gc',
     potentially introducing things-that-look-like-pointers onto the stack
     However, the pre-aligned ESP will be saved into a register in order for
     it to be restored post-call, so we push that instead of ESP itself *)
  let esp = if is_osx then esp_store else Reg(ESP) in
  [
    IMov(Reg(EAX), LabelContents("HEAP_END"));
    ISub(Reg(EAX), size);
    ICmp(Reg(EAX), Reg(ESI));
    IJge(Label(ok));
  ] @ (call (Label "try_gc") [esp; Reg(EBP); Reg(ESI); size]) @ [
    (* assume gc success if returning here, so EAX holds the new ESI value *)
    IMov(Reg(ESI), Reg(EAX));
    ILabel(ok);
    IMov(Reg(EAX), Reg(ESI));
    IAdd(Reg(ESI), size);
  ]

let rec compile_fun (args : string list)
    (freevars : string list)
    (body : tag aexpr)
    (check_types : bool)
  : (instruction list * instruction list * instruction list) =
  let count_vars e =
    let rec helpA e =
      match e with
      | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
      | ALetRec(binds, body, _) ->
        let max_in_binds = List.fold_left
            (fun max_acc (_, expr) ->
               (max (helpC expr) max_acc))
            min_int
            binds in
        (List.length binds) + (max max_in_binds (helpA body))
      | ASeq(first, rest, _) -> (max (helpC first) (helpA rest))
      | ACExpr e -> helpC e
    and helpC e =
      match e with
      | CIf(_, t, f, _) -> max (helpA t) (helpA f)
      | _ -> 0 in
    helpA e in

  let rec replicate x i =
    if i = 0 then []
    else x :: (replicate x (i - 1)) in

  (*
    General proper tail call implementation, copied from Diamondback:

    To support proper tail calls with an arbitrary number of arguments, we
    use a differnet calling convention from C's.

    Rather than placing arguments below the return address, our convention
    puts them above EBP. It is the caller's responsibility to put the return
    address, the old value of EBP (the caller's EBP), and the arguments to
    the call on the stack before jumping to the call, leaving ESP at the top
    of the last argument.

    Since arguments are a part of the callee's stack frame in this new
    convention, it is the callee's responsibility to clean up its arguments
    before popping the old EBP and returning.
  *)

  (* As part of our calling convention, the closure address will be the first argument *)
  let num_args = (List.length args) + 1 in
  let get_closure_addr = [IMov(Reg(EDX), RegOffset(~-word_size, EBP))] in
  let args_env =
    List.mapi (fun i a -> (a, RegOffset(~-(i + 2) * word_size, EBP))) args in

  (* Note: assumes the closure tag was stripped before it was pushed onto the stack *)
  let restore_free_vars = List.mapi
      (fun i _ -> IPush(Sized(DWORD_PTR, RegOffset((i + 3) * word_size, EDX))))
      freevars in
  let free_env = List.mapi
      (fun i f -> (f, RegOffset(~-(i + num_args + 1) * word_size, EBP)))
      freevars in
  let compiled =
    compile_aexpr body 1 (args_env @ free_env) (num_args + (List.length freevars)) true check_types in
  let count_local_vars = count_vars body in
  let setup_stack = (replicate (IPush(Sized(DWORD_PTR, Const(0)))) count_local_vars) in
  let prologue = [
    ILineComment("Function prologue");
  ]
    @ get_closure_addr
    @ restore_free_vars
    @ setup_stack in
  let body = [ILineComment("Function body")] @ compiled in
  let epilogue = [
    (* Note: if we jump on a tail call to another function we'll never hit
       these instructions, but we always generate them to be safe *)
    ILineComment("Function epilogue");
    IMov(Reg(ESP), Reg(EBP));
    IPop(Reg(EBP));
    IRet;
  ] in
  (prologue, body, epilogue)

and compile_closure (args : string list)
    (freevars : string list)
    (body : 'a aexpr)
    (tag : tag)
    (env : arg envt)
    (closure : arg option)
    (check_types : bool)
  : instruction list =
  let fun_start = sprintf "lambda_%d_start" tag in
  let fun_end = sprintf "lambda_%d_end" tag in
  let words_needed = 3 + (List.length freevars) in
  let (prologue, body, epilogue) = compile_fun args freevars body check_types in
  let get_closure_loc = match closure with
    | None -> (reserve words_needed tag)
    | Some(arg) ->
      (mov_if_needed (Reg(EAX)) arg) @ [ISub(Reg(EAX), HexConst(closure_tag))] in
  let free_moves =
    List.flatten
      (List.mapi
         (fun i var -> [
              IMov(Reg(ECX), (find env var));
              IMov(RegOffset((i + 3) * word_size, EAX), Reg(ECX));
            ])
         freevars) in
  [
    IJmp(Label(fun_end));
    ILabel(fun_start);
  ] @ prologue @ body @ epilogue @ [
    ILabel(fun_end);
  ] @ get_closure_loc @ [
    (* For GC, store the size of the closure - 1 in the first word of the allocated
       space, mimicking what is done for tuples and allowing us to have a uniform
       process for determining how many words to copy *)
    IMov(RegOffset(0, EAX), Sized(DWORD_PTR, Const(words_needed - 1)));
    IMov(RegOffset(word_size, EAX), Sized(DWORD_PTR, Const(List.length args)));
    IMov(RegOffset(2 * word_size, EAX), Sized(DWORD_PTR, Label(fun_start)));
  ] @ free_moves @ [
    IAdd(Reg(EAX), HexConst(closure_tag));
  ]

and compile_aexpr (expr : tag aexpr)
    (si : int)
    (env : arg envt)
    (num_args : int)
    (is_tail : bool)
    (check_types : bool)
  : instruction list =
  match expr with
  | ALet(id, bind, body, _) ->
    let prelude = compile_cexpr bind (si + 1) env num_args false check_types in
    let id_offset = RegOffset(~-(num_args + si) * word_size, EBP) in
    let compiled_body =
      compile_aexpr body (si + 1) ((id, id_offset)::env) num_args is_tail check_types in
    prelude
    @ [IMov(id_offset, Reg(EAX))]
    @ compiled_body
  | ALetRec(binds, body, _) ->
    let rec allocate_lambdas (binds : (string * tag cexpr) list)
        (si_acc : int)
        (instr_acc : instruction list)
        (env_acc : arg envt)
        (free_acc : (string list) envt)
      : (int * instruction list * arg envt * (string list) envt) =
      match binds with
      | (f, CLambda(fargs, fbody, ftag))::rest ->
        let freevars = free_vars (ACExpr(CLambda(fargs, fbody, ftag))) in
        let words_needed = 3 + (List.length freevars) in
        let get_closure_addr = reserve words_needed ftag in
        let closure_offset = RegOffset(~-(num_args + si_acc) * word_size, EBP) in
        allocate_lambdas rest
          (si_acc + 1)
          (instr_acc @ get_closure_addr @ [
              IMov(RegOffset(0, EAX), Sized(DWORD_PTR, Const(words_needed - 1)));
              IAdd(Reg(EAX), HexConst(closure_tag));
              IMov(closure_offset, Reg(EAX));
            ])
          ((f, closure_offset) :: env_acc)
          ((f, freevars) :: free_acc)
      | _ -> (si_acc, instr_acc, env_acc, free_acc) in

    let rec compile_lambdas (binds: (string * tag cexpr) list)
        (env: arg envt)
        (free_env : (string list) envt)
      : instruction list =
      match binds with
      | (f, CLambda(fargs, fbody, ftag))::rest ->
        (compile_closure fargs
           (find free_env f)
           fbody
           ftag
           env
           (Some(find env f))
           check_types)
        @ (compile_lambdas rest env free_env)
      | _ -> [] in

    let (next_si, alloc_instrs, new_env, freevars) =
      allocate_lambdas binds si [] env [] in

    alloc_instrs
    @ (compile_lambdas binds new_env freevars)
    @ (compile_aexpr body next_si new_env num_args is_tail check_types)
  | ASeq(first, rest, _) ->
    let compiled_first = compile_cexpr first si env num_args false check_types in
    let compiled_rest = compile_aexpr rest si env num_args is_tail check_types in
    compiled_first @ compiled_rest
  | ACExpr e -> compile_cexpr e si env num_args is_tail check_types

and compile_cexpr (expr : tag cexpr)
    (si : int)
    (env : arg envt)
    (num_args : int)
    (is_tail : bool)
    (check_types : bool)
  : instruction list =
  let check_tag err scratch arg tag =
    if check_types
    then []
    else
      (mov_if_needed scratch arg)
      @ [
        IShl(scratch, Const(29));
        ICmp(scratch, HexConst(tag lsl (29)));
        IJne(Label(err));
      ] in
  let check_num err arg =
    if check_types
    then []
    else
      [
        ITest(Sized(DWORD_PTR, arg), HexConst(1));
        IJnz(Label(err));
      ] in
  let check_nums err left right =
    check_num err left @ check_num err right in
  let check_bool err scratch arg =
    check_tag err scratch arg bool_tag in
  let check_bools err scratch left right =
    check_bool err scratch left @ check_bool err scratch right in
  let check_tuple err scratch arg =
    check_tag err scratch arg tuple_tag in
  let check_overflow err =
    [IJo(Label(err))] in
  match expr with
  | CPrim1(op, e, tag) ->
    let e_reg = compile_imm e env in
    (mov_if_needed (Reg EAX) e_reg)
    @ (match op with
        | Add1 ->
          (check_num "err_arith_not_num" (Reg EAX))
          @ [IAdd(Reg(EAX), Const(2))]
          @ (check_overflow "err_overflow")
        | Sub1 ->
          (check_num "err_arith_not_num" (Reg EAX))
          @ [ISub(Reg(EAX), Const(2))]
          @ (check_overflow "err_overflow")
        | IsBool ->
          [
            IMov(Reg(ECX), Reg(EAX));
            IMov(Reg(EAX), Const(1));
            IAnd(Reg(ECX), Const(7));
            IShl(Reg(EAX), Reg(CL));
            IShl(Reg(EAX), Const(24));
            IOr(Reg(EAX), const_false);
          ]
        | IsNum ->
          [
            IShl(Reg(EAX), Const(31));
            IXor(Reg(EAX), const_true);
          ]
        | IsTuple ->
          [
            IMov(Reg(ECX), Reg(EAX));
            IMov(Reg(EAX), Const(1));
            IAnd(Reg(ECX), Const(7));
            IShl(Reg(EAX), Reg(CL));
            IShl(Reg(EAX), Const(30));
            IOr(Reg(EAX), const_false);
          ]
        | Not ->
          (check_bool "err_logic_not_bool" (Reg EDX) (Reg EAX))
          @ [IXor(Reg(EAX), bool_mask)]
        | Print -> call (Label "print") [Reg(EAX)]
        | PrintStack -> failwith "NYI: printStack")
  | CPrim2(op, left, right, tag) ->
    let left_reg = compile_imm left env in
    let right_reg = compile_imm right env in
    let arith_op op =
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ check_nums "err_arith_not_num" (Reg EAX) (Reg EDX)
      @ [ op (Reg(EAX), Reg(EDX)) ]
      @ check_overflow "err_overflow" in
    let comp_op op =
      let true_label = sprintf "true_%d" tag in
      let done_label = sprintf "done_%d" tag in
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ (check_nums "err_comp_not_num" (Reg EAX) (Reg EDX))
      @ [
        IMov(Reg(EAX), left_reg);
        ICmp(Reg(EAX), right_reg);
        IMov(Reg(EAX), const_false);
        op done_label;
        ILabel(true_label);
        IMov(Reg(EAX), const_true);
        ILabel(done_label);
      ] in
    let logic_op op =
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ (check_bools "err_logic_not_bool" (Reg ECX) (Reg EAX) (Reg EDX))
      @ [
        IMov(Reg(EAX), left_reg);
        op (Reg(EAX), right_reg)
      ] in
    (match op with
        | Plus -> arith_op (fun (dest, src) -> IAdd(dest, src))
        | Minus -> arith_op (fun (dest, src) -> ISub(dest, src))
        | Times ->
          (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
          @ check_nums "err_arith_not_num" (Reg EAX) (Reg EDX)
          @ [ ISar(Reg(EAX), Const(1)); IMul(Reg(EAX), Reg(EDX)) ]
          @ check_overflow "err_overflow"
        | Less -> comp_op (fun dest -> IJge (Label dest))
        | Greater -> comp_op (fun dest -> IJle (Label dest))
        | LessEq -> comp_op (fun dest -> IJg (Label dest))
        | GreaterEq -> comp_op (fun dest -> IJl (Label dest))
        | Eq ->
          let true_label = sprintf "true_%d" tag in
          let done_label = sprintf "done_%d" tag in
          (mov_if_needed (Reg EAX) left_reg) @
          [
            ICmp(Reg(EAX), right_reg);
            IMov(Reg(EAX), const_false);
            IJne(Label(done_label));
            ILabel(true_label);
            IMov(Reg(EAX), const_true);
            ILabel(done_label)
          ]
        | And -> logic_op (fun (dest, src) -> IAnd(dest, src))
        | Or -> logic_op (fun (dest, src) -> IOr(dest, src)))
  | CImmExpr i -> [IMov(Reg(EAX), compile_imm i env)]
  | CIf(cond, thn, els, tag) ->
    let cond_reg = compile_imm cond env in
    let else_label = sprintf "else_%d" tag in
    let end_label = sprintf "end_%d" tag in
    (mov_if_needed (Reg EAX) cond_reg)
    @ (check_bool "err_if_not_bool" (Reg ECX) (Reg EAX))
    @ [
      ICmp(Reg(EAX), const_true);
      IJne(Label(else_label));
    ]
    @ (compile_aexpr thn si env num_args is_tail check_types)
    @ [ IJmp(Label(end_label)); ILabel(else_label) ]
    @ (compile_aexpr els si env num_args is_tail check_types)
    @ [ ILabel(end_label) ]
  | CTuple(elts, tag) ->
    let num_elts = List.length elts in
    let elt_movs = List.flatten (List.mapi (fun i elt ->
        let compiled_elt = compile_imm elt env in [
          IMov(Reg(ECX), Sized(DWORD_PTR, compiled_elt));
          IMov(Sized(DWORD_PTR, RegOffset((i + 1) * word_size, EAX)), Reg(ECX));
        ])
        elts) in
    (reserve (1 + num_elts) tag)
    @ [
      (* Move the element count into the tuple's head tag *)
      IMov(RegOffset(0, EAX), Sized(DWORD_PTR, Const(num_elts)));
    ] @ elt_movs @ [
      (* Tag the tuple's pointer before moving on *)
      IAdd(Reg(EAX), HexConst(tuple_tag));
    ]
  | CGetItem(tup, index, _) ->
    let tup_reg = compile_imm tup env in
    let index_reg = compile_imm index env in
    (mov_if_needed (Reg(EAX)) tup_reg)
    @ (check_tuple "err_get_not_tuple" (Reg(ECX)) (Reg(EAX)))
    @ (mov_if_needed (Reg(EDX)) index_reg)
    @ (check_num "err_index_not_num" (Reg(EDX)))
    @ [
      (* Make sure the index is nonnegative *)
      ICmp(Reg(EDX), Const(0));
      IJl(Label("err_get_low_index"));
      (* Wipe the tag off the pointer *)
      ISub(Reg(EAX), HexConst(tuple_tag));
      (* Make sure the index isn't larger than the size of the tuple *)
      IMov(Reg(ECX), RegOffset(0, EAX));
      ISar(Reg(EDX), Const(1));
      ICmp(Reg(EDX), Reg(ECX));
      IJge(Label("err_get_high_index"));
      (* Get the tuple element *)
      IAdd(Reg(EDX), Const(1));
      IMov(Reg(EAX), RegOffsetReg(EAX, EDX, word_size, 0));
    ]
  | CSetItem(tup, index, new_val, _) ->
    let tup_loc = compile_imm tup env in
    let index_loc = compile_imm index env in
    let new_val_loc = compile_imm new_val env in
    (mov_if_needed (Reg(ECX)) tup_loc)
    @ (check_tuple "err_set_not_tuple" (Reg(EAX)) (Reg(ECX)))
    @ (mov_if_needed (Reg(EDX)) index_loc)
    @ (check_num "err_index_not_num" (Reg(EDX)))
    @ [
      (* Make sure the index is nonnegative *)
      ICmp(Reg(EDX), Const(0));
      IJl(Label("err_get_low_index"));
      (* Wipe the tag off the pointer *)
      ISub(Reg(ECX), HexConst(tuple_tag));
      (* Make sure the index isn't larger than the size of the tuple *)
      IMov(Reg(EAX), RegOffset(0, ECX));
      ISar(Reg(EDX), Const(1));
      ICmp(Reg(EDX), Reg(EAX));
      IJge(Label("err_get_high_index"));
    ] @ (mov_if_needed (Reg(EAX)) new_val_loc) @ [
      (* Set the tuple element *)
      IAdd(Reg(EDX), Const(1));
      IMov(RegOffsetReg(ECX, EDX, word_size, 0), Reg(EAX));
    ]
  | CLambda(args, body, tag) ->
    let freevars = free_vars (ACExpr(expr)) in
    compile_closure args freevars body tag env None check_types
  | CApp(func, args, tag) ->
    (*
      General proper tail call implementation, copied from Diamondback:

      To support proper tail calls with an arbitrary number of arguments, we
      use a differnet calling convention from C's.

      Rather than placing arguments below the return address, our convention
      puts them above EBP. It is the caller's responsibility to put the return
      address, the old value of EBP (the caller's EBP), and the arguments to
      the call on the stack before jumping to the call, leaving ESP at the top
      of the last argument.

      Since arguments are a part of the callee's stack frame in this new
      convention, it is the callee's responsibility to clean up its arguments
      before popping the old EBP and returning.
    *)
    let num_args = (List.length args) + 1 in
    let get_closure =
      (mov_if_needed (Reg(EAX)) (compile_imm func env))
      @ (check_tag "err_call_not_function" (Reg(ECX)) (Reg(EAX)) closure_tag)
      @ [ISub(Reg(EAX), HexConst(closure_tag))] in
    let check_arity =
      if check_types
      then []
      else [
        IMov(Reg(ECX), RegOffset(word_size, EAX));
        ICmp(Reg(ECX), Const(num_args - 1));
        IJne(Label("err_call_bad_arity"));
      ] in
    (* Both tail- and non-tail-calls will require pushing call arguments onto
       the stack, but the setup / teardown around the pushing will be different. *)
    let arg_pushes =
      [IPush(Reg(EAX))]
      @ List.map (fun arg -> IPush(Sized(DWORD_PTR, compile_imm arg env))) args in
    let fun_loc = RegOffset(2 * word_size, EAX) in
    let call_body =
      if is_tail
      then
        (*
          To make proper tail calls, we:
          1. Push all call arguments onto the stack. We perform this
             intermediate step (rather than immediately overwriting the
             locations above our EBP with the new call args) to ensure that
             we don't munge any of our own arguments which might be needed
             to calculate arguments of the call.
          2. Move each argument, in order from first to last, into its
             designated slot above EBP. The first-to-last order is important
             because the arguments for the tail call might grow far enough on
             the stack to overwrite the values we just pushed, but if they do
             then they'll only overwrite arguments that have already been
             copied.
          3. Move ESP back to EBP, then decrement it by one word for each of
             the args that were just placed above EBP, placing it at the top
             of the last arg.
          4. Jump to the function being tail-called.
        *)
        let arg_moves =
          List.flatten
            (List.mapi
               (fun i _ -> [
                    (* It's not possible to move directly from one memory location to
                       another, so we need an intermediate stop in a register *)
                    IMov(Reg(ECX), RegOffset((num_args - (i + 1)) * word_size, ESP));
                    IMov(RegOffset(~-(i + 1) * word_size, EBP), Reg(ECX));
                  ])
               arg_pushes) in
        arg_pushes @ arg_moves @ [
          IMov(Reg(ESP), Reg(EBP));
          ISub(Reg(ESP), Const(num_args * word_size));
          IJmp(fun_loc);
        ]
      else
        (*
          For non-tail-calls, we:
          1. Push the name of a return label we'll generate later onto
             the stack to serve as the return address for the called function.
          2. Push the current EBP onto the stack.
          3. Push all call arguments onto the stack.
          4. Move EBP to ESP, then increment it by one word for each of the
             args that were just pushed, placing it at the bottom of the
             first arg.
          5. Jump to the function being called.

          The label whose name is pushed in 1. is placed just after the jump
          instruction in 5. to ensure the call returns to the correct location.
        *)
        let ret_label = sprintf "call_%d_ret" tag in
        [
          IPush(Label(ret_label));
          IPush(Reg(EBP));
        ] @ arg_pushes @ [
          IMov(Reg(EBP), Reg(ESP));
          IAdd(Reg(EBP), Const(num_args * word_size));
          IJmp(fun_loc);
          ILabel(ret_label);
        ] in
    get_closure
    @ check_arity
    @ call_body

and compile_imm (expr : tag immexpr) (env : arg envt) : arg =
  match expr with
  | ImmNum(n, _) -> Const(n lsl 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)

let compile_prog anfed check_types =
  let prelude =
    "section .text
extern error
extern print
extern equal
extern try_gc
extern HEAP_END
extern STACK_BOTTOM
global our_code_starts_here" in
  let suffix = sprintf "
err_comp_not_num:%s
err_arith_not_num:%s
err_logic_not_bool:%s
err_if_not_bool:%s
err_overflow:%s
err_get_not_tuple:%s
err_get_low_index:%s
err_get_high_index:%s
err_index_not_num:%s
err_call_not_function:%s
err_call_bad_arity:%s
err_set_not_tuple:%s"
      (* If you modified `call` above, then fix these up, too *)
      (to_asm (call (Label "error") [Const(err_COMP_NOT_NUM)]))
      (to_asm (call (Label "error") [Const(err_ARITH_NOT_NUM)]))
      (to_asm (call (Label "error") [Const(err_LOGIC_NOT_BOOL)]))
      (to_asm (call (Label "error") [Const(err_IF_NOT_BOOL)]))
      (to_asm (call (Label "error") [Const(err_OVERFLOW)]))
      (to_asm (call (Label "error") [Const(err_GET_NOT_TUPLE)]))
      (to_asm (call (Label "error") [Const(err_GET_LOW_INDEX)]))
      (to_asm (call (Label "error") [Const(err_GET_HIGH_INDEX)]))
      (to_asm (call (Label "error") [Const(err_INDEX_NOT_NUM)]))
      (to_asm (call (Label "error") [Const(err_CALL_NOT_FUNC)]))
      (to_asm (call (Label "error") [Const(err_CALL_BAD_ARITY)]))
      (to_asm (call (Label "error") [Const(err_SET_NOT_TUPLE)]))
  in
  let (prologue, comp_main, epilogue) = compile_fun [] [] anfed check_types in
  (* Since we use a different calling convention than C, we need to do some
     extra steps manually to compile our main entry point function *)
  let extra_setup = [
    ILabel("our_code_starts_here");
    ILineComment("save old EBP, since C expects us to do it");
    IPush(Reg(EBP));
    IMov(Reg(EBP), Reg(ESP));
    IInstrComment(IPush(HexConst(0x0)), "fake closure pointer");
    IInstrComment(IMov(LabelContents("STACK_BOTTOM"), Reg(EBP)),
                  "This is the bottom of our Snake stack");
    ILineComment("heap start");
    IInstrComment(IMov(Reg(ESI), RegOffset(2 * word_size, EBP)),
                  "Load ESI with our argument, the heap pointer");
  ] in
  let main = (extra_setup @ prologue @ comp_main @ epilogue) in
  sprintf "%s%s%s\n" prelude (to_asm main) suffix

let compile_to_string prog (check_types : bool) (verbose : bool) : (exn list, string) either =
  let env = [ (* DBuiltin("equal", 2) *) ] in
  let errors = well_formed prog env check_types in
  match errors with
  | [] ->
    let tagged : tag program = tag prog in
    begin
      try
        if check_types
        then begin
          Hashtbl.clear global_unif;
          (* Infer the program's type, but ignore the result.
             The only thing we care about is that the process
             doesn't raise an error. *)
          ignore(type_infer [] tagged);
        end;
        let anfed : tag aprogram = atag (anf tagged) in
        let optimized : tag aprogram =
          optimize anfed verbose true true true (* Run all optimizations. *) in
        Right(compile_prog optimized check_types)
      with | err -> Left([err])
    end
  | _ -> Left(errors)
