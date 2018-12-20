open Types
open Expr
open Pretty
open Printf

let free_vars (e : 'a aexpr) : string list =
  let rec helpA (bound : string list) (e : 'a aexpr) : string list =
     match e with
     | ASeq(fst, rest, _) ->
        helpC bound fst @ helpA bound rest
     | ALet(name, binding, body, _) ->
       (helpC bound binding) (* all the free variables in the binding, plus *)
       (* all the free variables in the body, except the name itself *)
       @ (helpA (name :: bound) body)
     | ALetRec(bindings, body, _) ->
        let names = List.map fst bindings in
        let new_bound = (names @ bound) in
        (helpA new_bound body) @ List.flatten (List.map (fun binding -> helpC new_bound (snd binding)) bindings)
     | ACExpr c -> helpC bound c
  and helpC (bound : string list) (e : 'a cexpr) : string list =
    match e with
    | CLambda(args, body, _) ->
      helpA (args @ bound) body
    | CIf(cond, thn, els, _) ->
      helpI bound cond @ helpA bound thn @ helpA bound els
    | CPrim1(_, arg, _) -> helpI bound arg
    | CPrim2(_, left, right, _) -> helpI bound left @ helpI bound right
    | CApp(fn, args, _) ->
      (helpI bound fn) @ (List.flatten (List.map (fun arg -> helpI bound arg) args))
    | CTuple(vals, _) -> List.flatten (List.map (fun v -> helpI bound v) vals)
    | CGetItem(tup, idx, _) -> helpI bound tup @ helpI bound idx
    | CSetItem(tup, idx, rhs, _) -> helpI bound tup @ helpI bound idx @ helpI bound rhs
    | CImmExpr i -> helpI bound i
  and helpI (bound : string list) (e : 'a immexpr) : string list =
    match e with
    | ImmId(name, _) ->
      (* a name is free if it is not bound *)
      if List.mem name bound then [] else [name]
    | _ -> []
  in List.sort_uniq String.compare (helpA [] e)
;;

let purity_env (prog : tag aprogram) : (string, bool) Hashtbl.t =
  let ans : (string, bool) Hashtbl.t = Hashtbl.create 0 in
  let call_purity : (string, bool) Hashtbl.t = Hashtbl.create 0 in

  let rec helpA (aexp : tag aexpr) (binding_to_name : string option) : bool =
    match aexp with
    | ALet(s, cexp, aexp, _) ->
      let binding_s_is_pure = helpC cexp (Some s) in
      (* special case for setting functions to eachother*)
      (match cexp with
      | CImmExpr(ImmId(st, _)) -> if Hashtbl.mem call_purity st
                                  then (Hashtbl.replace call_purity s (Hashtbl.find call_purity st))
                                  else ()
      | _ -> ());
      Hashtbl.replace ans s binding_s_is_pure;
      (helpA aexp binding_to_name) && binding_s_is_pure
    | ALetRec(binds, body, _) ->
      List.iter (fun (f, _) ->
          Hashtbl.replace ans f false;
          Hashtbl.replace call_purity f true)
        binds;
      let rec converge_purity () : unit =
        let purity_changed = ref false in
        List.iter
          (fun (f, func) ->
             let pre_func_purity = Hashtbl.find call_purity f in
             ignore(helpC func (Some f));
             if (Hashtbl.find call_purity f) != pre_func_purity
             then purity_changed := true)
          binds;
        if !purity_changed then converge_purity() in
      converge_purity();
      ignore(helpA body binding_to_name);
      false
    | ASeq(cexp, aexp, ta) ->
      let evaluating_first_is_pure = helpC cexp None in
      (* We create a name for the first expression, so we know
         later if we can eliminate it or not. *)
      let first_label = sprintf "$seq_%d" ta in
      Hashtbl.replace ans first_label evaluating_first_is_pure;
      (helpA aexp binding_to_name) && evaluating_first_is_pure
    | ACExpr(cexp) -> helpC cexp binding_to_name
  and helpC (cexp : tag cexpr) (binding_to_name : string option) : bool =
    match cexp with
    | CImmExpr(_) -> true
    | CPrim1(p, a, _) ->
      (match p, a with
             | Print, _ | PrintStack, _
             | Add1, ImmBool(_) | Sub1, ImmBool(_)
             | Not, ImmNum(_) -> false
             | _, _ -> true)
    (* looking for obvious type errors here and marking them impure *)
    | CPrim2(p, a1, a2, _) ->
      (match p with
       | Plus | Minus | Times | Less | Greater | LessEq | GreaterEq ->
         (match a1, a2 with
          | ImmBool(_), _ | _, ImmBool(_) -> false
          | _, _ -> true)
       | And | Or ->
         (match a1, a2 with
          | ImmNum(_), _ | _, ImmNum(_) -> false
          | _, _ -> true)
       | _ -> true)
    | CGetItem(tup, idx, _) ->
      (match tup, idx with
       | ImmId(_), ImmId(_)
       | ImmId(_), ImmNum(_) -> true
       | _, _ -> false)
    | CIf(c, t, f, _) ->
      let an1 = (helpA t binding_to_name) in
      let an2 = (helpA f binding_to_name) in
      (match c with
       | ImmNum(_) -> false
       | ImmBool(b, _) -> if b
                       then an1
                       else an2
       | ImmId(_) -> an1 && an2)
    | CLambda(args, body, _) ->
      (* Without a proper effect system, there's no sane way to figure out the
         purities of functions returned from higher-order functions, i.e.:

         let f = (lambda x: (lambda: if random_bool(): x else: print(x))) in
         let y = f(10) in
         let z = y() in (* Not used, can we eliminate??? *)
         20

         We bind function names to the purities of calling their bodies where
         possible, and use those entries to figure out the purities of calls to
         those functions. If we do see a call to an ID we don't know the purity
         of calling, we just assume it's impure to be safe. *)
      List.iter (fun x -> Hashtbl.replace call_purity x true) args;
      List.iter (fun x -> Hashtbl.replace ans x true) args;
      begin match binding_to_name with
        | Some(f) ->
          Hashtbl.replace call_purity f ((helpA body None) &&
                                         ((not (Hashtbl.mem call_purity f)) ||
                                          (Hashtbl.find call_purity f)))

        | None ->
          ignore((helpA body None))
      end;
      true
    | CApp(ImmId(f, _), _, _) when Hashtbl.mem call_purity f ->
      Hashtbl.find call_purity f
    | _ -> false
  in ignore(helpA prog None);
  ans
;;

let const_fold (prog : tag aprogram) : unit aprogram =
  let constants : (string, simple_expr) Hashtbl.t = Hashtbl.create 0 in
  let simple_funs : (string, (string list * simple_expr)) Hashtbl.t = Hashtbl.create 0 in
  let rec helpS (expr : simple_expr) : simple_expr =
    match expr with
    | Num(_) | Bool(_) -> expr
    | Id(x) ->
      if Hashtbl.mem constants x
      then Hashtbl.find constants x
      else expr
    | App(func, args) ->
      let folded_func = helpS func in
      let folded_args = List.map helpS args in
      begin match folded_func with
        | Id(f) ->
          if Hashtbl.mem simple_funs f
          then
            let fun_args, fun_body = Hashtbl.find simple_funs f in
            List.iter2 (fun x a -> Hashtbl.replace constants x a) fun_args args;
            helpS fun_body
          else App(folded_func, folded_args)
        | _ -> App(folded_func, folded_args)
      end
    | Fun(args, body) -> Fun(args, helpS body)
    | Prim1(op, arg) ->
      let folded_arg = helpS arg in
      begin match op, folded_arg with
        | Add1, Num(n) when (n + 1) <= max_int -> Num(n + 1)
        | Sub1, Num(n) when (n - 1) >= min_int -> Num(n - 1)
        | Not, Bool(b) -> Bool(not b)
        | IsNum, Num(_) -> Bool(true)
        | IsNum, Bool(_) -> Bool(false)
        | IsBool, Num(_) -> Bool(false)
        | IsBool, Bool(_) -> Bool(true)
        | IsTuple, Num(_) | IsTuple, Bool(_) -> Bool(false)
        | _ -> Prim1(op, folded_arg)
      end
    | Prim2(op, arg1, arg2) ->
      let folded_arg1 = helpS arg1 in
      let folded_arg2 = helpS arg2 in
      begin match op, folded_arg1, folded_arg2 with
        | Plus, Num(n1), Num(n2) ->
          let folded = n1 + n2 in
          if (folded < min_int) || (folded > max_int)
          then Prim2(op, folded_arg1, folded_arg2)
          else Num(folded)
        | Minus, Num(n1), Num(n2) ->
          let folded = n1 - n2 in
          if (folded < min_int) || (folded > max_int)
          then Prim2(op, folded_arg1, folded_arg2)
          else Num(folded)
        | Times, Num(n1), Num(n2) ->
          let folded = n1 * n2 in
          if (folded < min_int) || (folded > max_int)
          then Prim2(op, folded_arg1, folded_arg2)
          else Num(folded)
        | Plus, Num(0), Id(x) | Plus, Id(x), Num(0)
        | Minus, Id(x), Num(0)
        | Times, Num(1), Id(x) | Times, Id(x), Num(1) -> Id(x)
        | Times, Num(0), Id(_) | Times, Id(_), Num(0) -> Num(0)
        | Less, Num(n1), Num(n2) -> Bool(n1 < n2)
        | Greater, Num(n1), Num(n2) -> Bool(n1 > n2)
        | LessEq, Num(n1), Num(n2) -> Bool(n1 <= n2)
        | GreaterEq, Num(n1), Num(n2) -> Bool(n1 >= n2)
        | Eq, Num(n1), Num(n2) -> Bool(n1 = n2)
        | Eq, Bool(b1), Bool(b2) -> Bool(b1 = b2)
        | Eq, Num(_), Bool(_) | Eq, Bool(_), Num(_) -> Bool(false)
        | And, Bool(b1), Bool(b2) -> Bool(b1 && b2)
        | Or, Bool(b1), Bool(b2) -> Bool(b1 || b2)
        | And, Bool(true), Id(x) | And, Id(x), Bool(true)
        | Or, Bool(false), Id(x) | Or, Id(x), Bool(false) -> Id(x)
        | And, Bool(false), Id(_) | And, Id(_), Bool(false) -> Bool(false)
        | Or, Bool(true), Id(_) | Or, Id(_), Bool(true) -> Bool(true)
        | _ -> Prim2(op, folded_arg1, folded_arg2)
      end

  and helpI (imm : tag immexpr) : unit immexpr =
    match simple_to_cexpr (helpS (imm_to_simple imm)) with
    | CImmExpr(i) -> i
    | _ -> failwith "Impossible"

  and helpC (expr : tag cexpr) : unit aexpr =
    match cexpr_to_simple_opt expr with
    | Some(sexpr) -> ACExpr(simple_to_cexpr (helpS sexpr))
    | None ->
      match expr with
      | CTuple(elts, _) -> ACExpr(CTuple(List.map helpI elts, ()))
      | CGetItem(tup, idx, _) -> ACExpr(CGetItem(helpI tup, helpI idx, ()))
      | CSetItem(tup, idx, rhs, _) -> ACExpr(CSetItem(helpI tup, helpI idx, helpI rhs, ()))
      | CLambda(args, body, _) -> ACExpr(CLambda(args, helpA body, ()))
      | CIf(cond, thn, els, _) ->
        let folded_cond = helpI cond in
        let folded_thn = helpA thn in
        let folded_els = helpA els in
        begin match folded_cond with
          | ImmBool(b, _) -> if b then folded_thn else folded_els
          | _ -> ACExpr(CIf(folded_cond, folded_thn, folded_els, ()))
        end
      | _ -> failwith "Impossible"

  and helpA (expr : tag aexpr) : unit aexpr =
    match expr with
    | ALet(x, bind, body, _) ->
      let rec raise_aexprs (folded_aexp : unit aexpr) : unit aexpr =
        match folded_aexp with
        | ACExpr(cexp) ->
          begin match cexp with
            | CImmExpr(imm) ->
              begin match imm with
                | ImmNum(_) | ImmBool(_) ->
                  Hashtbl.add constants x (imm_to_simple imm)
                | _ -> ()
              end
            | CLambda(_) ->
              begin match cexpr_to_simple_opt cexp with
                | Some(simple_fun) ->
                  begin match simple_fun with
                    | Fun(args, simple_body) ->
                      Hashtbl.replace simple_funs x (args, simple_body)
                    | _ -> failwith "Impossible"
                  end
                | None -> ()
              end
            | _ -> ()
          end;
          ALet(x, cexp, helpA body, ())
        | ALet(y, folded_bind, folded_body, _) ->
          ALet(y, folded_bind, raise_aexprs folded_body, ())
        | ALetRec(folded_funs, folded_body, _) ->
          ALetRec(folded_funs, raise_aexprs folded_body, ())
        | ASeq(folded_first, folded_rest, _) ->
          ASeq(folded_first, raise_aexprs folded_rest, ()) in
      raise_aexprs (helpC bind)
    | ALetRec(binds, body, _) ->
      let folded_binds = List.map
          (fun (f, func) -> match helpC func with
             | ACExpr(folded_func) -> (f, folded_func)
             | _ -> failwith "Impossible by well-formedness")
          binds in
      ALetRec(folded_binds, helpA body, ())
    | ASeq(expr, rest, _) ->
      let rec raise_aexprs (folded_aexp : unit aexpr) : unit aexpr =
        match folded_aexp with
        | ACExpr(cexp) -> ASeq(cexp, helpA rest, ())
        | ALet(y, folded_bind, folded_body, _) ->
          ALet(y, folded_bind, raise_aexprs folded_body, ())
        | ALetRec(folded_funcs, folded_body, _) ->
          ALetRec(folded_funcs, raise_aexprs folded_body, ())
        | ASeq(folded_first, folded_rest, _) ->
          ASeq(folded_first, raise_aexprs folded_rest, ()) in
      raise_aexprs (helpC expr)
    | ACExpr(expr) -> helpC expr in
  helpA prog
;;

let cse (prog : tag aprogram) : unit aprogram =
  (* note that all names are unique, but will still need to remove bindings at certain points *)
  let purity = purity_env prog in
  let rec helpA (aexp : tag aexpr) (env : (simple_expr * string) list) : unit aexpr =
    match aexp with
    | ALet(s, cexp, aexp, t) ->
      let trimmed_binding = helpC cexp env in
      let maybe_simple_binding = cexpr_to_simple_opt trimmed_binding in
        begin match maybe_simple_binding with
          | None -> ALet(s, trimmed_binding, helpA aexp env, ())
          | Some(simple_bind) ->
            if Hashtbl.find purity s
            then begin
              let se = simp simple_bind env in
              let maybe_prev_id =
                if List.mem_assoc se env
                then Id(List.assoc se env)
                else se in
              let new_env = match maybe_prev_id with
                | Num(_) | Bool(_) | Fun(_, _) -> env
                | Id(r) -> (Id(s), r) :: env
                | _ -> (se, s) :: env in
              ALet(s, simple_to_cexpr maybe_prev_id, helpA aexp new_env, ())
            end
            else ALet(s, trimmed_binding, helpA aexp env, ())
      end
    | ALetRec(binds, body, _) ->
      ALetRec(List.map (fun (f, func) -> (f, helpC func env)) binds, helpA body env, ())
    | ASeq(cexp, aexp, _) -> ASeq(helpC cexp env, helpA aexp env, ())
    | ACExpr(cexp) -> ACExpr(helpC cexp env)
  and helpC (cexp : tag cexpr) (env : (simple_expr * string) list) : unit cexpr =
    let helpI (imm : tag immexpr)  : unit immexpr =
      (simple_to_imm (simp (imm_to_simple imm) env)) in
    match cexp with
    | CIf(c, t, f, _) -> CIf(helpI c, (helpA t env), (helpA f env), ())
    | CLambda(args, body, _) -> CLambda(args, (helpA body env), ())
    | CPrim1(op, arg, _) -> CPrim1(op, helpI arg, ())
    | CPrim2(op, arg1, arg2 , _) -> CPrim2(op, helpI arg1, helpI arg2, ())
    | CApp(f, args, _) -> CApp(helpI f, List.map helpI args, ())
    | CTuple(elts, _) ->  CTuple(List.map helpI elts, ())
    | CGetItem(tup, idx, _) -> CGetItem(helpI tup, helpI idx, ())
    | CSetItem(tup, idx, rhs, _) ->  CSetItem(helpI tup, helpI idx, helpI rhs, ())
    | CImmExpr(imm) -> CImmExpr(helpI imm)
  and simp (se : simple_expr) (env : (simple_expr * string) list) : simple_expr =
    if List.mem_assoc se env
    then Id(List.assoc se env)
    else
      match se with
      | Id _ -> se
      | Num _ -> se
      | Bool _ -> se
      | Prim1(op, arg) -> Prim1(op, simp arg env)
      | Prim2(op, left, right) -> Prim2(op, simp left env, simp right env)
      | App(f, args) -> App(simp f env, List.map (fun x -> simp x env) args)
      | Fun(args, body) -> Fun(args, simp body env)
  in helpA prog []
;;

let letrec_breakup (binds : (string * unit cexpr) list) (body : unit aexpr) : unit aexpr =
  let index = ref 0 in
  let stack : (string list) ref = ref [] in
  let res : ((string list) list) ref = ref [] in

  (* mapping from func ID to list of IDs in the letrec used by the function with that ID *)
  let graph = List.map (fun (id, func) ->
      (id, List.filter (fun x -> List.mem_assoc x binds)
                       (free_vars (ACExpr func))))
      binds in

  (* index, lowlink, onstack *)
  let data : (string, (int * int * bool)) Hashtbl.t = Hashtbl.create 0 in
  List.iter (fun (id, func) -> (Hashtbl.add data id (-1, 0, false))) binds;

  let rec strongconnect (v : string) : unit =
    Hashtbl.replace data v (!index, !index, true);
    index := !index + 1;
    stack := v::!stack;
    List.iter (fun w ->
      let (wi, wl, wo) = (Hashtbl.find data w) in
      let (vi, vl, vo) = (Hashtbl.find data v) in
      let try_swap =
        (fun () -> if wl < vl then Hashtbl.replace data v (vi, wl, vo)) in
      if wi = -1
      then (strongconnect w; try_swap())
      else if wo then try_swap())
      (List.assoc v graph);
    let (vi, vl, _) = Hashtbl.find data v in
    if vl = vi
    then res := (new_SCC v [])::!res;

  and new_SCC (v : string) (ss : string list) : string list =
    match !stack with
    | first::rest ->
      stack := rest;
      let (a, b, _) = (Hashtbl.find data first) in
      Hashtbl.replace data first (a, b, false);
      if first != v
      then new_SCC v (first::ss)
      else first::ss
    | _ -> failwith "Impossible by algorithm" in

  (* run on each vertex *)
  List.iter (fun (v, _) ->
      let (i, _, _) = Hashtbl.find data v in
      if i = -1 then strongconnect v;)
    binds;
  List.fold_left (fun acc scc ->
      if List.exists (fun x -> List.mem x (free_vars acc)) scc
      then let bind_segment = (List.map (fun x -> (x, List.assoc x binds)) scc) in
        match bind_segment with
        | [(x, y)] when (not (List.mem x (List.assoc x graph)))-> ALet(x, y, acc, ())
        | _ -> ALetRec(bind_segment, acc, ())
      else acc)
    body
    !res

let dae (prog : tag aprogram) : unit aprogram =
  let purity = purity_env prog in
  let rec helpA (expr : tag aexpr) : unit aexpr =
    match expr with
    | ALet(x, cexpr, body, _) ->
      let trimmed_body = helpA body in
      let used_vars = free_vars trimmed_body in
      if List.mem x used_vars
      then ALet(x, helpC cexpr, trimmed_body, ())
      else if Hashtbl.find purity x
      then trimmed_body
      else ASeq(helpC cexpr, trimmed_body, ())
    | ALetRec(binds, body, _) ->
      letrec_breakup (List.map (fun (x, y) -> (x, helpC y)) binds) (helpA body)
    | ASeq(cexpr, rest, t) ->
      let trimmed_rest = helpA rest in
      if Hashtbl.find purity (sprintf "$seq_%d" t)
      then trimmed_rest
      else ASeq(helpC cexpr, trimmed_rest, ())
    | ACExpr(cexpr) -> ACExpr(helpC cexpr)
  and helpC (expr : tag cexpr) : unit cexpr =
    match cexpr_to_simple_opt expr with
    | Some(sexpr) -> simple_to_cexpr sexpr
    | None ->
      match expr with
      | CTuple(elts, _) -> CTuple(List.map untag_imm elts, ())
      | CGetItem(tup, idx, _) -> CGetItem(untag_imm tup, untag_imm idx, ())
      | CSetItem(tup, idx, rhs, _) -> CSetItem(untag_imm tup, untag_imm idx, untag_imm rhs, ())
      | CIf(cond, thn, els, _) -> CIf(untag_imm cond, helpA thn, helpA els, ())
      | CLambda(args, body, _) -> CLambda(args, helpA body, ())
      | _ -> failwith "Impossible" in
  helpA prog
;;

let optimize (prog : tag aprogram) (verbose : bool) (run_cf : bool) (run_cse : bool) (run_dae : bool) : tag aprogram =
  let iter_count = ref 0 in
  let optimized = ref prog in
  let rec converge () : unit  =
    iter_count := !iter_count + 1;
    let pre_iter = !optimized in
    let const_prog = if run_cf then atag (const_fold pre_iter) else pre_iter in
    let cse_prog = if run_cse then atag (cse const_prog) else const_prog in
    let dae_prog = if run_dae then atag (dae cse_prog) else cse_prog in
    if verbose
    then begin
      if run_cf then printf "Const/tagged %d:\n%s\n" !iter_count (string_of_aprogram const_prog);
      if run_cse then printf "CSE/tagged %d:\n%s\n" !iter_count (string_of_aprogram cse_prog);
      if run_dae then printf "DAE/tagged %d:\n%s\n" !iter_count (string_of_aprogram dae_prog);
    end;
    optimized := dae_prog;
    if !optimized <> pre_iter
    then converge() in
  converge();
  !optimized
