open Compile
open Runner
open Printf
open OUnit2
open ExtLib
open Types
open Expr
open Pretty
open Optimize

let is_osx = Conf.make_bool
  "osx"
  (let ic = Unix.open_process_in "uname" in
   let uname = input_line ic in
   let () = close_in ic in
   uname = "Darwin")
  "Set this flag to run on osx";;

let t name program expected =
  (* Check types by default. *)
  name>::test_run [] program name expected true;;
let tgc name heap_size program expected =
  (* We disable type-checking for gc tests to allow for cyclic structures. *)
  name>::test_run [string_of_int heap_size] program name expected false;;
let tvg name program expected = name>::(fun test_ctx ->
  skip_if (is_osx test_ctx) "Valgrind not supported on newer OSX versions";
  test_run_valgrind [] program name expected true test_ctx)
let tvgc name heap_size program expected = name>::(fun test_ctx ->
  skip_if (is_osx test_ctx) "Valgrind not supported on newer OSX versions";
  test_run_valgrind [string_of_int heap_size] program name expected false test_ctx);;
let terr name program expected =
  name>::test_err [] program name expected true ;;
let tgcerr name heap_size program expected =
  name>::test_err [string_of_int heap_size] program name expected false;;

let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let vars = free_vars anfed in
    let c = Pervasives.compare in
    let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
    assert_equal (List.sort ~cmp:c vars) (List.sort ~cmp:c expected) ~printer:str_list_print)

module StringMap = Map.Make(String)
let tewf name program expected_errs = name>::(fun _ ->
  let count_substring str sub =
    (* https://www.rosettacode.org/wiki/Count_occurrences_of_a_substring#OCaml *)
    let sub_len = String.length sub in
    let len_diff = (String.length str) - sub_len
    and reg = Str.regexp_string sub in
    let rec aux i n =
      if i > len_diff then n else
        try
          let pos = Str.search_forward reg str i in
          aux (pos + sub_len) (succ n)
        with Not_found -> n
    in
    aux 0 0 in
  let expected_counts = List.fold_left
    (fun acc err ->
      if StringMap.mem err acc
      then StringMap.add err (1 + StringMap.find err acc) acc
      else StringMap.add err 1 acc)
    StringMap.empty
    expected_errs in
  let prog_errs = print_errors (well_formed (parse_string "" program) [] true) in
  let concat_errs = String.concat "\n" prog_errs in
  let actual_counts =
    StringMap.mapi (fun err _ -> count_substring concat_errs err) expected_counts in
  let diff_printer = (fun fmt _ ->
    Format.fprintf fmt
                   "Expected errors: %s\nActual errors: %s"
                   ("[\"" ^ (String.concat "\",\"" expected_errs) ^ "\"]")
                   concat_errs) in
  (assert_equal (List.length expected_errs)
                (List.length prog_errs)
                ~pp_diff:diff_printer);
  (assert_equal expected_counts
                actual_counts
                ~cmp:(StringMap.equal (fun x y -> x = y))
                ~pp_diff:diff_printer))

let topt name program expected run_cf run_cse run_dae = name>::(fun _ ->
    let optimized =
      (* Skips well-formedness checking for simplicity. *)
      optimize (atag (anf (tag (parse_string "" program)))) false run_cf run_cse run_dae in
    let anfed_expected =
      (atag (anf (tag (parse_string "" expected)))) in
    assert_equal anfed_expected optimized ~printer:string_of_aprogram)

let tpe name program (exp_impures : string list) = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let pe = purity_env (atag anfed) in
    let impures = Hashtbl.fold (fun x pure acc -> if pure then acc else x::acc) pe [] in
    let c = Pervasives.compare in
    let str_list_print strs = "[" ^ (ExtString.String.join ", "strs) ^ "]" in
    assert_equal (List.sort ~cmp:c exp_impures)
    (List.sort ~cmp:c impures) ~printer:str_list_print)

;;

let tcf name program expected = topt name program expected true false false
let tcse name program expected = topt name program expected false true false
let tdae name program expected = topt name program expected false false true

(* Utility to generate both a "normal" and a valgrind test for a function call. *)
let test_funcall name declblock body expected =
  let test_prog = (sprintf "%s\n%s" declblock body) in
  [
    t name test_prog expected;
    tvg (name ^ "_valgrind") test_prog expected;
  ];;

(* Utility to generate both a "normal" and a valgrind test for a gc run. *)
let test_gc name mem body expected =
  [
    tgc name mem body expected;
    tvgc (name ^ "_valgrind") mem body expected;
  ];;

let tterr = (fun name prog -> terr name prog "Type error");;

let imm_tests = [
  t "forty" "40" "40";
  t "fals" "false" "false";
  t "tru" "true" "true";
  tewf "unbound_id" "x" ["not in scope"];
];;

let alloc_tests = [
  t "tup1" "(5, 7, 8)" "(5, 7, 8)";
  t "tup2" "(true, 7, false, 8)" "(true, 7, false, 8)";
  t "func1" "(lambda: 1)" "<function>";
  t "func2" "(lambda x: x)" "<function>";

  tewf "unbound_in_tup1" "(true, y)" ["not in scope"];
  tewf "unbound_in_tup2" "(z, someFun())" ["not in scope"; "not in scope"];
];;

let prim1_tests = [
  t "print_num" "print(9)" "9\n9";
  t "print_true" "print(true)" "true\ntrue";
  t "print_false" "print(false)" "false\nfalse";
  t "print_tuple1" "print((1, 2))" "(1, 2)\n(1, 2)";
  t "print_tuple2" "print((1, (2, 3)))" "(1, (2, 3))\n(1, (2, 3))";
  t "print_func" "print((lambda: 1))" "<function>\n<function>";

  t "add1" "add1(10)" "11";
  t "sub1" "sub1(11)" "10";

  t "not_false" "!(false)" "true";
  t "not_true" "!(true)" "false";

  t "isnum_num" "isnum(5)" "true";
  t "isnum_bool" "isnum(true)" "false";
  t "isnum_tup" "isnum((1, 2))" "false";
  t "isnum_func" "isnum((lambda: 1))" "false";

  t "isbool_num" "isbool(10)" "false";
  t "isbool_bool" "isbool(false)" "true";
  t "isbool_tup" "isbool((1, 2))" "false";
  t "isbool_func" "isbool((lambda: 1))" "false";

  t "istuple_num" "istuple(10)" "false";
  t "istuple_bool" "istuple(false)" "false";
  t "istuple_tup" "istuple((1, 2))" "true";
  t "istuple_func" "istuple((lambda: 1))" "false";

  t "add1_sub1" "add1(sub1(2))" "2";
  t "sub1_add1" "sub1(add1(2))" "2";
  t "add1_print" "add1(print(9))" "9\n10";
  t "sub1_print" "sub1(print(9))" "9\n8";
  t "not_print" "!(print(false))" "false\ntrue";
  t "print_print" "print(print(10))" "10\n10\n10";
  t "print_add1" "print(add1(9))" "10\n10";
  t "print_sub1" "print(sub1(9))" "8\n8";
  t "print_not" "print(!(true))" "false\nfalse";

  tterr "add1_true" "add1(true)";
  tterr "add1_false" "add1(false)";
  tterr "sub1_true" "sub1(true)";
  tterr "sub1_false" "sub1(false)";
  tterr "add1_tup" "add1((1, 2))";
  tterr "sub1_tup" "sub1((1, 2, (1, 2), 4))";
  tterr "add1_func" "add1((lambda: 1))";
  tterr "sub1_func" "sub1((lambda: 1))";

  tterr "not_num" "!(10)";
  tterr "not_tup" "!((1, 2))";
  tterr "not_func" "!((lambda: 1))";
];;

let prim2_tests = [
  t "plus" "40 + 50" "90";
  t "minus" "60 - 25" "35";
  t "times" "12 * 5" "60";

  tterr "add_bool1" "true + 5";
  tterr "add_bool2" "6 + false";
  tterr "add_bool3" "false + true";
  tterr "mul_bool1" "(-5) * true";
  tterr "mul_bool2" "9 * true";
  tterr "sub_bool1" "true - false";
  tterr "add_tup1" "9 + (2, 4)";
  tterr "add_tup2" "(1, 6) + (false, 4)";
  tterr "sub_tup1" "(true, false) - 10";
  tterr "sub_tup2" "(1, 2, 3) - (0, 1, 2)";
  tterr "mul_tup1" "3 * (1, 2, 3)";
  tterr "add_func" "5 + (lambda: 1)";
  tterr "sub_func" "(lambda: 1) - 3";
  tterr "mul_func" "(lambda: 1) * (lambda: 1)";

  terr "sub1_overflow" "sub1(-1073741824)" "overflow";
  terr "add1_overflow" "add1(1073741823)" "overflow";
  terr "plus_overflow" "773741823 + 773741829" "overflow";
  terr "times_overflow" "773741823 * 773741829" "overflow";
  terr "sub_overflow" "773741823 - (-773741829)" "overflow";

  t "and1" "true && false" "false";
  t "and2" "true && true" "true";
  t "and3" "false && false" "false";
  t "and4" "false && true" "false";
  t "or1" "true || false" "true";
  t "or2" "true || true" "true";
  t "or3" "false || false" "false";
  t "or4" "false || true" "true";
  t "print_or" "print(true || false)" "true\ntrue";
  t "or_print1" "print(true) || false" "true\ntrue";
  t "or_print2" "true || print(false)" "false\ntrue";

  tterr "and_num1" "true && 8";
  tterr "and_num2" "8 && false";
  tterr "and_num3" "false && 2";
  tterr "and_num4" "-5 && true";
  tterr "and_num5" "9 && 0";
  tterr "or_num1" "true || 9";
  tterr "or_num2" "0 || false";
  tterr "or_num3" "false || -6";
  tterr "or_num4" "2 || true";
  tterr "or_num5" "9 || 20";
  tterr "or_num6" "true && (9, 8)";
  tterr "and_tup1" "(1, 2) && 20";
  tterr "and_tup2" "(1, 2) && (7, 8)";
  tterr "or_tup1" "true || (true, true)";
  tterr "or_tup2" "9 || (9, false)";
  tterr "or_tup3" "(6, true, false) || (6, 7, 8, 9)";
  tterr "and_func" "(lambda: 1) && true";
  tterr "or_func" "false || (lambda: 1)";

  t "gt1" "15 > -9" "true";
  t "gt2" "5 > 9" "false";
  t "gt3" "5 > 5" "false";
  t "gte1" "14 >= 7" "true";
  t "gte2" "4 >= 9" "false";
  t "gte3" "7 >= 7" "true";
  t "lt1" "14 < 7" "false";
  t "lt2" "-4 < 9" "true";
  t "lt3" "7 < 7" "false";
  t "lte1" "13 <= 6" "false";
  t "lte2" "-4 <= 5" "true";
  t "lte" "2 <= 2" "true";
  t "eq1" "2 == 2" "true";
  t "eq2" "2 == -3" "false";
  t "eq3" "6 == 9" "false";
  t "eq4" "true == true" "true";
  t "eq5" "true == false" "false";
  t "eq6" "true == 8" "false";
  t "eq7" "false == true" "false";
  t "eq8" "false == -2" "false";
  t "eq9" "false == false" "true";
  t "eq10" "(1, 2) == (1, 2)" "false";
  t "eq11" "(1, 2) == 3" "false";
  t "eq12" "false == (1, 2)" "false";
  t "eq13" "(lambda: 1) == (lambda: 1)" "false";
  t "eq14" "(lambda: 1) == true" "false";
  t "eq15" "-5 == (lambda: 1)" "false";
  t "eq16" "(1, 2, 3) == (lambda: 1)" "false";

  t "ref_equality_tup" "let t = (1, 2) in t == t" "true";
  t "ref_equality_func" "let f = (lambda: 1) in f == f" "true";

  tterr "gte_bool1" "true >= 5";
  tterr "gte_bool2" "false >= false";
  tterr "lt_bool1" "true < 8";
  tterr "lt_bool2" "5 < false";
  tterr "lt_bool3" "true < true";
  tterr "gt_bool1" "false > 19";
  tterr "gt_bool2" "true > false";
  tterr "lte_bool1" "false <= -12";
  tterr "lte_bool2" "5 <= true";
  tterr "lte_bool3" "false <= true";
  tterr "gte_tup" "5 >= (9, 8)";
  tterr "gt_tup" "2 > (1, 5, true)";
  tterr "lt_tup" "(1, 2, false) < 10";
  tterr "lte_tup" "(3, 4, 5) <= 76";
  tterr "lt_tup_bool" "(1, 2) < false";
  tterr "gte_func" "10 >= (lambda: 1)";
  tterr "gt_func" "10 > (lambda: 1)";
  tterr "lte_func" "(lambda: 1) <= 10";
  tterr "lt_func" "(lambda: 1) < 10";
];;

let prim1_prim2_mix_tests = [
  t "print_plus" "print(40 + 50)" "90\n90";
  t "plus_print1" "print(40) + 50" "40\n90";
  t "plus_print2" "40 + print(50)" "50\n90";
  t "print_minus" "print(60 - 25)" "35\n35";
  t "minus_print1" "print(60) - 25" "60\n35";
  t "minus_print2" "60 - print(25)" "25\n35";
  t "print_times" "print(12 * 5)" "60\n60";
  t "times_print1" "print(12) * 5" "12\n60";
  t "times_print2" "12 * print(5)" "5\n60";

  t "print_and" "print(true && false)" "false\nfalse";
  t "and_print1" "print(true) && false" "true\nfalse";
  t "and_print2" "true && print(false)" "false\nfalse";

  t "print_eq" "print(10) == print(true)" "10\ntrue\nfalse";

  t "complex1"
    "(let x = 10 in print(sub1(x))) + (let x = 9, y = 11 in print(x * y))"
    "9\n99\n108";
];;

let if_tests = [
  t "if1" "if true: 10 else: 5" "10";
  t "if2" "if false: 3 else: 4" "4";
  t "if3" "if (5 < 4): false else: true" "true";
  t "if4" "if (1 == true): 7 else: (9 * 2)" "18";
  t "nested_if" "if false: 10 else: if true: 9 else: 8" "9";

  tterr "cond_not_bool1" "if 8: 6 else: 7";
  tterr "cond_not_bool2" "if (true, false): 6 else: 7";
  tterr "cond_not_bool3" "if (lambda: true): 6 else: 7";

  tterr "mismatched_branch_types1" "if isbool(10): true else: 10";
  tterr "mismatched_branch_types2" "(lambda x: if (isbool(x)): !(x) else: (-1 * x))";
  tterr "mismatched_branch_types3" "if isnum(10): print(8) else: print(false)";
];;

let tup_access_tests = [
  t "tup_get1" "(1, 2, 3)[0]" "1";
  t "tup_get2" "(1, 2, 3)[2]" "3";
  t "tup_get_exact" "(1, (2, 3), 4)[:1:]" "(2, 3)";

  t "tup_set1" "let t = (4, 5, 6) in
                begin
                  t[0] := 7;
                  t
                end" "(7, 5, 6)";

  t "tup_set2" "let t = ((1, 2), (2, 3)) in
                begin
                  t[1] := (4, 5);
                  t
                end" "((1, 2), (4, 5))";

  t "tup_set_exact" "let t = (1, (2, 3), 4) in
                     begin
                       t[:1:] := (5, 6);
                       t
                     end" "(1, (5, 6), 4)";

  tterr "access_int" "1[0]";
  tterr "access_bool" "true[1]";
  tterr "access_fun" "(lambda: 1)[0]";

  tterr "index_bool" "(1, 2)[false]";
  tterr "index_tup" "(1, 2)[(0, 1)]";
  tterr "index_fun" "(1, 2)[(lambda: 1)]";

  tterr "set_int" "1[0] := 2";
  tterr "set_bool" "false[1] := true";
  tterr "set_func" "(lambda: 1)[2] := 3";

  (* Using inexact indices prevents useful type inference for heterogenous tuples. *)
  tterr "add_access_maybe_not_int" "(1, (2, 5), 3)[0] + 5";
  tterr "or_access_maybe_not_bool" "(false, true, 0)[1] || false";
  tterr "double_access_maybe_not_tup" "(1, (2, 5), 3)[1][1]";
  tterr "call_access_maybe_not_func" "((lambda: 1), 3, (lambda: 2))[2]()";

  (* But using exact indices enables inference. *)
  t "add_exact_access" "(1, (2, 5), 3)[:0:] + 5" "6";
  t "or_exact_access" "(false, true, 0)[:1:] || false" "true";
  t "access_exact_access" "(1, (2, 5), 3)[:1:][1]" "5";
  t "call_exact_access" "((lambda: 1), 3, (lambda: 2))[:2:]()" "2";

  (* Setting can't overwrite types. *)
  tterr "set_change_type1" "(1, 2)[0] := (3, 4)";
  tterr "set_change_type2" "(true, false)[1] := 3";

  (* And it doesn't work at all for heterogenous tuples and non-exact indexes. *)
  tterr "set_heterogenous_non_exact" "(1, (2, 3))[0] := 1";
  tterr "set_heterogenous_non_exact" "((lambda: 1), false)[1] := true";

  (* Using non-exact get or set won't catch bad index values during type checking,
     and the error will emerge at runtime. *)
  terr "negative_index" "(1, 2)[-1]" "index too small";
  terr "very_large_index" "(1, 2)[100000]" "index too large";
  terr "off_by_one_index" "(1, 2)[2]" "index too large";
];;

let simple_funcall_tests = [
  t "call_thunk" "(lambda: 1)()" "1";
  t "call_id_num" "(lambda x: x)(1)" "1";
  t "call_id_bool" "(lambda x: x)(true)" "true";
  t "fun_returns_fun" "(lambda x: (lambda y: x - y))(7)(5)" "2";

  tterr "call_num" "(5+7)(10)";
  tterr "call_bool" "(false)(2)";
  tterr "call_tup" "((1, 2, 3))(3)";
  tterr "arity1" "(lambda x: x)(5, 6)";
  tterr "arity2" "(lambda:7)(5, 6)";
  tterr "arity3" "(lambda x, y: x+y)(5)";
  tterr "arity4" "(lambda x, y, z: x)(5, 6)";
];;

let scope_tests = [
  t "multi_let" "let x = 10, y = x in y" "10";
  t "nested_let" "let x = 10 in let y = x in y" "10";
  t "free_vars_lexical_scope"
    "let f = (let x = 10 in (lambda: x)) in let x = 11 in f()"
    "10";

  tewf "dup_id" "let x = 10, x = 11 in x" ["duplicates"];
  tewf "shadowed_id" "let x = 10 in let x = (lambda: 1) in x()" ["shadows"];
  tewf "rec_func_normal_rec" "let f = (lambda: f()) in f()" ["not in scope"];
  tewf "rec_non_func1" "let rec x = 10 in x" ["not bound to a function"];
  tewf "rec_non_func2" "let rec f = (lambda: 1), x = f() in x" ["not bound to a function"];
  tewf "mut_rec_func" "let rec x = (lambda: y()), y = (lambda: x()) in x()" [];
  tewf "nested_let_rec" "let rec x = (lambda: y()) in let rec y = (lambda: x()) in x()" ["not in scope"];
];;

let type_annotation_tests = [
  tewf "unbound_tyvar1" "let x : Y = 10 in x" ["type"];
  tewf "unbound_tyvar2" "let x : [X] Y = 10 in x" ["type"];
  tewf "unused_tyvar" "let x : [X] int = 10 in x" [];

  tterr "wrong_annotation1" "let x : bool = 10 in x";
  tterr "wrong_annotation2" "let x : (int -> bool) = 10 in x";
  tterr "wrong_annotation3" "let x : (int, int) = 10 in x";
  tterr "wrong_annotation4" "let x : int = true in x";
  tterr "wrong_annotation5" "let x : int = (1, 2, 3) in x";
  tterr "wrong_annotation6" "let x : (int -> int) = false in x";
  tterr "wrong_annotation5" "let f : [X] (X -> bool) = (lambda x: 10) in f(true)";
];;

(*** Function bindings to use in many tests ***)

(* Sanity-check *)
let identity =
"let id = (lambda x: x) in
"
;;
(* Compute the sum of 0 to n *)
let sum =
"let sum = (lambda n:
  let rec tail_sum = (lambda m, acc:
    if (m == 0): acc
    else: tail_sum(m - 1, acc + m)) in
  tail_sum(n, 0)) in
"
;;
(* Compute factorial *)
let fact =
"let fact = (lambda n:
  let rec tail_fact = (lambda m, acc:
    if (m == 0): acc
    else: tail_fact(m - 1, m * acc)) in
  tail_fact(n, 1)) in
"
;;
(* Mutually recursive is-even and is-odd functions *)
let is_even_is_odd =
"let rec
  is_even = (lambda n:
    if (n == 0): true
    else: is_odd(n - 1)),
  is_odd = (lambda n:
    if (n == 0): false
    else: is_even(n - 1)) in
"
;;
(* Function to test that functions safely handle overwriting their
   own arguments when preparing to make a function call *)
let try_to_munge_args =
"let try_munge_two = (lambda x, y:
  if (x == y): true else: false) in
let try_munge = (lambda x, y:
  # Depending on how the compiler handles copying arguments to tail-calls,
  # the value for y might overwrite the value for x.
  try_munge_two(y, x)) in
"
;;
(*
  Inspired by the answer to my Piazza question about Valgrind:

  https://piazza.com/class/ixi5udrwjfe2x2?cid=59

  f and g take differing numbers of arguments, and swap their first two args
  on each tail-call to one another. Eventually one of them calls h in a
  non-tail position. Even with a huge number of recursive calls, this should
  work fine.
*)
let fgh =
"let h = (lambda a, b, c, d, e:
  # Print and return a
  print(a)) in

let rec
  f = (lambda x, y, z:
    # If z is even, print x and return x+1 after z recursive calls
    # Else print y and return y-1 after z recursive calls
    if (z == 0): h(x, x, y, y, x * y) + 1
    else: g(x, y, z - 1, 0)),

  g = (lambda s, t, u, v:
    # If u is even, print t and return t-1 after u recursive calls
    # Else print s and return s+1 after u recursive calls
    if (u == 0): h(t, s, u, v, s * t) - 1
    else: f(s, t, u - 1)) in
"
;;
(* Function to test that making tail calls doesn't munge the local variables
   of any call frames placed lower on the stack *)
let try_to_munge_lower_locals =
"let third = (lambda a, b, c, d, e, f:
  print(f)) in

let second = (lambda y:
  # Call third in tail position. It has many more arguments than this function,
  # so if arbitrary tail-calls aren't implemented properly we'll either write
  # above our call frame (if ESP isn't properly incremented) or munge the local
  # vars of the call frame from which this function was called (if function args
  # are placed below EBP instead of above it).
  third(y, 2 * y, 3 * y, 4 * y, 5 * y, 6 * y)) in

let first = (lambda x:
  # Call second in non-tail position. After ANF-ing, the result of (3 * 2)
  # should be stored in a slot for local vars in first's call frame while
  # the call to second evaluates.
  (3 * 2) + second(print(x))) in
"
;;
(* Example testing capture of free variables within closure allocations *)
let capture_free_vars =
"let second = (lambda a, b:
  (lambda c, d:
    a(c) + d(b))) in
  let first = (lambda:
    second((lambda x: x + 5), (lambda y: y + 2))(5, (lambda z: z(12)))) in"
;;

let vg_funcall_tests = List.flatten [
  test_funcall "id_10" identity "id(10)" "10";
  test_funcall "id_polymorphic" identity "(id(10), id(true))" "(10, true)";
  test_funcall "sum_0" sum "sum(0)" "0";
  test_funcall "sum_20000" sum "sum(20000)" "200010000";
  test_funcall "fact_0" fact "fact(0)" "1";
  test_funcall "fact_10" fact "fact(10)" "3628800";
  test_funcall "is_even_0" is_even_is_odd "is_even(0)" "true";
  test_funcall "is_even_100000001" is_even_is_odd "is_even(100000001)" "false";
  test_funcall "is_odd_0" is_even_is_odd "is_odd(0)" "false";
  test_funcall "is_odd100000001" is_even_is_odd "is_odd(100000001)" "true";
  test_funcall "try_munge_args" try_to_munge_args "try_munge(1, 2)" "false";
  test_funcall "tail_rec_mismatched_nargs1" fgh "f(5, 6, 100000000)" "5\n6";
  test_funcall "tail_rec_mismatched_nargs2" fgh "f(5, 6, 100000001)" "6\n5";
  test_funcall "try_munge_lower_locals" try_to_munge_lower_locals "first(1)" "1\n6\n12";
  test_funcall "capture_free_vars" capture_free_vars "first()" "24";
  (* Example brought up by B.Lerner during office hours as a potential counter-example. *)
  test_funcall "feel_the_blern" identity "let blerner_func = (lambda f, g, x:
    let t = (f, g) in
    t[0](t[1](x))) in
    blerner_func(id, id, 10)" "10";
];;

let gc_tests = [
  tgcerr "oomgc1" 7 "(1, (3, 4))" "Out of memory";
  tgcerr "oomgc2" 3 "(3, 4)" "Allocation";
  tgcerr "oomgc3" 1 "(lambda: 1)" "Allocation";
  tgcerr "oomgc4" 3 "let x = 10 in (lambda: x)" "Allocation";
] @ List.flatten [
  test_gc "gc_tup1" 4 "(3, 4)" "(3, 4)";
  test_gc "gc_tup2" 8 "(1, (3, 4))" "(1, (3, 4))";
  test_gc "gc_func1" 4 "(lambda: 1)" "<function>";
  test_gc "gc_func2" 4 "(lambda x: x)" "<function>";
  test_gc "gc_func3" 4 "let x = 10 in (lambda: x)" "<function>";

  test_gc "gc4" 10
      "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
      "(1, 2)";

  test_gc "gc5" 12
    "let f = (lambda: let t = (1, 2) in (t, t)) in
      begin
        f();
        f();
        f();
        f()
      end"
    "((1, 2), (1, 2))";

  test_gc "gc6" 12
    "let f = (lambda:
      let t = (1, (2, 3), 4) in
      begin
        t[:1:][1] := t[1];
        t[2] := t;
        t
      end) in
      begin
        f();
        f();
        f();
        f()
      end"
    "(1, (2, <cyclic tuple 2>), <cyclic tuple 1>)";

  test_gc "gc7" 14
    "let x = (2, 3, 4, 5) in
    let f = (lambda n:
      let t = (1, x, 4) in
      begin
        t[:1:][n] := t[1];
        t[2] := t;
        t
      end) in
      begin
        f(0);
        f(1);
        f(2);
        f(3);
        x
      end"
    "(<cyclic tuple 1>, <cyclic tuple 1>, <cyclic tuple 1>, <cyclic tuple 1>)";
];;

let purity_tests = [
  (* Numbers and booleans are always pure. *)
  tpe "num_pure" "let x = 5 in x" [];
  tpe "bool_pure" "let b = false in b" [];

  (* Tuples are always impure because allocation is a side-effect. *)
  tpe "tup_impure" "let t = (1, false) in t" ["t"];
  (* Functions are pure only at the top level, inner nested functions are
     sometimes impure. *)
  tpe "func_pure" "let f = (lambda x: x) in f" [];

  (* `print` and `printStack` are the only always-impure Prim1s.
     `add1`, `sub1` and `not` are impure if they have improperly-typed constants. *)
  tpe "add1_pure" "let x = add1(10) in x" [];
  tpe "sub1_pure" "let x = sub1(10) in x" [];
  tpe "not_pure" "let b = !(true) in b" [];
  tpe "isnum_pure" "let b = isnum(10) in b" [];
  tpe "isbool_pure" "let b = isbool(10) in b" [];
  tpe "istup_pure" "let b = istuple(10) in b" [];
  tpe "print_impure" "let x = print(10) in x" ["x"];
  tpe "printStack_impure" "let x = printStack(10) in x" ["x"];

  (* All Prim2s are pure, so long as they don't have improperly-typed constants. *)
  tpe "add_pure" "let x = 1 + 2 in x" [];
  tpe "sub_pure" "let x = 1 - 2 in x" [];
  tpe "times_pure" "let x = 1 * 2 in x" [];
  tpe "lt_pure" "let b = 1 < 2 in x" [];
  tpe "lte_pure" "let b = 1 <= 2 in x" [];
  tpe "gt_pure" "let b = 1 > 2 in x" [];
  tpe "gte_pure" "let b = 1 >= 2 in x" [];
  tpe "eq_pure1" "let e = 1 == 1 in e" [];
  tpe "eq_pure2" "let e = 1 == true in e" [];
  tpe "eq_pure3" "let e = false == true in e" [];
  tpe "and_pure" "let b = true && false in b" [];
  tpe "or_pure" "let b = false || false in b" [];
  tpe "add_impure" "let x = 1 + true in x" ["x"];
  tpe "sub_impure" "let x = false - 2 in x" ["x"];
  tpe "times_impure" "let x = 1 * false in x" ["x"];
  tpe "lt_impure" "let b = 1 < true in x" ["b"];
  tpe "lte_impure" "let b = false <= 2 in x" ["b"];
  tpe "gt_impure" "let b = false > 2 in x" ["b"];
  tpe "gte_impure" "let b = 1 >= true in x" ["b"];
  tpe "and_impure" "let b = true && 1 in b" ["b"];
  tpe "or_impure" "let b = 2 || false in b" ["b"];

  (* Getting from a tuple is pure, as long as the tuple is an id and the index is not a bool.
     Note that the tuple can only become a non-id during optimization.
     Setting in a tuple is impure. *)
  tpe "get_pure" "let t = (1, 2, 3), x = t[1] in x" ["t"];
  tpe "get_impure" "let t = (1, 2, 3), x = t[true] in x" ["t"; "x"];
  tpe "set_pure" "let t = (1, 2, 3), x = (t[1] := 4) in x" ["t"; "x"];

  (* Calling a function is pure if the body of the function is pure. *)
  tpe "call_pure" "let f = (lambda x: x), y = f(10) in y" [];
  tpe "call_impure" "let f = (lambda x: print(x)), y = f(10) in y" ["y"];
  tpe "rec_call_pure"
    "let rec x = (lambda a: y(a)), y = (lambda b: x(b)) in
     let ans = y(5) in
     ans"
    ["x"; "y"];
  tpe "rec_call_impure"
    "let rec x = (lambda a: let printed = print(a) in y(printed)), y = (lambda b: x(b)) in
     let ans = y(5) in
     ans"
    ["x"; "y"; "printed"; "ans"];

(* An `if` is pure if both of its branches are pure or if there's a constant condition
   and the corresponding branch is pure. If the condition is a number, it's impure. *)
  tpe "if_pure" "let x = (if true: 10 else: true) in x" [];
  tpe "if_impure1" "let x = (if true: 10 else: print(true)) in x" [];
  tpe "if_impure2" "let c = true in
                    let x = (if c: 10 else: print(true)) in x" ["x"];
  tpe "if_impure3" "let x = (if true: print(10) else: true) in x" ["x"];
  tpe "if_impure4" "let x = (if 1: false else: true) in x" ["x"];

  (* Higher-order functions assume their arguments are pure. *)
  tpe "sound_ho_func"
    "let f = (lambda g: g(10)) in
     let arg = (lambda x: x) in
     let ans = f(arg) in
     ans"
    [];
  tpe "unsound_ho_func"
    "let f = (lambda g: g(10)) in
     let arg = (lambda x: print(x)) in
     let ans = f(arg) in
     ans"
    (* `ans` is really impure, but we miss it because of our assumption. *)
    [];

  (* Functions returned from higher-order functions are assumed to be impure. *)
  tpe "pure_ho_return"
    "let f = (lambda x: (lambda: x)) in
     let g = f(10) in
     let ans = g() in
     ans"
    (* `ans` is actually pure, but it's too much of a hassle to figure that out. *)
    ["ans"];
  tpe "impure_ho_return"
    "let f = (lambda x: (lambda: print(x))) in
     let g = f(10) in
     let ans = g() in
     ans"
    ["ans"];

  (* `seqs` record if any of their pieces are impure. *)
  tpe "seq_pure" "begin 1; 2; 3 end" [];
  tpe "seq_impure" "begin 1; print(2); 3 end" ["$seq_2"];
];;

let cf_tests = [
  (* Prim1 constant-folds *)
  tcf "add1_const" "add1(1)" "2";
  tcf "sub1_const" "sub1(-30)" "-31";
  tcf "not_const" "!(true)" "false";
  tcf "isnum_const1" "isnum(false)" "false";
  tcf "isnum_const2" "isnum(10)" "true";
  tcf "isbool_const1" "isbool(true)" "true";
  tcf "isbool_const2" "isbool(-50)" "false";

  (* Prim2 constant-folds *)
  tcf "plus_const" "3 + 4" "7";
  tcf "minus_const" "10 - (-10)" "20";
  tcf "times_const" "-3 * -6" "18";
  tcf "lt_const" "3 < 4" "true";
  tcf "gt_const" "3 > 4" "false";
  tcf "lte_const" "-10 <= -10" "true";
  tcf "gte_const" "100 >= 101" "false";
  tcf "num_eq_const1" "10 == 10" "true";
  tcf "num_eq_const2" "10 == 20" "false";
  tcf "num_bool_eq1" "10 == false" "false";
  tcf "num_bool_eq2" "true == 20" "false";
  tcf "bool_eq_const1" "false == false" "true";
  tcf "bool_eq_const2" "false == true" "false";
  tcf "and_const1" "true && true" "true";
  tcf "and_const2" "false && true" "false";
  tcf "or_const1" "false || true" "true";
  tcf "or_const2" "false || false" "false";

  (* Overflows preserved by constant folding. *)
  tcf "add1_max" (sprintf "add1(%d)" max_int) (sprintf "add1(%d)" max_int);
  tcf "sub1_min" (sprintf "sub1(%d)" min_int) (sprintf "sub1(%d)" min_int);
  tcf "plus_max" (sprintf "1 + %d" max_int) (sprintf "1 + %d" max_int);
  tcf "minus_min" (sprintf "%d - 1" min_int) (sprintf "%d - 1" min_int);
  tcf "times_max" (sprintf "%d * 2" max_int) (sprintf "%d * 2" max_int);
  tcf "times_min" (sprintf "2 * %d" min_int) (sprintf "2 * %d" min_int);
  tcf "max_minus_min" (sprintf "%d - %d" max_int min_int) (sprintf "%d - %d" max_int min_int);

  (* Type mismatches preserved by constant folding. *)
  tcf "add1_bool" "add1(true)" "add1(true)";
  tcf "sub1_bool" "sub1(false)" "sub1(false)";
  tcf "not_num" "!(10)" "!(10)";
  tcf "plus_bool1" "0 + true" "0 + true";
  tcf "plus_bool2" "true + 0" "true + 0";
  tcf "sub_bool" "false - 0" "false - 0";
  tcf "times_bool1" "1 * false" "1 * false";
  tcf "times_bool2" "true * 1" "true * 1";
  tcf "times_bool3" "false * 0" "false * 0";
  tcf "times_bool4" "0 * true" "0 * true";
  tcf "and_num1" "10 && false" "10 && false";
  tcf "and_num2" "true && 11" "true && 11";
  tcf "or_num1" "true || 9" "true || 9";
  tcf "or_num2" "12 || false" "12 || false";

  (* Constant-folds that might erase runtime type errors. *)
  tcf "zero_plus_var1" "0 + x" "x";
  tcf "zero_plus_var2" "x + 0" "x";
  tcf "var_minus_zero" "x - 0" "x";
  tcf "one_times_var1" "1 * x" "x";
  tcf "one_times_var2" "x * 1" "x";
  tcf "zero_times_var1" "0 * x" "0";
  tcf "zero_times_var2" "x * 0" "0";
  tcf "and_var1" "true && x" "x";
  tcf "and_var2" "x && true" "x";
  tcf "and_var3" "false && x" "false";
  tcf "and_var4" "x && false" "false";
  tcf "or_var1" "false || x" "x";
  tcf "or_var2" "x || false" "x";
  tcf "or_var3" "true || x" "true";
  tcf "or_var4" "x || true" "true";

  (* If constant folds. *)
  tcf "if_constant1" "if true: 5 else: 6" "5";
  tcf "if_constant2" "if false: 5 else: 6" "6";
  tcf "if_constant3" "if true: if false: 5 else: 6 else: 7" "6";
  tcf "if_constant4" "if false: 5 else: if true: 6 else: 7" "6";

  (* Nested constant folding *)
  tcf "assignment_example"
    "let x = 4 + 5 in
    let y = x * 2 in
    let z = y - x in
    let a = x + 7 in
    let b = 14 in
    a + b"
    "let x = 9 in
    let y = 18 in
    let z = 9 in
    let a = 16 in
    let b = 14 in
    30";

  tcf "simple_fun_inlining"
    "let f = (lambda: 9) in
     let x = f() in
     x"
    "let f = (lambda: 9) in
     let x = 9 in
     9";

  tcf "inline_with_args"
    "let f = (lambda x, y: x - y) in
     let x = f(10, 8) in
     x"
    "let f = (lambda x, y: x - y) in
     let x = 2 in
     2";

  tcf "fold_free_vars"
    "let x = 10 + 5 in
     let f = (lambda: x) in
     let f_call = f() in
     let y = x + f_call in
     y"
    "let x = 15 in
     let f = (lambda: 15) in
     let f_call = 15 in
     let y = 30 in
     30";

  tcf "replace_call_args"
    "let x = 10 + 5 in
     let y = true in
     let f = (lambda a, b: if b: add1(a) else: sub1(a)) in
     f(x, y)"
    "let x = 15 in
     let y = true in
     let f = (lambda a, b: if b: add1(a) else: sub1(a)) in
     f(15, true)";

  tcf "raise_let_from_if_in_let"
    "let x = if true: let a = 10 in a + 6
             else: let b = 9 in b - 8 in
     x + 20"
    "let a = 10 in
     let x = 16 in
     36";

  tcf "raise_let_from_if_in_seq"
    "begin
      if false: let a = 10 in a + 6
      else: let b = 9 in b - 8;
      print(20)
    end"
    "let b = 9 in
     begin
       1;
       print(20)
     end";

  tcf "raise_letrec_from_if_in_let"
    "let x = if false: 10
             else: let rec f = (lambda x: g(x)),
                           g = (lambda y: f(y)) in
                   f(10) in
     x + 30"
    "let rec f = (lambda x: g(x)), g = (lambda y: f(y)) in
     let x = f(10) in
     x + 30";

  tcf "raise_letrec_from_if_in_seq"
    "begin
       if true: let rec f = (lambda x: g(x)),
                        g = (lambda y: f(y)) in f(10)
       else: 10;
       print(100)
     end"
    "let rec f = (lambda x: g(x)), g = (lambda y: f(y)) in
     begin
       f(10);
       print(100)
     end";

  tcf "raise_seq_from_if_in_let"
    "let x = if true: if false: 30
                      else: begin print(10); 40 end
             else: 50 in
     x - 100"
    "begin
      print(10);
      let x = 40 in
      -60
     end";

  tcf "raise_seq_from_if_in_seq"
    "begin
       if false: 50
       else: if true: begin print(10); 40 end
             else: 30;
       print(-35)
     end"
    "begin
       print(10);
       40;
       print(-35)
     end"
];;

let cse_tests = [
  tcse "cse_num" "5" "5";
  tcse "cse_bool" "false" "false";
  tcse "cse_print1"  "print(9)" "print(9)";
  tcse "cse_print2" "(lambda x: print(x))"
                    "(lambda x: print(x))";
  tcse "cse_print3" "let t = print(5) in 7"
                    "let t = print(5) in 7";
  tcse "cse_fun1" "let t = (lambda x: x) in print(5)"
                  "let t = (lambda x: x) in print(5)";
  tcse "cse_fun2" "let t = (lambda x: print(x)) in t"
                  "let t = (lambda x: print(x)) in t";

  tcse "cse_simple" "let t = 2 + 4 in
                     let x = 2 + 4 in
                     x"
                    "let t = 2 + 4 in
                     let x = t in
                     t";

  tcse "cse_none" "let x = 5 in
                   let y = x in
                   y"
                  "let x = 5 in
                   let y = x in
                   x";

  tcse "cse_var" "let x = 5 in
                  let y = x in
                  let a = x + 2 in
                  a"
                 "let x = 5 in
                  let y = x in
                  let a = x + 2 in
                  a";

  tcse "cse_var_and_add" "let x = 5 in
                          let y = x in
                          let a = x + 2 in
                          let b = y + 2 in
                          b"
                         "let x = 5 in
                          let y = x in
                          let a = x + 2 in
                          let b = a in a";

  tcse "cse_impure1" "let x = print(5) in
                      let y = print(5) in
                      y"
                     "let x = print(5) in
                      let y = print(5) in
                      y";

  tcse "cse_impure2" "let x = (1, 2) in
                      let y = (1, 2) in
                      y"
                     "let x = (1, 2) in
                      let y = (1, 2) in
                      y";

  tcse "cse_impure3" "let x = 5 in
                      let y = print(x) in
                      let z = (lambda: print(x)) in
                      let a = z in
                      let b = z() in
                      let c = a() in
                      7"
                     "let x = 5 in
                      let y = print(x) in
                      let z = (lambda: print(x)) in
                      let a = z in
                      let b = z() in
                      let c = z() in
                      7";

  tcse "cse_impure4" "let z = (lambda: print(x)) in
                      let a = z in
                      let b = a() in
                      let c = a() in
                      7"
                     "let z = (lambda: print(x)) in
                      let a = z in
                      let b = z() in
                      let c = z() in
                      7";

  tcse "cse_inlambda" "(lambda: let t = 2 + 4 in
                                let x = 2 + 4 in
                                x)"
                      "(lambda: let t = 2 + 4 in
                                let x = t in
                                t)";

  tcse "cse_outlambda" "let t = 2 + 4 in
                        (lambda: let x = 2 + 4 in x)"
                       "let t = 2 + 4 in
                        (lambda: let x = t in t)";

  tcse "cse_pure_lambda" "let t = 2 + 4 in
                          let y = (lambda: let x = 2 + 4 in x) in
                          let z = y() in
                          let a = y() in
                          7"
                         "let t = 2 + 4 in
                          let y = (lambda: let x = t in t) in
                          let z = y() in
                          let a = z in
                          7";

  tcse "cse_app_diff_args" "let y = (lambda u: let x = 2 + 4 in x) in
                            let z = y(8) in
                            let a = y(7) in 7"
                           "let y = (lambda u: let x = 2 + 4 in x) in
                            let z = y(8) in
                            let a = y(7) in 7";

  tcse "cse_no_const_fold" "let r = 7 in
                            let y = (lambda u: 9) in
                            let z = y(7) in
                            let a = y(r) in
                            r"
                           "let r = 7 in
                            let y = (lambda u: 9) in
                            let z = y(7) in
                            let a = y(r) in
                            r";

  tcse "cse_pure_app" "let x = 5 in
                       let y = print(x) in
                       let z = (lambda: y) in
                       let a = z in
                       let b = z() in
                       let c = a() in
                       c"
                      "let x = 5 in
                       let y = print(x) in
                       let z = (lambda: y) in
                       let a = z in
                       let b = z() in
                       let c = b in
                       b" ;

  tcse "cse_if_func_impure" "let x = if true: (lambda: 5) else: (lambda: print(5)) in
                             let y = x() in
                             let z = x() in
                             z"
                            "let x = if true: (lambda: 5) else: (lambda: print(5)) in
                             let y = x() in
                             let z = x() in
                             z";

  tcse "cse_seq" "let x = (begin print(5); (lambda: print(5)) end) in
                  let y = x() in
                  let z = x() in
                  z"
                 "let x = (begin print(5); (lambda: print(5)) end) in
                  let y = x() in
                  let z = x() in
                  z" ;

  tcse "cse_pure_seq_lambda" "let x = (begin print(5); (lambda: 5) end) in
                              let y = x() in
                              let z = x() in
                              z"
                             "let x = (begin print(5); (lambda: 5) end) in
                              let y = x() in
                              let z = y in
                              y";

  tcse "cse_multi_pure_if" "let x = if true: (lambda: 5) else: (lambda: 6) in
                            let y = x() in
                            let z = x() in
                            y"
                           "let x = if true: (lambda: 5) else: (lambda: 6) in
                            let y = x() in
                            let z = y in
                            y";

  tcse "cse_nested" "let r = (lambda: let x = if true: (lambda: 5) else: (lambda: 6) in
                                      let y = x() in
                                      let z = x() in
                                      z) in
                     let t = r() in
                     let e = r() in
                     e"
                    "let r = (lambda: let x = if true: (lambda: 5) else: (lambda: 6) in
                                      let y = x() in
                                      let z = y in
                                      y) in
                     let t = r() in
                     let e = t in
                     t" ;

  tcse "cse_nested_pure" "let r = (lambda: let x = 6 + 7 in
                                           let y = x + 2 in
                                           let z = x + 2 in
                                           z) in
                          let t = r() in
                          let e = r() in
                          e"
                         "let r = (lambda: let x = 6 + 7 in
                                           let y = x + 2 in
                                           let z = y in
                                           y) in
                          let t = r() in
                          let e = t in
                          t";

  tcse "cse_letrec1" "let rec a = (lambda: 5),
                              b = (lambda: let x = 2 + 4 in
                                           let y = x * 7 in
                                           let z = x * 7 in
                                           print(z)),
                              c = (lambda: 7) in
                      let d = a() in
                      let e = a() in
                      let f = b() in
                      let g = b() in
                      g"
                     "let rec a = (lambda: 5),
                              b = (lambda: let x = 2 + 4 in
                                           let y = x * 7 in
                                           let z = y in
                                           print(y)),
                              c = (lambda: 7) in
                      let d = a() in
                      let e = d in
                      let f = b() in
                      let g = b() in
                      g";

  tcse "cse_letrec2" "let rec a = (lambda: b()),
                              b = (lambda: c),
                              c = (lambda: print(7)) in
                      let d = a() in
                      let e = a() in
                      let f = b() in
                      let g = b() in
                      g"
                     "let rec a = (lambda: b()),
                              b = (lambda: c),
                              c = (lambda: print(7)) in
                      let d = a() in
                      let e = d in
                      let f = b() in
                      let g = f in

                      f";
];;

let dae_tests = [
  tdae "eliminate_unused_letbind1" "let x = 10 in 11" "11";
  tdae "eliminate_unused_letbind2" "let x = 10, y = x + 3 in 13" "13";
  tdae "rewrite_unused_impure_letbind1"
    "let x = print(10) in 11"
    "begin
      print(10);
      11
    end";
  tdae "rewrite_unused_impure_letbind2"
    "let f = (lambda x: (lambda: x)) in
     let gen_zero = f(0) in
     let z = gen_zero() in
     100"
    "let f = (lambda x: (lambda: x)) in
     let gen_zero = f(0) in
     begin
      gen_zero();
      100
     end";

  tdae "eliminate_unused_letrecbinds1"
    "let rec f = (lambda x: x),
             g = (lambda y: y) in
       10"
    "10";
  tdae "eliminate_unused_letrecbinds2"
    "let rec f = (lambda x: h(x)),
             g = (lambda y: y),
             h = (lambda z: f(z)) in
       10"
    "10";

  tdae "eliminate_unused_letrecbinds3"
    "let rec f = (lambda x: f(x)) in
       10"
    "10";

  tdae "eliminate_unused_letrecbinds4"
    "let rec f = (lambda x: f(x)) in
       f"
    "let rec f = (lambda x: f(x)) in
       f";

  tdae "eliminate_unused_letrecbinds5"
    "let rec f = (lambda x: h(x)),
             g = (lambda y: y),
             h = (lambda z: f(z)) in
       g"
    "let g = (lambda y: y) in
       g";

  tdae "eliminate_unused_letrecbinds6"
    "let rec f = (lambda x: h(x)),
             g = (lambda y: y),
             h = (lambda z: f(z)) in
       f"
    "let rec f = (lambda x: h(x)),
             h = (lambda z: f(z)) in
       f";

  tdae "eliminate_unused_letrecbinds7"
    "let rec f = (lambda x: h(x)),
             g = (lambda y: y),
             h = (lambda z: f(z)),
             i = (lambda x: g(x)),
             j = (lambda y: j(y)),
             k = (lambda z: z) in
       (f, g, h, i, j, k)"
    "let rec f = (lambda x: h(x)),
             h = (lambda z: f(z)) in
     let g = (lambda y: y) in
     let i = (lambda x: g(x)) in
     let rec j = (lambda y: j(y)) in
     let k = (lambda z: z) in
       (f, g, h, i, j, k)";

  tdae "eliminate_unused_letrecbinds8"
    "let rec f = (lambda x: x) in
       f"
    "let f = (lambda x: x) in
       f";

  tdae "eliminate_pure_seq1"
    "begin
      10 + 2;
      100
     end"
    "100";
  tdae "eliminate_pure_seq2"
    "let f = (lambda x: x) in
     begin f(); 100 end"
    "100";
];;

let optimization_integration_tests = [
  topt "cse_cf_const_fold" "let r = 7 in
                            let y = (lambda u: 9) in
                            let z = y(7) in
                            let a = y(r) in
                            r"
                           "let r = 7 in
                            let y = (lambda u: 9) in
                            let z = 9 in
                            let a = 9 in
                            7" true true false;

  topt "cse_cf_simple" "let t = 2 + 4 in
                        let x = 2 + 4 in
                        x"
                       "let t = 6 in
                        let x = 6 in
                        6" true true false;

  topt "chained_inlining"
    "let b = true in
     let f0 = (lambda: (lambda: (lambda: (lambda: (lambda: if b: 100 else: 200))))) in
     let f1 = f0() in
     let f2 = f1() in
     let f3 = f2() in
     let f4 = f3() in
     let f5 = f4() in
     f5"
    "100" true true true;

  topt "multiple_passes_needed1"
    "# The first pass of optimization will eliminate the `10` from the seq within `f`
     # The second pass will see that `f` is now inlineable, inline it where it's called,
     # then eliminate the unused binding of `f`
     let f = (lambda x: begin 10; x end) in
     let y = f(9) + 10 in
     let z = f(9) + 9 in
     y - z"
    "1" true true true;

  topt "multiple_passes_needed2"
    "let x = 5 in
     let y = print(x) in
     let z = (lambda: print(x)) in
     let a = z in
     let b = z() in
     # The first pass of optimization will rewrite this `a` to `z`
     # The second pass of optimization will then inline that call to `z`,
     # allowing for the assignment of `z` to be eliminated
     let c = a() in
     7"
    "begin
       print(5);
       print(5);
       print(5);
       7
     end" true true true;
];;

let imm_suite = "imm_suite">:::imm_tests;;
let alloc_suite = "alloc_suite">:::alloc_tests;;
let prim1_suite = "prim1_suite">:::prim1_tests;;
let prim2_suite = "prim2_suite">:::prim2_tests;;
let prim1_prim2_mix_suite = "prim1_prim2_mix_suite">:::prim1_prim2_mix_tests;;
let if_suite = "if_suite">:::if_tests;;
let tup_access_suite = "tup_access_suite">:::tup_access_tests;;
let simple_funcall_suite = "simple_funcall_suite">:::simple_funcall_tests;;
let scope_suite = "scope_suite">:::scope_tests;;
let type_annotation_suite = "type_annotation_suite">:::type_annotation_tests;;
let vg_funcall_suite = "vg_funcall_suite">:::vg_funcall_tests;;
let gc_suite = "gc_suite">:::gc_tests;;
let purity_suite = "purity_suite">:::purity_tests;;
let cf_suite = "cf_suite">:::cf_tests;;
let cse_suite = "cse_suite">:::cse_tests;;
let dae_suite = "dae_suite">:::dae_tests;;
let optimization_integration_suite = "optimization_suite">:::optimization_integration_tests;;

let () = List.iter run_test_tt_main [
  imm_suite;
  alloc_suite;
  prim1_suite;
  prim2_suite;
  prim1_prim2_mix_suite;
  if_suite;
  tup_access_suite;
  simple_funcall_suite;
  scope_suite;
  type_annotation_suite;
  vg_funcall_suite;
  gc_suite;
  purity_suite;
  cf_suite;
  cse_suite;
  dae_suite;
  optimization_integration_suite;
];;
