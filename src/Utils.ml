exception Invalid_Env of string

let parse_constr = Pcoq.parse_string Pcoq.Constr.constr;;

let str_to_constr str = (parse_constr str)

let strip str = 
  let str = Str.replace_first (Str.regexp "^ +") "" str in
  Str.replace_first (Str.regexp " +$") "" str

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try 
      ignore (Str.search_forward re s1 0); 
      true
  with Not_found -> false

let get_str_of_pp pp_expr : string= 
    Pp.string_of_ppcmds pp_expr

let get_exp_str env sigma expr : string =
  (get_str_of_pp (Printer.pr_goal_concl_style_env env sigma expr))

let get_sexp_compatible_expr_str env sigma expr : string = 
  "(" ^ (get_exp_str env sigma expr) ^ ")"

let get_term_count terms exp =
    List.fold_left (fun acc (e, count) -> if Sexp.equal e exp then (count) else acc) 0 terms

let add_term (acc : (Sexp.t list * int) list) (term: Sexp.t list): (Sexp.t list * int) list * int =
    let count = (get_term_count acc term) + 1
    in List.append acc [(term, count)], count

let add_term_remove_dup (acc : Sexp.t list list)
                        (term: Sexp.t list): 
                        (Sexp.t list) list =
  let exists = List.exists (fun e -> Sexp.equal e term) acc
  in if exists then acc else List.append acc [term]

let next_val counter = 
  fun () ->
    counter := (!counter) + 1;
    !counter

let get_hyps hyps =
  List.map
    (function
    | Context.Named.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), y)
    | Context.Named.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), y))
    hyps

let get_hyps_strl hyps env sigma =
  List.fold_left (fun acc (v, hyp) -> 
                              let var_str = (Names.Id.to_string v)
                              in let regex_ih  = Str.regexp "IH*"
                              in let regex_H = Str.regexp "H*"
                              in let is_match = 
                                    Str.string_match regex_ih var_str 0
                              in (if is_match
                                  then (get_sexp_compatible_expr_str env sigma hyp)::acc
                                  else acc)
                 ) [] (get_hyps hyps)

let string_of_sexp_list elem =
"[" ^ (List.fold_left (fun accl e -> (Sexp.string_of_sexpr e) ^ ";" ^ accl) "" elem) ^ "]"

let econstr_to_constr x = EConstr.to_constr Evd.empty x

let add_var acc var =
  let var_exists = List.exists (fun e -> String.equal e var) acc
  in if var_exists then acc else (var :: acc)

let get_vars_in_expr expr =
  let constr_goal = (econstr_to_constr expr)
  in let rec aux constr_goal (vars : string list) =
      match Constr.kind constr_goal with
      | Var v -> add_var vars (Names.Id.to_string v)
      | Cast (ty1,ck,ty2) ->  let ty1_vars = aux ty1 vars
                              in aux ty2 ty1_vars
      | Prod (na,ty,c)    ->  let ty_vars = aux ty vars
                              in aux c ty_vars
      | Lambda (na,ty,c)  ->  let ty_vars = aux ty vars
                              in aux c ty_vars
      | LetIn (na,b,ty,c) ->  let ty_vars = aux ty vars
                              in aux c ty_vars
      (* | Const (c,u) -> print_endline (Names.Constant.to_string c); vars *)
      | App (f,args)      ->
      let f_vars = aux f vars
                              in let args_vars = (vars_of_constrarray args)
                              in List.fold_left 
                                  (fun acc v -> add_var acc v) f_vars args_vars
      | Proj (p,c)        ->  aux c vars
      | Case (ci,p,c,bl)  ->  aux c vars
      | _ -> vars
and vars_of_constrarray a : string list =
    List.fold_left (fun acc elem -> List.append acc (aux elem acc)) [] (Array.to_list a)
in aux constr_goal []


let get_funcs_in_expr expr funcs=
  let constr_goal = (econstr_to_constr expr)
  in let rec aux constr_goal (funcs : string list) =
      match Constr.kind constr_goal with
      | Cast (ty1,ck,ty2) ->  let ty1_vars = aux ty1 funcs
                              in aux ty2 ty1_vars
      | Prod (na,ty,c)    ->  let ty_vars = aux ty funcs
                              in aux c ty_vars
      | Lambda (na,ty,c)  ->  let ty_vars = aux ty funcs
                              in aux c ty_vars
      | LetIn (na,b,ty,c) ->  let ty_vars = aux ty funcs
                              in aux c ty_vars
      | Const (c,u) -> add_var funcs (Names.Constant.to_string c)
      | App (f,args)      ->
      let f_vars = aux f funcs
                              in let args_vars = (vars_of_constrarray args)
                              in List.fold_left 
                                  (fun acc v -> add_var acc v) f_vars args_vars
      | Proj (p,c)        ->  aux c funcs
      | Case (ci,p,c,bl)  ->  aux c funcs
      | _ -> funcs
and vars_of_constrarray a : string list =
    List.fold_left (fun acc elem -> List.append acc (aux elem acc)) [] (Array.to_list a)
in aux constr_goal funcs

let get_env_var env_var : string =
  let env = Unix.environment ()
  in Array.fold_left (fun path p -> let p_list = Array.of_list(String.split_on_char '=' p)
                                    in let var = (try (Array.get p_list 0) with Invalid_argument _ -> "")
                                    in let var_path = try (Array.get p_list 1) with Invalid_argument _ -> ""
                                    in if String.equal var env_var then var_path else path
                     )
                     "" env

let get_modules file_name : string list =
  (* let cmd = "grep \"Require Import\" " ^ file_name
  in let modules = FileUtils.run_cmd cmd
  in modules *)
  []
   (* List.fold_left (fun acc m-> (List.nth (String.split_on_char ' ' m) 1)::acc) [] modules *)

let gen_rand_str length =
let gen() = match Random.int(26+26+10) with
    n when n < 26 -> int_of_char 'a' + n
  | n when n < 26 + 26 -> int_of_char 'A' + n - 26
  | n -> int_of_char '0' + n - 26 - 26 in
let gen _ = String.make 1 (char_of_int(gen())) in
String.concat "" (Array.to_list (Array.init length gen))

let slice_list (start_i: int) (end_i: int) (lst: 'a list) = 
  let _, slice = List.fold_right (fun e (index, acc) -> 
                                  let n_acc = if index >= start_i && index <= end_i
                                              then e :: acc
                                              else acc
                                  in index + 1, n_acc
                                 ) lst (0,[])
  in slice

let cpu_count () = 
  try 
    (match Sys.os_type with 
    | "Win32" -> int_of_string (Sys.getenv "NUMBER_OF_PROCESSORS") 
    | _ ->
        (
          let i = Unix.open_process_in "getconf _NPROCESSORS_ONLN" in
          let close () = ignore (Unix.close_process_in i) in
          try Scanf.fscanf i "%d" (fun n -> close (); n) with e -> close (); raise e
        )
    )
  with  _ -> 1
  
let env_setup () =
  let prover_path = get_env_var Consts.prover
  in
  if String.equal prover_path "" then raise (Invalid_Env "Prover path not set!")
  else Consts.prover_path := if prover_path.[(String.length prover_path) -1] = '/' 
                           then prover_path
                           else prover_path ^ "/";

  if String.equal !Consts.synthesizer "myth" then
  (
    let synthesizer_path = get_env_var "MYTH"
    in if String.equal synthesizer_path "" then raise (Invalid_Env "Synthesizer path not set!")
    else 
    Consts.synthesizer_path := synthesizer_path;
  );

  let rewriter_path = get_env_var Consts.rewriter
  in if String.equal rewriter_path "" then raise (Invalid_Env "AST rewriter path not set!")
  else Consts.rewriter_path := rewriter_path;

  let coqofocaml_path = get_env_var "COQOFOCAML"
  in if String.equal coqofocaml_path "" then raise (Invalid_Env "COQOFOCAML path not set!")
  else Consts.coq_of_ocaml_path := coqofocaml_path;

  let lfind_path = get_env_var "LFIND"
  in if String.equal lfind_path "" then raise (Invalid_Env "LFIND SRC path not set!")
  else Consts.lfind_path := if lfind_path.[(String.length lfind_path) -1] = '/' 
                            then lfind_path
                            else lfind_path ^ "/";