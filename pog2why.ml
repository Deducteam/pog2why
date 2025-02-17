(*
  On records:
  Decl.make_record ?
  How to declare record types??
 *)

open Why3
open Whyutils

type ast = Element of string * (string * string) list * ast list | Text of string
exception Bad_Ast of ast

let debug = ref false

let rec print_ast =
  function
  | Text s -> print_endline s
  | Element(s1,args,s2) ->
     print_string s1;
     List.iter (fun (x,y) -> print_string (" " ^ x ^ "=" ^ y)) args;
     print_newline ();
     List.iter print_ast s2

(* Convert the whole XML file into an ast, kept in memory (consumes lot of memory if the XML is big) *)
let file_to_tree s =
  let open Markup in
  let input, close = file s in
  let output =
    input |> parse_xml |> signals |> trim |>
      tree
        ~text:(fun l -> Text(String.trim @@ String.concat "" l))
        ~element:(fun (_, name) l children -> Element (name, List.map (fun ((_,x),y) -> (x,y)) l, children)) |>
      function
      | Some x -> x
      | None -> failwith "Not an XML file"
  in close (); output
let parse_fail x = (* print_ast x; *) raise (Bad_Ast x)

let counter () =
  object
    val mutable x = 0

    method init =
      x <- 0

    method get =
      let y = x in
      x <- x + 1;
      y
  end

(*
  hashtable where keys are automatically generated unique integers
 *)
let one_table id =
  object
    val id = id
    val c = counter ()
    val h = Hashtbl.create 128

    method clear = c#init; Hashtbl.clear h

    method add x = Hashtbl.add h c#get x
    method iter f = Some (Hashtbl.iter (fun _ x -> f x) h)
    method get n =
      try
        Some (Hashtbl.find h n)
      with
        Not_found -> prerr_endline @@ "Not found: " ^ id ^ " " ^ string_of_int n; None
  end

let possible_contexts = ["B definitions";"ctx";"seext";"inv";"ass";"lprp";"inprp";"inext";"cst";"sets";"mchcst";"aprp";"abs";"imlprp";"imprp";"imext"]

let define_table = Hashtbl.create (List.length possible_contexts)
let po_table = one_table "Proof Obligation"
(* let anon_table = Hashtbl.create 128 *)

let type_infos =
  object
    val h = Hashtbl.create 128

    method clear = Hashtbl.clear h

    (* add index ast why3term *)
    method add i x t = Hashtbl.add h i (x, t)

    method get x =
      try
        let _,t =
          Hashtbl.find h x in t
      with
        Not_found -> failwith "type_infos"
  end

let env =
  object(this)
    val h = Hashtbl.create 128
    val closure = ref []
    val type_closure = ref []

    method clear = Hashtbl.clear h;
                   closure := [];
                   type_closure := []

    method add x t =
      let t' = type_infos#get t in
      let var_v = Term.create_vsymbol (Ident.id_fresh x) t' in
      let v = Term.t_var var_v  in
      begin
        Hashtbl.add h x v;
        closure := var_v :: !closure;
        type_closure := t' :: !type_closure;
        var_v, x
      end
    method remove x =
      Hashtbl.remove h x;
      closure := List.tl !closure; (* risky *)
      type_closure := List.tl !type_closure (* risky *)

    method get_closure = !closure
    method get_type_closure = !type_closure

    method new_const x t =
        let v = Term.create_fsymbol (Ident.id_fresh x) [] t in
        let v' = Term.t_app_infer v [] in
        let d = Decl.create_param_decl v in
        begin
            my_task := Task.add_decl !my_task d;
            Hashtbl.add h x v';
            v'
        end

    method get x t =
      match Hashtbl.find_opt h x with
      | Some v -> v
      | None -> this#new_const x (type_infos#get t)
  end

let type_name x = "t_" ^ x
let label_name x = "l_" ^ x
let var_name x s n = "v_" ^ x ^ (match s with None -> "" | Some x -> "'" ^ x) ^ "_" ^ n
let anon_set_name =
  let c = counter () in
  fun n -> "anon_set_" ^ n ^ "_" ^ (string_of_int c#get)
let anon_fun_name =
  let c = counter () in
  fun () -> "anon_fun_" ^ (string_of_int c#get)
let anon_bool_name =
  let c = counter () in
  fun () -> "anon_bool_" ^ (string_of_int c#get)
let goal_name =
  let c = counter () in
  fun () -> "goal_" ^ (string_of_int c#get)

let parse_type_group id_set =
  let id_check s =
    if Stdlib.not (Hashtbl.mem id_set s) then
      begin
        let new_id = Ty.create_tysymbol (Ident.id_fresh s) [] Ty.NoDef in
        Hashtbl.add id_set s new_id;
        my_task := Task.add_decl !my_task @@ Decl.create_ty_decl new_id;
        new_id
      end
    else
      try
        Hashtbl.find id_set s
      with
        Not_found -> failwith "id_check"
  in
  let rec foo =
    let parse_record_item =
      function
      | Element ("Record_Item", args, [x]) ->
         let label = List.assoc "label" args |> label_name in
         failwith "TODO struct items (how?)"
      | x -> parse_fail x
    in
    function
    | Element ("Binary_Exp", args, [x;y]) ->
       Ty.ty_tuple [foo x; foo y]
    | Element ("Id", args, children) ->
       begin
         match List.assoc "value" args with
         | "INTEGER" -> Ty.ty_int
         | "REAL" -> Ty.ty_real
         | "FLOAT" -> Ty.ty_real
         | "BOOL" -> Ty.ty_bool
         | "STRING" -> Ty.ty_str
         | s -> let s = (type_name s) in Ty.ty_app (id_check s) []
       end
    | Element ("Unary_Exp", args, [x]) -> Ty.ty_app set [foo x]
    | Element ("Struct", args, children) -> failwith "TODO struct (how?)"
    | x -> parse_fail x
  in foo

let id_set = Hashtbl.create 128

let parse_type_infos =
  List.iter @@
    function
    | Element ("Type", args, [x]) ->
       let i = int_of_string @@ List.assoc "id" args in
       let t = parse_type_group id_set x in
       type_infos#add i x t
    | x -> parse_fail x

let element_type Ty.{ ty_node = n; ty_tag = _ } =
  match n with
  | Tyapp (_,t::_) -> t
  | _ -> failwith "element_type"

let rec my_tuple f =
  function
  | [] -> failwith "should not happen"
  | [t] -> t
  | t1 :: t2 :: l -> my_tuple f (f [t1;t2] :: l)

let close_type t =
  match env#get_type_closure with
  | [] -> t
  | l -> Ty.ty_func (my_tuple Ty.ty_tuple l) t

let close_term t =
  match env#get_closure with
  | [] -> t
  | l -> Term.t_func_app t (my_tuple Term.t_tuple (List.map Term.t_var l))

let create_set name t l =
  let t = type_infos#get t in
  let t' = close_type t in
  let set = close_term @@ env#new_const name t' in
  let name = Decl.create_prsymbol (Ident.id_fresh (name ^ "_pred")) in
  let var_v = Term.create_vsymbol (Ident.id_fresh "x") (element_type t) in
  let v = Term.t_var var_v in
  let left_term = binary_op ":" v set in
  let right_term = nary_op "or" (List.map (fun x -> binary_op "=" v x) l) in
  let term = Term.t_forall_close (var_v::env#get_closure) [] (binary_op "<=>" left_term right_term) in
  my_task := Task.add_decl !my_task (Decl.create_prop_decl Paxiom name term);
  set

let create_comprehension name t var_v pred =
  let v = List.map Term.t_var var_v in
  let foo = Ty.ty_app set [my_tuple Ty.ty_tuple t] in
  let set = close_term @@ env#new_const name (close_type foo) in
  let name = Decl.create_prsymbol (Ident.id_fresh (name ^ "_pred")) in
  let tuple = my_tuple Term.t_tuple v in
  let left_term = binary_op ":" tuple set in
  let right_term = pred in
  let term = Term.t_forall_close (List.concat [var_v;env#get_closure]) [] (binary_op "<=>" left_term right_term) in
  my_task := Task.add_decl !my_task (Decl.create_prop_decl Paxiom name term);
  set

let create_fun name t t' var_v pred body =
  let v = List.map Term.t_var var_v in
  let foo =
    Ty.ty_app set [Ty.ty_tuple [my_tuple Ty.ty_tuple t; t']]
  in
  let set = close_term @@ env#new_const name (close_type foo) in
  let name = Decl.create_prsymbol (Ident.id_fresh (name ^ "_pred")) in
  let var_x = Term.create_vsymbol (Ident.id_fresh "x") t' in
  let x = Term.t_var var_x in
  let tuple1 = my_tuple Term.t_tuple v in
  let tuple2 = Term.t_tuple [tuple1;x] in
  let left_term = binary_op ":" tuple2 set in
  let right_term = nary_op "&" [pred; binary_op "=" x body] in
  let term = Term.t_forall_close (List.concat [var_v;[var_x];env#get_closure]) [] (binary_op "<=>" left_term right_term) in
  my_task := Task.add_decl !my_task (Decl.create_prop_decl Paxiom name term);
  set

let create_bool b =
  let name = anon_bool_name () in
  let c = close_term @@ env#new_const name (close_type Ty.ty_bool) in
  let name = Decl.create_prsymbol (Ident.id_fresh (name ^ "_pred")) in
  let left_term = binary_op "=" c Term.t_bool_true in
  let term = Term.t_forall_close env#get_closure [] (binary_op "<=>" left_term b) in
  my_task := Task.add_decl !my_task (Decl.create_prop_decl Paxiom name term);
  c

let parse_variables =
  let foo =
    function
    | Element ("Id", args, []) ->
       let o = List.assoc "typref" args in
       let n = o |> int_of_string in
       let id = List.assoc "value" args in
       let name = var_name id (List.assoc_opt "suffix" args) o in
       env#add name n, type_infos#get (int_of_string o);
    | x -> parse_fail x
  in List.map foo

let get_type =
  function
    Element (_, args, _) ->
    List.assoc "typref" args |> int_of_string |> type_infos#get(* TODO: it does not work if Body is a Record_Update *)
  | x -> parse_fail x

let rec parse_pred =
  function
  | Element ("Binary_Pred", args, [x;y]) ->
     let op = List.assoc "op" args |> binary_op in
     let c1 = parse_pred x in
     let c2 = parse_pred y in
     op c1 c2
  | Element ("Exp_Comparison", args, [x;y]) ->
     let op = List.assoc "op" args |> binary_op in
     let c1 = parse_exp x in
     let c2 = parse_exp y in
     op c1 c2
  | Element ("Quantified_Pred", args, [Element ("Variables", _, children);Element ("Body", _, [b])]) ->
     begin
       try
         let op = List.assoc "type" args |> quantified_pred_op in
         let var_v, t = List.split @@ parse_variables children in
         let var_v, v = List.split var_v in
         let p = parse_pred b in
         let () = List.iter env#remove v in
         op var_v p
       with
         Not_found -> failwith "quantified pred"
     end
  | Element ("Unary_Pred", args, [x]) as err ->
     let () = if List.assoc "op" args <> "not" then parse_fail err in (* for debugging *)
     Term.t_not (parse_pred x)
  | Element ("Nary_Pred", args, children) ->
     let op = List.assoc "op" args |> nary_op in
     let l = List.map parse_pred children in
     op l
  | x -> parse_fail x
and parse_exp =
  let parse_record_item =
    function
    | Element ("Record_Item", args, [x]) ->
       let label = List.assoc "label" args |> label_name in
       let c = parse_exp x in
       failwith "TODO records"
    | x -> parse_fail x
  in
  function
  | Element ("Unary_Exp", args, [x]) ->
     let op = List.assoc "op" args |> unary_op in
     let c = parse_exp x in
     op c
  | Element ("Binary_Exp", args, [x;y]) ->
     let op = List.assoc "op" args |> binary_op in
     let c1 = parse_exp x in
     let c2 = parse_exp y in
     begin
       try
         op c1 c2
       with
         _ -> failwith "nani"
     end
  | Element ("Ternary_Exp", args, [x;y;z]) ->
     let op = List.assoc "op" args |> ternary_op in
     let c1 = parse_exp x in
     let c2 = parse_exp y in
     let c3 = parse_exp z in
     op c1 c2 c3
  | Element ("Nary_Exp", args, children) ->
     let o = List.assoc "typref" args in
     let t = o |> int_of_string in
     let nary_op =
       function
       | "[" -> fun l -> failwith "TODO sequence"
       | "{" -> fun l ->
                begin
                  try
                    create_set (anon_set_name o) t l
                  with
                    _ -> failwith "found it"
                end
       | x -> failwith ("Invalid n-ary expression : " ^ x)
     in
     let op = List.assoc "op" args |> nary_op in
     let c = List.map parse_exp children in
     op c
  | Element ("Boolean_Literal", args, _) ->
     begin
       try
         match List.assoc "value" args with
         | "TRUE" -> Term.t_bool_true
         | "FALSE" -> Term.t_bool_false
         | _ -> failwith "wrong Boolean literal"
       with
         _ -> failwith "should not happen"
     end
  | Element ("Boolean_Exp", _, [x]) ->
     let c = parse_pred x in
     create_bool c
  (* failwith "TODO boolean exp" *)
  | Element ("EmptySet", args, _) ->
     let t = List.assoc "typref" args |> int_of_string in
     let t = type_infos#get t in
     Term.t_app empty [] (Some t)
  | Element ("EmptySeq", args, children) ->
     let t = List.assoc "typref" args |> int_of_string in
     let t = type_infos#get t in
     Term.t_app empty [] (Some t)
  | Element ("Id", args, children) ->
     begin
       let o = List.assoc "typref" args in
       let t = o |> int_of_string in
       let id = List.assoc "value" args in
       let a = List.assoc_opt "suffix" args in
       let name = var_name id a o in
       (* try *)
         env#get name t
       (* with
         _ -> failwith (name ^ "???") *)
     end
  | Element ("Integer_Literal", args, children) ->
     let v = List.assoc "value" args in
     Term.t_int_const (BigInt.of_string v)
  | Element ("Quantified_Exp", args, [Element ("Variables", _, children);Element ("Pred", _, [p]);Element ("Body", _, [b])]) ->
     begin
       try
         let op = List.assoc "type" args |> quantified_exp_op in
         let var_v, t = List.split @@ parse_variables children in
         let var_v, v = List.split var_v in
         let t' = get_type b in
         let p =
           try parse_pred p
           with
             _ -> failwith "pred"
         in
         let b =
           try
             debug := true;
             let b = parse_exp b in
             debug := false;
             b
           with
             x -> raise x
         in
         let () = List.iter env#remove v in
         let s = create_fun (anon_fun_name ()) t t' var_v p b in
         op s
       with
         Not_found -> failwith "quantified exp"
     end
  | Element ("Quantified_Set", args, [Element ("Variables", _, children);Element ("Body", _, [p])]) ->
     begin
       try
         let o = List.assoc "typref" args in
         let var_v, t = List.split @@ parse_variables children in
         let var_v, v = List.split var_v in
         let p =
           try parse_pred p
           with
             _ -> failwith "pred"
         in
         let () = List.iter env#remove v in
         create_comprehension (anon_set_name o) t var_v p
       with
         _ -> failwith "quantified set"
     end
  | Element ("STRING_Literal", args, children) ->
     let v = List.assoc "value" args in
     Term.t_string_const v
  | Element ("Struct", args, children) ->
     failwith "TODO struct"
  | Element ("Record", args, children) ->
     failwith "TODO record"
  | Element ("Real_Literal", args, children) ->
     let v = "{| " ^ List.assoc "value" args ^ " |}" in
     begin
       print_endline "Warning: reals are not fully supported. (TODO)";
       Term.t_real_const BigInt.zero
     end
  | Element ("Record_Update", args, [x;y]) ->
     failwith "TODO record update"
  | Element ("Record_Field_Access", args, [Element(_, args', _) as x]) ->
     failwith "TODO record field access"
  | x -> parse_fail x

let parse_id =
  function
  | Element ("Id", args, []) ->
     let o = List.assoc "typref" args in
     let t = o |> int_of_string in
     let v = List.assoc "value" args in
     let s = List.assoc_opt "suffix" args in
     let name = var_name v s o in
     begin
       env#new_const name (type_infos#get t)
     end
  | x -> parse_fail x

let parse_set name t =
  function
  | [Element ("Enumerated_Values", _, children)] ->
     let l = List.map parse_id children in
     create_set name t l
  | [] -> env#new_const name (type_infos#get t)
  | _ -> assert false

let parse_def name x =
  try
    let content = ref [] in
    let foo =
      function
      | Element ("Set", _, Element("Id", args,[]) :: l) ->
         begin
           try
             let o = List.assoc "typref" args in
             let t = o |> int_of_string in
             let v = List.assoc "value" args in
             let s = List.assoc_opt "suffix" args in
             let name = var_name v s o in
             ignore (parse_set name t l)
           with
             Not_found -> failwith "set"
         end
      | Element (_, args,_) as a ->
         begin
           try
             let term = parse_pred a in
             content := term :: !content
           with
             Not_found -> failwith "predicate"
         end
      | x -> parse_fail x
    in List.iter foo x;
       let name = Term.create_psymbol (Ident.id_fresh name) [] in
       let term = nary_op "&" (List.rev !content) in
       let decl = Decl.make_ls_defn name [] term in
       my_task := Task.add_decl !my_task (Decl.create_logic_decl [decl]);
       Term.ps_app name []
  with
    Not_found -> failwith "parse_def"

let parse_goal def hyp loc_hyp l =
  let rec foo =
    function
    | Element ("Tag", _, _) :: l -> foo l
    | Element ("Ref_Hyp", args, _) :: l ->
       begin
         try
           let n = List.assoc "num" args in
           let h = n |> Hashtbl.find loc_hyp |> Lazy.force in
           foo l |> Term.t_implies h
         with
           Not_found -> failwith "parse_goal"
       end
    | Element ("Goal", _, [x]) :: _ ->
       parse_pred x
    | Element ("Proof_State", _, _) :: l -> foo l
    | x :: l -> parse_fail x
    | _ -> assert false
  in
  let name = Decl.create_prsymbol (Ident.id_fresh (goal_name ())) in
  let term = foo l in
  let term = Queue.fold (fun x h -> Term.t_implies (Lazy.force h) x) term hyp in
  try
    let term = Queue.fold (fun x h -> Term.t_implies (Lazy.force (Hashtbl.find define_table h)) x) term def in
    my_task := Task.add_decl !my_task @@ Decl.create_prop_decl Decl.Pgoal name term
  with
    Not_found -> failwith "parse_goal2"

let parse_hyp name h =
  let name = Term.create_psymbol (Ident.id_fresh name) [] in
  let term = parse_pred h in
  let decl = Decl.make_ls_defn name [] term in
  my_task := Task.add_decl !my_task (Decl.create_logic_decl [decl]);
  Term.ps_app name []

let add_po_table c co =
  let def = Queue.create () in
  let hyp = Queue.create () in
  let loc_hyp = Hashtbl.create 128 in
  let goal = one_table "Goal" in
  let count = counter () in
  let pass =
    function
    | Element("Tag", _, [Text(s)]) -> ()
    | Element("Definition", args, []) ->
       Queue.add (List.assoc "name" args) def
    | Element("Hypothesis", _, [x]) ->
       Queue.add (lazy (parse_hyp ("hyp_" ^ (string_of_int count#get) ^ "_" ^ co) x)) hyp
    | Element("Local_Hyp", args, [x]) ->
       let n = List.assoc "num" args in
       Hashtbl.add loc_hyp n (lazy (parse_hyp ("loc_hyp_" ^ n ^ "_" ^ co) x))
    | Element("Simple_Goal", _, l) ->
       goal#add (lazy (parse_goal def hyp loc_hyp l))
    | x -> parse_fail x
  in
  begin
    List.iter pass c;
    po_table#add goal
  end

(* None for all the goals, Some x for the goal x *)
let parse_po choice goal =
  match choice with
  | None -> goal#iter Lazy.force
  | Some x -> match goal#get x with
              | Some g -> Some (Lazy.force g)
              | None -> None

(*
  TODO:
  - for sets defined by comprehension, and booleans defined by predicates, have a hashtbl for them
  - for predicates:
  function that transform them into terms
  - for terms:
  function that transform them into terms
  - for sets:
  functions that transform them into term, and give them a unique name (through a hashtable)
  - for define blocks:
  function that transform sets into declarations, and predicates into axioms, while removing stuff that has already been declared
  - for proof_obligation blocks:
  function that process the "Definition" blocks (unqueue them), add hypotheses as axioms (unqueue them), parse local-hyps (print them only once, if reasked for, only give their name) (Lazy monad?), then parse the wanted goal

  Idea:
  - there is an environment for declaring types (new types will be dealt with later) DONE
  - there is an environment for declaring (and retrieving) variables DONE
  - there is a way to create terms / propositions DONE (almost)
  - there is a way to declare new functions in the theory DONE
  - there is a way to declare new hypotheses / axioms in the theory DONE
  - there is a way to retrieve the name corresponding to the declaration of a "define" block TODO
  - lazy computation: only declare what we depend on (TODO)
  - top-down approach HINT

  Organization of the POG file:
  - a list of Define blocks
  - a list of ProofObligation blocks
  - a TypeInfos block


Roadblocks:
  - TODO
 *)

let get_all_goals x =
  let c = ref (-1) in
  let d = ref (-1) in
  let foo =
    function
    | Element("Simple_Goal", _, l) -> d := !d + 1; [(!c,!d)]
    | _ -> []
    in
  let bar =
    function
    | Element ("Proof_Obligation", args, children) -> c := !c+1; d := -1; List.concat @@ List.map foo children
    | _ -> []
  in List.concat @@ List.map bar x

(* choice is None for getting all the POs, or Some([(a1,b1);...;(an,bn)]) for goals a1:b1 ... an:bn *)
let rec parse_pog choice =
  let co = counter () in
  let pass1 =
    function
    | Element("Define", args, children) ->
       let x = List.assoc "name" args in
       Hashtbl.add define_table x (lazy (parse_def (if x = "B definitions" then "b_def" else x) children))
    | Element ("Proof_Obligation", args, children) ->
       add_po_table children (string_of_int co#get)
    | Element ("TypeInfos", args, children) -> parse_type_infos children
    | _ -> ()
  in
  let pass2 l children =
    begin
      let error a b = prerr_endline ("Goal " ^ string_of_int a ^ ":" ^ string_of_int b ^" does not exist."); exit 1 in
      let parse (a,b) =
        print_endline (string_of_int a ^ " " ^ string_of_int b);
        my_task := new_task;
        type_infos#clear;
        Hashtbl.clear define_table;
        Hashtbl.clear id_set;
        po_table#clear;
        env#clear;
        List.iter pass1 children;
        match Option.bind (po_table#get a) (parse_po (Some b)) with
        | None -> error a b
        | Some () -> !my_task
      in
      Seq.map parse (List.to_seq l)
    end
  in
  function
  | Element ("Proof_Obligations", _, children) ->
     let l =
       match choice with
       | None ->
          get_all_goals children
       | Some l -> l
     in pass2 l children
  | x -> parse_fail x

let printme out = Format.fprintf out "%a" Pretty.print_task !my_task

let print_tptp driver out =
  Driver.print_task driver out !my_task

let result prover driver : Call_provers.prover_result =
  Call_provers.wait_on_call
    (Driver.prove_task
       ~limits:Call_provers.{limit_time = 3.; limit_mem = 0; limit_steps = 0}
       ~config:main
       ~command:(Whyconf.get_complete_command prover ~with_steps:false)
    driver !my_task)


           (*
pog2why
	version 1.0
	copyright CLEARSY Systems Engineering 2019
Translates Atelier B proof obligation file to Why3 format.
	pog2why -a N1 M1 -a N2 M2 ... -a Nk Mk -i file.pog -o file.why
		-a N M
			selects the N-th Simple_Goal child element from the M-th Proof_Obligation
			element for translation
		-A
			translates all goals
		-i FILE
			specifies the path for the input file
		-o FILE
			specifies the path for the output file
		-h
			prints help
	Note: options -A and -a are exclusive

            *)
