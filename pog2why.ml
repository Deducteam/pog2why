open Why3
open Whyutils

type ast = Element of string * (string * string) list * ast list | Text of string
exception Bad_Ast of ast

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
let parse_fail x = raise (Bad_Ast x)

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

    method add x = Hashtbl.add h c#get x
    method iter f = Hashtbl.iter (fun _ x -> f x) h
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

    (* add index ast why3term *)
    method add i x t = Hashtbl.add h i (x, t)

    method get x = let _,t = Hashtbl.find h x in t
  end

let env =
  object(this)
    val h = Hashtbl.create 128

    method add x t =
      let t' = type_infos#get t in
      let v = Term.t_var @@ Term.create_vsymbol (Ident.id_fresh x) t' in
      begin
        Hashtbl.add h (x,t) v;
        v
      end
    method remove x t = Hashtbl.remove h (x,t)

    method new_const x t =
      let t' = type_infos#get t in
      let v = Term.create_fsymbol (Ident.id_fresh x) [] t' in
      let v' = Term.t_app_infer v [] in
      let d = Decl.create_param_decl v in
      begin
        my_theory := Theory.add_decl !my_theory d;
        Hashtbl.add h (x,t) v';
        v'
      end

    method get x t =
      match Hashtbl.find_opt h (x,t) with
      | Some v -> v
      | None -> this#new_const x t
  end

let type_name x = "t_" ^ x
let label_name x = "l_" ^ x
let var_name x s n = "v_" ^ x ^ (match s with None -> "" | Some x -> "'" ^ x) ^ "_" ^ n
let anon_set_name =
  let c = counter () in
  fun n -> "anon_set_" ^ n ^ "_" ^ (string_of_int c#get)
let anon_fun_name = "anon_fun"
let anon_bool_name = "anon_bool"

let parse_type_group id_set =
  let id_check s =
    if Stdlib.not (Hashtbl.mem id_set s) then
      begin
        let new_id = Ty.create_tysymbol (Ident.id_fresh s) [] Ty.NoDef in
        Hashtbl.add id_set s new_id;
        my_theory := Theory.add_decl !my_theory @@ Decl.create_ty_decl new_id;
        new_id
      end
    else Hashtbl.find id_set s
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

let parse_type_infos =
  let id_set = Hashtbl.create 128 in
  List.iter @@
    function
    | Element ("Type", args, [x]) ->
       let i = int_of_string @@ List.assoc "id" args in
       let t = parse_type_group id_set x in
       type_infos#add i x t
    | x -> parse_fail x

let element_type t =
  let Ty.{ ty_node = n; ty_tag = _ } = type_infos#get t in
  match n with
  | Tyapp (_,t::_) -> t
  | _ -> failwith "element_type"

let create_set name t l =
  let set = env#new_const name t in
  let name = Term.create_psymbol (Ident.id_fresh (name ^ "_pred")) [] in
  let var_v = Term.create_vsymbol (Ident.id_fresh "x") (element_type t) in
  let v = Term.t_var var_v in
  let left_term = binary_op ":" v set in
  let right_term = nary_op "or" (List.map (fun x -> binary_op "=" v x) l) in
  let term = Term.t_forall_close [var_v] [] (binary_op "<=>" left_term right_term) in
  let decl = Decl.make_ls_defn name [] term in
  my_theory := Theory.add_decl !my_theory (Decl.create_logic_decl [decl]);
  set

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
  | Element ("Quantified_Pred", args, [Element ("Variables", _, children);Element ("Body", _, [b])]) -> failwith "TODO quantified pred"
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
     op c1 c2
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
       | "{" -> fun l -> create_set (anon_set_name o) t l
       | x -> failwith ("Invalid n-ary expression : " ^ x)
     in
     let op = List.assoc "op" args |> nary_op in
     let c = List.map parse_exp children in
     op c
  | Element ("Boolean_Literal", args, _) ->
     begin
       match List.assoc "value" args with
       | "TRUE" -> Term.t_bool_true
       | "FALSE" -> Term.t_bool_false
       | _ -> failwith "wrong Boolean literal"
     end
  | Element ("Boolean_Exp", _, [x]) ->
     let c = parse_pred x in
     print_endline "TODO boolean exp"; Term.t_bool_true
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
     let o = List.assoc "typref" args in
     let t = o |> int_of_string in
     let id = List.assoc "value" args in
     let a = List.assoc_opt "suffix" args in
     let name = var_name id a o in
     env#get name t
  | Element ("Integer_Literal", args, children) ->
     let v = List.assoc "value" args in
     Term.t_int_const (BigInt.of_string v)
  | Element ("Quantified_Exp", args, [Element ("Variables", _, children);Element ("Pred", _, [p]);Element ("Body", _, [b])]) ->
     failwith "TODO quantified expressions"
  | Element ("Quantified_Set", args, [Element ("Variables", _, children);Element ("Body", _, [b])]) ->
     failwith "TODO sets by comprehension"
  | Element ("STRING_Literal", args, children) ->
     let v = List.assoc "value" args in
     begin
       print_endline "Warning: strings are not fully supported.";
       Term.t_string_const v
     end
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
       env#new_const name t
     end
  | x -> parse_fail x

let parse_set name t =
  function
  | [Element ("Enumerated_Values", _, children)] ->
     let l = List.map parse_id children in
     create_set name t l
  | [] -> env#new_const name t
  | _ -> assert false

let parse_def name x =
  let content = ref [] in
  let foo =
    function
    | Element ("Set", _, Element("Id", args,[]) :: l) ->
       let o = List.assoc "typref" args in
       let t = o |> int_of_string in
       let v = List.assoc "value" args in
       let s = List.assoc_opt "suffix" args in
       let name = var_name v s o in
       ignore (parse_set name t l)
    | Element (_, args,_) as a ->
       let term = parse_pred a in
       content := term :: !content
    | x -> parse_fail x
  in List.iter foo x;
     let name = Term.create_psymbol (Ident.id_fresh name) [] in
     let term = nary_op "&" (List.rev !content) in
     let decl = Decl.make_ls_defn name [] term in
     my_theory := Theory.add_decl !my_theory (Decl.create_logic_decl [decl]);
     Term.ps_app name []

let parse_goal def hyp loc_hyp l =
  let rec foo =
    function
    | Element ("Tag", _, _) :: l -> foo l
    | Element ("Ref_Hyp", args, _) :: l ->
       let n = List.assoc "num" args in
       let h = n |> Hashtbl.find loc_hyp |> Lazy.force in
       foo l |> Term.t_implies h
    | Element ("Goal", _, [x]) :: _ ->
       parse_pred x
    | Element ("Proof_State", _, _) :: l -> foo l
    | x :: l -> parse_fail x
    | _ -> assert false
  in
  let name = Decl.create_prsymbol (Ident.id_fresh "goal") in
  let term = foo l in
  let term = Queue.fold (fun x h -> Term.t_implies (Lazy.force h) x) term hyp in
  let term = Queue.fold (fun x h -> Term.t_implies (Lazy.force (Hashtbl.find define_table h)) x) term def in
  my_theory := Theory.add_decl !my_theory @@ Decl.create_prop_decl Decl.Pgoal name term

let parse_hyp name h =
  let name = Term.create_psymbol (Ident.id_fresh name) [] in
  let term = parse_pred h in
  let decl = Decl.make_ls_defn name [] term in
  my_theory := Theory.add_decl !my_theory (Decl.create_logic_decl [decl]);
  Term.ps_app name []

let add_po_table c =
  let def = Queue.create () in
  let hyp = Queue.create () in
  let loc_hyp = Hashtbl.create 128 in
  let goal = one_table "Goal" in
  let pass =
    function
    | Element("Tag", _, [Text(s)]) -> ()
    | Element("Definition", args, []) ->
       Queue.add (List.assoc "name" args) def
    | Element("Hypothesis", _, [x]) ->
       Queue.add (lazy (parse_hyp "name" x)) hyp
    | Element("Local_Hyp", args, [x]) ->
       let n = List.assoc "num" args in
       Hashtbl.add loc_hyp n (lazy (parse_hyp ("loc_hyp" ^ n) x))
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
              | Some g -> Lazy.force g
              | None -> print_endline "goal not found"


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

(* choice is None for getting all the POs, or Some([(a1,b1);...;(an,bn)]) for goals a1:b1 ... an:bn *)
let parse_pog choice =
  let pass1 =
    function
    | Element("Define", args, children) ->
       let x = List.assoc "name" args in
       Hashtbl.add define_table x (lazy (parse_def (if x = "B definitions" then "b_def" else x) children))
    | Element ("Proof_Obligation", args, children) ->
       add_po_table children
    | Element ("TypeInfos", args, children) -> parse_type_infos children
    | _ -> ()
  in
  function
  | Element ("Proof_Obligations", args, children) ->
     begin
       List.iter pass1 children;
       match choice with
       | None -> po_table#iter (parse_po None)
       | Some l ->
          let error a b = prerr_endline ("Goal " ^ string_of_int a ^ ":" ^ string_of_int b ^" does not exist.") in
          let parse (a,b) =
            match Option.bind (po_table#get a) (fun x -> parse_po (Some b) x |> Option.some) with
            | None -> error a b
            | Some () -> ()
          in
          List.iter parse l
     end
  | x -> parse_fail x


let printme () = Format.printf "@[my new theory is as follows:@\n@\n%a@]@."
           Pretty.print_theory (Theory.close_theory !my_theory)

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