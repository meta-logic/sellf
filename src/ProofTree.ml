open Term 
open Prints
open Sequent

let counter = ref 0 ;;

module ProofTree = 
  struct

    (* Declare mutable so I can modify directly on the object *)
    type prooftree = {
      mutable conclusion : Sequent.sequent;
      mutable premisses : prooftree list;
      mutable closed : bool;
    }
    
    let create sq = {
      conclusion = sq;
      premisses = [];
      closed = true (* for printing purposes... fixme later *)
    }

    let setConclusion pt c = pt.conclusion <- c

    let getConclusion pt = pt.conclusion

    let setPremisses pt p = pt.premisses <- p
    let getPremisses pt = pt.premisses

    let addPremisse pt p = let newc = create p in
      pt.premisses <- newc :: pt.premisses

    let getLatestPremisse pt = try List.hd pt.premisses 
      with Failure "hd" -> failwith "[ERROR] This sequent has no premisses."

    let rec copy pt = let cp = create pt.conclusion in
      let rec cpPremisses lst = match lst with
        | [] -> []
        | p::t -> (copy p) :: cpPremisses t
      in
      setPremisses cp (cpPremisses pt.premisses); cp

    (* Updates the tree with a new premisse and returns a reference to this new
    child *)
    let update pt sq = let newc = create sq in
      pt.premisses <- newc :: pt.premisses; newc

    let close pt = pt.closed <- true
    
    let openproof pt = pt.closed <- false
    
    let rec getLeaves pt = List.fold_right (fun el acc -> 
      match el.premisses with
        | [] -> el :: acc
        | _ -> getLeaves el @ acc
      ) pt.premisses []

(*
    let rec getOpenLeaves pt = List.fold_right (fun el acc -> 
      match el.premisses with
        | [] -> if is_open el.conclusion then el :: acc else acc
        | _ -> getOpenLeaves el @ acc
      ) pt.premisses []
*)

(*
    let rec getOpenLeaves pt = List.fold_right (fun el acc ->
      if not el.closed then el :: acc
      else getOpenLeaves el @ acc
      ) pt.premisses []
*)

(* FIXME this was a very bad hack done for the permutation algorithm... try to fix it.
    let rec mask m pt = 
      let concm = m.conclusion in
      let concpt = pt.conclusion in
      if isEqual concm concpt then begin
        let rec filteredPrem lst = match lst with
          | [] -> []
          | hd::tl -> try
            let pm = List.find (fun p -> isEqual p.conclusion hd.conclusion) m.premisses in
              mask pm hd;
              hd :: filteredPrem tl
            with Not_found -> filteredPrem tl
        in
        setPremisses pt (filteredPrem pt.premisses)
      end
      else failwith "[ERROR] Masking trees with different root."
*)

    (* G: Not printing the context. *)
    (* TODO create a printing function on sequent module and fix all FIXME
    let printSequent sq num = match sq with
      | SEQM(k, [], _) ->
      (*| SEQ(k, [], _) ->*)
        print_string "Sequent "; 
        print_int num; print_newline ();
        Hashtbl.iter (fun key data -> print_string (key^(string_of_int data)^", ") ) k; 
        print_newline ();
        print_string "--> Open sequent";
        print_newline ();
        flush stdout;
      | SEQM(_, t :: tl, _) -> 
      (*| SEQ(_, t :: tl, _) ->*) 
        print_string "Sequent "; 
        print_int num; print_newline ();
        (*print_hashtbl k; print_newline ();*)
        print_string "--> Closed sequent with initial rule on: "; print_term t;
        print_newline ();
        flush stdout;
      | _ -> print_string "Unexpected sequent."; flush stdout

    let rec  printLeavesAux lvsLst n = match lvsLst with
      | [] -> print_string "End of macro rule.\n\n"
      | hd :: tl -> printSequent (getConclusion hd) n; printLeavesAux tl (n+1)

    let printLeaves pt = printLeavesAux (getLeaves pt) 0
  
    (* Printing XML file (not implemented for macro rules) *)
    let rec printTreeChildren children out = match children with
      | [] -> ()
      | h::t -> printTree h out; printTreeChildren t out

    and printTree pt out = match pt.conclusion with
      | SEQ(_, terms, ASYN) -> 
        Printf.fprintf out "<seq phase='neg' terms='"; 
        printf_list_terms out terms; Printf.fprintf out "' closed='";
        if pt.closed then Printf.fprintf out "true'>\n"
        else Printf.fprintf out "false'>\n";
        printTreeChildren pt.premisses out;
        Printf.fprintf out "</seq>\n"

      | SEQ(_, terms, SYNC) ->
        Printf.fprintf out  "<seq phase='pos' terms='"; 
        printf_list_terms out terms; Printf.fprintf out  "' closed='";
        if pt.closed then Printf.fprintf out "true'>\n"
        else Printf.fprintf out "false'>\n";
        printTreeChildren pt.premisses out;
        Printf.fprintf out "</seq>\n"
     
      | SEQM(_, _, _) -> failwith "Printing XML is not implemented for macro
        rules."

      | EMPSEQ -> ()
    ;;

    let rec printLatexChildren children out = match children with
      | [] -> ()
      | h::t -> printLatex h out; printLatexChildren t out

    and printLatex pt out = match pt.conclusion with
      (* Regular proof sequent - does not print context *)
      | SEQ(_, terms, ASYN) -> 
        Printf.fprintf out "\\;\\;\\infer{ \\mathcal{K} ; \\Gamma \\Uparrow "; 
        print_list_terms_tex out terms; Printf.fprintf out "}\n{";
        printLatexChildren pt.premisses out;
        Printf.fprintf out "}\n"

      | SEQ(_, terms, SYNC) ->
        Printf.fprintf out "\\;\\;\\infer{ \\mathcal{K} ; \\Gamma \\Downarrow "; 
        print_list_terms_tex out terms; Printf.fprintf out "}\n{";
        printLatexChildren pt.premisses out;
        Printf.fprintf out "}\n"

      (* Macro rule - printing generic context *)
      | SEQM(k, terms, ASYN) -> 
        if pt.closed then Printf.fprintf out "\\;\\;\\infer{ ";
        Hashtbl.iter (fun s i -> Printf.fprintf out "\\Gamma_{%s}^{%d}\\; "
        (remSpecial s) i) k;
        Printf.fprintf out " \\Uparrow "; 
        print_list_terms_tex out terms; 
        if pt.closed then Printf.fprintf out "}\n{";
        printLatexChildren pt.premisses out;
        if pt.closed then Printf.fprintf out "}\n"

      | SEQM(k, terms, SYNC) ->
        if pt.closed then Printf.fprintf out "\\;\\;\\infer{ ";
        Hashtbl.iter (fun s i -> Printf.fprintf out "\\Gamma_{%s}^{%d}\\; "
        (remSpecial s) i) k;
        Printf.fprintf out " \\Downarrow "; 
        print_list_terms_tex out terms; 
        if pt.closed then Printf.fprintf out "}\n{";
        printLatexChildren pt.premisses out;
        if pt.closed then Printf.fprintf out "}\n"

      | EMPSEQ -> ()
    ;;

    let printTex2Proofs pt1 pt2 out = 
      Printf.fprintf out "\\documentclass[a4paper, 11pt]{article}\n"; 
      Printf.fprintf out "\\usepackage[utf8]{inputenc}\n"; 
      Printf.fprintf out "\\usepackage{amsmath}\n"; 
      Printf.fprintf out "\\usepackage{amssymb}\n"; 
      Printf.fprintf out "\\usepackage{stmaryrd}\n"; 
      Printf.fprintf out "\\usepackage{proof}\n\n"; 
      Printf.fprintf out "\\usepackage[landscape]{geometry}\n\n"; 
      Printf.fprintf out "\\begin{document}\n{\\tiny\n$$\n";
      printLatex pt1 out;
      Printf.fprintf out "$$\n}\n";
      Printf.fprintf out "\\vspace{1cm}\n";
      Printf.fprintf out "{\\tiny\n$$\n";
      printLatex pt2 out;
      Printf.fprintf out "$$\n}\n\\end{document}"
 
    let printTexProof pt out = 
      Printf.fprintf out "\\documentclass[a4paper, 11pt]{article}\n"; 
      Printf.fprintf out "\\usepackage[utf8]{inputenc}\n"; 
      Printf.fprintf out "\\usepackage{amsmath}\n"; 
      Printf.fprintf out "\\usepackage{amssymb}\n"; 
      Printf.fprintf out "\\usepackage{stmaryrd}\n"; 
      Printf.fprintf out "\\usepackage{proof}\n\n"; 
      Printf.fprintf out "\\usepackage[landscape]{geometry}\n\n"; 
      Printf.fprintf out "\\begin{document}\n{\\tiny\n$$\n";
      printLatex pt out;
      Printf.fprintf out "$$\n}\n\\end{document}"
    
    let printTexMacros lst out = 
      Printf.fprintf out "\\documentclass[a4paper, 11pt]{article}\n"; 
      Printf.fprintf out "\\usepackage[utf8]{inputenc}\n"; 
      Printf.fprintf out "\\usepackage{amsmath}\n"; 
      Printf.fprintf out "\\usepackage{amssymb}\n"; 
      Printf.fprintf out "\\usepackage{stmaryrd}\n"; 
      Printf.fprintf out "\\usepackage{proof}\n\n"; 
      Printf.fprintf out "\\usepackage[landscape]{geometry}\n\n";
      Printf.fprintf out "\\begin{document}\n\n";
      let rec printEach lst out = match lst with
        | [] -> ()
        | (p, c)::t -> 
          Printf.fprintf out "{\\tiny\n$$\n";
          printLatex p out; 
          Printf.fprintf out "$$\n}\n";
          (*Printf.fprintf out "\\begin{itemize}\n";
          Constraints.printTexConstraints c out;
          Printf.fprintf out "\\end{itemize}\n";*)
          printEach t out
      in printEach lst out;
      Printf.fprintf out "\n\\end{document}"


(* Printing the tree for JIT (not implemented for macro rules) *)
    let rec printJitChildren children out = match children with
      | [] -> ()
      | h::t -> printJitTree h out; printJitChildren t out

    and printJitTree pt out = match pt.conclusion with
      | SEQ(_, terms, ASYN) -> 
        Printf.fprintf out "{ id: \"%d\", name: \"" !counter;
        counter := !counter + 1; 
        printf_list_terms out terms; Printf.fprintf out "\", \ndata: {},\nchildren: [";
        printJitChildren pt.premisses out;
        Printf.fprintf out "]}\n"
  
      | SEQ(_, terms, SYNC) ->
        Printf.fprintf out "{ id: \"%d\", name: \"" !counter; 
        counter := !counter + 1;
        printf_list_terms out terms; Printf.fprintf out "\", \ndata: {},\nchildren: [";
        printJitChildren pt.premisses out;
        Printf.fprintf out "]}\n"
(*  
      | SEQ(_, terms, LHS, ASYN) ->
        Printf.fprintf out "{ id: \"%d\", name: \"" !counter;
        counter := !counter + 1; 
        printf_list_terms out terms; Printf.fprintf out "\", \ndata: {},\nchildren: [";
        printJitChildren pt.premisses out;
        Printf.fprintf out "]}\n"
   
      | SEQ(_, terms, LHS, SYNC) ->
        Printf.fprintf out "{ id: \"%d\", name: \"" !counter;
        counter := !counter + 1; 
        printf_list_terms out terms; Printf.fprintf out "\", \ndata: {},\nchildren: [";
        printJitChildren pt.premisses out;
        Printf.fprintf out "]}\n"
*)
      | SEQM(_, _, _) -> failwith "Printing Jit tree is not implemented for
        macro rules."

      | EMPSEQ -> ()
    ;;  
*)
 end
;;



