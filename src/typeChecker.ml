
open Types
open Prints
open Term

(** Auxiliary method for introducing deBruijn indices to a parsed clause.
    Called by {!TypeChekcer.deBruijn}.
    It works in one of two modes: if @flag is true, all free variables are bound
    and replaced by deBruijn indices; if @flag is false, no deBruijn indices are
    introuced and free variables remain free. You should use flag=true if you
    want a term that normalizes, and flag=false if you want to typecheck the
    term.
    @param flag [boolean] ([true] for introducing deBruijn indices, [false] otherwise)
    @param fVarC function from a [string] (variable name) to a triple [(id, nAbs,
    tAbs)], where [id] is used for hashing, [nAbs] is the deBruijn index and
    [tAbs] is [1] for bound terms and [0] otherwise.
    @param nABS the number of abstractions in that branch so far
    @param form the input formula
*)
(* TODO: find out why id changes when VAR remains VAR *)
let rec deBruijn_aux flag fVarC nABS form = match form with
  | VAR v -> begin 
    match (fVarC v.str) with
      | (id, _, 0) -> (* Free variable: keep it as is *)
        let (idNew, _, _ ) = fVarC v.str in
        let v2 = {str = v.str; id = idNew; tag = v.tag; ts = v.ts; lts = v.lts} in VAR v2
      | (id, nABS1, 1) -> (* Bound variable: add deBruijn index if flag=true *) 
        if flag then DB(id + nABS1) 
        else let (idNew, _, _ ) = fVarC v.str in
        let v2 = {str = v.str; id = idNew; tag = v.tag; ts = v.ts; lts = v.lts} in VAR v2
      | _ -> failwith "Impossible case reached in the De Bruijn Auxiliary."
    end
  | APP (term1, term2) -> 
     APP (deBruijn_aux flag fVarC nABS term1, List.map (deBruijn_aux flag fVarC nABS) term2)
  | ABS (str, i, body1) -> 
     let fVarCNew x = 
     begin match x with
       | x when x = str ->  (1, 0, 1)
       | x -> let (id, nABS_rest, tABS) = fVarC x in (id, nABS_rest + 1, tABS)
     end
     in ABS (str, 1, deBruijn_aux flag fVarCNew (nABS + 1) body1)
  | PLUS (f1, f2) -> PLUS (deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2)
  | MINUS (f1, f2) -> MINUS (deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2)
  | TIMES (f1, f2) -> TIMES (deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2) 
  | DIV (f1, f2) -> DIV (deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2)
  | TENSOR (f1, f2) -> TENSOR (deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2)
  | ADDOR (f1, f2) -> ADDOR (deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2)
  | LOLLI (sub, f1, f2) -> LOLLI (deBruijn_aux flag fVarC nABS sub, deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2)
  | BANG (sub, f1) -> BANG (deBruijn_aux flag fVarC nABS sub, deBruijn_aux flag fVarC nABS f1) 
  | QST (sub, f1) -> QST (deBruijn_aux flag fVarC nABS sub, deBruijn_aux flag fVarC nABS f1) 
  | WITH (f1, f2) -> WITH (deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2)
  | PARR (f1, f2) -> PARR (deBruijn_aux flag fVarC nABS f1, deBruijn_aux flag fVarC nABS f2)
  | BRACKET (f1) -> BRACKET (deBruijn_aux flag fVarC nABS f1)
  | FORALL (str, _, f1) -> 
     let fVarCNew x = 
     begin match x with
       | x when x = str -> (1, 0, 1)
       | x -> let (id, nABS_rest, tABS) = fVarC x in (id, nABS_rest + 1, tABS)
     end
     in FORALL (str, 1, deBruijn_aux flag fVarCNew (nABS + 1) f1)
  | EXISTS (str, _, f1) -> 
     let fVarCNew x = 
     begin match x with
       | x when x = str -> (1, 0, 1)
       | x -> let (id, nABS_rest, tABS) = fVarC x in (id, nABS_rest + 1, tABS)
     end
     in EXISTS (str, 1, deBruijn_aux flag fVarCNew (nABS + 1) f1)
  | NEW (str, f1) -> 
     let fVarCNew x = 
     begin match x with
       | x when x = str -> (1, 0, 1)
       | x -> let (id, nABS_rest, tABS) = fVarC x in (id, nABS_rest + 1, tABS)
     end
     in NEW (str, deBruijn_aux flag fVarCNew (nABS + 1) f1)
  | PRED (srt, terms, p) ->  PRED (srt, deBruijn_aux flag fVarC nABS terms, p)
  | NOT (f) -> NOT(deBruijn_aux flag fVarC nABS f)
  | EQU (str, _, terms) -> 
     let (id, nABS, tABS) =  fVarC str in 
     EQU (str, id, deBruijn_aux flag fVarC nABS terms)
  | CLS(tp, t1, t2) -> CLS(tp, deBruijn_aux flag fVarC nABS t1, deBruijn_aux flag fVarC nABS t2)
  | COMP(comp, t1, t2) -> COMP(comp, deBruijn_aux flag fVarC nABS t1, deBruijn_aux flag fVarC nABS t2)
  | ASGN(t1, t2) -> ASGN(deBruijn_aux flag fVarC nABS t1, deBruijn_aux flag fVarC nABS t2)
  | PRINT(t1) -> PRINT(deBruijn_aux flag fVarC nABS t1)
  | TOP | ONE | BOT | ZERO | STRING(_) | CONST(_) -> form
  | DB(_) -> failwith "[ERROR] deBruijn index found while inserting deBruijn indices (typeChecker.ml)."
  | _ -> failwith ("[ERROR] Unexpected term while inserting deBruijn indices (typeChecker.ml): " ^ (termToString form))

let rec collect_free_variables clause =
  let rec collect_free_variables_list freeVar bVar lst = 
    begin
      match lst with
      | [] -> []
      | [t] -> collect_free_variables_aux freeVar bVar t
      | t :: body ->  
          let freeVar1 = collect_free_variables_aux freeVar bVar t in 
          collect_free_variables_list freeVar1 bVar body
    end
  and
  collect_free_variables_aux freeVar bVar clause = 
    begin
      match observe clause with
        | VAR v  when List.mem v.str freeVar || List.mem v.str bVar-> freeVar
        | VAR v  -> v.str :: freeVar
        | PRED(_, t1, _) -> collect_free_variables_aux freeVar bVar t1
        | TOP | ONE | BOT | ZERO | CUT | DB _ | INT _ | CONST _ | STRING _ | SUSP _ -> freeVar
        | EQU(_, _, t1) | PRINT(t1)  -> collect_free_variables_aux freeVar bVar t1
        | FORALL(str, _, t1) | EXISTS(str, _, t1) 
        | ABS(str, _, t1) | NEW (str, t1) -> collect_free_variables_aux freeVar (str :: bVar) t1
        | APP(t1, t2) -> let freeVar1 = collect_free_variables_aux freeVar bVar t1 in
                                collect_free_variables_list freeVar1 bVar t2 
        | DIV (t1, t2)  | TIMES (t1, t2) | MINUS (t1, t2) | PLUS (t1, t2) 
        | TENSOR(t1, t2) | ADDOR(t1, t2) | PARR(t1, t2) | COMP(_, t1, t2) | ASGN(t1, t2)
        | WITH(t1,t2) | CLS(_, t1, t2) | BANG(t1, t2) | QST(t1, t2) -> 
          let freeVar1 = collect_free_variables_aux freeVar bVar t1 in 
          let freeVar2 = collect_free_variables_aux freeVar1 bVar t2 in 
          freeVar2
        | LOLLI (subex, t1, t2)  -> 
          let freeVar1 = collect_free_variables_aux freeVar bVar subex in 
          let freeVar2 = collect_free_variables_aux freeVar1 bVar t1 in
          let freeVar3 = collect_free_variables_aux freeVar2 bVar t2 in
            freeVar3
        | BRACKET (form) -> collect_free_variables_aux freeVar bVar form
        | NOT (form) -> collect_free_variables_aux freeVar bVar form
        | _ -> failwith "Not expected term in 'collect_free_variables_aux', typeChecker.ml"
    end
  in 
  collect_free_variables_aux [] [] clause

(** This method introduces deBruijn indices to a parsed clause.
    It works in one of two modes: if @flag is [true], all free variables are bound
    and replaced by deBruijn indices; if @flag is [false], no deBruijn indices are
    introuced and free variables remain free. You should use [flag=true] if you
    want a term that normalizes, and [flag=false] if you want to typecheck the
    term.
    @param flag [boolean]
    @param form the input formula
*)
(* TODO: find out why the false flag exists... *)
let deBruijn flag form =
  let rec add_abstractions freeVar form = 
   begin 
    match freeVar with
    | [] ->  form
    | h::t -> ABS(h, 1, add_abstractions t form)
  end in
  let freeVar = collect_free_variables form in
  let form_abs = add_abstractions freeVar form in
  match flag with
    | true -> deBruijn_aux flag (fun (x: string) -> (0,0,0)) 0 form_abs
    | false -> deBruijn_aux flag (fun (x: string) -> (0,0,0)) 0 form

(*VN: Still have to check for occurchecks.*)

(* Function for unifying types. It returns a substitution with the unification. In the 
case that the types are not unifyable, then the function fails with an error. 
Here we assume that type variables are defined as a kind.*)
let rec unifyTypes gTyp vTyp sub = match (gTyp, vTyp) with 
  | (ARR (x1, y1), ARR (x2, y2)) -> 
    let sub2 = unifyTypes x1 x2 sub in (unifyTypes y1 y2 sub2)
  | (TBASIC (TINT), TBASIC (TINT)) -> sub
  | (TBASIC (TSUBEX), TBASIC (TSUBEX)) -> sub
  | (TBASIC (TSTRING), TBASIC (TSTRING)) -> sub
  | (TBASIC (TPRED), TBASIC (TPRED)) -> sub
  | (x, TBASIC (TKIND (y))) -> begin
    match sub (TBASIC (TKIND (y))) with
      | None ->  let sub2 z = (match z with
        | TBASIC (TKIND (d)) when d = y ->  Some (x)
        | d -> sub d)
        in sub2
      | Some (x1) when x1 = x -> sub
      | Some (_) -> failwith "Failed when unifying type variables."
    end
  | _ -> print_endline (" Type1:"^(typeToString gTyp)^"  Type2:"^(typeToString vTyp)); failwith "Failed when unifying type variables:"

(* Function that applies a substitution eagerly to a type. *)
let rec applySub sub typ = match typ with 
  | ARR (t0, t1) -> ARR (applySub sub t0, applySub sub t1)
  | x -> (match sub x with
    | None -> typ
    | Some (t) -> (match sub t with
      | None -> t
      | Some(t2) -> t2 ) )
 
(*Function that typechecks a term. It takes a term, possibly with variables, a type, a subsitution for the 
type variables, an environment that given a term variable returns its type, and a number varC with the 
number of the type variables used. *)
let rec tCheckAux term typ sub env varC = 
(*Initialize the substitution for type variables as empty*)
let subInit x = (match x with 
                  | _ -> None) 
in 
(*All variables appearing in a comparison must have type int.*)
let rec tCheckInt intBody env = 
match intBody with
  | INT (x) -> (subInit, env)
  | VAR v -> (match env (v.str,v.id) with 
    | None -> let env2 z = (match z with
      | (x1,i1) when (x1,i1) = (v.str,v.id) -> Some (TBASIC(TINT))
      | (x1,i1) -> env (x1,i1)) 
      in (subInit, env2)
    | Some (TBASIC(TINT)) -> (subInit, env)
    | Some (_) -> failwith ("Error: Variable  "^v.str^" does not have type INT in a comparison."))
  | PLUS (int1, int2) -> 
    let (_,env1) = tCheckInt int1 env in
    let (_,env2) = tCheckInt int2 env1 in (subInit, env2)
  | MINUS (int1, int2) -> 
    let (_,env1) = tCheckInt int1 env in
    let (_,env2) = tCheckInt int2 env1 in (subInit, env2)
  | TIMES (int1, int2) -> 
    let (_,env1) = tCheckInt int1 env in
    let (_,env2) = tCheckInt int2 env1 in (subInit, env2)
  | DIV (int1, int2) -> 
    let (_,env1) = tCheckInt int1 env in
    let (_,env2) = tCheckInt int2 env1 in (subInit, env2) 
  | _ -> failwith "Error: Invalid term in a comparison."
in
match term with 
  (*Typecheck terms and at the same time updating the environment and substitution functions.*)
  | INT (x) -> ((TBASIC (TINT)), unifyTypes (TBASIC (TINT)) typ sub, env, varC)
  | STRING (x) -> ((TBASIC (TSTRING)), unifyTypes (TBASIC (TSTRING)) typ sub, env, varC)
  | CONST (x) -> begin
    match typ with 
      | TBASIC(TSUBEX) -> begin try 
        let _ = Hashtbl.find (Subexponentials.typeTbl) x in (typ, sub, env, varC)
      with
        | Not_found -> failwith ("ERROR: Subexponential name expected, but found -> "^x)
      end
      | _ -> begin try 
        let typC = Hashtbl.find Specification.typeTbl x in (typC, unifyTypes typC typ sub, env, varC)
      with
        | Not_found -> failwith ("ERROR: Constant not declared -> "^x)
      end
  end
  | VAR v -> let (x, y) = (v.str, v.id) in begin
    match env (x,y) with
      | None -> 
        let env2 z = (match z with
          | (x1,y1) when (x1,y1) = (x,y) -> Some (typ)
          | (x1,y1) -> env (x1,y1))
        in (typ, sub, env2, varC)
      | Some (typ2) -> 
        let sub2 = unifyTypes typ2 typ sub in
        let newTyp = applySub sub2 typ in  
        let env2 z = (match z with
          | (x1,y1) when (x1,y1) = (x,y) -> Some (newTyp)
          | (x1,y1) -> env (x1,y1))
        in (newTyp, sub2, env2, varC)
  end
  | ABS (x, y, term2) -> begin
    match typ with
      | ARR(t1, t2) -> (match env (x,y) with
        | None -> 
          let env2 z = (match z with
            | (x1,y1) when (x1,y1) = (x,y) -> Some (t1)
            | (x1,y1) -> env (x1,y1))
          in tCheckAux term2 t2 sub env2 varC
        | Some (typ2) -> 
          let sub2 = unifyTypes typ2 typ sub in
          let newTyp = applySub sub2 typ in  
          let env2 z = (match z with
            | (x1,y1) when (x1,y1) = (x,y) -> Some (newTyp)
            | (x1,y1) -> env (x1,y1))
          in tCheckAux term2 t2 sub2 env2 varC)
      | _ -> print_string (typeToString typ); failwith " Expected an arrow type."
  end
  | APP (head, body) -> (*VN: Construct an arrow type for all body elements with type variables.*)
    let rec construct_type_arr args endType varC = begin
      match args with
        | [] -> (endType, varC)
        | t :: body -> 
          let (rTyp, varCup) = construct_type_arr body endType (varC+1) in
          let lTyp = TBASIC (TKIND (varName "typeVar" varC)) in (ARR(lTyp, rTyp), varCup)
    end
    in (*VN: Typecheck and unify types of the elements of the body.*)
    let rec construct_type_args args typ sub1 env1 varC = begin
      match args, typ with
        | [t], ARR(t1, tHead) -> let (t2, sub2, env2, varC2) = tCheckAux t t1 sub env (varC + 1) in
          (ARR(t2, tHead), sub2, env2, varC2)
        | tr::body, ARR(t1, t2) -> 
          let (t3, sub2, env2, varC2) = tCheckAux tr t1 sub env (varC + 1) in
          let (t4, sub3, env3, varC3) = construct_type_args body t2 sub2 env2 varC2  in (ARR(t3,t4), sub3, env3, varC3)
        | _, _ -> failwith "Not expected arguments in 'cosntruct_type_args', typeChecker.ml"
    end
    in (*VN: First construct the arrow type with type variables.*)
    let (builtType, varC1) = construct_type_arr body typ varC 
    in (*VN: Type check the head of the application using the arrow type created.*)
    let (t_head, sub_head, env_head, varC_head) = tCheckAux head builtType sub env varC1
    in (*VN: Typecheck the body elements of the application.*)
    let (t_final, sub_final, env_final, varC_final) =  construct_type_args body t_head sub_head env_head varC_head 
    in (*VN: Return the type instantiated with the substitution computed.*)
    ((applySub sub_final t_final), sub_final, env_final, varC_final)
  (*Arithmetic comparisons do not require type variables since everything is integer, hence the value 0*)
  | PLUS (int1, int2) -> 
    let (_,env1) = tCheckInt int1 env in
    let (_,env2) = tCheckInt int2 env1 in (TBASIC(TINT), subInit, env2, 0)
  | MINUS (int1, int2) -> 
    let (_,env1) = tCheckInt int1 env in
    let (_,env2) = tCheckInt int2 env1 in (TBASIC(TINT), subInit, env2, 0)
  | TIMES (int1, int2) -> 
    let (_,env1) = tCheckInt int1 env in
    let (_,env2) = tCheckInt int2 env1 in (TBASIC(TINT), subInit, env2, 0)
  | DIV (int1, int2) -> 
    let (_,env1) = tCheckInt int1 env in
    let (_,env2) = tCheckInt int2 env1 in (TBASIC(TINT), subInit, env2, 0)
  | _ -> failwith "Error: Encountered a Susp term when typechecking a term."


 (* Functions that grounds the image of an environment, so that the type variables created in the 
unification process are eliminated. Usually this function is called when moving from typechecking one predicate 
to the next one. In the process, we want that the image of the environment does not mention any type 
variables created, so that one can reset the type variable counter.*)
let rec grEnvImgTerms sub env terms = match terms with
  | VAR v -> let (x,i) = (v.str, v.id) in
    let env2 z = (match z with
      | (x1,i1) when (x1,i1) = (x,i) -> begin
        match env (x1,i1) with
          | Some (t) -> Some (applySub sub t)
          | _ -> None
      end
      | (x1,i1) -> env (x1,i1)) in env2
  | APP (x, y) -> 
    let rec grListTerms sub env lst = begin
      match lst with
        | [t] -> grEnvImgTerms sub env t
        | t :: body -> let envT = grEnvImgTerms sub env t in grListTerms sub envT body
        | [] -> failwith "[ERROR] Encountered an application with no body terms when grounding environment."
    end in
    let env2 = grEnvImgTerms sub env x in grListTerms sub env2 y
  | _ -> env

let rec grEnvImgProp sub env prop = match prop with
  | PRED (_, terms, _) -> grEnvImgTerms sub env terms
  | _ -> env


(*Main function used to typecheck a clause.
  We do not typecheck terms inside prints.
  G: We typecheck also terms that are not clauses (needed for init and cut clauses of specifications)
*)
let rec typeCheck clause = 
  let subInit x = (match x with _ -> None) in 
  let envInit x = (match x with _ -> None) in
  let rec tCheckBody body env = 
    begin match body with
      | PRED(_, x, _) -> let (_, s, e, _) = tCheckAux x (TBASIC (TPRED)) subInit env 0
            in let e2 = grEnvImgTerms s e x
            in (s, e2) 
      | TOP -> (subInit, env)
      | BOT -> (subInit, env)
      | ONE -> (subInit, env)
      | ZERO -> (subInit, env)
      | CUT -> (subInit, env)
      | EQU (x, i, y) -> let newType = TBASIC (TKIND (varName "typeVar" 0)) in
          let (typeY, subY, envY, varC) = tCheckAux y newType subInit env 1
          in 
          begin
            match envY (x,i) with
            | None -> let env2 z = 
                begin match z with
                  | (x1,i1) when (x1,i1) = (x,i) -> Some (typeY)
                  | (x1,i1) -> envY (x1,i1)
                end
              in (subY, env2)
            | Some (typeY1) when typeY1 = typeY -> (subY,envY)
            | Some (_) -> failwith "Error: Type variable mismatched"
          end
      | COMP (_, int1, int2) -> let (_,_,env1,_) = tCheckAux int1 (TBASIC (TINT)) subInit env 0
              in let (_,_,env2,_) = (tCheckAux int2 (TBASIC (TINT)) subInit env1 0)
              in (subInit, env2)
      | ASGN (int1, int2) -> let (_,_,env1,_) = tCheckAux int1 (TBASIC (TINT)) subInit env 0
              in let (_,_,env2,_) = (tCheckAux int2 (TBASIC (TINT)) subInit env1 0)
              in (subInit, env2)
        (*We do not typecheck the terms in prints.*)
      | PRINT _ ->  (subInit, env)
      | LOLLI (subexp, body1, body2) -> (*print_term (LOLLI (subexp, body1, body2));*)
              let (_,_,env1,_) = tCheckAux subexp (TBASIC(TSUBEX)) subInit env 0 in
              let (_,env2) = tCheckBody body1 env1 in
              tCheckBody body2 env2
      | QST (subexp, body1) -> 
              let (_,_,env1,_) = tCheckAux subexp (TBASIC(TSUBEX)) subInit env 0 in
              tCheckBody body1 env1
      | BANG (subexp, body1) -> 
              let (_,_,env1,_) = tCheckAux subexp (TBASIC(TSUBEX)) subInit env 0 in
              tCheckBody body1 env1
      | TENSOR (body1, body2) -> let (sub2, env2) = tCheckBody body1 env in
              tCheckBody body2 env2
      | PARR (body1, body2) -> let (sub2, env2) = tCheckBody body1 env in
              tCheckBody body2 env2
      | ADDOR (body1, body2) -> let (sub2, env2) = tCheckBody body1 env in
              tCheckBody body2 env2
      | WITH (body1, body2) -> let (sub2, env2) = tCheckBody body1 env in
          tCheckBody body2 env2
      | FORALL (_, _, body1) -> tCheckBody body1 env
      | EXISTS (_, _, body1) -> tCheckBody body1 env
      | NEW (_, t) -> tCheckBody t env 
      (*VN: The following two cases are for when variables are of type o.*) 
      | VAR v ->  tCheckBody (PRED("", VAR v, NEG)) env
      | APP(head, args) -> tCheckBody (PRED("", APP(head, args), NEG)) env
      | BRACKET (f) -> tCheckBody f env
      | NOT body1 -> tCheckBody body1 env
      | _ -> print_string (termToString body); failwith " Expected a body element while typechecking."
    end
    in
    match clause with
      | CLS (_, head, body) -> let (sub, env2) = tCheckBody head envInit
                                 in let envH = grEnvImgProp sub env2 head 
                                 in  tCheckBody body envH
      | body -> tCheckBody body envInit
  (*| _ -> print_term clause; failwith " Expected a clause while typechecking."*)
  
