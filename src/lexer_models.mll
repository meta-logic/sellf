(* 
 * Definition of tokes for the parsing of DLV models
 *
 * Giselle Machado Reis
 * 2013
 * 
 * *)

{
  open Parser_models
}

rule token = parse
  | "in"         { IN } 
  | "mctx"       { MCTX }
  | "elin"       { ELIN }
  | "emp"        { EMP }
  | "union"      { UNION }
  | "addform"    { ADDFORM }
  | "requiredIn" { REQIN }
  | "removed"    { REMOVED }
  | "_"          { UNDERSCORE }
 
