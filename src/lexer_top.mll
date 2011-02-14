(* File lexerTypes.mll *)
{
open Parser        (* The type token is defined in parser.mli *)
exception Eof
open Lexing 

}
let filepath =  [^' ']+

rule token = parse 

[' ' '\t' '\r']         { token lexbuf }
| "="           {EQ}
| "#load"     {LOAD}
| "#help"         {HELP}
| "#verbose"    {VERBOSE}
| "on"          {ON}
| "off"          {OFF}
| "#exit"      {EXIT}
| filepath as str {FILE(str)}

