(* File lexerTypes.mll *)
{
(*open Parser*)        (* The type token is defined in parser.mli *)
open Parser_systems 
exception Eof
open Lexing 

}
let filepath =  [^' ']+

rule token = parse 

[' ' '\t' '\r']         { token lexbuf }
| "#load"     {LOAD}
| "#help"         {HELP}
| "#verbose"    {VERBOSE}
| "#time"	{TIME}
| "on"          {ON}
| "off"          {OFF}
| "#exit"      {EXIT}
| filepath as str {FILE(str)}

