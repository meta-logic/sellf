(* File lexer_types.mll *)
{
open Parser 
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

