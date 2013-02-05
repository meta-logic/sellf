(**************************************)
(*                                    *)
(*        Linear Logic Rules          *)
(*                                    *)
(*  Giselle Machado Reis              *)
(*  2013                              *)
(*                                    *)
(**************************************)

type llrule = 
  | TENSORRULE 
  | ADDOR1RULE
  | ADDOR2RULE
  | PARRRULE
  | WITHRULE
  | BANGRULE
  | HBANGRULE
  | QSTRULE
  | FORALLRULE
  | EXISTSRULE
  | TOPRULE
  | BOTRULE
  | ONERULE
  | INIT
  | DECIDE
  | RELEASEUP
  | RELEASEDOWN
;;
