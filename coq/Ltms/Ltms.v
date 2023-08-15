
Require Export CSC.Ltms.syntax CSC.Ltms.static CSC.Ltms.dynamic.

Require Import CSC.Ltms.Parser CSC.Ltms.Lexer CSC.Util.Convenience.
Import MenhirLibParser.Inter.

Definition string2expr s :=
  match option_map (Parser.top_expr 50) (Lexer.lex_string s) with
  | Some (Parsed_pr f _) => Some f
  | _ => None
  end.

Definition expr2string e := string_of_expr e.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From Coq Require Extraction.

Extraction Language OCaml.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive option => "option" [ "Some" "None" ].

Extraction "Ltms/Parser.ml" CSC.Ltms.Parser.top_expr CSC.Ltms.Lexer.lex_string string2expr expr2string.
