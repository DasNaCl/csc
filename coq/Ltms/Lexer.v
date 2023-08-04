Require Import BinNat Ascii String.
Require Import CSC.Ltms.Parser.
Import MenhirLibParser.Inter.
Open Scope char_scope.
Open Scope bool_scope.

(** No such thing as an empty buffer, instead we use
    an infinite stream of EOF *)
CoFixpoint TheEnd : buffer := Buf_cons (EOF tt) TheEnd.

Fixpoint ntail n s :=
  match n, s with
  | 0, _ => s
  | _, EmptyString => s
  | S n, String _ s => ntail n s
  end.

(** Comparison on characters *)
Definition ascii_eqb c c' := (N_of_ascii c =? N_of_ascii c')%N.
Definition ascii_leb c c' := (N_of_ascii c <=? N_of_ascii c')%N.

Definition is_digit c := (("0" <=? c) && (c <=? "9"))%char.

Definition is_alpha c :=
  ((("a" <=? c) && (c <=? "z")) ||
   (("A" <=? c) && (c <=? "Z")) ||
   (c =? "_"))%char.

Fixpoint identsize s :=
  match s with
  | EmptyString => 0
  | String c s =>
    if is_alpha c || is_digit c then S (identsize s)
    else 0
  end.

Fixpoint readnum acc s :=
  match s with
  | String "0" s => readnum (acc*10) s
  | String "1" s => readnum (acc*10+1) s
  | String "2" s => readnum (acc*10+2) s
  | String "3" s => readnum (acc*10+3) s
  | String "4" s => readnum (acc*10+4) s
  | String "5" s => readnum (acc*10+5) s
  | String "6" s => readnum (acc*10+6) s
  | String "7" s => readnum (acc*10+7) s
  | String "8" s => readnum (acc*10+8) s
  | String "9" s => readnum (acc*10+9) s
  | _ => (acc,s)
  end.

Fixpoint lex_string_cpt n s :=
  match n with
  | 0 => None
  | S n =>
    match s with
    | EmptyString => Some TheEnd
    | String c s' =>
      match c with
      | " " => lex_string_cpt n s'
      | "009" => lex_string_cpt n s' (* \t *)
      | "010" => lex_string_cpt n s' (* \n *)
      | "013" => lex_string_cpt n s' (* \r *)
      | "(" => option_map (Buf_cons (LPAREN tt)) (lex_string_cpt n s')
      | ")" => option_map (Buf_cons (RPAREN tt)) (lex_string_cpt n s')
      | "," => option_map (Buf_cons (COMMA tt)) (lex_string_cpt n s')
      | "+" => option_map (Buf_cons (ADD tt)) (lex_string_cpt n s')
      | "-" => option_map (Buf_cons (SUB tt)) (lex_string_cpt n s')
      | "*" => option_map (Buf_cons (MUL tt)) (lex_string_cpt n s')
      | "/" => option_map (Buf_cons (DIV tt)) (lex_string_cpt n s')
      | "=" => option_map (Buf_cons (EQUAL tt)) (lex_string_cpt n s')
      | "<" =>
        let maybearrow := substring 0 1 s in
        let s := ntail 1 s in
        match s with
        | EmptyString => option_map (Buf_cons (LANGLE tt)) (lex_string_cpt n s')
        | String c s' =>
          match c with
          | "-" => option_map (Buf_cons (SUB tt)) (lex_string_cpt n s')
          | _ => option_map (Buf_cons (LANGLE tt)) (lex_string_cpt n s)
          end
        end
      | "[" => option_map (Buf_cons (LBRACKET tt)) (lex_string_cpt n s')
      | "]" => option_map (Buf_cons (RBRACKET tt)) (lex_string_cpt n s')
      | ">" => option_map (Buf_cons (RANGLE tt)) (lex_string_cpt n s')
      | _ =>
        if is_digit c then
          let (m,s) := readnum 0 s in
          option_map (Buf_cons (NUM m)) (lex_string_cpt n s)
        else if is_alpha c then
          let k := identsize s in
          let id := substring 0 k s in
          let s := ntail k s in
          if String.eqb id "get" then
            option_map (Buf_cons (GET tt)) (lex_string_cpt n s)
          else if String.eqb id "set" then
            option_map (Buf_cons (SET tt)) (lex_string_cpt n s)
          else if String.eqb id "in" then
            option_map (Buf_cons (IN tt)) (lex_string_cpt n s)
          else if String.eqb id "let" then
            option_map (Buf_cons (LET tt)) (lex_string_cpt n s)
          else if String.eqb id "new" then
            option_map (Buf_cons (NEW tt)) (lex_string_cpt n s)
          else if String.eqb id "delete" then
            option_map (Buf_cons (DELETE tt)) (lex_string_cpt n s)
          else if String.eqb id "call" then
            option_map (Buf_cons (CALL tt)) (lex_string_cpt n s)
          else if String.eqb id "return" then
            option_map (Buf_cons (RETURN tt)) (lex_string_cpt n s)
          else if String.eqb id "ifz" then
            option_map (Buf_cons (IFZ tt)) (lex_string_cpt n s)
          else if String.eqb id "then" then
            option_map (Buf_cons (THEN tt)) (lex_string_cpt n s)
          else if String.eqb id "else" then
            option_map (Buf_cons (ELSE tt)) (lex_string_cpt n s)
          else if String.eqb id "abort" then
            option_map (Buf_cons (ABORT tt)) (lex_string_cpt n s)
          else
            option_map (Buf_cons (ID id)) (lex_string_cpt n s)
        else None
      end
    end
  end.

Definition lex_string s := lex_string_cpt ((length s)+1) s.

