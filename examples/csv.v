From Comparse Require Import Monad Combinators.
From Coq Require Import Ascii String.
From ExtLib Require Import Char.

Import AsciiSyntax.

Generalizable All Variables.

Instance string_Input : Input string ascii :=
  { unpack := fun x => match x with
                       | EmptyString => None
                       | String c rst => Some (c, rst)
                       end
  ; input_to_string := id
  ; token_to_string := Basics.flip String EmptyString
  }.

#[program]
Instance string_InputLaws : InputLaws string ascii String.length := {}.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

Next Obligation.
Admitted.

Definition entry : parser string (list ascii) :=
  many_until read_token
             (peek ((token ","%char;; pure tt)
                         <|> (token "010"%char;; pure tt)
                         <|> eoi)).

Definition rows `{Input string ascii}
  : parser string (list (list ascii)) :=
  sep entry (token ","%char).

Definition csv `{Input string ascii}
  : parser string (list (list (list ascii))) :=
  sep rows (token "010"%char).

Extraction "csv.ml" csv.
