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
  induction input; now split.
Qed.

Next Obligation.
  destruct input.
  + cbn; split.
    ++ intros falso.
       inversion falso.
    ++ intros [x [output equ]].
       discriminate.
  + split.
    ++ intros _.
       now exists a, input.
    ++ intros _.
       apply PeanoNat.Nat.lt_0_succ.
Qed.

Next Obligation.
  destruct input.
  + discriminate.
  + inversion H; subst.
    reflexivity.
Qed.

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
