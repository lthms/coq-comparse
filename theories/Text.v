From Prelude Require Import All Text.
From Comparse Require Import Monad Combinators.

#[program]
Instance text_Input : Input text wchar :=
  { length := Text.text_length_nat
  ; unpack := fun (x : text) =>
                match x with
                | TNil => None
                | TCons x rst => Some (x, rst)
                end
  ; input_to_text := id
  ; token_to_text := fun c => TCons c TNil
  }.

Next Obligation.
  now destruct input.
Defined.

Next Obligation.
  destruct input.
  + split.
    ++ intros _.
       exists c.
       exists input.
       reflexivity.
    ++ intros _.
       cbn.
       auto with arith.
  + split.
    ++ now intros exfalso.
    ++ intros [x [output equ]].
       discriminate.
Defined.

Next Obligation.
  destruct input.
  + now inversion H; subst.
  + discriminate.
Defined.

From Coq Require Import FunInd.

Instance tag_parser : StrictParser (tag (t := wchar) (TCons x rst)).
(* begin hide *)
Proof.
  intros x rst.
  constructor.
  intros input r output equ.
  unfold tag in equ.
  destruct input.
  + rewrite tag_aux_equation in equ.
    cbn in equ.
    destruct wchar_eqb.
    ++ eapply PeanoNat.Nat.le_lt_trans.
       +++ eapply is_parser in equ.
           exact equ.
       +++ cbn.
           auto with arith.
    ++ discriminate.
  + discriminate.
Qed.
(* end hide *)
