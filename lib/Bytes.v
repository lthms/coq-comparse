From Prelude Require Import All Byte Bytes Text.
From Comparse Require Import Monad Combinators.

#[program]
Instance bytes_Input : Input bytes byte :=
  { length := length_nat
  ; unpack := fun (x : bytes) =>
                match unwrap_bytes x with
                | [] => None
                | x :: rst => Some (x, wrap_bytes rst)
                end
  ; input_to_text := fun x => match text_of_bytes x with
                              | Some x => x
                              | _ => t#"(invalid utf8 sequence)"
                              end
  ; token_to_text := fun c => match text_of_bytes (wrap_bytes [c]) with
                              | Some x => x
                              | _ => t#"(invalid utf8 character)"
                              end
  }.

Next Obligation.
  now destruct input as [[ | x rst]].
Defined.

Next Obligation.
  destruct input as [[ | x rst]].
  + split.
    ++ now intros exfalso.
    ++ intros [x [output equ]].
       discriminate.
  + split.
    ++ intros _.
       exists x.
       exists (wrap_bytes rst).
       reflexivity.
    ++ intros _.
       cbn.
       auto with arith.
Defined.

Next Obligation.
  destruct input as [[ | y rst']].
  + cbn in H.
    discriminate.
  + now inversion H; subst.
Defined.

From Coq Require Import FunInd.

Instance tag_parser : StrictParser (tag (t := byte) (wrap_bytes (x :: rst))).
(* begin hide *)
Proof.
  intros x rst.
  constructor.
  intros input r output equ.
  unfold tag in equ.
  destruct input as [[ | y rst']].
  + discriminate.
  + rewrite tag_aux_equation in equ.
    cbn in equ.
    destruct byte_equb.
    ++ eapply PeanoNat.Nat.le_lt_trans.
       +++ eapply is_parser in equ.
           exact equ.
       +++ cbn.
           auto with arith.
    ++ discriminate.
Qed.
(* end hide *)
