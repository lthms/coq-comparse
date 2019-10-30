From Coq Require Import String Ascii.
From Prelude Require Import All.
From Comparse Require Import Monad Combinators.

#[program]
Instance string_Input : Input string ascii :=
  { length := String.length
  ; unpack := fun (x : string) =>
                match x with
                | EmptyString => None
                | String x rst => Some (x, rst)
                end
  }.

Next Obligation.
  now destruct input.
Defined.

Next Obligation.
  destruct input.
  + split.
    ++ now intros falso.
    ++ now intros [x [output equ]].
  + split.
    ++ intros _.
       exists a.
       exists input.
       reflexivity.
    ++ intros _.
       apply PeanoNat.Nat.lt_0_succ.
Defined.

Next Obligation.
  destruct input.
  + discriminate.
  + now inversion H; subst.
Qed.

Class FromString (α : Type) :=
  { from_string (x : string) : α
  }.

Instance string_FromString : FromString string :=
  { from_string (x : string) := x
  }.
