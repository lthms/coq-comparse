From Coq Require Export Byte.
From Prelude Require Import All Bytes.
From Comparse Require Import Monad Combinators.

#[program]
Instance bytes_Input : Input bytes byte :=
  { length := fun x => List.length (unwrap_bytes x)
  ; unpack := fun (x : bytes) =>
                match x with
                | wrap_bytes [] => None
                | wrap_bytes (x :: rst) => Some (x, wrap_bytes rst)
                end
  }.

Next Obligation.
  now destruct input as [ [ | x rst ] ].
Defined.

Next Obligation.
  destruct input as [ [ | x rst ] ].
  + split.
    ++ now intros falso.
    ++ now intros [x [output equ]].
  + split.
    ++ intros _.
       exists x.
       exists (wrap_bytes rst).
       reflexivity.
    ++ intros _.
       apply PeanoNat.Nat.lt_0_succ.
Defined.

Next Obligation.
  destruct input as [ [ | x' rst' ] ].
  + discriminate.
  + now inversion H; subst.
Qed.
