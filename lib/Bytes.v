From Coq Require Export Byte.
From Prelude Require Import All.
From Comparse Require Import Monad Combinators.

#[program]
Instance byte_EquDec : EquDec byte :=
  { equalb := Byte.eqb
  }.

Next Obligation.
  split.
  + apply Byte.byte_dec_lb.
  + apply Byte.byte_dec_bl.
Defined.

Inductive bytes := to_bytes { of_bytes : list byte }.
Definition id_byte (x : byte) := x.

Declare Scope bytes_scope.
Delimit Scope bytes_scope with bytes.
Bind Scope bytes_scope with bytes.

String Notation bytes to_bytes of_bytes : bytes_scope.
String Notation byte id_byte id_byte : byte_scope.

Definition append (x y : bytes) :=
  to_bytes (List.app (of_bytes x) (of_bytes y)).

Infix "++" := append : bytes_scope.

#[program]
Instance bytes_Input : Input bytes byte :=
  { length := fun x => List.length (of_bytes x)
  ; unpack := fun (x : bytes) =>
                match x with
                | to_bytes [] => None
                | to_bytes (x :: rst) => Some (x, to_bytes rst)
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
       exists (to_bytes rst).
       reflexivity.
    ++ intros _.
       apply PeanoNat.Nat.lt_0_succ.
Defined.

Next Obligation.
  destruct input as [ [ | x' rst' ] ].
  + discriminate.
  + now inversion H; subst.
Qed.
