From Coq Require Import String FunInd Recdef.
From Prelude Require Import All.
From Comparse Require Import Monad.

(** ** <<many>> *)

Function many_aux (i t : Type) (I : Input i t) (α : Type) (p : parser i α) (S : StrictParser p)
    (input : i) (acc : list α) {measure length input}
  : list α * i :=
  match p input with
  | inl _ => (rev acc, input)
  | inr (x, output) => many_aux i t I α p S output (x :: acc)
  end.

Proof.
  intros i t I a p S input acc res x output eqr equ.
  now apply is_strict in equ.
Defined.

Definition many `{Input i t} {α} (p : parser i α) `{StrictParser i t α p} : parser i (list α) :=
  fun (input : i) => inr (many_aux _ _ _ _ p _ input []).

Instance many_parser `(StrictParser i t α p) : Parser (many p).

Proof.
  unfold many.
  constructor.
  intros input x output equ.
  functional induction (many_aux i t H α p H0 input []).
  + now inversion equ; ssubst.
  + transitivity (length output0).
    ++ apply (IHp0 equ).
    ++ now apply is_parser in e.
Qed.

(** ** <<some>> *)

Definition some `{Input i t} {α} (p : parser i α) `{StrictParser i t α p} : parser i (list α) :=
  cons <$> p <*> (many p).

(** ** <<fail>> *)

Definition fail `{Input i t} {α} (msg : string) : parser i α :=
  fun s => inl (msg :: nil).

Instance fail_Parser : Parser (@fail i t H α msg).

Proof.
  constructor.
  now intros input x output equ.
Qed.

(** ** <<read_token>> *)

Definition read_token `{Input i t} : parser i t :=
  do let* input <- get in
     match unpack input with
     | Some (x, rst) => put rst *> pure x
     | None => fail "expected character, found end of input"
     end
  end.

Instance read_token_Strict : StrictParser (@read_token i t H).

Proof.
  constructor.
  intros input x output equ.
  unfold read_token in equ.
  cbn in equ.
  case_eq (unpack input).
  + intros [y rst] equ'.
    rewrite equ' in equ.
    inversion equ; subst.
    rewrite (unpack_length input output y equ').
    auto.
  + intros equ'.
    now rewrite equ' in equ.
Qed.

(** ** <<ensure>> *)

Definition ensure `{Input i t} {α} (p : parser i α) (cond : α -> bool) : parser i α :=
  do let* res <- p in
     if cond res
     then pure res
     else fail "ensure: result of p is not valid according to cond"
  end.

(** ** <<token>> *)

Definition token `{EquDec t, Input i t} (a : t) : parser i t :=
  ensure read_token (equalb a).
