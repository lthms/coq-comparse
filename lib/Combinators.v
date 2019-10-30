From Coq Require Import String FunInd Recdef.
From Prelude Require Import All.
From Comparse Require Import Monad.

(** ** <<many>> *)

(** [many p] tries to apply a _strict_ parser [p] as long as [p] succeeds, then
    returns the list of terms constructed by [p].

      - [many p] is never a _strict_ parser. It consumes the input if [p]
        succeeds at least once.
      - [many p] never fails. *)

(* begin hide *)
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
(* end hide *)
Definition many `{Input i t} {α} (p : parser i α) `{StrictParser i t α p} : parser i (list α) :=
  fun (input : i) => inr (many_aux _ _ _ _ p _ input []).

Instance many_parser `(StrictParser i t α p) : Parser (many p).
(* begin hide *)
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
(* end hide *)

(** ** <<some>> *)

(** [some p] tries to apply a _strict_ parser [p] at least once, and as long as
    [p] succeeds, then returns the list of terms constructed by [p]. That is,
    contrary to [many p], [some p] fails if [p] does not succeed at least once.

      - [some p] is a _strict_ parser.
      - [some p] fails if [p] does not suceed at least once. *)

Definition some `{Input i t} {α} (p : parser i α) `{StrictParser i t α p} : parser i (list α) :=
  cons <$> p <*> (many p).

(** ** <<alt>> *)

(** [p <|> q] first tries to apply [p] and returns its result if [p]
    succeeds. Otherwise, it tries to apply [q].

      - [p <|> q] is a _strict_ parser if both [p] and [q] are _strict_. It
        consumes the same input as [p] or [q] would if applied directly.
      - [p <|> q] fails if both [p] and [q] fail. *)

Definition alt `{Input i t} {α} (p q : parser i α) : parser i α :=
  fun* input =>
    match p input with
    | inl _ => q input
    | x => x
    end.

Infix "<|>" := alt (at level 50, left associativity) : monad_scope.

Instance alt_Parser `(Input i t, !@Parser i t α _ p, !@Parser i t α _  q) : @Parser i t α _ (alt p q).
(* begin hide *)
Proof.
  unfold alt.
  constructor.
  intros input x output equ.
  case_eq (p input).
  + intros e eque.
    rewrite eque in equ.
    now apply is_parser in equ.
  + intros [x' output'] equ'.
    rewrite equ' in equ.
    inversion equ; subst.
    now apply is_parser in equ'.
Qed.
(* end hide *)

Instance alt_Strict `(Input i t, !@StrictParser i t α _ p, !@StrictParser i t α _  q) : @StrictParser i t α _ (alt p q).
(* begin hide *)
Proof.
  unfold alt.
  constructor.
  intros input x output equ.
  case_eq (p input).
  + intros e eque.
    rewrite eque in equ.
    now apply is_strict in equ.
  + intros [x' output'] equ'.
    rewrite equ' in equ.
    inversion equ; subst.
    now apply is_strict in equ'.
Qed.
(* end hide *)

(** ** <<optional>> *)

(** [optional p] tries to apply [p], but does not fail if [p] fails and just
    returns [None] instead, leaving the input untouched.

      - [optional p] is _strict_ if [p] is _strict_. It consumes the same [input] as [p] would if applied directly.
      - [optional p] never fails. *)


Definition optional `{Input i t} {α} (p : parser i α) : parser i (option α) :=
  (Some <$> p) <|> pure None.

(** ** <<fail>> *)

Definition fail `{Input i t} {α} (msg : string) : parser i α :=
  fun s => inl [msg].

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

(** ** <<tag>> *)

Fixpoint tag `{EquDec t, Input i t} (x : list t) : parser i unit :=
  match x with
  | x :: rst => do token x *> tag rst end
  | [] => pure tt
  end.

Instance tag_parser `(EquDec t, Input i t) (l : list t) : Parser (tag l).
(* begin hide *)
Proof.
  induction l; typeclasses eauto.
Qed.
(* end hide *)

(** [tag' x] is a variant of [tag x] which returns [x] and not [tt]. This can be
    useful used in conjunction of [<|>]. *)

Definition tag' `{EquDec t, Input i t} (x : list t) : parser i (list t) :=
  tag x *> pure x.

(** ** <<many_until>> *)

(** [many_until p q] applies the _strict_ parser [p] as long as [q] fails, then
    returns the list of terms produced by [p].

      - [many_until p q] is a _strict_ parser if _q_ is strict.
      - [many_until p q] fails if [p] fails before [q] could suceed. *)

(* begin hide *)
Function many_until_aux (α β i t : Type) (I : Input i t)
    (p : parser i α) (H : StrictParser p) (q : parser i β)
    (input : i) (acc : list α) {measure length input}
  : error_stack + (list α * i) :=
  match q input with
  | inl _ => match p input with
             | inl _ => inl ["p failed before q could succeed"%string]
             | inr (x, output) => many_until_aux α β i t I p H q output (x :: acc)
             end
  | inr (_, output) => inr (rev acc, output)
  end.

Proof.
  intros α b i t I p H q input acc e eque res x output equr equ.
  now apply is_strict in equ.
Defined.
(* end hide *)
Definition many_until {α β} `{Input i t}
    (p : parser i α) `{StrictParser i t α p} (q : parser i β)
  : parser i (list α) :=
  fun input => many_until_aux _ _ _ _ _ p _ q input [].

Instance many_until_parser `(Input i t, !StrictParser (p : parser i a), !Parser (q : parser i b))
  : Parser (many_until p q).
(* begin hide *)
Proof.
  constructor.
  intros input x output equ.
  unfold many_until in *.
  functional induction (many_until_aux a b i t _ p _ q input []).
  + discriminate.
  + destruct many_until_aux.
    ++ discriminate.
    ++ destruct p0 as [y output'].
       inversion equ; subst.
       transitivity (length output0).
       +++ now apply IHs.
       +++ now apply is_parser in e0.
  + inversion equ; subst.
    now apply is_parser in e.
Qed.
(* end hide *)

Instance many_until_strict `(Input i t, !StrictParser (p : parser i α), !StrictParser (q : parser i β))
  : StrictParser (many_until p q).
(* begin hide *)
Proof.
  constructor.
  intros input x output equ.
  unfold many_until in *.
  functional induction (many_until_aux α β i t _ p _ q input []).
  + discriminate.
  + destruct many_until_aux.
    ++ discriminate.
    ++ destruct p0 as [y output'].
       inversion equ; subst.
       transitivity (length output0).
       +++ now apply IHs.
       +++ now apply is_strict in e0.
  + inversion equ; subst.
    now apply is_strict in e.
Qed.
(* end hide *)

(** ** <<some_until>> *)

(** [some_until p q] applies the _strict_ parser [p] as long as [q] fails, then
    returns the list of terms produced by [p]. Contrary to [many_until],
    [some_until] requires [p] to succeed at least once.

      - [some_until p q] is a _strict_ parser.
      - [some_until p q] fails [p] does not succeeds at least once, and if [p]
        fails before [q] could succeed. *)

Definition some_until {α β} `{Input i t}
    (p : parser i α) `{StrictParser i t α p} (q : parser i β)
  : parser i (list α) :=
  cons <$> p <*> many_until p q.

(** ** <<sep>> *)

Definition sep {α β} `{Input i t} (p : parser i α)
    (q : parser i β) `{!StrictParser q, !Parser p}
  : parser i (list α) :=
  cons <$> p <*> many (q *> p).
