From Coq Require Import String FunInd Recdef List.
From ExtLib Require Import RelDec.
From Comparse Require Import Monad.

Import ListNotations.
Import MonadLetNotation.

Generalizable All Variables.

Open Scope parser_scope.
Open Scope monad_scope.

(** ** <<many>> *)

(** [many p] tries to apply a _strict_ parser [p] as long as [p] succeeds, then
    returns the list of terms constructed by [p].

      - [many p] is never a _strict_ parser. It consumes the input if [p]
        succeeds at least once.
      - [many p] never fails. *)

Function many_aux
    (i t : Type) (len : i -> nat) (I : Input i t)
    (L : @InputLaws i t len I) (α : Type) (p : parser i α)
    (S : StrictParser len p)
    (input : i) (acc : list α) {measure len input}
  : list α * i :=
  match runStateT p input with
  | inr (x, output) => many_aux i t len I L α p S output (x :: acc)
  | inl _ => (rev acc, input)
  end.

Proof.
  intros i t len I L a p S input acc res x output eqr equ.
  now apply is_strict in equ.
Defined.

Arguments many_aux {_ _ _ _ _ _} _ [_] _ _.
Extraction Implicit many_aux [x1].

Definition many `{I : Input i t} {α} (p : parser i α) `{StrictParser i t α len p} : parser i (list α) :=
  mkStateT (fun (input : i) => inr (many_aux p input [])).

Extraction Implicit many [I len].

Instance many_parser `(StrictParser i t α len p) : Parser len (many p).

Proof.
  unfold many.
  constructor.
  intros input x output equ.
  cbn in equ.
  inversion equ.
  functional induction (many_aux p input []).
  + transitivity (len output0).
    ++ eapply IHp0; eauto.
    ++ now apply is_parser in e.
  + now inversion equ.
Qed.

(** ** <<some>> *)

(** [some p] tries to apply a _strict_ parser [p] at least once, and as long as
    [p] succeeds, then returns the list of terms constructed by [p]. That is,
    contrary to [many p], [some p] fails if [p] does not succeed at least once.

      - [some p] is a _strict_ parser.
      - [some p] fails if [p] does not suceed at least once. *)

Definition some `{I : Input i t} {α} (p : parser i α) `{StrictParser i t α len p} : parser i (list α) :=
  cons <$> p <*> (many p).

Extraction Implicit some [I len].

(** ** <<alt>> *)

(** [p <|> q] first tries to apply [p] and returns its result if [p]
    succeeds. Otherwise, it tries to apply [q].

      - [p <|> q] is a _strict_ parser if both [p] and [q] are _strict_. It
        consumes the same input as [p] or [q] would if applied directly.
      - [p <|> q] fails if both [p] and [q] fail. *)

Definition alt {i α} (p q : parser i α) : parser i α :=
  mkStateT (fun input =>
              match runStateT p input with
              | inl _ => runStateT q input
              | x => x
              end).

Infix "<|>" := alt (at level 50, left associativity) : parser_scope.

Instance alt_Parser
   `(InputLaws i t len, ! @Parser i t α len _ _ p, ! @Parser i t α len _ _ q)
  : @Parser i t α len _ _ (alt p q).

Proof.
  unfold alt.
  constructor.
  intros input x output equ.
  case_eq (runStateT p input).
  + intros e eque.
    cbn in equ.
    rewrite eque in equ.
    now apply is_parser in equ.
  + intros [x' output'] equ'.
    cbn in equ.
    rewrite equ' in equ.
    inversion equ; subst.
    now apply is_parser in equ'.
Qed.

Instance alt_Strict
   `(InputLaws i t len, !@StrictParser i t α len _ _ p, !@StrictParser i t α len _ _ q)
  : @StrictParser i t α len _ _ (alt p q).

Proof.
  unfold alt.
  constructor.
  intros input x output equ.
  case_eq (runStateT p input); cbn in equ.
  + intros e eque.
    rewrite eque in equ.
    now apply is_strict in equ.
  + intros [x' output'] equ'.
    rewrite equ' in equ.
    inversion equ; subst.
    now apply is_strict in equ'.
Qed.

(** ** <<optional>> *)

(** [optional p] tries to apply [p], but does not fail if [p] fails and just
    returns [None] instead, leaving the input untouched.

      - [optional p] is _strict_ if [p] is _strict_. It consumes the same [input] as [p] would if applied directly.
      - [optional p] never fails. *)

Definition optional {i α} (p : parser i α) : parser i (option α) :=
  (Some <$> p) <|> pure None.

(** ** <<fail>> *)

Definition fail {i α} (msg : string) : parser i α :=
  mkStateT (fun s => inl [msg]).

Instance fail_Parser `(InputLaws i t len) : Parser len (@fail i α msg).

Proof.
  constructor.
  now intros input x output equ.
Qed.

(** ** <<read_token>> *)

Definition read_token `{Input i t} : parser i t :=
  let* input := MonadState.get in
  match unpack input with
  | Some (x, rst) => put rst;;
                     pure x
  | None => fail "expected character, found end of input"
  end.

Instance read_token_Strict `(InputLaws i t len) : StrictParser len (@read_token i t _).

Proof.
  constructor.
  intros input x output equ.
  unfold read_token in equ.
  cbn in equ.
  case_eq (unpack input).
  + intros [y rst] equ'.
    rewrite equ' in equ.
    cbn in equ.
    inversion equ; subst.
    rewrite (unpack_len (InputLaws := H0) input output x equ').
    auto.
  + intros equ'.
    now rewrite equ' in equ.
Qed.

(** ** <<ensure>> *)

Definition ensure `{Input i t} {α} (p : parser i α) (cond : α -> bool) : parser i α :=
  let* res := p in
  if cond res
  then pure res
  else fail "ensure: result of p is not valid according to cond".

(** ** <<token>> *)

Definition token `{RelDec t eqv, I : Input i t} (a : t) : parser i t :=
  ensure read_token (rel_dec a).

(** ** <<tag>> *)

Function tag_aux (i t : Type) (eqv : t -> t -> Prop) (H : @RelDec t eqv)
    (len : i -> nat)
    (I : Input i t) (L : InputLaws i t len) (x : i) (input : i)
    {measure len x}
  : error_stack + (unit * i) :=
  match unpack input, unpack x with
  | Some (c, rst), Some (c', rst') =>
    if rel_dec c c'
    then tag_aux i t _ H len I L rst' rst
    else inl ["nop"%string]
  | _, None => inr (tt, input)
  | _, _ => inl ["nop"%string]
  end.

Proof.
  intros i t H' H len I L x input [x' input'] c' rst' equ1 equ2 [y rst] y' rst'' equ3 equ4 equ5.
  inversion equ3; subst.
  apply unpack_len in equ4.
  rewrite equ4.
  auto with arith.
Defined.

Arguments tag_aux [_ _ _ _ _ _ _] _ _.
Extraction Implicit tag_aux [x3].

Definition tag `{RelDec t eqv, InputLaws i t len} (x : i) : parser i unit :=
  mkStateT (fun input => tag_aux x input).

Extraction Implicit tag [len].

Instance tag_parser `(RelDec t eqv, InputLaws i t len) : Parser len (tag x).

Proof.
  intros x.
  constructor.
  intros input r output equ.
  unfold tag in equ.
  cbn in *.
  functional induction (tag_aux x input).
  + transitivity (len rst).
    ++ apply IHs.
       apply equ.
    ++ apply unpack_len in e.
       rewrite e.
       auto with arith.
  + discriminate.
  + inversion equ; subst.
    auto with arith.
  + discriminate.
Qed.

(** [tag' x] is a variant of [tag x] which returns [x] and not [tt]. This can be
    useful used in conjunction of [<|>]. *)

Definition tag' `{RelDec t eqv, InputLaws i t len} (x : i) : parser i i :=
  tag x;;
  pure x.

Extraction Implicit tag' [len].

(** ** <<many_until>> *)

(** [many_until p q] applies the _strict_ parser [p] as long as [q] fails, then
    returns the list of terms produced by [p].

      - [many_until p q] is a _strict_ parser if _q_ is strict.
      - [many_until p q] fails if [p] fails before [q] could suceed. *)

Function many_until_aux (α β i t : Type) (len : i -> nat) (I : Input i t)
    (L : InputLaws i t len)
    (p : parser i α) (H : StrictParser len p) (q : parser i β)
    (input : i) (acc : list α) {measure len input}
  : error_stack + (list α * i) :=
  match runStateT q input with
  | inl _ => match runStateT p input with
             | inl _ => inl ["p failed before q could succeed"%string]
             | inr (x, output) => many_until_aux α β i t len I L p H q output (x :: acc)
             end
  | inr (_, output) => inr (rev acc, output)
  end.

Proof.
  intros α b i t len I L p H q input acc e eque res x output equr equ.
  now apply is_strict in equ.
Defined.

Arguments many_until_aux [_ _ _ _ _ _ _] _ [_] _ _ _.
Extraction Implicit many_until_aux [x3].

Definition many_until {α β} `{InputLaws i t len}
    (p : parser i α) `{StrictParser i t α len p} (q : parser i β)
  : parser i (list α) :=
  mkStateT (fun input => many_until_aux p q input []).

Extraction Implicit many_until [len].

Instance many_until_parser
   `(InputLaws i t len, !StrictParser len (p : parser i a), !Parser len (q : parser i b))
  : Parser len (many_until p q).

Proof.
  constructor.
  intros input x output equ.
  unfold many_until in *.
  cbn in *.
  functional induction (many_until_aux p q input []).
  + discriminate.
  + destruct many_until_aux.
    ++ discriminate.
    ++ destruct p0 as [y output'].
       inversion equ; subst.
       transitivity (len output0).
       +++ now apply IHs.
       +++ now apply is_parser in e0.
  + inversion equ; subst.
    now apply is_parser in e.
Qed.

Instance many_until_strict
   `(InputLaws i t len, !StrictParser len (p : parser i α), !StrictParser len (q : parser i β))
  : StrictParser len (many_until p q).

Proof.
  constructor.
  intros input x output equ.
  unfold many_until in *.
  cbn in *.
  functional induction (many_until_aux p q input []).
  + discriminate.
  + destruct many_until_aux.
    ++ discriminate.
    ++ destruct p0 as [y output'].
       inversion equ; subst.
       transitivity (len output0).
       +++ now apply IHs.
       +++ now apply is_strict in e0.
  + inversion equ; subst.
    now apply is_strict in e.
Qed.

(** ** <<some_until>> *)

(** [some_until p q] applies the _strict_ parser [p] as long as [q] fails, then
    returns the list of terms produced by [p]. Contrary to [many_until],
    [some_until] requires [p] to succeed at least once.

      - [some_until p q] is a _strict_ parser.
      - [some_until p q] fails [p] does not succeeds at least once, and if [p]
        fails before [q] could succeed. *)

Definition some_until {α β} `{InputLaws i t len}
    (p : parser i α) `{StrictParser i t α len p} (q : parser i β)
  : parser i (list α) :=
  cons <$> p <*> many_until p q.

Extraction Implicit some_until [len].

(** ** <<sep>> *)

Definition sep {α β} `{InputLaws i t len} (p : parser i α)
    (q : parser i β) `{!StrictParser len q, !Parser len p}
  : parser i (list α) :=
  cons <$> p <*> many (q;; p).

Extraction Implicit sep [len].

(** ** <<eoi>> *)

Definition eoi `{Input i t} : parser i unit :=
  mkStateT (fun input =>
              match unpack input with
              | None => inr (tt, input)
              | Some (c, _) => inl [("Expected end of input, found " ++ token_to_string c)%string]
              end).

Instance eoi_Parser `(InputLaws i t len) : Parser len (eoi (i := i)).

Proof.
  constructor.
  intros input res output Heq.
  unfold eoi in Heq.
  cbn in *.
  destruct (unpack input) as [[tok in'] | ]; cbn in *.
  + discriminate.
  + now inversion Heq.
Qed.

(** ** <<skip>> *)

Definition skip {i α} (p : parser i α) : parser i unit :=
  p;;
  pure tt.

(** ** <<peek>> *)

Definition peek {i α} (p : parser i α) : parser i α :=
  mkStateT (fun input =>
              match runStateT p input with
              | inr (x, _) => inr (x, input)
              | inl x => inl x
              end).

Instance peek_Parser `(InputLaws i t len) (a : Type) (p : parser i a) : Parser len (peek p).

Proof.
  constructor.
  intros input res output Heq.
  unfold peek in Heq.
  cbn in *.
  destruct (runStateT p input) as [err | [res' in']]; cbn in *.
  + discriminate.
  + now inversion Heq.
Qed.
