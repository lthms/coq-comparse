From ExtLib Require Export MonadState StateMonad Functor Applicative Monad EitherMonad.
From Coq Require Export String.

Export FunctorNotation.
Export ApplicativeNotation.
Export MonadBaseNotation.

Open Scope monad_scope.

Generalizable All Variables.

(** * Definition *)

Definition error_stack := list string.

Notation parser i := (stateT i (sum error_stack)).

Declare Scope parser_scope.

(** * Type Classes *)

(** ** Definition *)

Class Input (i : Type) (t : Type) :=
  { unpack (x : i) : option (t * i)
  ; input_to_string (x : i) : string
  ; token_to_string (x : t) : string
  }.

Class InputLaws (i : Type) (t : Type) (len : i -> nat) `{Input i t} : Prop :=
  { unpack_equ_1 (input : i) : len input = 0%nat <-> unpack input = None
  ; unpack_equ_2 (input : i) : (0 < len input)%nat <-> exists x output, unpack input = Some (x, output)
  ; unpack_len (input rst : i) (x : t) : unpack input = Some (x, rst) -> len input = S (len rst)
  }.

Class Parser {i t α} (len : i -> nat) `{InputLaws i t len} (p : parser i α) : Prop :=
  { is_parser (input : i) : forall (x : α) (output : i),
      runStateT p input = inr (x, output) -> (len output <= len input)%nat
  }.

Class StrictParser {i t α} (len : i -> nat) `{InputLaws i t len} (p : parser i α) : Prop :=
  { is_strict (input : i) : forall (x : α) (output : i),
      runStateT p input = inr (x, output) -> (len output < len input)%nat
  }.

(** ** Instances *)

(** *** Reflexivity *)

Instance strict_parser `(StrictParser i t α len p) : Parser len p.

Proof.
  constructor.
  intros input x output equ.
  apply PeanoNat.Nat.lt_le_incl.
  now apply is_strict in equ.
Qed.

(** *** Functor *)

Instance map_parser {i α β} (len : i -> nat) (f : α -> β) `(Parser i t α len p)
  : Parser len (f <$> p).

Proof.
  constructor.
  intros input x output.
  cbn.
  case_eq (runStateT p input).
  + now intros.
  + intros [y output'] equ equ'.
    cbn in equ'.
    inversion equ'; subst.
    now apply is_parser in equ.
Qed.

Instance map_strict {i t α β} (f : α -> β) `(StrictParser i t α len p)
  : StrictParser len (f <$> p).

Proof.
  constructor.
  intros input x output.
  cbn.
  case_eq (runStateT p input).
  + now intros.
  + intros [y output'] equ equ'.
    cbn in equ'.
    inversion equ'; subst.
    now apply is_strict in equ.
Qed.

(** *** Applicative *)

Instance pure_Parser : @Parser i t α H H1 len (pure x).

Proof.
  intros i t α H x.
  constructor.
  intros input y output equ.
  now inversion equ; subst.
Qed.

Instance apply_parser
   `(H : Input i t, @Parser i t (α -> β) len H H1 f, @Parser i t α len H H1 p)
  : Parser len (f <*> p)|10.

Proof.
  constructor.
  intros input x output.
  cbn.
  case_eq (runStateT f input).
  + now intros.
  + intros [y output'] equ equ'.
    cbn in equ'.
    case_eq (runStateT p output').
    ++ intros e equ''.
       now rewrite equ'' in equ'.
    ++ intros [z output''] equ''.
       rewrite equ'' in equ'.
       cbn in equ'.
       inversion equ'; subst.
       transitivity (len output').
       +++ now apply is_parser in equ''.
       +++ now apply is_parser in equ.
Qed.

Instance apply_strict_1
   `(H : Input i t, @StrictParser i t (α -> β) len H H1 f, @Parser i t α len H H1 p)
  : StrictParser len (f <*> p)|10.

Proof.
  constructor.
  intros input x output.
  cbn.
  case_eq (runStateT f input).
  + now intros.
  + intros [y output'] equ equ'.
    cbn in equ'.
    case_eq (runStateT p output').
    ++ intros e equ''.
       now rewrite equ'' in equ'.
    ++ intros [z output''] equ''.
       rewrite equ'' in equ'.
       cbn in equ'.
       inversion equ'; subst.
       apply PeanoNat.Nat.le_lt_trans with (m := len output').
       +++ now apply is_parser in equ''.
       +++ now apply is_strict in equ.
Qed.

Instance apply_strict_2
   `(H : Input i t, @Parser i t (α -> β) len H H1 f, @StrictParser i t α len H H1 p)
  : StrictParser len (f <*> p)|15.

Proof.
  constructor.
  intros input x output.
  cbn.
  case_eq (runStateT f input).
  + now intros.
  + intros [y output'] equ equ'.
    cbn in equ'.
    case_eq (runStateT p output').
    ++ intros e equ''.
       now rewrite equ'' in equ'.
    ++ intros [z output''] equ''.
       rewrite equ'' in equ'.
       cbn in equ'.
       inversion equ'; subst.
       eapply PeanoNat.Nat.lt_le_trans with (m := len output').
       +++ now apply is_strict in equ''.
       +++ now apply is_parser in equ.
Qed.

(** *** Monad *)

Instance bind_parser `(Parser i t α len p, (forall x, @Parser i t β len _ _ (f x)))
  : Parser len (p >>= f).

Proof.
  constructor.
  intros input x output.
  cbn.
  case_eq (runStateT p input).
  + now intros.
  + intros [y output'] equ equ'.
    cbn in equ'.
    specialize H2 with y.
    apply is_parser in equ.
    apply is_parser in equ'.
    etransitivity; eauto.
Qed.

(** Note: wrt. [bind] and [StrictParser], we provide two different instances
    whose goal is basically to find at least one strict parser in one of the two
    operands.

    We manually assign a priority so that (1) Coq prefers other instances first,
    and to be sure Coq first searches for a strict parser in the left operand of
    [bind] first.  This way, the parser is explored from the beginning of the
    parser up to the end, and not the other way around. *)

Instance bind_strict_1
   `(StrictParser i t α len p, (forall x, @Parser i t β len _ _ (f x)))
  : StrictParser len (p >>= f)|10.

Proof.
  constructor.
  intros input x output.
  cbn.
  case_eq (runStateT p input).
  + now intros.
  + intros [y output'] equ equ'.
    cbn in equ'.
    specialize H2 with y.
    apply is_strict in equ.
    apply is_parser in equ'.
    eapply PeanoNat.Nat.le_lt_trans; eauto.
Qed.

Instance bind_strict_2
  `(Parser i t α len p, (forall x, @StrictParser i t β len _ _ (f x)))
  : StrictParser len (p >>= f)|15.

Proof.
  constructor.
  intros input x output.
  cbn.
  case_eq (runStateT p input).
  + now intros.
  + intros [y output'] equ equ'.
    cbn in equ'.
    specialize H2 with y.
    apply is_parser in equ.
    apply is_strict in equ'.
    eapply PeanoNat.Nat.lt_le_trans; eauto.
Qed.

(** *** Conditional Branching *)

Instance if_parser
   `(H : Input i t, @Parser i t α len H H1 p, @Parser i t α len H H1 q)
    (cond : bool)
  : Parser len (if cond then p else q).

Proof.
  constructor.
  intros input x output equ.
  destruct cond;
    now apply is_parser in equ.
Qed.

Instance if_strict
   `(H : Input i t, @StrictParser i t α len H H1 p, @StrictParser i t α len H H1 q)
    (cond : bool)
  : StrictParser len (if cond then p else q).

Proof.
  constructor.
  intros input x output equ.
  destruct cond;
    now apply is_strict in equ.
Qed.
