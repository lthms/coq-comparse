From Prelude Require Import All.
From Comparse Require Import Monad Combinators.

Remark some_parser `(StrictParser i t α p) : StrictParser (some p).

Proof.
  typeclasses eauto.
Qed.

Remark ensure_Strict `(StrictParser i t α p) (cond : α -> bool) : StrictParser (ensure p cond).

Proof.
  typeclasses eauto.
Qed.

Remark ensure_Parser `(Parser i t α p) (cond : α -> bool) : Parser (ensure p cond).

Proof.
  typeclasses eauto.
Qed.

Remark token_Strict `(EquDec t, StrictParser i t α p) (cond : α -> bool) : StrictParser (ensure p cond).

Proof.
  typeclasses eauto.
Qed.

Remark token_Parser `(EquDec t, Parser i t α p) (cond : α -> bool) : Parser (ensure p cond).

Proof.
  typeclasses eauto.
Qed.
