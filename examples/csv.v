From Comparse Require Import Monad Combinators.
From Coq Require Import Ascii String.
From ExtLib Require Import Char.

Import AsciiSyntax.

Generalizable All Variables.

Definition entry `{Input string ascii} : parser string (list ascii) :=
  many_until read_token
             (peek ((token ","%char;; pure tt)
                         <|> (token "010"%char;; pure tt)
                         <|> eoi)).

Definition rows `{Input string ascii}
  : parser string (list (list ascii)) :=
  sep entry (token ","%char).

Definition csv `{Input string ascii}
  : parser string (list (list (list ascii))) :=
  sep rows (token "010"%char).

From Coq Require Extraction.
Extraction "csv.ml" csv.
