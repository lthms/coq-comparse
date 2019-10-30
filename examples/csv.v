From Prelude Require Import All.
From Comparse Require Import Monad Combinators Bytes.

(* TODO: use a more relevant entry format *)
Definition entry : parser bytes bytes :=
  to_bytes <$> many (token "a"%byte).

Definition rows : parser bytes (list bytes) :=
  sep entry (token ","%byte).

Definition csv : parser bytes (list (list bytes)) :=
  sep rows (token x0a).

Arguments csv _%bytes.

Definition newline : bytes := to_bytes [x0a].

Eval lazy in do
  fst <$> csv ("aaa,aaaa,aaaaa" ++ newline ++
               ",,aaaaa,")
end.
