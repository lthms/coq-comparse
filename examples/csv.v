From Prelude Require Import All Bytes.
From Comparse Require Import Monad Combinators Bytes.

(* TODO: use a more relevant entry format *)
Definition entry : parser bytes bytes := wrap_bytes <$> many (token "a"%byte).

Definition rows : parser bytes (list bytes) := sep entry (token ","%byte).

Definition csv : parser bytes (list (list bytes)) := sep rows (token x0a).

Arguments csv !_%bytes.

Time Eval vm_compute in do
  fst <$> csv ("aaa,aaaa,aaaaa\n" ++
               ",,aaaaa,\n"       ++
               "aa,a")
end.
