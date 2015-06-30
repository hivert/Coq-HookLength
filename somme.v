Require Import ssreflect ssrbool ssrnat eqtype seq bigop.

Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sommation n : 2 * sumn (iota 1 n) = n * (n + 1).
Proof.
  elim: n => [//= | n IHn].
  (* rewrite -{1 3}[n.+1]addn1. *)
  rewrite -(addn1 n) iota_add /= sumn_cat !mulnDr IHn /= mulnC -!addnA.
  congr (_ + _).
  by rewrite muln0 !muln1 /= !add0n addn0 [RHS]addnA [RHS]addnC [n + 1]addnC.
Qed.
