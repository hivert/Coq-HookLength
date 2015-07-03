Require Import ssreflect ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Require Import bigop Omega fintype.

Definition f (n:nat) := (\sum_(i<n.+1) i).

Lemma S10 : f(10)=55.

Theorem sommation : forall (n : nat), 2 * sumn (iota 1 n) = n*(n.+1).
induction n; first trivial.
replace (n.+1) with (n+1) by ring.
rewrite (iota_add ).
rewrite sumn_cat.
simpl.
ring_simplify.
rewrite IHn.
ring.
Qed.

Theorem sommation_ssr n : 2 * sumn (iota 1 n) = n * (n + 1).
Proof.
  elim: n => [//= | n IHn].
  (* rewrite -{1 3}[n.+1]addn1. *)
  rewrite -(addn1 n) iota_add sumn_cat.
  ring_simplify.
  rewrite IHn.
  simpl.
  ring.
Qed.

Theorem sommation3 n : 2 * sumn (iota 1 n) = n * (n + 1).
Proof.
  elim: n => [//= | n IHn].
  (* rewrite -{1 3}[n.+1]addn1. *)
  rewrite -(addn1 n).
  rewrite 
 iota_add /= sumn_cat !mulnDr IHn /= mulnC -!addnA.
  congr (_ + _).
  by rewrite muln0 !muln1 /= !add0n addn0 [RHS]addnA [RHS]addnC [n + 1]addnC.
Qed.

Theorem sommation4 n : 2 * (\sum_(i<n.+1) i) = n * (n + 1).
elim : n => [|n IHn].
rewrite big_ord_recr.
rewrite big_ord0.
reflexivity.
replace (\sum_(i < n.+2) i) with ((\sum_(i < n.+1) i) + n.+1).
rewrite mulnDr.
rewrite IHn.
ring.
symmetry.
apply big_ord_recr.
Qed.
