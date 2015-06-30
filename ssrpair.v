Require Import ssreflect ssrbool eqtype seq ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Version SSReflect *)

Fixpoint div2 n : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | n'.+2 => S (div2 n')
  end.

Lemma indSS (P : nat -> Prop) :
  P 0 -> P 1 -> (forall n : nat, P n -> P n.+2) -> forall n : nat, P n.
Proof.
  move=> H0 H1 IHn n.
  move H2 : (div2 n) => m.
  elim: m n H2 => [//= | m IHm] [| [| n]] //=.
  move/eqP; by rewrite eqSS => /eqP/IHm/IHn.
Qed.

Fixpoint is_even n :=
  match n with 0 => true | 1 => false | p.+2 => is_even p end.

Definition even n := exists p, n = 2*p.

Lemma is_evenP n : reflect (even n) (is_even n).
Proof.
  rewrite /even; apply (iffP idP).
  - elim/indSS: n => [_ | | n IHn] //=; first by exists 0.
    move/IHn => [] x ->.
    exists x.+1.
    by rewrite -2!addn1 -[x.+1]add1n -addnA add1n addnC mulnDr.
  - move=> [] {n} n ->.
    elim: n => [//= |n IHn]. (* rewrite /= Triggers a strange bug *)
    by rewrite -(addn1 n) mulnDr muln1 -{2}[2]addn1 addnA !addn1.
Qed.
