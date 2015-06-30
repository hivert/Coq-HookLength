Require Import Arith.
Require Import Omega.

Fixpoint even1 (n:nat) :=
    match n with 0 => True | S 0 => False | S (S p) => even1 p end.

Definition rec2 := Div2.ind_0_1_SS.

Definition even2 n := exists p, n = 2*p.

Theorem even40 : (even2 40).
Proof.
unfold even2.
exists 20.
trivial.
Qed.

Lemma even12 : forall n, even1 n <-> even2 n.
induction n using rec2.
simpl.
intuition.
exists 0; trivial.
simpl; intuition.
destruct H.
omega.
simpl.
rewrite IHn.
intuition.
destruct H0.
exists (S x); intuition.
destruct H1.
exists (pred x); intuition.
Save.

Inductive even3 : nat -> Prop :=
   even0 : even3 0 | evenSS : forall n, even3 n -> even3 (S (S n)).
Hint  Constructors even3.

Lemma even31 : forall n, even3 n -> even1 n.
induction 1; simpl; trivial.
Save.

Lemma even13 : forall n, even1 n -> even3 n.
induction n using rec2; simpl; intuition.
Save.

Lemma notPclasse : forall P , ~~(P \/ ~P).
intros P HP.
red in HP.
apply HP.
right.
intro Hp.
apply HP.
left.
exact Hp.
Save.

Lemma allevenornot : forall n, even1 n \/ ~ (even1 n).
induction n using rec2; simpl; intuition.
Save.

Lemma even23 : forall n, even2 n <-> even3 n.
intro n.
intuition.
(even12 n).
