Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
           | le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)

Definition relation (X: Type) := X -> X -> Prop.

Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Check next_nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H Q. 
  inversion H.
  inversion Q.
  reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  intros contra.
unfold partial_function in contra.
specialize contra with (x := 0).
specialize contra with (y1 := 0).
specialize contra with (y2 := 1).
assert (H: 0 <= 0).
reflexivity.
assert (G: 0 <= 1).
apply le_S.
reflexivity.
apply contra in H.
inversion H.
apply G.
Qed.

Inductive empty_relation : nat -> nat -> Prop := .
  

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H Q. 
  inversion H.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive.
  intros a.
  reflexivity.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans' :
  transitive le.
Proof.
  unfold transitive.
  intros a b c.
  intros H G.
specialize le_trans with (m := a).
intros Q.
specialize Q with (n := b).
specialize Q with (o := c).
apply Q in H.
apply H.
apply G.
Qed.


Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt.
unfold transitive.
  intros a b c.
  intros H G.
apply le_plus_trans with (p:=1) in H.
rewrite <- plus_n_Sm in H.
rewrite -> add_0_r in H.
specialize le_trans with (m := S a).
intros R.
specialize R with (n:=S b).
specialize R with (o:=c).
apply R in H.
apply H.
apply G.
Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  apply le_plus_trans with (p:=1) in Hnm.
rewrite <- plus_n_Sm in Hnm.
rewrite -> add_0_r in Hnm.
apply Hnm.
apply le_plus_trans with (p:=1) in IHHm'o.
rewrite <- plus_n_Sm in IHHm'o.
rewrite -> add_0_r in IHHm'o.
apply IHHm'o.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o.
  inversion Hmo.
apply le_plus_trans with (p:=1) in Hnm.
rewrite <- plus_n_Sm in Hnm.
rewrite -> add_0_r in Hnm.
specialize le_trans with (m := S n).
intros R.
specialize R with (n:=S m).
specialize R with (o:=S o).
apply R in Hnm.
apply Hnm.
apply Hmo.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H.
  assert (Q : S n = n + 1).
  rewrite <- plus_n_Sm.
 rewrite -> add_0_r.
reflexivity.
rewrite Q in H.
apply plus_le in H.
destruct H.
apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  apply Sn_le_Sm__n_le_m in H.
  apply H.
Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  intros n contra.
  induction n.
  inversion contra.
  apply IHn.
  apply Sn_le_Sm__n_le_m in contra.
  apply contra.
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  intros contra.
  unfold symmetric in contra.
  specialize contra with (a := 0).
  specialize contra with (b := 1).
  assert (Q : 0 <= 1).
  apply le_S.
  reflexivity.
  apply contra in Q.
  inversion Q.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
 unfold antisymmetric. intros a b H1 H2.
  inversion H1.
  - reflexivity.
  - exfalso.
    rewrite <- H0 in H2.
    assert (Nonsense: S m <= m). {
      apply le_trans with a.
      apply H2.
      apply H.
    }
    apply (le_Sn_n m Nonsense).
Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros n m p H G.
  destruct H.
  apply Sn_le_Sm__n_le_m in G.
  apply G.
  apply le_Sn_le in H.
  apply Sn_le_Sm__n_le_m in G.
  specialize le_trans with (m := n).
  intros R.
  specialize R with (n := m).
  specialize R with (o := p).
  apply R in H.
  apply H.
  apply G.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order.
  split.
  apply le_reflexive.
  split.
  apply le_antisymmetric.
  apply le_trans' .
Qed.

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m.
  split.
  intros H.
  induction H.
  apply rt_refl.
  apply rt_trans with (y:=m).
  apply IHle.
  apply rt_step.
  apply nn.
  intros H.
  induction H.
  inversion H.
  apply le_S.
  apply le_n.
  apply le_n.
  specialize le_trans with (m := x).
  intros R.
  specialize R with (n := y).
  specialize R with (o := z).
  apply R in IHclos_refl_trans1.
  apply IHclos_refl_trans1.
  apply IHclos_refl_trans2.
Qed.

Inductive clos_refl_trans_1n {A : Type} (R : relation A) (x : A) : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A) (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) : clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros.
  apply rt1n_trans with (y := y).
  apply H.
apply rt1n_refl.
Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros.
  induction H.
apply H0.
apply rt1n_trans with (y:=y).
apply Hxy.
apply IHclos_refl_trans_1n.
apply H0.
Qed.

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros.
  split.
  intros H.
  induction H.
  apply rsc_R.
apply H.
apply rt1n_refl.
apply rsc_trans with (y:=y).
apply IHclos_refl_trans1.
apply IHclos_refl_trans2.
  intros H.
induction H.
apply rt_refl.
apply rt_trans with (y:=y).
apply rt_step.
apply Hxy.
apply IHclos_refl_trans_1n.
Qed.





