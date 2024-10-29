Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export ProofObjects.

Check nat_ind.

Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity. 
Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  reflexivity. simpl.
  intros n H.  
  rewrite -> H.
  reflexivity.
Qed.

Inductive time : Type :=
  | day
  | night.

Check time_ind. 

Inductive rgb : Type :=
  | red
  | green
  | blue.

Check rgb_ind.

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).

Check natlist'_ind.

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

Definition booltree_property_type : Type := booltree -> Prop.

Definition base_case (P : booltree_property_type) : Prop := P bt_empty.

Definition leaf_case (P : booltree_property_type) : Prop := forall b : bool, P (bt_leaf b).

Definition branch_case (P : booltree_property_type) : Prop := forall b : bool, P (bt_leaf b) -> forall t1 t2: booltree, P (bt_branch b t1 t2).
  

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.
  unfold booltree_ind_type.
  intros P HBP HLP HRP b.
  induction b.
  apply HBP.
  apply HLP.
  apply HRP.
  apply HLP.
Qed. 

Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy).

Check Toy_ind. 

Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof.
  exists con1. 
  exists con2.
  intros P Hb HnT t.
  induction t.
  apply Hb.
  apply HnT.
  apply IHt.
Qed.

Inductive list (X:Type) : Type :=
   | nil : list X
   | cons : X -> list X -> list X.

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.
(* tree_ind:
  forall (X : Type) (P : tree X -> Prop),
           (forall x : X, P (leaf x)) ->
           (forall t1 : tree X, P t1 -> forall t2 : tree X, P t2 -> P (node t1 t2) ->
            forall t : tree X, P t *)

(*foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2 *)

Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.

Check foo'_ind.
(* 
foo'_ind:
   forall (X:Type) (P: foo' X -> Prop),
      (forall (l: list X) (f: foo' X), 
           P f -> P (C1 X l f) ) ->
              P (C2 X) ->
   forall f: foo' X, P f
*)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Theorem mul_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* Note the proof state at this point! *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary n, m, and
     p..." *)
  intros n m p.
  (* ...We now use the induction tactic to prove P n (that
     is, n + (m + p) = (n + m) + p) for _all_ n,
     and hence also for the particular n that is in the context
     at the moment. *)
  induction n as [| n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem add_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite -> add_0_r. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Theorem add_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  (* Let's do induction on m this time, instead of n... *)
  induction m as [| m']. (* n is already introduced into the context *)
  - (* m = O *) simpl. rewrite -> add_0_r. reflexivity.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Print ev.
(* ===>

  Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)))

*)
Check ev_ind.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.

Inductive le1 : nat -> nat -> Prop :=
  | le1_n : forall n, le1 n n
  | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).
Notation "m <=1 n" := (le1 m n) (at level 70).

Inductive le2 (n:nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).
Notation "m <=2 n" := (le2 m n) (at level 70).

Check le1_ind.
Check le2_ind.

Print nat_ind.

Lemma even_ev : forall n: nat, even n = true -> ev n.
Proof.
  induction n; intros.
  - apply ev_0.
  - destruct n.
    + simpl in H. inversion H.
    + simpl in H.
      apply ev_SS.
Abort.


Lemma even_ev' : forall n : nat, (even n = true -> ev n) /\ (even (S n) = true -> ev (S n)).
Proof.
  induction n.
  split.
   intros H.
  apply ev_0.
  simpl.
  intros H.
  inversion H.
split.
   intros H.
  destruct IHn.
apply H1 in H.
apply H.
intros H.
apply ev_SS.
simpl in H.
destruct IHn.
apply H0 in H.
apply H.
Qed.

Definition nat_ind2 :
  forall (P : nat -> Prop),
  P 0 ->
  P 1 ->
  (forall n : nat, P n -> P (S(S n))) ->
  forall n : nat , P n :=
    fun P => fun P0 => fun P1 => fun PSS =>
      fix f (n:nat) := match n with
                         0 => P0
                       | 1 => P1
                       | S (S n') => PSS n' (f n')
                       end.

Lemma even_ev : forall n, even n = true -> ev n.
Proof.
  intros.
  induction n as [ | |n'] using nat_ind2.
  - apply ev_0.
  - simpl in H.
    inversion H.
  - simpl in H.
    apply ev_SS.
    apply IHn'.
    apply H.
Qed.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Inductive t_tree (X : Type) : Type :=
| t_leaf
| t_branch : (t_tree X * X * t_tree X) -> t_tree X.

Arguments t_leaf {X}.
Arguments t_branch {X}.

Check t_tree_ind.

Fixpoint reflect {X : Type} (t : t_tree X) : t_tree X :=
  match t with
  | t_leaf => t_leaf
  | t_branch (l, v, r) => t_branch (reflect r, v, reflect l)
  end.

Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof.
  intros X t. induction t.
  - reflexivity.
  - destruct p as [[l v] r]. simpl. Abort.

Definition better_t_tree_ind_type : Prop
  := forall (X : Type) (P : t_tree X -> Prop), P (t_leaf) -> 
    (forall v : X, forall l : t_tree X, P l -> forall r : t_tree X, P r -> P (t_branch (l, v, r))) -> 
    forall (t : t_tree X), P t.



Definition better_t_tree_ind : better_t_tree_ind_type
  := fun X P Pleaf Pbranch => fix f t :=
    match t with
    | t_leaf => Pleaf
    | t_branch (l, v, r) => Pbranch v l (f l) r (f r)
    end.


Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof.
  intros X.
  apply better_t_tree_ind.
  - reflexivity.
  - intros v l IHl r IHr. simpl. rewrite IHl. rewrite IHr. reflexivity.
Qed.
