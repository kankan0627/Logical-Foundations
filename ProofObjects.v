Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. 
  apply ev_SS. 
  apply ev_0. 
Qed.

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)

Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8 := ev_SS 6 (ev_SS 4 (ev_SS 2 ((ev_SS 0 ev_0)))).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) => ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) := ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'' : forall n : nat, ev n -> ev (4 + n).

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.

Compute add1 2.

Module Props.

Module And.
Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.
End And.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
  intros P Q R [HP HQ] [HQ' HR].
  split.
  apply HP.
apply HR.
Defined.

Print conj_fact.

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].
Notation "P \/ Q" := (or P Q) : type_scope.

Definition inj_l : forall (P Q : Prop), P -> P \/ Q.
  intros P Q HP.
  apply or_introl.
  apply HP.
Show Proof.
  Defined.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
Qed.


Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.
End Or.

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P.
  intros P Q HPQ.
  destruct HPQ as [HP | HQ].
  right.
  apply HP.
  left.
  apply HQ.
  Show Proof.
  Defined.

Module Ex.

Inductive ex {X : Type} (P : X -> Prop) : Prop :=
  | ex_intro : forall x : X, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.

Check ex (fun n => ev n).

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => ev (S n)).
 exists 3.
 apply ev_SS. 
  apply ev_SS. 
  apply ev_0. 
Show Proof.
 Defined.

Inductive True : Prop :=
  | I : True.

Definition p_implies_true : forall P, P -> True.
  intros.
  apply I.
Show Proof.
 Defined.

Inductive False : Prop := .

Fail
  Definition contra : False :=
  0 = 1.

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

Definition ex_falso_quodlibet' : forall P, False -> P.
  intros.
  inversion H.
Show Proof.
Defined.

End Props.

Module EqualityPlayground.

Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity) : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].

Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq.
  destruct Heq.
  Fail reflexivity.
  apply eq_refl.
Qed.

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2.
intros X h1 h2 t1 t2 H T.
destruct H.
destruct T.
apply eq_refl.
Defined.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  intros X x y H HP HPx.
  destruct H.
  apply HPx.
  Show Proof.
Qed.

Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y.
  intros X x y H HP HPx.
  destruct H.
  apply HPx.
  Defined.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P: X -> Prop, P x -> P y) -> x == y.
Proof.
  intros X x y H.
  specialize H with (P := (fun y => x==y)).
  simpl in H.
  apply H.
  apply eq_refl.
Qed.

End EqualityPlayground.

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or_introl H => H
    end.

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

Definition and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
intros P Q R H.
destruct H as [HP [HQ HR]].
split.
split.
apply HP.
apply HQ.
apply HR.
Show Proof.
Defined.

Definition or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
intros P Q R.
split.
intros H.
destruct H.
split.
left.
apply H.
left.
apply H.
split.
destruct H.
right.
apply H.
destruct H.
right.
apply H0.
intros [[HP | HQ] [HP' | HR]].
left.
apply HP.
left.
apply HP.
left.
apply HP'.
right.
split.
apply HQ.
apply HR.
Defined.

Definition double_neg : forall P : Prop,
    P -> ~~P.
intros P HP con. 
unfold not in con.
apply con.
apply HP.
Defined.

Definition contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
intros P Q [HP HNP].
unfold not in HNP.
apply HNP in HP.
inversion HP.
Defined.


Definition de_morgan_not_or : forall P Q : Prop,
    ~ (P \/ Q) -> ~P /\ ~Q.
intros P Q.
intros contra.
unfold not in contra.
split.
unfold not.
intros HP.
apply contra.
left.
apply HP.
unfold not.
intros HQ.
apply contra.
right.
apply HQ.
Defined.


Definition curry : forall P Q R : Prop,
    ((P /\ Q) -> R) -> (P -> (Q -> R)).
intros P Q R H HP HQ.
apply H.
split.
apply HP.
apply HQ.
Defined.



Definition uncurry : forall P Q R : Prop,
    (P -> (Q -> R)) -> ((P /\ Q) -> R).
 intros P Q R H HAND.
 destruct HAND.
 apply H.
 apply H0.
  apply H1.
Defined.

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Theorem pe_implies_or_eq :
  propositional_extensionality -> forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  intros H P Q.
  apply H.
  split.
  intros G.
  apply or_commut.
  apply G.
  intros G.
  apply or_commut.
  apply G.
Qed.

Lemma pe_implies_true_eq :
  propositional_extensionality -> forall (P : Prop), P -> True = P.
Proof.
  intros Hpe P HP.
  apply Hpe.
  split.
  intros HT.
  apply HP.
  intros HP1.
  apply I.
Qed.

Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
 intros PE P pf1 pf2.
  assert (H: True = P). { apply (pe_implies_true_eq PE). apply pf1. }
  destruct H.
  destruct pf1.
  destruct pf2.
  reflexivity.
Qed.




















