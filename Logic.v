Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactic.

Check (forall n m: nat, n + m = m + n).
Check 2 = 2.
Check 3 = 3.
Check forall n: nat, n = 2.

Theorem plus_2_2_is_4:
  2 + 2 = 4.
Proof.
  reflexivity.
  Qed.

Definition plus_claim: Prop := 2 + 2 = 4.
Check plus_claim.

Theorem plus_claim_is_true:
  plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.

Compute is_three 2.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y: A, f x = f y -> x = y.

Lemma succ_inj: injective S.
Proof. 
  intros n m H.
  injection H as H1.
  apply H1.
  Qed.

Check @eq: forall A: Type, A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. 
  apply conj.
  - reflexivity.
  - reflexivity.
  Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  apply conj.
  induction n.
reflexivity.
discriminate H.
induction m.
reflexivity.
destruct n in H.
simpl in H.
rewrite -> H.
reflexivity.
discriminate H.
  Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity.
  Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity.
  Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn.
  rewrite Hm.
  reflexivity.
  Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn.
  reflexivity.
  Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.
  Qed.


Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q HPQ.
   destruct HPQ as [_ HQ].
  apply HQ.
  Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  apply HQ.
  apply HP. 
  Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ. 
  apply HR. 
  Qed.

Check and.

Lemma factor_is_0:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  rewrite -> Hn.
  simpl.
  reflexivity.
  rewrite -> Hm.
  rewrite -> mul_0_r.
  reflexivity.
  Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
  Qed.

Lemma zero_or_succ : 
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
  Qed.

Lemma mult_is_0 : 
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n'].
  intros m H.
  simpl in H.
  left.
  reflexivity.
  intros [|m'].
  intros H1.
  simpl in H1.
  rewrite -> mul_0_r in H1.
  right.
  reflexivity.
  intros H2.
  left.
  discriminate H2.
  Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
 intros P Q [HP | HQ].
 right.
 apply HP.
 left.
apply HQ.
  Qed.

Definition not (P:Prop) := P -> False.

Check not.

Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P constra.
  destruct constra.
  Qed.

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P contra.
  unfold not in contra.
  intros Q HP.
  apply contra in HP.
  destruct HP.
  Qed.

Notation "x <> y" := (~ (x = y)).

Theorem zero_not_one : 0 <> 1.

Proof.
  intros contra.
  discriminate contra.
  Qed.

Theorem not_False :
  ~ False.
Proof.
  intros contra.
  apply contra.
  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP HQ].
  unfold not in HQ.
  apply HQ in HP.
  destruct HP.
  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P HP.
  unfold not.
  intros H1.
  apply H1 in HP.
  apply HP.
  Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H N.
  unfold not.
  intros HP.
  unfold not in N. 
  apply N in H.
  destruct H.
  apply HP.
  Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
intros P.
unfold not.
intros H.
destruct H as [HP HQ].
apply HQ in HP.
destruct HP.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop),
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q contra.
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
  Qed.

Theorem not_true_is_false : forall b : bool,
  ~(b = true) -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  unfold not in H.
  apply ex_falso_quodlibet.
  apply H. 
  reflexivity.
  reflexivity.
  Qed.

Theorem not_true_is_false' : forall b : bool,
  ~(b = true) -> b = false.
Proof.
  intros [] H.
  unfold not in H.
  exfalso.
  apply H. 
  reflexivity.
  reflexivity.
  Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Definition disc_fn (n : nat) : Prop :=
  match n with 
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~(0 = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn 0).
  simpl. 
  apply I.
  rewrite H1 in H2. 
  simpl in H2. 
  apply H2.
  Qed.

Definition iff(P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)  (at level 95, no associativity) : type_scope.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  apply HBA.
  apply HAB.
  Qed.

Lemma not_true_iff_false : forall b,
  ~(b = true) <-> b = false.
Proof.
  intros b.
  split.
  apply not_true_is_false.
  intros H.
  rewrite H.
  intros H'.
  discriminate H'.
  Qed.

Lemma apply_iff_example1 :
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP.
  apply H.
  apply Hiff.
  apply HP.
  Qed.

Lemma apply_iff_example2 :
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ.
  apply H.
  apply Hiff.
  apply HQ.
  Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  intros [HP | [HQ HR]].
  split.
  left.
  apply HP.
  left.
  apply HP.
  split.
  right.
  apply HQ.
  right.
  apply HR.
  intros [[HP1 | HQ] [HP2 | HR]].
  left.
  apply HP1.
   left.
  apply HP1.
  left.
  apply HP2.
  right.
  split.
  apply HQ.
  apply HR.
  Qed.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros n m.
  split.
  intros H.
  apply mult_is_0 in H.
  apply H.
  intros G.
  destruct G as [GF | GR].
  rewrite GF.
  simpl.
  reflexivity.
  rewrite GR.
  apply mul_0_r.
  Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof. 
  intros P Q R.
  split.
  intros [HP | [HQ | HR]].
  left.
  left.
  apply HP.
  left.
  right.
  apply HQ.
  right.
  apply HR.
  intros [[HP | HQ] | HR].
  left.
  apply HP.
  right.
  left.
  apply HQ.
  right.
  right.
  apply HR.
  Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  split.
  intros H.
  apply mul_eq_0 in H. 
  destruct H.
  apply mul_eq_0 in H. 
  apply or_assoc.
  left.
  apply H.
  apply or_assoc.
  right.
  apply H.
  intros [HM | HP].
  rewrite -> HM.
  simpl.
  reflexivity.
  destruct HP.
  rewrite -> H.
  rewrite -> mul_0_r.
  simpl.
  reflexivity.
  rewrite -> H.
  rewrite -> mul_0_r.
  reflexivity.
  Qed.

Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even.
  exists 2.
  reflexivity.
  Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm. 
  Qed. 

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
 (forall x , P x) -> ~(exists x, ~ P x).
Proof.
  intros X P HP.
  unfold not.
  intros [x G].
  destruct G.
  apply HP.
  Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  intros [x [HP | HQ]].
  left.
  exists x.
  apply HP.
  right.
  exists x.
  apply HQ.
  intros [[x HP] | [x HQ]].
  exists x.
  left.
  apply HP.
  exists x.
  right.
  apply HQ.
  Qed.


Theorem leb_plus_exists : forall n m, 
    n <=? m = true -> exists x, m = n + x.
Proof.
induction n.
  intros m H.
   exists m.
  simpl.
   reflexivity. 
destruct m.
simpl.
discriminate.
simpl.
intros H.
apply IHn in H.
destruct H as [x0 H].
rewrite H.
exists x0. 
reflexivity.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  induction n.
  simpl.
reflexivity. 
  induction m.
 specialize IHn with (m := 0).
intros H.
simpl in H.
destruct H as [x0 H].
discriminate H.
simpl.
intros H.
specialize IHn with (m := m).
apply IHn.
destruct H as [x0 H].
apply S_injective in H.
exists x0.
apply H.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In x l'
   end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl.
  right.
  right.
  right.
  left. 
  reflexivity. 
  Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl. 
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
  Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
  + rewrite H. 
    left. 
    reflexivity.
  + right. 
    apply IHl'. 
    apply H.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
          In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  induction l as [|x' l' IHl']. 
  simpl. 
  split.
  intros [].
  intros H.
  destruct H as [x0 G2].
  destruct G2.
  apply H0.
  simpl.
  split.
  intros H.
  destruct H.
  exists x'.
  split.
  apply H.
  left.
  reflexivity.
  apply IHl' in H.
  destruct H as [x0 G2].
  exists x0.
  split.
  apply G2.
  right.
  apply G2.
  intros H.
  destruct H as [x0 [H0 [H1 | H2]]].
  left.
  rewrite H1.
  apply H0.
  right.
  apply IHl'.
  exists x0.
  split.
  apply H0.
  apply H2.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. 
  induction l as [|a' l' IH].
  simpl.
  split.
  intros H.
  right.
  apply H.
  intros [[] | H].
  apply H.
  split.
  intros H.
  simpl in H.
  simpl.
  apply or_assoc.
  specialize IH with (l' := l'0).
  specialize IH with (a := a).
  destruct IH.
  destruct H.
  left.
  apply H.
  right.
  apply H0.
  apply H.
  intros H.
  simpl.
  simpl in H.
  apply or_assoc in H.
  destruct H.
  left.
  apply H.
  right.
  apply IH in H.
  apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
    match l with
    | [] => True
    | x' :: l' => P x' /\ All P l'
   end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  split.
  intros H.
  induction l as [|x' l' IH].
  simpl.
  apply I.
  simpl.
  split.
  specialize H with (x := x').
  apply H.
  simpl.
  left.
  reflexivity.
  apply IH.
  intros x H1.
  apply H.
  simpl.
  right.
  apply H1.
  induction l as [|x' l' IH].
  simpl.
  intros H2.
  intros x [].
  simpl.
  intros [G1 G2].
  intros x [Q1 | Q2].
  rewrite Q1 in G1.
  apply G1.
  apply IH.
  apply G2. 
  apply Q2.
Qed. 

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
 fun (n : nat) => if (odd n) then Podd n else Peven n.

Theorem combine_odd_even_intro :
 forall  (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven.
  induction n as [|n' Hn].
  intros G1 G2.
  unfold combine_odd_even.
  simpl.
  apply G2.
  reflexivity.
  intros G3 G4.
  unfold combine_odd_even.
  destruct (odd (S n')) eqn:Hodd.
  apply G3.
  reflexivity.
  apply G4.
  reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven.
  induction n as [|n' Hn].
  intros H H'.
  unfold combine_odd_even in H.
  rewrite H' in H.
  apply H.
  intros G G'.
  unfold combine_odd_even in G.
  rewrite G' in G.
  apply G.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven.
  induction n as [|n' Hn].
  intros H H'.
  unfold combine_odd_even in H.
  rewrite H' in H.
  apply H.
  intros G G'.
  unfold combine_odd_even in G.
  rewrite G' in G.
  apply G.
Qed.

Check plus.
Check @rev.
Check add_comm.

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> ~(l = []).
Proof.
  intros A x.
  induction l as [|x' l' IH].
  simpl.
  intros [].
  unfold not in IH.
  unfold not.
  intros H H1.
  rewrite H1 in H.
  simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> ~(l = []).
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> ~(l = []).
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed. 

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> ~(l = []).
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> ~(l = []).
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> ~(l = []).
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm Hn]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example even_42_bool : even 42 = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example even_42_prop : Even 42.
Proof.
  exists 21.
  simpl.
  reflexivity.
Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  induction k.
  simpl.
  reflexivity.
  simpl.
  apply IHk.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  induction n.
  simpl.
  exists 0.
  simpl.
  reflexivity.
  destruct IHn as [k0 H].
  destruct even in H.
  assert (G: even (S n) = false).
  rewrite -> even_S.
  rewrite -> H.
  rewrite -> even_double.
  simpl.
  reflexivity.
  rewrite G.
  exists k0.
  rewrite <- H.
  reflexivity.
  rewrite -> H.
  simpl.
  rewrite -> even_double.
  simpl.
  exists (S k0).
  simpl.
  reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
split.
intros H.
unfold Even.
specialize even_double_conv with (n := n).
rewrite -> H.
intros [k0 H'].
exists k0.
apply H'.
intros [x G].
rewrite G.
apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
   n1 =? n2 = true <-> n1 = n2.
Proof.
  split.
  intros H.
  apply eqb_true in H.
  apply H.
  intros H.
induction n1 as [| n' IHn'].
destruct n2 as [| m'] eqn:E.
reflexivity.
discriminate H.
rewrite H.
rewrite eqb_refl.
reflexivity.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

Example even_1000 : Even 1000.
Proof.
  unfold Even.
  exists 500.
  simpl.
  reflexivity.
Qed.

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

Example not_even_1001' : ~(Even 1001).
Proof.
  intros contra.
  apply even_bool_prop in contra.
  discriminate contra.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p.
  intros H.
  apply eqb_eq in H.
  rewrite H.
  rewrite eqb_refl.
  reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2:bool,
  andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2.
  split.
  intros H.
  split.
  specialize andb_commutative with (b := b1).
  intros G.
specialize G with (c := b2).
  rewrite G in H.
specialize andb_true_elim2 with (b := b2).
  intros Q.
specialize Q with (c := b1).
apply Q.
apply H.
specialize andb_true_elim2 with (b := b1).
  intros Q.
specialize Q with (c := b2).
apply Q.
apply H.
intros [H1 H2].
rewrite H1.
rewrite H2.
simpl.
  reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2.
  split.
  intros H.
  destruct b1.
  left.
  reflexivity.
  right.
  destruct b2.
  reflexivity.
  simpl in H.
  discriminate H.
  intros [H1 | H2].
  rewrite H1.
  simpl.
  reflexivity.
  rewrite H2.
  destruct b1.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> ~(x = y).
Proof.
  intros x y.
  split.
  intros H G.
  specialize not_true_iff_false with (b := (x =? y)).
  intros Q.
  apply Q in H.
  unfold not in H.
  apply H.
  rewrite G.
  rewrite eqb_refl.
  reflexivity.
  intros contra.
  unfold not in contra.
  specialize not_true_iff_false with (b := (x =? y)).
  intros Q.
  apply Q.
  unfold not.
  intros H.
  apply contra.
  apply eqb_true.
  apply H.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1 with
 |nil => 
    match l2 with
     |nil => true
     |h2 :: t2 => false
    end
 |h1 :: t1 =>
    match l2 with
     |nil => false
     |h2 :: t2 => 
        if eqb h1 h2 then eqb_list eqb t1 t2
        else false
    end
end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
induction l1 as [|x1 IH1].
induction l2 as [|x2 IH2].
split.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
split.
discriminate.
intros G.
discriminate G.
induction l2 as [|x2 IH2].
split.
simpl.
discriminate.
discriminate.
simpl.
destruct eqb eqn:He.
split.
intros G.
specialize IHIH1 with (l2 := IH2).
apply IHIH1 in G.
apply H in He.
rewrite -> He.
rewrite -> G.
reflexivity. 
intros G.
specialize IHIH1 with (l2 := IH2).
apply IHIH1.
injection G as Hmn.
apply H0.
split.
discriminate.
intros G.
injection G as Hmn.
apply H in Hmn.
rewrite -> He in Hmn. 
discriminate Hmn.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
 match l with 
   |nil => true
   |h :: t => 
           if (test h) then forallb test t
           else false
 end.


Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  induction l as [|x IH].
  simpl.
  split.
  intros H.
  apply I.
  reflexivity.
  simpl.
  split.
  intros H.
  destruct test eqn:Gn in H.
  split.
  apply Gn.
  apply IHIH.
  apply H.
  discriminate H.
  intros [H1 H2].
  rewrite -> H1.
  apply IHIH.
  apply H2.
Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof.
  simpl.
reflexivity.
Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
               (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
 (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma rev_append_nil : forall X (l1 l2 : list X), rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l1 l2.
  generalize dependent l2.
  induction l1.
  - reflexivity.
  - intros l2.
    simpl.
    rewrite -> IHl1. 
    rewrite -> (IHl1 [x]). 
    rewrite <- app_assoc. 
    reflexivity.
Qed.


Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
 intros X.
  apply functional_extensionality.
  intros l.
  induction l.
  + reflexivity.
  + simpl. rewrite <- IHl. unfold tr_rev. simpl. apply rev_append_nil.
Qed.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  left. 
  apply H. reflexivity.
  right.
  intros contra. 
  apply H in contra. 
  discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ ~(n = m).
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  split.
  apply eqb_eq.
  apply eqb_eq.
Qed.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Axiom excluded_middle_extensionality : forall P : Prop, P \/ ~ P.

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
 intros P contra.
 apply contra.
 apply excluded_middle_extensionality.
Qed.

Theorem not_exists_dist :
  excluded_middle -> forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
 intros H X P G x.
 unfold excluded_middle in H.
 unfold not in G.
 specialize H with (P := P x).
destruct H as [HY | HN].
apply HY.
unfold not in HN.
destruct G.
exists x.
apply HN.
Qed.




