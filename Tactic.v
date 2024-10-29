Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality". 
From LF Require Export Poly.

Theorem silly1 : forall (n m : nat),
    n = m -> n = m.
Proof.
   intros n m eq.
   apply eq. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m -> (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
  Qed.

Theorem silly2a : forall (n m : nat),
  (n , n) = (m , m) ->
  (forall (q r : nat), (q , q) = (r , r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
  Qed.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even(S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p eq1 eq2 eq3.
  apply eq2.
  apply eq1.
  apply eq3.
  Qed.

Theorem silly3 : forall (n m : nat),
  n = m -> m = n.
Proof.
  intros n m H.
  symmetry. 
  apply H.
  Qed.

Search rev.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  symmetry. 
  rewrite -> H.
  apply rev_involutive.
  Qed.

Example trans_eq_example : forall (a b c d e f : nat),
   [a;b] = [c;d] -> 
   [c;d] = [e;f] -> 
   [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity. Qed.


Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  apply eq2.
  apply eq1.
  Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2 : n = pred (S n)).
  reflexivity.
  rewrite H2.
  rewrite H1.
  simpl. reflexivity.
  Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hmn.
  apply Hmn.
  Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
  Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
intros X x y z l j H1 H2.
injection H1 as L1 L2.
assert (H3 : y :: l = z :: l).
rewrite L2.
rewrite H2.
reflexivity.
injection H3 as L3.
rewrite L1.
rewrite L3.
reflexivity.
 Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
 intros n m contra.
 discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Example discriminate_ex3:
  forall (X:Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     x = z.
 Proof.
  intros X x y z l j contra.
discriminate contra. Qed.

Theorem eqb_0_1 : forall n,
  0 =? n = true -> n = 0.
Proof.
 intros n.
destruct n as [| n'] eqn:E.
intros H. reflexivity.
intros H. discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
intros A B f x y H.
rewrite H.
reflexivity.
 Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. 
intros n m H.
rewrite H.
reflexivity.
 Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
intros n m b.
simpl.
intros H.
rewrite H.
reflexivity.
 Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H. Qed.


Theorem specialize_example: forall n,
     (forall m, m * n = 0) ->  n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  simpl in H.
  rewrite add_comm in H.
  simpl in H.
  apply H. 
  Qed.

Example trans_eq_example''' : forall (a b c d e f : nat),
          [a;b] = [c;d] ->
          [c;d] = [e;f] ->
          [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (m := [c;d]) as H.
  apply H.
  apply eq1.
  apply eq2.
  Qed.

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
- (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.
  Abort.


Theorem double_injective : forall n m, 
  double n = double m ->
  n = m.
Proof. 
intros n. induction n as [| n' IHn'].
- (* n = O *)  simpl. intros m eq. destruct m as [| m'] eqn:E.
+ (* m = O *)  reflexivity.
+ (* m = S m' *) discriminate eq.
- (* n = S n' *) intros m eq.
destruct m as [| m'] eqn:E.
+ (* m = O *) discriminate eq.
+ (* m = S m' *) f_equal.
apply IHn'. 
simpl in eq. 
injection eq as goal. 
apply goal. Qed.


Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
intros n. induction n as [| n' IHn'].
intros m eq. destruct m as [| m'] eqn:E.
reflexivity.
discriminate eq.
intros m eq.
destruct m as [| m'] eqn:E.
discriminate eq.
simpl in eq.
apply IHn' in eq.
rewrite eq.
reflexivity.
Qed.

Search double.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
intros n m H.
rewrite <- double_plus in H.
apply silly3 in H.
rewrite <- double_plus in H.
apply double_injective in H.
apply silly3 in H.
apply H.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction m as [|m' IHm'].
- simpl. intros eq. destruct n as [|n'] eqn : E.
+ reflexivity.
+ discriminate eq.
- intros eq. destruct n as [|n'] eqn : E.
+ discriminate eq.
+ f_equal.
Abort.

Theorem _injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
 (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *) 
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
 intros n X l.
 generalize dependent n.
 induction l as [| l' IHl'].
 simpl.
 intros n eq.
 reflexivity.
 intros n eq. 
 destruct n as [| n'] eqn:E.
 discriminate eq.
 apply IHIHl'.
 simpl in eq.
 injection eq as goal.
 apply goal.
 Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
 intros n m.
 unfold square.
 rewrite mult_assoc.
 assert (H : n * m * n = n * n * m).
 { rewrite mul_comm. apply mult_assoc. }
 rewrite H. rewrite mult_assoc. reflexivity.
 Qed.

Definition foo (x : nat) := 5.

Fact silly_fact_l : forall m, foo m + 1 = foo (m + 1) + 1.
 Proof.
  intros m.
  simpl.
reflexivity.
Qed.

Definition bar x := 
  match x with
   | O => 5
   | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
 intros m.
 simpl. 
Abort. 

Fact silly_fact_2 : forall m, bar m + 1 = bar (m +1) + 1.
Proof. 
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
  Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m +1) + 1.
Proof. 
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
  Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem siilyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn:E2.
  + reflexivity.
  + reflexivity.
  Qed.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([] , [])
  | (x , y) :: t =>
          match split t with
          (lx , ly) => (x :: lx , y :: ly)
          end
  end.


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1,l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  - intros l1 l2 H. 
    simpl in H. 
    injection H as H. 
    rewrite <- H. 
    rewrite <- H0. 
    reflexivity.
  - destruct x as (x,y).
    destruct l1 as [| x'].
    + intros l2 H. 
      simpl in H. 
      destruct (split l) in H. 
      discriminate H.
    + destruct l2 as [| y'].
      * intros H. 
        simpl in H. 
        destruct (split l) in H. 
        discriminate H.
      * intros H.
        simpl.
        assert (G: split l = (l1, l2)). 
        {
          simpl in H. 
          destruct (split l).
          injection H as H. 
          rewrite -> H0. 
          rewrite -> H2. 
          reflexivity.
        }
        apply IHl in G.
        simpl in H. 
        destruct (split l) in H. 
        injection H as H.
        rewrite -> G. 
        rewrite <- H. 
        rewrite <- H1. 
        reflexivity.
        Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (n =? 3) eqn : Heqe3.
  apply eqb_true in Heqe3.
  rewrite -> Heqe3.
  reflexivity.
  destruct (n =? 5) eqn : Heqe5.
  apply eqb_true in Heqe5.
  rewrite -> Heqe5.
  reflexivity.
  discriminate eq.
  Qed.

Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  induction b.
  destruct (f true) eqn:Ht.
  rewrite -> Ht.
  rewrite -> Ht.
  reflexivity.
  destruct (f false) eqn:Hf.
  rewrite -> Ht.
  reflexivity.
  rewrite -> Hf.
  reflexivity.
  destruct (f false) eqn:Hff.
  destruct (f true) eqn:Hft.
  rewrite -> Hft.
  reflexivity.
  rewrite -> Hff.
  reflexivity.
  rewrite -> Hff.
  rewrite -> Hff.
  reflexivity.
  Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
induction n.
intros m.
induction m.
simpl.
reflexivity.
rewrite -> S_neqb_0.
rewrite -> zero_neqb_S.
reflexivity.
intros m.
induction m.
rewrite -> S_neqb_0.
rewrite -> zero_neqb_S.
reflexivity.
destruct (S n =? S m) eqn:Hmn.
apply eqb_true in Hmn.
rewrite -> Hmn.
symmetry. 
rewrite -> eqb_refl.
reflexivity.
destruct (S m =? S n) eqn:H1.
apply eqb_true in H1.
rewrite -> H1 in Hmn.
rewrite -> eqb_refl in Hmn.
discriminate Hmn.
reflexivity.
 Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p eqA eqB. 
  apply eqb_true in eqA.
  apply eqb_true in eqB.
  rewrite -> eqB in eqA.
  rewrite eqA.
  simpl.
  rewrite -> eqb_refl.
  reflexivity.
 Qed.

Search filter.

Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros X.
  induction l.
  intros lf eq.
  simpl in eq.
  discriminate eq.
  intros lf eq.
  simpl in eq.
  destruct (test x0) eqn:Hd.
  injection eq.
  intros H1 H2.
  rewrite <- H2. 
  rewrite -> Hd.
  reflexivity.
  apply IHl in eq.
  rewrite -> eq.
  reflexivity.
  Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with 
   |nil => true
   |h :: t => 
           if (test h) then forallb test t
           else false
 end.

Compute forallb odd [1;3;5;7;9].

Compute forallb negb [false;false].

Compute forallb even [0;2;4;5].

Compute forallb (eqb 5) [].

Compute forallb negb [false;false].

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
   |nil => false
   |h :: t => 
           if (test h) then true
           else existsb test t
  end.
 
Compute existsb (eqb 5) [0;2;3;6].

Compute existsb (andb true) [true;true;false].

Compute existsb odd [1;0;0;0;0;3].

Compute existsb even [].

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
   if (forallb (fun x => negb(test x)) l) then false
   else true.
 
Compute existsb' odd [1;0;0;0;0;3].

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. 
intros X.
induction l.
reflexivity.
simpl.
destruct (test x) eqn:Ex.
unfold existsb'.
destruct forallb eqn:Ef.
unfold forallb in Ef.
rewrite -> Ex in Ef.
simpl in Ef.
discriminate Ef.
  reflexivity.
unfold existsb'.
unfold forallb.
rewrite -> Ex.
simpl.
destruct forallb eqn:Ell.
unfold existsb' in IHl.
rewrite -> Ell in IHl.
rewrite -> IHl.
reflexivity.
unfold existsb' in IHl.
rewrite -> Ell in IHl.
rewrite -> IHl.
reflexivity.
  Qed.


















