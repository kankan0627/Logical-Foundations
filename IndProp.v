Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.


Fixpoint div2 (n : nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.

Compute f 3.

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more (n : nat) : Collatz_holds_for (f n) -> Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_done. Qed.

Module LePlayground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

End LePlayground.

Module LePlayground1.

Reserved Notation "n <= m" (at level 70).

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : n <= n
  | le_S (n m : nat) : n <= m -> n <= (S m)
 
  where "n <= m" := (le n m).

End LePlayground1.

Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
| po_SC : parent_of Sage Cleo
| po_SR : parent_of Sage Ridley
| po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of1 : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of. 
  apply t_trans with Cleo.
  - apply t_step. 
    apply po_SC.
  - apply t_step. 
    apply po_CM. 
    Qed.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Example Perm3_example1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap23. Qed.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn. apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
induction n.
simpl.
apply ev_0.
rewrite -> double_incr.
apply ev_SS.
apply IHn.
Qed.

Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [ | n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
intros n H. apply ev_inversion in H. destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E' Heq].
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H. 
  destruct H.
discriminate H.
destruct H as [m [Hm Hn]].
discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
intros n H. inversion H. inversion H1.
apply H3.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
inversion H. 
inversion H1. 
inversion H3. 
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  unfold Even. 
  intros n E. 
  inversion E as [EQ' | n' E' EQ'].
  exists 0. 
  reflexivity.
  assert (H: (exists k', n' = double k')
         -> (exists n0, S (S n') = double n0)).
  {intros [k' EQ'']. 
  exists (S k'). 
  simpl.
  rewrite <- EQ''. 
  reflexivity. }
  apply H.
  generalize dependent E'.
Abort.

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  unfold Even.
  exists 0.
  reflexivity.
  unfold Even in IH.
  destruct IH as [k Hk].
  rewrite Hk.
  unfold Even. 
  exists (S k). 
  simpl. 
  reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. 
  split.
  apply ev_Even.
  unfold Even. 
  intros [k Hk]. 
  rewrite Hk. 
  apply ev_double.
Qed.


Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m E H.
  induction E as [|n' E' IE].
  simpl.
  apply H.
  induction H as [|m' H' IH].
  rewrite -> add_0_r.
  apply ev_Even_iff.
  unfold Even.
  apply ev_Even_iff in E'.
  unfold Even in E'.
  destruct E' as [k Hk].
  exists (S k).
  simpl.
  rewrite <- Hk.
  reflexivity.
  apply ev_Even_iff.
  unfold Even.
  apply ev_Even_iff in IE.
  unfold Even in IE.
  destruct IE as [k Hk].
  exists (S k).
  simpl.
  rewrite <- Hk.
  reflexivity.
Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 intros n.
 split.
 intros H.
 induction H.
 apply ev_0.
 apply ev_Even_iff.
 unfold Even.
 exists 1.
 reflexivity.
 apply ev_sum.
 apply IHev'1.
 apply IHev'2.
 intros G.
 induction G as [|n' G' IG].
 apply ev'_0.
 assert (Q : S (S n') = n' + 2).
 rewrite <- plus_n_Sm.
 rewrite <- plus_n_Sm.
 rewrite -> add_0_r.
 reflexivity.
 rewrite Q.
 apply (ev'_sum n' 2).
 apply IG.
 apply ev'_2.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m H G.
  induction G as [|n' G' IG].
  simpl in H.
  apply H.
  simpl in H.
  specialize evSS_ev with (n := n' + m).
  intros Q.
  apply Q in H.
  apply IG in H.
  apply H.
Qed.

Theorem ev_plus_aux: forall n m p,
  ev (n+m) -> ev (n+p) -> ev ((n+m) + (n+p)).
Proof.
  intros n m p H G.
specialize ev_sum with (n := n + m).
  intros Q.
specialize Q with (m := n + p).
apply Q in H.
apply H.
apply G.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p H G.
specialize ev_plus_aux with (n := n).
  intros Q.
 specialize Q with (m := m).
specialize Q with (p := p).
apply Q in H.
rewrite -> add_shuffle3' in H.
assert (P : n + m + p = n + (m + p)).
rewrite -> add_assoc.
reflexivity.
assert (A : n + (m + p) = (m + p) + n).
rewrite -> add_comm.
reflexivity.
rewrite -> P in H.
rewrite -> A in H.
rewrite -> add_shuffle3 in H.
rewrite <- double_plus in H.
rewrite -> add_comm in H.
specialize ev_ev__ev with (n := double n).
intros B. 
specialize B with (m := m + p).
apply B in H.
apply H.
specialize ev_double with (n := n).
intros L.
apply L.
apply G.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
Notation "n <= m" := (le n m).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2. Qed.

Definition lt (n m : nat) := le (S n) m.
Notation "n < m" := (lt n m).

End Playground.

Inductive total_relation : nat -> nat -> Prop :=
  | total_re (n m : nat) : total_relation n m.
  

Theorem total_relation_is_total : forall n m, total_relation n m.
  Proof.
  intros n m.
  apply total_re.
Qed.

Inductive empty_relation : nat -> nat -> Prop := .

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
Proof.
   intros n m H.
   inversion H.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H G.
  destruct H.
  apply G.
  induction G.
  apply le_S.
  apply H.
  apply le_S.
  apply IHG.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  apply le_n.
  apply le_S.
  apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H.
  apply le_n.
  apply le_S.
  apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  induction n.
  apply O_le_n.
  inversion H. 
  apply le_n.
  assert (G: S n <= S (S n)).
  apply le_S.
  apply le_n.
  specialize le_trans with (n := S (S n)).
  intros Q.
  specialize Q with (m := S n).
  specialize Q with (o := m).
  apply Q in G.
  apply G.
  apply H1.
Qed.


Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
intros n m.
destruct m.
right.
apply O_le_n.
induction n.
+ left. apply n_le_m__Sn_le_Sm. apply O_le_n.
 + destruct IHn.
      * destruct H.
        right. apply le_n.
        left. apply n_le_m__Sn_le_Sm. apply H.
      * right. apply le_S. apply H.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  destruct a.
  simpl.
apply O_le_n.
induction b.
rewrite add_0_r.
apply le_n.
rewrite add_comm in IHb.
rewrite <- plus_n_Sm in IHb.
simpl.
apply le_S.
rewrite <- plus_n_Sm.
rewrite add_comm.
apply IHb.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
 intros n1 n2 m H.
 split.
 destruct n1.
apply O_le_n.
assert (G: S n1 <= S n1 + n2).
apply le_plus_l.
specialize le_trans with (m := S n1).
intros Q.
specialize Q with (n := S n1 + n2).
specialize Q with (o := m).
apply Q in G.
apply G.
apply H.
destruct n2.
apply O_le_n.
rewrite add_comm in H.
assert (G: S n2 <= S n2 + n1).
apply le_plus_l.
specialize le_trans with (m := S n2).
intros Q.
specialize Q with (n := S n2 + n1).
specialize Q with (o := m).
apply Q in G.
apply G.
apply H.
Qed.


Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
induction n.
intros m p q H.
simpl in H.
left.
apply O_le_n.
induction p.
intros q H.
right.
rewrite plus_O_n in H.
apply plus_le in H.
destruct H as [H1 H2].
apply H2.
intros q.
intros H.
simpl in H.
apply Sn_le_Sm__n_le_m in H.
apply IHn in H.
destruct H.
left.
apply n_le_m__Sn_le_Sm.
apply H.
right.
apply H.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
 induction n.
 intros m p H.
 rewrite add_0_r.
 apply le_plus_l.
induction m.
intros p H.
inversion H.
intros p H.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
apply n_le_m__Sn_le_Sm.
apply Sn_le_Sm__n_le_m in H.
specialize IHn with (p := p).
apply IHn in H.
apply H.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p H.
  rewrite add_comm.
  assert (R: m + p = p + m).
  rewrite add_comm.
  reflexivity.
  rewrite R.
  specialize plus_le_compat_l with (p := p).
  intros Q.
  apply Q in H.
  apply H.
Qed.


Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  induction n.
  intros m p H.
apply O_le_n.
  induction m.
intros p H.
inversion H.
intros p H.
rewrite add_comm.
rewrite <- plus_n_Sm.
apply n_le_m__Sn_le_Sm.
rewrite add_comm.
apply IHn.
apply Sn_le_Sm__n_le_m in H.
apply H.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
induction n.
intros m H.
apply O_le_n.
induction m.
intros H.
inversion H.
intros H.
apply Sn_le_Sm__n_le_m in H.
apply le_S.
apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
induction n1.
intros n2 m H.
simpl in H.
induction m.
inversion H.
split.
apply n_le_m__Sn_le_Sm.
apply O_le_n.
apply H.
intros n2 m H.
induction m.
inversion H.
split.
apply n_le_m__Sn_le_Sm.
apply Sn_le_Sm__n_le_m in H.
apply plus_le in H.
destruct H as [H1 H2].
apply H1.
apply n_le_m__Sn_le_Sm.
apply Sn_le_Sm__n_le_m in H.
apply plus_le in H.
destruct H as [H1 H2].
apply H2.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
 induction n.
 intros m H.
 apply O_le_n.
induction m.
intros H.
inversion H.
intros H.
simpl in H.
apply IHn in H.
apply n_le_m__Sn_le_Sm.
apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
induction n.
intros m H.
simpl.
reflexivity.
intros m H.
induction m.
inversion H.
simpl.
apply IHn.
apply Sn_le_Sm__n_le_m.
apply H.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <->  n <= m.
Proof.
induction n.
split.
intros H.
 apply O_le_n.
simpl.
reflexivity.
split.
intros H.
apply leb_complete in H.
apply H.
intros H.
apply leb_correct  in H.
apply H.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
induction n.
simpl.
reflexivity.
induction m.
intros o H G.
inversion H.
intros o H G.
simpl in H.
induction o.
inversion G.
simpl.
specialize IHn with (m := m).
specialize IHn with (o := o).
apply IHn in H.
apply H.
simpl in G.
apply G.
Qed.


Module R.


Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R (S m) n (S o)
  | c3 m n o (H : R m n o ) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o ) : R n m o.

Example R_test : R 1 1 2.
Proof.
apply c2.
apply c3.
apply c1.
Qed.

Definition fR : nat -> nat -> nat := plus.

Lemma R_aux_fR : forall m n o, fR m n = o -> R m n o.
Proof.
  induction m.
  induction n.
  intros o H.
  simpl in H.
  rewrite <- H.
  apply c1.
  intros o H.
  simpl in H.
  rewrite <- H.
 apply c3.
  specialize IHn with (o := n).
 apply IHn.
 simpl.
 reflexivity.
 induction n.
  intros o H.
  rewrite add_0_r in H.
 rewrite <- H.
apply c2.
 specialize IHm with (o := m).
 specialize IHm with (n := 0).
apply IHm.
 rewrite add_0_r.
 reflexivity.
induction o.
intros H.
inversion H.
intros H.
unfold fR in H.
rewrite <- plus_n_Sm in H.
apply S_injective' in H.
apply c3.
apply IHn.
apply H.
Qed.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
intros m n o.
split.
intros H.
induction H.
reflexivity.
simpl.
apply eq_implies_succ_equal.
apply IHR.
rewrite add_comm.
simpl.
apply eq_implies_succ_equal.
rewrite add_comm in IHR.
apply IHR.
simpl in IHR.
apply S_injective in IHR.
rewrite add_comm in IHR.
simpl in IHR.
apply S_injective in IHR.
rewrite add_comm in IHR.
apply IHR.
rewrite add_comm in IHR.
apply IHR.
apply R_aux_fR.
Qed.
End R.


Inductive subseq : list nat -> list nat -> Prop :=
  | subseq0 l : subseq [] l
  | subseq1 x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | subseq2 x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2).
                              
Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  induction l.
  apply subseq0.
  apply subseq1.
  apply IHl.
  Qed.


Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
 intros.
  induction H as [| x l1 l2 H IH | x l1 l2 H IH].
  - apply subseq0.
  - simpl. apply (subseq1 x l1 (l2 ++ l3) IH).
  - simpl. apply (subseq2 x l1 (l2 ++ l3) IH).
Qed.



Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 H12 H23.
  generalize dependent l1.
  induction H23 as [| x l2 l3 H23 IH | x l2 l3 H23 IH].
  - intros.
    assert (l1 = []) as Hl1. inversion H12. reflexivity.
    rewrite Hl1. apply subseq0.
  - intros. inversion H12 as [| x' l1' l2' H12' | x' l1' l2' H12'].
    + apply subseq0.
    + apply (subseq1 x l1' l3 (IH l1' H12')).
    + apply (subseq2 x l1 l3 (IH l1 H12')).
  - intros. apply (subseq2 x l1 l3 (IH l1 H12)).
Qed.

Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.

Example R_provability_A : R 2 [1;0].
Proof.
  apply c2.
  apply c2.
  apply c1.
Qed.



Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
 apply MChar.
 Qed.


Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  assert (H:[1;2]=[1]++[2]).
 reflexivity.
rewrite H.
  apply MApp.
apply MChar.
apply MChar.
 Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros constra.
  inversion constra.
   Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl.
  assert (H:[1;2;3]=[1]++[2;3]).
  reflexivity.
  rewrite H.
  apply MApp.
  apply MChar.
  assert (G:[2;3]=[2]++[3]).
  reflexivity.
  rewrite G.
  apply MApp.
  apply MChar.
  assert (Q:[3]=[3]++[]).
  reflexivity.
  rewrite Q.
  apply MApp.
  apply MChar.
  apply MEmpty.
 Qed.

Lemma MStar1 :
  forall T s (re : reg_exp T),
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  induction re.
  inversion H.
  inversion H.
  apply MStar0.
  inversion H.
  assert (Q:[t]=[t]++[]).
  reflexivity.
  rewrite Q.
  apply MStarApp.
  apply MChar.
  apply MStar0.
  assert (G:s = s ++ []).
  rewrite -> app_nil_r.
  reflexivity.
  rewrite G.
  apply MStarApp.
  apply H.
  apply MStar0.
  assert (G:s = s ++ []).
  rewrite -> app_nil_r.
  reflexivity.
  rewrite G.
  apply MStarApp.
  apply H.
  apply MStar0.
  assert (G:s = s ++ []).
  rewrite -> app_nil_r.
  reflexivity.
  rewrite G.
  apply MStarApp.
  apply H.
  apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
intros T s constra. 
inversion constra.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
intros T s re1 re2 H. 
destruct H.
apply MUnionL.
apply H.
apply MUnionR.
apply H.
Qed.

Search In.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
intros T ss re H.
induction ss.
simpl.
apply MStar0.
simpl.
apply MStarApp.
specialize H with (s := x).
apply H.
simpl.
left.
reflexivity.
apply IHss.
intros s G.
apply H.
simpl.
right.
apply G.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.
    specialize In_app_iff with (A := T).
    intros G.
    specialize G with (l := s1).
    specialize G with (l' := s2).
    specialize G with (a := x).
    apply G in Hin.
    apply In_app_iff.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
    - (* MUnionL *)
      simpl. apply In_app_iff.
      left. apply (IH Hin).
    - (* MUnionR *)
      simpl. apply In_app_iff.
      right. apply (IH Hin).
    - (* MStar0 *)
      destruct Hin.
    - (* MStarApp *)
      simpl.
      specialize In_app_iff with (A := T).
      intros G.
      specialize G with (l := s1).
      specialize G with (l' := s2).
      specialize G with (a := x).
      apply G in Hin.
      destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
   match re with
     | EmptySet => false
     | EmptyStr => true
     | Char _ => true
     | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
     | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
     | Star _ => true
   end.
  
Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  split.
  intros H.
  destruct H as [s H'].
  induction H'.
  reflexivity.
reflexivity.
simpl.
rewrite -> IHH'1.
rewrite -> IHH'2.
reflexivity.
simpl.
rewrite -> IHH'.
reflexivity.
simpl.
rewrite -> IHH'.
simpl.
specialize orb_true_iff with (b1 := re_not_empty re1).
intros G.
specialize G with (b2 := true).
apply G.
right.
reflexivity.
reflexivity.
reflexivity.
intros G.
induction re.
simpl in G.
inversion G.
simpl in G.
exists [].
apply MEmpty.
exists [t].
apply MChar.
simpl in G.
apply andb_true_iff in G.
destruct G as [G1 G2].
apply IHre1 in G1.
apply IHre2 in G2.
destruct G1 as [s1 G1'].
destruct G2 as [s2 G2'].
exists (s1 ++ s2).
apply MApp.
apply G1'.
apply G2'.
simpl in G.
apply orb_true_iff in G.
destruct G as [G1 | G2].
apply IHre1 in G1.
destruct G1 as [s1 G1'].
exists s1.
apply MUnionL.
apply G1'.
apply IHre2 in G2.
destruct G2 as [s2 G2'].
exists s2.
apply MUnionR.
apply G2'.
exists [].
apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    simpl. intros H. apply H.
  - (* MChar. *) intros H. simpl. (* Stuck... *)
  Abort.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate. 
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    intros H. apply H.
  - (* MStarApp *)
    intros H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      apply Heqre'.
      apply H1.
Qed.



Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  exists [].
  simpl.
  split.
  reflexivity.
  intros s' H.
  specialize ex_falso_quodlibet with (P := s' =~ re).
  intros G.
  apply G in H.
  apply H.
  injection Heqre'.
  intros Eq.
  apply IHexp_match2 in Heqre'.
  destruct Heqre' as [ss He].
  exists (s1::ss).
  split.
  simpl.
  destruct He.
  rewrite <- H1.
  reflexivity.
  intros s' G.
  simpl in G.
  destruct G.
  rewrite <- H1.
  rewrite <- Eq.
  apply H.
  destruct He.
  apply H3.
  apply H1.
Qed.

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    le 1 (pumping_constant re).
Proof.
  intros T re.
  induction re.
  simpl.
  apply le_n.
  simpl.
  apply le_n.
  simpl.
  apply le_S.
  apply le_n.
  simpl.
  apply le_plus_trans.
  apply IHre1.
  simpl.
  apply le_plus_trans.
  apply IHre1.
  simpl.
  apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
  pumping_constant re = 0 -> False.
Proof. 
  intros T re H.
  assert (G:le 1 (pumping_constant re)).
  apply pumping_constant_ge_1.
  rewrite H in G.
  inversion G.
Qed.


Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof. 
  intros T n m l.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- app_assoc.
  rewrite IHn.
 reflexivity.
Qed.

Lemma napp_star :
    forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re H G.
  induction m.
  simpl.
  apply G.
  simpl.
  rewrite <- app_assoc.
  apply MStar1 in H.
  remember (napp m s1 ++ s2) as s3.
  assert (Q: s1 ++ s3 =~ Star re).
  apply star_app.
  apply H.
  apply IHm .
  apply Q.
Qed.


Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  le (pumping_constant re) (length s) ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    ~ (s2 = []) /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s H G.
  induction H.
simpl in G.
inversion G.
simpl in G.
apply Sn_le_Sm__n_le_m in G.
inversion G.
simpl in G.
rewrite app_length in G.
specialize add_le_cases with (n := pumping_constant re1).
intros Q.
specialize Q with (m := pumping_constant re2).
specialize Q with (p := length s1).
specialize Q with (q := length s2).
apply Q in G.
destruct G.
apply IHexp_match1 in H1.
destruct H1 as [s0 H1].
destruct H1 as [s3 H1].
destruct H1 as [s4 H1].
exists s0.
exists s3.
exists (s4++s2).
split.
destruct H1.
rewrite H1.
 rewrite <- app_assoc.
 rewrite <- app_assoc.
reflexivity.

destruct H1.
destruct H2.
split.
apply H2.
intros m.
assert (F:s0 ++ napp m s3 ++ s4 ++ s2 = (s0 ++ napp m s3 ++ s4)++ s2).
rewrite <- app_assoc.
rewrite <- app_assoc.
reflexivity.
rewrite F.
apply MApp.
specialize H3 with (m := m).
apply H3.
apply H0.
apply IHexp_match2 in H1.
destruct H1 as [s0 H1].
destruct H1 as [s3 H1].
destruct H1 as [s4 H1].
exists (s1 ++ s0).
exists s3.
exists s4.
split.
destruct H1.
rewrite H1.
rewrite <- app_assoc.
reflexivity.
destruct H1.
destruct H2.
split.
apply H2.
intros m.
rewrite <- app_assoc.
apply MApp.
apply H.
specialize H3 with (m := m).
apply H3.
simpl in G.
specialize plus_le with (n1 := pumping_constant re1).
intros Q.
specialize Q with (n2 := pumping_constant re2).
specialize Q with (m := length s1).
apply Q in G.
destruct G.
apply IHexp_match in H0.
destruct H0 as [s2 H0].
destruct H0 as [s3 H0].
destruct H0 as [s4 H0].
exists s2.
exists s3.
exists s4.
split.
destruct H0.
apply H0.
split.
destruct H0.
destruct H2.
apply H2.
intros m.
apply MUnionL.
destruct H0.
destruct H2.
specialize H3 with (m := m).
apply H3.
simpl in G.
specialize plus_le with (n1 := pumping_constant re1).
intros Q.
specialize Q with (n2 := pumping_constant re2).
specialize Q with (m := length s2).
apply Q in G.
destruct G.
apply IHexp_match in H1.
destruct H1 as [s1 H1].
destruct H1 as [s3 H1].
destruct H1 as [s4 H1].
exists s1.
exists s3.
exists s4.
split.
destruct H1.
apply H1.
split.
destruct H1.
destruct H2.
apply H2.
destruct H1.
destruct H2.
intros m.
apply MUnionR.
specialize H3 with (m := m).
apply H3.
simpl in G.
assert (Q:le 1 (pumping_constant re)).
  apply pumping_constant_ge_1.
specialize le_trans with (m:=1).
intros R.
specialize R with (n:=pumping_constant re).
specialize R with (o:=0).
apply R in Q.
inversion Q.
apply G.
exists [].
exists (s1++s2).
exists [].
simpl.
rewrite app_nil_r.
split.
reflexivity.
split.
unfold not.
intros AND.
rewrite AND in G.
simpl in G.
inversion G.
 assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
rewrite H2 in Hp.
inversion Hp.
induction m.
simpl.
apply MStar0.
simpl.
rewrite app_nil_r.
apply star_app.
apply star_app.
apply MStar1 in H.
apply H.
apply H0.
rewrite app_nil_r in IHm.
apply IHm.
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    ~ (s2 = []) /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
 intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - simpl. intros contra. apply Sn_le_Sm__n_le_m in contra. inversion contra.
  - intros H.
    assert (le_n_n: forall n : nat, ~ n < n).
    { intros n contra. induction n. inversion contra. apply IHn. apply Sn_le_Sm__n_le_m in contra. apply contra. }
    rewrite app_length in H. simpl in H.
    destruct (lt_ge_cases (length s1) (pumping_constant re1)) as [H1 | H1].
  + destruct (lt_ge_cases (length s2) (pumping_constant re2)) as [H2 | H2].

      * apply add_le_cases in H. destruct H as [H1' | H2'].
        ** assert (contra: pumping_constant re1 < pumping_constant re1).
           {
             apply le_trans with (n := S (length s1)).
             apply n_le_m__Sn_le_Sm. apply H1'. apply H1.
           }

           apply le_n_n in contra. exfalso. apply contra.
        ** assert (contra: pumping_constant re2 < pumping_constant re2).
           {
             apply le_trans with (n := S (length s2)).
             apply n_le_m__Sn_le_Sm. apply H2'. apply H2.
           }
           apply le_n_n in contra. exfalso. apply contra.
 * apply IH2 in H2.
        destruct H2 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists (s1 ++ s1'). exists s2'. exists s3'.
 split. rewrite Happ.
        rewrite <- app_assoc with T s1 s1' (s2' ++ s3').
        reflexivity.
        split. apply Hne.
        split. simpl. rewrite app_length. rewrite <- add_assoc.
        apply le_trans with (n := length s1 + pumping_constant re2).
        apply plus_le_compat_l. apply Hlen.
        apply plus_le_compat_r. apply n_lt_m__n_le_m in H1. apply H1.
        intros m.
        rewrite <- app_assoc with T s1 s1' (napp m s2' ++ s3').
        apply MApp. apply Hmatch1. apply Hnapp.
 + apply IH1 in H1.
      destruct H1 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
      exists s1'. exists s2'. exists (s3' ++ s2).
      split. rewrite Happ.
      rewrite <- app_assoc with T s1' (s2' ++ s3') s2.
      rewrite <- app_assoc with T s2' s3' s2.
      reflexivity.
      split. apply Hne.
      split. simpl.
      apply le_trans with (n := pumping_constant re1).
      apply Hlen. apply le_plus_l.
      intros m.
      rewrite app_assoc with T s1' (napp m s2') (s3' ++ s2).
      rewrite app_assoc with T (s1' ++ napp m s2') s3' s2.
      rewrite <- app_assoc with T s1' (napp m s2') s3'.
      apply MApp. apply Hnapp. apply Hmatch2.
- intros H.
  simpl in H.
  apply plus_le in H.
  destruct H as [H1 H2].
  apply IH in H1.
  destruct H1 as [s2 [s3 [s4 G]]].
  exists s2. 
  exists s3. 
  exists s4.
  split.
  destruct G.
  apply H.
  destruct G.
  destruct H0.
  split.
  apply H0.
  split.
  destruct H1.
  simpl.
apply le_plus_trans with (p:= pumping_constant re2)in H1.
apply H1.
destruct H1.
intros m.
apply MUnionL.
apply H3.
- intros H.
  simpl in H.
apply plus_le in H.
destruct H as [H1 H2].
apply IH in H2.
 destruct H2 as [s3 [s4 [s5 G]]].
  exists s3. 
  exists s4. 
  exists s5.
  split.
 destruct G.
  apply H.
  destruct G.
  destruct H0.
  split.
  apply H0.
split.
destruct H2.
  simpl.
apply le_plus_trans with (p:= pumping_constant re1)in H2.
assert (W: pumping_constant re2 + pumping_constant re1 = pumping_constant re1 + pumping_constant re2).
rewrite add_comm.
reflexivity.
rewrite W in H2.
apply H2.
destruct H2.
intros m.
apply MUnionR.
apply H3.
- intros H.
simpl in H.
assert (Q : pumping_constant re >= 1).
apply pumping_constant_ge_1.
specialize le_trans with (m := 1).
intros W.
specialize W with (n := pumping_constant re).
specialize W with (o := 0).
apply W in Q.
inversion Q.
apply H.
 - (* MStarApp *)
    intros H.
    rewrite app_length in H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    assert (Hl: (1 <= length s1 \/ 1 <= length s2)).
    { destruct s1. right. 
      apply le_trans with (pumping_constant re). 
      apply Hp. apply H. left. 
      simpl. 
      apply n_le_m__Sn_le_Sm. 
      apply O_le_n. }
    destruct s1 as [| x s11].
    + destruct (lt_ge_cases (length s2) (pumping_constant (Star re))) as [H2 | H2].
      * exists []. exists s2. exists [].
        split. rewrite app_nil_r. reflexivity.
        split. destruct Hl as [Hl | Hl].
        ** inversion Hl.
        ** destruct s2. inversion Hl. discriminate.
        ** split. apply n_lt_m__n_le_m in H2. apply H2.
        induction m. apply MStar0. simpl. rewrite <- app_assoc. apply star_app. apply Hmatch2. apply IHm.
      * apply IH2 in H2.
        destruct H2 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists s1'. exists s2'. exists s3'.
        split. rewrite Happ. reflexivity.
        split. apply Hne.
        split. apply Hlen.
        apply Hnapp.
    + remember (x :: s11) as s1.
      destruct (lt_ge_cases (length s1) (pumping_constant re)) as [H1 | H1].
      * exists []. exists s1. exists s2.
        split. reflexivity.
        split. rewrite Heqs1. discriminate.
        split. apply n_lt_m__n_le_m in H1. apply H1.
        intros m. simpl. apply napp_star. apply Hmatch1. apply Hmatch2.
      * apply IH1 in H1.
        destruct H1 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists s1'. exists s2'. exists (s3' ++ s2).
        split. rewrite Happ. simpl.
        rewrite <- app_assoc with (m := s2' ++ s3').
        rewrite <- app_assoc with (m := s3').
        reflexivity.
        split. apply Hne.
        split. apply Hlen.
        intros m. rewrite app_assoc. rewrite app_assoc. apply MStarApp.
        rewrite <- app_assoc. apply Hnapp. apply Hmatch2.
Qed.

End Pumping.


Theorem filter_not_empty_In : forall n l,
  ~ (filter (fun x => n =? x) l = []) ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. apply eqb_true in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  destruct H.
  - apply ReflectT. apply H0. reflexivity.
  - destruct H. apply ReflectF. intros contra. 
    apply H in contra. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  split.
  destruct H.
 intros W.
reflexivity.
 intros W.
unfold not in H.
exfalso.
apply H.
apply W.
 destruct H.
intros W.
apply H.
intros W.
discriminate W.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. 
  specialize eqb_eq with (n1 := n). 
  intros H.
  specialize H with (n2 := m). 
  apply iff_sym in H.
  apply H.
Qed.

Theorem filter_not_empty_In' : forall n l,
  ~ (filter (fun x => n =? x) l) = [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.


Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  intros contra.
  simpl in contra.
  apply contra.
  intros contra.
  destruct (eqbP n m) as [H | H].
  rewrite <- H in Hcount.
  simpl in contra.
  apply IHl'.
  simpl in Hcount.
  rewrite eqb_refl in Hcount.
  inversion Hcount.
  destruct contra.
  simpl in Hcount.
  rewrite eqb_refl in Hcount.
  inversion Hcount.
  apply H0.
  apply IHl'.
  simpl in Hcount.
  apply eqb_neq in H.
  rewrite H in Hcount.
  simpl in Hcount.
  apply Hcount.
  simpl in contra.
  destruct contra.
  rewrite H0 in Hcount.
  simpl in Hcount.
  rewrite eqb_refl in Hcount.
  inversion Hcount.
  apply H0.
Qed.

Inductive nostutter {X:Type} : list X -> Prop :=
  |nos0                  : nostutter []
  |nos1 (x:X) (H1 : nostutter []) : nostutter [x]
  |nos2 (x1:X) (x2:X) (l:list X) (H1 : nostutter (x2::l)) (H2: ~(x1=x2)):  nostutter (x1::x2::l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6]. 
Proof.
  apply nos2.
  apply nos2.
  apply nos2.
  apply nos2.
  apply nos2.
  apply nos1.
  apply nos0.
  intros H.
  inversion H.
  intros H.
  inversion H.
  intros H.
  inversion H.
  intros H.
  inversion H.
  intros H.
  inversion H.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  apply nos0.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  apply nos1.
  apply nos0.
Qed.


Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intros contra.
  inversion contra.
  inversion H3.
  destruct H9.
  apply eqb_eq.
  simpl.
  reflexivity.
Qed.

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | mergel0 l : merge l [] l
  | merger0 l : merge [] l l
  | mergel1 x l l1 l2 (H: merge l1 l2 l) : merge (x :: l1) l2 (x :: l)
  | merger1 x l l1 l2 (H: merge l1 l2 l) : merge l1 (x :: l2) (x :: l).


Theorem merge_filter : forall (X : Set) (test: X -> bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 H G Q.
  induction H.
  induction l.
  simpl.
 reflexivity.
simpl.
simpl in G.
destruct G.
rewrite H.
apply IHl in H0.
rewrite H0.
 reflexivity.
induction l.
simpl.
 reflexivity.
simpl.
destruct Q.
rewrite H.
apply IHl.
apply H0.
simpl in G.
destruct G.
apply IHmerge in H1.
simpl.
rewrite H0.
rewrite H1.
 reflexivity.
apply Q.
simpl.
destruct Q.
rewrite H0.
apply IHmerge.
apply G.
apply H1.
Qed.

Inductive pal {X:Type} : list X -> Prop :=
  | pal0 : pal []
  | pal1 x : pal [x]
  | pal2 x l (H: pal l) : pal (x :: l ++ [x]).

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l.
  induction l.
  simpl.
  apply pal0.
  simpl.
  rewrite -> app_assoc.
  apply pal2.
  apply IHl.
Qed.


Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l H.
  induction H.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  rewrite rev_app_distr.
  rewrite <- IHpal.
  simpl.
  reflexivity.
Qed.

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
intros X.
  assert (rev_length: forall (l: list X), length (rev l) = length l).
  {
    intros l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> app_length.
      simpl. rewrite -> IHl'. rewrite add_comm.
      reflexivity.
  }
  assert (lemma: forall (n: nat) (l: list X), length l <= n -> l = rev l -> pal l).
  {
    induction n.
    - intros l Hn _. destruct l. apply pal0. inversion Hn.
    - destruct l.
      + intros _ _. apply pal0.
      + intros Hlen Hrev. destruct (rev l) as [| x' l'] eqn:H'.
        * destruct l. apply pal1. apply f_equal with (f:=rev) in H'. rewrite rev_involutive in H'. discriminate.
        * simpl in Hrev. rewrite H' in Hrev. rewrite Hrev. injection Hrev as H0 H. destruct H0. apply pal2.
          apply f_equal with (f:=rev) in H. rewrite rev_app_distr in H. simpl in H. rewrite H' in H. injection H as H.
          apply f_equal with (f:=length) in H'. simpl in H'.
          simpl in Hlen. apply Sn_le_Sm__n_le_m in Hlen.
          rewrite rev_length in H'.
          assert (Hlen': length l' <= n).
          { apply Sn_le_Sm__n_le_m. rewrite <- H'. apply le_S. apply Hlen. }
          apply (IHn l' Hlen' H).
  }
  intros l.
  apply (lemma (length l) l). apply le_n.
Qed.


Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l H.
  induction l.
  inversion H.
  simpl in H.
  destruct H.
  rewrite H.
  exists [].
 exists l.
reflexivity.
apply IHl in H.
destruct H as [l1 H].
destruct H as [l2 H].
exists (x0::l1).
exists l2.
simpl.
rewrite H.
reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats1 x l (P: In x l): repeats (x :: l)
  | repeats2 x l (H: repeats l): repeats (x :: l).

Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1 l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
 intros EM X l1. induction l1 as [|x l1' IHl1'].
  - intros. inversion H0.
  - intros. destruct (EM (In x l1')) as [HIn | HnIn].
    + apply repeats1. apply HIn.
    + apply repeats2.
      destruct (in_split X x l2) as [l0 [l2' H3]].
      { apply H. simpl. left. reflexivity. }
      apply IHl1' with (l0 ++ l2').
      * intros. apply In_app_iff. assert (In x0 l2). apply H. right. apply H1.
        rewrite H3 in H2. apply In_app_iff in H2. destruct H2. left. apply H2.
        right. destruct H2. rewrite H2 in HnIn. exfalso. apply HnIn. apply H1. apply H2.
      * apply f_equal with (f:=length) in H3. rewrite app_length in H3. rewrite add_comm in H3. simpl in H3. rewrite app_length. rewrite add_comm. rewrite H3 in H0. simpl in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.

Require Import Coq.Strings.Ascii.
Definition string := list ascii.

Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

Lemma not_equiv_false : forall (P : Prop), ~ P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.


Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.


Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.


Lemma char_nomatch_char :
  forall (a b : ascii) s, ~ (b = a) -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.


Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.


Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    + reflexivity.
    + split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 re0 s1 re1 Hmat0 Hmat1).
Qed.


Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. induction s1. left. split.
    + apply H3. 
    + simpl. apply H4. 
    + simpl in H1. injection H1. intros G1 G2. right. exists s1. exists s2. split.
      rewrite G1. reflexivity. split. rewrite G2 in H3. apply H3. apply H4.
  - intros. destruct H as [H1 | H2]. destruct H1 as [H1A H1B].
    apply (MApp [] re0 (a::s) re1 H1A H1B).
    destruct H2 as [s0 H2]. destruct H2 as [s1 H2].
    destruct H2 as [H2A [H2B H2C]].
    assert (Q: (a::s0)++s1 = a::s).
    simpl. rewrite H2A. reflexivity.
    rewrite <- Q.
    apply (MApp (a::s0) re0 s1 re1 H2B H2C).
Qed.


Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  split.
  - remember (a :: s) as s'. remember (Star re) as re'.
    intros H. induction H as [| | | | | | s1 s2 re' H1 _ H2 IH].
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct s1.
      * apply (IH Heqs' Heqre').
      * injection Heqre' as Heqre'. destruct Heqre'.
        injection Heqs' as Heqs' Happ. destruct Heqs'.
        exists s1. exists s2.
        split. rewrite Happ. reflexivity.
        split. apply H1. apply H2.
  - intros H. destruct H as [s1 [s2 [H1 [H2 H3]]]].
    rewrite H1.
    assert (silly: a :: s1 ++ s2 = (a :: s1) ++ s2). reflexivity. rewrite silly.
    apply (MStarApp (a :: s1) s2 re H2 H3).
Qed.

Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

Fixpoint match_eps (re: reg_exp ascii) : bool := 
    match re with
     | EmptySet => false
     | EmptyStr => true
     | Char _ => false
     | App re1 re2 => andb (match_eps re1) (match_eps re2)
     | Union re1 re2 => orb (match_eps re1) (match_eps re2)
     | Star _ => true
    end.

Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  induction re.
  - simpl. apply ReflectF. intros contra. inversion contra.
  - simpl. apply ReflectT. apply MEmpty.
  - simpl. apply ReflectF. intros contra. inversion contra.
  - simpl. destruct (match_eps re1). 
    + destruct (match_eps re2). apply reflect_iff in IHre1. destruct IHre1. simpl in H0.
    simpl. apply ReflectT. assert (T1: true = true). reflexivity.
    apply H0 in T1.  apply reflect_iff in IHre2. destruct IHre2. 
    assert (T2: true = true). reflexivity. apply H2 in T2. 
    apply (MApp [] re1 [] re2 T1 T2). simpl. apply ReflectF. intros contra.
    apply reflect_iff in IHre1. destruct IHre1. apply reflect_iff in IHre2. destruct IHre2. 
    apply app_exists in contra. destruct contra as [s1 Q]. destruct Q as [s2 Q].
   destruct Q as [Q1 [Q2 Q3]]. assert (T1: true = true). reflexivity.
    apply H0 in T1. assert (W: s1 = []). induction s1. reflexivity. discriminate.
    rewrite W in Q1. simpl in Q1. rewrite <- Q1 in Q3. apply H1 in Q3. discriminate.
  + simpl.  apply ReflectF. intros contra. apply reflect_iff in IHre1. apply app_exists in contra. 
   destruct contra as [s1 Q]. destruct Q as [s2 Q]. destruct Q as [Q1 [Q2 Q3]].  
  assert (W: s1 = []). induction s1. reflexivity. discriminate. rewrite W in Q2. apply IHre1 in Q2. discriminate.
   - simpl. destruct (match_eps re1). destruct (match_eps re2). simpl. apply ReflectT.
   apply union_disj. apply reflect_iff in IHre1. destruct IHre1. assert (T1: true = true). reflexivity.
    apply H0 in T1. left. apply T1. simpl. apply ReflectT. apply union_disj. apply reflect_iff in IHre1. destruct IHre1. assert (T1: true = true). reflexivity.
    apply H0 in T1. left. apply T1. destruct (match_eps re2). simpl. apply ReflectT. apply union_disj.
    apply reflect_iff in IHre2. destruct IHre2. assert (T1: true = true). reflexivity.
    apply H0 in T1. right. apply T1. simpl.  apply ReflectF. intros contra. apply union_disj in contra.
    destruct contra. apply reflect_iff in IHre1. destruct IHre1. apply H0 in H. discriminate.
apply reflect_iff in IHre2. destruct IHre2. apply H0 in H. discriminate.
    - simpl. apply ReflectT.  apply MStar0. 
Qed.

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
     match re with
     | EmptySet => EmptySet
     | EmptyStr => EmptySet
     | Char x => if eqb x a then EmptyStr else EmptySet
     | App re1 re2 => if match_eps re1 then Union (derive a re2) (App (derive a re1) re2) else App (derive a re1) re2
     | Union re1 re2 => Union (derive a re1) (derive a re2)
     | Star re => App (derive a re) (Star re)
     end.

Lemma derive_corr : derives derive.
Proof.
  unfold derives.
  intros.
  induction re.
  - simpl. unfold is_der. intros. split. intros Q. inversion Q.
    intros Q. inversion Q.
  - simpl. unfold is_der. intros. split. intros Q. inversion Q.
    intros Q. inversion Q.
  - unfold is_der. intros. split. intros H. inversion H. simpl. rewrite -> eqb_refl. apply MEmpty. 
    intros H. simpl in H. destruct (t =? a)%char eqn:Hta in H. inversion H. apply eqb_eq in Hta. 
    rewrite Hta. apply MChar. inversion H.
  - unfold is_der. intros. 
    split. intros H. simpl.  destruct match_eps_refl with re1. destruct match_eps_refl with re2.
    apply union_disj. apply app_ne in H. destruct H. destruct H. unfold is_der in IHre1.
    unfold is_der in IHre2. apply IHre2 in H2. left. apply H2. right. apply app_exists. destruct H as [sx [[] H]].
    destruct H as [Hx [Hy Hz]]. rewrite app_nil_r in Hx. rewrite <- Hx in Hy.  apply IHre1 in Hy.
    exists s. exists []. split. rewrite app_nil_r. reflexivity. split. apply Hy. apply Hz. unfold is_der in IHre1.
    exists sx. exists (x::l). split. simpl. destruct H as [Hx [Hy Hz]]. apply Hx. split. destruct H as [Hx [Hy Hz]].
    specialize IHre1 with (s := sx). apply IHre1. apply Hy. destruct H as [Hx [Hy Hz]]. apply Hz. unfold not in H1.
    apply union_disj. apply app_ne in H. destruct H. destruct H. apply IHre2 in H2. left. apply H2. right. apply app_exists. 
    destruct H as [sx [[] H]]. destruct H as [Hx [Hy Hz]]. apply H1 in Hz. inversion Hz. exists sx. exists (x::l).
    destruct H as [Hx [Hy Hz]]. split. apply Hx. split. unfold is_der in IHre1. specialize IHre1 with (s := sx). apply IHre1.
    apply Hy. apply Hz. apply app_exists. apply app_ne in H. destruct H. destruct H. apply H0 in H. inversion H.
    destruct H as [sx [sy H]]. destruct H as [Hx [Hy Hz]]. exists sx. exists sy. split. apply Hx. split. unfold is_der in IHre1.
    specialize IHre1 with (s := sx). apply IHre1 in Hy. apply Hy. apply Hz.  intros H. apply app_ne. simpl in H.
    destruct match_eps_refl with re1. apply union_disj in H. unfold is_der in IHre2. destruct H. apply IHre2 in H.
    left. split. apply H0. apply H. apply app_exists in H. destruct H as [sx [sy H]]. unfold is_der in IHre1.
    specialize IHre1 with (s := sx). destruct H as [Hx [Hy Hz]]. right. exists sx. exists sy. split.  apply Hx.
    split. apply IHre1 in Hy. apply Hy. apply Hz. apply app_exists in H. unfold is_der in IHre1. destruct H as [sx [sy H]].
    destruct H as [Hx [Hy Hz]]. right. exists sx. exists sy. split. apply Hx. specialize IHre1 with (s := sx). apply IHre1 in Hy.
    split. apply Hy. apply Hz. 
  - unfold is_der. intros. split. intros H. simpl. apply union_disj. inversion H. unfold is_der in IHre1. apply IHre1 in H2.
    left. apply H2. unfold is_der in IHre2. apply IHre2 in H1. right. apply H1. intros H. simpl in H. apply union_disj in H.
    simpl. destruct H. apply MUnionL. unfold is_der in IHre1. apply IHre1 in H. apply H. apply MUnionR. unfold is_der in IHre2.
    apply IHre2 in H. apply H.
  - unfold is_der. intros. split. intros H. simpl. apply app_exists. apply star_ne in H. destruct H as [sx [sy H]]. 
    destruct H as [Hx [Hy Hz]]. exists sx. exists sy. split. apply Hx. split. unfold is_der in IHre. apply IHre in Hy.
    apply Hy. apply Hz. intros H. apply star_ne. simpl in H. apply app_exists in H.  destruct H as [sx [sy H]]. 
    destruct H as [Hx [Hy Hz]]. exists sx. exists sy. split. apply Hx. split. unfold is_der in IHre. apply IHre in Hy.
    apply Hy. apply Hz. 
Qed.

Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool := 
    match s with
     | (a :: s) => regex_match s (derive a re)
     | [] => match_eps re
     end.

Theorem regex_match_correct : matches_regex regex_match.
Proof. 
  unfold matches_regex.
  induction s.
  intros.
  apply iff_reflect. split. intros.
  simpl.
  destruct match_eps_refl with re.
  reflexivity.
  apply H0 in H.
  inversion H.
  simpl.
  intros.
  destruct match_eps_refl with re.
  apply H0.
  inversion H.
  intros.
  apply iff_reflect.
  split. intros.
  simpl.
  specialize IHs with (re := derive x re).
  apply reflect_iff in IHs.
  apply IHs.
  destruct (derive_corr x re) with (s:=s).
  apply H0.
  apply H.
  intros H.
  simpl in H.
  specialize IHs with (re := derive x re).
  apply reflect_iff in IHs.
  apply IHs in H.
  destruct (derive_corr x re) with (s:=s).
  apply H1.
  apply H.
Qed.






