
From LF Require Export basic.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. 
  rewrite -> IHn'. 
  reflexivity. 
  Qed.

Theorem minus_n_n : forall n,
   minus n n = 0.
Proof.  
   induction n as [| n' IHn'].
   simpl. reflexivity.
   simpl. rewrite -> IHn'.
   reflexivity.
   Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. 
  rewrite -> IHn'. 
  reflexivity. 
  Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros n. 
induction n as [| n' IHn'].
 reflexivity.
 simpl. 
intros m.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros n. 
induction n as [| n' IHn'].
intros m.
rewrite -> add_0_r.
reflexivity.
simpl.
intros m.
rewrite -> IHn'.
rewrite -> plus_n_Sm.
reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n. 
induction n as [| n' IHn'].
reflexivity.
simpl.
intros m. 
intros p. 
rewrite <- IHn'.
reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Compute double 4.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.  Qed.

Lemma double_plus : forall n, double n = n + n .
Proof.
intros n. 
induction n as [| n' IHn'].
reflexivity.
simpl.
rewrite -> IHn'.
rewrite -> plus_n_Sm.
reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
intros n. 

induction n as [| n' IHn'].
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
 intros n. induction n as [|n']. 
  - reflexivity.
  - destruct n' as [|n'']. 
    + reflexivity.
    + rewrite IHn'. rewrite negb_involutive. reflexivity. 
Qed.

Theorem mult_0_plus' : forall n m : nat,
   (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H : n + 0 + 0 = n).
  rewrite add_comm. 
  simpl.
rewrite add_comm.
reflexivity.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
 assert (H: n + p = p + n).
  { rewrite add_comm. reflexivity. }
rewrite H.
assert (L: m + (p + n) = (m + p) + n).
  { rewrite add_assoc. reflexivity. }
rewrite L.
assert (K: (m + p) + n = n + (m + p)).
  { rewrite add_comm. reflexivity. }
rewrite K.
reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
intros m. induction m as [|m'].
intros n.
rewrite -> mul_0_r.
reflexivity.
simpl.
intros n.
rewrite -> IHm'.
rewrite add_comm.
rewrite <- mult_n_Sm.
reflexivity.
Qed.


Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
intros n m p.
intros H.
induction p as [|p' IHp'].
rewrite add_comm.
rewrite add_0_r.
rewrite add_comm.
rewrite add_0_r.
rewrite H.
reflexivity.
simpl.
rewrite IHp'.
reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
 intros n.
induction n as [|n' IHn'].
reflexivity.
simpl.
rewrite IHn'.
reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
intros n.
simpl.
reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
intros b.
destruct b.
reflexivity.
reflexivity.
Qed.


Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
intros n.
simpl.
reflexivity.
Qed.


Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
intros n.
simpl.
rewrite add_0_r.
reflexivity.
Qed.


Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
intros b c.
destruct b.
destruct c.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.


Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
induction n as [|n' IHn'].
reflexivity.
simpl.
intros m p.
rewrite -> IHn'.
rewrite <- add_assoc.
reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
 induction n as [|n' IHn'].
reflexivity.
simpl.
intros m p.
rewrite -> mult_plus_distr_r.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros n m p.
rewrite -> add_assoc.
rewrite -> add_assoc.
replace (n + m) with (m + n).
reflexivity.
rewrite -> add_comm.
reflexivity.
Qed.

Fixpoint incr (m:bin) : bin := match m with
     | Z    => B1 Z
     | B0 n => B1 n
     | B1 n => B0 (incr n)
     end.

Fixpoint bin_to_nat (m:bin) : nat := match m with
     | Z    => O
     | B0 n => (bin_to_nat n) + (bin_to_nat n)
     | B1 n => S ((bin_to_nat n) + (bin_to_nat n))
     end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl.
  rewrite -> IHb'.
  simpl. rewrite <- plus_n_Sm.
  reflexivity.
Qed.

Compute (minus 93 2).

Fixpoint divideTwo (n:nat) : nat :=
  match n with
   | O => O
   | S n' => S (divideTwo (minus n' 1)) 
 end.

Compute divideTwo 7.

Fixpoint nat_to_bin (n:nat) : bin :=
match n with
  | 0 => Z
  | S n' => incr (nat_to_bin n')
  end.

Compute nat_to_bin (S (S (S (S O)))).

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n.
 reflexivity.
simpl.
rewrite -> bin_to_nat_pres_incr.
simpl.
rewrite -> IHn.
 reflexivity.
Qed.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
simpl.
reflexivity.
Qed.

Definition double_bin (b:bin) : bin :=
 match b with
  |Z => Z
  |B0 b' => B0 (B0 b')
  |B1 b' => B0 (B1 b')
 end.

Compute double_bin (B1 (B0 (B1 Z))).

Example double_bin_zero : double_bin Z = Z.
Proof.
  simpl.
reflexivity.
Qed.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
 induction b.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.


Fixpoint normalize (b:bin) : bin
  := match b with
     | Z     => Z
     | B0 b' => double_bin (normalize b')
     | B1 b' => incr (double_bin (normalize b'))
     end.

Lemma nat_to_bin_double : forall n : nat,
  nat_to_bin(double n) = double_bin(nat_to_bin n).
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> double_incr_bin. rewrite <- IHn.
    reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b as [|b'|b'].
  - reflexivity.
  - simpl. rewrite <- IHb'.
    destruct (bin_to_nat).
    + reflexivity.
    + rewrite <- double_plus. rewrite -> nat_to_bin_double.
      reflexivity.
  - simpl. rewrite <- IHb'.
    rewrite <- double_plus. rewrite -> nat_to_bin_double.
    reflexivity.
Qed.



