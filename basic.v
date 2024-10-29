Inductive day : Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

Definition next_weekday (d:day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
     (next_weekday (next_weekday saturday))=tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
     | true
     | false.

Definition negb (b:bool) : bool :=
     match b with
     | true => false
     | false => true
     end.

Definition ret (b:bool) : bool :=
     match b with
     | true => true
     | false => false
     end.

Definition andb (b1:bool) (b2:bool) : bool :=
     match b1 with
     | true => b2
     | false => false
     end.

Definition orb (b1:bool) (b2:bool) : bool :=
     match b1 with
     | true => true
     | false => b2
     end.

Compute (andb true false).

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
    if b then false
    else true.

Compute (negb' true).

Definition nandb (b1:bool) (b2:bool) : bool :=
     if (orb (negb b1) (negb b2)) then true
     else false.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
     if (andb b1 b2) then 
        if b3 then true
        else false
     else false.

Compute (andb3 true true true).
Compute (andb3 false true false).
Compute (andb3 true false true).
Compute (andb3 true true false).

Check true.
Check negb.
Check andb.
Check andb3.

Inductive rgb : Type :=
    | red
    | green
    | blue.


Inductive color : Type :=
    | black
    | white
    | primary (p:rgb).

Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary p => false
    end.

Compute (monochrome (primary red)).

Definition isred (c : color) : bool :=
    match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
    end.

Compute (isred (primary green)).

Module Playground.
   Definition foo : rgb := blue.
End Playground.

Compute Playground.foo.

Definition foo : bool := true.

Compute foo.


Module TuplePlayground.

Inductive bit : Type := 
   | B1
   | B0.

Inductive nybble : Type :=
   | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool := 
   match nb with
   | (bits B0 B0 B0 B0) => true
   | (bits _ _ _ _) => false
   end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n => n
    end.

Compute (pred (S (S O))).
End NatPlayground.

Check (S (S (S (S 0)))).

Definition minustwo (n : nat) : nat :=
    match n with
    | 0 => 0
    | S 0 => 0
    | S (S n) => n
    end.

Compute (minustwo 4).
Compute S (S (S 1)).

Fixpoint even (n:nat) : bool :=
   match n with
   | 0 => true
   | S 0 => false
   | S (S n) => even n
   end.

Compute even 54.

Definition odd (n:nat) : bool :=
  negb (even n).

Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
   match n with
   | 0 => m
   | S n => S (plus n m)
   end.

Fixpoint multi (n : nat) (m : nat) : nat :=
   match n with
   | 0 => 0
   | S n' => plus m (multi n' m)
   end.

Fixpoint minus (n : nat) (m : nat) : nat :=
   match n, m with
   | 0, _ => 0
   | n', 0 => n'
   | S n', S m' => minus n' m'
   end.

Compute plus 2 3.
Compute multi 2 3.
Compute minus 98 3.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
   match power with
   | 0 => S 0
   | S p => mult base (exp base p)
   end.

Fixpoint fac (n : nat) : nat :=
   match n with
   | 0 => 1
   | S n' => mult n (fac n')
   end.

Compute fac 4.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Compute leb 4 4.

Definition ltb (n m : nat) : bool :=
   if (leb n m) then
      match m with
       | O => false
       | S m' => leb n m'
      end
   else false.



Compute ltb 3 3.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat, n = m -> n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros L.
  rewrite -> H.
  rewrite -> L.
  reflexivity. Qed.

Check plus_id_exercise.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Check mult_n_1.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct c eqn:Ec.
  - destruct b eqn:Eb.
    + reflexivity.
    + intros H.
      rewrite <- H.
      reflexivity.
  - destruct b eqn:Eb.
    + intros H.
      rewrite <- H.
      reflexivity.
    + intros H.
      rewrite <- H.
      reflexivity.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b. destruct b eqn:Eb.
  - destruct f eqn:Ef.
    + reflexivity.
    + rewrite <- Ef.
      rewrite -> x.
      rewrite -> x.
      reflexivity.
  - destruct f eqn:Ef.
    + rewrite <- Ef.
      rewrite -> x.
      rewrite -> x.
      reflexivity.
    + reflexivity.
Qed.

Theorem andb_eq_orb :
forall (b c : bool),
(andb b c = orb b c) ->
b = c.
Proof.
  intros b c.
  intros H.
  destruct b eqn:Eb.
      - destruct andb eqn:Eand.
        + destruct c eqn:Ec.
          reflexivity.
          rewrite <- Eand.
          reflexivity.
        + destruct c eqn:Ec.
          reflexivity.
          rewrite -> H.
          reflexivity.
      - destruct andb eqn:Eand.
        + destruct c eqn:Ec.
          rewrite <- Eand.
          reflexivity.
          reflexivity.
        + destruct c eqn:Ec.
          rewrite -> H.
          reflexivity.
          reflexivity.
Qed.

Module LateDays.

Inductive letter : Type :=
    | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
   Grade (l : letter) (m : modifier).

Inductive comparison : Type :=
   | Eq (* "equal" *)
   | Lt (* "less than" *)
   | Gt. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter): 
comparison :=
   match l1, l2 with
   | A, A => Eq
   | A, _ => Gt
   | B, A => Lt
   | B, B => Eq
   | B, _ => Gt
   | C, (A | B) => Lt
   | C, C => Eq
   | C, _ => Gt
   | D, (A | B | C) => Lt
   | D, D => Eq
   | D, _ => Gt
   | F, (A | B | C | D) => Lt
   | F, F => Eq
   end.

Compute letter_comparison B A.

Compute letter_comparison D D.

Compute letter_comparison B F.

Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  intros l.
  destruct l eqn : El.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) :
comparison :=
   match m1, m2 with
   | Plus, Plus => Eq
   | Plus, _ => Gt
   | Natural, Plus => Lt
   | Natural, Natural => Eq
   | Natural, _ => Gt
   | Minus, (Plus | Natural) => Lt
   | Minus, Minus => Eq
   end.

Definition grade_comparison (g1 g2 : grade) : 
comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 => 
    match (letter_comparison l1 l2) with
    | Eq => modifier_comparison m1 m2
    | not_eq => not_eq
    end 
  end.
 
Compute grade_comparison (Grade A Minus) (Grade B Plus).
Compute grade_comparison (Grade A Minus) (Grade A Plus).
Compute grade_comparison (Grade F Plus) (Grade F Plus).
Compute grade_comparison (Grade B Minus) (Grade C Plus).

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F
  end.


Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. 
Abort.

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  intros H.
  destruct l.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite <- H.
    reflexivity.
Qed.

Definition lower_grade (g : grade) : grade :=
  match g with
   |Grade l m =>
      match l with 
        |F =>    
           match m with
            | Minus => Grade l Minus
            | Plus => Grade l Natural
            | Natural => Grade l Minus
           end
        |(A | B | C | D)=> 
           match m with
            | Minus => Grade (lower_letter l) Plus
            | Plus => Grade l Natural
            | Natural => Grade l Minus
           end
      end
   end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
    destruct Grade eqn:Eg.
       destruct l eqn:El.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
 Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
     destruct Grade eqn:Eg.
       destruct l eqn:El.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
destruct Grade eqn:Eg.
       destruct l eqn:El.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
Qed.



Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
destruct Grade eqn:Eg.
       destruct l eqn:El.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
Qed.



Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
destruct Grade eqn:Eg.
       destruct l eqn:El.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
Qed.


Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
destruct Grade eqn:Eg.
       destruct l eqn:El.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
Qed.


Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
destruct Grade eqn:Eg.
       destruct l eqn:El.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
        rewrite <- Eg.
        reflexivity.
Qed.

Compute lower_grade (Grade F Minus).

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof.
     reflexivity.
Qed.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
   intros g.
   intros H.
   destruct g eqn : Eg.
    + destruct l eqn : El.
       - destruct m eqn : Em.
          reflexivity.
          reflexivity.
          reflexivity.
       - destruct m eqn : Em.
          reflexivity.
          reflexivity.
          reflexivity.
       - destruct m eqn : Em.
          reflexivity.
          reflexivity.
          reflexivity.
       - destruct m eqn : Em.
          reflexivity.
          reflexivity.
          reflexivity.
       - destruct m eqn : Em.
          reflexivity.
          reflexivity.
          rewrite -> lower_grade_F_Minus.
          rewrite -> H.
          reflexivity.
    Qed.


(* This function encodes the following policy:
      # late days     penalty
         0 - 8        no penalty
         9 - 16       lower grade by one step (A+ => A, A => A-, A- => B+, etc.)
        17 - 20       lower grade by two steps
          >= 21       lower grade by three steps (a whole letter) *)
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold :
 forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof.
  intros late_days.
  intros g.
  intros H.
  destruct late_days eqn:Eday.
      + rewrite -> apply_late_policy_unfold.
        reflexivity.
      + rewrite -> apply_late_policy_unfold.
        rewrite -> H.
        reflexivity.
Qed.

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (grade_comparison (Grade F Minus) g = Lt) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
  intros late_days.
  intros g.
  intros H.
  intros L.
  intros Q.
destruct late_days eqn:Eday.
      + rewrite -> apply_late_policy_unfold.
        rewrite -> H.
        rewrite -> L.
        reflexivity.
      + rewrite -> apply_late_policy_unfold.
        rewrite -> H.
        rewrite -> L.
        reflexivity.
Qed.

End LateDays.


Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).


Fixpoint incr (m:bin) : bin :=
match m with
 | Z => B1 Z
 | B1 n => B0 (incr n)
 | B0 n => B1 n
end.

Fixpoint bin_to_nat (m:bin) : nat :=
match m with
 |Z => O
 |B0 n => (bin_to_nat n) + (bin_to_nat n)
 |B1 n => S ((bin_to_nat n) + (bin_to_nat n)) 
end.

Compute  bin_to_nat (B0 (B0 (B1 Z))).
Compute  bin_to_nat (B1 Z).

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
reflexivity.
Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
reflexivity.
Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
reflexivity.
Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof.
reflexivity.
Qed.


Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof.
reflexivity.
Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof.
reflexivity.
Qed.





