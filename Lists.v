 From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
   | pair (n1 n2 : nat).

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with 
    | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with 
    | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst'(p : natprod) : nat :=
  match p with
   | (x,y) => x
  end.

Definition snd'(p : natprod) : nat :=
  match p with
   | (x,y) => y
  end.

Definition swap_pair(p : natprod) : natprod :=
  match p with
   | (x,y) => (y,x)
  end.

Fixpoint minus (n m : nat) : nat :=
   match n,m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
   end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
simpl.
reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
induction p.
simpl.
reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
intros p. destruct p as [n m].
simpl.
reflexivity. Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
intros p. destruct p as [n m].
simpl.
reflexivity. Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1(cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | h :: t => S( length t)
 end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with 
   | nil => default
   | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with 
   | nil => nil
   | h :: t => t
  end.

Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2 : hd 0 [] = 0.
Proof.  reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
   match l with
    | nil => nil
    | 0 :: t => nonzeros t
    | h :: t => h :: (nonzeros t)
   end.

Compute nonzeros [1;0;1;0;8;0;2;3;0;0].

Fixpoint oddmembers (l:natlist) : natlist :=
   match l with
    | nil => nil
    | h :: t => 
             match even h with
              |true => oddmembers t
              |false => h :: (oddmembers t)
             end
   end.
 
Compute  oddmembers [0;1;0;2;3;0;0].

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Compute  countoddmembers [1;0;3;1;4;5].

Compute  countoddmembers nil.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
   | nil => l2
   | h :: t =>
           match l2 with
             | nil => l1
             | h' :: t' => h :: h' :: (alternate t t')
           end
  end.

Compute (alternate [1;2;3] [4;5;6]).

Compute (alternate [1] [4;5;6]).

Compute (alternate [1;2;3] [4]).

Compute (alternate [] [20;30]).

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
   | nil => 0
   | h :: t =>
          if (eqb v h) then S (count v t)
          else count v t
  end.

Compute (count 1 [1;2;3;1;4;1] ).

Compute (count 6 [1;2;3;1;4;1]).

Definition sum (a b : bag): bag :=
  app a b.

Compute (count 1 (sum [1;2;3] [1;4;1])).

Definition add (v : nat) (s : bag) : bag :=
   v::s.

Compute  add 1 [1;4;1].

Compute  add 6 [1;4;1].

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with 
   |nil => false
   |h :: t => 
           if (eqb v h) then true
           else (member v t)
 end.

Compute (member 1 [1;4;1]).

Compute (member 2 [1;4;1]).

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with 
   |nil => nil
   |h :: t => 
         if (eqb v h) then t
         else h::(remove_one v t)
  end.

Compute (remove_one 1 [2;1;5;4;1]).

Compute count 5 (remove_one 5 [2;1;4;1]).
  
Compute count 4 (remove_one 5 [2;1;4;5;1;4]).
  
Compute count 5 (remove_one 5 [2;1;5;4;5;1;4]).
  
Fixpoint remove_all (v:nat) (s:bag) : bag :=
match s with 
   |nil => nil
   |h :: t => 
         if (eqb v h) then remove_all v t
         else h::(remove_all v t)
  end.


Compute remove_all 5 [5;2;5;5;1;5;4;1].
 
Compute  count 5 (remove_all 5 [2;1;4;1]).
 
Compute  count 4 (remove_all 5 [2;1;4;5;1;4]).
 
Compute  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]).
 
Fixpoint included (s1 : bag) (s2 : bag) : bool :=
match s1 with 
 |nil => true
 |h1 :: t1 =>
        if (member h1 s2) then included t1 (remove_one h1 s2)
        else false
end.


  
Compute  included [1;2] [2;1;4;1].
 
Compute  included [1;2;2] [2;1;4;1].

 
Theorem add_inc_count : forall (s : bag) (v:nat),
      S (count v s) = count v (add v s).
Proof.
intros s.
intros v.
simpl.
destruct v as [|v'].
simpl.
reflexivity.
rewrite -> eqb_refl.
reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [|n l1' IHl1'].
reflexivity.
simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Compute rev [1;2;3].

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.


Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite add_comm.
    reflexivity.
Qed.

Search rev.

Search (_ + _ = _ + _).

Search (_ + _ = _ + _) inside Induction.

Search (?x + ?y = ?y + ?x).

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
intros l. induction l as [| n l' IHl'].
reflexivity.
simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros l1 l2. induction l1 as [| n l1' IHl1'].
simpl.
rewrite -> app_nil_r.
reflexivity.
simpl.
rewrite -> IHl1'.
rewrite <- app_assoc.
reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
reflexivity.
simpl.
rewrite -> rev_app_distr.
rewrite -> IHl'.
simpl.
reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
intros l1 l2 l3 l4.
simpl.
rewrite -> app_assoc.
rewrite -> app_assoc.
reflexivity.
Qed.


Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
intros l1 l2.
induction l1 as [| n l1' IHl1'].
simpl.
reflexivity.
simpl.
rewrite -> IHl1'.
induction n.
reflexivity.
reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
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
        if eqb h1 h2 then eqblist t1 t2
        else false
    end
end.

Compute eqblist [1;2;3] [1;2;3].

Compute eqblist [1;2;3] [1;2;4].

Compute eqblist nil nil.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
intros l. 
induction l as [| n l' IHl'].
reflexivity.
simpl.
rewrite -> eqb_refl.
rewrite <- IHl'.
reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
intros s.
induction s as [| n s IHs].
simpl. reflexivity.
induction n as [| n' IHn'].
simpl. rewrite -> leb_n_Sn.
reflexivity.
simpl. rewrite -> IHs. reflexivity. Qed.

Search bag.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
intros f n.
intros n1 n2.
intros H.
rewrite -> n.
rewrite <- H.
rewrite <- n.
reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
intros l1 l2.
intros H.
rewrite <- rev_involutive.
rewrite <- H.
rewrite -> rev_involutive.
reflexivity.
Qed.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
   | nil => None
   | a :: l' => match n with
                 | 0 => Some a 
                 | S n' => nth_error l' n'
                end
 end.


Compute nth_error [4;5;6;7] 0.

Compute nth_error [4;5;6;7] 3.

Compute nth_error [4;5;6;7] 9.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with 
   | nil => None
   | h :: t => Some h
 end.

Compute hd_error [].

Compute hd_error [1].

Compute hd_error [5;6].

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
intros l.
induction l as [| n l' IHl'].
reflexivity.
simpl.
reflexivity.
Qed.


End NatList.

Inductive id : Type :=
 |Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  |Id n1, Id n2 => n1 =? n2
 end.

Compute eqb 2 2.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
intros x.
induction x.
simpl.
rewrite eqb_refl.
reflexivity.
Qed.

Module PartialMap.
Export NatList.


Inductive partial_map : Type :=
  |empty
  |record (i : id) (v : nat) (m : partial_map).


Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
   record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
   |empty => None
   |record y v d' => if eqb_id x y then Some v
                     else find x d'
 end.

Theorem update_eq:
   forall (d : partial_map) (x : id) (v : nat),
    find x (update d x v) = Some v.
Proof.
simpl.
induction x.
simpl.
rewrite eqb_refl.
reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
simpl.
intros d x y o.
intros H.
rewrite -> H.
reflexivity.
Qed.

End PartialMap.
