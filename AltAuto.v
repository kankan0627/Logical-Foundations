Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality,-deprecated-syntactic-definition,-deprecated]".
From Coq Require Import Arith List.
From LF Require Import IndProp.

Fixpoint re_opt_e {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App EmptyStr re2 => re_opt_e re2
  | App re1 re2 => App (re_opt_e re1) (re_opt_e re2)
  | Union re1 re2 => Union (re_opt_e re1) (re_opt_e re2)
  | Star re => Star (re_opt_e re)
  | _ => re
  end.

Lemma re_opt_e_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) simpl.
    destruct re1.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + inversion Hmatch1. simpl. apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
  - (* MUnionL *) simpl. apply MUnionL. apply IH.
  - (* MUnionR *) simpl. apply MUnionR. apply IH.
  - (* MStar0 *)  simpl. apply MStar0.
  - (* MStarApp *) simpl. apply MStarApp.
    * apply IH1.
    * apply IH2.
Qed.

Theorem silly1 : forall n, 1 + n = S n.
Proof. try reflexivity. (* this just does reflexivity *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  Fail reflexivity.
  try reflexivity. (* proof state is unchanged *)
  apply HP.
Qed.

Lemma simple_semi : forall n, (n + 1 =? 0) = false.
Proof.
  intros n.
  destruct n eqn:E.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

Lemma simple_semi' : forall n, (n + 1 =? 0) = false.
Proof.
  intros n.
  (* destruct the current goal *)
  destruct n;
  (* then simpl each resulting subgoal *)
  simpl;
  (* and do reflexivity on each resulting subgoal *)
  reflexivity.
Qed.

Lemma simple_semi'' : forall n, (n + 1 =? 0) = false.
Proof.
  destruct n; reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. 
  destruct b; destruct c; intros; simpl in H; inversion H; reflexivity.
  Qed.

Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. 
induction n;
try reflexivity;
simpl;
intros;
rewrite <- IHn;
reflexivity.
Qed.

Fixpoint nonzeros (lst : list nat) :=
  match lst with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Lemma nonzeros_app : forall lst1 lst2 : list nat,
  nonzeros (lst1 ++ lst2) = (nonzeros lst1) ++ (nonzeros lst2).
Proof. 
  induction lst1; try reflexivity; simpl; destruct x;
intros; simpl; rewrite <- IHlst1; reflexivity.
Qed.

Lemma re_opt_e_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    (* Do the simpl for every case here: *)
    simpl.
  - (* MEmpty *) apply MEmpty.
  - (* MChar *) apply MChar.
  - (* MApp *)
    destruct re1;
    (* Most cases follow by the same formula.  Notice that apply MApp gives two subgoals: try apply IH1 is run on _both_ of
       them and succeeds on the first but not the second; apply IH2
       is then run on this remaining goal. *)
    try (apply MApp; try apply IH1; apply IH2).
    (* The interesting case, on which try... does nothing, is when
       re1 = EmptyStr. In this case, we have to appeal to the fact
       that re1 matches only the empty string: *)
    inversion Hmatch1. simpl. apply IH2.
  - (* MUnionL *) apply MUnionL. apply IH.
  - (* MUnionR *) apply MUnionR. apply IH.
  - (* MStar0 *) apply MStar0.
  - (* MStarApp *) apply MStarApp. apply IH1. apply IH2.
Qed.

Theorem app_length : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [reflexivity | simpl; rewrite IHlst1; reflexivity].
Qed.

Theorem app_length' : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
  [idtac | simpl; rewrite IHlst1];
  reflexivity.
Qed.

Theorem add_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros; induction n;
  [idtac | simpl; rewrite IHn];
  reflexivity.
Qed.

Lemma re_opt_e_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    (* Do the simpl for every case here: *)
    simpl.
  - (* MEmpty *) apply MEmpty.
  - (* MChar *) apply MChar.
  - (* MApp *)
    destruct re1;
    try (apply MApp; [apply IH1 | apply IH2]). (* <=== *)
    inversion Hmatch1. simpl. apply IH2.
  - (* MUnionL *) apply MUnionL. apply IH.
  - (* MUnionR *) apply MUnionR. apply IH.
  - (* MStar0 *) apply MStar0.
  - (* MStarApp *) apply MStarApp; [apply IH1 | apply IH2]. (* <=== *)
Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

Theorem ev100: ev 100.
Proof. 
 repeat (apply ev_SS).
 apply ev_0. Qed.

Fixpoint re_opt {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App _ EmptySet => EmptySet
  | App EmptyStr re2 => re_opt re2
  | App re1 EmptyStr => re_opt re1
  | App re1 re2 => App (re_opt re1) (re_opt re2)
  | Union EmptySet re2 => re_opt re2
  | Union re1 EmptySet => re_opt re1
  | Union re1 re2 => Union (re_opt re1) (re_opt re2)
  | Star EmptySet => EmptyStr
  | Star EmptyStr => EmptyStr
  | Star re => Star (re_opt re)
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char x => Char x
  end.

Lemma re_opt_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) simpl.
    destruct re1.
    + inversion IH1.
    + inversion IH1. simpl. destruct re2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r.  apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
  - (* MUnionL *) simpl.
    destruct re1.
    + inversion IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
  - (* MUnionR *) simpl.
    destruct re1.
    + apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
 - (* MStar0 *) simpl.
    destruct re.
    + apply MEmpty.
    + apply MEmpty.
    + apply MStar0.
    + apply MStar0.
    + apply MStar0.
    + simpl.
      destruct re.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
 - (* MStarApp *) simpl.
   destruct re.
   + inversion IH1.
   + inversion IH1. inversion IH2. apply MEmpty.
   + apply star_app.
     * apply MStar1. apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
Qed.



Lemma re_opt_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) 
    simpl;
    destruct re1;
    [inversion IH1 | inversion IH1; simpl; destruct re2; apply IH2 | | | |];
    (destruct re2;
    [inversion IH2 | inversion IH2; rewrite app_nil_r; apply IH1 | | | | ];
    (apply MApp; [apply IH1 | apply IH2])).
  - (* MUnionL *)
      simpl;
      destruct re1;
      [inversion IH | | | | |];
      destruct re2; try apply MUnionL; apply IH.
  - (* MUnionR *)
     simpl;
     destruct re1;
     [apply IH | | | | |];
     (destruct re2; [inversion IH | | | | |]; apply MUnionR; apply IH).
  - (* MStar0 *)
     simpl;
     destruct re; try apply MEmpty; try apply MStar0.
  - (* MStarApp *)
     simpl;
     destruct re;
     [inversion IH1 | inversion IH1; inversion IH2; apply MEmpty | | | |];
     (apply star_app; [apply MStar1; apply IH1 | apply IH2]).
Qed.

Theorem hyp_name : forall (P : Prop), P -> P.
Proof.
  intros P HP. apply HP.
Qed.

Theorem no_hyp_name : forall (P : Prop), P -> P.
Proof.
  intros. assumption.
Qed.


Theorem false_assumed : False -> 0 = 1.
Proof.
  intros H. destruct H.
Qed.


Theorem false_assumed' : False -> 0 = 1.
Proof.
  intros. contradiction.
Qed.


Theorem contras : forall (P : Prop), P -> ~ P -> 0 = 1.
Proof.
  intros P HP HNP. exfalso.  apply HNP. apply HP.
Qed.


Theorem contras' : forall (P : Prop), P -> ~ P -> 0 = 1.
Proof.
  intros. contradiction.
Qed.


Theorem many_eq : forall (n m o p : nat),
  n = m ->
  o = p ->
  [n; o] = [m; p].
Proof.
  intros n m o p Hnm Hop. rewrite Hnm. rewrite Hop. reflexivity.
Qed.


Theorem many_eq' : forall (n m o p : nat),
  n = m ->
  o = p ->
  [n; o] = [m; p].
Proof.
  intros. subst. reflexivity.
Qed.

Check ev_0.
Check ev_SS.

Example constructor_example: forall (n:nat),
    ev (n + n).
Proof.
  induction n; simpl.
  - constructor. (* applies ev_0 *)
  - rewrite add_comm. simpl. constructor. (* applies ev_SS *)
    assumption.
Qed.

From Coq Require Import Lia.

Theorem lia_succeed1 : forall (n : nat),
  n > 0 -> n * 2 > n.
Proof. lia. Qed.


Theorem lia_succeed2 : forall (n m : nat),
    n * m = m * n.
Proof.
  lia. (* solvable though non-linear *)
Qed.

Theorem lia_fail1 : 0 = 1.
Proof.
  Fail lia. (* goal is invalid *)
Abort.

Theorem lia_fail2 : forall (n : nat),
    n >= 1 -> 2 ^ n = 2 * 2 ^ (n - 1).
Proof.
  Fail lia. (*goal is non-linear, valid, but unsolvable by lia *)
Abort.

Require Import Ring.

Theorem mult_comm : forall (n m : nat),
    n * m = m * n.
Proof.
  intros n m. ring.
Qed.

Theorem eq_example1 :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  intros. rewrite H. reflexivity.
Qed.

Theorem eq_example1' :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  congruence.
Qed.


Theorem eq_example2 : forall (n m o p : nat),
    n = m ->
    o = p ->
    (n, o) = (m, p).
Proof.
  congruence.
Qed.


Theorem eq_example3 : forall (X : Type) (h : X) (t : list X),
    ~ ([] = h :: t).
Proof.
  congruence.
Qed.

Theorem intuition_succeed1 : forall (P : Prop),
    P -> P.
Proof. intuition. Qed.

Theorem intuition_succeed2 : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof. intuition. 
unfold not in H.
- unfold not.
intros.
apply H. left. apply H0.
- unfold not.
intros.
apply H. right. apply H0.
Qed.



Theorem intuition_simplify1 : forall (P : Prop),
    ~~P -> P.
Proof.
intuition. 
Abort.


Theorem intuition_simplify2 : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Proof.
  Fail congruence. (* the propositions stump it *)
  intuition. (* the = stumps it, but it simplifies the propositions *)
  congruence.
Qed.


Theorem intuition_simplify2' : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Proof.
  intuition congruence.
Qed.

Theorem plus_id_exercise_from_basics : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. 
  congruence.
Qed.


Theorem add_assoc_from_induction : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. 
  intros.
  ring.
Qed.


Theorem S_injective_from_tactics : forall (n m : nat),
  S n = S m ->
  n = m.
Proof. 
  intros.
  congruence.
Qed.

Theorem or_distributes_over_and_from_logic : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. 
  split.
  - intuition congruence.
  - intuition congruence.
Qed.

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.


Example auto_example_1' : forall (P Q R: Prop),
   (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.


Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, auto does nothing *)
  auto.
  (* Optional argument says how deep to search (default is 5) *)
  auto 6.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

Example auto_example_5 : 2 = 2.
Proof.
  (* auto subsumes reflexivity because eq_refl is in the hint
     database. *)
  info_auto.
Qed.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto using le_antisym.
Qed.

Create HintDb le_db.
Hint Resolve le_antisym : le_db.

Example auto_example_6' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto with le_db.
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* does nothing *)
Abort.

Hint Unfold is_fortytwo : le_db.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. info_auto with le_db. Qed.

Example auto_example_8 : forall (n m : nat),
    n + m = m + n.
Proof.
  auto. (* no progress *)
  info_auto with arith. (* uses Nat.add_comm *)
Qed.

Lemma re_opt_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) constructor. 
  - (* MChar *) constructor. 
  - (* MApp *) 
    simpl;
    destruct re1;
    [inversion IH1 | inversion IH1; simpl; destruct re2; auto | | | |];
    (destruct re2;
    [inversion IH2 | inversion IH2; rewrite app_nil_r; auto | | | | ];
    (constructor; auto)).
  - (* MUnionL *) 
     simpl;
     destruct re1;
     [inversion IH | | | | |];
     destruct re2; try apply MUnionL; auto.
  - (* MUnionR *)
     simpl;
     destruct re1;
     [auto | | | | |];
     (destruct re2; [inversion IH | | | | |]; apply MUnionR; auto).
  - (* MStar0 *) simpl;
    destruct re; constructor.
  - (* MStarApp *)  simpl;
     destruct re;
     [inversion IH1 | inversion IH1; inversion IH2; constructor | | | |];
     (apply star_app; [apply MStar1; auto | auto]).
Qed.

Import Pumping.

Create HintDb le_ari.
Hint Resolve app_assoc : le_ari.


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
  - simpl in G.
    + lia.
  - simpl in G.
    + lia.
  - simpl in G. rewrite app_length in G.
      assert (Q : pumping_constant re1 <= length s1 \/ pumping_constant re2 <= length s2).
      * lia.
      * destruct Q. apply IHexp_match1 in H1. destruct H1 as [s0 H1]. destruct H1 as [s3 H1].
        destruct H1 as [s4 H1]. exists s0. exists s3. exists (s4++s2).
        ** split. destruct H1. subst. rewrite <- app_assoc. rewrite <- app_assoc.
           reflexivity. destruct H1. destruct H2. split. auto.
           intros m.
assert (F:s0 ++ napp m s3 ++ s4 ++ s2 = (s0 ++ napp m s3 ++ s4)++ s2).
rewrite <- app_assoc. rewrite <- app_assoc.
reflexivity.  rewrite F. constructor. apply H3. assumption.
** apply IHexp_match2 in H1.
destruct H1 as [s0 H1]. destruct H1 as [s3 H1]. destruct H1 as [s4 H1].
exists (s1 ++ s0). exists s3. exists s4. split.
destruct H1. subst. rewrite <- app_assoc. reflexivity.
destruct H1. destruct H2. split. assumption.
intros m. rewrite <- app_assoc. constructor. assumption. apply H3.
- simpl in G.
assert (W: pumping_constant re1 <= length s1 /\ pumping_constant re2 <= length s1).
lia. destruct W. apply IHexp_match in H0.
destruct H0 as [s2 H0]. destruct H0 as [s3 H0]. destruct H0 as [s4 H0].
exists s2. exists s3. exists s4.
split. destruct H0. assumption.
split. destruct H0. destruct H2. assumption.
intros m. constructor.
destruct H0. destruct H2. apply H3.
- simpl in G.
assert (W: pumping_constant re1 <= length s2 /\ pumping_constant re2 <= length s2). lia.
destruct W. apply IHexp_match in H1.
destruct H1 as [s1 H1]. destruct H1 as [s3 H1]. destruct H1 as [s4 H1].
exists s1. exists s3. exists s4.
split. destruct H1. assumption. split.
destruct H1. destruct H2.
apply H2. destruct H1. destruct H2.
intros m.  apply MUnionR. apply H3.
- simpl in G. 
assert (Q:le 1 (pumping_constant re)). apply pumping_constant_ge_1. 
assert (W: 1<=0). lia. inversion W.
- exists []. exists (s1++s2). exists []. 
simpl. split. auto using app_nil_r.
split. unfold not. intros AND. 
rewrite AND in G. simpl in G. inversion G.
assert (Hp : (pumping_constant re) >= 1). 
{ apply pumping_constant_ge_1. }
assert (W: 1<=0). lia.
inversion W.
induction m. simpl. constructor. simpl. rewrite app_nil_r.
apply star_app. apply star_app. apply MStar1 in H. auto. auto. 
rewrite app_nil_r in IHm. assumption.
Qed.

Example trans_example1: forall a b c d,
    a <= b + b * c ->
    (1 + c) * b <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  apply le_trans with (b + b * c).
    (* ^ We must supply the intermediate value *)
  - apply H1.
  - simpl in H2. rewrite mul_comm. apply H2.
Qed.

Example trans_example1': forall a b c d,
    a <= b + b * c ->
    (1 + c) * b <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  eapply le_trans. (* 1 *)
  - apply H1. (* 2 *)
  - simpl in H2. rewrite mul_comm. apply H2.
Qed.


Example trans_example2: forall a b c d,
    a <= b + b * c ->
    b + b * c <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  info_eauto using le_trans.
Qed.

Ltac simpl_and_try tac := simpl; try tac.


Example sat_ex1 : 1 + 1 = 2.
Proof. simpl_and_try reflexivity. Qed.


Example sat_ex2 : forall (n : nat), 1 - 1 + n + 1 = 1 + n.
Proof. simpl_and_try reflexivity. lia. Qed.


Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n.
  - reflexivity.
  - reflexivity.
Qed.


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Ltac destructpf x :=
  destruct x; try reflexivity.

Theorem plus_1_neq_0' : forall n : nat,
    (n + 1) =? 0 = false.
Proof. intros n; destructpf n. Qed.

Theorem negb_involutive' : forall b : bool,
  negb (negb b) = b.
Proof. intros b; destructpf b. Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c; destructpf b; destructpf c.
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof. 
  intros b c d; destructpf b; destructpf c; destructpf d.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. intros H. destruct c eqn:Ec.
    + reflexivity.
    + rewrite H. reflexivity.
Qed.

Ltac destructpf' x :=
  destruct x; simpl; intros; try assumption; try reflexivity.

Theorem andb_true_elim2' : forall b c : bool,
    andb b c = true -> c = true.
Proof. 
   intros b c; destructpf' b. destructpf' c.
Qed.

Theorem andb3_exchange' :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros; destructpf' b. destructpf' c; destructpf' d.
Qed.

Theorem app_nil_r : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Proof.
  intros X lst. induction lst as [ | h t IHt].
  - reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

Theorem match_ex1 : True.
Proof.
  match goal with
  | [ |- True ] => apply I
  end.
Qed.

Theorem match_ex2 : True /\ True.
Proof.
  match goal with
  | [ |- True ] => apply I
  | [ |- True /\ True ] => split; apply I
  end.
Qed.

Theorem match_ex2' : True /\ True.
Proof.
  match goal with
  | [ |- True ] => idtac "branch 1"; apply I
  | [ |- True /\ True ] => idtac "branch 2"; split; apply I
  end.
Qed.

Fail Definition redundant_match (n : nat) : nat :=
  match n with
  | x => x
  | 0 => 1
  end.

Theorem match_ex2'' : True /\ True.
Proof.
  match goal with
  | [ |- _ ] => idtac "branch 1"; apply I
  | [ |- True /\ True ] => idtac "branch 2"; split; apply I
  end.
Qed.


Theorem match_ex2''' : True /\ True.
Proof.
  Fail match goal with
  | [ |- _ ] => idtac "branch 1"; apply I
  | [ |- _ ] => idtac "branch 2"; apply I
  end.
Abort.

Theorem match_ex3 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  match goal with
  | [ H : _ |- _ ] => apply H
  end.
Qed.

Theorem match_ex3' : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  match goal with
  | [ H : _ |- _ ] => idtac H; apply H
  end.
Qed.

Theorem match_ex4 : forall (P Q : Prop), P -> Q -> P.
Proof.
  intros P Q HP HQ.
  match goal with
  | [ H : _ |- _ ] => idtac H; apply H
  end.
Qed.

Theorem match_ex5 : forall (P Q R : Prop), P -> Q -> R.
Proof.
  intros P Q R HP HQ.
  Fail match goal with
  | [ H : _ |- _ ] => idtac H; apply H
  end.
Abort.

Theorem match_ex5 : forall (P Q : Prop), P -> Q -> P.
Proof.
  intros P Q HP HQ.
  match goal with
  | [ H : ?X |- ?X ] => idtac H; apply H
  end.
Qed.

Fail Definition dup_first_two_elts (lst : list nat) :=
  match lst with
  | x :: x :: _ => true
  | _ => false
  end.


Theorem app_nil_r' : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Proof.
  intros X lst. induction lst as [ | h t IHt].
  - reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

Ltac simple_induction t :=
  induction t; simpl;
  try match goal with
      | [H : _ = _ |- _] => rewrite H
      end;
  reflexivity.

Theorem app_nil_r'' : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Proof.
  intros X lst. simple_induction lst.
Qed.

Theorem add_assoc'' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.


Theorem add_assoc''' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. simple_induction n.
Qed.


Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.


Theorem plus_n_Sm' : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m. simple_induction n.
Qed.

Ltac imp_intuition :=
  repeat match goal with
         | [ H : ?P |- ?P ] => idtac H; apply H
         | [ |- forall _, _ ] => intro
         | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => idtac H1; idtac H2; apply H1 in H2
         end.

Example imp1 : forall (P : Prop), P -> P.
Proof. imp_intuition. Qed.

Example imp2 : forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof. imp_intuition. Qed.


Example imp3 : forall (P Q R : Prop), (P -> Q -> R) -> (Q -> P -> R).
Proof.  imp_intuition.  Qed.


Inductive nor (P Q : Prop) :=
| stroke : ~ P -> ~ Q -> nor P Q.

Theorem nor_not_or : forall (P Q : Prop),
    nor P Q -> ~ (P \/ Q).
Proof.

  intros. destruct H. unfold not. intros. destruct H. auto. auto.
Qed.

Theorem nor_comm : forall (P Q : Prop),
    nor P Q <-> nor Q P.
Proof.
  intros P Q. split.
  - intros H. destruct H. apply stroke; assumption.
  - intros H. destruct H. apply stroke; assumption.
Qed.


Theorem nor_not : forall (P : Prop),
    nor P P <-> ~ P.
Proof.
  intros P. split.
  - intros H. destruct H. assumption.
  - intros H. apply stroke; assumption.
Qed.

    Ltac nor_intuition :=
         repeat match goal with
         | [ H : ?P |- ?P ] => idtac H; apply H
         | [ |- forall _, _ ] => intro
         | [ |- _ <-> _ ] => split
         | [ |- ?P /\ ?Q ] => split
         | [ |- ~ ?P ] => unfold not
         | [ H: ~ ?P |- _ ] => unfold not in H
         | [ |- ~ ?P ] => unfold not
         | [ H: ?P \/ ?Q |- _ ] => destruct H
         | [ H: ?P /\ ?Q |- _ ] => destruct H
         | [ |- nor ?P ?Q ] => apply stroke
         | [ H: nor ?P ?Q |- _ ] => destruct H
         | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => idtac H1; idtac H2; apply H1 in H2
         end.

Theorem nor_not_or' : forall (P Q : Prop),
    nor P Q -> ~ (P \/ Q).
Proof. nor_intuition. Qed.

Theorem nor_comm' : forall (P Q : Prop),
    nor P Q <-> nor Q P.
Proof. nor_intuition. Qed.

Theorem nor_not' : forall (P : Prop),
    nor P P <-> ~ P.
Proof. nor_intuition. Qed.

Theorem nor_not_and' : forall (P Q : Prop),
    nor P Q -> ~ (P /\ Q).
Proof. nor_intuition. Qed.



