From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Locate "+".
Print Init.Nat.add.

Check String.eqb_refl :
 forall x : string, (x =? x)%string = true.

Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.

Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> ~ (n = m).

Check String.eqb_spec :
  forall x y : string, reflect (x = y) (String.eqb x y).

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true) "bar" true.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  intros.
  unfold t_empty.
  reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros.
  unfold t_update.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  ~ (x1 = x2) ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update.
  rewrite <- String.eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  apply functional_extensionality.
  intros x0.
  destruct ((x =? x0)%string) eqn:Hn.
   - apply String.eqb_eq in Hn. 
     rewrite Hn.
     rewrite -> t_update_eq.
     rewrite -> t_update_eq.
     reflexivity.
   - unfold t_update.
     rewrite Hn.
     reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
intros.
  apply functional_extensionality.
intros x0.
  destruct ((x =? x0)%string) eqn:Hn.
 - apply String.eqb_eq in Hn. 
     rewrite Hn.
     rewrite -> t_update_eq.
     reflexivity.
   - unfold t_update.
     rewrite Hn.
     reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
  ~ (x2 = x1) ->
  (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  destruct ((x1 =? x)%string) eqn:Hn1.
  - apply String.eqb_eq in Hn1. 
    rewrite Hn1.
    rewrite -> t_update_eq.
    rewrite Hn1 in H.
    rewrite <- String.eqb_neq in H.
    unfold t_update. 
    rewrite -> H.
    rewrite -> String.eqb_refl.
    reflexivity.
  - unfold t_update.
    rewrite -> Hn1.
    reflexivity.
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v : A) := 
                          (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).


Notation "x '|->' v" := (update empty x v) (at level 100).

Definition examplepmap := ("Church" |-> true ; "Turing" |-> false).

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof. 
  intros.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof. 
  intros.
  unfold update.
  rewrite -> t_update_eq.
  reflexivity.
Qed.

#[global] Hint Resolve update_eq : core.


Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  ~ (x2 = x1) -> (x2 |-> v ; m) x1 = m x1.
Proof. 
  intros.
  rewrite <- String.eqb_neq in H.
  unfold update.
  unfold t_update.
  rewrite -> H.
  reflexivity.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof. 
  intros.
  apply functional_extensionality.
  intros x0.
  destruct ((x =? x0)%string) eqn:Hn.
   - apply String.eqb_eq in Hn. 
     rewrite Hn.
     rewrite -> update_eq.
     rewrite -> update_eq.
     reflexivity.
   - unfold update.
     unfold t_update.
     rewrite -> Hn.
     reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v -> (x |-> v ; m) = m.
Proof. 
  intros.
  apply functional_extensionality.
  intros x0.
  destruct ((x =? x0)%string) eqn:Hn.
  - apply String.eqb_eq in Hn. 
    rewrite Hn.
    rewrite -> update_eq.
    rewrite Hn in H.
    rewrite H.
    reflexivity.
  - unfold update.
    unfold t_update.
    rewrite -> Hn.
    reflexivity.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A) x1 x2 v1 v2,
  ~ (x2 = x1) -> (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.  
  intros.
  apply functional_extensionality.
  intros x.
  destruct ((x1 =? x)%string) eqn:Hn1.
  - apply String.eqb_eq in Hn1. 
    rewrite Hn1.
    rewrite -> update_eq.
    rewrite Hn1 in H.
    rewrite <- String.eqb_neq in H.
    unfold update. 
    unfold t_update. 
    rewrite -> H.
    rewrite -> String.eqb_refl.
    reflexivity.
  - unfold update. 
    unfold t_update.
    rewrite -> Hn1.
    reflexivity.
Qed.

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : forall (A : Type) (m m' : partial_map A) (x : string) (vx : A),
  includedin m m' -> includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. 
    rewrite update_eq. 
    intro H1. 
    apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.





