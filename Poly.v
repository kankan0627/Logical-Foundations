Require Export Lists.

Inductive boollist : Type :=
  |bool_nil
  |bool_cons (b : bool) (l : boollist).

Inductive list (X : Type) : Type :=
  |nil
  |cons (x : X) (l : list X).

Check list.

Check (nil nat).

Check (cons nat 3 (nil nat)).

Check nil.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X 
:=
  match count with
   |0 => nil X
   |S count' => cons X x (repeat X x count')
  end.

Check repeat.

Compute repeat nat 4 2.

Compute repeat bool false 1.

Module MumbleGrumble.

Inductive mumble : Type :=
    |a
    |b (x : mumble) (y : nat)
    |c.

Inductive grumble (X : Type) : Type :=
    |d (m : mumble)
    |e (x : X).

Check d mumble (b a 5).

Check d bool (b a 5).

Check e bool true.

Check  e mumble (b c 0).

Check  c.

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
   |0 => nil X
   |S count' => cons X x (repeat' X x count')
  end.

Check repeat'.  

Fixpoint repeat'' X x count : list X :=
  match count with
   |0 => nil _
   |S count' => cons _ x (repeat'' _ x count')
 end.

Check repeat''.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) 
: list X :=
  match count with
   |0 => nil
   |S count' => cons x (repeat''' x count')
  end.

Fixpoint app {X:Type} (l1 l2 : list X) : list X :=
  match l1 with 
   |nil => l2
   |cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
   match l with
    |nil => nil
    |cons h t => app (rev t) (cons h nil)
   end.


Fixpoint  length {X : Type} (l : list X) : nat :=
  match l with 
   |nil => 0
   |cons _ l' => S (length l')
  end.

Compute rev (cons 1 (cons 2 nil)).

Compute length (cons 1 (cons 2 (cons 3 nil))).

Definition mynil : list nat := nil.

Check nil.


Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X : Type), forall l : list X,
  l ++ [] = l.
Proof.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> IHl.
reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
induction l.
simpl.
reflexivity.
simpl.
intros m n.
rewrite -> IHl.
reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
induction l1.
simpl.
reflexivity.
simpl.
intros l2.
rewrite -> IHl1.
reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
induction l1.
simpl.
intros l2.
rewrite -> app_nil_r.
reflexivity.
simpl.
intros l2.
rewrite -> IHl1.
rewrite <- app_c.
reflexivity.
Qed.


Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> rev_app_distr.
rewrite -> IHl.
simpl.
reflexivity.
Qed.


Inductive prod (X Y : Type) : Type :=
  |pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
   | (x ,y) => x
 end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
   | (x ,y) => y
 end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
                      : list (X * Y) :=
 match lx, ly with
  |[], _ => []
  |_, [] => []
  |x :: tx, y :: ty => (x, y) :: (combine tx ty)
 end.

Check @combine.


Compute (combine [1;2] [false;false;true;true]).


Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with 
   |[] => ([],[])
   |(x, y) :: l' => (x::fst(split(l')), y::snd(split(l')))
  end.

Compute split [(1,false);(2,false)].

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  |Some (x : X)
  |None. 

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Check [1] :: [[2]].
Compute nth_error [[1];[2]] 1.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with 
   | nil => None
   | h :: t => Some h
 end.

Check @hd_error.

Compute hd_error [1;2].

Compute hd_error [[1];[2]].

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times.

Compute doit3times minustwo 9.

Compute doit3times negb true.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
   match l with 
    | [] => []
    | h :: t =>
        if test h then h :: (filter test t)
        else filter test t
  end.

Compute filter even [1;2;3;4].

Definition length_is_1 {X : Type} (l : list X) : bool :=
 (length l) =? 1.

Compute filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ].

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).

Definition fsquare (n : nat) : nat :=
n * n.

Example test_anon_fun':
  doit3times fsquare 2 = 256.
Proof. reflexivity. Qed.

Compute filter (fun l => (length l) =? 1) [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ].

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => ltb 7 x) (filter even l).

Compute filter_even_gt7 [1;2;6;9;10;3;12;8].

Compute  filter_even_gt7 [5;2;6;19;129].

Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
   (filter test l, filter (fun x => negb(test x)) l).
     
Compute partition odd [1;2;3;4;5].

Compute partition (fun x => false) [5;9;0].

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
 match l with 
  |[] => []
  |h::t => (f h) :: (map f t)
 end.

Compute map (fun x => plus 3 x) [2;0;2].

Compute map odd [2;1;2;5].

Compute map (fun n => [even n; odd n]) [2;1;2;5].

Lemma map_rev_aux : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
induction l1.
simpl.
reflexivity.
simpl.
intros l2.
rewrite <- IHl1.
reflexivity.
Qed.


Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> map_rev_aux.
simpl.
rewrite -> IHl.
reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with 
   |[] => []
   |h::t => app (f h) (flat_map f t)
  end.

Compute flat_map (fun n => [n;n+1;n+2]) [1;5;10].

Compute flat_map (fun n => [n;n;n]) [1;5;4].

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X): option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
   |nil => b
   |h :: t => f h (fold f t b)
  end.


Compute fold plus [1;2;3;4] 0.

Compute fold andb [true;true;false;true] true.

Definition constfun {X : Type} (x : X) :nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Compute ftrue 0.

Compute (constfun 5) 99.

Definition plus3 := plus 3.

Compute plus3 4.

Compute doit3times plus3 0.

Compute doit3times (plus 3) 0.

Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Compute fold_length [4;7;0].

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
induction l.
reflexivity.
simpl.
rewrite <- IHl.
reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
fold (fun x l => cons (f x) l) l nil.

Compute fold_map negb [false;false;true;true].

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
intros X Y Z f p.
assert (H : prod_uncurry (prod_curry f) p = (prod_curry f) (fst p) (snd p)).
reflexivity.
assert (L : prod_curry f (fst p) (snd p) = f ((fst p),(snd p)) ).
reflexivity.
assert (G : f ((fst p),(snd p)) = f p ).
induction p.
simpl.
reflexivity.
rewrite -> H.
rewrite -> L.
rewrite -> G.
reflexivity.
Qed.

Fixpoint nth_error {X: Type} (l : list X) (n : nat) : option X :=
  match l with 
   | [] => None
   | a::l' => if n =? 0 then Some a else nth_error l' (pred n)
  end.

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun(X :Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition zero' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => zero.

Definition one' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ zero.

Definition two' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

Compute zero nat S O.

Compute one nat S O.

Compute two nat S O.

Compute one nat plus3 4.

Definition three : cnat := @doit3times.

Definition scc (n : cnat) : cnat := 
     fun (X : Type) (f : X -> X) (x : X) => n X f (f x).

Compute scc two.
Compute scc zero.
Compute scc one.

Definition plus (n m : cnat) : cnat :=
     fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Compute plus two one.

Example plus_2 : plus two three = plus three two.
Proof.
reflexivity.
Qed.

Example plus_3 : plus (plus two two) three = plus one (plus three three).
Proof.
reflexivity.
Qed.

Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => m X (n X f) x.

Compute mult one three.

Definition exp (n m : cnat) : cnat :=
 fun (X : Type) => m (X -> X) (n X).

Compute exp three two.

End Church.
End Exercises.






