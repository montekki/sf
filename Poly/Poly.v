Require Export Lists.

Inductive boollist : Type :=
    | bool_nil : boollist
    | bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
    | nil : list X
    | cons : X -> list X -> list X.

Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 ( nil nat ))).

Fixpoint length (X:Type) (l:list X) : nat :=
    match l with
    | nil => 0
    | cons h t => S (length X t)
    end.

Example test_length2 :
        length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.
Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
    match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
    end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
    match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
    end.

Fixpoint rev (X:Type) (l:list X) : list X :=
    match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
    end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Fixpoint app' X l1 l2 : list X :=
    match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
    end.

Check app'.
Check app.

Fixpoint length' (X:Type) (l:list X) : nat :=
    match l with
    | nil => 0
    | cons h t => S (length' _ t)
    end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
    match l with
    | nil => 0
    | cons h t => S (length'' t)
    end.

Definition mynil : list nat := nil.

Check @nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                         (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                         (at level 60, right associativity).

Definition list123''' := [1;2;3].

Fixpoint repeat {X:Type} (n:X) (count : nat) : list X :=
    match count with
    | 0 => nil
    | S count' => n :: (repeat n count')
    end.

Example test_repeat1:
    repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.


Theorem nil_app : forall X : Type , forall l : list X,
    app [] l = l.
Proof.
    intros.
    reflexivity.
Qed.


Theorem rev_snoc : forall X : Type,
                   forall v : X,
                   forall s : list X,
        rev (snoc s v) = v :: (rev s).
Proof.
    intros.
    simpl.
    induction s as [| n' s'].
        reflexivity.

        simpl. rewrite IHs'. simpl. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
    rev (rev l) = l.
Proof.
    intros.
    induction l as [| n' l'].
    reflexivity.

    simpl. rewrite rev_snoc. rewrite IHl'. reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type,
                        forall l1 l2 : list X,
                        forall v : X,
            snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
    intros.
    induction l1 as [| n' l1'].
    reflexivity.

    simpl. rewrite IHl1'. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
    pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X*Y) :X :=
    match p with (x, y) => x end.

Definition snd {X Y : Type} (p : X*Y) :Y :=
    match p with (x, y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
    : list (X*Y) :=
    match (lx, ly) with
    | ([], _) => []
    | (_, []) => []
    | (x::tx, y::ty) => (x,y) :: (combine tx ty)
    end.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
    match l with
    | [] => ([],[])
    | (h1, h2) :: t => (h1 :: (fst (split t)), h2 :: (snd (split t)))
    end.

Example test_split:
    split [(1,false);(2, false)] = ([1;2],[false; false]).
Proof. reflexivity. Qed.

Inductive option (X:Type) : Type :=
    | Some : X -> option X
    | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
        match l with
        | [] => None
        | a :: l' => if beq_nat n 0 then Some a else index (pred n) l'
        end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X :=
    match l with
    | nil => None
    | h :: _ => Some h
    end.

Example test_hd_opt1 : hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
    f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Check plus.
Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
    (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
    (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
    intros.
    reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof.
    intros.
    destruct p as [x y].
    reflexivity.
Qed.


Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
    : (list X) :=
    match l with
    | [] => []
    | h :: t => if test h then h :: (filter test t)
            else filter test t
    end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
    beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
    [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
    = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
      length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
    doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
        [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
    filter (fun n => andb (ble_nat 7 n) (evenb n)) l.

Eval compute in filter_even_gt7 [1;2;6;9;10;3;12;8].

Example test_filter_even_gt7_1 :
      filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
      filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X)
                         : list X * list X :=
            (filter (test) l, filter (fun n => negb (test n)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
