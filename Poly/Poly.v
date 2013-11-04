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



