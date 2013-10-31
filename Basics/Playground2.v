Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat ) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
    end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.

Fixpoint factorial (n : nat) : nat :=
    match n with
    | O => S O
    | S n => mult (S n) (factorial n)
    end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y)
                        (at level 50, left associativity)
                        : nat_scope.
Notation "x - y" := (minus x y)
                        (at level 50, left associativity)
                        : nat_scope.

Notation "x * y" := (mult x y)
                        (at level 40, left associativity)
                        : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
    match n with
    | O => match m with
        | O => true
        | S m' => false
        end
    | S n' => match m with
        | O => false
        | S m' => beq_nat n' m'
        end
    end.

Fixpoint ble_nat (n m : nat) : bool :=
    match n with
    | O => true
    | S n' =>
        match m with
        | O => false
        | S m' => ble_nat n' m'
        end
    end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.

Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.

Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
    negb (ble_nat m n).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
    intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
    intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
    intros n. reflexivity. Qed.

Theorem plus_id_example: forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity. Qed.

Theorem plus_id_excercise: forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
    intros m n o.
    intros H.
    intros H2.
    rewrite -> H.
    rewrite -> H2.
    reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
    intros n m.
    rewrite -> plus_O_n.
    reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n ->
    m * (1 + n) = m * m.
Proof.
    intros n m.
    intros H.
    rewrite -> plus_1_l.
    rewrite -> H.
    reflexivity. Qed.

Theorem plus_1_neq_0 : forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
    intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
    intros b. destruct b.
    reflexivity.
    reflexivity. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    beq_nat 0 (n + 1) = false.
Proof.
    intros n. destruct n as [ | n'].
    reflexivity.
    reflexivity. Qed.

Theorem identity_fn_applied_twice:
    forall (f : bool -> bool),
    (forall(x : bool), f x = x) ->
    forall(b : bool), f (f b) = b.
Proof.
    intros f.
    intros H.
    intros b.
    rewrite -> H.
    rewrite -> H.
    reflexivity. Qed.


Theorem andb_eq_orb:
    forall(b c: bool),
    (andb b c = orb b c) -> 
    b = c.
Proof.
    intros b c.
    destruct b.
    destruct c.
    simpl.
    reflexivity.
    simpl.
    intro H.
    rewrite H.
    reflexivity.
    simpl.
    intro H.
    rewrite H.
    reflexivity.
Qed.

Inductive bin : Type :=
    | OO : bin 
    | M : bin -> bin 
    | I : bin -> bin.

Fixpoint inc (n : bin) : bin:=
    match n with
    | OO => I OO
    | I OO => M (I OO)
    | I (M b') => M (I b')
    | M b' => I (M b')
    | I (I b') => I (M (I b'))
    end.
    
Check OO.
Check I OO.
Check I (I OO).
Check inc OO.
Eval simpl in inc (I OO).

Example inc_test1: inc(M (I OO)) = I (M (I OO)).
Proof. reflexivity. Qed.

Fixpoint bin_to_un(b : bin) : nat :=
    match b with
    | OO => O
    | M b' => (2 * bin_to_un(b'))
    | I b' => S (bin_to_un(b'))
    end.

Eval simpl in bin_to_un(I (M (M (I OO)))).

Example test_bin_un1 : bin_to_un(I (M (M (I OO)))) = 5.
Proof. reflexivity. Qed.
