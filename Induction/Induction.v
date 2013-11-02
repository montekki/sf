Require Export Booleans.
Require Export Basics.
Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1: forall b c : bool,
    andb b c = true -> b = true.
Proof.
    intros b c H.
    destruct b.
    Case "b = true".
        reflexivity.
    Case "b = false".
        rewrite <- H.
        reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
      andb b c = true -> c = true.
Proof.
    intros b c H.
    destruct b.
    Case "b = true".
    rewrite <- H.
    reflexivity.
    Case "b = false".
    destruct c.
    trivial.
    trivial.
Qed.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
    intros n. induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
    intros n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
    intros n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
      S (n + m) = n + (S m).
Proof.
    intros n m. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
      n + m = m + n.
Proof.
    intros n m. induction n as [| n'].
    Case "n = 0".
        simpl. rewrite -> plus_0_r. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
      n + (m + p) = (n + m) + p.
Proof.
    intros n m p. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
    match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
    intros n.
    induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
      n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    assert (H: n + m = m + n).
    Case "Proof of assertion".
        rewrite -> plus_comm. reflexivity.
    rewrite -> H.
    reflexivity.
Qed.

Theorem mult_m_Sn : forall m n : nat,
    m * S n = m + m * n.
Proof.
    intros n m.
    induction n as [| n'].
    Case "n = 0".
    simpl. reflexivity.
    Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_swap. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
     m * n = n * m.
Proof.
    intros m n.
    induction n as [| n'].
    Case "n = 0".
    rewrite -> mult_0_r. reflexivity.
    Case "n = S n'".
    simpl.
    rewrite <- IHn'. rewrite -> mult_m_Sn. reflexivity.
Qed.

Theorem ble_nat_refl : forall n:nat,
      true = ble_nat n n.
Proof.
    intros n.
    induction n as [| n'].
    Case "n = 0".
    simpl. reflexivity.
    Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
      beq_nat 0 (S n) = false.
Proof.
    intros n.
    simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
    andb b false = false.
Proof.
    intros b.
    destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
    ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
    intros n m p.
    intros H.
    induction p as [| p'].
    Case "p = 0".
    simpl. rewrite -> H. reflexivity.
    Case "p = S p'".
    simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
    beq_nat (S n) 0 = false.
Proof.
    intros n.
    simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
    intros n.
    simpl.
    rewrite <- plus_comm.
    simpl.
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
    destruct c.
    destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl.
    destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
    intros n m p.
    induction n as [| n'].
    Case "n = 0".
    simpl. reflexivity.
    Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
    intros n m p.
    induction n as [| n'].
    Case "n = 0".
    simpl. reflexivity.
    Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.
