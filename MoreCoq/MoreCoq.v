Require Export Poly.

Theorem silly1 : forall(n m o p : nat),
    n = m ->
    [n;o] = [n;p] ->
    [n;o] = [m;p].
Proof.
    intros n m o p eq1 eq2.
    rewrite <- eq1.
    apply eq2.
Qed.

Theorem silly2 : forall(n m o p : nat),
    n = m ->
    (forall(q r : nat), q = r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].
Proof.
    intros n m o p eq1 eq2.
    apply eq2. apply eq1.
Qed.

Theorem silly2a : forall(n m : nat),
    (n, n) = (m, m) ->
    (forall(q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
    intros n m eq1 eq2.
    apply eq2. apply eq1.
Qed.

Theorem silly_ex :
    (forall n, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true ->
    oddb 4 = true.
Proof.
    intros.
    apply H.
    apply H0.
Qed.

Theorem silly3 : forall(n : nat),
    true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
    intros n H.
    symmetry.
    simpl.
    apply H.
Qed.

Theorem rev_exercise1: forall (l l' : list nat),
    l = rev l' ->
    l' = rev l.
Proof.
    intros.
    rewrite H.
    symmetry.
    apply rev_involutive.
Qed.

Example trans_eq_example : forall(a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
    intros a b c d e f eq1 eq2.
    rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Theorem trans_eq : forall(X:Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
    intros X n m o eq1 eq2. rewrite -> eq1.
    rewrite -> eq2. reflexivity.
Qed.

Example trans_eq_example' : forall(a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
    intros a b c d e f eq1 eq2.
    apply trans_eq with (m:=[c;d]).
    apply eq1.
    apply eq2.
Qed.

Example trans_eq_exercise : forall(n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
    intros n m o p eq1 eq2.
    apply trans_eq with (m := m).
    apply eq2.
    apply eq1.
Qed.

Theorem eq_add_S : forall(n m : nat),
    S n = S m ->
    n = m.
Proof.
    intros n m eq. inversion eq. reflexivity.
Qed.

Theorem silly4 : forall(n m : nat),
    [n] = [m] ->
    n = m.
Proof.
    intros n o eq. inversion eq. reflexivity.
Qed.

Theorem silly5 : forall(n m o : nat),
    [n;m] = [o;o] ->
    [n] = [m].
Proof.
    intros n m o eq. inversion eq. reflexivity.
Qed.

Example sillyex1 : forall(X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
    intros.
    inversion H0.
    reflexivity.
Qed.

Theorem silly6 : forall(n : nat),
    S n = O ->
    2 + 2 = 5.
Proof.
    intros n contra. inversion contra.
Qed.

Theorem silly7 : forall(n m : nat),
    false = true ->
    [n] = [m].
Proof.
    intros n m contra. inversion contra.
Qed.

Example sillyex2 : forall(X:Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
    intros X x y z l j contra1 contra2.
    inversion contra1.
Qed.

Theorem f_equal : forall(A B : Type) (f: A -> B) (x y : A),
    x = y -> f x = f y.
Proof.
    intros A B f x y eq.
    rewrite eq.
    reflexivity.
Qed.

Theorem length_snoc' : forall(X : Type) (v : X)
    (l : list X) (n : nat),
    length l = n ->
    length (snoc l v) = S n.
Proof.
    intros X v l. induction l as [| v' l'].
    Case "l = []". intros n eq. rewrite <- eq. reflexivity.
    Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
apply f_equal. apply IHl'. inversion eq. reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
    beq_nat 0 n = true -> n = 0.
Proof.
    intros n eq1.
    induction n as [| n'].
    Case "n = 0".
        reflexivity.
    Case "n = S n'".
        inversion eq1.
Qed.

Theorem beq_nat_0_r : forall n,
    beq_nat n 0 = true -> n = 0.
Proof.
    intros n eq1.
    induction n as [| n'].
    Case "n = 0".
        reflexivity.

    Case "n = S n'".
        inversion eq1.
Qed.

Theorem S_inj : forall(n m : nat) (b : bool),
    beq_nat (S n) (S m) = b ->
    beq_nat n m = b.
Proof.
    intros n m b H.
    simpl in H.
    apply H.
Qed.

Theorem silly3' : forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
        true = beq_nat n 5 ->
        true = beq_nat (S (S n)) 7.
Proof.
    intros n eq H.
    symmetry in H. apply eq in H. symmetry in H.
    apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m ->
    n = m.
Proof.
    intros n. induction n as [| n'].
    intros.
    simpl in H.
    destruct m.
        reflexivity.
        inversion H.

    intros.
    destruct m.
    inversion H.
    simpl in H.
    rewrite <- plus_n_Sm in H.
    rewrite <- plus_n_Sm in H.
    apply eq_add_S in H.
    apply eq_add_S in H.
    assert (n' = m) as Heq. apply IHn'. assumption.
    rewrite Heq.
    reflexivity.
Qed.

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
    intros n.
    induction n as [| n'].
    intros m eq.
    destruct m.
    reflexivity.

    inversion eq.

    intros m eq.
    destruct m as [| m'].
    inversion eq.

    apply f_equal.
    apply IHn'.
    inversion eq.
Qed.

