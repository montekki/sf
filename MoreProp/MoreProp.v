Require Export "Prop".

Inductive le : nat -> nat -> Prop :=
    | le_n : forall n, le n n
    | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
    3 <= 3.
Proof.
    apply le_n.
Qed.

Theorem test_le2 :
    3 <= 6.
Proof.
    apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Theorem test_le3 :
    (2 <= 1) -> 2 + 2 = 5.
Proof.
    intros H. inversion H. inversion H2.
Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
    sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
    | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
    | ne_1 : ev (S n) -> next_even n (S n)
    | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
    tr : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop :=
    er : forall n m : nat, 1 + 1 = 3 -> (empty_relation n m).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
    intros m n o H1 H2.
    induction H2.
    apply H1.

    apply le_S.
    apply IHle.
    apply H1.
Qed.

Theorem O_le_n : forall n,
    0 <= n.
Proof.
    intros n.
    induction n as [| n'].
    Case "n = 0".
        apply le_n.

    Case "n = S n'".
        apply le_S.
        apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
    n <= m -> S n <= S m.
Proof.
    intros n m E.
    induction E.
    apply le_n.

    apply le_S.
    apply IHE.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
    S n <= S m -> n <= m.
Proof. Admitted.

Theorem le_plus_l : forall a b,
    a <= a + b.
Proof.
    intros a b.
    induction a as [| a'].
    Case "a = 0".
        simpl. apply O_le_n.

    Case "a = S a'".
        rewrite plus_comm.
        rewrite <- plus_n_Sm.
        apply n_le_m__Sn_le_Sm.
        rewrite plus_comm.
        apply IHa'.
Qed.

Theorem plus_lt : forall n1 n2 m,
    n1 + n2 < m ->
    n1 < m /\ n2 < m.
Proof. Admitted.

Theorem lt_S : forall n m,
    n < m -> 
    n < S m.
Proof.
    unfold lt.
    intros n m H.
    apply le_S in H.
    apply H.
Qed.

Module R.
Inductive R : nat -> nat -> nat -> Prop :=
| c1 : R 0 0 0
| c2 : forall m n o, R m n o -> R (S m) n (S o)
| c3 : forall m n o, R m n o -> R m (S n) (S o)
| c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
| c5 : forall m n o, R m n o -> R n m o.


Example test_R1 : R 1 1 2.
Proof.
    apply c2.
    apply c3.
    apply c1.
Qed.

Example test_R2: R 2 2 6.
Proof. Abort.

(*
 If we removed c5 or c4 nothing would change, we never used it
 *)

End R.

Definition true_for_zero (P:nat -> Prop) : Prop :=
    P 0.

Definition true_for_all_numbers (P:nat -> Prop) : Prop :=
    forall n, P n.

Definition preserved_by_S (P:nat -> Prop) : Prop :=
    forall n', P n' -> P (S n').

Definition natural_number_induction_valid : Prop :=
    forall (P:nat -> Prop),
        true_for_zero P ->
        preserved_by_S P ->
        true_for_all_numbers P.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
    fun n => if (evenb n) then Peven n else Podd n.

Theorem combine_odd_even_intro :
    forall(Podd Peven : nat -> Prop) (n : nat),
        (oddb n = true -> Podd n) ->
        (oddb n = false -> Peven n) ->
        combine_odd_even Podd Peven n.
Proof.
    intros.
    unfold oddb in H, H0.
    induction n.
    unfold combine_odd_even.
    apply H0.
    reflexivity.

    unfold combine_odd_even.
    destruct evenb.
    apply H0.
    reflexivity.

    apply H.
    reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
    forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.

Proof.
    intros.
    unfold combine_odd_even in H.
    unfold oddb in H0.
    destruct evenb.
        inversion H0.

        apply H.
Qed.

Theorem combine_odd_even_elim_even :
    forall(Podd Peven : nat -> Prop) (n : nat),
        combine_odd_even Podd Peven n ->
        oddb n = false ->
        Peven n.
Proof.
    intros.
    unfold combine_odd_even in H.
    unfold oddb in H0.
    destruct evenb.
        apply H.

        inversion H0.
Qed.
