Require Export MoreCoq.

Inductive beautiful : nat -> Prop :=
    b_0 : beautiful 0
  | b_3 : beautiful 3
  | b_5 : beautiful 5
  | b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem tree_is_beautiful: beautiful 3.
Proof.
    apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
    apply b_sum with (n:=3) (m:=5).
    apply b_3.
    apply b_5.
Qed.

Theorem beautiful_plus_eight : forall n, beautiful n -> beautiful (8+n).
Proof.
    intros n B.
    apply b_sum with (n:=8) (m:=n).
    apply eight_is_beautiful.
    apply B.
Qed.

Theorem b_timesm : forall n m, beautiful n -> beautiful (m*n).
Proof.
    intros n m B.
    induction m as [| m'].
    Case "m = 0".
        apply b_0.

    Case "m = S m'".
        simpl.
        apply b_sum with (n := n) (m := m' * n).
        apply B.
        apply IHm'.
Qed.

Inductive gorgeous : nat -> Prop :=
    g_0 : gorgeous 0
  | g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
  | g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

Theorem gorgeous_plus13: forall n,
    gorgeous n -> gorgeous(13+n).
Proof.
    intros n B.
    induction n as [| n'].
    Case "n = 0".
        simpl.
        apply g_plus3 with (n := 10).
        apply g_plus5 with (n := 5).
        apply g_plus5 with (n := 0).
        apply g_0.

    Case "n = S n'".
        apply g_plus5 with (n := 8 + S n').
        apply g_plus5 with (n := 3 + S n').
        apply g_plus3 with (n := S n').
        apply B.
Qed.

Theorem gorgeous__beautiful : forall n,
    gorgeous n -> beautiful n.
    Proof.
    intros n H.
    induction H as [| n'| n'].
    Case "g_0".
        apply b_0.

    Case "g_plus3".
        apply b_sum.
        apply b_3.

        apply IHgorgeous.

    Case "g_plus5".
        apply b_sum.
        apply b_5.

        apply IHgorgeous.
Qed.

Theorem gorgeous_sum : forall n m,
    gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
    intros n m B.
    intros B2.
    induction B as [| n'| n'].
    Case "g_0".
    simpl.
    apply B2.

    Case "g_plus3".
    apply g_plus3 with (n := n' + m).
    apply IHB.

    Case "g_plus5".
    apply g_plus5 with (n := n' + m).
    apply IHB.
Qed.

Theorem beautiful__gorgeous : forall n,
    beautiful n -> gorgeous n.
Proof.
    intros n B.
    induction B as [| n'| n'| n'].
    Case "b_0".
    apply g_0.

    Case "b_3".
    apply g_plus3.
    apply g_0.

    Case "b_5".
    apply g_plus5.
    apply g_0.

    Case "b_sum".
    apply gorgeous_sum.
    apply IHB1.

    apply IHB2.
Qed.

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
    intros x y z.
    replace (z + y) with (y + z) .
    rewrite <- plus_swap.
    replace (x + z) with (z + x) .
    apply plus_comm.

    apply plus_comm.


    apply plus_comm.
Qed.

Theorem g_times2 : forall n, gorgeous n -> gorgeous(2*n).
Proof.
intros n H.
simpl.
induction H.
 Case "g_0".
 apply g_0.

 Case "g_plus3".
 rewrite plus_0_r in IHgorgeous.
 rewrite plus_0_r.
 apply g_plus3 with (n := n + (3 + n)).
 rewrite helper_g_times2.
 apply g_plus3 with (n := n + n).
 apply IHgorgeous.

 Case "g_plus5".
 rewrite plus_0_r in IHgorgeous.
 apply g_plus5 with (n := n + (5 + n + 0)).
 rewrite helper_g_times2.
 apply g_plus5 with (n := n + n + 0).
 rewrite plus_0_r.
 apply IHgorgeous.
Qed.

Definition even (n:nat) : Prop :=
    evenb n = true.

Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem double_even : forall n,
    ev (double n).
Proof.
    intros n.
    induction n as [| n'].
    Case "n = 0".
        simpl. apply ev_0.

    Case "n = S n'".
        rewrite double_plus.
        rewrite <- plus_n_Sm.
        rewrite plus_comm.
        rewrite <- plus_n_Sm.
        apply ev_SS.
        rewrite double_plus in IHn'.
        apply IHn'.
Qed.

Theorem ev__even : forall n,
    ev n -> even n.
Proof.
    intros n E. induction E as [| n' E'].
    Case "E = ev_0".
        unfold even. reflexivity.
    Case "E = ev_SS n' E'".
        unfold even. apply IHE'.
Qed.

Theorem l : forall n,
    even n.
Proof.
    intros n. induction n.
    (*
     * In the second case of induction we will
     * end up with the need to prove S n = n
     *)
Abort.

Theorem ev_sum : forall n m,
    ev n -> ev m -> ev (n + m).
Proof.
    intros n m E1 E2.
    induction E1.
    Case "ev_0".
    rewrite plus_comm. rewrite plus_0_r. apply E2.

    Case "ev_SS".
    rewrite plus_comm. rewrite <- plus_n_Sm.
    rewrite <- plus_n_Sm. apply ev_SS.
    rewrite plus_comm. apply IHE1.
Qed.

Theorem ev_minus2 : forall n,
    ev n -> ev (pred (pred n)).
Proof.
    intros n E.
    inversion E as [| n' E'].
    Case "E = ev_0". simpl. apply ev_0.
    Case "E = ev_SS n' E'". simpl. apply E'.
Qed.

Theorem SSev_even : forall n,
    ev (S (S n)) -> ev n.
Proof.
    intros n E.
    inversion E as [| n' E'].
    apply E'.
Qed.

Theorem SSSSev__even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
    intros n E.
    inversion E as [| n' E'].
    inversion E' as [| n'' E''].
    apply E''.
Qed.
