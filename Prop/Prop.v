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
