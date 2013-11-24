Require Export Logic.

Print beautiful.
Check b_sum.

Theorem eight_is_beautiful: beautiful 8.
Proof.
    apply b_sum with (n := 3) (m := 5).
    apply b_3.
    apply b_5. Qed.

Print eight_is_beautiful.
Check (b_sum 3 5 b_3 b_5).

Theorem eight_is_beautiful': beautiful 8.
Proof.
    apply (b_sum 3 5 b_3 b_5).
Qed.

Theorem eight_is_beautiful'': beautiful 8.
Proof.
    Show Proof.
    apply b_sum with (n:=3) (m:=5).
    Show Proof.
    apply b_3.
    Show Proof.
    apply b_5.
    Show Proof.
Qed.

Definition eight_is_beautiful''' : beautiful 8 :=
    b_sum 3 5 b_3 b_5.

Print eight_is_beautiful.
Print eight_is_beautiful'.
Print eight_is_beautiful''.
Print eight_is_beautiful'''.

Theorem six_is_beautiful : beautiful 6.
Proof.
    apply b_sum with (n:=3) (m:=3).
    apply b_3.
    apply b_3.
Qed.

Definition six_is_beautiful' : beautiful 6 :=
    b_sum 3 3 b_3 b_3.

Theorem nine_is_beautiful :
    beautiful 9.
Proof.
    apply b_sum with (n:=3) (m:=6).
    apply b_3.
    apply six_is_beautiful.
Qed.

Definition nine_is_beautiful' : beautiful 9 :=
    b_sum 3 6 b_3 six_is_beautiful'.

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
    intros n H.
    apply b_sum.
    apply b_3.
    apply H.
Qed.

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) :=
    fun (n : nat) => fun (H : beautiful n) =>
        b_sum 3 n b_3 H.

Check b_plus3'.

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) :=
    b_sum 3 n b_3 H.

Check b_plus3''.

Definition beautiful_plus3 : Prop :=
    forall n, forall(E : beautiful n), beautiful (n+3).

Definition beautiful_plus3' : Prop :=
    forall n, forall(_ : beautiful n), beautiful (n+3).

Definition beatufiul_plus3'' : Prop :=
    forall n, beautiful n -> beautiful (n+3).

(* "P -> Q" is a syntatic sugar for "forall (_:P), Q" *)

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    intros.
    simpl.
    apply b_sum.
        Case "n".
            apply H.
        Case "n + 0".
            apply b_sum.
            SCase "n". apply H.

            SCase "0". apply b_0.
Qed.

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
    fun (n : nat) => fun (H : beautiful n) =>
        b_sum n (n+0) H (b_sum n 0 H b_0).

Definition gorgeous_plus13_po : forall n, gorgeous n -> gorgeous (13+n) :=
    fun (n : nat) => fun (H : gorgeous n) =>
        g_plus5 (8+n) (g_plus5 (3+n) (g_plus3 n H)).

Theorem and_example :
    (beautiful 0) /\ (beautiful 3).
Proof.
    apply conj.
        apply b_0.
        apply b_3.
Qed.

Print and_example.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
    intros P Q H.
    inversion H as [HP HQ].
    split.
        Case "left". apply HQ.
        Case "right". apply HP.
Qed.

Print and_commut.

Check plus_comm.

Lemma plus_comm_r : forall a b c, c + (b + a) = c + (a + b).
Proof.
    intros a b c.
    (* rewrite plus_comm *)
        (* rewrites in the first possible spot; not what we want *)
    rewrite (plus_comm b a). (* directs rewriting to the right spot *)
    reflexivity.
Qed.

(* In this case giving just one argument would be sufficient *)
Lemma plus_comm_r' : forall a b c, c + (b + a) = c + (a + b).
Proof.
    intros a b c.
    rewrite (plus_comm b).
    reflexivity.
Qed.

(* Arguments must be given in order, but wildcards (_) may be used to
    * skip arguments that Coq can infer *)
Lemma plus_comm_r'' : forall a b c, c + (b + a) = c + (a + b).
Proof.
    intros a b c.
    rewrite (plus_comm _ a).
    reflexivity.
Qed.

Lemma plus_comm_r''' : forall a b c, c + (b + a) = c + (a + b).
Proof.
    intros a b c.
    rewrite plus_comm with (n := b).
    reflexivity.
Qed.
