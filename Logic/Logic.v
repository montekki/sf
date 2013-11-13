Require Export MoreProp.

Inductive and (P Q : Prop) : Prop :=
    conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example :
    (beautiful 0) /\ (beautiful 3).
Proof.
    apply conj.
    Case "left". apply b_0.
    Case "right". apply b_3.
Qed.

Theorem and_example' :
    (ev 0) /\ (ev 4).
Proof.
    split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
    intros P Q H.
    inversion H as [HP HQ].
    apply HP.
Qed.

Theorem proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
    intros P Q H.
    inversion H as [HP HQ].
    apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
    intros P Q H.
    inversion H.
    split.
        apply H1.

        apply H0.
Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    intros P Q R H.
    inversion H as (HP, (HQ, HR)).
    split.
    split.
        apply HP.

        apply HQ.

        apply HR.
Qed.

Theorem even__ev : forall n : nat,
    (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
    intros n.
    induction n as [| n'].
        split.
        intros H.
        apply ev_0.

        intros H1.
        inversion H1.

    inversion IHn' as (HP, HQ).
    split.
    apply HQ.

    intros J.
    apply ev_SS.
    apply HP.
    unfold even.
    unfold even in J.
    simpl in J.
    apply J.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity)
                        : type_scope.

Theorem iff_implies : forall P Q : Prop,
    (P <-> Q) -> P -> Q.
Proof.
    intros P Q H.
    inversion H as [HAB HBA].
    apply HAB.
Qed.

Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
    intros P Q H.
    inversion H as [HAB HBA].
    split.
    Case "->". apply HBA.
    Case "<-". apply HAB.
Qed.

Theorem iff_refl : forall P : Prop,
    P <-> P.

Proof.
    intros P.
    split.
    Case "->". intros J. apply J.
    Case "<-". intros J. apply J.
Qed.

Theorem iff_trans : forall P Q R : Prop,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. Admitted.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.
Check or_introl.

Check or_intror.

Theorem or_commut : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
    intros P Q H.
    inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.
Qed.

Theorem or_commut' : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
    intros P Q H.
    inversion H as [HP | HQ].
        Case "left". right. apply HP.
        Case "right". left. apply HQ.
Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
    P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
        SCase "left". left. apply HP.
        SCase "right". left. apply HP.
    Case "right". split.
        SCase "left". right. apply HQ.
        SCase "right". right. apply HR.
Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
    (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
    intros P Q R H.
    inversion H as [[HP1| HQ1] [HP2| HR1]].
    Case "leftleft".
        left. apply HP1.

    Case "left".
        left. apply HP1.

    Case "right".
        left. apply HP2.

    Case "rightright".
        right. split.
            SCase "left". apply HQ1.
            SCase "right". apply HR1.
Qed.
