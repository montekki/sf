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
