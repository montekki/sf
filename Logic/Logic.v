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

Theorem andb_prop : forall b c,
    andb b c = true -> b = true /\ c = true.
Proof.
    intros b c H.
    destruct b.
    Case "b = true". destruct c.
        SCase "c = true". apply conj. reflexivity. reflexivity.
        SCase "c = false". inversion H.
    Case "b = false". inversion H.
Qed.

Theorem andb_true_intro : forall b c,
    b = true /\ c = true -> andb b c = true.
Proof.
    intros b c H.
    inversion H.
    rewrite H0. rewrite H1. reflexivity.
Qed.

Theorem andb_false : forall b c,
    andb b c = false -> b = false \/ c = false.
Proof.
    intros b c H.
    destruct b.
    Case "b = true".
        simpl in H. right. apply H.

    Case "b = false".
        simpl in H. left. apply H.
Qed.

Theorem orb_prop : forall b c,
    orb b c = true -> b = true \/ c = true.
Proof.
    intros b c H.
    destruct b.
    Case "b = true".
        simpl in H. left. apply H.

    Case "b = false".
        simpl in H. right. apply H.
Qed.

Theorem orb_false_elim : forall b c,
    orb b c = false -> b = false /\ c = false.
Proof.
    intros b c H.
    destruct b.
    Case "b = true".
        inversion H.

    Case "b = false".
        simpl in H. split.
        SCase "left". reflexivity.
        SCase "right". apply H.
Qed.

Inductive False : Prop := .
Check tt.

Theorem False_implies_nonsense :
    False -> 2 + 2 = 5.
Proof.
    intros contra.
    inversion contra.
Qed.

Theorem ex_falso_quodlibet : forall(P:Prop),
    False -> P.
Proof.
    intros P contra.
    inversion contra.
Qed.

Inductive True : Prop := tt : True.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
    ~ False.
Proof.
    unfold not.
    intros H.
    inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
    intros P Q H.
    inversion H as [HP HNA]. unfold not in HNA.
    apply HNA in HP. inversion HP.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
    intros P H. unfold not. intros G. apply G. apply H.
Qed.

Theorem contrapositive : forall P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
intros P Q H NQ.
unfold not.
intros HP.
unfold not in NQ.
apply NQ in H.
    apply H.

    apply HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~ (P /\ ~P).
Proof.
    intros P.
    unfold not.
    intros H.
    inversion H as [HL HR].
    apply HR in HL.
    apply HL.
Qed.

Theorem five_not_even :
    ~ ev 5.
Proof.
    unfold not.
    intros H.
    inversion H.
    inversion H1.
    inversion H3.
Qed.

Theorem classic_double_neg : forall P : Prop,
    ~~P -> P.
Proof.
    intros P H. unfold not in H. Abort.


(*
    TODO: Exercise classical_axioms
*)

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
    b <> false -> b = true.
Proof.
    intros b H. destruct b.
    Case "b = true". reflexivity.
    Case "b = false".
        unfold not in H.
        apply ex_falso_quodlibet.
        apply H. reflexivity.
Qed.

Theorem false_beq_nat : forall n m : nat,
    n <> m ->
    beq_nat n m = false.
Proof. Admitted.

Theorem beq_nat_false : forall n m,
    beq_nat n m = false -> n <> m.
Proof. Admitted.

Theorem ble_nat_false : forall n m ,
    ble_nat n m = false -> ~(n <= m).
Proof. Admitted.

Inductive ex (X:Type) (P : X->Prop) : Prop :=
    ex_intro : forall(witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
    (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
    (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
    apply ex_intro with (witness:=2).
    reflexivity.
Qed.

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
    exists 2.
    reflexivity.
Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) ->
    (exists o, n = 2 + o).
Proof.
    intros n H.
    inversion H as [m Hm].
    exists(2 + m).
    apply Hm.
Qed.
