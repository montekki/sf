Require Export SfLib.

Module AExp.

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with
    | ANum n =>
        ANum n
    | APlus (ANum 0) e2 =>
        optimize_0plus e2
    | APlus e1 e2 =>
        APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 =>
        AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 =>
        AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
                    = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound : forall a,
    aeval (optimize_0plus a) = aeval a.

Proof.
  intros a. induction a.
  Case "ANum". reflexivity.
  Case "APlus". destruct a1.
    SCase "a1 = ANum n". destruct n.
      SSCase "n = 0". simpl. apply IHa2.
      SSCase "n <> 0". simpl. rewrite IHa2. reflexivity.
    SCase "a1 = APlus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMinus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMult a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Case "AMult".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem ev100 : ev 100.
Proof.
    repeat (apply ev_SS).
    apply ev_0.
Qed.

Theorem ev100' : ev 100.
Proof.
    repeat (apply ev_0).
    repeat (apply ev_SS). apply ev_0.
Qed.

Theorem silly1: forall ae, aeval ae = aeval ae.
Proof. try reflexivity. Qed.

Theorem silly2 : forall(P : Prop), P -> P.
Proof.
    intros P HP.
    try reflexivity.
    apply HP.
Qed.

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
    intros.
    destruct n.
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
Qed.

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
    intros.
    destruct n; simpl; reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  (* The remaining cases -- ANum and APlus -- are different *)
  Case "ANum". reflexivity.
  Case "APlus".
    destruct a1;
      (* Again, most cases follow directly by the IH *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the try... does nothing,
       is when e1 = ANum n. In this case, we have to destruct
       n (to see whether the optimization applies) and rewrite
       with the induction hypothesis. *)
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ANum" | Case_aux c "APlus"
    | Case_aux c "AMinus" | Case_aux c "AMult" ].

Theorem optimize_0plus_sound''' : forall a,
    aeval (optimize_0plus a) = aeval a.
Proof.
    intros a.
    aexp_cases (induction a) Case;
        try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
        try reflexivity;
    Case "APlus".
        aexp_cases (destruct a1) SCase;
            try (simpl; simpl in IHa1;
                 rewrite IHa1; rewrite IHa2; reflexivity).
        SCase "ANum". destruct n;
            simpl; rewrite IHa2; reflexivity.
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

Theorem optimize_0plus_b_sound : forall b,
    beval (optimize_0plus_b b) = beval b.
Proof.
    intros b.
    induction b.
    Case "BTrue".
        reflexivity.
    Case "BFalse".
        reflexivity.
    Case "BEq".
        simpl.
        rewrite optimize_0plus_sound.
        rewrite optimize_0plus_sound.
        reflexivity.
    Case "BLe".
        simpl.
        rewrite optimize_0plus_sound.
        rewrite optimize_0plus_sound.
        reflexivity.
    Case "BNot".
        simpl.
        rewrite IHb.
        reflexivity.
    Case "BAnd".
        simpl.
        rewrite IHb1.
        rewrite IHb2.
        reflexivity.
Qed.

Theorem optimize_0plus_b_sound' : forall b,
    beval (optimize_0plus_b b) = beval b.
Proof.
    intros b.
    induction b;
        try (simpl; rewrite 2 optimize_0plus_sound);
        try reflexivity.
    Case "BNot".
        simpl. rewrite IHb. reflexivity.
    Case "BAnd".
        simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.
