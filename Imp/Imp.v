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

Example silly_presburger_example : forall m n o p,
    m + n <= n + o /\ o + 3 = p + 3 ->
    m <= p.
Proof.
    intros. omega.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum: forall(n: nat),
        aevalR (ANum n) n
    | E_APlus: forall(e1 e2: aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus: forall(e1 e2: aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMinus e1 e1) (n1 - n2)
    | E_AMult : forall(e1 e2: aexp) (n1 n2: nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMult e1 e2) (n1 * n2).

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum : forall(n:nat),
        (ANum n) || n
    | E_APlus : forall(e1 e2: aexp) (n1 n2 : nat),
        (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
    | E_AMinus : forall(e1 e2: aexp) (n1 n2 : nat),
        (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
    | E_AMult : forall(e1 e2: aexp) (n1 n2 : nat),
        (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

    where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
    | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
 split.
 Case "->".
   intros H.
   aevalR_cases (induction H) SCase; simpl.
   SCase "E_ANum".
     reflexivity.
   SCase "E_APlus".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase;
      simpl; intros; subst.
   SCase "ANum".
     apply E_ANum.
   SCase "APlus".
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMinus".
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
    (a || n) <-> aeval a = n.
Proof.
    split.
    Case "->".
        intros H; induction H; subst; reflexivity.
    Case "<-".
        generalize dependent n.
        induction a; simpl; intros; subst; constructor;
            try apply IHa1; try apply IHa2; reflexivity.
Qed.

Module aevalR_division.

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| ADiv : aexp -> aexp -> aexp.

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall(n:nat),
    (ANum n) || n
| E_APlus : forall(a1 a2 : aexp) (n1 n2 : nat),
    (a1 || n1) -> (a2 || n2) -> (APlus a1 a2 ) || (n1 + n2)
| E_AMinus : forall(a1 a2 : aexp) (n1 n2 : nat),
    (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
| E_AMult : forall(a1 a2 : aexp) (n1 n2 : nat),
    (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)
| E_ADiv : forall(a1 a2 : aexp) (n1 n2 n3 : nat),
    (a1 || n1) -> (a2 || n2) -> (mult n2 n3 = n1) -> (ADiv a1 a2) || n3

where "a '||' n" := (aevalR a n) : type_scope.
End aevalR_division.

Module aevalR_extended.
Inductive aexp : Type :=
| AAny : aexp
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.
Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall(n:nat),
      AAny || n (* <--- new *)
  | E_ANum : forall(n:nat),
      (ANum n) || n
  | E_APlus : forall(a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall(a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult : forall(a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_extended.

Module Id.

Inductive id : Type :=
    Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
    intros id1 id2.
    destruct id1 as [n1]. destruct id2 as [n2].
    destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
    Case "n1 = n2".
        left. rewrite Heq. reflexivity.
    Case "n1 <> n2".
        right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

Lemma eq_id : forall(T:Type) x (p q:T),
              (if eq_id_dec x x then p else q) = p.
Proof.
    intros.
    destruct (eq_id_dec x x).
    Case "x = x".
        reflexivity.
    Case "x <> x (impossible)".
        apply ex_falso_quodlibet; apply n; reflexivity.
Qed.

Lemma neq_id : forall(T:Type) x y (p q:T), x <> y ->
               (if eq_id_dec x y then p else q) = q.
Proof.
    intros.
    destruct (eq_id_dec x y).
    Case "x = y (impossible)".
        rewrite e in H.
        apply ex_falso_quodlibet.
        apply H.
        reflexivity.

    Case "x <> y".
        reflexivity.
Qed.

End Id.

Definition state := id -> nat.

Definition empty_state : state :=
    fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
    fun x' => if eq_id_dec x x' then n else st x'.

Theorem update_eq : forall n x st,
    (update st x n) x = n.
Proof.
    intros.
    unfold update.
    rewrite eq_id.
    reflexivity.
Qed.

Theorem update_neq : forall x2 x1 n st,
    x2 <> x1 ->
    (update st x2 n) x1 = (st x1).
Proof.
intros.
unfold update.
destruct (eq_id_dec x2 x1) as [Heq| Hneq].
    Case "x2 = x1 (impossible)".
        rewrite Heq in H.
        apply ex_falso_quodlibet.
        apply H.
        reflexivity.
    Case "x2 <> x1".
        reflexivity.
Qed.


Theorem update_example : forall(n:nat),
    (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
    intros.
    unfold update.
    simpl.
    unfold empty_state.
    reflexivity.
Qed.

Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
    (update (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
    intros.
    unfold update.
    destruct (eq_id_dec x2 x1) as [Heq| Hneq].
    Case "x2 = x1".
        reflexivity.
    Case "x2 <> x1".
        reflexivity.
Qed.

Theorem update_same : forall n1 x1 x2 (st : state),
    st x1 = n1 ->
    (update st x1 n1) x2 = st x2.
Proof.
    intros.
    unfold update.
    destruct (eq_id_dec x1 x2) as [Heq| Hneq].
    Case "x1 = x2".
        symmetry in H.
        rewrite H.
        apply f_equal.
        apply Heq.
    Case "x1 <> x2".
        reflexivity.
Qed.

Theorem update_permute : forall n1 n2 x1 x2 x3 st,
    x2 <> x1 ->
    (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
    intros.
    unfold update.
    destruct (eq_id_dec x1 x3) as [H1eq| H1neq].
    Case "x1 = x3".
        destruct (eq_id_dec x2 x3) as [H2eq| H2neq].
        SCase "x2 = x3".
            symmetry in H1eq.
            rewrite H1eq in H2eq.
            rewrite H2eq in H.
            apply ex_falso_quodlibet.
            apply H.
            reflexivity.
        SCase "x2 <> x3".
            reflexivity.
    Case "x1 <> x3".
        destruct (eq_id_dec x2 x3) as [H2eq| H2neq].
        SCase "x2 = x3".
            reflexivity.
        SCase "x2 <> x3".
            reflexivity.
Qed.
