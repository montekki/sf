Require Export Induction.

Module NatList.

Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

Eval compute in (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Eval compute in (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
    match p with
    | (x, y) => x
    end.

Definition snd' (p : natprod) : nat :=
    match p with
    | (x, y) => y
    end.

Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.

Theorem surjective_pairing' : forall (n m : nat),
    (n, m) = (fst (n, m), snd (n, m)).
Proof.
    reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
    p = (fst p, snd p).
Proof.
    simpl.
Abort.

Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
    intros p.
    destruct p as (m, n).
    simpl.
    reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
Proof.
    intros p.
    destruct p as (m, n).
    simpl.
    reflexivity.
Qed.

Theorem fst_swap_is_snd : forall(p : natprod),
    fst (swap_pair p) = snd p.
Proof.
    intros p.
    destruct p as (m, n).
    simpl.
    reflexivity.
Qed.

Inductive natlist : Type :=
    | nil : natlist
    | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.

Definition tl (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
            match h with
            | 0 => (nonzeros t)
            | h => h :: (nonzeros t)
            end
    end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
            match (oddb h) with
            | true => h :: oddmembers t
            | false => oddmembers t
            end
    end.

Example test_oddmembers : oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
    match l with
    | nil => O 
    | h :: t =>
            match (oddb h) with
            | true => S (countoddmembers t)
            | false => countoddmembers t
            end
    end.

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h1 :: t1 =>
            match l2 with
            | nil => h1 :: t1
            | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
            end
    end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4: alternate [] [20; 30] = [20; 30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint nat_eq (n m : nat) : bool :=
    match n with
    | O =>
            match m with
            | O => true
            | _ => false
            end
    | S n' =>
            match m with
            | O => false
            | S m' => nat_eq n' m'
            end
    end.

Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
    | nil => O
    | h :: t =>
            match (nat_eq h v) with
            | true => S (count v t)
            | flase => count v t
            end
    end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
    alternate.

Example test_sum1 : count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
    v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
    match (count v s) with
    | O => false
    | _ => true
    end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t =>
            match (nat_eq h v) with
            | true => t
            | false => h :: (remove_one v t)
            end
    end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t =>
            match (nat_eq h v) with
            | true => remove_all v t
            | false => h :: (remove_all v t)
            end
    end.


Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
    | nil => true
    | h :: t =>
            match (count h s2) with
            | O => false
            | c1 =>
                    match (ble_nat (count h s1) c1) with
                    | true => subset t s2
                    | false => false
                    end
            end
    end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem nil_app : forall l:natlist,
    [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
    pred (length l) = length (tl l).
Proof.
    intros l. destruct l as [| n l'].
    Case "l = nil".
        reflexivity.
    Case "l = cons n l'".
        reflexivity.
Qed.

Theorem app_ass : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros l1 l2 l3. induction l1 as [| n l1'].
    Case "l1 = nil".
        reflexivity.
    Case "l1 = cons n l1'".
        simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    intros l1 l2. induction l1 as [| n l1'].
    Case "l1 = nil".
        reflexivity.
    Case "l1 = cons".
        simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
    match l with
    | nil => [v]
    | h :: t => h :: (snoc t v)
    end.

Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => snoc (rev t) h
    end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
      length (rev l) = length l.
Proof.
    intros l. induction l as [| n l'].
    Case "l = []".
        reflexivity.
    Case "l = n :: l'".
        simpl.
        rewrite <- IHl'.
Abort.

Theorem length_snoc : forall n : nat, forall l:natlist,
    length (snoc l n) = S (length l).
Proof.
    intros n l. induction l as [| n' l'].
    Case "l = nil".
        reflexivity.
    Case "l = cons n' l'".
        simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
Proof.
    intros l. induction l as [| n l'].
    Case "l = nil".
        reflexivity.
    Case "l = cons".
        simpl. rewrite -> length_snoc.
        rewrite -> IHl'. reflexivity.
Qed.

Theorem app_nil_end : forall l : natlist,
      l ++ [] = l.
Proof.
    intros l.
    induction l as [| n l'].
    Case "l = nil".
        reflexivity.
    Case "l = n l'".
        simpl.  rewrite IHl'. reflexivity.
Qed.

Lemma rev_snoc : forall l : natlist, forall n : nat,
    rev(snoc l n) = n::rev(l).
Proof.
    intros l n.
    induction l as [| n' l'].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = n' l'".
        simpl. rewrite IHl'. simpl. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
Proof.
    intros l.
    induction l as [| l'].
    Case "l = nil".
        reflexivity. simpl.
    Case "l = n l'".
        rewrite -> rev_snoc. rewrite -> IHl. reflexivity.
Qed.

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
    intros.
    rewrite -> app_ass.
    rewrite -> app_ass.
    reflexivity.
Qed.

Theorem snoc_append : forall(l:natlist) (n:nat),
    snoc l n = l ++ [n].
Proof.
    intros.
    induction l as [| n' l'].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = n' l'".
        simpl. rewrite -> IHl'. reflexivity.
Qed.

Lemma app_empty: forall l1 : natlist,
    l1 ++ [] = l1.
Proof.
    intros l1.
    induction l1 as [| n l1'].
    Case "l1 = nil".
        reflexivity.
    Case "l1 = n' l1'".
        simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
    rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
    intros l1 l2.
    induction l1 as [| n' l1'].
    Case "l1 = nil".
        simpl. rewrite app_empty. reflexivity.
    Case "l1 = n' l1'".
        simpl. rewrite -> IHl1'. simpl.
        rewrite -> snoc_append.
        rewrite -> snoc_append.
        rewrite -> app_ass. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
    nonzeros(l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    intros.  induction l1 as [| n l1'].
    Case "l1 = nil".
        simpl. reflexivity.
    Case "l1 = n l1'".
        destruct n as [| n'].
            simpl. rewrite IHl1'. reflexivity.

            simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem count_number_nonzero : forall(s : bag),
    ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
    intros s.
    reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
    ble_nat n (S n) = true.
Proof.
    intros n. induction n as [| n'].
    Case "0".
        simpl. reflexivity.
    Case "S n'".
        simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_decreases_count : forall (s : bag),
    ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
    intros s. simpl.
    induction s as [| n' s'].
    Case "s = nil".
        simpl. reflexivity.

    Case "s = n' s'".
        destruct n' as [| n''].
            simpl. rewrite ble_n_Sn. reflexivity.

            simpl. rewrite IHs'. reflexivity.
Qed.

Theorem rev_inj : forall(l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
    intros l1 l2.
    intros H.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite rev_involutive.
    reflexivity.
Qed.

Inductive natoption : Type :=
    | Some : nat -> natoption
    | None : natoption.

Fixpoint index (n:nat) (l:natlist) : natoption :=
    match l with
    | nil => None
    | a :: l' => match beq_nat n 0 with
                 | true => Some a
                 | false => index (pred n) l'
                 end
    end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4;5;6;7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4;5;6;7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
    match l with
    | nil => None
    | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
    end.

Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.

Definition hd_opt (l : natlist) : natoption :=
    match l with
    | nil => None
    | h :: _ => Some h
    end.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall(l:natlist) (default:nat),
    hd default l = option_elim default (hd_opt l).
Proof.
    intros l default.
    destruct l as [| l'].
    simpl. reflexivity.

    simpl. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1 with
    | nil => match l2 with
             | nil => true
             | _ => false
             end
    | h1 :: t1 => match l2 with
                  | nil => false
                  | h2 :: t2 => if nat_eq h1 h2 then beq_natlist t1 t2 else false
                  end
    end.
Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Lemma nat_eq_same : forall (n : nat),
    nat_eq n n = true.
Proof.
    intros n.
    induction n as [| n'].
        reflexivity.

        simpl. rewrite IHn'. reflexivity.
Qed.

Theorem beq_natlist_refl : forall l : natlist,
    true = beq_natlist l l.
Proof.
    intros l.
    induction l as [| l'].
        reflexivity.

        simpl. rewrite nat_eq_same. rewrite IHl. reflexivity.

Qed.

Module Dictionary.

Inductive dictionary : Type :=
    | empty : dictionary
    | record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d: dictionary) : dictionary :=
    (record key value d).

Fixpoint find (key: nat) (d: dictionary) : natoption :=
    match d with
    | empty => None
    | record k v d' => if (beq_nat key k)
                        then (Some v)
                        else (find key d')
    end.

Theorem dictionary_invariant' : forall (d : dictionary) (k v: nat),
    (find k (insert k v d)) = Some v.
Proof.
    intros.
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.

Theorem dictionary_invariant2' : forall(d:dictionary) (m n o: nat),
    beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
    intros.
    simpl.
    rewrite H.
    reflexivity.
Qed.

End Dictionary.

End NatList.



