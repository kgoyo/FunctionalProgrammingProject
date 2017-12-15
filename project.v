Require Import Arith.

Inductive tree23 : Type :=
  | empty : tree23
  | node2 : nat -> tree23 -> tree23 -> tree23
  | node3 : nat -> nat -> tree23 -> tree23 -> tree23 -> tree23
.

Fixpoint search23tree (sk:nat) (n:tree23) : bool :=
  match n with
  | empty => false
  | node2 k n1 n2 => 
    match Nat.compare sk k with
    | Eq => true
    | Lt => search23tree sk n1
    | Gt => search23tree sk n2
    end
  | node3 k1 k2 n1 n2 n3 =>
    match Nat.compare sk k1 , Nat.compare sk k2 with
    | Eq,_ => true
    | _,Eq => true
    | Lt,_ => search23tree sk n1
    | _,Gt => search23tree sk n3
    | _,_ => search23tree sk n2
    end
  end.

(*Test cases for search *)

Example searchtest1: search23tree 2 empty = false.
Proof. reflexivity. Qed.

Example searchtest2: search23tree 2 (node2 2 empty empty) = true.
Proof. reflexivity. Qed.

Example searchtest3: search23tree 1 (node2 2 empty empty) = false.
Proof. reflexivity. Qed.

Example searchtest4: search23tree 3 (node2 2 empty empty) = false.
Proof. reflexivity. Qed.

Example searchtest5: search23tree 2 (node3 2 4 empty empty empty) = true.
Proof. reflexivity. Qed.

Example searchtest6: search23tree 4 (node3 2 4 empty empty empty) = true.
Proof. reflexivity. Qed.

Example searchtest7: search23tree 1 (node3 2 4 empty empty empty) = false.
Proof. reflexivity. Qed.

Example searchtest8: search23tree 3 (node3 2 4 empty empty empty) = false.
Proof. reflexivity. Qed.

Example searchtest9: search23tree 5 (node3 2 4 empty empty empty) = false.
Proof. reflexivity. Qed.




(* new search *)
Inductive insertResult : Set :=
  | irTree : tree23 -> insertResult
  | irSplit : tree23 -> nat -> tree23 -> insertResult.


Fixpoint insertHelper (k:nat) (t:tree23) : insertResult :=

  match t with

  (* base cases *)

  | empty => irSplit empty k empty

  | node2 n empty empty =>
    match Nat.leb k n with
    | true  => irTree (node3 k n empty empty empty)
    | false => irTree (node3 n k empty empty empty)
    end

  | node3 n1 n2 empty empty empty =>
    match Nat.leb k n2 with
      | true  =>
        match Nat.leb k n1 with
        | true  => irSplit (node2 k empty empty) n1 (node2 n2 empty empty) (* k is smallest *)
        | false => irSplit (node2 n1 empty empty) k (node2 n2 empty empty) (* k is middle *)
        end
      |   false => irSplit (node2 n1 empty empty) n2 (node2 k empty empty)   (* k is largest *)
    end

  (* recursive cases *)

  | node2 n t1 t2 =>
    match Nat.leb k n with
    | true  =>
      match (insertHelper k t1) with
      | irTree t1' =>      irTree (node2 n t1' t2)
      | irSplit w1 m w2 => irTree (node3 m n w1 w2 t2)
      end
    | false =>
      match (insertHelper k t2) with
      | irTree t2' =>      irTree (node2 n t1 t2')
      | irSplit w1 m w2 => irTree (node3 n m t1 w1 w2)
      end
    end

  | node3 n1 n2 t1 t2 t3 =>
    match Nat.leb k n2 with
    | true  =>
      match Nat.leb k n1 with
      | true  => (* k is smallest *)
        match (insertHelper k t1) with
        | irTree t1' =>      irTree (node3 n1 n2 t1' t2 t3)
        | irSplit w1 m w2 => irSplit (node2 m w1 w2) n1 (node2 n2 t2 t3)
        end
      | false =>  (* k is middle *)
        match (insertHelper k t2) with
        | irTree t2' =>      irTree (node3 n1 n2 t1 t2' t3)
        | irSplit w1 m w2 => irSplit (node2 n1 t1 w1) m (node2 n2 w2 t3)
        end
      end
    | false => (* k is largest *)
        match (insertHelper k t3) with
        | irTree t3' =>      irTree (node3 n1 n2 t1 t2 t3')
        | irSplit w1 m w2 => irSplit (node2 n1 t1 t2) n2 (node2 m w1 w2)
        end
    end
  end.

Definition insert23tree (k:nat) (t:tree23) : tree23 :=
  match (insertHelper k t) with
  | irTree t' => t'
  | irSplit w1 m w2 => (node2 m w1 w2)
  end.


(* Test cases for search *)

(* leaf cases *)



Example insertTest1: insert23tree 2 empty = node2 2 empty empty.
Proof. reflexivity. Qed.

Example insertTest2: insert23tree 2 (node2 1 empty empty) =
                                     node3 1 2 empty empty empty.
Proof. reflexivity. Qed.

Example insertTest3: insert23tree 2 (node2 3 empty empty) =
                                     node3 2 3 empty empty empty.
Proof. reflexivity. Qed.

Example insertTest4: insert23tree 3 (node3 2 4 empty empty empty) =
                                     node2 3 (node2 2 empty empty) (node2 4 empty empty).
Proof. reflexivity. Qed.

Example insertTest5: insert23tree 1 (node3 2 4 empty empty empty) =
                                     node2 2 (node2 1 empty empty) (node2 4 empty empty).
Proof. reflexivity. Qed.

Example insertTest6: insert23tree 5 (node3 2 4 empty empty empty) =
                                     node2 4 (node2 2 empty empty) (node2 5 empty empty).
Proof. reflexivity. Qed.

(* node cases *)

(* node2 *)

Example insertTest7: insert23tree 4 (node2 5 (node2 3 empty empty) (node2 7 empty empty)) =
                                     node2 5 (node3 3 4 empty empty empty) (node2 7 empty empty).
Proof. reflexivity. Qed.

Example insertTest8: insert23tree 6 (node2 5 (node2 3 empty empty) (node2 7 empty empty)) =
                                     node2 5 (node2 3 empty empty) (node3 6 7 empty empty empty).
Proof. reflexivity. Qed.

Example insertTest9: insert23tree 4 (node2 5 (node3 2 3 empty empty empty) (node2 7 empty empty)) =
                                     node3 3 5 (node2 2 empty empty) (node2 4 empty empty) (node2 7 empty empty).
Proof. reflexivity. Qed.

Example insertTest10: insert23tree 6 (node2 5 (node2 3 empty empty) (node3 7 8 empty empty empty)) =
                                      node3 5 7 (node2 3 empty empty) (node2 6 empty empty) (node2 8 empty empty).
Proof. reflexivity. Qed.

(* node3 *)

Example insertTest11: insert23tree 2 (node3 4 8 (node2 3 empty empty) (node2 5 empty empty) (node2 9 empty empty)) =
                                      node3 4 8 (node3 2 3 empty empty empty) (node2 5 empty empty) (node2 9 empty empty).
Proof. reflexivity. Qed.

Example insertTest12: insert23tree 6 (node3 4 8 (node2 3 empty empty) (node2 5 empty empty) (node2 9 empty empty)) =
                                      node3 4 8 (node2 3 empty empty) (node3 5 6 empty empty empty) (node2 9 empty empty).
Proof. reflexivity. Qed.

Example insertTest13: insert23tree 10 (node3 4 8 (node2 3 empty empty) (node2 5 empty empty) (node2 9 empty empty)) =
                                       node3 4 8 (node2 3 empty empty) (node2 5 empty empty) (node3 9 10 empty empty empty).
Proof. reflexivity. Qed.

Example insertTest14: insert23tree 2 (node3 4 8 (node3 1 3 empty empty empty) (node2 5 empty empty) (node2 9 empty empty)) =
                                      node2 4 (node2 2 (node2 1 empty empty) (node2 3 empty empty)) (node2 8 (node2 5 empty empty) (node2 9 empty empty)).
Proof. reflexivity. Qed.

Example insertTest15: insert23tree 6 (node3 4 8 (node2 3 empty empty) (node3 5 7 empty empty empty) (node2 9 empty empty)) =
                                      node2 6 (node2 4 (node2 3 empty empty) (node2 5 empty empty)) (node2 8 (node2 7 empty empty) (node2 9 empty empty)).
Proof. reflexivity. Qed.

Example insertTest16: insert23tree 10 (node3 4 8 (node2 3 empty empty) (node2 5 empty empty) (node3 9 11 empty empty empty)) =
                                       node2 8 (node2 4 (node2 3 empty empty) (node2 5 empty empty)) (node2 10 (node2 9 empty empty) (node2 11 empty empty)).
Proof. reflexivity. Qed.


Inductive keyIn : nat -> tree23 -> Prop :=
  | In2_match : forall k t1 t2, keyIn k (node2 k t1 t2)
  | In2_left : forall k n t1 t2, keyIn k t1 -> keyIn k (node2 n t1 t2)
  | In2_right : forall k n t1 t2, keyIn k t2 -> keyIn k (node2 n t1 t2)

  | In3_match1 : forall k k2 t1 t2 t3, keyIn k (node3 k k2 t1 t2 t3)
  | In3_match2 : forall k k1 t1 t2 t3, keyIn k (node3 k1 k t1 t2 t3)
  | In3_left : forall k k1 k2 t1 t2 t3, keyIn k t1 -> keyIn k (node3 k1 k2 t1 t2 t3)
  | In3_middle : forall k k1 k2 t1 t2 t3, keyIn k t2 -> keyIn k (node3 k1 k2 t1 t2 t3)
  | In3_right : forall k k1 k2 t1 t2 t3, keyIn k t3 -> keyIn k (node3 k1 k2 t1 t2 t3).

Inductive Balanced': nat -> tree23 -> Prop :=
  | b_treeEmpty : Balanced' 0 empty
  | b_tree2 : forall k n t1 t2, Balanced' n t1 -> Balanced' n t2 -> Balanced' (S n) (node2 k t1 t2)
  | b_tree3 : forall k1 k2 n t1 t2 t3, Balanced' n t1 -> Balanced' n t2 -> Balanced' n t3 -> Balanced' (S n) (node3 k1 k2 t1 t2 t3).


Inductive Balanced : tree23 -> Prop :=
  | bal : forall t n, Balanced' n t -> Balanced t.

Definition k_inBounds (k:nat) (l: option nat) (u: option nat) : Prop :=
  (match l with
   | Some l' => l' <= k
   | None => True
   end)
   /\
  (match u with
   | Some u' => k <= u'
   | None => True
   end).

Definition correct_Bounds (l u : option nat) : Prop :=
  match l with
  | None => True
  | Some l' => match u with
               | None => True
               | Some u' => l' <= u'
               end
  end.
Inductive SearchTree' : option nat -> option nat -> tree23 -> Prop :=
  | srch_empty : forall o1 o2, correct_Bounds o1 o2 -> SearchTree' o1 o2 empty
  | srch_node2 : forall k t1 t2 lower upper,
        SearchTree' lower (Some k) t1 ->
        SearchTree' (Some k) upper t2 ->
        k_inBounds k lower upper ->
        SearchTree' lower upper (node2 k t1 t2)
  | srch_node3 : forall k1 k2 t1 t2 t3 lower upper,
        SearchTree' lower (Some k1) t1 ->
        SearchTree' (Some k1) (Some k2) t2 ->
        SearchTree' (Some k2) upper t3 ->
        k1 <= k2 ->
        k_inBounds k1 lower upper ->
        k_inBounds k2 lower upper ->
        SearchTree' lower upper (node3 k1 k2 t1 t2 t3).

Inductive SearchTree : tree23 -> Prop :=
  | srch : forall t lower upper, SearchTree' lower upper t -> SearchTree t.


(* new min and max that handle None as no bound *)

Definition min' (a:nat) (b:option nat) : option nat :=
  match b with
  | None => None
  | Some b' => Some (min a b')
  end.

Definition max' (a:nat) (b:option nat) : option nat :=
  match b with
  | None => None
  | Some b' => Some (max a b')
  end.

(* proofs *)



Lemma Search_node2_conj :
  forall n t1 t2, SearchTree (node2 n t1 t2) -> SearchTree t1 /\ SearchTree t2.
Proof.
intros.
inversion H; subst.
inversion H0; subst.
split.
- apply srch with (lower:=lower) (upper:= (Some n)).
  apply H6.
- apply srch with (lower:= (Some n)) (upper:= upper).
  apply H7.
Qed.

Lemma Search_node3_conj :
  forall n1 n2 t1 t2 t3, SearchTree (node3 n1 n2 t1 t2 t3) -> SearchTree t1 /\ SearchTree t2 /\ SearchTree t3.
Proof.
intros.
inversion H; subst.
inversion H0; subst.
split.
- apply srch with (lower:=lower) (upper:= (Some n1)).
  apply H6.
- split.
  + apply srch with (lower:= (Some n1)) (upper:= (Some n2)).
    apply H9.
  + apply srch with (lower:= (Some n2)) (upper:= upper).
    apply H10.
Qed.

Lemma n_lt_n : forall n, n<n -> False.
Proof.
  intros.
  inversion H; subst.
  - clear H.
    induction n.
    + inversion H0.
    + apply IHn.
      inversion H0.
      apply H0.
  - clear H.
    induction m.
    + inversion H0.
    + apply IHm.
      apply le_S_n in H0.
      apply H0.
Qed.


Lemma loosen_lower_bound : forall n1 n2 u t, SearchTree' (Some n2) u t -> n1 <= n2 -> SearchTree' (Some n1) u t.
Proof.
  intros.
  generalize dependent n1.
  remember (Some n2) as l.
  generalize dependent n2.
  induction H; intros; subst.
  - apply srch_empty; destruct o2; unfold correct_Bounds in *; auto.
    rewrite <- H.
    apply H0.
  - apply srch_node2.
    + apply IHSearchTree'1 with n2; auto.
    + apply H0.
    + unfold k_inBounds in *.
      destruct upper.
      * destruct H1.
        split.
        -- rewrite H1 in H2.
           apply H2.
        -- apply H3.
      * destruct H1.
        split.
        -- rewrite H1 in H2.
           apply H2.
        -- apply H3.
  - apply srch_node3.
    + apply IHSearchTree'1 with n2; auto.
    + apply H0.
    + apply H1.
    + apply H2.
    + unfold k_inBounds in *.
      destruct upper.
      * destruct H4; destruct H3.
        split.
        -- rewrite H3 in H5.
           apply H5.
        -- apply H7.
      * destruct H4; destruct H3.
        split.
        -- rewrite H3 in H5.
           apply H5.
        -- apply H7.
    + unfold k_inBounds in *.
      destruct upper.
      * destruct H4; destruct H3.
        split.
        -- rewrite H4 in H5.
           apply H5.
        -- apply H6.
      * destruct H4; destruct H3.
        split.
        -- rewrite H4 in H5.
           apply H5.
        -- apply H6.
Qed.

Lemma loosen_upper_bound : forall n1 n2 l t, SearchTree' l (Some n2) t -> n2 <= n1 -> SearchTree' l (Some n1) t.
Proof.
  intros.
  generalize dependent n1.
  remember (Some n2) as u.
  generalize dependent n2.
  induction H; intros; subst.
  - apply srch_empty; destruct o1; unfold correct_Bounds in *; auto.
    rewrite <- H0.
    apply H.
  - apply srch_node2.
    + apply IHSearchTree'1 with k; reflexivity.
    + apply IHSearchTree'2 with n2.
      * reflexivity.
      * apply H2.
    + unfold k_inBounds in *.
      destruct lower; destruct H1.
      * split.
        -- apply H1.
        -- rewrite H2 in H3.
           apply H3.
      * split.
        -- apply H1.
        -- rewrite H2 in H3.
           apply H3.
  - apply srch_node3.
    + apply IHSearchTree'1 with k1; reflexivity.
    + apply IHSearchTree'2 with k2; reflexivity.
    + apply IHSearchTree'3 with n2.
      * reflexivity.
      * apply H5.
    + apply H2.
    + unfold k_inBounds in *.
      destruct lower; destruct H4; destruct H3.
      * split.
        -- apply H3.
        -- rewrite H5 in H7.
           apply H7.
      * split.
        -- apply H3.
        -- rewrite H5 in H7.
           apply H7.
    + unfold k_inBounds in *.
      destruct lower; destruct H4; destruct H3.
      * split.
        -- apply H4.
        -- rewrite H5 in H6.
           apply H6.
      * split.
        -- apply H4.
        -- rewrite H5 in H6.
           apply H6.
Qed.

(* this lemma states if k is in the tree upper bounded by n, then k<=n *)
Lemma leftTreeSearch_aux :
  forall n k lower t, keyIn k t -> SearchTree' lower (Some n) t -> k<=n.
Proof.
  intros.
  generalize dependent lower.
  generalize dependent n.
  induction H; intros; inversion H0; subst.
  - unfold k_inBounds in *.
    destruct H7.
    apply H1.
  - apply IHkeyIn with lower.
    unfold k_inBounds in *.
    apply loosen_upper_bound with n.
    + apply H6.
    + destruct H8.
      apply H2.
  - apply IHkeyIn with (Some n).
    apply H7.
  - unfold k_inBounds in *.
    destruct H11.
    apply H1.
  - unfold k_inBounds in *.
    destruct H12.
    apply H1.
  - apply IHkeyIn with lower.
    apply loosen_upper_bound with k1.
    + apply H6.
    + unfold k_inBounds in *.
      destruct H12.
      apply H2.
  - apply IHkeyIn with (Some k1).
    apply loosen_upper_bound with k2.
    + apply H9.
    + unfold k_inBounds in *.
      destruct H13.
      apply H2.
  - apply IHkeyIn with (Some k2).
    apply H10.
Qed.

(* this lemma states if k is in the tree lower bounded by n then n<=k *)
Lemma rightTreeSearch_aux :
  forall n k upper t, keyIn k t -> SearchTree' (Some n) upper t -> n<=k.
Proof.
  intros.
  generalize dependent upper.
  revert n.
  induction H; intros; inversion H0; subst.
  - inversion H7.
    apply H.
  - apply IHkeyIn with (Some n).
    apply H6.
  - unfold k_inBounds in *.
    destruct H8.
    apply IHkeyIn with upper.
    apply loosen_lower_bound with n.
    + apply H7.
    + apply H1.
  - unfold k_inBounds in *.
    destruct H11.
    apply H.
  - unfold k_inBounds in *.
    destruct H12.
    apply H.
  - apply IHkeyIn with (Some k1).
    apply H6.
  - apply IHkeyIn with (Some k2).
    apply loosen_lower_bound with k1.
    + apply H9.
    + unfold k_inBounds in *.
      destruct H12.
      apply H1.
  - apply IHkeyIn with upper.
    apply loosen_lower_bound with k2.
    + apply H10.
    + unfold k_inBounds in *.
      destruct H13.
      apply H1.
Qed.

(* this lemma states if k is in the tree lower bounded by n1 and upper bounded by n2 then n1<=k<=n2 *)
Lemma middleTreeSearch_aux :
  forall n1 n2 k t, keyIn k t -> SearchTree' (Some n1) (Some n2) t -> n1<=k /\ k<=n2.
Proof.
  intros.
  split.
  - apply rightTreeSearch_aux with (t:=t) (upper:= (Some n2)); assumption.
  - apply leftTreeSearch_aux with (t:=t) (lower:= (Some n1)); assumption.
Qed.

Theorem SearchCorrectness :
  forall t k, SearchTree t -> (keyIn k t <-> search23tree k t = true).
Proof.
intros.
split.
- intros.
  induction t.
  + inversion H0.
  + simpl.
    destruct (k ?= n) eqn:H1.
    * reflexivity.
    * apply IHt1.
      -- apply Search_node2_conj in H.
         destruct H.
         apply H.
      -- apply nat_compare_Lt_lt in H1.
         inversion H; subst.
         inversion H2; subst.
         inversion H0; subst.
         ++ apply n_lt_n in H1; inversion H1.
         ++ apply H5.
         ++ apply rightTreeSearch_aux with (n:= n) (upper:= upper) in H5.
            ** apply le_lt_or_eq in H5.
               destruct H5; rewrite H3 in H1; apply n_lt_n in H1; inversion H1.
            ** apply H9.
    * apply IHt2.
      -- apply Search_node2_conj in H.
         destruct H.
         apply H2.
      -- apply nat_compare_Gt_gt in H1; unfold gt in H1.
         inversion H; subst.
         inversion H2; subst.
         inversion H0; subst.
         ++ apply n_lt_n in H1; inversion H1.
         ++ apply leftTreeSearch_aux with (n:= n) (lower:= lower) in H5.
            ** apply le_lt_or_eq in H5.
               destruct H5; rewrite H3 in H1; apply n_lt_n in H1; inversion H1.
            ** apply H8.
         ++ apply H5.
  + simpl.
    destruct (k ?= n) eqn: H4.
    * reflexivity.
    * destruct (k ?= n0) eqn: H5.
      -- reflexivity.
      -- apply IHt1.
         ++ apply Search_node3_conj in H.
            destruct H as [H1 [H2 H3]].
            apply H1.
         ++ apply nat_compare_Lt_lt in H4.
            apply nat_compare_Lt_lt in H5.
            inversion H; inversion H1; inversion H0; subst.
            ** apply n_lt_n in H4; inversion H4.
            ** apply n_lt_n in H5; inversion H5.
            ** apply H20.
            ** apply middleTreeSearch_aux with (n1:=n) (n2:= n0) in H20.
               --- destruct H20.
                   apply le_lt_or_eq in H2.
                   destruct H2; rewrite H2 in H4; apply n_lt_n in H4; inversion H4.
               --- apply H13.
            ** apply rightTreeSearch_aux with (n:=n0) (upper:=upper) in H20.
               --- apply le_lt_or_eq in H20.
                   destruct H20; rewrite H2 in H5; apply n_lt_n in H5; inversion H5.
               --- apply H14.
      -- apply IHt1.
         ++ apply Search_node3_conj in H.
            destruct H as [H1 [H2 H3]].
            apply H1.
         ++ apply nat_compare_Lt_lt in H4.
            apply nat_compare_Gt_gt in H5; unfold gt in H5.
            inversion H; inversion H1; inversion H0; subst.
            ** apply n_lt_n in H4; inversion H4.
            ** apply n_lt_n in H5; inversion H5.
            ** apply H20.
            ** apply middleTreeSearch_aux with (n1:=n) (n2:= n0) in H20.
               --- destruct H20.
                   apply le_lt_or_eq in H2.
                   destruct H2; rewrite H2 in H4; apply n_lt_n in H4; inversion H4.
               --- apply H13.
            ** apply rightTreeSearch_aux with (n:= n0) (upper:= upper) in H20.
               --- apply le_lt_or_eq in H20;
                   destruct H20;
                     apply le_lt_or_eq in H15;
                     destruct H15;
                       rewrite H3 in H4;
                       rewrite H5 in H4;
                       apply n_lt_n in H4; inversion H4.
               --- apply H14.
    * destruct (k ?= n0) eqn: H5.
      -- reflexivity.
      -- apply IHt2.
         ++ apply Search_node3_conj in H.
            destruct H as [H1 [H2 H3]].
            apply H2.
         ++ apply nat_compare_Lt_lt in H5.
            apply nat_compare_Gt_gt in H4; unfold gt in H4.
            inversion H; subst; inversion H1; subst; inversion H0; subst.
            ** apply n_lt_n in H4; inversion H4.
            ** apply n_lt_n in H5; inversion H5.
            ** apply leftTreeSearch_aux with (n:= n) (lower:= lower) in H6.
               --- apply le_lt_or_eq in H6.
                   destruct H6; rewrite H2 in H4; apply n_lt_n in H4; inversion H4.
               --- apply H9.
            ** apply H6.
            ** apply rightTreeSearch_aux with (n:=n0) (upper:= upper) in H6.
               --- apply le_lt_or_eq in H6.
                   destruct H6; rewrite H2 in H5; apply n_lt_n in H5; inversion H5.
               --- apply H13.
      -- apply IHt3.
         ++ apply Search_node3_conj in H.
            destruct H as [H1 [H2 H3]].
            apply H3.
         ++ apply nat_compare_Gt_gt in H4; unfold gt in H4.
            apply nat_compare_Gt_gt in H5; unfold gt in H5.
            inversion H; subst; inversion H1; subst; inversion H0; subst.
            ** apply n_lt_n in H4; inversion H4.
            ** apply n_lt_n in H5; inversion H5.
            ** apply leftTreeSearch_aux with (n:=n) (lower:=lower) in H6.
               --- apply le_lt_or_eq in H6.
                   destruct H6; rewrite H2 in H4; apply n_lt_n in H4; inversion H4.
               --- apply H9.
            ** apply middleTreeSearch_aux with (n1:= n) (n2:= n0) in H6.
               --- destruct H6.
                   apply le_lt_or_eq in H3; destruct H3; rewrite H3 in H5; apply n_lt_n in H5; inversion H5.
               --- apply H12.
            ** apply H6.
- intros.
  induction t.
  + inversion H0.
  + inversion H; inversion H1; subst; clear H H1.
    simpl in H0.
    destruct (k ?= n) eqn: H1.
    * apply nat_compare_eq in H1.
      rewrite H1.
      apply In2_match.
    * apply In2_left.
      apply IHt1.
      -- apply srch with lower (Some n).
         apply H8.
      -- apply H0.
    * apply In2_right.
      apply IHt2.
      -- apply srch with (Some n) upper.
         apply H9.
      -- apply H0.
  + inversion H; inversion H1; subst; clear H H1.
    simpl in H0.
    destruct (k ?= n) eqn: H1.
    * apply nat_compare_eq in H1.
      rewrite H1.
      apply In3_match1.
    * destruct (k ?= n0) eqn: H2.
      -- apply nat_compare_eq in H2.
         rewrite H2.
         apply In3_match2.
      -- apply In3_left.
         apply IHt1.
         ++ apply srch with lower (Some n).
            apply H8.
         ++ apply H0.
      -- apply In3_left.
         apply IHt1.
         ++ apply srch with lower (Some n).
            apply H8.
         ++ apply H0.
    * destruct (k ?= n0) eqn: H2.
      -- apply nat_compare_eq in H2.
         rewrite H2.
         apply In3_match2.
      -- apply In3_middle.
         apply IHt2.
         ++ apply srch with (Some n) (Some n0).
            apply H11.
         ++ apply H0.
      -- apply In3_right.
         apply IHt3.
         ++ apply srch with (Some n0) (upper).
            apply H12.
         ++ apply H0.
Qed.

Opaque min max.
Hint Resolve Nat.le_min_r Nat.le_min_l.
Hint Resolve Nat.le_max_r Nat.le_max_l.
Hint Resolve Nat.max_lub Nat.min_glb.

Lemma TreeBounds : forall l u t, SearchTree' (Some l) (Some u) t -> l <= u.
Proof.
  intros.
  destruct t.
  - inversion H; subst.
    unfold correct_Bounds in H0.
    apply H0.
  - inversion H; subst.
    unfold k_inBounds in H7; destruct H7.
    rewrite <- H1.
    apply H0.
  - inversion H; subst.
    unfold k_inBounds in *; destruct H11; destruct H12.
    rewrite <- H3.
    apply H2.
Qed.

Lemma PreserveSearchInsertHelper : forall lower upper k t,
  SearchTree' lower upper t ->
  match insertHelper k t with
  | irTree t' =>       SearchTree' (min' k lower) (max' k upper) t'
  | irSplit t1 s t2 => SearchTree' (min' k lower) (Some s) t1
                    /\ SearchTree' (Some s) (max' k upper) t2
  end.
Proof.
intros.
induction H; intros.
- simpl; split; apply srch_empty; unfold correct_Bounds in *; unfold min'; unfold max'; try destruct o1; try destruct o2; auto.
- simpl.
  destruct t1.
  + destruct t2.
    * destruct (k <=? k0) eqn: H2.
      -- apply srch_node3; try apply srch_empty.
         ++ unfold correct_Bounds; destruct lower; unfold min'; auto.
         ++ apply leb_complete in H2.
            unfold correct_Bounds; apply H2.
         ++ apply leb_complete in H2.
            unfold correct_Bounds; destruct upper; unfold max'; auto.
            unfold k_inBounds in H1; destruct lower; destruct H1.
            ** rewrite H3; auto.
            ** rewrite H3; auto. 
         ++ apply leb_complete in H2.
            apply H2.
         ++ unfold min'; unfold max'.
            destruct lower; destruct upper; unfold k_inBounds; split; auto.
         ++ apply leb_complete in H2.
            unfold min'; unfold max'.
            destruct lower; destruct upper; unfold k_inBounds; split; auto.
            ** rewrite <- H2; auto.
            ** unfold k_inBounds in H1.
               destruct H1.
               rewrite H3.
               auto.
            ** rewrite <- H2.
               auto.
            ** unfold k_inBounds in H1; destruct H1.
               rewrite H3.
               auto.
      -- apply leb_complete_conv in H2.
         apply Nat.lt_le_incl in H2.
         apply srch_node3; try apply srch_empty; auto.
         unfold k_inBounds in H1; destruct H1.
         ++ unfold correct_Bounds; destruct lower; unfold min'; auto.
            rewrite <- H1; auto.
         ++ unfold correct_Bounds; destruct upper; unfold max'; auto.
         ++ unfold min'; unfold max'.
            destruct lower; destruct upper; unfold k_inBounds in *; destruct H1; split; auto.
            ** rewrite <- H1.
               auto.
            ** rewrite H3.
               auto.
            ** rewrite <- H1.
               auto.
            ** rewrite H3.
               auto.
         ++ unfold min'; unfold max'.
            destruct lower; destruct upper; unfold k_inBounds; split; auto.
    * destruct (k <=? k0) eqn: H2.
      -- apply srch_node3.
         ++ apply srch_empty.
            unfold correct_Bounds; destruct lower; unfold min'; auto.
         ++ apply srch_empty.
            apply leb_complete in H2.
            unfold correct_Bounds.
            apply H2.
         ++ destruct upper.
            ** apply srch_node2; inversion H0; subst; clear H0.
               --- apply H8.
               --- unfold k_inBounds in H10; destruct H10.
                   apply leb_complete in H2.
                   unfold max'.
                   rewrite H3 in H0.
                   rewrite H0 in H2.
                   apply max_r in H2.
                   rewrite H2.
                   apply H9.
               --- apply leb_complete in H2.
                   unfold k_inBounds in *; destruct H10; split; auto.
                   unfold max'.
                   rewrite H3 in H0.
                   rewrite H0 in H2.
                   apply max_r in H2.
                   rewrite H2.
                   apply H3.
            ** auto.
         ++ apply leb_complete in H2; apply H2.
         ++ unfold k_inBounds; unfold min'; unfold max'; destruct lower; destruct upper; auto.
         ++ unfold k_inBounds in *; destruct H1; unfold min'; unfold max'; destruct lower; destruct upper; apply leb_complete in H2; auto.
            ** split.
               --- apply (Nat.min_le_compat k k0 n0 k0) in H2.
                   +++ rewrite Nat.min_id in H2.
                       apply H2.
                   +++ apply H1.
               --- rewrite H3 in H2.
                   apply max_r in H2.
                   rewrite H2.
                   apply H3.
            ** split; auto.
               apply (Nat.min_le_compat k k0 n0 k0) in H2.
               --- rewrite Nat.min_id in H2.
                   apply H2.
               --- apply H1.
            ** split; auto.
               rewrite H3. (* why doesnt auto rewrite *)
               auto.
      -- (* stuck *)
               
               Admitted.


Theorem PreserveSearchTreeInvariant :
  forall t k, SearchTree t -> SearchTree (insert23tree k t).
Proof.
  intros.
  inversion H; subst; clear H.
  unfold insert23tree.
  apply (PreserveSearchInsertHelper lower upper k t) in H0.
  destruct (insertHelper k t).
  - eapply srch.
    apply H0.
  - destruct H0.
    eapply srch.
    apply srch_node2.
    + apply H.
    + apply H0.
    + destruct lower; destruct upper; unfold min' in *; unfold max' in *; unfold k_inBounds; split; auto.
      * apply TreeBounds in H.
        apply H.
      * apply TreeBounds in H0.
        apply H0.
      * apply TreeBounds in H.
        apply H.
      * apply TreeBounds in H0.
        apply H0.
Qed.


Lemma PreserveBalanceInsertHelper : forall n k t,
  Balanced' n t ->
  match insertHelper k t with
  | irTree t' =>       Balanced' n t'
  | irSplit t1 s t2 => Balanced' n t1
                    /\ Balanced' n t2
  end.
Proof.
  intros.
  induction H; intros; simpl.
  - split; apply b_treeEmpty.
  - destruct t1; destruct t2.
    + destruct (k <=? k0); apply b_tree3; apply H.
    + destruct (k <=? k0).
      * destruct (insertHelper k empty).
        -- apply b_tree2.
           ** apply IHBalanced'1.
           ** apply H0.
        -- apply b_tree3; destruct IHBalanced'1; auto.
      * destruct (insertHelper k (node2 n0 t2_1 t2_2)). 
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'2; assumption.
    + destruct (k <=? k0).
      * destruct (insertHelper k empty).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'1; assumption.
      * destruct (insertHelper k (node3 n0 n1 t2_1 t2_2 t2_3)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'2; assumption.
    + destruct (k <=? k0).
      * destruct (insertHelper k (node2 n0 t1_1 t1_2)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'1; assumption.
      * destruct (insertHelper k empty).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'2; assumption.
    + destruct (k <=? k0).
      * destruct (insertHelper k (node2 n0 t1_1 t1_2)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'1; assumption.
      * destruct (insertHelper k (node2 n1 t2_1 t2_2)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'2; assumption.
    + destruct (k <=? k0).
      * destruct (insertHelper k (node2 n0 t1_1 t1_2)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'1; assumption.
      * destruct (insertHelper k (node3 n1 n2 t2_1 t2_2 t2_3)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'2; assumption.
    + destruct (k <=? k0).
      * destruct (insertHelper k (node3 n0 n1 t1_1 t1_2 t1_3)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'1; assumption.
      * destruct (insertHelper k empty).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'2; assumption.
    + destruct (k <=? k0).
      * destruct (insertHelper k (node3 n0 n1 t1_1 t1_2 t1_3)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'1; assumption.
      * destruct (insertHelper k (node2 n2 t2_1 t2_2)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'2; assumption.
    + destruct (k <=? k0).
      * destruct (insertHelper k (node3 n0 n1 t1_1 t1_2 t1_3)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'1; assumption.
      * destruct (insertHelper k (node3 n2 n3 t2_1 t2_2 t2_3)).
        -- apply b_tree2; assumption.
        -- apply b_tree3; destruct IHBalanced'2; assumption.
  - destruct t1.
    + destruct t2.
      * destruct t3.
        -- destruct (k <=? k2).
           ++ destruct (k <=? k1).
              ** split; apply b_tree2; assumption.
              ** split; apply b_tree2; assumption.
           ++ split; apply b_tree2; assumption.
        -- destruct (k <=? k2) eqn:H2.
           ++ destruct (k <=? k1) eqn:H3.
              ** destruct (insertHelper k empty).
                 --- apply b_tree3; assumption.
                 --- split; apply b_tree2; destruct IHBalanced'1; assumption.
              ** destruct (insertHelper k empty).
                 --- apply b_tree3; assumption.
                 --- split; apply b_tree2; destruct IHBalanced'1; assumption.
           ++ destruct (insertHelper k (node2 n0 t3_1 t3_2)).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'3; assumption.
        -- destruct (k <=? k2) eqn:H2.
           ++ destruct (k <=? k1) eqn:H3.
              ** destruct (insertHelper k empty).
                 --- apply b_tree3; assumption.
                 --- split; apply b_tree2; destruct IHBalanced'1; assumption.
              ** destruct (insertHelper k empty).
                 --- apply b_tree3; assumption.
                 --- split; apply b_tree2; destruct IHBalanced'1; assumption.
           ++ destruct (insertHelper k (node3 n0 n1 t3_1 t3_2 t3_3)).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'3; assumption.
      * destruct (k <=? k2).
        -- destruct (k <=? k1).
           ++ destruct (insertHelper k empty).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'1; assumption.
           ++ destruct (insertHelper k (node2 n0 t2_1 t2_2)).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'2; assumption.
        -- destruct (insertHelper k t3).
           ++ apply b_tree3; assumption.
           ++ split; apply b_tree2; destruct IHBalanced'3; assumption.
      * destruct (k <=? k2).
        -- destruct (k <=? k1).
           ++ destruct (insertHelper k empty).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'1; assumption.
           ++ destruct (insertHelper k (node3 n0 n1 t2_1 t2_2 t2_3)).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'2; assumption.
        -- destruct (insertHelper k t3).
           ++ apply b_tree3; assumption.
           ++ split; apply b_tree2; destruct IHBalanced'3; assumption.
    + destruct (k <=? k2).
        -- destruct (k <=? k1).
           ++ destruct (insertHelper k (node2 n0 t1_1 t1_2)).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'1; assumption.
           ++ destruct (insertHelper k t2).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'2; assumption.
        -- destruct (insertHelper k t3).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'3; assumption.
    + destruct (k <=? k2).
        -- destruct (k <=? k1).
           ++ destruct (insertHelper k (node3 n0 n1 t1_1 t1_2 t1_3)).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'1; assumption.
           ++ destruct (insertHelper k t2).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'2; assumption.
        -- destruct (insertHelper k t3).
              ** apply b_tree3; assumption.
              ** split; apply b_tree2; destruct IHBalanced'3; assumption.
Qed.

Theorem PreserveBalancedInvariant :
  forall t k, Balanced t -> Balanced (insert23tree k t).
Proof.
  intros.
  inversion H; subst; clear H.
  unfold insert23tree.
  apply PreserveBalanceInsertHelper with (k:=k) in H0.
  destruct (insertHelper k t).
  - apply bal with n.
    apply H0.
  - destruct H0.
    apply bal with (S n).
    apply b_tree2.
    + apply H.
    + apply H0.
Qed.

Lemma keyIn_insert : forall t k, match insertHelper k t with
  | irTree t' => keyIn k t'
  | irSplit t1 m t2 => match (k ?= m) with
    | Lt => keyIn k t1
    | Eq => k=m
    | Gt => keyIn k t2
    end
  end.
Proof.
  intros.
  induction t.
  - simpl.
    destruct (k ?= k) eqn: H.
    + apply nat_compare_eq in H.
      apply H.
    + apply nat_compare_lt in H.
      apply n_lt_n in H; inversion H.
    + apply nat_compare_gt in H.
      unfold gt in H.
      apply n_lt_n in H; inversion H.
  - simpl.
    destruct t1.
    + destruct t2.
      * destruct (k <=? n) eqn:H.
        -- apply In3_match1.
        -- apply In3_match2.
      * destruct (k <=? n) eqn: H.
        -- simpl.
           apply In3_match1.
        -- destruct (insertHelper k (node2 n0 t2_1 t2_2)).
           ++ apply In2_right.
              apply IHt2.
           ++ destruct (k ?= n1) eqn : H1.
              ** apply nat_compare_eq in H1.
                 rewrite H1.
                 apply In3_match2.
              ** apply In3_middle.
                 apply IHt2.
              ** apply In3_right.
                 apply IHt2.
      * destruct (k <=? n) eqn: H.
        -- destruct (insertHelper k empty).
           ++ apply In2_left.
              apply IHt1.
           ++ destruct (k ?= n2).
              ** rewrite IHt1.
                 apply In3_match1.
              ** apply In3_left.
                 apply IHt1.
              ** apply In3_middle.
                 apply IHt1.
        -- destruct (insertHelper k (node3 n0 n1 t2_1 t2_2 t2_3)).
           ++ apply In2_right.
              apply IHt2.
           ++ destruct (k ?= n2).
              ** rewrite IHt2.
                 apply In3_match2.
              ** apply In3_middle; assumption.
              ** apply In3_right; assumption.
    + destruct (k <=? n).
      * destruct (insertHelper k (node2 n0 t1_1 t1_2)).
        -- apply In2_left; assumption.
        -- destruct (k ?= n1).
           ++ rewrite IHt1.
              apply In3_match1.
           ++ apply In3_left; assumption.
           ++ apply In3_middle; assumption.
      * (destruct (insertHelper k t2)).
        -- apply In2_right; assumption.
        -- destruct (k ?= n1).
           ++ rewrite IHt2.
              apply In3_match2.
           ++ apply In3_middle; assumption.
           ++ apply In3_right; assumption.
    + destruct (k <=? n). (*Andreas stopped here*)



Admitted.

Theorem InsertCorrectness1 :
  forall t k, keyIn k (insert23tree k t).
Proof.
  intros.
  unfold insert23tree.
  induction t; unfold insert23tree.
  - simpl.
    apply In2_match.
  - destruct (insertHelper k (node2 n t1 t2)) eqn: H.
    
    (*apply keyIn_insert in IHt1.
      why cant I do this *)
Admitted.

Theorem insertCorrectness2 :
  forall t k k', keyIn k' t -> keyIn k' (insert23tree k t).
Proof.
  intros.
  induction H.
  - unfold insert23tree.
    
Admitted.

Theorem insertCorrectness3 :
  forall t k k', keyIn k' (insert23tree k t) -> k' = k \/ keyIn k' t.
Proof.
  intros.
  induction t; intros.
  - unfold insert23tree in H.
    simpl in *.
    inversion H; subst.
    + left; reflexivity.
    + inversion H2.
    + right; apply H2.
  - unfold insert23tree in H.
    (* stuck again *)
Admitted.


