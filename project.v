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


Inductive tree234 : Type :=
  | empty' : tree234
  | node2' : nat -> tree234 -> tree234 -> tree234
  | node3' : nat -> nat -> tree234 -> tree234 -> tree234 -> tree234
  | node4' : nat -> nat -> nat -> tree234 -> tree234 -> tree234 -> tree234 -> tree234
.

Fixpoint translateTo234 (t:tree23) : tree234 :=
  match t with
  | empty => empty'
  | node2 k t1 t2 => node2' k (translateTo234 t1) (translateTo234 t2)
  | node3 k1 k2 t1 t2 t3 => node3' k1 k2 (translateTo234 t1) (translateTo234 t2) (translateTo234 t3)
end.


Fixpoint translateTo23 (t:tree234) : tree23 :=
  match t with
  | empty' => empty
  | node2' k t1 t2 => node2 k (translateTo23 t1) (translateTo23 t2)
  | node3' k1 k2 t1 t2 t3 => node3 k1 k2 (translateTo23 t1) (translateTo23 t2) (translateTo23 t3)
  | node4' k1 k2 k3 t1 t2 t3 t4 => node2 k2 (node2 k1 (translateTo23 t1) (translateTo23 t2)) (node2 k3 (translateTo23 t3) (translateTo23 t4))
  end.

Fixpoint insert23subtree (k:nat) (t:tree23) : tree234 :=
  match t with

  | empty => node2' k empty' empty'

  | node2 k1 empty empty =>
    match Nat.leb k k1 with
    | true => node3' k k1 empty' empty' empty'
    | false => node3' k1 k empty' empty' empty'
    end

  | node3 k1 k2 empty empty empty =>
    match Nat.leb k k2 with
      | true => 
        match Nat.leb k k1 with
        | true => node4' k k1 k2 empty' empty' empty' empty'
        | false => node4' k1 k k2 empty' empty' empty' empty'
        end
      | false => node4' k1 k2 k empty' empty' empty' empty'
    end

  | node2 k1 t1 t2 =>
    match Nat.leb k k1 with
    | true =>
      match insert23subtree k t1 with
      | node4' n1 n2 n3 w1 w2 w3 w4 => node3' n2 k1 (node2' n1 w1 w2) (node2' n3 w3 w4) (translateTo234 t2)
      | t' => node2' k1 t' (translateTo234 t2)
      end
    | false =>
      match insert23subtree k t2 with
      | node4' n1 n2 n3 w1 w2 w3 w4 => node3' k1 n2 (translateTo234 t1) (node2' n1 w1 w2) (node2' n3 w3 w4)
      | t' => node2' k1 (translateTo234 t1) t'
      end
    end

  | node3 k1 k2 t1 t2 t3 =>
    match Nat.leb k k2 with
      | true => 
        match Nat.leb k k1 with
        | true =>
          match insert23subtree k t1 with
          | node4' n1 n2 n3 w1 w2 w3 w4 => node4' n2 k1 k2 (node2' n1 w1 w2) (node2' n3 w3 w4) (translateTo234 t2) (translateTo234 t3)
          | t' => node3' k1 k2 t' (translateTo234 t2) (translateTo234 t3)
          end
        | false =>
          match insert23subtree k t2 with
          | node4' n1 n2 n3 w1 w2 w3 w4 => node4' k1 n2 k2 (translateTo234 t1) (node2' n1 w1 w2) (node2' n3 w3 w4) (translateTo234 t3)
          | t' => node3' k1 k2 (translateTo234 t1) t' (translateTo234 t3)
          end
        end
      | false =>
        match insert23subtree k t3 with
        | node4' n1 n2 n3 w1 w2 w3 w4 => node4' k1 k2 n2 (translateTo234 t1) (translateTo234 t2) (node2' n1 w1 w2) (node2' n3 w3 w4)
        | t' => node3' k1 k2 (translateTo234 t1) (translateTo234 t2) t'
        end
    end
  end.

Definition insert23tree (k:nat) (t:tree23) : tree23 :=
  translateTo23 (insert23subtree k t).

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
  | In2a : forall k t1 t2, keyIn k (node2 k t1 t2)
  | In2b : forall k n t1 t2, keyIn k t1 -> keyIn k (node2 n t1 t2)
  | In2c : forall k n t1 t2, keyIn k t2 -> keyIn k (node2 n t1 t2)

  | In3a : forall k k2 t1 t2 t3, keyIn k (node3 k k2 t1 t2 t3)
  | In3b : forall k k1 t1 t2 t3, keyIn k (node3 k1 k t1 t2 t3)
  | In3c : forall k k1 k2 t1 t2 t3, keyIn k t1 -> keyIn k (node3 k1 k2 t1 t2 t3)
  | In3d : forall k k1 k2 t1 t2 t3, keyIn k t2 -> keyIn k (node3 k1 k2 t1 t2 t3)
  | In3e : forall k k1 k2 t1 t2 t3, keyIn k t3 -> keyIn k (node3 k1 k2 t1 t2 t3).


Inductive Balanced': nat -> tree23 -> Prop :=
  | b_base : Balanced' 0 empty
  | b_tree2 : forall k n t1 t2, Balanced' n t1 -> Balanced' n t2 -> Balanced' (S n) (node2 k t1 t2)
  | b_tree3 : forall k1 k2 n t1 t2 t3, Balanced' n t1 -> Balanced' n t2 -> Balanced' n t3 -> Balanced' (S n) (node3 k1 k2 t1 t2 t3).


Inductive Balanced : tree23 -> Prop :=
  | bal : forall t, (exists n, Balanced' n t) -> Balanced t.

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
(*
Inductive k_inBounds : nat -> option nat -> option nat -> Prop :=
  | kb_doubleNone :  forall n, k_inBounds n None None
  | kb_leftNone : forall n upper, n <= upper -> k_inBounds n None (Some upper)
  | kb_rightNone : forall n lower, lower <= n -> k_inBounds n (Some lower) None
  | kb_noNone : forall n lower upper, lower <= n -> n <= upper -> k_inBounds n (Some lower) (Some upper).
  *)

Inductive SearchTree' : option nat -> option nat -> tree23 -> Prop :=
  | srch_empty : forall o1 o2, SearchTree' o1 o2 empty
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
  - apply srch_empty.
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
  - apply srch_empty.
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
  (*TODO*)
  Admitted.

Theorem PreserveSearchTreeInvariant :
  forall t k, SearchTree t -> SearchTree (insert23tree k t).
Proof.
Admitted.

Theorem PreserveBalancedInvariant :
  forall t k, Balanced t -> Balanced (insert23tree k t).
Proof.
Admitted.

Theorem InsertCorrectness1 :
  forall t k, keyIn k (insert23tree k t).
Proof.
Admitted.

Theorem insertCorrectness2 :
  forall t k k', keyIn k' t -> keyIn k' (insert23tree k t).
Proof.
Admitted.

Theorem insertCorrectness3 :
  forall t k k', keyIn k' (insert23tree k t) -> k' = k \/ keyIn k' t.
Proof.
Admitted.










