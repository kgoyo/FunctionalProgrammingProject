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





















