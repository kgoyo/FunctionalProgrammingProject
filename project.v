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


Fixpoint insert23treeStep1 (k:nat) (t:tree23) : tree234 :=
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
    | true => insert23treeStep1 k t1
    | false => insert23treeStep1 k t2
    end

  | node3 k1 k2 t1 t2 t3 =>
    match Nat.leb k k2 with
      | true => 
        match Nat.leb k k1 with
        | true => insert23treeStep1 k t1
        | false => insert23treeStep1 k t2
        end
      | false => insert23treeStep1 k t3
    end
  end.


Fixpoint insert23treeStep2 (t:tree234) : tree23 :=
  match t with
  | empty' => empty
  
  (* for the root *)
  | node4' k1 k2 k3 t1 t2 t3 t4 => node2 k2 (node2 k1 (insert23treeStep2 t1) (insert23treeStep2 t2)) (node2 k3 (insert23treeStep2 t3) (insert23treeStep2 t4))

  | node3' k1 k2 t1 t2 t3 => node3 k1 k2 (insert23treeStep2 t1) (insert23treeStep2 t2) (insert23treeStep2 t3)
  
  | node2' k t1 t2 => node2 k (insert23treeStep2 t1) (insert23treeStep2 t2)
  end.



Inductive keyIn : nat -> tree23 -> Prop :=
  | In2a : forall k t1 t2, keyIn k (node2 k t1 t2)
  | In2b : forall k n t1 t2, keyIn k t1 -> keyIn k (node2 n t1 t2)
  | In2c : forall k n t1 t2, keyIn k t2 -> keyIn k (node2 n t1 t2)

  | In3a : forall k k2 t1 t2 t3, keyIn k (node3 k k2 t1 t2 t3)
  | In3b : forall k k1 t1 t2 t3, keyIn k (node3 k1 k t1 t2 t3)
  | In3c : forall k k1 k2 t1 t2 t3, keyIn k t1 -> keyIn k (node3 k1 k2 t1 t2 t3)
  | In3d : forall k k1 k2 t1 t2 t3, keyIn k t2 -> keyIn k (node3 k1 k2 t1 t2 t3)
  | In3e : forall k k1 k2 t1 t2 t3, keyIn k t3 -> keyIn k (node3 k1 k2 t1 t2 t3).





















