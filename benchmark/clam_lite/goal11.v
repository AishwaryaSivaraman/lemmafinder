
From QuickChick Require Import QuickChick.
Inductive natural : Type := Succ : natural -> natural |  Zero : natural.
Derive Show for natural. Derive Arbitrary for natural.  Instance Dec_Eq_natural : Dec_Eq natural. Proof. dec_eq. Qed.
Inductive lst : Type := Cons : natural -> lst -> lst |  Nil : lst.

Inductive tree : Type := Node : natural -> tree -> tree -> tree |  Leaf : tree.

Inductive Pair : Type := mkpair : natural -> natural -> Pair
with Zlst : Type := zcons : Pair -> Zlst -> Zlst |  zNil : Zlst.

Fixpoint append (append_arg0 : lst) (append_arg1 : lst) : lst
           := match append_arg0, append_arg1 with
              | Nil, x => x
              | Cons x y, z => Cons x (append y z)
              end.

Fixpoint rev (rev_arg0 : lst) : lst
           := match rev_arg0 with
              | Nil => Nil
              | Cons x y => append (rev y) (Cons x Nil)
              end.

Lemma append_assoc: forall l1 l2 l3, 
  append l1 (append l2 l3) = append (append l1 l2) l3.
Proof.
induction l1.
  - simpl. intros. rewrite IHl1. reflexivity.
  - reflexivity.
Qed.

Lemma lem: forall l n, Cons n (rev l) = rev (append l (Cons n Nil)).
Proof.
intros. induction l.
  - simpl. rewrite <- IHl. reflexivity.
  - reflexivity.
Qed.

Lemma lem2: forall l, rev (rev l) = l.
Proof.
induction l.
  - simpl. rewrite <- lem. rewrite IHl. reflexivity.
  - reflexivity.
Qed.

Lemma lem3: forall l, append l Nil = l.
Proof.
induction l.
  - simpl. rewrite IHl. reflexivity.
  - reflexivity.
Qed.

Theorem theorem0 : forall (x : lst) (y : lst), eq (rev (append (rev x) (rev y))) (append y x).
Proof.
 induction x.
 - intros. simpl. rewrite <- append_assoc. simpl. 
   rewrite lem. rewrite IHx. rewrite <- append_assoc. reflexivity.
 - intros. simpl. rewrite lem2. rewrite lem3. reflexivity.
Qed.
