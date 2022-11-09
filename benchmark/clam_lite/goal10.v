
From QuickChick Require Import QuickChick.
Inductive natural : Type := Succ : natural -> natural |  Zero : natural.
Derive Show for natural. Derive Arbitrary for natural.  Instance Dec_Eq_natural : Dec_Eq natural. Proof. dec_eq. Qed.
Inductive lst : Type := Cons : natural -> lst -> lst |  Nil : lst.

Inductive tree : Type := Node : natural -> tree -> tree -> tree |  Leaf : tree.

Inductive Pair : Type := mkpair : natural -> natural -> Pair
with Zlst : Type := zcons : Pair -> Zlst -> Zlst |  znil : Zlst.

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

Theorem append_Nil: forall (l: lst), append l Nil = l.
Proof.
  induction l.
  { simpl. f_equal. assumption. }
  { simpl. reflexivity. }
Qed.

Theorem append_assoc:
  forall (l1 l2 l3: lst), append l1 (append l2 l3) = append (append l1 l2) l3.
Proof.
  induction l1; induction l2; induction l3; try (simpl; reflexivity).
  - simpl. rewrite <- IHl1. f_equal. 
  - simpl. rewrite 2 append_Nil. reflexivity. 
  - simpl. rewrite append_Nil.  reflexivity. 
  - simpl. rewrite 2 append_Nil. reflexivity. 
Qed.

Theorem append_rev_Cons:
  forall (l1 l2: lst) (x: natural),
    rev (append l1 (Cons x l2)) = append (rev l2) (Cons x (rev l1)).
Proof.
  induction l1; induction l2; try (simpl; reflexivity).
  { intro. simpl. rewrite IHl1. simpl. rewrite <- append_assoc.
    f_equal. }
  { intro. simpl. rewrite IHl1. simpl. reflexivity. }
Qed.

Theorem rev_append: forall (l1 l2: lst), rev (append l1 l2) = append (rev l2) (rev l1).
Proof.
  induction l1.
  { induction l2.
    { simpl. rewrite append_rev_Cons.
      rewrite <- 2 append_assoc.
      f_equal. }
    { simpl. rewrite append_Nil. reflexivity. }
  }
  { intro. simpl. rewrite append_Nil. reflexivity. }
Qed.

Theorem theorem0 : forall (x : lst), eq (rev (rev x)) x.
Proof.
  induction x.
  { simpl. rewrite rev_append. simpl. f_equal.
    assumption. }
  { simpl. reflexivity. }
Qed.
