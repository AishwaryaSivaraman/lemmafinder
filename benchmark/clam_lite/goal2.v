

Inductive natural : Type := Succ : natural -> natural |  Zero : natural.

Inductive lst : Type := Cons : natural -> lst -> lst |  Nil : lst.

Inductive tree : Type := Node : natural -> tree -> tree -> tree |  Leaf : tree.

Inductive Pair : Type := mkpair : natural -> natural -> Pair
with Zlst : Type := zcons : Pair -> Zlst -> Zlst |  znil : Zlst.

Fixpoint append (append_arg0 : lst) (append_arg1 : lst) : lst
           := match append_arg0, append_arg1 with
              | Nil, x => x
              | Cons x y, z => Cons x (append y z)
              end.

Fixpoint len (len_arg0 : lst) : natural
           := match len_arg0 with
              | Nil => Zero
              | Cons x y => Succ (len y)
              end.

Lemma lem : forall l1 l2 n, Succ (len (append l1 l2)) = len (append l1 (Cons n l2)).
Proof.
   induction l1.
   - intros. simpl. f_equal. apply IHl1.
   - intros. reflexivity.
Qed.

Lemma lem2 : forall l, len l = len (append l Nil).
Proof.
   induction l.
   - simpl. f_equal. apply IHl.
   - reflexivity.
Qed.

Theorem theorem0 : forall (x : lst) (y : lst), eq (len (append x y)) (len (append y x)).
Proof.
   induction x.
   - intros. simpl. rewrite IHx. apply lem.
   - intros. simpl. apply lem2.
Qed.

