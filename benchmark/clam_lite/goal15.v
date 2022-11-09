

Inductive natural : Type := Succ : natural -> natural |  Zero : natural.

Inductive lst : Type := Cons : natural -> lst -> lst |  Nil : lst.

Inductive tree : Type := Node : natural -> tree -> tree -> tree |  Leaf : tree.

Inductive Pair : Type := mkpair : natural -> natural -> Pair
with Zlst : Type := zcons : Pair -> Zlst -> Zlst |  znil : Zlst.

Fixpoint plus (plus_arg0 : natural) (plus_arg1 : natural) : natural
           := match plus_arg0, plus_arg1 with
              | Zero, n => n
              | Succ n, m => Succ (plus n m)
              end.

Lemma lem: forall m n, Succ (plus m n) = plus m (Succ n).
Proof.
intros. simpl. induction m.
  - simpl. rewrite IHm. reflexivity.
  - reflexivity.
Qed.

Theorem theorem0 : forall (x : natural), eq (plus x (Succ x)) (Succ (plus x x)).
Proof.
induction x.
  - simpl. rewrite IHx. f_equal. 
    rewrite lem. 
    rewrite lem. 
    reflexivity.
  - reflexivity.
Qed.

