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

Fixpoint double (double_arg0 : natural) : natural
           := match double_arg0 with
              | Zero => Zero
              | Succ n => Succ (Succ (double n))
              end.

Lemma lem: forall m n, Succ (plus m n) = plus m (Succ n).
Proof.
   induction m.
   - intros. simpl. rewrite IHm. reflexivity.
   - intros. reflexivity.
Qed.

Theorem theorem0 : forall (x : natural), eq (double x) (plus x x).
Proof.
   induction x.
   - simpl. f_equal. rewrite IHx. apply lem.
   - reflexivity.
Qed.
