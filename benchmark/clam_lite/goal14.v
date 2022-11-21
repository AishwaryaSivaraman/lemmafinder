

Inductive natural : Type := Succ : natural -> natural |  Zero : natural.

Inductive lst : Type := Cons : natural -> lst -> lst |  Nil : lst.

Inductive tree : Type := Node : natural -> tree -> tree -> tree |  Leaf : tree.

Inductive Pair : Type := mkpair : natural -> natural -> Pair
with Zlst : Type := zcons : Pair -> Zlst -> Zlst |  znil : Zlst.

Fixpoint less (less_arg0 : natural) (less_arg1 : natural) : bool
           := match less_arg0, less_arg1 with
              | x, Zero => false
              | Zero, Succ x => true
              | Succ x, Succ y => less x y
              end.

Fixpoint eqn (m n : natural) : bool :=
  match m , n with
  | Zero , Zero => true
  | Succ m' , Succ n' => eqn m' n'
  | _, _ => false
  end.

Definition leq (m n : natural) : bool :=
  orb (eqn m n) (less m n).

Fixpoint insort (insort_arg0 : natural) (insort_arg1 : lst) : lst
           := match insort_arg0, insort_arg1 with
              | i, Nil => Cons i Nil
              | i, Cons x y => if less i x then Cons i (Cons x y) else Cons x (insort i y)
              end.

Fixpoint sorted (sorted_arg0 : lst) : bool
           := match sorted_arg0 with
              | Nil => true
              | Cons x l =>
                let s := sorted l in
                match l with
                | Nil => true
                | Cons y _ => andb s (leq x y)
                end
              end.

Fixpoint sort (sort_arg0 : lst) : lst
           := match sort_arg0 with
              | Nil => Nil
              | Cons x y => insort x (sort y)
              end.


(*
Lemma lem2: forall m n, less m n = false -> leq n m = true.
(* Proof. 
  induction m.
  - intros. unfold leq. unfold orb. remember (eqn n (Succ m)).
    destruct b.
    * reflexivity.
    * destruct n.
      + simpl. simpl in H.  *)
Admitted.

Lemma lem3: forall n0 n l, sorted (Cons n l) = true -> leq n0 n = true -> 
    sorted (Cons n0 (Cons n l)) = true.
Admitted.
*)

Lemma lem: forall n l, sorted l = true -> sorted (insort n l) = true.
(* Proof.
 intros. induction l.
  - simpl. remember (less n n0) as lt. destruct lt.
    * remember (Cons n0 l) as l0. simpl. rewrite Heql0 in H. rewrite Heql0.
      rewrite H. simpl. unfold leq. rewrite <- Heqlt. destruct (eqn n n0).
      + auto.
      + auto.
    * assert (sorted l = true). 
      + destruct l.
        ** simpl in H. unfold andb in H. remember (match l with | Cons y _ => if sorted l then leq n1 y else false
      | Nil => true end). destruct b.
          *** simpl. unfold andb. rewrite <- Heqb. reflexivity.
          *** inversion H.
        ** reflexivity.
      + remember (insort n l) as li. destruct li.
        ** apply lem3. apply IHl. assumption.
        assert ((sorted (Cons n1 li)) = true).
        ** apply IHl. apply H0.
        ** assert (leq n0 n1 = true).
           *** inversion H1. remember (leq n0 n1). destruct b.
              ++ rewrite H3. reflexivity.
              ++ destruct li.
                +++ rewrite H3. 
        remember (sorted (Cons n1 li)) as r1.
        remember (leq n0 n1) as r2.
        destruct andb.
        ** reflexivity.
        ** 
        ** simpl. simpl in IHl. unfold andb. 
           remember (match li with
  | Cons y _ => if sorted li then leq n1 y else false
  | Nil => true
  end). destruct b.
          *** *)
Admitted.
        

Theorem theorem0 : forall (x : lst), eq (sorted (sort x)) true.
Proof.
induction x.
  - simpl. apply lem. apply IHx.
  - reflexivity.
Qed.
