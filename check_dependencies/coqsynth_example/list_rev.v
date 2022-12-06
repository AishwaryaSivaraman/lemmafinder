
Inductive lst : Type :=
  | Nil : lst
  | Cons : nat -> lst -> lst.

Fixpoint append (l1 : lst) (l2 : lst) : lst :=
  match l1 with
  | Nil => l2
  | Cons x y => Cons x (append y l2)
  end.

Fixpoint rev (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons x y => append (rev y) (Cons x Nil)
  end.

Lemma append_nil : forall x : lst, append x Nil = x.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma append_assoc : forall x y z : lst,
  append x (append y z) = append (append x y) z.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma rev_append: forall x y : lst, rev (append x y) = append (rev y) (rev x).
Proof.
  intros.
  induction x.
  - simpl. rewrite append_nil. reflexivity.
  - simpl. rewrite IHx. rewrite append_assoc. reflexivity.
Qed.

Theorem rev_rev : forall x : lst, rev (rev x) = x.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl. rewrite rev_append. rewrite IHx. reflexivity.
Qed.
