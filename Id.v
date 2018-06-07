Require Import BinNums.
Require Import ZArith.

Inductive id : Type :=
  Id : Z -> id.

Lemma id_eq_neq : forall (id1 id2 : id), {id1 <> id2} + {id1 = id2}.
Proof. intros. destruct id1, id2. remember (Z_noteq_dec z z0).
       destruct s.
       - left. unfold not in *. intro. apply n. inversion H. auto.
       - right. rewrite e. reflexivity. Qed.