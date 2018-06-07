Require Export Id.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Import List.ListNotations.

Variable op : Type.

Inductive loc : Type :=
| Concrete : id -> loc
| LI_loc : loc -> loc.

Inductive th : Type :=
| Op : op -> list th -> th
| LI_th : loc -> th.

(*Reserved Notation "x =t= y" (at level 99).

Inductive theory_equal : th -> th -> Prop :=
| theq_loc : forall (loc1 loc2 : loc), loc1 = loc2 -> LI_th loc1 =t= LI_th loc2
(* Something with Op ? *)
where "x =t= y" := (theory_equal x y).*)

Inductive term : Type :=
| Theory : th -> term
| Location : loc -> term
| Union : list (Prop * term) -> term.

Reserved Notation "x =s= y" (at level 50).

Inductive semantically_equal : relation term :=
(*| semeq_th : forall (th1 th2 : th), th1 = th2 -> Theory th1 =s= Theory th2
| semeq_loc : forall (loc1 loc2 : loc), loc1 = loc2 -> Location loc1 =s= Location loc2*)
| semeq_eq : forall (t1 t2 : term), t1 = t2 -> t1 =s= t2
| semeq_symm : forall (t1 t2 : term), t1 =s= t2 -> t2 =s= t1
| semeq_union_nil : forall (l : list (Prop * term)),
    ~ (fold_left (fun disj x => match x with (p, _) => disj \/ p end) l False)
    -> Union l =s= Union []
| semeq_union : forall (t : term) (l : list (Prop * term)),
    fold_left (fun disj x => match x with (p, t') => disj \/ (p /\ t =s= t') end) l False
    -> Union l =s= t
where "x =s= y" := (semantically_equal x y).

Lemma semeq_IsSymm : Symmetric semantically_equal.
Proof. unfold Symmetric. apply semeq_symm. Qed.

Lemma semeq_IsRefl : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x. induction x.
       - constructor. reflexivity.
       - constructor. reflexivity.
       - induction l.
         + apply semeq_union_nil. auto.
         + apply semeq_union. simpl.

  
Lemma union_True : forall (t : term), Union [(True, t)] =s= t.
Proof. 