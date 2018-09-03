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

(*Definition GuardedValues := list (Prop * term)*)               

Inductive term : Type :=
| Theory : th -> term
| Location : loc -> term
| Union : list (Prop * term) -> term.

Fixpoint All {X : Type} (p : X -> Prop) (l : list X) : Prop :=
  match l with
  | [] => True
  | (x :: xs) => p x /\ All p xs
  end.

Fixpoint Any {X : Type} (p : X -> Prop) (l : list X) : Prop :=
  match l with
  | [] => False
  | (x :: xs) => p x \/ Any p xs
  end.

Fixpoint Union_app (ts : term) (g : Prop) (x : term) : term :=
  match ts with
  | Union l => Union ((g, x) :: l)
  | ts => Union []
  end.

Inductive empty_union : term -> Prop :=
| empty_union_nil: empty_union (Union [])
| empty_union_cons_empty: forall (t ts : term) (g : Prop),
    empty_union t -> empty_union ts -> empty_union (Union_app ts g t)
| empty_union_cons_false_guard: forall (t ts : term) (g : Prop),
    ~ g -> empty_union ts -> empty_union (Union_app ts g t)
.

Lemma empty_union_not_theory : forall (t : th), ~ empty_union (Theory t).
Proof. unfold not. intros. inversion H; induction ts; inversion H0. Qed.

Lemma empty_union_not_location : forall (l : loc), ~ empty_union (Location l).
Proof. unfold not. intros. inversion H; induction ts; inversion H0. Qed.

Reserved Notation "x =s= y" (at level 50).

Inductive semantically_equal : relation term :=
(*| semeq_th : forall (th1 th2 : th), th1 = th2 -> Theory th1 =s= Theory th2
| semeq_loc : forall (loc1 loc2 : loc), loc1 = loc2 -> Location loc1 =s= Location loc2*)
(*| semeq_symm : forall (t1 t2 : term), t1 =s= t2 -> t2 =s= t1*)
| semeq_unionr : forall (t : term) (l : list (Prop * term)), union_equal empty_union t (Union l) -> t =s= Union l
| semeq_unionl : forall (t : term) (l : list (Prop * term)), union_equal empty_union t (Union l) -> Union l =s= t
| semeq_eq : forall (t1 t2 : term), t1 = t2 -> t1 =s= t2
where "x =s= y" := (semantically_equal x y)
with union_equal : (term -> Prop) -> relation term :=
| uneq_nil : forall (isempty : term -> Prop) (x : term), isempty x -> union_equal isempty x (Union [])
| uneq_cons_false : forall (isempty : term -> Prop) (x v : term) (g : Prop) (gvs : list (Prop * term)),
  ~ g -> union_equal isempty x (Union gvs) -> union_equal isempty x (Union ((g, v) :: gvs))
| uneq_cons_true : forall (isempty : term -> Prop) (x v : term) (g : Prop) (gvs : list (Prop * term)),
  g -> x =s= v -> union_equal (fun _ => True) x (Union gvs) -> union_equal isempty x (Union ((g, v) :: gvs))
.

Lemma empty_test : forall (x : term), Union [] =s= Union [(False, x)].
Proof. intro x. repeat constructor. tauto. Qed.


(* ----------------------------------Relation lemmas-------------------------------------- *)
Instance union_equal_empty_is_reflexive : Reflexive (union_equal empty_union).
Proof. unfold Reflexive. intro x. admit. Admitted.


Instance semeq_is_reflexive : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x. destruct x; try repeat constructor. reflexivity. Qed.



(* ----------------------------------Properties lemmas-------------------------------------- *)
Lemma union_True : forall (t : term), Union [(True, t)] =s= t.
Proof. intro t. constructor. apply uneq_cons_true.
  - constructor.
  - reflexivity.
  - repeat constructor.
Qed.

Lemma union_false_erasing : forall (t : term) (gvs : list (Prop * term)), Union ((False, t) :: gvs) =s= Union gvs.
Proof. intros t gvs. apply semeq_unionr. apply uneq_cons_false; auto. reflexivity. Qed.

Lemma union_unfolding : forall (g : Prop) (xgvs ygvs : list (Prop * term)),
  Union ((g, Union xgvs) :: ygvs) =s= Union (map (fun x => match x with (g', v) => (g /\ g', v) end) xgvs ++ ygvs).
Proof. intros g xgvs ygvs. admit. Admitted.

Lemma union_same_value : forall (g1 g2 : Prop) (v : term) (gvs : list (Prop * term)),
  Union ((g1, v) :: (g2, v) :: gvs) =s= Union ((g1 \/ g2, v) :: gvs).
Proof. intros g1 g2 v gvs. induction gvs.
  - 