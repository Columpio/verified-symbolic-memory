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

Fixpoint disjunct (gvs : list (Prop * term)) : Prop :=
  match gvs with
  | [] => False
  | ((g, _) :: gvs) => g \/ disjunct gvs
  end.

Inductive empty_union : term -> Prop :=
| empty_union_nil: empty_union (Union [])
| empty_union_cons_empty: forall (g : Prop) (t : term) (ts : list (Prop * term)),
    empty_union t -> empty_union (Union ts) -> empty_union (Union ((g, t) :: ts))
| empty_union_cons_false_guard: forall (g : Prop) (t : term) (ts : list (Prop * term)),
    ~ g -> empty_union (Union ts) -> empty_union (Union ((g, t) :: ts))
.

Lemma empty_union_not_theory : forall (t : th), ~ empty_union (Theory t).
Proof. unfold not. intros. inversion H; induction ts; inversion H0. Qed.

Lemma empty_union_not_location : forall (l : loc), ~ empty_union (Location l).
Proof. unfold not. intros. inversion H; induction ts; inversion H0. Qed.

Reserved Notation "x =s= y" (at level 50).
Reserved Notation "x =u= y" (at level 50).

Inductive semantically_equal : relation term :=
(*| semeq_th : forall (th1 th2 : th), th1 = th2 -> Theory th1 =s= Theory th2
| semeq_loc : forall (loc1 loc2 : loc), loc1 = loc2 -> Location loc1 =s= Location loc2*)
(*| semeq_symm : forall (t1 t2 : term), t1 =s= t2 -> t2 =s= t1*)
| semeq_unionr : forall (t : term) (l : list (Prop * term)), t =u= Union l -> t =s= Union l
| semeq_unionl : forall (t : term) (l : list (Prop * term)), t =u= Union l -> Union l =s= t
| semeq_eq : forall (t1 t2 : term), t1 = t2 -> t1 =s= t2
where "x =s= y" := (semantically_equal x y)
with union_equal : (term -> Prop) -> relation term :=
| uneq_nil : forall (isempty : term -> Prop) (x : term), isempty x -> union_equal isempty x (Union [])
| uneq_cons : forall (isempty : term -> Prop) (x v : term) (g : Prop) (gvs : list (Prop * term)),
  (g \/ disjunct gvs) /\
  ((~ g -> union_equal isempty x (Union gvs)) \/
   (g -> x =s= v /\ union_equal (fun _ => True) x (Union gvs))) -> union_equal isempty x (Union ((g, v) :: gvs))
where "x =u= y" := (union_equal empty_union x y)
.

Lemma empty_test : forall (x : term), Union [] =s= Union [(False, x)].
Proof. intro x. apply semeq_unionl. constructor. apply empty_union_cons_false_guard. tauto. constructor. Qed.





(* ----------------------------------Relation lemmas-------------------------------------- *)
Instance union_equal_empty_is_reflexive : Reflexive (union_equal empty_union).
Proof. unfold Reflexive. intro x. admit. Admitted.

Instance semeq_is_reflexive : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x. destruct x; try repeat constructor. reflexivity. Qed.

Instance unino_equal_empty_is_symmetric : Symmetric (union_equal empty_union).
Proof. unfold Symmetric. intros x y Hxy. admit. Admitted.
  
Instance semeq_is_symmetric : Symmetric semantically_equal.
Proof. unfold Symmetric. intros x y Hxy. destruct x; destruct y; inversion_clear Hxy; admit. Admitted.

Instance unino_equal_empty_is_transitive : Transitive (union_equal empty_union).
Proof. unfold Transitive. intros x y z Hxy Hyz. admit. Admitted.

Instance semeq_is_transitive : Transitive semantically_equal.
Proof. unfold Transitive. intros x y z Hxy Hyz. destruct x; destruct y; inversion_clear Hxy; admit. Admitted.


(* ----------------------------------Technical lemmas-------------------------------------- *)
Lemma union_Uequal_split : forall (gvs1 gvs2 : list (Prop * term)),
  Union gvs1 =u= Union gvs2 <-> (forall (x : term), x =u= Union gvs1 <-> x =u= Union gvs2).
Proof. intros gvs1 gvs2. split; intro H.
  - intro x. split; intro Hg.
    + symmetry in H. etransitivity; eauto.
    + etransitivity; eauto.
  - apply H. reflexivity.
Qed.

Lemma union_Sequal_split : forall (gvs1 gvs2 : list (Prop * term)),
  Union gvs1 =s= Union gvs2 <-> (forall (x : term), Union gvs1 =s= x <-> Union gvs2 =s= x).
Proof. intros gvs1 gvs2. split; intro H.
  - intro x. split; intro Hg.
    + symmetry in H. etransitivity; eauto.
    + etransitivity; eauto.
  - apply H. reflexivity.
Qed.


(* ----------------------------------Properties lemmas-------------------------------------- *)
Lemma union_True : forall (t : term), Union [(True, t)] =s= t.
Proof. intro t. constructor. apply uneq_cons. right. intros _. split.
  - reflexivity.
  - repeat constructor.
Qed.

Lemma union_false_erasing : forall (t : term) (gvs : list (Prop * term)), Union ((False, t) :: gvs) =s= Union gvs.
Proof. intros t gvs. apply semeq_unionl. apply uneq_cons. left. intros _. reflexivity. Qed.

Lemma union_unfolding : forall (g : Prop) (xgvs ygvs : list (Prop * term)),
  Union ((g, Union xgvs) :: ygvs) =s= Union (map (fun x => match x with (g', v) => (g /\ g', v) end) xgvs ++ ygvs).
Proof. intros g xgvs ygvs. admit. Admitted.

Lemma union_same_value_lr : forall (g1 g2 : Prop) (v x : term), x =u= Union [(g1, v); (g2, v)] <-> x =u= Union [(g1 \/ g2, v)].
Proof. admit. Admitted.

Lemma union_same_value : forall (g1 g2 : Prop) (v : term) (gvs : list (Prop * term)),
  Union ((g1, v) :: (g2, v) :: gvs) =s= Union ((g1 \/ g2, v) :: gvs).
Proof. intros g1 g2 v gvs. induction gvs.
  - apply union_Sequal_split. intro x. split; intro H; constructor; inversion_clear H;
    try (subst; apply union_same_value_lr; auto); solve [reflexivity | symmetry; assumption].
  - 
Qed.