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

Reserved Notation "x =s= y" (at level 50).

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

Inductive sem_empty : term -> Prop :=
| sem_empty_nil: sem_empty (Union [])
| sem_empty_cons_empty: forall (t ts : term) (g : Prop),
    sem_empty t -> sem_empty ts -> sem_empty (Union_app ts g t)
| sem_empty_cons_false_guard: forall (t ts : term) (g : Prop),
    ~ g -> sem_empty ts -> sem_empty (Union_app ts g t)
.

Lemma sem_empty_not_theory : forall (t : th), ~ sem_empty (Theory t).
Proof. unfold not. intros. inversion H; induction ts; inversion H0. Qed.

Lemma sem_empty_not_location : forall (l : loc), ~ sem_empty (Location l).
Proof. unfold not. intros. inversion H; induction ts; inversion H0. Qed.

Fixpoint sem_equal (t1 : term) :=
  fix sem_equal1 (t2 : term) :=
    sem_empty t1 /\
    sem_empty t2
    \/ match t1 with
       | Union l =>
         fold_left (fun disj x => match x with (p, t) => disj \/ p /\ (sem_equal t t2) end) l False
       | _ =>
         match t2 with
         | Union l =>
           Any (fun x => match x with (p, t) => p /\ sem_equal1 t end) l (*
           fold_right (fun x disj => match x with (p, t) => disj \/ p /\ (sem_equal1 t) end) False l*)
           (*fold_left (fun disj x => match x with (p, t) => disj \/ p /\ (sem_equal1 t) end) l False *)
         | _ => t1 = t2
         end
       end
where "x =s= y" := (sem_equal x y).

Lemma union_uncons_l : forall (g : Prop) (t x : term) (l : GuardedValues),
    g /\ t =s= x \/ Union l =s= x <-> Union ((g, t) :: l) =s= x.
Proof. admit. Admitted.

Lemma union_uncons_r : forall (g : Prop) (t x : term) (l : GuardedValues),
    x =s= Union ((g, t) :: l) <-> g /\ t =s= x \/ x =s= Union l.
Proof. admit. Admitted.

Ltac sem_empty_simpl :=
  try match goal with
      | [ H : sem_empty (Theory _) |- _ ] => apply sem_empty_not_theory in H; tauto
      | [ H : sem_empty (Location _) |- _ ] => apply sem_empty_not_location in H; tauto
      end.

Ltac semeq_simpl :=
  try match goal with
  | [ H : Theory _ =s= Theory _ |- _ ] =>
    destruct H as [[?A ?B] | ?C]; sem_empty_simpl; inversion_clear C
  | [ H : Location _ =s= Location _ |- _ ] =>
    destruct H as [[?A ?B] | ?C]; sem_empty_simpl; inversion_clear C
  | [ H : Location _ =s= Theory _ |- _ ] =>
    destruct H as [[?A _] | ?C]; sem_empty_simpl; inversion C
  | [ H : Theory _ =s= Location _ |- _ ] =>
    destruct H as [[_ ?A] | ?C]; sem_empty_simpl; inversion C
  | [ H : Theory _ =s= Union [] |- _ ] =>
    inversion_clear H as [[?A _] | ?C]; sem_empty_simpl
  | [ H : Location _ =s= Union [] |- _ ] =>
    inversion_clear H as [[?A _] | ?C]; sem_empty_simpl
  | [ H : Union [] =s= Theory _ |- _ ] =>
    inversion_clear H as [[_ ?A] | ?C]; sem_empty_simpl
  | [ H : Union [] =s= Location _ |- _ ] =>
    inversion_clear H as [[_ ?A] | ?C]; sem_empty_simpl
  end;
try (simpl; tauto).

Lemma semeq_theories : forall (t1 t2 : th), t1 = t2 <-> Theory t1 =s= Theory t2.
Proof. intros. split; intros; subst; simpl; auto. semeq_simpl. Qed.

Lemma semeq_locations : forall (l1 l2 : loc), l1 = l2 <-> Location l1 =s= Location l2.
Proof. intros. split; intros; subst; simpl; auto. semeq_simpl. Qed.

Lemma semeq_IsSymm : Symmetric sem_equal.
Proof. unfold Symmetric. intros. destruct x, y; semeq_simpl.
       - induction g. semeq_simpl. destruct a. apply union_uncons_l. apply union_uncons_r in H.
         destruct H; auto.
       - induction g. semeq_simpl. destruct a. apply union_uncons_l. apply union_uncons_r in H.
         destruct H; auto.
       - induction g. semeq_simpl. destruct a. apply union_uncons_r. apply union_uncons_l in H.
         destruct H; auto.
       - induction g. semeq_simpl. destruct a. apply union_uncons_r. apply union_uncons_l in H.
         destruct H; auto.
       - induction g0.
         + simpl. left. split. constructor. inversion H as [[A _] | C]. assumption.
       - induction g.
         + simpl in *. destruct H as [[_ B] | C].
           * left. split. assumption. constructor.
           * admit.
         + 

Lemma kek : forall (g : Prop) (t' trm : term) (l : GuardedValues),
    fold_left (fun disj x => match x with (p, t) => disj \/ p /\ (t =s= t') end) ((g, trm) :: l) False = fold_left (fun disj x => match x with (p, t) => disj \/ p /\ (t =s= t') end) l False \/ g /\ trm =s= t'.
Proof. intros. simpl. admit. Admitted.

Lemma union_cons_simpl : forall (g : Prop) (t x : term) (gv : GuardedValues),
    Union ((g, t) :: gv) =s= x -> Union gv =s= x \/ g /\ t =s= x.
Proof. intros. unfold semantically_equal in H; fold semantically_equal in H. simpl in H.
       simpl. admit. Admitted.

Lemma semeq_IsRefl : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x. destruct x. simpl; auto. simpl; auto.
       induction g. simpl; auto. unfold semantically_equal; fold semantically_equal.
       replace (a :: g) with ([a] ++ g); auto. rewrite fold_left_app.
       simpl. destruct a. admit. Admitted.


(* ----------------------------------Meaningfull lemmas-------------------------------------- *)

Lemma union_True : forall (t : term), Union [(True, t)] =s= t.
Proof. intro t. simpl. right. split; auto. apply semeq_IsRefl. Qed.
