Require Export Id.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
(* From QuickChick Require Import QuickChick. *)
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

Fixpoint disjunct (gvs : list (Prop * term)) : Prop :=
  match gvs with
  | [] => False
  | ((g, _) :: gvs) => g \/ disjunct gvs
  end.

Inductive empty_union : term -> Prop :=
| empty_union_nil: empty_union (Union [])
| empty_union_cons_empty: forall (g : Prop) (t : term) (ts : list (Prop * term)),
    g -> empty_union t -> empty_union (Union ts) -> empty_union (Union ((g, t) :: ts))
| empty_union_cons_false_guard: forall (g : Prop) (t : term) (ts : list (Prop * term)),
    ~ g -> empty_union (Union ts) -> empty_union (Union ((g, t) :: ts))
.

Lemma empty_union_not_theory : forall (t : th), ~ empty_union (Theory t).
Proof. unfold not. intros. inversion H; induction ts; inversion H0. Qed.

Lemma empty_union_not_location : forall (l : loc), ~ empty_union (Location l).
Proof. unfold not. intros. inversion H; induction ts; inversion H0. Qed.

Reserved Notation "x =s= y" (at level 50).
Reserved Notation "x =u= y" (at level 50).
Reserved Notation "x =lu= y" (at level 50).

Definition empty_pair g v := ~g \/ empty_union v.

Inductive semantically_equal : relation term :=
(*| semeq_th : forall (th1 th2 : th), th1 = th2 -> Theory th1 =s= Theory th2
| semeq_loc : forall (loc1 loc2 : loc), loc1 = loc2 -> Location loc1 =s= Location loc2*)
(*| semeq_symm : forall (t1 t2 : term), t1 =s= t2 -> t2 =s= t1*)
| semeq_union : forall (gvs1 gvs2 : list (Prop * term)), Union gvs1 =u= Union gvs2 -> Union gvs1 =s= Union gvs2
| semeq_th : forall (th1 th2 : th), th1 = th2 -> Theory th1 =s= Theory th2
| semeq_loc : forall (loc1 loc2 : loc), loc1 = loc2 -> Location loc1 =s= Location loc2
| semeq_th_u_l : forall (th1 : th) (gvs : list (Prop * term)),
  Theory th1 =lu= Union gvs -> Theory th1 =s= Union gvs
| semeq_th_u_r : forall (th1 : th) (gvs : list (Prop * term)),
  Theory th1 =lu= Union gvs -> Union gvs =s= Theory th1
| semeq_loc_u_l : forall (loc1 : loc) (gvs : list (Prop * term)),
  Location loc1 =lu= Union gvs -> Location loc1 =s= Union gvs
| semeq_loc_u_r : forall (loc1 : loc) (gvs : list (Prop * term)),
  Location loc1 =lu= Union gvs -> Union gvs =s= Location loc1
where "x =s= y" := (semantically_equal x y)
with union_equal_linear : relation term :=
| uneql : forall (g : Prop) (x v : term) (gvs : list (Prop * term)),
  g /\ x =s= v \/ ~g /\ x =lu= Union gvs -> x =lu= Union ((g, v)::gvs)
where "x =lu= y" := (union_equal_linear x y)
with union_equal : relation term :=
| uneq_nil_l : forall (gvs : list (Prop * term)), empty_union (Union gvs) -> Union gvs =u= Union []
| uneq_nil_r : forall (gvs : list (Prop * term)), empty_union (Union gvs) -> Union [] =u= Union gvs
| uneq_cons : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
     ~empty_pair g1 v1 /\ Union ((g1, v1)::gvs1) =u= Union gvs2 /\ (empty_pair g2 v2 \/ ~empty_pair g2 v2 /\ v1 =s= v2)
  \/ ~empty_pair g2 v2 /\ Union gvs1 =u= Union ((g2, v2)::gvs2) /\ (empty_pair g1 v1 \/ ~empty_pair g1 v1 /\ v1 =s= v2)
  \/ Union gvs1 =u= Union gvs2 /\ (empty_pair g1 v1 /\ empty_pair g2 v2 \/ ~empty_pair g1 v1 /\ ~empty_pair g2 v2 /\ v1 =s= v2)
  -> Union ((g1, v1)::gvs1) =u= Union ((g2, v2)::gvs2)
where "x =u= y" := (union_equal x y)
.

Axiom excluded_middle : forall P : Prop, P \/ ~ P.


Ltac ueqtauto :=
  (* repeat progress ( *)
    try match goal with
    | [ H: empty_pair _ _ |- _ ] => inversion_clear H
    | [ H: empty_union (Union _) |- _ ] => inversion_clear H
    | [ H: Union _ =u= Union _ |- _ ] => inversion_clear H
    | [ H: Union _ =s= Union _ |- _ ] => inversion_clear H
    | [ |- Union _ =s= Union _ ] => constructor
    | [ |- Union _ =u= Union _ ] => constructor
    | [ |- empty_union (Union []) ] => constructor
    | [ |- empty_union (Union ((True, _)::_)) ] => apply empty_union_cons_empty
    | [ |- empty_pair True _ ] => unfold empty_pair; right
    | _ => fail 1
    end; intuition (* + intuition*)
  (* ) *)
  .


(* ----------------------------------Common tests-------------------------------------- *)
Example empty_test : forall (x : term), Union [] =s= Union [(False, x)].
Proof. intro x. do 2 constructor. apply empty_union_cons_false_guard. tauto. constructor.
Qed.

Example truth_erasing_test : forall (x : term), Union [(True, x)] =s= x.
Proof. admit. Admitted.

Lemma empty_equal_hence_empty : forall (x y : term), x =s= y -> empty_union x -> empty_union y.
Proof. admit. Admitted.

Example two_truths_test : forall (x y : term), Union [(True, x)] =s= Union [(True, x); (True, y)] <->
   empty_union y \/ x =s= y.
Proof. intros x y. split; intro.
  - ueqtauto; ueqtauto; ueqtauto; ueqtauto; ueqtauto; ueqtauto.
  - ueqtauto.
    + ueqtauto. destruct (excluded_middle (empty_pair True x)).
      * do 2 right. do 4 ueqtauto. left. do 2 ueqtauto.
      * do 2 right. do 4 ueqtauto. right. ueqtauto. admit.
    + ueqtauto. destruct (excluded_middle (empty_pair True x)).
      * do 2 right. do 4 ueqtauto. eapply empty_equal_hence_empty; eauto. left. do 2 ueqtauto.
      * left. do 2 ueqtauto. do 2 right. do 3 ueqtauto. right. do 2 ueqtauto. apply H. ueqtauto.
        eapply empty_equal_hence_empty; eauto. admit. right. ueqtauto. admit.
Admitted.

Example truths_permut_test : forall (x y : term), Union [(True, x)] =s= Union [(True, x); (True, y)]
  <-> Union [(True, x)] =s= Union [(True, y); (True, x)].

Example singles_test : forall (g1 g2 : Prop) (v1 v2 : term),
Union [(g1, v1)] =u= Union [(g2, v2)] <->
~g1 /\ ~g2 \/
 g1 /\ ~g2 /\ empty_union v1 \/
~g1 /\  g2 /\ empty_union v2 \/
 g1 /\  g2 /\ v1 =s= v2.
Proof. intros. split; intro.
- inversion_clear H; simpl in *. inversion_clear H0; inversion_clear H; inversion_clear H1.
  + inversion_clear H; tauto.
  + right; right. symmetry in H. inversion_clear H.
    * inversion_clear H1; inversion_clear H.
      ** left. repeat split; try tauto. inversion_clear H1. inversion_clear H3. assumption.
      ** right. repeat split; try tauto. destruct H1 as [_ [H _]]. symmetry. assumption.
    * symmetry in H1. inversion_clear H1. inversion_clear H.
      ** left. repeat split; try tauto. inversion_clear H1. inversion_clear H3. assumption.
      ** right. repeat split; try tauto. destruct H1 as [_ [H _]]. symmetry. assumption.
- constructor. destruct H as [[Hng1 Hng2] | [[Hg1 [Hng2 Hev1]] | [[Hng1 [Hg2 Hev2]] | [Hg1 [Hg2 Heq]]]]].
  + left; split; try tauto. constructor. apply empty_union_cons_false_guard. tauto. constructor.
  + left; split; try tauto. constructor. apply empty_union_cons_empty. tauto. assumption. constructor.
  + right; split; try tauto. split; constructor; try tauto. constructor. left. split; try tauto. constructor. assumption.
  + right; split; try tauto. split; constructor; try tauto. constructor. right. split; try tauto.
    split. symmetry. assumption. constructor. tauto.
Qed.







Instance semeq_is_reflexive : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x. destruct x; constructor; auto.
  induction l as [|(g, v)]; constructor. repeat constructor. destruct (excluded_middle g).
  - do 3 right. intuition.
    + (* v =s= v *) admit.
    + (*l ~u~ gvl*)
      induction l as [| (g', v')]; constructor. right. inversion_clear IHl. intuition.
      * left. intuition. admit.
      * do 2 right. intuition. admit. admit. constructor. tauto.
    + (*gvl ~u~ l*) admit.
  - tauto.
Admitted.

(* ----------------------------------Relation lemmas-------------------------------------- *)
Lemma u_hence_neu : forall (gvs1 gvs2 : list (Prop * term)),
  Union gvs1 =u= Union gvs2 -> Union gvs1 =neu= Union gvs2.
Proof. intros. induction gvs2 as [| (g, v)]; inversion_clear H; constructor. tauto. Qed.

Lemma empty_eq_neu : forall (gvs : list (Prop * term)), empty_union (Union gvs) <-> Union [] =neu= Union gvs.
Proof. admit. Admitted.

Lemma u_to_empty : forall (gvs : list (Prop * term)), Union [] =u= Union gvs -> empty_union (Union gvs).
Proof. admit. Admitted.

Theorem union_eq_symmetric : forall (gvs1 gvs2 : list (Prop * term)),
  Union gvs1 =u= Union gvs2 -> Union gvs2 =u= Union gvs1.
Proof. intros. induction gvs1 as [| (g, v)]; constructor.
  - induction gvs2 as [| (g, v)].
    + now inversion_clear H.
    + inversion_clear H. intuition.
      * apply empty_union_cons_false_guard; tauto.
      * apply empty_union_cons_empty; try tauto.
        ** inversion_clear H. auto using u_to_empty. now inversion_clear H1.
        ** now apply empty_eq_neu.
  - inversion H; subst. admit. intuition. 
  
  (* induction gvs2 as [| (g, v)].
  - inversion_clear H. induction H0; constructor.
    + constructor.
    + right; intuition. now repeat constructor. auto using neu_empty.
    + tauto.
  - *)
  
  (*remember (Union gvs1). induction H; subst; auto.
  - induction H; constructor.
    + constructor.
    + right. intuition.
      * now repeat constructor.
      * inversion_clear IHempty_union2; constructor. intuition auto using u_hence_neu.
    + tauto.
  - intuition. admit. Admitted.*)

Instance union_equal_empty_is_symmetric : Symmetric (union_equal empty_union).
Proof. unfold Symmetric. intros x y Hxy. destruct y; destruct x.
  - inversion Hxy.
  - inversion Hxy.
  - inversion_clear Hxy; assumption.
  - inversion Hxy.
  - inversion Hxy.
  - inversion_clear Hxy; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - apply union_eq_symmetric. assumption.
Qed.

Theorem semeq_left_part : forall (g : Prop) (t : term) (gvs : list (Prop * term)),
  ~g -> Union gvs =u= Union gvs -> Union gvs =u= Union ((g, t) :: gvs).
Proof. intros. constructor. tauto. Qed.

Theorem semeq_right_part : forall (g : Prop) (t : term) (gvs : list (Prop * term)),
  g -> Union gvs =u= Union gvs -> t =u= Union ((g, t) :: gvs) /\ union_equal (fun _ : term => True) t (Union gvs).
Proof. intros. split.
  - constructor. right.

Instance semeq_is_reflexive : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x.
  induction semantically_equal.
  
  
  destruct x; try repeat constructor. induction l.
  - repeat constructor.
  - destruct a as [g t]. constructor.
    assert (H: ~ g /\ Union l =u= Union ((g, t) :: l)
      \/ g /\ t =u= Union ((g, t) :: l) /\ union_equal (fun _ : term => True) t (Union l)).
    { admit. }
    destruct H as [[Hng Hu] | [Hg [Ht Hu]]].
    + left; split; try tauto. symmetry. assumption.
    + right; split; try tauto. split. constructor. assumption. assumption.
Qed.

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
Proof. intros g1 g2 v gvs. induction gvs; apply union_Sequal_split; intro x.
  - split; intro H; constructor; inversion_clear H;
    try (subst; apply union_same_value_lr; auto); solve [reflexivity | symmetry; assumption].
  - split; intro H.
    + constructor. inversion_clear H.
Qed.