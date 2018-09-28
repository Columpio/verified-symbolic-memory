Require Export Id.
Require Import Coq.Program.Wf.
Import Wf.WfExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Recdef.
(* From QuickChick Require Import QuickChick. *)
Import List.ListNotations.
Unset Intuition Negation Unfolding.

Variable op : Type.

Inductive loc : Type :=
| Concrete : id -> loc
| LI_loc : loc -> loc.

Inductive th : Type :=
| Op : op -> list th -> th
| LI_th : loc -> th.

Unset Elimination Schemes.
Inductive term : Type :=
| Theory : th -> term
| Location : loc -> term
| Union : list (Prop * term) -> term.
Set Elimination Schemes.

Section correct_term_ind.
Variables (P : term -> Prop).
(* (Q : list (Prop * term) -> Prop). *)

Hypotheses
  (Hth : forall (x : th), P (Theory x))
  (Hloc : forall (x : loc), P (Location x))
  (Hu_nil : P (Union []))
  (Hu_cons : forall (g : Prop) (v : term) (gvs : list (Prop * term)), P v -> P (Union gvs) -> P (Union ((g, v)::gvs))).

Fixpoint term_ind (t : term) : P t :=
  match t as x return P x with
  | Theory x => Hth x
  | Location x => Hloc x
  | Union gvs =>
    (* Hall gvs *)
      ((fix u_ind (gvs' : list (Prop * term)) : P (Union gvs') :=
        match gvs' as x return P (Union x) with
        | [] => Hu_nil
        | (g, v)::gvs'' => Hu_cons g v gvs'' (term_ind v) (u_ind gvs'')
        end) gvs)
  end.
End correct_term_ind.

Inductive empty_union : term -> Prop :=
| empty_union_nil: empty_union (Union [])
| empty_union_cons_empty: forall (g : Prop) (t : term) (ts : list (Prop * term)),
    g -> empty_union t -> empty_union (Union ts) -> empty_union (Union ((g, t) :: ts))
| empty_union_cons_false_guard: forall (g : Prop) (t : term) (ts : list (Prop * term)),
    ~ g -> empty_union (Union ts) -> empty_union (Union ((g, t) :: ts)).
Hint Constructors empty_union.


Reserved Notation "x =s= y" (at level 50).
Reserved Notation "x =u= y" (at level 50).
Reserved Notation "x =lu= y" (at level 50).

Definition empty_pair g v := ~g \/ empty_union v.
Hint Unfold empty_pair.

Inductive semantically_equal : relation term :=
(*| semeq_th : forall (th1 th2 : th), th1 = th2 -> Theory th1 =s= Theory th2
| semeq_loc : forall (loc1 loc2 : loc), loc1 = loc2 -> Location loc1 =s= Location loc2*)
(*| semeq_symm : forall (t1 t2 : term), t1 =s= t2 -> t2 =s= t1*)
| semeq_union : forall (gvs1 gvs2 : list (Prop * term)), gvs1 =u= gvs2 -> Union gvs1 =s= Union gvs2
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
  g /\ x =s= v /\ (empty_union (Union gvs) \/ x =lu= Union gvs) \/ ~g /\ x =lu= Union gvs -> x =lu= Union ((g, v)::gvs)
where "x =lu= y" := (union_equal_linear x y)
with union_equal : relation (list (Prop * term)) :=
| uneq_nil_l : forall (gvs : list (Prop * term)), empty_union (Union gvs) -> gvs =u= []
| uneq_nil_r : forall (gvs : list (Prop * term)), empty_union (Union gvs) -> [] =u= gvs
| uneq_e_e : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  empty_pair g1 v1 -> empty_pair g2 v2 -> gvs1 =u= gvs2 -> ((g1, v1)::gvs1) =u= ((g2, v2)::gvs2)
| uneq_e_ne : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  empty_pair g1 v1 -> ~ empty_pair g2 v2 -> gvs1 =u= ((g2, v2)::gvs2) -> ((g1, v1)::gvs1) =u= ((g2, v2)::gvs2)
| uneq_ne_e : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  ~ empty_pair g1 v1 -> empty_pair g2 v2 -> ((g1, v1)::gvs1) =u= gvs2 -> ((g1, v1)::gvs1) =u= ((g2, v2)::gvs2)
| uneq_ne_ne_l : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  ~ empty_pair g1 v1 -> ~ empty_pair g2 v2 -> v1 =s= v2 -> ((g1, v1)::gvs1) =u= gvs2
  -> ((g1, v1)::gvs1) =u= ((g2, v2)::gvs2)
| uneq_ne_ne_r : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  ~ empty_pair g1 v1 -> ~ empty_pair g2 v2 -> v1 =s= v2 -> gvs1 =u= ((g2, v2)::gvs2)
  -> ((g1, v1)::gvs1) =u= ((g2, v2)::gvs2)
| uneq_ne_ne : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  ~ empty_pair g1 v1 -> ~ empty_pair g2 v2 -> v1 =s= v2 -> gvs1 =u= gvs2
  -> ((g1, v1)::gvs1) =u= ((g2, v2)::gvs2)
where "x =u= y" := (union_equal x y).
Hint Constructors semantically_equal.
Hint Constructors union_equal.

Axiom excluded_middle : forall P : Prop, P \/ ~ P.
(* This axiom must only be used for guards, which occasionally are of type `Prop`.
   No "metatheoretic" usage is allowed *)


(* ----------------------------------Technical lemmas-------------------------------------- *)
Ltac ueqtauto :=
    try match goal with
    | [ H: Theory _ =s= _ |- _ ] => inversion_clear H
    | [ H: _ =s= Theory _ |- _ ] => inversion_clear H
    | [ H: Location _ =s= _ |- _ ] => inversion_clear H
    | [ H: _ =s= Location _ |- _ ] => inversion_clear H
    | [ H: Union _ =s= Union _ |- _ ] => inversion_clear H
    | [ H: _ =lu= Union (_::_) |- _ ] => inversion_clear H
    | [ H: (_::_) =u= (_::_) |- _ ] => inversion_clear H
    | [ H: _ =u= [] |- _ ] => inversion_clear H
    | [ H: [] =u= _ |- _ ] => inversion_clear H
    | [ H: empty_pair _ _ |- _ ] => inversion_clear H
    | _ => fail 1
    end; auto 6.

Lemma empty_union_dichotomy : forall (t : term), empty_union t \/ ~ empty_union t.
Proof. intros. induction t using term_ind; try now right. auto.
  intuition; destruct (excluded_middle g); auto; right; intro Hfalse; inversion_clear Hfalse; tauto.
Qed.

Lemma empty_pair_dichotomy : forall (g : Prop) (v : term), empty_pair g v \/ ~ empty_pair g v.
Proof. intros. unfold empty_pair. destruct (excluded_middle g); destruct (empty_union_dichotomy v); tauto. Qed.

Lemma union_s_to_u : forall (gvs1 gvs2 : list (Prop * term)), Union gvs1 =s= Union gvs2 -> gvs1 =u= gvs2.
Proof. intuition ueqtauto. Qed.
Hint Resolve union_s_to_u.


(* ----------------------------------Relation lemmas-------------------------------------- *)
Instance semeq_is_reflexive : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x. induction x using term_ind; ueqtauto. destruct (empty_pair_dichotomy g x); auto. Qed.
Hint Resolve semeq_is_reflexive.

Instance semeq_is_symmetric : Symmetric semantically_equal.
Proof. unfold Symmetric. intros x. induction x using term_ind; intros y Hxy; auto; destruct y; ueqtauto.
  - ueqtauto.
  - induction l as [|(g', v')]; ueqtauto.
Qed.


(* ----------------------------------Properties lemmas-------------------------------------- *)
Theorem empty_pair_cons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  empty_pair g v -> Union ((g, v)::gvs) =s= Union gvs.
Proof. intros g v gvs Hng. constructor. generalize dependent v. generalize dependent g. induction gvs as [|(g', v')]; intros.
  - destruct (excluded_middle g); ueqtauto.
  - destruct (empty_pair_dichotomy g v); destruct (empty_pair_dichotomy g' v'); auto.
Qed.
Hint Resolve empty_pair_cons.

Theorem guard_squashing : forall (g1 g2 : Prop) (v : term) (gvs : list (Prop * term)),
  Union ((g1, v)::(g2, v)::gvs) =s= Union ((g1 \/ g2, v)::gvs).
Proof. intros g1 g2 v gvs. constructor.
  destruct (excluded_middle g1); destruct (excluded_middle g2); destruct (empty_union_dichotomy v); auto 6.
  - apply uneq_ne_ne_r; intuition ueqtauto. apply uneq_ne_ne; intuition ueqtauto.
  - apply uneq_ne_ne; intuition ueqtauto.
  - apply uneq_e_ne; intuition ueqtauto. apply uneq_ne_ne; intuition ueqtauto.
  - apply uneq_e_e; auto. constructor. tauto.
Qed.

Theorem union_of_True : forall (t : term), Union [(True, t)] =s= t.
Proof. intros t. induction t using term_ind.
  4:{}. constructor. destruct (empty_union_dichotomy (Union ((g, t)::gvs))).
  + inversion_clear H; auto.
  + inversion_clear IHt0. destruct (empty_pair_dichotomy g t).
    * apply uneq_ne_e; auto. unfold empty_pair in *. tauto. admit. (*transitivity*)
    * apply uneq_ne_ne_l; intuition ueqtauto. admit. admit.
Admitted.



Lemma erase_empty_pair : forall (gy : Prop) (vy : term) (gvsx gvsy : list (Prop * term)),
  Union gvsx =u= Union gvsy -> empty_pair gy vy -> Union gvsx =u= Union ((gy, vy)::gvsy).
Proof. admit. Admitted. (*intros gy vy gvsx gvsy Hueq Hemp. induction gvsx as [|(gx, vx)]. admit.
  constructor. destruct (empty_pair_dichotomy gx vx).
  - do 2 right. intuition.*)



Instance semeq_is_transitive : Transitive semantically_equal.
Proof. unfold Transitive. intros x y z Hxy Hyz. generalize dependent x.
  induction y as [t | HHH | HHH | gy vy gvsy Hhead Htail] using term_ind; intros x Hxy.
  - admit.
  - admit.
  - admit.
  - destruct x.
    + admit.
    + admit. 
    + induction l as [|(gx, vx) gvsx]. admit. inversion_clear Hxy.
      destruct z.
      * admit.
      * admit.
      * induction l as [|(gz, vz) gvsz]. admit. inversion_clear Hyz. inversion_clear H; inversion_clear H0; intuition.
        ** do 2 constructor; auto.



Lemma empty_equal_hence_empty : forall (x y : term), x =s= y -> empty_union x -> empty_union y.
Proof. admit. Admitted.

Example two_truths_test : forall (x y : term), Union [(True, x)] =s= Union [(True, x); (True, y)] <->
   empty_union y \/ x =s= y.
Proof. intros x y. split; intro.
  - ueqtauto; ueqtauto; ueqtauto; ueqtauto; ueqtauto; ueqtauto.
  - ueqtauto.
    + ueqtauto. destruct (excluded_middle (empty_pair True x)).
      * do 2 right. do 4 ueqtauto. left. do 2 ueqtauto.
      * do 2 right. do 4 ueqtauto.
    + ueqtauto. destruct (excluded_middle (empty_pair True x)).
      * do 2 right. do 4 ueqtauto. eapply empty_equal_hence_empty; eauto. left. do 2 ueqtauto.
      * left. do 2 ueqtauto. do 2 right. do 3 ueqtauto. right. do 2 ueqtauto. apply H. ueqtauto.
        eapply empty_equal_hence_empty; eauto. admit. (* symmetry *)
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


Lemma union_unfolding : forall (g : Prop) (xgvs ygvs : list (Prop * term)),
  Union ((g, Union xgvs) :: ygvs) =s= Union (map (fun '(g', v) => (g /\ g', v)) xgvs ++ ygvs).
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