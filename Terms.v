Require Export Id.
Require Import Coq.Program.Wf.
Import Wf.WfExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Recdef.
Require Import Coq.Program.Equality.
(* From QuickChick Require Import QuickChick. *)
Import List.ListNotations.
Unset Intuition Negation Unfolding.
Hint Resolve in_eq.


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


Reserved Notation "x =s= y" (at level 70).
Reserved Notation "x =lu= y" (at level 70).
Reserved Notation "x =d= y" (at level 70).

Inductive Disjoint : term -> Prop :=
| disjoint_th : forall (t : th), Disjoint (Theory t)
| disjoint_loc : forall (l : loc), Disjoint (Location l)
| disjoint_union_nil : Disjoint (Union [])
| disjoint_union_cons_e : forall (gvs : list (Prop * term)) (g : Prop) (v : term),
  Disjoint (Union gvs) -> ~ g -> Disjoint (Union ((g, v)::gvs))
| disjoint_union_cons_ne : forall (gvs : list (Prop * term)) (g1 : Prop) (v1 : term),
  Disjoint (Union gvs) -> g1 -> Disjoint v1->
  (forall (g2 : Prop) (v2 : term), In (g2, v2) gvs -> g2 -> v1 =s= v2) -> Disjoint (Union ((g1, v1)::gvs))
with semantically_equal : relation term :=
| semeq_union_nonempty : forall (gvsx gvsy : list (Prop * term)),
  Disjoint (Union gvsx) -> Disjoint (Union gvsy) ->
  (forall (gx : Prop) (vx : term), In (gx, vx) gvsx -> gx ->
    exists (gy : Prop) (vy : term), In (gy, vy) gvsy /\ gy) ->
  (forall (gy : Prop) (vy : term), In (gy, vy) gvsy -> gy ->
    exists (gx : Prop) (vx : term), In (gx, vx) gvsx /\ gx) ->
  (forall (gx gy : Prop) (vx vy : term),
    In (gx, vx) gvsx -> In (gy, vy) gvsy ->
    gx -> gy ->
    vx =s= vy) ->
  Union gvsx =s= Union gvsy
| semeq_union_empty : forall (gvsx gvsy : list (Prop * term)),
  empty_union (Union gvsx) -> empty_union (Union gvsy) -> Union gvsx =s= Union gvsy
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
| uneql : forall (x : term) (gvs : list (Prop * term)),
  Disjoint (Union gvs) ->
  (exists (g : Prop) (v : term), In (g, v) gvs /\ g) ->
  (forall (g : Prop) (v : term), In (g, v) gvs -> g -> x =s= v) -> x =lu= Union gvs
where "x =lu= y" := (union_equal_linear x y).
Hint Constructors Disjoint.
Hint Constructors union_equal_linear.
Hint Constructors semantically_equal.

Definition DisjointTerm := { x : term | Disjoint x }.

Definition extract {A: Type} {P: A -> Prop} (x : { y : A | P y }) : A :=
 match x with
 | exist _ y _ => y
 end.

Definition disjoint_eq (x y : { t : term | Disjoint t }) := (extract x) =s= (extract y).
Notation "x =d= y" := (disjoint_eq x y) (at level 70).
Hint Unfold disjoint_eq.


Axiom excluded_middle : forall P : Prop, P \/ ~ P.
(* This axiom must only be used for guards, which occasionally are of type `Prop`.
   No "metatheoretic" usage is allowed *)



(* ----------------------------------Technical lemmas-------------------------------------- *)
Ltac usimpl_step :=
  try match goal with
  (* | [ |- _ =s= _ ] => econstructor *)
  | [ |- _ =d= _ ] => unfold disjoint_eq
  end.

Ltac usimpl := repeat usimpl_step.

Ltac ueqtauto_step :=
  try match goal with
  | [ x: DisjointTerm |- _ ] => destruct x
  | [ x: {_ : term | Disjoint _} |- _ ] => destruct x
  | [ H: (_, _) = (_, _) |- _ ] => inversion H; subst; clear H
  | [ H: ?g |- Disjoint (Union ((?g, _)::_)) ] => eapply disjoint_union_cons_ne
  | [ H: In _ (_::_) |- _ ] =>
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    inversion_clear H as [Hx|Hy]; try (inversion Hx; subst; clear Hx)
  | [ H: _ =d= _ |- _ ] => unfold disjoint_eq in H
  | [ H: Theory _ =s= _ |- _ ] => inversion_clear H
  | [ H: _ =s= Theory _ |- _ ] => inversion_clear H
  | [ H: Location _ =s= _ |- _ ] => inversion_clear H
  | [ H: _ =s= Location _ |- _ ] => inversion_clear H
  | [ H: _ =lu= Union _ |- _ ] => inversion_clear H
  end.

Ltac ueqtauto :=
  usimpl; repeat ueqtauto_step; subst; simpl in *; intuition.

Lemma empty_union_dichotomy : forall (t : term), empty_union t \/ ~ empty_union t.
Proof. intros. induction t; try now right. auto.
  intuition; destruct (excluded_middle g); auto; right; intro Hfalse; inversion_clear Hfalse; tauto.
Qed.

Lemma disjoint_uncons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  Disjoint (Union ((g, v)::gvs)) -> Disjoint (Union gvs).
Proof. intros g v gvs Hdisj. inversion_clear Hdisj; ueqtauto. Qed.
Hint Resolve disjoint_uncons.

Lemma non_empty_hence_exists : forall (gvs : list (Prop * term)),
  ~ empty_union (Union gvs) -> exists (gy : Prop) (vy : term), In (gy, vy) gvs /\ gy.
Proof. intros gvs Hne. induction gvs as [|(g, v)]. exfalso. intuition.
  destruct (excluded_middle g); firstorder eauto. Qed.
Hint Resolve non_empty_hence_exists.

Lemma in_empty_union : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  In (g, v) gvs -> empty_union (Union gvs) -> g -> empty_union v.
Proof. intros g v gvs Hin He Hg.
  generalize dependent g. generalize dependent v. induction gvs as [|(g', v')];
  intros v g Hin Hg; inversion Hin.
  - ueqtauto; inversion_clear He; intuition. 
  - inversion_clear He; eauto.
Qed.
Hint Resolve in_empty_union.

Lemma empty_union_property : forall (gvs : list (Prop * term)),
  empty_union (Union gvs) <-> (forall (g : Prop) (v : term), In (g, v) gvs -> ~ g \/ empty_union v).
Proof. intro gvs. split.
  - intros Hemp g v Hin. destruct (excluded_middle g); eauto.
  - intros Hprop. induction gvs as [|(g', v')]. auto. destruct (excluded_middle g'); intuition. constructor; auto.
    + specialize (Hprop g' v'). firstorder.
    + firstorder.
Qed.

Lemma empty_unions_are_equal : forall (x y : term), empty_union x -> empty_union y -> x =s= y.
Proof. intros x y Hex Hey. inversion Hex; inversion Hey; auto. Qed.
Hint Resolve empty_unions_are_equal.

Lemma any_guard_dichotomy : forall (gvs : list (Prop * term)),
  (exists (gx : Prop) (vx : term), In (gx, vx) gvs /\ gx)
  \/ (forall (gx : Prop) (vx : term), In (gx, vx) gvs -> ~ gx).
Proof. intros gvs. induction gvs as [|(g, v)].
  - auto.
  - destruct (excluded_middle g).
    + left. exists g, v. intuition.
    + firstorder congruence.
Qed.

Lemma disjoint_unapp : forall (gvs gvs' : list (Prop * term)),
  Disjoint (Union (gvs' ++ gvs)) -> Disjoint (Union gvs).
Proof. intros gvs gvs' Hdisj. induction gvs' as [|(g', v')]. auto. apply IHgvs'.
  rewrite <- app_comm_cons in Hdisj. eauto using disjoint_uncons. Qed.

Lemma disjoint_element : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  Disjoint (Union gvs) -> g -> In (g, v) gvs -> Disjoint v.
Proof. intros. apply in_split in H1 as [l1 [l2]]; subst. apply disjoint_unapp in H.
  inversion_clear H; ueqtauto. Qed.
Hint Resolve disjoint_element.

Lemma empty_is_disjoint : forall (x : term), empty_union x -> Disjoint x.
Proof. intros x Hemp. induction Hemp; auto. ueqtauto. eauto. Qed.
Hint Resolve empty_is_disjoint.

Lemma empty_union_uncons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  empty_union (Union ((g, v)::gvs)) -> empty_union (Union gvs).
Proof. intros. inversion H; auto. Qed.
Hint Resolve empty_union_uncons.

Lemma eq_to_disj1 : forall (x y : term), x =s= y -> Disjoint x.
Proof. intros x y Hxy. induction Hxy; ueqtauto. Qed.

Lemma eq_to_disj2 : forall (x y : term), x =s= y -> Disjoint y.
Proof. intros x y Hxy. induction Hxy; ueqtauto. Qed.

(* Lemma disjoint_dichotomy : forall (x : term), Disjoint x \/ ~ Disjoint x.
Proof. admit. Admitted. *)

Lemma linear_equal_not_empty_th : forall (th1 : th) (t : term),
    Theory th1 =s= t -> empty_union t -> False.
Proof. intros th1 t Heq Hemp. induction t; try easy; ueqtauto. firstorder. firstorder.
  - ueqtauto. destruct (any_guard_dichotomy gvs).
    * apply IHt0; eauto 6.
    * apply IHt; eauto.
  - destruct (excluded_middle g).
    * apply IHt; eauto.
    * apply IHt0.
      ** do 2 constructor; eauto.
      ** eauto.
Qed.

Lemma linear_equal_not_empty_loc : forall (loc1 : loc) (t : term),
    Location loc1 =s= t -> empty_union t -> False.
Proof. intros loc1 t Heq Hemp. induction t; try easy; ueqtauto. firstorder. firstorder.
  - ueqtauto. destruct (any_guard_dichotomy gvs).
    * apply IHt0; eauto 6.
    * apply IHt; eauto.
  - destruct (excluded_middle g).
    * apply IHt; eauto.
    * apply IHt0.
      ** do 2 constructor; eauto.
      ** eauto.
Qed.

Lemma empty_union_equals : forall (t1 t2 : term), empty_union t1 -> t1 =s= t2 -> empty_union t2.
Proof. intros t1 t2 He1 Heq. induction Heq; try easy.
  - apply empty_union_property. intros. destruct (excluded_middle g); auto. right.
    specialize (H2 g v H5 H6) as [gx [vx [Hinx Hgx]]]. eapply H4; eauto.
  - exfalso. eauto using linear_equal_not_empty_th.
  - exfalso. eauto using linear_equal_not_empty_loc.
Qed.

Lemma nempty_unions_equals : forall (t1 t2 : term), ~ empty_union t1 -> t2 =s= t1 -> ~ empty_union t2.
Proof. eauto using empty_union_equals. Qed.


(* ----------------------------------Relation lemmas-------------------------------------- *)
Instance disjoint_eq_is_symmetric : Symmetric disjoint_eq.
Proof. unfold Symmetric. intros x y Hxy. ueqtauto. induction Hxy; ueqtauto. eauto. Qed.
(* Hint Resolve disjoint_eq_is_symmetric. *)

Instance semeq_is_symmetric : Symmetric semantically_equal.
Proof. unfold Symmetric. intros x y Heq.
  assert (Hdx: Disjoint x). { eauto using eq_to_disj1. }
  assert (Hdy: Disjoint y). { eauto using eq_to_disj2. }
  enough (exist Disjoint y Hdy =d= exist Disjoint x Hdx). auto. symmetry. eauto. Qed.
Hint Resolve semeq_is_symmetric.

Instance disjoint_eq_is_reflexive : Reflexive disjoint_eq.
Proof. unfold Reflexive. intros x. ueqtauto. induction d; auto; constructor; firstorder ueqtauto.
  - inversion_clear IHd; eauto.
  - inversion_clear IHd1; eauto.
Qed.
(* Hint Resolve disjoint_eq_is_reflexive. *)

Lemma semeq_is_reflexive : forall (x : term), Disjoint x -> x =s= x.
Proof. intros x Hdx. enough (exist Disjoint x Hdx =d= exist Disjoint x Hdx). auto. reflexivity. Qed.
Hint Resolve semeq_is_reflexive.

Lemma disjoint_property : forall (gx gy : Prop) (vx vy : term) (gvs : list (Prop * term)),
  In (gx, vx) gvs -> gx -> In (gy, vy) gvs -> gy -> Disjoint (Union gvs) -> vx =s= vy.
Proof. intros.
  enough (exist Disjoint (Union gvs) H3 =d= exist Disjoint (Union gvs) H3); auto.
  ueqtauto. inversion_clear H4; eauto.
Qed.

Lemma th_th_transitive : forall (th1 th2 : th) (t : term),
  Theory th1 =s= t -> Theory th2 =s= t -> th1 = th2.
Proof. intros th1 th2 t H1. induction t; intros; ueqtauto. firstorder.
  destruct (excluded_middle g).
  - apply IHt; eauto.
  - destruct (any_guard_dichotomy gvs).
    + apply IHt0; do 2 constructor; eauto.
    + destruct H4 as [g0 [v0]]. do 2 ueqtauto. firstorder.
Qed.

Lemma th_loc_not_transitive : forall (t : th) (l : loc) (v : term),
  Theory t =s= v -> Location l =s= v -> False.
Proof. intros t l v H1. induction v; intros; ueqtauto. firstorder.
  destruct (excluded_middle g).
  - apply IHv; eauto.
  - destruct (any_guard_dichotomy gvs).
    + apply IHv0; do 2 constructor; eauto.
    + destruct H4 as [g0 [v0]]. do 2 ueqtauto. firstorder.
Qed.

Lemma th_transitive : forall (t : th) (x y : term), Theory t =s= x -> Theory t =s= y -> x =s= y.
Proof. intros t x y Hx. generalize dependent y. induction x; intros; ueqtauto.
  constructor; auto. intros. ueqtauto.
  - eauto.
  - enough (Union gvs =s= Union gvs0). inversion_clear H0. eapply H13; eauto. eauto.
    apply IHx0; ueqtauto. do 2 constructor. eauto. exists gx, vx; auto. eauto.
Qed.

Lemma loc_loc_transitive : forall (loc1 loc2 : loc) (t : term),
  Location loc1 =s= t -> Location loc2 =s= t -> loc1 = loc2.
Proof. intros loc1 loc2 t H1. induction t; intros; ueqtauto. firstorder.
  destruct (excluded_middle g).
  - apply IHt; eauto.
  - destruct (any_guard_dichotomy gvs).
    + apply IHt0; do 2 constructor; eauto.
    + destruct H4 as [g0 [v0]]. do 2 ueqtauto. firstorder.
Qed.

Lemma loc_transitive : forall (t : loc) (x y : term), Location t =s= x -> Location t =s= y -> x =s= y.
Proof. intros t x y Hx. generalize dependent y. induction x; intros; ueqtauto.
  constructor; auto. intros. ueqtauto.
  - eauto.
  - enough (Union gvs =s= Union gvs0). inversion_clear H0. eapply H13; eauto. eauto.
    apply IHx0; ueqtauto. do 2 constructor. eauto. exists gx, vx; auto. eauto.
Qed.

Instance disjoint_eq_is_transitive : Transitive disjoint_eq.
Proof. unfold Transitive. intros x y z Hxy Hyz. ueqtauto.
  rename x1 into y, x0 into z, d0 into Hy, d into Hz.
    generalize dependent x.
  induction Hyz as [gvsy gvsz _ _ Hyexz Hzexy Hyz Hind|gvsy gvsz|HHH|HHH|thy gvsz Hyz|thz gvsy Hyz|locy gvsz Hyz|locz gvsy Hyz];
  try congruence.
  * intros x Hx Hxy. inversion Hxy; subst.
    + constructor; auto. firstorder eauto. firstorder eauto. intros gx gz vx vz Hinx Hinz Hgx Hgz.
      specialize (H2 gx vx Hinx Hgx) as [gy [vy [Hiny Hgy]]]. eapply Hind. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
      firstorder.
    + eauto using empty_union_equals.
    + constructor. clear Hxy. ueqtauto. firstorder. constructor; auto. firstorder. intros.
      eapply Hind; eauto.
    + constructor. clear Hxy. ueqtauto. firstorder. constructor; auto. firstorder. intros.
      eapply Hind; eauto.
  * eauto using empty_union_equals.
  * intros x Hdisjx Hxy. eauto using th_transitive.
  * intros x Hdisjx Hxy. apply semeq_th_u_r in Hyz. induction Hxy; try easy; try congruence.
    ** do 2 constructor; auto; ueqtauto.
      *** firstorder.
      *** apply semeq_is_symmetric. eauto. auto. destruct H7 as [gy' [vy' [Hin' Hgy']]]. eapply H4; eauto.
    ** eauto using empty_union_equals.
    ** constructor. eauto using th_th_transitive.
    ** ueqtauto.
    ** exfalso. eauto using th_loc_not_transitive.
  * intros x Hdisjx Hxy. eauto using loc_transitive.
  * intros x Hdisjx Hxy. apply semeq_loc_u_r in Hyz. induction Hxy; try easy; try congruence.
    ** do 2 constructor; auto; ueqtauto.
      *** firstorder.
      *** apply semeq_is_symmetric. eauto. auto. destruct H7 as [gy' [vy' [Hin' Hgy']]]. eapply H4; eauto.
    ** eauto using empty_union_equals.
    ** exfalso. eauto using th_loc_not_transitive.
    ** constructor. eauto using loc_loc_transitive.
    ** ueqtauto.
Qed.

(* Lemma semeq_is_symmetric : forall (x y : term), x =s= y -> y =s= x.
Proof. intros x y Heq.
  assert (Hdx: Disjoint x). { eauto using eq_to_disj1. }
  assert (Hdy: Disjoint y). { eauto using eq_to_disj2. }
  enough (exist Disjoint y Hdy =d= exist Disjoint x Hdx). auto. symmetry. eauto. Qed.
Hint Resolve semeq_is_symmetric. *)

Instance semeq_is_transitive : Transitive semantically_equal.
Proof. unfold Transitive. intros x y z Hxy Hyz.
  assert (Hdx: Disjoint x). { eauto using eq_to_disj1. }
  assert (Hdy: Disjoint y). { eauto using eq_to_disj2. }
  assert (Hdz: Disjoint z). { eauto using eq_to_disj2. }
  enough (exist Disjoint x Hdx =d= exist Disjoint z Hdz). auto.
  etransitivity. instantiate (1:=exist Disjoint y Hdy). auto. auto.
Qed.
Hint Resolve semeq_is_transitive.


(* ----------------------------------Properties lemmas-------------------------------------- *)
Lemma erase_empty_pair_from_union : forall (gy : Prop) (vy : term) (gvsx gvsy : list (Prop * term)),
  ~ gy -> Union gvsx =s= Union gvsy -> Union gvsx =s= Union ((gy, vy)::gvsy).
Proof. intros gy vy gvsx gvsy Hngy Heq. inversion_clear Heq; auto. constructor; auto.
  + intuition. enough (exists (gy0 : Prop) (vy0 : term), In (gy0, vy0) gvsy /\ gy0). firstorder. eauto.
  + firstorder; congruence.
  + firstorder; congruence.
Qed.

Theorem erase_empty_pair : forall (gy : Prop) (x vy : term) (gvsy : list (Prop * term)),
  ~ gy -> x =s= Union gvsy -> x =s= Union ((gy, vy)::gvsy).
Proof. intros gy x vy gvsy Hngy Heq. induction x.
  - ueqtauto. do 2 constructor. auto. firstorder. firstorder congruence.
  - ueqtauto. do 2 constructor. auto. firstorder. firstorder congruence.
  - eauto using empty_union_equals.
  - auto using erase_empty_pair_from_union.
Qed.

Theorem guard_squashing : forall (g1 g2 : Prop) (v1 v2 : DisjointTerm) (gvs : list (Prop * term)),
  Disjoint (Union ((g1, extract v1)::(g2, extract v2)::gvs)) ->
  Disjoint (Union ((g1 \/ g2, extract v2)::gvs)) ->
  v1 =d= v2 -> Union ((g1, extract v1)::(g2, extract v2)::gvs) =s= Union ((g1 \/ g2, extract v2)::gvs).
Proof. intros g1 g2 v1 v2 gvs Hl Hr Hvv. ueqtauto. rename x0 into v1, x into v2.
  constructor; auto; intros.
  - ueqtauto. exists (gx \/ g2), v2; auto. exists (g1 \/ gx), vx; auto. exists gx, vx; auto.
  - ueqtauto; firstorder eauto. exists g2, vy; auto.
  - ueqtauto.
    + eapply disjoint_property with (gvs := (g1 \/ g2, vy) :: gvs) (gx := gx); intuition.
    + eapply disjoint_property with (gvs := (g1 \/ g2, vy) :: gvs) (gx := gx); intuition.
    + eapply disjoint_property with (gvs := (gx, vx) :: (g2, v2) :: gvs) (gy := gy); intuition.
    + eapply disjoint_property with (gvs := (g1, v1) :: (gx, vx) :: gvs) (gx := gx) (gy := gy); intuition.
    + eapply disjoint_property; eauto.
Qed.

Definition InTerm gv t :=
  match t with
  | Union gvs => In gv gvs
  | _ => False
  end.

Lemma equal_to_disjoint : forall (g : Prop) (v t : term),
  Disjoint t -> InTerm (g, v) t -> g -> v =s= t.
Proof. intros g v t Hdisj Hin Hg.
  generalize dependent v. generalize dependent g.
  induction t; try easy. destruct (excluded_middle g).
  - intros. destruct (empty_union_dichotomy v).
    -- apply empty_unions_are_equal; auto. constructor; auto.
      + eapply empty_union_equals. eauto. unfold InTerm in Hin. eauto using disjoint_property.
      + rewrite empty_union_property. intros.
        destruct (excluded_middle g1); intuition. right. eapply empty_union_equals. eauto.
        eapply disjoint_property; eauto. eauto using in_cons.
    -- inversion_clear Hin. ueqtauto.
      + destruct v.
        * do 2 constructor. auto. eauto. do 2 ueqtauto.
          eapply disjoint_property with (gvs:=(g0, Theory t) :: gvs); eauto using in_cons.
        * do 2 constructor. auto. eauto. do 2 ueqtauto.
          eapply disjoint_property with (gvs:=(g0, Location l) :: gvs); eauto using in_cons.
        * constructor; auto. inversion_clear Hdisj; tauto. eauto. intros. ueqtauto.
          ** eapply IHt. inversion_clear Hdisj; tauto. exact H3. auto.
          ** enough (Union l =s= Union gvs). inversion_clear H2; intuition. eapply H9; eauto.
            apply semeq_is_transitive with (y := vy). inversion_clear Hdisj. tauto. eauto. eauto.
      + destruct v.
        * do 2 constructor. auto. eauto. do 2 ueqtauto.
          ** eapply disjoint_property with (gvs:=(g1, v) :: gvs); eauto using in_cons.
          ** etransitivity. eapply IHt0. inversion Hdisj; auto. exact Hg. auto. eauto.
        * do 2 constructor. auto. eauto. do 2 ueqtauto.
          ** eapply disjoint_property with (gvs:=(g1, v) :: gvs); eauto using in_cons.
          ** etransitivity. eapply IHt0. inversion Hdisj; auto. exact Hg. auto. eauto.
        * constructor; auto. eapply disjoint_element with (g:=g0) (gvs:=gvs); auto. eauto. eauto.
          assert (Heq: Union l =s= Union gvs). { eauto. }
          do 2 ueqtauto; inversion_clear Heq; intuition.
          ** specialize (H7 gx vx H2 H4) as [g' [v' [Hin' Hg']]].
            etransitivity. eapply H9. eauto. eauto. auto. auto.
            eapply disjoint_property with (gvs:=(gy, vy)::gvs). eauto using in_cons. eauto. eauto. auto. auto.
          ** eauto.
  - intros. inversion_clear Hin; ueqtauto. eauto using erase_empty_pair.
Qed.

Lemma equal_to_disjoint_union : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  Disjoint (Union gvs) -> In (g, v) gvs -> g -> v =s= Union gvs.
Proof. eauto using equal_to_disjoint. Qed.

Theorem union_of_true : forall (g : Prop) (v : term), g -> Disjoint v -> v =s= Union [(g, v)].
Proof. intros g v Hg Hdisj. eapply equal_to_disjoint_union; intuition. Qed.

Lemma union_unfolding : forall (g : Prop) (xgvs ygvs : list (Prop * term)),
  Disjoint (Union ((g, Union xgvs) :: ygvs)) ->
  Disjoint (Union (map (fun '(g', v) => (g /\ g', v)) xgvs ++ ygvs)) ->
  Union ((g, Union xgvs) :: ygvs) =s= Union (map (fun '(g', v) => (g /\ g', v)) xgvs ++ ygvs).
Proof. intros g gvsx gvsy Hdisjl Hdisjr.
  destruct gvsy.
  - rewrite app_nil_r in *.
    destruct (excluded_middle g) as [Hg|Hg].
    -- destruct (empty_union_dichotomy (Union gvsx)).
      + apply semeq_union_empty. destruct (excluded_middle g); auto.
        clear Hdisjl Hdisjr.
        induction gvsx as [|(gx, vx)]. auto.
        simpl. destruct (excluded_middle (g /\ gx)).
        * constructor; auto. inversion H; tauto. eauto.
        * eauto.
      + constructor; auto.
        * intros. ueqtauto. apply non_empty_hence_exists. intros Hemp. apply H. clear Hdisjl Hdisjr H H1.
          induction gvsx as [|(g, v)]. auto. inversion_clear Hemp; ueqtauto.
        * intros. exists g, (Union gvsx). auto.
        * do 2 ueqtauto.
    -- apply semeq_union_empty. auto. clear Hdisjl Hdisjr. induction gvsx as [|(gx, vx)]. auto.
      simpl. apply empty_union_cons_false_guard. tauto. auto.
  
  admit. Admitted.















Lemma cons_equal : forall (g : Prop) (v1 v2 : term) (gvs : list (Prop * term)),
  v1 =s= v2 -> (g, v1)::gvs =u= (g, v2)::gvs.
Proof. intros g v1 v2 gvs Heq.
  destruct (empty_pair_dichotomy g v1) as [He1 | Hne1].
  - destruct (excluded_middle g); usimpl. remember (empty_union_equals v1 v2 H0 Heq) as He2. auto.
  - enough (Hne2: ~ empty_pair g v2). auto. destruct (excluded_middle g); usimpl. eapply nempty_union_equals; eauto.
Qed.

(* Lemma equal_guards : forall (gvs gvs' : list (Prop * term)) (f : Prop -> Prop),
  (forall x, f x <-> x) -> gvs' = map (fun '(g, v) => (f g, v)) gvs -> gvs =u= gvs'.
Proof. intros gvs gvs' f Hf Hgvs'. generalize dependent gvs'. induction gvs as [|(g, v)].
  - admit.
  - intros gvs' Hgvs'. subst. simpl.

Theorem union_of_true' : forall (t : term), Union [(True, t)] =s= t.
Proof. intros t. induction t using term_ind.
  4:{}. remember (union_unfolding True ((g, t) :: gvs) []) as Hu. simpl in Hu. admit. (*transitivity*)
Admitted. *)

(* Theorem union_of_True' : forall (v : term), Disjoint v -> Union [(True, v)] =s= v. *)

Theorem union_of_True : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  Disjoint (Union ((g, v)::gvs)) -> ~ empty_pair g v -> Union ((g, v)::gvs) =s= v. (* TODO: the opposite direction *)
Proof. intros g v. generalize dependent g.
  induction v as [v|v|_|g' v' gvs' IHv IHgvs]; intros g gvs Hdisj Hne. (* 3:{}. exfalso. auto. *)
  4:{}. usimpl_step. destruct (empty_pair_dichotomy g' v').
  - usimpl_step. apply erase_empty_pair; auto. assert (Hl: (g, Union gvs') :: gvs =u= (g, Union ((g', v') :: gvs')) :: gvs).
    { apply cons_equal. symmetry. apply empty_pair_cons. assumption. } apply semeq_union in Hl. symmetry in Hl.
    apply union_s_to_u. etransitivity; eauto. clear Hl.
    apply IHgvs.
    + clear IHv IHgvs. apply empty_union_empty_pair_uncons in H1; auto.
      inversion_clear Hdisj. unfold empty_pair in H3. intuition. inversion_clear H4; usimpl.
      apply disjoint_union_cons_ne; auto.
      ++ usimpl.
      ++ usimpl.
      ++ intros g2 v2 Hin Hg2. specialize (H5 g2 v2 Hin Hg2). eapply unerase_empty_pair_s; eauto.
    + usimpl.
  - do 2 usimpl_step.
    assert (Hval: Union ((g', v')::gvs') =s= v'). { apply IHv; usimpl. }
    usimpl_step. usimpl. clear H4. usimpl_step. usimpl. clear H7. admit.
Admitted.
