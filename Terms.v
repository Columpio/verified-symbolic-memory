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
  usimpl; repeat ueqtauto_step; simpl in *; intuition.

Lemma empty_union_dichotomy : forall (t : term), empty_union t \/ ~ empty_union t.
Proof. intros. induction t; try now right. auto.
  intuition; destruct (excluded_middle g); auto; right; intro Hfalse; inversion_clear Hfalse; tauto.
Qed.

Lemma disjoint_uncons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  Disjoint (Union ((g, v)::gvs)) -> Disjoint (Union gvs).
Proof. intros g v gvs Hdisj. inversion_clear Hdisj; ueqtauto. Qed.
Hint Resolve disjoint_uncons.

Lemma disjoint_non_empty : forall (gvs : list (Prop * term)),
  Disjoint (Union gvs) -> ~ empty_union (Union gvs)
  -> exists (gy : Prop) (vy : term), In (gy, vy) gvs /\ gy.
Proof. intros gvs Hdisj Hne. induction gvs as [|(g, v)]. exfalso. intuition.
  destruct (excluded_middle g). firstorder eauto.
  assert (Hdisj': Disjoint (Union gvs)). { eauto. } firstorder.
Qed.

Lemma in_empty_union : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  In (g, v) gvs -> empty_union (Union gvs) -> g -> empty_union v.
Proof. intros g v gvs Hin He Hg. (*remember (Union gvs) as t.*)
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

Lemma empty_unions_equal : forall (x y : term), empty_union x -> empty_union y -> x =s= y.
Proof. intros x y Hex Hey. inversion Hex; inversion Hey; auto. Qed.
Hint Resolve empty_unions_equal.

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

(* Lemma extract_property : forall (x : {}) *)

Lemma disjoint_dichotomy : forall (x : term), Disjoint x \/ ~ Disjoint x.
Proof. admit. Admitted.

Lemma first_equal : forall (g : Prop) (t1 t2 : term) (gvs : list (Prop * term)),
  Union ((g, t1)::gvs) =s= t2 -> g -> t1 =s= t2 \/ t2 =s= t1.
Proof. intros. induction t2. ueqtauto. firstorder eauto. ueqtauto. firstorder eauto.
  - inversion_clear H. exfalso. destruct (H3 g t1); auto. firstorder. left. eauto.
  - admit. Admitted.

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



(* ----------------------------------Relation lemmas-------------------------------------- *)
Instance disjoint_eq_is_symmetric : Symmetric disjoint_eq.
Proof. unfold Symmetric. intros x y Hxy. ueqtauto. induction Hxy; ueqtauto. eauto. Qed.
(* Hint Resolve disjoint_eq_is_symmetric. *)

Instance disjoint_eq_is_reflexive : Reflexive disjoint_eq.
Proof. unfold Reflexive. intros x. ueqtauto. induction d; auto; constructor; firstorder ueqtauto.
  - inversion_clear IHd; eauto.
  - enough (Disjoint vx); eauto. enough (exist Disjoint vx H2 =d= exist Disjoint vy d2).
    eauto. symmetry. eauto.
  - inversion_clear IHd1; eauto.
Qed.
Hint Resolve disjoint_eq_is_reflexive.

Lemma disjoint_property : forall (gx gy : Prop) (vx vy : term) (gvs : list (Prop * term)),
  In (gx, vx) gvs -> gx -> In (gy, vy) gvs -> gy -> Disjoint (Union gvs) -> vx =s= vy.
Proof. intros.
  enough (exist Disjoint (Union gvs) H3 =d= exist Disjoint (Union gvs) H3); auto.
  ueqtauto. inversion_clear H4; eauto.
Qed.

Instance semeq_is_transitive : Transitive disjoint_eq.
Proof. unfold Transitive. intros x y z Hxy Hyz. ueqtauto.
  rename x1 into y, x0 into z, d0 into Hy, d into Hz.
  destruct (empty_union_dichotomy x).
  generalize dependent x.
  induction Hyz as [gvsy gvsz _ _ Hyexz Hzexy Hyz Hind|HHH|HHH|HHH|HHH|HHH|HHH|HHH]; try congruence.
  - intros x Hx Hxy. inversion_clear Hxy.
    + constructor; auto. firstorder eauto. firstorder eauto. intros gx gz vx vz Hinx Hinz Hgx Hgz.
      specialize (H1 gx vx Hinx Hgx) as [gy [vy [Hiny Hgy]]]. eapply Hind; eauto.
    + apply empty_unions_equal; auto.
  induction y.
  - rename x into y. clear Hy. intros. 


(* ----------------------------------Properties lemmas-------------------------------------- *)


Lemma nempty_unions_equal : forall (t1 t2 : term), ~ empty_union t1 -> t1 =s= t2 -> ~ empty_union t2.
Proof. admit. Admitted.
  (* intros t1 t2 Hne1 Heq He2. apply Hne1. eapply empty_unions_equal; eauto. symmetry. assumption. Qed. *)

Theorem erase_empty_pair : forall (gy : Prop) (vy : term) (gvsx gvsy : list (Prop * term)),
  ~ gy -> Union gvsx =d= Union gvsy -> Union gvsx =d= Union ((gy, vy)::gvsy).
Proof. intros gy vy gvsx gvsy Hngy Heq. ueqtauto. remember (disjoint_uncons _ _ _ Hy) as Hy'. ueqtauto.
  clear Hy' HeqHy'. inversion_clear H0; auto. constructor; auto.
  + intuition. enough (exists (gy0 : Prop) (vy0 : term), In (gy0, vy0) gvsy /\ gy0); firstorder.
  + firstorder; congruence.
  + firstorder; congruence.
Qed.

Theorem guard_squashing : forall (g1 g2 : Prop) (v1 v2 : term) (gvs : list (Prop * term)),
  v1 =d= v2 -> Union ((g1, v1)::(g2, v2)::gvs) =d= Union ((g1 \/ g2, v2)::gvs).
Proof. intros g1 g2 v1 v2 gvs Hvv. ueqtauto.
  constructor; eauto.
  - intros. ueqtauto; firstorder eauto.
  - intros. ueqtauto; firstorder eauto. exists g2, vy; intuition.
  - intros. ueqtauto_step.
    + ueqtauto_step.
      ++ eauto.
      ++ ueqtauto_step.
        +++ apply disjoint_eq_is_reflexive; eauto.
        +++ eapply disjoint_property with (gvs := (g1 \/ g2, vy) :: gvs) (gx := gx); intuition.
    + ueqtauto_step.
      ++ eapply disjoint_property with (gvs := (gx, vx) :: (g2, v2) :: gvs) (gy := gy); intuition.
      ++ ueqtauto_step.
        +++ eapply disjoint_property with (gvs := (g1, v1) :: (gx, vx) :: gvs) (gx := gx) (gy := gy); intuition.
        +++ eapply disjoint_property; eauto.
Qed.

Lemma union_unfolding : forall (g : Prop) (xgvs ygvs : list (Prop * term)),
  Union ((g, Union xgvs) :: ygvs) =s= Union (map (fun '(g', v) => (g /\ g', v)) xgvs ++ ygvs).
Proof. intros g gvsx gvsy. admit. Admitted.















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






 (*unfold Transitive. intros x y z Hxy Hyz. generalize dependent x.
  induction y as [t | HHH | HHH | gy vy gvsy Hhead Htail] using term_ind; intros x Hxy.
  4:{}. destruct x.
  3:{}. induction l as [|(gx, vx) gvsx]. admit. inversion_clear Hxy.
      destruct z. 3:{}.
      induction l as [|(gz, vz) gvsz]. admit. inversion_clear Hyz. inversion_clear H; inversion_clear H0; intuition.*)


Lemma empty_empty_hence_equal : forall (x y : term), empty_union x -> empty_union y -> x =s= y.
Proof. admit. Admitted.
Hint Resolve empty_empty_hence_equal.

Example two_truths_test : forall (x y : term), Union [(True, x)] =s= Union [(True, x); (True, y)] <->
   empty_union y \/ x =s= y.
Proof. admit. Admitted.

Example truths_permut_test : forall (x y : term), Union [(True, x)] =s= Union [(True, x); (True, y)]
  <-> Union [(True, x)] =s= Union [(True, y); (True, x)].
Proof. admit. Admitted.

Example singles_test : forall (g1 g2 : Prop) (v1 v2 : term),
  [(g1, v1)] =u= [(g2, v2)] <->
  ~g1 /\ ~g2 \/
  g1 /\ ~g2 /\ empty_union v1 \/
  ~g1 /\  g2 /\ empty_union v2 \/
  g1 /\  g2 /\ v1 =s= v2.
Proof. intros. split; intro.
  - ueqtauto; unfold empty_pair in *; destruct (excluded_middle g2); destruct (excluded_middle g1);
    intuition; ueqtauto; try (match goal with | [H:empty_union (Union _)|-_] => inversion_clear H; tauto end).
  - intuition. destruct (empty_union_dichotomy v1); destruct (empty_union_dichotomy v2); auto.
    apply empty_equal_hence_empty in H2; tauto.
    symmetry in H2.
    apply empty_equal_hence_empty in H2; tauto.
    apply uneq_ne_ne; auto; unfold empty_pair; tauto.
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
