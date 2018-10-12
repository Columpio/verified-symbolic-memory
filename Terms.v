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
  Disjoint (Union gvs) -> (forall (g : Prop) (v : term), In (g, v) gvs -> x =s= v) -> x =lu= Union gvs
where "x =lu= y" := (union_equal_linear x y).
Hint Constructors Disjoint.
Hint Constructors union_equal_linear.
Hint Constructors semantically_equal.

Definition disjoint_eq x y := Disjoint x -> Disjoint y -> x =s= y.
Notation "x =d= y" := (disjoint_eq x y) (at level 70).
Hint Unfold disjoint_eq.


Axiom excluded_middle : forall P : Prop, P \/ ~ P.
(* This axiom must only be used for guards, which occasionally are of type `Prop`.
   No "metatheoretic" usage is allowed *)



(* ----------------------------------Technical lemmas-------------------------------------- *)
Ltac usimpl_step :=
  try match goal with
  (* | [ |- _ =s= _ ] => econstructor *)
  | [ |- _ =d= _ ] =>
    let x := fresh "Hx" in
    let y := fresh "Hy" in  
    unfold disjoint_eq; intros x y
  end.

Ltac usimpl := repeat usimpl_step.

Ltac ueqtauto :=
  usimpl; repeat try match goal with
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
  end; intuition.

Lemma empty_union_dichotomy : forall (t : term), empty_union t \/ ~ empty_union t.
Proof. intros. induction t; try now right. auto.
  intuition; destruct (excluded_middle g); auto; right; intro Hfalse; inversion_clear Hfalse; tauto.
Qed.

Lemma disjoint_non_empty : forall (gvs : list (Prop * term)),
  Disjoint (Union gvs) -> ~ empty_union (Union gvs)
  -> exists (gy : Prop) (vy : term), In (gy, vy) gvs /\ gy.
Proof. intros gvs Hdisj Hne. induction gvs as [|(g, v)]. exfalso. intuition.
  destruct (excluded_middle g). exists g, v. intuition.
  assert (Hdisj': Disjoint (Union gvs)). { inversion Hdisj; assumption. }
  assert (Hne': ~ empty_union (Union gvs)). { auto. }
  enough (exists (gy : Prop) (vy : term), In (gy, vy) gvs /\ gy). destruct H0 as [gy [vy HH]].
  exists gy, vy. intuition. tauto.
Qed.

Lemma in_empty_union : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  In (g, v) gvs -> empty_union (Union gvs) -> g -> empty_union v.
Proof. intros g v gvs Hin He Hg. (*remember (Union gvs) as t.*)
  generalize dependent g. generalize dependent v. induction gvs as [|(g', v')];
  intros v g Hin Hg; inversion Hin.
  - inversion H; subst; clear H. inversion_clear He. assumption. tauto.
  - inversion_clear He; eauto.
Qed.
Hint Resolve in_empty_union.

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

Lemma disjoint_uncons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  Disjoint (Union ((g, v)::gvs)) -> Disjoint (Union gvs).
Proof. intros g v gvs Hdisj. inversion_clear Hdisj; ueqtauto. Qed.
Hint Resolve disjoint_uncons.

Lemma disjoint_unapp : forall (gvs gvs' : list (Prop * term)),
  Disjoint (Union (gvs' ++ gvs)) -> Disjoint (Union gvs).
Proof. intros gvs gvs' Hdisj. induction gvs' as [|(g', v')]. auto. apply IHgvs'.
  rewrite <- app_comm_cons in Hdisj. eauto using disjoint_uncons. Qed.

Lemma disjoint_element : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  In (g, v) gvs -> g -> Disjoint (Union gvs) -> Disjoint v.
Proof. intros. apply in_split in H as [l1 [l2]]; subst. apply disjoint_unapp in H1.
  inversion_clear H1; ueqtauto. Qed.
Hint Resolve disjoint_element.


(* ----------------------------------Relation lemmas-------------------------------------- *)
Instance disjoint_eq_is_symmetric : Symmetric disjoint_eq.
Proof. unfold Symmetric. intros x. induction x; intros y Hxy.
  - destruct y; do 2 ueqtauto.
  - destruct y; do 2 ueqtauto.
  - destruct y; do 2 ueqtauto; inversion_clear H0; ueqtauto. clear H1 H2 H4 Hy H Hx.
    assert (Hle: forall (gy : Prop) (vy : term), In (gy, vy) l -> ~ gy).
    { firstorder. } clear H3. apply semeq_union_empty; auto. induction l as [|(g, v)]. auto. firstorder eauto.
  - destruct y; do 2 ueqtauto. inversion_clear H0; auto.
    destruct (any_guard_dichotomy gvs) as [Hany|Hall].
    -- enough (Union l =s= Union gvs) as Htail.
      + constructor; auto. do 2 ueqtauto.
        * apply IHx; eauto.
        * inversion_clear Htail; eauto.
      + apply IHx0; auto. ueqtauto. constructor; firstorder. eauto.
    -- constructor; auto. do 2 ueqtauto.
      + apply IHx; eauto.
      + firstorder.
Qed.
Hint Resolve disjoint_eq_is_symmetric.

Instance disjoint_eq_is_reflexive : Reflexive disjoint_eq.
Proof. unfold Reflexive. unfold disjoint_eq. intros x HdisjBig _. induction x; auto.
  destruct (empty_union_dichotomy (Union ((g, x)::gvs))); auto. constructor; firstorder; ueqtauto;
  inversion_clear HdisjBig; firstorder; match goal with [H: Union _ =s= Union _ |- _] => inversion_clear H end; eauto;
  enough (vx =d= vy); eauto.
Qed.
Hint Resolve disjoint_eq_is_reflexive.


Instance semeq_is_transitive : Transitive semantically_equal.
Proof. admit. Admitted.


(* ----------------------------------Properties lemmas-------------------------------------- *)
Lemma empty_union_equals : forall (t1 t2 : term), empty_union t1 -> t1 =s= t2 -> empty_union t2.
Proof. admit. Admitted.

Lemma nempty_unions_equal : forall (t1 t2 : term), ~ empty_union t1 -> t1 =s= t2 -> ~ empty_union t2.
Proof. admit. Admitted.
  (* intros t1 t2 Hne1 Heq He2. apply Hne1. eapply empty_unions_equal; eauto. symmetry. assumption. Qed. *)

Theorem erase_empty_pair : forall (gy : Prop) (vy : term) (gvsx gvsy : list (Prop * term)),
  ~ gy -> Union gvsx =d= Union gvsy -> Union gvsx =d= Union ((gy, vy)::gvsy).
Proof. intros gy vy gvsx gvsy Hngy Heq. ueqtauto. remember (disjoint_uncons _ _ _ Hy) as Hy'. ueqtauto.
  clear Hy' HeqHy'. inversion_clear H0; auto. constructor; auto.
  + intuition. enough (exists (gy0 : Prop) (vy0 : term), In (gy0, vy0) gvsy /\ gy0); firstorder.
  + firstorder congruence.
  + firstorder. inversion H5; subst; tauto.
Qed.

Lemma unerase_empty_pair : forall (g : Prop) (v : term) (gvs gvs' : list (Prop * term)),
  empty_pair g v -> (g, v)::gvs =u= gvs' -> gvs =u= gvs'.
Proof. intros g v gvs gvs' He Heq. induction gvs' as [|(g', v')].
  - inversion_clear Heq. inversion_clear H; auto.
  - destruct (empty_pair_dichotomy g' v'); inversion_clear Heq; auto using erase_empty_pair; tauto.
Qed.

Lemma unerase_empty_pair_s : forall (g : Prop) (v t : term) (gvs : list (Prop * term)),
empty_pair g v -> Union ((g, v)::gvs) =s= t -> Union gvs =s= t.
Proof. intros g v t gvs Hep Heq. inversion_clear Heq; constructor; eauto using unerase_empty_pair;
  inversion_clear H; intuition; usimpl; exfalso; symmetry in H; apply empty_union_equals in H; auto; inversion H.
Qed.

Theorem guard_squashing : forall (g1 g2 : Prop) (v1 v2 : term) (gvs : list (Prop * term)),
  v1 =s= v2 -> Union ((g1, v1)::(g2, v2)::gvs) =s= Union ((g1 \/ g2, v1)::gvs).
Proof. intros g1 g2 v1 v2 gvs Hvv. constructor.
  destruct (excluded_middle g1); destruct (excluded_middle g2); destruct (empty_union_dichotomy v1); auto 6.
  - eapply empty_union_equals in H1 as H2; eauto 10.
  - apply uneq_ne_ne_r; intuition ueqtauto. apply uneq_ne_ne; intuition ueqtauto.
    apply H1. eapply empty_union_equals; eauto. all: symmetry; assumption.
  - apply uneq_ne_ne; intuition ueqtauto.
  - eapply empty_union_equals in H1 as H2; eauto 10.
  - apply uneq_e_ne; intuition ueqtauto. apply uneq_ne_ne; intuition ueqtauto.
    apply H1. eapply empty_union_equals; eauto. all: symmetry; assumption.
  - apply uneq_e_e; auto. constructor. tauto.
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
