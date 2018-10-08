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
Reserved Notation "x =u= y" (at level 70).
Reserved Notation "x =lu= y" (at level 70).

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

Inductive Disjoint : term -> Prop :=
| disjoint_th : forall (t : th), Disjoint (Theory t)
| disjoint_loc : forall (l : loc), Disjoint (Location l)
| disjoint_union_nil : Disjoint (Union [])
| disjoint_union_cons_e : forall (gvs : list (Prop * term)) (g : Prop) (v : term),
  Disjoint (Union gvs) -> empty_pair g v -> Disjoint (Union ((g, v)::gvs))
| disjoint_union_cons_ne : forall (gvs : list (Prop * term)) (g1 : Prop) (v1 : term),
  Disjoint (Union gvs) -> ~ empty_pair g1 v1  -> Disjoint v1->
  (forall (g2 : Prop) (v2 : term), In (g2, v2) gvs -> g2 -> v1 =s= v2) -> Disjoint (Union ((g1, v1)::gvs)).
Hint Constructors Disjoint.


Axiom excluded_middle : forall P : Prop, P \/ ~ P.
(* This axiom must only be used for guards, which occasionally are of type `Prop`.
   No "metatheoretic" usage is allowed *)


(* ----------------------------------Technical lemmas-------------------------------------- *)
Lemma not_empty_pair : forall (g : Prop) (v : term), ~ empty_pair g v -> g /\ ~ empty_union v.
Proof. intros g v Hne. unfold empty_pair in Hne. destruct (excluded_middle g); tauto. Qed.

Ltac usimpl_step :=
  try match goal with
  | [ |- _ =s= _ ] => constructor
  | [ |- context [ empty_pair _ _ ] ] => unfold empty_pair
  | [ H: Union _ =s= Union _ |- _ ] => inversion_clear H
  | [ H: ~ empty_pair _ _ |- _ ] => apply not_empty_pair in H; intuition
  | [ H: empty_pair _ _ -> False |- _ ] => apply not_empty_pair in H; intuition
  | [ H: empty_pair _ _ |- _ ] => inversion_clear H; intuition
  | [ H: Disjoint (Union (_::_)) |- _ ] => inversion_clear H
  end.

Ltac usimpl := repeat usimpl_step.

Ltac ueqtauto :=
  usimpl; try match goal with
  | [ H: Theory _ =s= _ |- _ ] => inversion_clear H
  | [ H: _ =s= Theory _ |- _ ] => inversion_clear H
  | [ H: Location _ =s= _ |- _ ] => inversion_clear H
  | [ H: _ =s= Location _ |- _ ] => inversion_clear H
  | [ H: Union _ =s= Union _ |- _ ] => inversion_clear H
  | [ H: _ =lu= Union (_::_) |- _ ] => inversion_clear H
  | [ H: (_::_) =u= (_::_) |- _ ] => inversion_clear H
  | [ H: _ =u= [] |- _ ] => inversion_clear H
  | [ H: [] =u= _ |- _ ] => inversion_clear H
  | _ => fail 1
  end; auto 6.

Lemma empty_union_dichotomy : forall (t : term), empty_union t \/ ~ empty_union t.
Proof. intros. induction t; try now right. auto.
  intuition; destruct (excluded_middle g); auto; right; intro Hfalse; inversion_clear Hfalse; tauto.
Qed.

Lemma empty_pair_dichotomy : forall (g : Prop) (v : term), empty_pair g v \/ ~ empty_pair g v.
Proof. intros. usimpl. destruct (excluded_middle g); destruct (empty_union_dichotomy v); tauto. Qed.

Lemma empty_union_empty_pair : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  empty_pair g v -> empty_union (Union gvs) -> empty_union (Union ((g, v)::gvs)).
Proof. intros g v gvs Hep Heu. destruct (excluded_middle g); usimpl. Qed.
Hint Resolve empty_union_empty_pair.

Lemma empty_union_empty_pair_uncons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  empty_pair g v -> ~ empty_union (Union ((g, v)::gvs)) -> ~ empty_union (Union gvs).
Proof. intros g v gvs Hneu Heu. destruct (excluded_middle g); usimpl. Qed.

Lemma union_s_to_u : forall (gvs1 gvs2 : list (Prop * term)), Union gvs1 =s= Union gvs2 -> gvs1 =u= gvs2.
Proof. intuition ueqtauto. Qed.
Hint Resolve union_s_to_u.

Lemma super_lemma : forall (g : Prop) (v t : term) (gvs : list (Prop * term)),
  Union ((g, v)::gvs) =s= t -> g /\ v =s= t \/ Union gvs =s= t.
Proof. admit. Admitted.

Lemma empty_union_equals : forall (t1 t2 : term), empty_union t1 -> t1 =s= t2 -> empty_union t2.
Proof. intros t1 t2 Hempt1 Heq. induction t1 using term_ind. easy. easy. destruct t2; do 2 ueqtauto; easy.
  apply super_lemma in Heq. inversion_clear Hempt1; tauto. Qed.


(* ----------------------------------Relation lemmas-------------------------------------- *)
Instance semeq_is_reflexive : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x. induction x; ueqtauto. destruct (empty_pair_dichotomy g x); auto. Qed.
Hint Resolve semeq_is_reflexive.

Instance semeq_is_symmetric : Symmetric semantically_equal.
Proof. unfold Symmetric. intros x. induction x; intros y Hxy; auto; destruct y; ueqtauto.
  induction l as [|(g', v')]; ueqtauto.
Qed.

Instance semeq_is_transitive : Transitive semantically_equal.
Proof. unfold Transitive. intros x y z Hxy Hyz.
  generalize dependent x. induction y.
  4:{}. intros x Hxy. induction x. 4:{}. induction z. 4:{}.
  admit. Admitted.


(* ----------------------------------Disjoint lemmas-------------------------------------- *)
Lemma disjoint_uncons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  Disjoint (Union ((g, v)::gvs)) -> Disjoint (Union gvs).
Proof. intros g v gvs Hdisj. usimpl; auto. Qed.

Lemma disjoint_unapp : forall (gvs gvs' : list (Prop * term)),
  Disjoint (Union (gvs' ++ gvs)) -> Disjoint (Union gvs).
Proof. intros gvs gvs' Hdisj. induction gvs' as [|(g', v')]. auto. apply IHgvs'.
  rewrite <- app_comm_cons in Hdisj. eauto using disjoint_uncons. Qed.

Lemma disjoint_property : forall (gvs : list (Prop * term)),
  Disjoint (Union gvs) -> forall (g1 g2 : Prop) (v1 v2 : term),
    In (g1, v1) gvs -> In (g2, v2) gvs -> ~ empty_pair g1 v1 -> ~ empty_pair g2 v2 -> v1 =s= v2.
Proof. intros gvs Hdisj g1 g2 v1 v2 H1 H2 He1 He2. apply in_split in H1 as [gvs1 [gvs2]]; subst.
  usimpl. apply in_app_or in H2 as [Hgvs1 | Hgvs2].
  - apply in_split in Hgvs1 as [gvs1' [gvs1'']]; subst. rewrite <- app_assoc in Hdisj.
    apply disjoint_unapp in Hdisj. rewrite <- app_comm_cons in Hdisj. usimpl.
    specialize (H6 g1 v1). symmetry. apply H6. apply in_or_app. intuition. tauto.
  - inversion_clear Hgvs2.
    + inversion_clear H2. reflexivity.
    + apply disjoint_unapp in Hdisj. usimpl. eauto.
Qed.


(* ----------------------------------Properties lemmas-------------------------------------- *)
Lemma nempty_union_equals : forall (t1 t2 : term), ~ empty_union t1 -> t1 =s= t2 -> ~ empty_union t2.
Proof. intros t1 t2 Hne1 Heq He2. apply Hne1. eapply empty_union_equals; eauto. symmetry. assumption. Qed.

Theorem empty_pair_cons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  empty_pair g v -> Union ((g, v)::gvs) =s= Union gvs.
Proof. intros g v gvs Hng. constructor. generalize dependent v. generalize dependent g. induction gvs as [|(g', v')]; intros.
  - destruct (excluded_middle g); ueqtauto.
  - destruct (empty_pair_dichotomy g v); destruct (empty_pair_dichotomy g' v'); auto.
Qed.
Hint Resolve empty_pair_cons.

Lemma erase_empty_pair : forall (gy : Prop) (vy : term) (gvsx gvsy : list (Prop * term)),
  gvsx =u= gvsy -> empty_pair gy vy -> gvsx =u= (gy, vy)::gvsy.
Proof. intros gy vy gvsx. generalize dependent gy. generalize dependent vy. induction gvsx as [|(gx, vx)]; intros.
  - destruct (excluded_middle gy); do 2 ueqtauto.
  - destruct (empty_pair_dichotomy gx vx); auto. constructor; auto.
    induction gvsy as [|(gy', vy')]; inversion_clear H; intuition. constructor. inversion_clear H2; auto.
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
