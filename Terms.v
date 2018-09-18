Require Export Id.
Require Import Coq.Program.Wf.
Import Wf.WfExtensionality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Recdef.
Require Import Coq.omega.Omega.
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

(*
Fixpoint mergeSort (ls : list A) : list A :=
  if leb (length ls) 1
    then ls
    else let lss := split ls in
      merge (mergeSort (fst lss)) (mergeSort (snd lss)).

Definition mergeSort : list A -> list A.
  refine (Fix lengthOrder_wf (fun _ => list A)
    (fun (ls : list A)
      (mergeSort : forall ls' : list A, lengthOrder ls' ls -> list A) =>
      if le_lt_dec 2 (length ls)
        then let lss := split ls in
          merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
        else ls)); subst lss; eauto.
Defined.
*)

Fixpoint height (t : term) : nat :=
  match t with
  | Union gvs => 1 + fold_left Nat.max (map (fun gv => match gv with (g, v) => height v end) gvs) 0
  | _ => 1
  end.

Lemma height_pos : forall (t : term), height t > 0.
Proof. admit. Admitted.

Lemma height_nested : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  In (g, v) gvs -> height v < height (Union gvs).
Proof. intros. simpl. admit. Admitted.

Fixpoint map' {A B} (xs : list A) : forall (f : forall (x:A), In x xs -> B), list B :=
match xs with
  | [] => fun _ => []
  | x :: xs => fun f => f x (or_introl eq_refl) :: map' xs (fun y h => f y (or_intror h))
end.

Definition heightOrder (t1 t2 : term) := height t1 < height t2.

Hint Constructors Acc.

Lemma heightOrder_wf' : forall (len : nat) (t : term), height t <= len -> Acc heightOrder t.
Proof. intros. unfold heightOrder. induction len. inversion H. remember (height_pos t). omega. admit. Admitted.
(* Defined. *)
Theorem heightOrder_wf : well_founded heightOrder.
red; intro; eapply heightOrder_wf'; eauto.
Defined.

Program Fixpoint flatten (t : term) {measure (height t)} : term :=
  match t with
  | Union gvs => Union (concat (map' gvs (
    fun gv _ =>
      match gv with
      | (g, v) =>
        match flatten v with
        | Union gvs' => map' gvs' (fun gv' _ => match gv' with (g', v') => (g /\ g', v') end)
        | v' => [(g, v')]
        end
      end
    )))
  | _ => t
  end.
Next Obligation. eapply height_nested; eauto. Defined.
Print All.

Definition flatten_pair (gv : Prop * term) :=
  match gv with
  | (g, v) =>
    match flatten v with
    | Union gvs' => map (fun gv' => match gv' with (g', v') => (g /\ g', v') end) gvs'
    | v' => [(g, v')]
    end
  end.

Definition pretty_flatten (t : term) : term :=
  match t with
  | Union gvs => Union (concat (map flatten_pair gvs))
  | _ => t
  end.

Theorem flatten_eq : forall (t : term), flatten t = pretty_flatten t.
Proof. admit. Admitted.

Reserved Notation "x =s= y" (at level 50).
Reserved Notation "x =lu= y" (at level 50).
Reserved Notation "x =l= y" (at level 50).
Reserved Notation "x =u= y" (at level 50).

Inductive all_guards_false : term -> Prop :=
| all_false_nil : all_guards_false (Union [])
| all_false_cons : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  ~ g -> all_guards_false (Union gvs) -> all_guards_false (Union ((g, v)::gvs)).

Inductive linear_equal : relation term :=
| lineq_th : forall (th1 th2 : th), th1 = th2 -> Theory th1 =l= Theory th2
| lineq_loc : forall (loc1 loc2 : loc), loc1 = loc2 -> Location loc1 =l= Location loc2
| lineq_th_u_l : forall (th1 : th) (gvs : list (Prop * term)),
  Theory th1 =lu= Union gvs -> Theory th1 =l= Union gvs
| lineq_th_u_r : forall (th1 : th) (gvs : list (Prop * term)),
  Theory th1 =lu= Union gvs -> Union gvs =l= Theory th1
| lineq_loc_u_l : forall (loc1 : loc) (gvs : list (Prop * term)),
  Location loc1 =lu= Union gvs -> Location loc1 =l= Union gvs
| lineq_loc_u_r : forall (loc1 : loc) (gvs : list (Prop * term)),
  Location loc1 =lu= Union gvs -> Union gvs =l= Location loc1
| lineq_union : forall (gvs1 gvs2 : list (Prop * term)), Union gvs1 =u= Union gvs2 -> Union gvs1 =l= Union gvs2
where "x =l= y" := (linear_equal x y)
with union_equal_linear : relation term :=
| uneql : forall (g : Prop) (x v : term) (gvs : list (Prop * term)),
  g /\ (x = v \/ x =lu= Union gvs) \/ ~g /\ x =lu= Union gvs -> x =lu= Union ((g, v)::gvs)
where "x =lu= y" := (union_equal_linear x y)
with union_equal : relation term :=
| uneq_nil_l : forall (gvs : list (Prop * term)), all_guards_false (Union gvs) -> Union gvs =u= Union []
| uneq_nil_r : forall (gvs : list (Prop * term)), all_guards_false (Union gvs) -> Union [] =u= Union gvs
| uneq_cons : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
     ~ g1 /\ ~ g2 /\ Union gvs1 =u= Union gvs2
  \/ ~ g1 /\   g2 /\ Union gvs1 =u= Union ((g2, v2)::gvs2)
  \/   g1 /\ ~ g2 /\ Union ((g1, v1)::gvs1) =u= Union gvs2
  \/   g1 /\   g2 /\ v1 = v2 /\ (Union gvs1 =u= Union gvs2
                             \/ Union gvs1 =u= Union ((g2, v2)::gvs2)
                             \/ Union ((g1, v1)::gvs1) =u= Union gvs2)
  -> Union ((g1, v1)::gvs1) =u= Union ((g2, v2)::gvs2)
where "x =u= y" := (union_equal x y)
.

Definition semantically_equal (t1 t2 : term) : Prop := flatten t1 =l= flatten t2.
Notation "x =s= y" := (semantically_equal x y).

Reserved Notation "x =iu= y" (at level 50).
Inductive ind_union_equal : relation term :=
| iuneq_nil_l : forall (gvs : list (Prop * term)), all_guards_false (Union gvs) -> Union gvs =iu= Union []
| iuneq_nil_r : forall (gvs : list (Prop * term)), all_guards_false (Union gvs) -> Union [] =iu= Union gvs
| iuneq_cons_false_1 : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  ~ g1 -> Union gvs1 =iu= Union ((g2, v2)::gvs2) -> Union ((g1, v1)::gvs1) =iu= Union ((g2, v2)::gvs2)
| iuneq_cons_false_2 : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  ~ g2 -> Union ((g1, v1)::gvs1) =iu= Union gvs2 -> Union ((g1, v1)::gvs1) =iu= Union ((g2, v2)::gvs2)
| iuneq_cons : forall (g1 g2 : Prop) (v1 v2 : term) (gvs1 gvs2 : list (Prop * term)),
  g1 -> g2 -> v1 = v2 -> (Union gvs1 =iu= Union gvs2
                          \/ Union gvs1 =iu= Union ((g2, v2)::gvs2)
                          \/ Union ((g1, v1)::gvs1) =iu= Union gvs2) -> Union ((g1, v1)::gvs1) =iu= Union ((g2, v2)::gvs2)
where "x =iu= y" := (ind_union_equal x y).


(* ----------------------------------Technical stuff-------------------------------------- *)
Axiom excluded_middle : forall P : Prop, P \/ ~ P.

Ltac ueqtauto :=
  (* repeat progress ( *)
    try match goal with
    (* | [ H: empty_pair _ _ |- _ ] => inversion_clear H *)
    | [ H: empty_union (Union _) |- _ ] => inversion_clear H
    | [ H: Union _ =u= Union _ |- _ ] => inversion_clear H
    | [ H: Union _ =s= Union _ |- _ ] => inversion_clear H
    | [ H: context [flatten _] |- _ ] => rewrite flatten_eq in H; unfold pretty_flatten in H
    | [ |- _ =s= _ ] => unfold semantically_equal
    | [ |- Union _ =u= Union _ ] => constructor
    | [ |- Union _ =l= Union _ ] => constructor
    | [ |- empty_union (Union []) ] => constructor
    | [ |- empty_union (Union ((True, _)::_)) ] => apply empty_union_cons_empty
    | [ |- context [flatten _] ] => rewrite flatten_eq; unfold pretty_flatten
    (* | [ |- empty_pair True _ ] => unfold empty_pair; right *)
    | _ => fail 1
    end; intuition (* + intuition*)
  (* ) *)
  .

Ltac simpl_flatten_pair :=
    match goal with
    | [ |- context [flatten_pair (_, ?v)] ] =>
      simpl; destruct (flatten v); try (constructor; auto; constructor);
      try match goal with
      | [ |- context [Union (map _ ?l)] ] =>
        let g' := fresh "g" in
        let v' := fresh "v" in
        induction l as [|(g', v')]; simpl
      end;
      simpl
    end.

Theorem iu_eq_u : forall (gvs1 gvs2 : list (Prop * term)),
  Union gvs1 =u= Union gvs2 <-> Union gvs1 =iu= Union gvs2.
Proof. intros. split; intro.
  - admit.
  - generalize dependent gvs2. generalize dependent gvs1.
    induction gvs1 as [|(g1, v1)]; intros. constructor; inversion_clear H; assumption.
    inversion H; subst.
    + constructor. assumption.
    + constructor. destruct (excluded_middle g2).
      * intuition.
      * left. intuition. apply IHgvs1. inversion_clear H5.
        ** constructor. inversion_clear H1. assumption.
        ** 
    + constructor. destruct (excluded_middle g1).
      * right; right. left. intuition. inversion_clear H5.
  - generalize dependent gvs2. generalize dependent gvs1.
    induction gvs2 as [|(g2, v2)]; intro. constructor. inversion_clear H; assumption.
    induction gvs1 as [|(g1, v1)]. constructor. inversion_clear H. assumption.
    inversion_clear H. intuition.
    + constructor. tauto. apply IHgvs1.

Lemma cons_flatten : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  flatten (Union ((g, v)::gvs)) = Union (flatten_pair (g, v) ++ concat (map flatten_pair gvs)).
Proof. intros. ueqtauto. Qed.

Instance ueq_is_reflexive : Reflexive (fun gvs1 gvs2 => Union gvs1 =u= Union gvs2).
Proof. unfold Reflexive. intro gvs. induction gvs as [|(g, v)]; constructor. constructor.
  destruct (excluded_middle g); tauto. Qed.

Instance semeq_is_reflexive : Reflexive semantically_equal.
Proof. unfold Reflexive. intro x. destruct x; do 2 ueqtauto; constructor; auto. apply ueq_is_reflexive. Qed.

Lemma strange_lemm : 

Lemma eql_app_r : forall (gvs gvs1 gvs2 : list (Prop * term)), Union gvs1 =u= Union gvs2 ->
  Union (gvs1 ++ gvs) =u= Union (gvs2 ++ gvs).
Proof. intros. induction gvs2.
  - simpl. inversion_clear H.
    + induction gvs1 as [|(g1, v1)]. simpl. apply ueq_is_reflexive. inversion_clear H0.
    + simpl. apply ueq_is_reflexive.
admit. Admitted.

Lemma false_flatten_pair_app : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  ~ g -> Union (flatten_pair (g, v) ++ gvs) =u= Union gvs.
Proof. (* TODO: useless*)
  (*intros. generalize dependent v. generalize dependent g. induction gvs as [|(g', v')]; intros.
  - constructor. rewrite app_nil_r. simpl_flatten_pair.
    constructor. constructor. tauto. auto.
  - destruct (excluded_middle g'); simpl; destruct (flatten v).
      * constructor; right; left; intuition; apply ueq_is_reflexive.
      * constructor; right; left; intuition; apply ueq_is_reflexive.
      * induction l as [|(g'', v'')]; simpl. apply ueq_is_reflexive. constructor. tauto.
      * simpl. constructor. left; intuition. admit.
      * admit.
      * admit.*)
admit. Admitted.

Theorem false_erasing : forall (g : Prop) (v : term) (gvs : list (Prop * term)),
  ~ g -> Union ((g, v)::gvs) =s= Union gvs.
Proof. intros. ueqtauto. rewrite cons_flatten. ueqtauto. constructor.
  replace (Union (concat (map flatten_pair gvs))) with (Union ([] ++ concat (map flatten_pair gvs))); auto.
  apply eql_app_r. constructor. simpl_flatten_pair; constructor. tauto. auto.
Qed.

Lemma ueqflat_is_symmetric : forall (gvs1 gvs2 : list (Prop * term)),
  flatten (Union gvs1) =u= flatten (Union gvs2) -> flatten (Union gvs2) =u= flatten (Union gvs1).
Proof.
  intros. generalize dependent gvs1. induction gvs2 as [|(g2, v2)].
  - admit.
  - induction gvs1 as [|(g1, v1)].
    + admit.
    + intros. repeat rewrite cons_flatten in *.
  admit. Admitted.

Instance semeq_is_symmetric : Symmetric semantically_equal.
Proof. unfold Symmetric. intros x y Hxy. unfold semantically_equal in *.
  destruct x; destruct y; do 2 ueqtauto.
  - inversion_clear Hxy; subst. apply semeq_is_reflexive.
  - inversion Hxy.
  - admit.
  - inversion Hxy.
  - inversion_clear Hxy; subst. apply semeq_is_reflexive.
  - admit.
  - admit.
  - admit.
  - do 2 ueqtauto. constructor. inversion_clear Hxy. fold flatten. apply ueqflat_is_symmetric.

    admit. Admitted.
  

Example truth_erasing_test : forall (x : term), Union [(True, x)] =s= x.
Proof. intro x. ueqtauto. ueqtauto. simpl. rewrite app_nil_r.
  destruct (flatten x); try constructor; try constructor; try tauto. induction l as [|(g, v)]. simpl. do 2 constructor.
  simpl. constructor. intuition. destruct (excluded_middle g); tauto.
Qed.

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







 intro x. destruct x; constructor; auto.
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