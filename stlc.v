Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality. (* for dependent induction *)
Require Import as2.

(* contexts *)
Definition ctxt n := fin n -> ty. (* this definition of a context lets us more readily use autosubst's notation and substitution machinery *)

Definition empty : ctxt 0 := fun x : fin 0 => let t := match x return ty with
                                                       end in t.

(* value relation *)
Inductive value {n} : tm n -> Prop :=
| v_abs : forall T t,
    value (lam T t)
| v_true : value ttrue
| v_false : value tfalse.

Hint Constructors value.

(* evaluation relation *)
Reserved Notation "t --> t'" (at level 50).
Inductive red {n} : tm n -> tm n -> Prop :=
| red_beta : forall (t : tm (S n)) (t' : tm n) (T: ty), (app (lam T t) t') --> (t [t' ..])
| red_app_1 : forall t1 t1' t2, t1 --> t1' ->
                                (app t1 t2) --> (app t1' t2)
| red_app_2 : forall t1 t2 t2', t2 --> t2' -> 
                                (app t1 t2) --> (app t1 t2')
| red_tif_disc : forall t1 t1' t2 t3, t1 --> t1' -> 
                                      (tif t1 t2 t3) --> (tif t1' t2 t3)
| red_tif_true : forall t2 t3, (tif ttrue t2 t3) --> t2
| red_tif_false : forall t2 t3, (tif tfalse t2 t3) --> t3
where " t --> t' " := (red t t').

Hint Constructors red.

(* typing relation *)
Reserved Notation " Gamma ||- t : T " (at level 60, t at level 70).
Inductive hasType {n} : ctxt n -> tm n -> ty -> Prop :=
| T_var: forall Gamma i,
    Gamma ||- (var_tm i) : (Gamma i)
| T_app : forall Gamma t1 t2 T1 T2,
    Gamma ||- t1 : (arrow T1 T2) ->
    Gamma ||- t2 : T1 ->
    Gamma ||- (app t1 t2) : T2
| T_abs : forall Gamma t T1 T2,
    @hasType (S n) (T1 .: Gamma) t T2 -> (* use stream cons defined by as2 to implement context bindings *)
    Gamma ||- (lam T1 t) : (arrow T1 T2)
| T_ttrue : forall Gamma, Gamma ||- ttrue : bool
| T_tfalse : forall Gamma, Gamma ||- ttrue : bool
| T_tif : forall Gamma t1 t2 t3 T, 
    Gamma ||- t1 : bool ->
    Gamma ||- t2 : T ->
    Gamma ||- t3 : T ->
    Gamma ||- (tif t1 t2 t3) : T
where " Gamma ||- t : T " := (hasType Gamma t T).

Hint Constructors hasType.

Ltac inv H := inversion H; subst; clear H.

Theorem canonical_forms_abs: forall n Gamma (t : tm n) T1 T2,
    Gamma ||- t : (arrow T1 T2) ->
    value t ->
    exists t', t = lam T1 t'.
  intros n Gamma t T1 T2 HTy Hval.
  induction Hval; inv HTy; exists t; reflexivity.
Qed.

Theorem canonical_forms_bool: forall n Gamma (t : tm n),
    Gamma ||- t : bool ->
    value t ->
    (t = ttrue) \/ (t = tfalse).
  intros n Gamma t HTy Hval.
  induction Hval; inv HTy; auto.
Qed.

(* catch-all automation tactic; not great, but works *)
Ltac crunch :=
  try match goal with
         | [t : tm _ |- _] => match goal with
                            | [ HTy : _ ||- t : (arrow _ _) , Hval : value t |- _] => pose proof (canonical_forms_abs _ _ _ _ _ HTy Hval)
                            end

         | [t : tm _ |- _] => match goal with
                            | [ HTy : _ ||- t : bool , Hval : value t |- _] => pose proof (canonical_forms_bool _ _ _ HTy Hval)
                            end
         (* fin 0 is uninhabited; this immediately solves the goal. *)
         | [ f : fin 0 |- _ ] => destruct f; crunch
         (* deal with some nonsense that crops up during induction and inversion on our typing relation *) 
         | [ t1 : tm 0 |- _] => match goal with                            
                          | [ HTy : empty ||- t1 : _ , H : forall t0 : tm 0,
                                  0 = 0 -> t1 ~= t0 -> forall T : ty, empty ||- t0 : T -> value t0 \/ (exists t' : tm 0, t0 --> t') |- _] => specialize (H _ eq_refl JMeq_refl _ HTy); crunch
                              end
         end.

Lemma progess: forall t T,
    empty ||- t : T ->
    value t \/ exists t', t --> t'.
Proof.
  intros t T HTy.
  dependent induction t; try inv HTy; eauto; crunch.
  - (* t is an application *)
    right.
    destruct IHt1 as [Hvalt1 | Hstept1].
    + (* t1 is a value *)
      destruct IHt2 as [Hvalt2 | Hstept2].
      * (* t2 is also value *)
        crunch.
        destruct H as [t0 Heq]. (* AUTOMATEME *)
        exists (t0 [t2 ..]).
        subst.
        eauto.
      * (* t2 steps *)
        inv Hstept2; exists (app t1 x); eauto.
    + (* t1 steps *)
      inv Hstept1; exists (app x t2); eauto.
  - (* t is an if *)
    right.
    destruct IHt1 as [Hvalt1 | Hstept1].
    + (* discriminant of if is a value *)
      crunch.
      destruct H; subst. (* AUTOMATEME *)
      * (* branch left *)
        exists t2; auto.
      * (* branch right *)
        exists t3; auto.
    + destruct Hstept1 as [t1' Hred].
      exists (tif t1' t2 t3); eauto.
Qed.
  
  Fixpoint typres_ren n m Gamma Delta t T (H : Gamma ||- t : T) (delta : fin n -> fin m) {struct H}:
    (forall f, Gamma f = Delta (delta f)) -> (Delta ||- t⟨delta⟩ : T).
    destruct H; simpl; intros; asimpl; try rewrite (H i); eauto; econstructor; try eapply typres_ren; try assumption; try eauto; try intro; try destruct f; try simpl; try eauto.
  Qed.

  (* CLEAN ME *)
  Fixpoint typres_subst n m (sigma : fin n -> tm m) (Gamma : ctxt n) (Delta : ctxt m) (t : tm n) T (H: Gamma ||- t : T) {struct H} : 
(forall i, Delta ||- (sigma i) : (Gamma i)) -> Delta ||- t[sigma] : T.
  Proof with eauto.
    intros.
    (* everything but the lambda case is immediate by substitution and the definitions *)
    destruct H; asimpl...
    (* lambda case follows by structural induction on terms, our
    substitution rules, and by preservation of types under
    renamings. *)
    econstructor.
    eapply typres_subst.
    exact H.
    intro.
    asimpl.
    destruct i.
    simpl.
    asimpl.
    eapply typres_ren...
    simpl.
    econstructor.
  Qed.

  Theorem typres_beta : forall n (Gamma : ctxt n) t t' T' T,
      (T' .: Gamma) ||- t : T ->
      Gamma ||- t' : T' ->
      Gamma ||- (t [t' ..]) : T.
  Proof.
    intros.
    eapply typres_subst.
    exact H.
    intro.
    destruct i; asimpl; simpl; eauto.
  Qed.

  (* preservation *)
  Theorem preservation t t' T (H: empty ||- t : T) (Hred: t --> t') : 
    empty ||- t' : T.
    induction H.
    - inversion Hred.
    - inversion Hred; subst.
      +
        inversion H; subst.
        apply (typres_beta _ _ _ _ T1 T2 H3 H0).
      +
        eapply T_app.
        eapply IHhasType1.
        assumption.
        assumption.
      +
        eapply T_app.
        apply H.
        eapply IHhasType2.
        assumption.
    - inversion Hred.
    -
      inversion Hred.
    -
      inversion Hred.
    -
      inversion Hred; subst;
        try econstructor;
        try eapply IHhasType1;
        auto.
  Qed.