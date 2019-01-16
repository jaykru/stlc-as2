Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality. (* for dependent induction *)
Require Import as2.
(* contexts *)
Definition ctxt n := fin n -> ty. (* this definition of a context probably lets us more readily use autosubst's notation and substitution machinery *)

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

Inductive red {n} : tm n -> tm n -> Prop :=
| red_beta : forall (t : tm (S n)) (t' : tm n) (T: ty),
    red (app (lam T t) t') (t [t' ..])
| red_app_1 : forall t1 t1' t2,
    red t1 t1' ->
    red (app t1 t2) (app t1' t2)
| red_app_2 : forall t1 t2 t2',
    red t2 t2' ->
    red (app t1 t2) (app t1 t2')
| red_tif_disc : forall t1 t1' t2 t3,
    red t1 t1' ->
    red (tif t1 t2 t3) (tif t1' t2 t3)
| red_tif_true : forall t2 t3,
    red (tif ttrue t2 t3) t2
| red_tif_false : forall t2 t3,
    red (tif tfalse t2 t3) t3.

Hint Constructors red.

(* typing relation *)
Inductive hasType {n} : ctxt n -> tm n -> ty -> Prop :=
| T_var: forall G i,
    hasType G (var_tm i) (G i)
| T_app : forall G t1 t2 T1 T2,
    hasType G t1 (arrow T1 T2) ->
    hasType G t2 T1 ->
    hasType G (app t1 t2) T2
| T_abs : forall G t T1 T2,
    @hasType (S n) (T1 .: G) t T2 (* use stream cons defined by as2 to implement context bindings *)
    -> hasType G (lam T1 t) (arrow T1 T2) 
| T_ttrue : forall G, hasType G ttrue bool
| T_tfalse : forall G, hasType G ttrue bool
| T_tif : forall G t1 t2 t3 T, 
    hasType G t1 bool ->
    hasType G t2 T ->
    hasType G t3 T ->
    hasType G (tif t1 t2 t3) T.

Hint Constructors hasType.

(* catch-all automation tactic *)
Ltac crunch :=
  repeat match goal with
         (* fin 0 is uninhabited; this immediately solves the goal. *)
         | [ f : fin 0 |- _ ] => destruct f
         (* deal with some nonsense that crops up during induction and inversion on our typing relation *) 
         | [ t1 : tm 0 |- _] => match goal with                            
                          | [ HTy : hasType empty t1 _ , H : forall t0 : tm 0,
                                  0 = 0 -> t1 ~= t0 -> forall T : ty, hasType empty t0 T -> value t0 \/ (exists t' : tm 0, red t0 t') |- _] => specialize (H _ eq_refl JMeq_refl _ HTy)
                           end
         end.

Ltac inv H := inversion H; crunch; subst; clear H.

Theorem canonical_forms_abs: forall n G (t : tm n) T1 T2,
    hasType G t (arrow T1 T2) ->
    value t ->
    exists t', t = lam T1 t'.
  intros n G t T1 T2 HTy Hval.
  induction Hval; inv HTy; exists t; reflexivity.
Qed.

Theorem canonical_forms_bool: forall n G (t : tm n),
    hasType G t bool ->
    value t ->
    (t = ttrue) \/ (t = tfalse).
  intros n G t HTy Hval.
  induction Hval; inv HTy; auto.
Qed.

Lemma progress: forall t T,
      hasType empty t T ->
      value t \/ exists t', red t t'.
  Proof.
    intros t T HTy.
    dependent induction t; eauto; crunch.
    -
      (* t is an application *)
      right.
      inv HTy.
      destruct IHt1 as [HValt1 | Hredt1].
      + (* t1 is a value *)
        destruct IHt2 as [HValt2 | Hredt2].
        * (* t2 also value *)
          assert (exists t0, t1 = lam T1 t0).
          eapply canonical_forms_abs; eauto.
          destruct H as [t0 Heq].
          exists (t0 [t2 ..]).
          subst.
          eauto. 
        * (* t2 steps *)
          inversion Hredt2.
          exists (app t1 x).
          eauto. 
      +  (* t1 steps *)
        inversion Hredt1.
        exists (app x t2); eauto.
    -
      inv HTy.
      right.
      destruct IHt1 as [HVal | HStep].
      + (* discriminant of branch is a value *)
        assert (Ht1: t1 = ttrue \/ t1 = tfalse) by (eapply canonical_forms_bool; eauto).
        destruct Ht1; subst.
        * (* branch left *) exists t2; eauto.
        * (* branch right *) exists t3; eauto.
      + destruct HStep as [t1' Hredt1].
        exists (tif t1' t2 t3); eauto.        
  Qed.
  
  Fixpoint typres_ren n m G D t T (H : hasType G t T) (delta : fin n -> fin m) {struct H}:
    (forall f, G f = D (delta f)) -> (hasType D t⟨delta⟩ T).
    destruct H; simpl; intros; asimpl; try rewrite (H i); econstructor; eauto; try eapply typres_ren; try assumption.
    - exact H.
    - intro.
      destruct f.
      simpl.
      exact (H0 f).
      simpl.
      auto.
  Qed.

  (* CLEAN ME *)
  Fixpoint typres_subst n m (sigma : fin n -> tm m) (Gamma : ctxt n) (Delta : ctxt m) (t : tm n) T (H: hasType Gamma t T) {struct H} : 
(forall i, hasType Delta (sigma i) (Gamma i)) -> hasType Delta t[sigma] T.
  Proof with eauto.
    intros.
    destruct H; asimpl...
    (* lambda case *)
    econstructor.
    eapply typres_subst.
    exact H.
    intro.
    asimpl.
    destruct i.
    simpl.
    asimpl.
    eapply typres_ren; eauto.
    simpl.
    econstructor.
  Qed.

  Theorem typres_beta : forall n (G : ctxt n) t t' T' T,
      hasType (T' .: G) t T ->
      hasType G t' T' ->
      hasType G (t [t' ..]) T.
  Proof.
    intros.
    eapply typres_subst.
    exact H.
    intro.
    destruct i; eauto.
    asimpl; simpl; eauto.
  Qed.

  (* preservation *)
  Theorem preservation t t' T (H: hasType empty t T) (Hred: red t t') : 
    hasType empty t' T.
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