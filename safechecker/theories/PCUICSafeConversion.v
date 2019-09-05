(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.RelationClasses Omega.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.Checker Require Import uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICSR PCUICEquality PCUICNameless PCUICConversion
     PCUICSafeLemmata PCUICNormal PCUICInversion PCUICReduction PCUICPosition
     PCUICContextConversion PCUICConfluence PCUICSN.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Local Set Keyed Unification.

Import MonadNotation.

Module PSR := PCUICSafeReduce.

(** * Conversion for PCUIC without fuel

  Following PCUICSafereduce, we derive a fuel-free implementation of
  conversion (and cumulativity) checking for PCUIC.

 *)


Definition global_uctx (Σ : global_env) : ContextSet.t
  := (global_levels Σ, global_constraints Σ).

Definition global_ext_uctx (Σ : global_env_ext) : ContextSet.t
  := (global_ext_levels Σ, global_ext_constraints Σ).

Definition wf_global_uctx_invariants {cf:checker_flags} Σ
  : ∥ wf Σ ∥ -> global_uctx_invariants (global_uctx Σ).
Proof.
  intros [HΣ]. split.
  - cbn. unfold global_levels.
    cut (LevelSet.In lSet (LevelSet_pair Level.lSet Level.lProp)).
    + generalize (LevelSet_pair Level.lSet Level.lProp).
      clear HΣ. induction Σ; simpl. easy.
      intros X H. apply LevelSet.union_spec. now right.
    + apply LevelSet.add_spec. right. now apply LevelSet.singleton_spec.
  - unfold global_uctx.
    simpl. intros [[l ct] l'] Hctr. simpl in *.
    induction Σ in HΣ, l, ct, l', Hctr |- *.
    * apply ConstraintSetFact.empty_iff in Hctr; contradiction.
    * simpl in *. apply ConstraintSet.union_spec in Hctr;
                    destruct Hctr as [Hctr|Hctr].
      -- split.
         inversion HΣ; subst.
         destruct H2 as [HH1 [HH HH3]].
         subst udecl. destruct a as [kn decl|kn decl]; simpl in *.
         destruct decl; simpl in *.
         destruct cst_universes;
           [eapply (HH (l, ct, l') Hctr)|
            apply ConstraintSetFact.empty_iff in Hctr; contradiction|
            apply ConstraintSetFact.empty_iff in Hctr; contradiction].
         destruct decl; simpl in *.
         destruct ind_universes;
           [eapply (HH (l, ct, l') Hctr)|
            apply ConstraintSetFact.empty_iff in Hctr; contradiction|
            apply ConstraintSetFact.empty_iff in Hctr; contradiction].
         inversion HΣ; subst.
         destruct H2 as [HH1 [HH HH3]].
         subst udecl. destruct a as [kn decl|kn decl]; simpl in *.
         destruct decl; simpl in *.
         destruct cst_universes;
           [eapply (HH (l, ct, l') Hctr)|
            apply ConstraintSetFact.empty_iff in Hctr; contradiction|
            apply ConstraintSetFact.empty_iff in Hctr; contradiction].
         destruct decl; simpl in *.
         destruct ind_universes;
           [eapply (HH (l, ct, l') Hctr)|
            apply ConstraintSetFact.empty_iff in Hctr; contradiction|
            apply ConstraintSetFact.empty_iff in Hctr; contradiction].
      -- inversion HΣ; subst.
         split; apply LevelSet.union_spec; right;
           unshelve eapply (IHΣ _ _ _ _ Hctr); tea.
Qed.

Definition wf_ext_global_uctx_invariants {cf:checker_flags} Σ
  : ∥ wf_ext Σ ∥ -> global_uctx_invariants (global_ext_uctx Σ).
Proof.
  intros [HΣ]. split.
  - apply LevelSet.union_spec. right. unfold global_levels.
    cut (LevelSet.In lSet (LevelSet_pair Level.lSet Level.lProp)).
    + generalize (LevelSet_pair Level.lSet Level.lProp).
      induction Σ.1; simpl. easy.
      intros X H. apply LevelSet.union_spec. now right.
    + apply LevelSet.add_spec. right. now apply LevelSet.singleton_spec.
  - destruct Σ as [Σ φ]. destruct HΣ as [HΣ Hφ].
    destruct (wf_global_uctx_invariants _ (sq HΣ)) as [_ XX].
    unfold global_ext_uctx, global_ext_levels, global_ext_constraints.
    simpl. intros [[l ct] l'] Hctr. simpl in *. apply ConstraintSet.union_spec in Hctr.
    destruct Hctr as [Hctr|Hctr].
    + destruct Hφ as [_ [HH _]]. apply (HH _ Hctr).
    + specialize (XX _ Hctr).
      split; apply LevelSet.union_spec; right; apply XX.
Qed.

Definition global_ext_uctx_consistent {cf:checker_flags} Σ
  : ∥ wf_ext Σ ∥ -> consistent (global_ext_uctx Σ).2.
  intros [HΣ]. cbn. unfold global_ext_constraints.
  unfold wf_ext, on_global_env_ext in HΣ.
  destruct HΣ as [_ [_ [_ HH]]]. apply HH.
Qed.


Section Conversion.

  Context {cf : checker_flags}.
  Context (flags : RedFlags.t).
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).
  Context (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition hΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct hΣ, Hφ; now constructor.
  Defined.


  Set Equations With UIP.

  Inductive state :=
  | Reduction (t : term)
  | Term (t : term)
  | Args
  | Fallback (t : term).

  Inductive stateR : state -> state -> Prop :=
  | stateR_Term_Reduction : forall u v, stateR (Term u) (Reduction v)
  | stateR_Arg_Term : forall u, stateR Args (Term u)
  | stateR_Fallback_Term : forall u v, stateR (Fallback u) (Term v).

  Derive Signature for stateR.

  Lemma stateR_Acc :
    forall s, Acc stateR s.
  Proof.
    assert (Acc stateR Args) as hArgs.
    { constructor. intros s h.
      dependent induction h.
      all: discriminate.
    }
    assert (forall t, Acc stateR (Fallback t)) as hFall.
    { intros t. constructor. intros s h.
      dependent induction h.
      all: discriminate.
    }
    assert (forall t, Acc stateR (Term t)) as hTerm.
    { intros t. constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      - apply hArgs.
      - apply hFall.
    }
    assert (forall t, Acc stateR (Reduction t)) as hRed.
    { intros t. constructor. intros s h.
      dependent induction h.
      all: try discriminate.
      apply hTerm.
    }
    intro s. destruct s ; eauto.
  Qed.

  Notation wtp Γ t π :=
    (wellformed Σ [] (zipx Γ t π)) (only parsing).

  Definition wts Γ s t π :=
    match s with
    | Reduction t'
    | Fallback t'
    | Term t' => wtp Γ t' π
    | Args => wtp Γ t π
    end.

  Set Primitive Projections.

  Record pack := mkpack {
    st : state ;
    ctx : context ;
    tm : term ;
    stk1 : stack ;
    stk2 : stack ;
    tm' := match st with
           | Reduction t | Fallback t | Term t => t
           | Args => tm
           end ;
    wth : wellformed Σ [] (zipx ctx tm' stk2)
  }.

  Record nlpack := mknlpack {
    nl_st : state ;
    nl_ctx : context ;
    nl_tm : term ;
    nl_stk1 : stack ;
    nl_stk2 : stack ;
    nl_tm' := match nl_st with
           | Reduction t | Fallback t | Term t => t
           | Args => nl_tm
           end ;
    nl_wth : wellformed Σ [] (zipx nl_ctx nl_tm' nl_stk2)
  }.

  Definition nlstate (s : state) :=
    match s with
    | Reduction t => Reduction (nl t)
    | Term t => Term (nl t)
    | Args => Args
    | Fallback t => Fallback (nl t)
    end.

  Definition nl_pack (p : pack) : nlpack.
  Proof.
    destruct p as [s Γ t π1 π2 t' h].
    unshelve eexists.
    - exact (nlstate s).
    - exact (nlctx Γ).
    - exact (nl t).
    - exact (nlstack π2).
    - exact (nlstack π1).
    - eapply wellformed_rename ; try assumption.
      + exact h.
      + destruct s; cbn.
        all: rewrite <- nl_zipx; eapply eq_term_upto_univ_tm_nl; auto.
  Defined.

  Definition wterm Γ := { t : term | wellformed Σ Γ t }.

  Definition wcored Γ (u v : wterm Γ) :=
    cored Σ Γ (` u) (` v).

  Lemma wcored_wf :
    forall Γ, well_founded (wcored Γ).
  Proof.
    intros Γ [u hu].
    destruct hΣ as [hΣ'].
    pose proof (normalisation' _ _ _ hΣ' hu) as h.
    dependent induction h.
    constructor. intros [y hy] r.
    unfold wcored in r. cbn in r.
    eapply H0. assumption.
  Qed.

  Definition R_aux :=
    t ⊩ cored Σ [] ⨶ @posR t ⊗ w ⊩ wcored [] ⨶ @posR (` w) ⊗ stateR.

  Notation nl_pzt u := (zipx (nl_ctx u) (nl_tm u) (nl_stk1 u)) (only parsing).
  Notation nl_pps1 u := (xpos (nl_ctx u) (nl_tm u) (nl_stk1 u)) (only parsing).
  Notation nl_pwt u := (exist _ (nl_wth u)) (only parsing).
  Notation nl_pps2 u := (xpos (nl_ctx u) (nl_tm' u) (nl_stk2 u)) (only parsing).

  Notation obpack u :=
    (nl_pzt u ; (nl_pps1 u, (nl_pwt u ; (nl_pps2 u, nl_st u)))) (only parsing).

  Definition R_nl (u v : nlpack) :=
    R_aux (obpack u) (obpack v).

  Definition R (u v : pack) :=
    R_nl (nl_pack u) (nl_pack v).

  Notation pzt u := (zipx (ctx u) (tm u) (stk1 u)) (only parsing).
  Notation pps1 u := (xpos (ctx u) (tm u) (stk1 u)) (only parsing).
  Notation pwt u := (exist _ (wth u)) (only parsing).
  Notation pps2 u := (xpos (ctx u) (tm' u) (stk2 u)) (only parsing).

  Lemma R_aux_Acc :
    forall t p w q s,
      wellformed Σ [] t ->
      Acc R_aux (t ; (p, (w ; (q, s)))).
  Proof.
    intros t p w q s ht.
    eapply dlexprod_Acc.
    - intro u. eapply Subterm.wf_lexprod.
      + intro. eapply posR_Acc.
      + intros [w' q']. eapply dlexprod_Acc.
        * intros [t' h']. eapply Subterm.wf_lexprod.
          -- intro. eapply posR_Acc.
          -- intro. eapply stateR_Acc.
        * eapply wcored_wf.
    - destruct hΣ as [hΣ'].
      eapply normalisation'; eassumption.
  Qed.

  Lemma R_Acc :
    forall u,
      wellformed Σ [] (zipx (ctx u) (tm u) (stk1 u)) ->
      Acc R u.
  Proof.
    intros u h.
    eapply Acc_fun with (f := fun x => obpack (nl_pack x)).
    apply R_aux_Acc.
    rewrite <- nl_zipx.
    eapply wellformed_rename ; try eassumption.
    eapply eq_term_upto_univ_tm_nl. all: auto.
  Qed.

  Lemma R_cored :
    forall p1 p2,
      cored Σ [] (pzt p1) (pzt p2) ->
      R p1 p2.
  Proof.
    intros p1 p2 h.
    left. rewrite <- 2!nl_zipx.
    change [] with (nlctx []).
    eapply cored_nl ; auto.
  Qed.

  Lemma R_aux_positionR :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2,
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux (t1 ; (p1, s1)) (t2 ; (p2, s2)).
  Proof.
    intros t1 t2 p1 p2 s1 s2 e h.
    subst. right. left. assumption.
  Qed.

  Lemma R_positionR :
    forall p1 p2,
      nl (pzt p1) = nl (pzt p2) ->
      positionR (` (pps1 p1)) (` (pps1 p2)) ->
      R p1 p2.
  Proof.
    intros [s1 Γ1 t1 π1 ρ1 t1' h1] [s2 Γ2 t2 π2 ρ2 t2' h2] e h. simpl in *.
    eapply R_aux_positionR ; simpl.
    - rewrite <- 2!nl_zipx. assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack.
      assumption.
  Qed.

  Lemma R_aux_cored2 :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      t1 = t2 ->
      ` p1 = ` p2 ->
      cored Σ [] (` w1) (` w2) ->
      R_aux (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 h.
    cbn in e2. cbn in h. subst.
    pose proof (uip hp1 hp2). subst.
    right. right. left. assumption.
  Qed.

  Lemma R_cored2 :
    forall p1 p2,
      nl (pzt p1) = nl (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      cored Σ [] (` (pwt p1)) (` (pwt p2)) ->
      R p1 p2.
  Proof.
    intros [s1 Γ1 t1 π1 ρ1 t1' h1] [s2 Γ2 t2 π2 ρ2 t2' h2] e1 e2 h. simpl in *.
    eapply R_aux_cored2 ; simpl.
    - rewrite <- 2!nl_zipx. assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
    - destruct s1, s2 ; simpl.
      all: rewrite <- 2!nl_zipx.
      all: change [] with (nlctx []).
      all: eapply cored_nl ; auto.
  Qed.

  Lemma R_aux_positionR2 :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      t1 = t2 ->
      ` p1 = ` p2 ->
      ` w1 = ` w2 ->
      positionR (` q1) (` q2) ->
      R_aux (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] q1 q2 s1 s2 e1 e2 e3 h.
    cbn in e2. cbn in e3. subst.
    pose proof (uip hp1 hp2). subst.
    pose proof (wellformed_irr h1' h2'). subst.
    right. right. right. left. assumption.
  Qed.

  Lemma R_positionR2 :
    forall p1 p2,
      nl (pzt p1) = nl (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      nl (` (pwt p1)) = nl (` (pwt p2)) ->
      positionR (` (pps2 p1)) (` (pps2 p2)) ->
      R p1 p2.
  Proof.
    intros [s1 Γ1 t1 π1 ρ1 t1' h1] [s2 Γ2 t2 π2 ρ2 t2' h2] e1 e2 e3 h.
    simpl in *.
    eapply R_aux_positionR2 ; simpl.
    - rewrite <- 2!nl_zipx. assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
    - destruct s1, s2 ; simpl.
      all: rewrite <- 2!nl_zipx. all: assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
  Qed.

  Lemma R_aux_stateR :
    forall t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2 ,
      t1 = t2 ->
      ` p1 = ` p2 ->
      ` w1 = ` w2 ->
      ` q1 = ` q2 ->
      stateR s1 s2 ->
      R_aux (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
  Proof.
    intros t1 t2 [p1 hp1] [p2 hp2] [t1' h1'] [t2' h2'] [q1 hq1] [q2 hq2] s1 s2
           e1 e2 e3 e4 h.
    cbn in e2. cbn in e3. cbn in e4. subst.
    pose proof (uip hp1 hp2). subst.
    pose proof (wellformed_irr h1' h2'). subst.
    pose proof (uip hq1 hq2). subst.
    right. right. right. right. assumption.
  Qed.

  Lemma R_stateR :
    forall p1 p2,
      nl (pzt p1) = nl (pzt p2) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      nl (` (pwt p1)) = nl (` (pwt p2)) ->
      ` (pps2 p1) = ` (pps2 p2) ->
      stateR (st p1) (st p2) ->
      R p1 p2.
  Proof.
    intros [s1 Γ1 t1 π1 ρ1 t1' h1] [s2 Γ2 t2 π2 ρ2 t2' h2] e1 e2 e3 e4 h.
    simpl in *.
    eapply R_aux_stateR ; simpl.
    - rewrite <- 2!nl_zipx. assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
    - destruct s1, s2 ; simpl.
      all: rewrite <- 2!nl_zipx. all: assumption.
    - rewrite 2!xposition_nlctx, 2!xposition_nlstack. assumption.
    - induction h ; constructor.
  Qed.

  Lemma zwts :
    forall {Γ s t π},
      wts Γ s t π ->
      wellformed Σ [] (zipx Γ match s with Reduction u | Fallback u | Term u => u | Args => t end π).
  Proof.
    intros Γ s t π h.
    destruct s ; assumption.
  Defined.

  (* Definition Ret s Γ t π π' := *)
  (*   match s with *)
  (*   | Reduction t' => *)
  (*     forall leq, { b : bool | if b then conv leq Σ Γ (zippx t π) (zippx t' π') else True } *)
  (*   | Fallback t' *)
  (*   | Term t' => *)
  (*     forall leq, *)
  (*       isred (t, π) -> *)
  (*       isred (t', π') -> *)
  (*       { b : bool | if b then conv leq Σ Γ (zippx t π) (zippx t' π') else True } *)
  (*   | Args => *)
  (*     { b : bool | if b then ∥ Σ ;;; Γ |- zippx t π == zippx t π' ∥ else True } *)
  (*   end. *)

  Definition Ret s Γ t π π' :=
    forall (leq : match s with Args => unit | _ => conv_pb end),
      (match s with Fallback t' | Term t' => isred (t, π) | _ => True end) ->
      (match s with Fallback t' | Term t' => isred (t', π') | _ => True end) ->
      { b : bool | match s
                return forall (leq : match s with Args => unit | _ => conv_pb end), Prop
                with
                | Reduction t' => fun leq =>
                  if b then conv leq Σ Γ (zippx t π) (zippx t' π') else True
                | Fallback t'
                | Term t' => fun leq =>
                  if b then conv leq Σ Γ (zippx t π) (zippx t' π') else True
                | Args => fun _ =>
                  if b then ∥ Σ ;;; Γ |- zippx t π == zippx t π' ∥ else True
                end leq
      }.

  Definition Aux s Γ t π1 π2 h2 :=
     forall s' Γ' t' π1' π2'
       (h1' : wtp Γ' t' π1')
       (h2' : wts Γ' s' t' π2'),
       R (mkpack s' Γ' t' π1' π2' (zwts h2'))
         (mkpack s Γ t π1 π2 (zwts h2)) ->
       Ret s' Γ' t' π1' π2'.

  Notation no := (exist false I) (only parsing).
  Notation yes := (exist true _) (only parsing).

  Notation repack e := (let '(exist b h) := e in exist b _) (only parsing).

  Notation isconv_red_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Reduction t2) Γ t1 π1 π2 _ _ _ leq I I) (only parsing).
  Notation isconv_prog_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Term t2) Γ t1 π1 π2 _ _ _ leq _ _) (only parsing).
  Notation isconv_args_raw Γ t π1 π2 aux :=
    (aux Args Γ t π1 π2 _ _ _ tt I I) (only parsing).
  Notation isconv_fallback_raw Γ leq t1 π1 t2 π2 aux :=
    (aux (Fallback t2) Γ t1 π1 π2 _ _ _ leq _ _) (only parsing).

  Notation isconv_red Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args Γ t π1 π2 aux :=
    (repack (isconv_args_raw Γ t π1 π2 aux)) (only parsing).
  Notation isconv_fallback Γ leq t1 π1 t2 π2 aux :=
    (repack (isconv_fallback_raw Γ leq t1 π1 t2 π2 aux)) (only parsing).

  Ltac tas := try assumption.

  Equations(noeqns) _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (aux : Aux (Reduction t2) Γ t1 π1 π2 h2)
    : { b : bool | if b then conv leq Σ Γ (zippx t1 π1) (zippx t2 π2) else True } :=

    _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux
    with inspect (decompose_stack π1) := {
    | @exist (args1, ρ1) e1 with inspect (decompose_stack π2) := {
      | @exist (args2, ρ2) e2
        with inspect (reduce_stack nodelta_flags Σ hΣ (Γ ,,, stack_context π1) t1 (appstack args1 ε) _) := {
        | @exist (t1',π1') eq1
          with inspect (reduce_stack nodelta_flags Σ hΣ (Γ ,,, stack_context π2) t2 (appstack args2 ε) _) := {
          | @exist (t2',π2') eq2 => isconv_prog Γ leq t1' (π1' +++ ρ1) t2' (π2' +++ ρ2) aux
          }
        }
      }
    }.
  Next Obligation.
    apply wellformed_zipx in h1 ; tas.
    apply wellformed_zipc_zippx in h1 ; tas.
    cbn. rewrite zipc_appstack. cbn.
    unfold zippx in h1. rewrite <- e1 in h1.
    apply wellformed_it_mkLambda_or_LetIn in h1 ; tas.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    rewrite stack_context_appstack. assumption.
  Qed.
  Next Obligation.
    clear aux eq1.
    apply wellformed_zipx in h2; tas.
    apply wellformed_zipc_zippx in h2 ; tas.
    cbn. rewrite zipc_appstack. cbn.
    unfold zippx in h2. rewrite <- e2 in h2.
    apply wellformed_it_mkLambda_or_LetIn in h2; tas.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
    rewrite stack_context_appstack. assumption.
  Qed.
  Next Obligation.
    pose proof hΣ as hΣ'.
    destruct hΣ' as [wΣ].
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c1
    end.
    rewrite <- eq1 in r1.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    clear eq1 eq2.
    apply wellformed_zipx in h1; tas.
    rewrite zipc_appstack in h1.
    case_eq (decompose_stack π1'). intros args1' ρ1' e1'.
    rewrite e1' in d1. cbn in d1.
    rewrite decompose_stack_appstack in d1. cbn in d1. subst.
    pose proof (decompose_stack_eq _ _ _ e1'). subst.
    rewrite stack_cat_appstack.
    eapply zipx_wellformed ; try assumption.
    rewrite zipc_appstack.

    rewrite stack_context_appstack in r1. cbn in r1.
    rewrite 2!zipc_appstack in r1. cbn in r1.

    eapply red_wellformed ; try assumption ; revgoals.
    - constructor. zip fold. eapply PCUICPosition.red_context. eassumption.
    - cbn. assumption.
  Qed.
  Next Obligation.
    pose proof hΣ as hΣ'.
    destruct hΣ' as [wΣ].
    match type of eq2 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c2
    end.
    rewrite <- eq2 in r2.
    rewrite <- eq2 in d2. cbn in d2.
    rewrite <- eq2 in c2. cbn in c2.
    rewrite stack_context_appstack in c2. cbn in c2.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
    clear eq1 eq2 aux.
    apply wellformed_zipx in h2; tas.
    rewrite zipc_appstack in h2.
    case_eq (decompose_stack π2'). intros args2' ρ2' e2'.
    rewrite e2' in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2. subst.
    pose proof (decompose_stack_eq _ _ _ e2'). subst.
    rewrite stack_cat_appstack.
    eapply zipx_wellformed ; try assumption.
    rewrite zipc_appstack.

    rewrite stack_context_appstack in r2. cbn in r2.
    rewrite 2!zipc_appstack in r2. cbn in r2.

    eapply red_wellformed ; try assumption ; revgoals.
    - constructor. zip fold. eapply PCUICPosition.red_context. eassumption.
    - cbn. assumption.
  Qed.
  Next Obligation.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c1
    end.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.
    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?hh =>
      pose proof (reduce_stack_Req f _ hΣ _ _ _ hh) as [ e | h ]
    end.
    - assert (ee1 := eq1). rewrite e in ee1. inversion ee1. subst.
      match type of eq2 with
      | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2 ;
        pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c2
      end.
      rewrite <- eq2 in d2. cbn in d2.
      rewrite <- eq2 in c2. cbn in c2.
      rewrite stack_context_appstack in c2. cbn in c2.
      pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
      match type of eq2 with
      | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?hh =>
        pose proof (reduce_stack_Req f _ hΣ _ _ _ hh) as [ ee | h ]
      end.
      + assert (ee2 := eq2). rewrite ee in ee2. inversion ee2. subst.
        unshelve eapply R_stateR.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. rewrite stack_cat_appstack. reflexivity.
        * simpl. constructor.
      + rewrite <- eq2 in h.
        rewrite stack_context_appstack in h.
        dependent destruction h.
        * cbn in H. rewrite zipc_appstack in H. cbn in H.
          unshelve eapply R_cored2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl.
             eapply cored_it_mkLambda_or_LetIn.
             rewrite app_context_nil_l.
             rewrite zipc_appstack. rewrite zipc_stack_cat.
             repeat zip fold. eapply cored_context.
             assumption.
        * destruct y' as [q hq].
          cbn in H0. inversion H0. subst.
          unshelve eapply R_positionR2.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. rewrite stack_cat_appstack. reflexivity.
          -- simpl. unfold zipx. f_equal. f_equal.
             rewrite zipc_stack_cat.
             rewrite <- H2.
             rewrite 2!zipc_appstack. cbn. reflexivity.
          -- simpl. unfold xposition. eapply positionR_poscat.
             unfold posR in H. cbn in H.
             rewrite stack_position_appstack in H. cbn in H.
             rewrite stack_position_stack_cat.
             rewrite stack_position_appstack.
             eapply positionR_poscat.
             assumption.
    - rewrite <- eq1 in h.
      rewrite stack_context_appstack in h.
      dependent destruction h.
      + cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply R_cored. simpl. eapply cored_it_mkLambda_or_LetIn.
        rewrite app_context_nil_l.
        rewrite zipc_appstack. rewrite zipc_stack_cat.
        repeat zip fold. eapply cored_context.
        assumption.
      + destruct y' as [q hq].
        cbn in H0. inversion H0. (* Why is noconf failing at this point? *)
        subst.
        unshelve eapply R_positionR ; simpl.
        * unfold zipx. f_equal. f_equal.
          rewrite zipc_stack_cat.
          rewrite <- H2.
          rewrite 2!zipc_appstack. cbn. reflexivity.
        * unfold xposition. eapply positionR_poscat.
          unfold posR in H. cbn in H.
          rewrite stack_position_appstack in H. cbn in H.
          rewrite stack_position_stack_cat.
          rewrite stack_position_appstack.
          eapply positionR_poscat.
          assumption.
  Qed.
  Next Obligation.
    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_isred f Σ hΣ Γ t π h eq_refl) as r1
    end.
    rewrite <- eq1 in r1. destruct r1 as [ha hl].
    split.
    - assumption.
    - cbn in hl. cbn. intro h.
      specialize (hl h).
      destruct π1'.
      all: try reflexivity.
      + cbn. destruct ρ1.
        all: try reflexivity.
        exfalso.
        apply (decompose_stack_not_app _ _ _ _ (eq_sym e1)).
      + discriminate hl.
  Qed.
  Next Obligation.
    match type of eq2 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_isred f Σ hΣ Γ t π h eq_refl) as r2
    end.
    rewrite <- eq2 in r2. destruct r2 as [ha hl].
    split.
    - assumption.
    - cbn in hl. cbn. intro h.
      specialize (hl h).
      destruct π2'.
      all: try reflexivity.
      + cbn. destruct ρ2.
        all: try reflexivity.
        exfalso.
        apply (decompose_stack_not_app _ _ _ _ (eq_sym e2)).
      + discriminate hl.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    unfold zippx. rewrite <- e1. rewrite <- e2.

    match type of eq1 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d1 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c1
    end.
    rewrite <- eq1 in r1.
    rewrite <- eq1 in d1. cbn in d1.
    rewrite <- eq1 in c1. cbn in c1.
    rewrite stack_context_appstack in c1. cbn in c1.

    match type of eq2 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c2
    end.
    rewrite <- eq2 in r2.
    rewrite <- eq2 in d2. cbn in d2.
    rewrite <- eq2 in c2. cbn in c2.
    rewrite stack_context_appstack in c2. cbn in c2.

    clear eq1 eq2.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e1)). subst.
    case_eq (decompose_stack π1'). intros args1' ρ1' e1'.
    rewrite e1' in d1. cbn in d1.
    rewrite decompose_stack_appstack in d1. cbn in d1. subst.
    pose proof (decompose_stack_eq _ _ _ e1'). subst.

    pose proof (decompose_stack_eq _ _ _ (eq_sym e2)). subst.
    case_eq (decompose_stack π2'). intros args2' ρ2' e2'.
    rewrite e2' in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2. subst.
    pose proof (decompose_stack_eq _ _ _ e2'). subst.

    rewrite stack_context_appstack in r1. cbn in r1.
    rewrite 2!zipc_appstack in r1. cbn in r1.

    rewrite stack_context_appstack in r2. cbn in r2.
    rewrite 2!zipc_appstack in r2. cbn in r2.

    rewrite 2!stack_cat_appstack in h.
    unfold zippx in h.
    rewrite 2!decompose_stack_appstack in h.
    rewrite decompose_stack_twice with (1 := eq_sym e1) in h.
    rewrite decompose_stack_twice with (1 := eq_sym e2) in h.
    simpl in h.
    rewrite 2!app_nil_r in h.

    eapply conv_trans'.
    - assumption.
    - eapply red_conv_l ; try assumption.
      eapply red_it_mkLambda_or_LetIn.
      eassumption.
    - eapply conv_trans'.
      + assumption.
      + eassumption.
      + eapply red_conv_r ; auto.
        eapply red_it_mkLambda_or_LetIn.
        assumption.
  Qed.

  Equations unfold_one_fix (Γ : context) (mfix : mfixpoint term)
            (idx : nat) (π : stack) (h : wtp Γ (tFix mfix idx) π)
    : option (term * stack) :=

    unfold_one_fix Γ mfix idx π h with inspect (unfold_fix mfix idx) := {
    | @exist (Some (arg, fn)) eq1 with inspect (decompose_stack_at π arg) := {
      | @exist (Some (l, c, θ)) eq2 with inspect (reduce_stack RedFlags.default Σ hΣ (Γ ,,, stack_context θ) c ε _) := {
        | @exist (cred, ρ) eq3 with construct_viewc cred := {
          | view_construct ind n ui := Some (fn, appstack l (App (zipc (tConstruct ind n ui) ρ) θ)) ;
          | view_other t h := None
          }
        } ;
      | _ := None
      } ;
    | _ := None
    }.
  Next Obligation.
    destruct hΣ.
    cbn. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    apply wellformed_zipx in h. all: tas. rewrite zipc_appstack in h. cbn in h.
    zip fold in h. apply wellformed_context in h ; auto. simpl in h.
    destruct h as [[T h]|[[ctx [s [h1 _]]]]]; [|discriminate].
    apply inversion_App in h as hh ; auto.
    destruct hh as [na [A' [B' [? [? ?]]]]].
    left. eexists. eassumption.
  Qed.

  Derive NoConfusion NoConfusionHom for option.

  Lemma unfold_one_fix_red_zippx :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      ∥ red (fst Σ) Γ (zippx (tFix mfix idx) π) (zippx fn ξ) ∥.
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    unfold zippx.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. simpl.
    case_eq (decompose_stack s). intros l' s' e'.
    simpl.
    match type of e1 with
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    constructor. eapply red_it_mkLambda_or_LetIn.
    rewrite <- 2!mkApps_nested. cbn. eapply red_mkApps_f.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite stack_context_appstack in r1.
    econstructor.
    - eapply app_reds_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite <- mkApps_nested ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym e0) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by omega. cbn.
        case_eq (decompose_stack s0). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_red :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      ∥ red (fst Σ) Γ (zipc (tFix mfix idx) π) (zipc fn ξ) ∥.
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of e1 with
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    do 2 zip fold. constructor. eapply PCUICPosition.red_context.
    econstructor.
    - eapply app_reds_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite <- mkApps_nested ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym e0) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by omega. cbn.
        case_eq (decompose_stack s0). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_cored :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      cored (fst Σ) Γ (zipc fn ξ) (zipc (tFix mfix idx) π).
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite !zipc_appstack. cbn.
    match type of e1 with
    | _ = reduce_stack ?flags ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_sound flags Σ hΣ Γ t π h) as [r1] ;
      pose proof (reduce_stack_decompose flags Σ hΣ Γ t π h) as hd
    end.
    rewrite <- e1 in r1. cbn in r1.
    rewrite <- e1 in hd. cbn in hd.
    do 2 zip fold. eapply cored_context.
    eapply cored_red_trans.
    - eapply app_reds_r. exact r1.
    - repeat lazymatch goal with
      | |- context [ tApp (mkApps ?t ?l) ?u ] =>
        replace (tApp (mkApps t l) u) with (mkApps t (l ++ [u]))
          by (rewrite <- mkApps_nested ; reflexivity)
      end.
      eapply red_fix.
      + symmetry. eassumption.
      + unfold is_constructor.
        pose proof (eq_sym e0) as eql.
        apply decompose_stack_at_length in eql. subst.
        rewrite nth_error_app_ge by auto.
        replace (#|l| - #|l|) with 0 by omega. cbn.
        case_eq (decompose_stack s0). intros l0 s1 ee.
        rewrite ee in hd.
        pose proof (decompose_stack_eq _ _ _ ee). subst.
        cbn in hd. subst.
        rewrite zipc_appstack. cbn.
        unfold isConstruct_app. rewrite decompose_app_mkApps by auto.
        reflexivity.
  Qed.

  Lemma unfold_one_fix_decompose :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof.
    intros Γ mfix idx π h fn ξ eq.
    revert eq.
    funelim (unfold_one_fix Γ mfix idx π h).
    all: intro eq ; noconf eq.
    pose proof (eq_sym e0) as eq.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq). subst.
    rewrite 2!decompose_stack_appstack. cbn.
    case_eq (decompose_stack s). intros l0 s1 H2.
    reflexivity.
  Qed.

  (* Tailored view for isconv_prog *)
  Equations prog_discr (t1 t2 : term) : Prop :=
    prog_discr (tApp _ _) (tApp _ _) := False ;
    prog_discr (tConst _ _) (tConst _ _) := False ;
    prog_discr (tLambda _ _ _) (tLambda _ _ _) := False ;
    prog_discr (tProd _ _ _) (tProd _ _ _) := False ;
    prog_discr (tCase _ _ _ _) (tCase _ _ _ _) := False ;
    prog_discr (tProj _ _) (tProj _ _) := False ;
    prog_discr (tFix _ _) (tFix _ _) := False ;
    prog_discr (tCoFix _ _) (tCoFix _ _) := False ;
    prog_discr _ _ := True.

  Inductive prog_view : term -> term -> Set :=
  | prog_view_App u1 v1 u2 v2 :
      prog_view (tApp u1 v1) (tApp u2 v2)

  | prog_view_Const c1 u1 c2 u2 :
      prog_view (tConst c1 u1) (tConst c2 u2)

  | prog_view_Lambda na1 A1 b1 na2 A2 b2 :
      prog_view (tLambda na1 A1 b1) (tLambda na2 A2 b2)

  | prog_view_Prod na1 A1 B1 na2 A2 B2 :
      prog_view (tProd na1 A1 B1) (tProd na2 A2 B2)

  | prog_view_Case ind par p c brs ind' par' p' c' brs' :
      prog_view (tCase (ind, par) p c brs) (tCase (ind', par') p' c' brs')

  | prog_view_Proj p c p' c' :
      prog_view (tProj p c) (tProj p' c')

  | prog_view_Fix mfix idx mfix' idx' :
      prog_view (tFix mfix idx) (tFix mfix' idx')

  | prog_view_CoFix mfix idx mfix' idx' :
      prog_view (tCoFix mfix idx) (tCoFix mfix' idx')

  | prog_view_other :
      forall u v, prog_discr u v -> prog_view u v.

  Equations prog_viewc u v : prog_view u v :=
    prog_viewc (tApp u1 v1) (tApp u2 v2) :=
      prog_view_App u1 v1 u2 v2 ;

    prog_viewc (tConst c1 u1) (tConst c2 u2) :=
      prog_view_Const c1 u1 c2 u2 ;

    prog_viewc (tLambda na1 A1 b1) (tLambda na2 A2 b2) :=
      prog_view_Lambda na1 A1 b1 na2 A2 b2 ;

    prog_viewc (tProd na1 A1 B1) (tProd na2 A2 B2) :=
      prog_view_Prod na1 A1 B1 na2 A2 B2 ;

    prog_viewc (tCase (ind, par) p c brs) (tCase (ind', par') p' c' brs') :=
      prog_view_Case ind par p c brs ind' par' p' c' brs' ;

    prog_viewc (tProj p c) (tProj p' c') :=
      prog_view_Proj p c p' c' ;

    prog_viewc (tFix mfix idx) (tFix mfix' idx') :=
      prog_view_Fix mfix idx mfix' idx' ;

    prog_viewc (tCoFix mfix idx) (tCoFix mfix' idx') :=
      prog_view_CoFix mfix idx mfix' idx' ;

    prog_viewc u v := prog_view_other u v I.

  Lemma elimT (P : Type) (b : bool) : reflectT P b -> b -> P.
  Proof.
    intros []; auto. discriminate.
  Defined.

  Lemma introT (P : Type) (b : bool) : reflectT P b -> P -> b.
  Proof.
    intros []; auto.
  Defined.

  Lemma wellformed_wf_local Γ t : wellformed Σ Γ t -> ∥ wf_local Σ Γ ∥.
  Proof.
    intros []. destruct hΣ. destruct H.
    now constructor; eapply typing_wf_local in X0.
    destruct H, hΣ. constructor. red in X.
    destruct X as [ctx [s [eq wf]]].
    now eapply All_local_env_app in wf.
  Qed.

  Equations(noeqns) _isconv_prog (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (ir1 : isred (t1, π1)) (ir2 : isred (t2, π2))
            (aux : Aux (Term t2) Γ t1 π1 π2 h2)
    : { b : bool | if b then conv leq Σ Γ (zippx t1 π1) (zippx t2 π2) else True } :=

    _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 ir1 ir2 aux with prog_viewc t1 t2 := {
    | prog_view_App _ _ _ _ :=
      False_rect _ _ ;

    | prog_view_Const c u c' u' with eq_dec c c' := {
      | left eq1 with eq_dec u u' := {
        | left eq2 with isconv_args_raw Γ (tConst c u) π1 π2 aux := {
          | @exist true h := yes ;
          (* Unfold both constants at once *)
          | @exist false _ with inspect (lookup_env Σ c) := {
            | @exist (Some (ConstantDecl n {| cst_body := Some body |})) eq3 :=
              (* In PCUICChecker, there is no subst but I guess it's just wrong. *)
              isconv_red Γ leq (subst_instance_constr u body) π1
                               (subst_instance_constr u body) π2 aux ;
            (* Inductive or not found *)
            | @exist _ _ := no
            }
          } ;
        (* If the two constants are different, we unfold one of them *)
        | right _ with inspect (lookup_env Σ c') := {
          | @exist (Some (ConstantDecl n {| cst_body := Some b |})) eq1 :=
            isconv_red Γ leq (tConst c u) π1 (subst_instance_constr u' b) π2 aux ;
          (* Inductive or not found *)
          | _ with inspect (lookup_env Σ c) := {
            | @exist (Some (ConstantDecl n {| cst_body := Some b |})) eq1 :=
              isconv_red Γ leq (subst_instance_constr u b) π1
                               (tConst c' u') π2 aux ;
            (* Both Inductive or not found *)
            | _ := no
            }
          }
        } ;
      | right _ := no
      } ;

    | prog_view_Lambda na A1 t1 na' A2 t2
      with isconv_red_raw Γ Conv A1 (Lambda_ty na t1 π1)
                                 A2 (Lambda_ty na' t2 π2) aux := {
      | @exist true h :=
        isconv_red Γ leq
                   t1 (Lambda_tm na A1 π1)
                   t2 (Lambda_tm na' A2 π2) aux ;
      | @exist false _ := no
      } ;

    | prog_view_Prod na A1 B1 na' A2 B2
      with isconv_red_raw Γ Conv A1 (Prod_l na B1 π1) A2 (Prod_l na' B2 π2) aux := {
      | @exist true h :=
        isconv_red Γ leq
                   B1 (Prod_r na A1 π1)
                   B2 (Prod_r na' A2 π2) aux ;
      | @exist false _ := no
      } ;

    | prog_view_Case ind par p c brs ind' par' p' c' brs'
      with inspect (nleq_term (tCase (ind, par) p c brs) (tCase (ind', par') p' c' brs')) := {
      | @exist true eq1 := isconv_args Γ (tCase (ind, par) p c brs) π1 π2 aux ;
      | @exist false _ with inspect (reduce_term RedFlags.default Σ hΣ (Γ ,,, stack_context π1) c _) := {
        | @exist cred eq1 with inspect (reduce_term RedFlags.default Σ hΣ (Γ ,,, stack_context π2) c' _) := {
           | @exist cred' eq2 with inspect (nleq_term cred c && nleq_term cred' c') := {
              | @exist true eq3 := no ;
              | @exist false eq3 :=
                isconv_red Γ leq (tCase (ind, par) p cred brs) π1
                                 (tCase (ind', par') p' cred' brs') π2 aux
              }
           }
        }
      } ;

    | prog_view_Proj p c p' c' with inspect (nleq_term (tProj p c) (tProj p' c')) := {
      | @exist true eq1 := isconv_args Γ (tProj p c) π1 π2 aux ;
      | @exist false _ := no
      } ;

    | prog_view_Fix mfix idx mfix' idx'
      with inspect (nleq_term (tFix mfix idx) (tFix mfix' idx')) := {
      | @exist true eq1 := isconv_args Γ (tFix mfix idx) π1 π2 aux ;
      | @exist false _ with inspect (unfold_one_fix Γ mfix idx π1 _) := {
        | @exist (Some (fn, θ)) eq1
          with inspect (decompose_stack θ) := {
          | @exist (l', θ') eq2
            with inspect (reduce_stack nodelta_flags Σ hΣ (Γ ,,, stack_context θ') fn (appstack l' ε) _) := {
            | @exist (fn', ρ) eq3 :=
              isconv_prog Γ leq fn' (ρ +++ θ') (tFix mfix' idx') π2 aux
            }
          } ;
        | _ with inspect (unfold_one_fix Γ mfix' idx' π2 _) := {
          | @exist (Some (fn, θ)) eq1
            with inspect (decompose_stack θ) := {
            | @exist (l', θ') eq2
              with inspect (reduce_stack nodelta_flags Σ hΣ (Γ ,,, stack_context θ') fn (appstack l' ε) _) := {
              | @exist (fn', ρ) eq3 :=
                isconv_prog Γ leq (tFix mfix idx) π1 fn' (ρ +++ θ') aux
              }
            } ;
          | _ := no
          }
        }
      } ;

    | prog_view_CoFix mfix idx mfix' idx'
      with inspect (nleq_term (tCoFix mfix idx) (tCoFix mfix' idx')) := {
      | @exist true eq1 := isconv_args Γ (tCoFix mfix idx) π1 π2 aux ;
      | @exist false _ := no
      } ;

    | prog_view_other t1 t2 h :=
      isconv_fallback Γ leq t1 π1 t2 π2 aux
    }.

  (* tApp *)
  Next Obligation.
    destruct ir1 as [ha1 _]. discriminate ha1.
  Qed.

  (* tConst *)
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    constructor.
  Qed.
  Next Obligation.
    destruct h. destruct hΣ. eapply conv_conv_l. all: auto.
  Qed.
  Next Obligation.
    eapply red_wellformed ; auto.
    - exact h1.
    - constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_wellformed ; auto.
    - exact h2.
    - constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl.
    eapply cored_zipx.
    eapply cored_const.
    eassumption.
  Qed.
  Next Obligation.
    destruct hΣ.
    destruct b ; auto.
    eapply conv_trans' ; try assumption.
    - eapply red_conv_l ; try assumption.
      eapply red_zippx.
      eapply red_const. eassumption.
    - eapply conv_trans' ; try eassumption.
      eapply red_conv_r ; try assumption.
      eapply red_zippx.
      eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_wellformed ; auto ; [ exact h2 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    unshelve eapply R_cored2.
    all: try reflexivity.
    simpl. eapply cored_zipx.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ.
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_r ; try assumption.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_wellformed ; auto ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. eapply cored_zipx.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l ; try assumption.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_wellformed ; auto ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. eapply cored_zipx.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l ; try assumption.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply red_wellformed ; auto ; [ exact h1 | ].
    constructor. eapply red_zipx. eapply red_const. eassumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl. eapply cored_zipx.
    eapply cored_const. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b0 ; auto.
    eapply conv_trans' ; try eassumption.
    eapply red_conv_l ; try assumption.
    eapply red_zippx. eapply red_const. eassumption.
  Qed.

  (* tLambda *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct b ; auto.
    destruct h0 as [h0].

    unfold zippx in h0. simpl in h0.
    unfold zippx in h. simpl in h. cbn in h.
    unfold zippx.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    case_eq (decompose_stack π2). intros l2 ρ2 e2.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    pose proof (decompose_stack_eq _ _ _ e2). subst.
    rewrite 2!stack_context_appstack in h0.
    rewrite 2!stack_context_appstack in h.

    destruct ir1 as [_ hl1]. cbn in hl1.
    specialize (hl1 eq_refl).
    destruct l1 ; try discriminate hl1. clear hl1.

    destruct ir2 as [_ hl2]. cbn in hl2.
    specialize (hl2 eq_refl).
    destruct l2 ; try discriminate hl2. clear hl2.
    cbn. assumption.
  Qed.

  (* tProd *)
  Next Obligation.
    unshelve eapply R_positionR.
    - reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    unshelve eapply R_positionR.
    - simpl. reflexivity.
    - simpl. unfold xposition. eapply positionR_poscat.
      simpl. rewrite <- app_nil_r. eapply positionR_poscat. constructor.
  Qed.
  Next Obligation.
    destruct b ; auto.
    destruct h0 as [h0].
    unfold zippx in h0. simpl in h0.
    unfold zippx in h. simpl in h. cbn in h.
    unfold zippx.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    case_eq (decompose_stack π2). intros l2 ρ2 e2.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    pose proof (decompose_stack_eq _ _ _ e2). subst.
    rewrite 2!stack_context_appstack in h0.
    rewrite 2!stack_context_appstack in h.

    apply wellformed_zipx in h1; tas.
    apply wellformed_zipc_zippx in h1 ; auto.
    unfold zippx in h1. rewrite decompose_stack_appstack in h1.
    rewrite decompose_stack_twice with (1 := e1) in h1.
    simpl in h1. rewrite app_nil_r in h1.
    apply wellformed_it_mkLambda_or_LetIn in h1; tas.
    pose proof (wellformed_wf_local _ _ h1).
    apply mkApps_Prod_nil' in h1 ; auto. subst.
    destruct H.
    clear aux.
    apply wellformed_zipx in h2; tas.
    apply wellformed_zipc_zippx in h2 ; auto.
    unfold zippx in h2. rewrite decompose_stack_appstack in h2.
    rewrite decompose_stack_twice with (1 := e2) in h2.
    simpl in h2. rewrite app_nil_r in h2.
    apply wellformed_it_mkLambda_or_LetIn in h2; tas.
    apply mkApps_Prod_nil' in h2 ; auto. subst.

    cbn.
    apply it_mkLambda_or_LetIn_stack_context_conv_inv in h0 as [? ?] ; auto.
    eapply it_mkLambda_or_LetIn_conv' ; auto.
    apply it_mkLambda_or_LetIn_stack_context_conv'_inv in h as [[?] hl] ; auto.
    apply Lambda_conv_inv in hl as [[?] ?] ; auto.
    eapply Prod_conv ; auto.
  Qed.

  (* tCase *)
  Next Obligation.
    symmetry in eq1.
    eapply wellformed_rename ; [ assumption .. | exact h2 |].
    eapply eq_term_upto_univ_sym. all: auto.
    eapply eq_term_upto_univ_zipx. all: auto.
    eapply elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      symmetry in eq1.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + eapply nleq_term_zipx. assumption.
    - simpl. constructor.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    eapply conv_conv. auto.
    destruct h. constructor.
    eapply conv_alt_trans ; try eassumption.
    eapply conv_zippx ; auto.
    constructor.
    symmetry in eq1.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - assumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    apply wellformed_zipx in h1 ; tas.
    zip fold in h1. apply wellformed_context in h1 ; auto. simpl in h1.
    destruct h1 as [[T h1] | [[ctx [s [h1 _]]]]] ; [| discriminate ].
    apply inversion_Case in h1 as hh ; auto.
    destruct hh
      as [uni [args [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]]].
    left. eexists. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    clear aux.
    apply wellformed_zipx in h2 ; tas.
    zip fold in h2. apply wellformed_context in h2 ; auto. simpl in h2.
    destruct h2 as [[T h2] | [[ctx [s [h2 _]]]]] ; [| discriminate ].
    apply inversion_Case in h2 as hh ; auto.
    destruct hh
      as [uni [args [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]]]].
    left. eexists. eassumption.
  Qed.
  Next Obligation.
    eapply red_wellformed ; auto.
    - exact h1.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipx.
      eapply reds_case.
      + constructor.
      + assumption.
      + clear.
        induction brs ; eauto.
  Qed.
  Next Obligation.
    eapply red_wellformed ; auto.
    - exact h2.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ ?t ?h ] =>
        pose proof (reduce_term_sound f Σ hΣ Γ t h) as [hr]
      end.
      constructor.
      eapply red_zipx.
      eapply reds_case.
      + constructor.
      + assumption.
      + clear.
        induction brs' ; eauto.
  Qed.
  Next Obligation.
    match goal with
    | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      destruct (reduce_stack_Req f Σ hΣ Γ c ε h) as [e | hr]
    end.
    - match goal with
      | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
        destruct (reduce_stack_Req f Σ hΣ Γ c' ε h) as [e' | hr]
      end.
      + exfalso.
        unfold reduce_term in eq3.
        rewrite e in eq3.
        rewrite e' in eq3.
        cbn in eq3. symmetry in eq3.
        assert (bot : eqb_term_upto_univ eqb eqb c c && eqb_term_upto_univ eqb eqb c' c').
        { apply andb_and. split.
          - eapply introT.
            + eapply reflect_eq_term_upto_univ_eqb.
            + eapply eq_term_upto_univ_refl. all: intro ; reflexivity.
          - eapply introT.
            + eapply reflect_eq_term_upto_univ_eqb.
            + eapply eq_term_upto_univ_refl. all: intro ; reflexivity.
        }
        rewrite bot in eq3. discriminate.
      + dependent destruction hr.
        * unshelve eapply R_cored2.
          all: try reflexivity.
          -- simpl. unfold reduce_term. rewrite e. reflexivity.
          -- simpl. eapply cored_zipx. eapply cored_case. assumption.
        * exfalso.
          destruct y'. simpl in H0. inversion H0. subst.
          unfold reduce_term in eq3.
          rewrite e in eq3.
          rewrite <- H2 in eq3.
          cbn in eq3. symmetry in eq3.
          assert (bot : eqb_term_upto_univ eqb eqb c c && eqb_term_upto_univ eqb eqb c' c').
          { apply andb_and. split.
            - eapply introT.
              + eapply reflect_eq_term_upto_univ_eqb.
              + eapply eq_term_upto_univ_refl. all: intro ; reflexivity.
            - eapply introT.
              + eapply reflect_eq_term_upto_univ_eqb.
              + eapply eq_term_upto_univ_refl. all: intro ; reflexivity.
          }
          rewrite bot in eq3. discriminate.
    - dependent destruction hr.
      + eapply R_cored. simpl.
        eapply cored_zipx. eapply cored_case. assumption.
      + match goal with
        | |- context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
          destruct (reduce_stack_Req f Σ hΣ Γ c' ε h) as [e' | hr]
        end.
        * exfalso.
          destruct y'. simpl in H0. inversion H0. subst.
          unfold reduce_term in eq3.
          rewrite e' in eq3.
          rewrite <- H2 in eq3.
          cbn in eq3. symmetry in eq3.
          assert (bot : eqb_term_upto_univ eqb eqb c c && eqb_term_upto_univ eqb eqb c' c').
          { apply andb_and. split.
            - eapply introT.
              + eapply reflect_eq_term_upto_univ_eqb.
              + eapply eq_term_upto_univ_refl. all: intro ; reflexivity.
            - eapply introT.
              + eapply reflect_eq_term_upto_univ_eqb.
              + eapply eq_term_upto_univ_refl. all: intro ; reflexivity.
          }
          rewrite bot in eq3. discriminate.
        * dependent destruction hr.
          -- unshelve eapply R_cored2.
             all: try reflexivity.
             ++ simpl. unfold reduce_term.
                destruct y'. simpl in H0. inversion H0. subst.
                rewrite <- H3. reflexivity.
             ++ simpl. eapply cored_zipx. eapply cored_case. assumption.
          -- exfalso.
             destruct y'. simpl in H0. inversion H0. subst.
             destruct y'0. simpl in H2. inversion H2. subst.
             unfold reduce_term in eq3.
             rewrite <- H4 in eq3.
             rewrite <- H5 in eq3.
             cbn in eq3. symmetry in eq3.
             assert (bot : eqb_term_upto_univ eqb eqb c c && eqb_term_upto_univ eqb eqb c' c').
             { apply andb_and. split.
               - eapply introT.
                 + eapply reflect_eq_term_upto_univ_eqb.
                 + eapply eq_term_upto_univ_refl. all: intro ; reflexivity.
               - eapply introT.
                 + eapply reflect_eq_term_upto_univ_eqb.
                 + eapply eq_term_upto_univ_refl. all: intro ; reflexivity.
             }
             rewrite bot in eq3. discriminate.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c h) as hr
    end.
    match type of h with
    | context [ reduce_term ?f ?Σ ?hΣ ?Γ c' ?h ] =>
      pose proof (reduce_term_sound f Σ hΣ Γ c' h) as hr'
    end.
    destruct hr as [hr], hr' as [hr'].
    eapply conv_trans'.
    - assumption.
    - eapply red_conv_l ; try assumption.
      eapply red_zippx.
      eapply reds_case.
      + constructor.
      + eassumption.
      + instantiate (1 := brs).
        clear.
        induction brs ; eauto.
    - eapply conv_trans' ; try eassumption.
      eapply red_conv_r ; try assumption.
      eapply red_zippx.
      eapply reds_case.
      + constructor.
      + eassumption.
      + clear.
        induction brs' ; eauto.
  Qed.

  (* tProj *)
  Next Obligation.
    destruct hΣ as [wΣ].
    eapply wellformed_rename ; try assumption.
    - exact h2.
    - apply eq_term_upto_univ_sym ; auto.
      eapply eq_term_upto_univ_zipx ; auto.
      eapply elimT.
      + eapply reflect_eq_term_upto_univ_eqb.
      + symmetry. assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + eapply nleq_term_zipx.
        symmetry. assumption.
    - simpl. constructor.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    eapply conv_conv. auto.
    destruct h. constructor.
    eapply conv_alt_trans ; try eassumption.
    eapply conv_zippx ; auto.
    constructor.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - symmetry. assumption.
  Qed.

  (* tFix *)
  Next Obligation.
    destruct hΣ as [wΣ].
    eapply wellformed_rename ; try assumption.
    - exact h2.
    - apply eq_term_upto_univ_sym ; auto.
      eapply eq_term_upto_univ_zipx ; auto.
      eapply elimT.
      + eapply reflect_eq_term_upto_univ_eqb.
      + symmetry. assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + eapply nleq_term_zipx.
        symmetry. assumption.
    - simpl. constructor.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    destruct h as [h].
    eapply conv_conv; auto.
    constructor.
    eapply conv_alt_trans ; try eassumption.
    eapply conv_zippx ; auto.
    constructor.
    symmetry in eq1.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - assumption.
  Qed.
  Next Obligation.
    cbn. rewrite zipc_appstack. cbn.
    apply unfold_one_fix_red_zippx in eq1 as r.
    unfold zippx in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π1). intros l1 ρ1 e1.
    rewrite e1 in r.
    apply wellformed_zipx in h1 as hh1 ; auto.
    apply wellformed_zipc_zippx in hh1 ; auto.
    pose proof (decompose_stack_eq _ _ _ e1). subst.
    unfold zippx in hh1. rewrite e1 in hh1.
    pose proof (red_wellformed _ hΣ hh1 r) as hh.
    apply wellformed_it_mkLambda_or_LetIn in hh; tas.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c2
    end.
    rewrite <- eq3 in r2. cbn in r2. rewrite zipc_appstack in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in c2. cbn in c2. rewrite stack_context_appstack in c2.
    cbn in c2.
    case_eq (decompose_stack ρ). intros l ξ e.
    rewrite e in d2. cbn in d2. subst.
    apply wellformed_zipx in h1 as hh1; tas.
    pose proof (red_wellformed _ hΣ hh1 r1) as hh.
    apply PCUICPosition.red_context in r2.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in hh. cbn in r2.
    pose proof (red_wellformed _ hΣ hh (sq r2)) as hh2.
    eapply zipx_wellformed ; auto.
    rewrite zipc_stack_cat.
    assumption.
  Qed.
  Next Obligation.
    apply unfold_one_fix_cored in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored. simpl. eapply cored_it_mkLambda_or_LetIn.
    rewrite app_context_nil_l.
    eapply red_cored_cored ; try eassumption.
    apply PCUICPosition.red_context in r2. cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    assumption.
  Qed.
  Next Obligation.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2 ;
      pose proof (reduce_stack_isred f Σ hΣ Γ t π h eq_refl) as ir
    end.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in ir. destruct ir as [? hl].
    split.
    - assumption.
    - simpl. intro h. specialize (hl h). cbn in hl.
      case_eq (decompose_stack ρ). intros l π e.
      rewrite e in d2. cbn in d2. subst.
      pose proof (decompose_stack_eq _ _ _ e). subst.
      rewrite stack_cat_appstack.
      apply isStackApp_false_appstack in hl. subst. cbn.
      eapply decompose_stack_noStackApp. symmetry. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    apply unfold_one_fix_red_zippx in eq1 as r1.
    destruct r1 as [r1].
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    apply unfold_one_fix_decompose in eq1 as d1.
    assert (r2' : red (fst Σ) Γ (zippx fn θ) (zippx fn' (ρ +++ θ'))).
    { unfold zippx.
      case_eq (decompose_stack ρ). intros l ξ e.
      rewrite e in d2. cbn in d2. subst.
      pose proof (decompose_stack_eq _ _ _ e). subst.
      rewrite stack_cat_appstack. rewrite decompose_stack_appstack.
      rewrite <- eq2.
      cbn in r2. rewrite 2!zipc_appstack in r2. cbn in r2.
      rewrite stack_context_decompose.
      eapply red_it_mkLambda_or_LetIn.
      rewrite <- eq2 in d1. cbn in d1. subst.
      case_eq (decompose_stack π1). intros l1 ρ1 e1.
      simpl. rewrite e1 in r2. simpl in r2.
      pose proof (decompose_stack_eq _ _ _ e1). subst.
      rewrite decompose_stack_twice with (1 := e1). cbn.
      rewrite app_nil_r.
      assumption.
    }
    pose proof (red_trans _ _ _ _ _ r1 r2') as r.
    eapply conv_trans'.
    - assumption.
    - eapply red_conv_l. all: eassumption.
    - assumption.
  Qed.
  Next Obligation.
    cbn. rewrite zipc_appstack. cbn.
    apply unfold_one_fix_red_zippx in eq1 as r.
    unfold zippx in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π2). intros l2 ρ2 e2.
    rewrite e2 in r.
    apply wellformed_zipx in h2 as hh2; tas.
    apply wellformed_zipc_zippx in hh2 ; auto.
    pose proof (decompose_stack_eq _ _ _ e2). subst.
    unfold zippx in hh2. rewrite e2 in hh2.
    pose proof (red_wellformed _ hΣ hh2 r) as hh.
    apply wellformed_it_mkLambda_or_LetIn in hh; tas.
  Qed.
  Next Obligation.
    apply unfold_one_fix_red in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2 ;
      pose proof (reduce_stack_context f Σ hΣ Γ t π h) as c2
    end.
    rewrite <- eq3 in r2. cbn in r2. rewrite zipc_appstack in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in c2. cbn in c2. rewrite stack_context_appstack in c2.
    cbn in c2.
    case_eq (decompose_stack ρ). intros l ξ e.
    rewrite e in d2. cbn in d2. subst.
    apply wellformed_zipx in h2 as hh2; tas.
    pose proof (red_wellformed _ hΣ hh2 r1) as hh.
    apply PCUICPosition.red_context in r2.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in hh. cbn in r2.
    pose proof (red_wellformed _ hΣ hh (sq r2)) as hh'.
    eapply zipx_wellformed ; auto.
    rewrite zipc_stack_cat; tas.
  Qed.
  Next Obligation.
    apply unfold_one_fix_cored in eq1 as r1.
    apply unfold_one_fix_decompose in eq1 as d1.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2]
    end.
    rewrite <- eq3 in r2.
    eapply R_cored2. all: try reflexivity. simpl.
    eapply cored_it_mkLambda_or_LetIn.
    rewrite app_context_nil_l.
    eapply red_cored_cored ; try eassumption.
    cbn in r2.
    rewrite zipc_stack_cat.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    zip fold. eapply PCUICPosition.red_context.
    assumption.
  Qed.
  Next Obligation.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2 ;
      pose proof (reduce_stack_isred f Σ hΣ Γ t π h eq_refl) as ir
    end.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    rewrite <- eq3 in ir. destruct ir as [? hl].
    split.
    - assumption.
    - simpl. intro h. specialize (hl h). cbn in hl.
      case_eq (decompose_stack ρ). intros l π e.
      rewrite e in d2. cbn in d2. subst.
      pose proof (decompose_stack_eq _ _ _ e). subst.
      rewrite stack_cat_appstack.
      apply isStackApp_false_appstack in hl. subst. cbn.
      eapply decompose_stack_noStackApp. symmetry. eassumption.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    apply unfold_one_fix_red_zippx in eq1 as r1.
    destruct r1 as [r1].
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2.
    rewrite <- eq3 in d2. cbn in d2. rewrite decompose_stack_appstack in d2.
    cbn in d2.
    apply unfold_one_fix_decompose in eq1 as d1.
    assert (r2' : red (fst Σ) Γ (zippx fn θ) (zippx fn' (ρ +++ θ'))).
    { unfold zippx.
      case_eq (decompose_stack ρ). intros l ξ e.
      rewrite e in d2. cbn in d2. subst.
      pose proof (decompose_stack_eq _ _ _ e). subst.
      rewrite stack_cat_appstack. rewrite decompose_stack_appstack.
      rewrite <- eq2.
      cbn in r2. rewrite 2!zipc_appstack in r2. cbn in r2.
      rewrite stack_context_decompose.
      eapply red_it_mkLambda_or_LetIn.
      rewrite <- eq2 in d1. cbn in d1. subst.
      case_eq (decompose_stack π2). intros l2 ρ2 e2.
      simpl. rewrite e2 in r2. simpl in r2.
      pose proof (decompose_stack_eq _ _ _ e2). subst.
      rewrite decompose_stack_twice with (1 := e2). cbn.
      rewrite app_nil_r.
      assumption.
    }
    pose proof (red_trans _ _ _ _ _ r1 r2') as r.
    eapply conv_trans' ; revgoals.
    - eapply red_conv_r. all: eassumption.
    - assumption.
    - assumption.
  Qed.

  (* tCoFix *)
  Next Obligation.
    destruct hΣ as [wΣ].
    eapply wellformed_rename ; try assumption.
    - exact h2.
    - apply eq_term_upto_univ_sym ; auto.
      eapply eq_term_upto_univ_zipx ; auto.
      eapply elimT.
      + eapply reflect_eq_term_upto_univ_eqb.
      + symmetry. assumption.
  Qed.
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    - simpl.
      eapply ssrbool.elimT.
      + eapply reflect_nleq_term.
      + eapply nleq_term_zipx.
        symmetry. assumption.
    - simpl. constructor.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    eapply conv_conv; auto.
    destruct h. constructor.
    eapply conv_alt_trans ; try eassumption.
    eapply conv_zippx ; auto.
    constructor.
    symmetry in eq1.
    eapply eq_term_upto_univ_eq_eq_term.
    eapply elimT.
    - eapply reflect_eq_term_upto_univ_eqb.
    - assumption.
  Qed.

  (* Fallback *)
  Next Obligation.
    unshelve eapply R_stateR.
    all: try reflexivity.
    simpl. constructor.
  Qed.

  Definition Aux' Γ t args l1 π1 π2 h2 :=
     forall u1 u2 ca1 a1 ρ2
       (h1' : wtp Γ u1 (coApp (mkApps t ca1) (appstack a1 π1)))
       (h2' : wtp Γ u2 ρ2),
       let x := mkpack (Reduction u2) Γ u1 (coApp (mkApps t ca1) (appstack a1 π1)) ρ2 h2' in
       let y := mkpack Args Γ (mkApps t args) (appstack l1 π1) π2 h2 in
       (S #|ca1| + #|a1| = #|args| + #|l1|)%nat ->
       pzt x = pzt y /\
       positionR (` (pps1 x)) (` (pps1 y)) ->
       Ret (Reduction u2) Γ u1 (coApp (mkApps t ca1) (appstack a1 π1)) ρ2.

  Equations(noeqns) _isconv_args' (Γ : context) (t : term) (args : list term)
            (l1 : list term) (π1 : stack) (h1 : wtp Γ (mkApps t args) (appstack l1 π1))
            (l2 : list term) (π2 : stack) (h2 : wtp Γ (mkApps t args) (appstack l2 π2))
            (aux : Aux' Γ t args l1 π1 (appstack l2 π2) h2)
    : { b : bool | if b then ∥ Σ ;;; Γ |- zippx (mkApps t args) (appstack l1 π1) == zippx (mkApps t args) (appstack l2 π2) ∥ else True } by struct l1 :=
    _isconv_args' Γ t args (u1 :: l1) π1 h1 (u2 :: l2) π2 h2 aux
    with aux u1 u2 args l1 (coApp (mkApps t args) (appstack l2 π2)) _ _ _ _ Conv I I := {
    | @exist true H1 with _isconv_args' Γ t (args ++ [u1]) l1 π1 _ l2 π2 _ _ := {
      | @exist true H2 := yes ;
      | @exist false _ := no
      } ;
    | @exist false _ := no
    } ;

    _isconv_args' Γ t args [] ε h1 [] ε h2 aux := yes ;

    _isconv_args' Γ t args l1 π1 h1 l2 π2 h2 aux := no.
  Next Obligation.
    constructor. apply PCUICCumulativity.conv_alt_refl, eq_term_refl.
  Defined.
  Next Obligation.
    split ; [ reflexivity |].
    unfold xposition. eapply positionR_poscat.
    cbn. eapply positionR_poscat. constructor.
  Defined.
  Next Obligation.
    rewrite <- mkApps_nested. assumption.
  Defined.
  Next Obligation.
    destruct hΣ as [wΣ].
    clear _isconv_args' aux.
    rewrite <- mkApps_nested.
    destruct H1 as [H1]. unfold zippx in H1.
    simpl in H1. rewrite 2!stack_context_appstack in H1.

    apply it_mkLambda_or_LetIn_stack_context_conv_inv in H1 as h ; auto.
    destruct h as [hc hu].

    apply zipx_wellformed ; auto.
    (* We get that u2 is well-typed *)
    apply wellformed_zipx in h2 ; tas. cbn in h2. cbn.
    zip fold in h2.
    apply wellformed_context in h2 as hh2 ; auto. simpl in hh2.
    rewrite stack_context_appstack in hh2.
    destruct hh2 as [[A2 hh2]|[[ctx [s [? _]]]]]; [| discriminate ].
    apply inversion_App in hh2 as ihh2 ; auto.
    destruct ihh2 as [na2 [A2' [B2' [? [hu2 ?]]]]].
    (* We get that u1 is well-typed *)
    apply wellformed_zipx in h1 ; tas. cbn in h1. cbn.
    zip fold in h1.
    apply wellformed_context in h1 as hh1 ; auto. simpl in hh1.
    rewrite stack_context_appstack in hh1.
    destruct hh1 as [[A1 hh1] | [[ctx [s [? _]]]]] ; [| discriminate ].
    apply inversion_App in hh1 as ihh1 ; auto.
    destruct ihh1 as [na1 [A1' [B1' [? [hu1 ?]]]]].
    (* apply type_it_mkLambda_or_LetIn in hu1 ; auto. *)
    (* apply type_it_mkLambda_or_LetIn in hu2 ; auto. *)
    match goal with
    | |- wellformed ?Σ ?Γ (zipc (tApp ?f ?u) ?π) =>
      change (wellformed Σ Γ (zipc u (coApp f π)))
    end.
    cbn in h2.
    match type of h2 with
    | wellformed ?Σ ?Γ (zipc (tApp ?f ?u) ?π) =>
      change (wellformed Σ Γ (zipc u (coApp f π))) in h2
    end.
    eapply wellformed_zipc_replace. auto. auto. eapply h2.
    - simpl. rewrite stack_context_appstack.
      left. exists A1'. eapply context_conversion. auto. 2:eauto.
      + now eapply typing_wf_local in hh1.
      + assumption.
      + now eapply typing_wf_local in hu2.
    - simpl. rewrite stack_context_appstack.
      eapply conv_alt_conv_ctx ; eauto.
  Defined.
  Next Obligation.
    simpl in H0. destruct H0 as [eq hp].
    rewrite app_length in H. cbn in H.
    eapply aux. all: auto.
    - cbn. omega.
    - instantiate (1 := h2'). simpl. split.
      + rewrite <- mkApps_nested in eq. assumption.
      + subst x y.
        unfold xposition. cbn. apply positionR_poscat.
        rewrite 2!stack_position_appstack.
        rewrite <- !app_assoc. apply positionR_poscat.
        assert (h : forall n m, positionR (list_make n app_l ++ [app_r]) (list_make m app_l)).
        { clear. intro n. induction n ; intro m.
          - destruct m ; constructor.
          - destruct m.
            + constructor.
            + cbn. constructor. apply IHn.
        }
        rewrite <- list_make_app_r.
        apply (h #|a1| (S #|l1|)).
  Defined.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct H1 as [H1]. destruct H2 as [H2].
    constructor.
    unfold zippx. simpl.
    rewrite 2!decompose_stack_appstack. simpl.
    unfold zippx in H1. simpl in H1.
    unfold zippx in H2. rewrite 2!decompose_stack_appstack in H2.
    rewrite <- !mkApps_nested in H2. cbn in H2.
    rewrite 2!stack_context_decompose in H2.
    rewrite 2!stack_context_decompose.
    rewrite <- !mkApps_nested. cbn in H2.
    rewrite 2!stack_context_appstack in H1.
    case_eq (decompose_stack π1). intros args1 ρ1 e1.
    rewrite e1 in H2. cbn in H2. cbn.
    case_eq (decompose_stack π2). intros args2 ρ2 e2.
    rewrite e2 in H2. cbn in H2. cbn.
    pose proof (decompose_stack_eq _ _ _ e1).
    pose proof (decompose_stack_eq _ _ _ e2).
    subst.
    rewrite !stack_context_appstack in H1.
    rewrite !stack_context_appstack in H2.
    rewrite !stack_context_appstack.

    apply it_mkLambda_or_LetIn_stack_context_conv_inv in H1 as [? ?] ; auto.
    apply it_mkLambda_or_LetIn_stack_context_conv_inv in H2 as [? ?] ; auto.
    eapply it_mkLambda_or_LetIn_conv ; auto.
    eapply conv_alt_trans ; eauto.
    eapply mkApps_conv_weak ; auto.
    eapply mkApps_conv_weak ; auto.
    eapply App_conv ; auto.
  Defined.

  Equations(noeqns) _isconv_args (Γ : context) (t : term)
           (π1 : stack) (h1 : wtp Γ t π1)
           (π2 : stack) (h2 : wtp Γ t π2)
           (aux : Aux Args Γ t π1 π2 h2)
    : { b : bool | if b then ∥ Σ ;;; Γ |- zippx t π1 == zippx t π2 ∥ else True } :=
    _isconv_args Γ t π1 h1 π2 h2 aux with inspect (decompose_stack π1) := {
    | @exist (l1, θ1) eq1 with inspect (decompose_stack π2) := {
      | @exist (l2, θ2) eq2 with _isconv_args' Γ t [] l1 θ1 _ l2 θ2 _ _ := {
        | @exist true h := yes ;
        | @exist false _ := no
        }
      }
    }.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    assumption.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    assumption.
  Qed.
  Next Obligation.
    specialize (aux (Reduction u2)) as h. cbn in h.
    eapply h. all: auto.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    instantiate (1 := h2').
    simpl in H0. destruct H0 as [eq hp].
    unshelve eapply R_positionR ; try assumption.
    simpl. f_equal. assumption.
  Qed.
  Next Obligation.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq1)). subst.
    pose proof (decompose_stack_eq _ _ _ (eq_sym eq2)). subst.
    assumption.
  Qed.

  Equations unfold_one_case (Γ : context) (ind : inductive) (par : nat)
            (p c : term) (brs : list (nat × term))
            (h : wellformed Σ Γ (tCase (ind, par) p c brs)) : option term :=
    unfold_one_case Γ ind par p c brs h
    with inspect (reduce_stack RedFlags.default Σ hΣ Γ c ε _) := {
    | @exist (cred, ρ) eq with cc_viewc cred := {
      | ccview_construct ind' n ui with inspect (decompose_stack ρ) := {
        | @exist (args, ξ) eq' := Some (iota_red par n args brs)
        } ;
      | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
        | @exist (Some (narg, fn)) eq2 with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' := Some (tCase (ind, par) p (mkApps fn args) brs)
          } ;
        | @exist None eq2 := None
        } ;
      | ccview_other t _ := None
      }
    }.
  Next Obligation.
    destruct hΣ as [wΣ].
    cbn. destruct h as [[T h] | [[ctx [s [h1 _]]]]]; [| discriminate ].
    apply inversion_Case in h ; auto.
    destruct h as
        [u [args [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]]]].
    left; eexists. eassumption.
  Qed.

  Lemma unfold_one_case_cored :
    forall Γ ind par p c brs h t,
      Some t = unfold_one_case Γ ind par p c brs h ->
      cored Σ Γ t (tCase (ind, par) p c brs).
  Proof.
    intros Γ ind par p c brs h t e.
    revert e.
    funelim (unfold_one_case Γ ind par p c brs h).
    all: intros eq ; noconf eq.
    - match type of e with
      | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_sound f Σ hΣ Γ t π h) as [r] ;
        pose proof (reduce_stack_decompose f Σ hΣ Γ t π h) as d
      end.
      rewrite <- e in r.
      rewrite <- e in d. cbn in d. rewrite <- e0 in d. cbn in d. subst.
      cbn in r.
      clear H. symmetry in e0. apply decompose_stack_eq in e0. subst.
      rewrite zipc_appstack in r. cbn in r.
      assert (r' : ∥ red Σ Γ (tCase (ind, par) p c brs) (tCase (ind, par) p (mkApps (tConstruct ind0 n ui) l) brs) ∥).
      { constructor. eapply red_case_c. eassumption. }
      pose proof (red_wellformed _ hΣ h r') as h'.
      eapply Case_Construct_ind_eq in h' ; eauto. subst.
      eapply cored_red_cored.
      + constructor. eapply red_iota.
      + eapply red_case_c. eassumption.
    - match type of e with
      | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_sound f Σ hΣ Γ t π h) as [r] ;
        pose proof (reduce_stack_decompose f Σ hΣ Γ t π h) as d
      end.
      rewrite <- e in r.
      rewrite <- e in d. cbn in d. rewrite <- e1 in d. cbn in d. subst.
      cbn in r.
      clear H. symmetry in e1. apply decompose_stack_eq in e1. subst.
      rewrite zipc_appstack in r. cbn in r.
      assert (r' : ∥ red Σ Γ (tCase (ind, par) p c brs) (tCase (ind, par) p (mkApps (tCoFix mfix idx) l) brs) ∥).
      { constructor. eapply red_case_c. eassumption. }
      pose proof (red_wellformed _ hΣ h r') as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_case. eauto.
      + eapply red_case_c. eassumption.
  Qed.

  Equations unfold_one_proj (Γ : context) (p : projection) (c : term)
            (h : wellformed Σ Γ (tProj p c)) : option term :=

    unfold_one_proj Γ p c h with p := {
    | (i, pars, narg) with inspect (reduce_stack RedFlags.default Σ hΣ Γ c ε _) := {
      | @exist (cred, ρ) eq with cc_viewc cred := {
        | ccview_construct ind' n ui with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' with inspect (nth_error args (pars + narg)) := {
            | @exist (Some arg) eq2 := Some arg ;
            | @exist None _ := None
            }
          } ;
        | ccview_cofix mfix idx with inspect (decompose_stack ρ) := {
          | @exist (args, ξ) eq' with inspect (unfold_cofix mfix idx) := {
            | @exist (Some (narg, fn)) eq2 :=
              Some (tProj (i, pars, narg) (mkApps fn args)) ;
            | @exist None eq2 := None
            }
          } ;
        | ccview_other t _ := None
        }
      }
    }.
  Next Obligation.
    destruct hΣ as [wΣ].
    cbn. destruct h as [[T h] | [[ctx [s [h1 _]]]]]; [| discriminate ].
    apply inversion_Proj in h ; auto.
    destruct h as [uni [mdecl [idecl [pdecl [args' [? [? [? ?]]]]]]]].
    left. eexists. eassumption.
  Qed.

  Lemma unfold_one_proj_cored :
    forall Γ p c h t,
      Some t = unfold_one_proj Γ p c h ->
      cored Σ Γ t (tProj p c).
  Proof.
    intros Γ p c h t e.
    revert e.
    funelim (unfold_one_proj Γ p c h).
    all: intros eq ; noconf eq.
    - match type of e with
      | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_sound f Σ hΣ Γ t π h) as [r] ;
        pose proof (reduce_stack_decompose f Σ hΣ Γ t π h) as d
      end.
      rewrite <- e in r.
      rewrite <- e in d. cbn in d. rewrite <- e0 in d. cbn in d. subst.
      cbn in r.
      clear H0. symmetry in e0. apply decompose_stack_eq in e0. subst.
      rewrite zipc_appstack in r. cbn in r.
      pose proof (red_proj_c (i, n0, n) _ _ r) as r'.
      pose proof (red_wellformed _ hΣ h (sq r')) as h'.
      apply Proj_Constuct_ind_eq in h' ; auto. subst.
      eapply cored_red_cored.
      + constructor. eapply red_proj. eauto.
      + eapply red_proj_c. eassumption.
    - match type of e with
      | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
        pose proof (reduce_stack_sound f Σ hΣ Γ t π h) as [r] ;
        pose proof (reduce_stack_decompose f Σ hΣ Γ t π h) as d
      end.
      rewrite <- e in r.
      rewrite <- e in d. cbn in d. rewrite <- e0 in d. cbn in d. subst.
      cbn in r.
      clear H0. symmetry in e0. apply decompose_stack_eq in e0. subst.
      rewrite zipc_appstack in r. cbn in r.
      pose proof (red_proj_c (i, n0, n) _ _ r) as r'.
      pose proof (red_wellformed _ hΣ h (sq r')) as h'.
      eapply cored_red_cored.
      + constructor. eapply red_cofix_proj. eauto.
      + eapply red_proj_c. eassumption.
  Qed.

  Equations reducible_head (Γ : context) (t : term) (π : stack)
            (h : wtp Γ t π)
    : option (term × stack) :=

    reducible_head Γ (tFix mfix idx) π h := unfold_one_fix Γ mfix idx π h ;

    reducible_head Γ (tCase (ind, par) p c brs) π h
    with inspect (unfold_one_case (Γ ,,, stack_context π) ind par p c brs _) := {
    | @exist (Some t) eq :=Some (t, π) ;
    | @exist None _ := None
    } ;

    reducible_head Γ (tProj p c) π h
    with inspect (unfold_one_proj (Γ ,,, stack_context π) p c _) := {
    | @exist (Some t) eq := Some (t, π) ;
    | @exist None _ := None
    } ;

    reducible_head Γ (tConst c u) π h
    with inspect (lookup_env Σ c) := {
    | @exist (Some (ConstantDecl _ {| cst_body := Some body |})) eq :=
      Some (subst_instance_constr u body, π) ;
    | @exist _ _ := None
    } ;

    reducible_head Γ _ π h := None.
  Next Obligation.
    apply wellformed_zipx in h; tas. zip fold in h.
    apply wellformed_context in h ; auto.
  Qed.
  Next Obligation.
    apply wellformed_zipx in h; tas. zip fold in h.
    apply wellformed_context in h ; auto.
  Qed.

  Lemma reducible_head_red_zippx :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      ∥ red (fst Σ) Γ (zippx t π) (zippx fn ξ) ∥.
  Proof.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_red_zippx. eassumption.
    - constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s eq.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      apply lookup_env_ConstantDecl_inv in e as ?. subst.
      eapply trans_red.
      + constructor.
      + eapply red_delta.
        * unfold declared_constant. eauto.
        * reflexivity.
    - apply unfold_one_case_cored in e as r. apply cored_red in r.
      destruct r as [r].
      constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s e'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      apply decompose_stack_eq in e'. subst.
      rewrite stack_context_appstack in r. assumption.
    - apply unfold_one_proj_cored in e as r. apply cored_red in r.
      destruct r as [r].
      constructor. unfold zippx.
      case_eq (decompose_stack π). intros l s e'.
      eapply red_it_mkLambda_or_LetIn. eapply red_mkApps_f.
      apply decompose_stack_eq in e'. subst.
      rewrite stack_context_appstack in r. assumption.
  Qed.

  Lemma reducible_head_cored :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      cored Σ Γ (zipc fn ξ) (zipc t π).
  Proof.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_cored. eassumption.
    - repeat zip fold. eapply cored_context.
      apply lookup_env_ConstantDecl_inv in e as ?. subst.
      constructor. eapply red_delta.
      + unfold declared_constant. eauto.
      + reflexivity.
    - repeat zip fold. eapply cored_context.
      eapply unfold_one_case_cored. eassumption.
    - repeat zip fold. eapply cored_context.
      eapply unfold_one_proj_cored. eassumption.
  Qed.

  Lemma reducible_head_decompose :
    forall Γ t π h fn ξ,
      Some (fn, ξ) = reducible_head Γ t π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
  Proof.
    intros Γ t π h fn ξ e.
    revert e.
    funelim (reducible_head Γ t π h).
    all: intro ee ; noconf ee.
    - eapply unfold_one_fix_decompose. eassumption.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.


  Definition leqb_term := eqb_term_upto_univ (try_eqb_universe G)
                                             (try_leqb_universe G).

  Definition eqb_term := eqb_term_upto_univ (try_eqb_universe G)
                                            (try_eqb_universe G).

  Lemma leqb_term_spec t u :
    leqb_term t u -> leq_term (global_ext_constraints Σ) t u.
  Proof.
    pose proof hΣ'.
    apply eqb_term_upto_univ_impl.
    intros u1 u2; eapply (try_eqb_universe_spec G (global_ext_uctx Σ)); tas.
    now eapply wf_ext_global_uctx_invariants.
    now eapply global_ext_uctx_consistent.
    intros u1 u2; eapply (try_leqb_universe_spec G (global_ext_uctx Σ)); tas.
    now eapply wf_ext_global_uctx_invariants.
    now eapply global_ext_uctx_consistent.
  Qed.

  Lemma eqb_term_spec t u :
    eqb_term t u -> eq_term (global_ext_constraints Σ) t u.
  Proof.
    pose proof hΣ'.
    apply eqb_term_upto_univ_impl.
    intros u1 u2; eapply (try_eqb_universe_spec G (global_ext_uctx Σ)); tas.
    now eapply wf_ext_global_uctx_invariants.
    now eapply global_ext_uctx_consistent.
    intros u1 u2; eapply (try_eqb_universe_spec G (global_ext_uctx Σ)); tas.
    now eapply wf_ext_global_uctx_invariants.
    now eapply global_ext_uctx_consistent.
  Qed.

  Equations(noeqns) _isconv_fallback (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (ir1 : isred (t1, π1)) (ir2 : isred (t2, π2))
            (aux : Aux (Fallback t2) Γ t1 π1 π2 h2)
    : { b : bool | if b then conv leq Σ Γ (zippx t1 π1) (zippx t2 π2) else True } :=
    _isconv_fallback Γ leq t1 π1 h1 t2 π2 h2 ir1 ir2 aux
    with inspect (reducible_head Γ t1 π1 h1) := {
    | @exist (Some (rt1, ρ1)) eq1 with inspect (decompose_stack ρ1) := {
      | @exist (l1, θ1) eq2
        with inspect (reduce_stack nodelta_flags Σ hΣ (Γ ,,, stack_context ρ1) rt1 (appstack l1 ε) _) := {
        | @exist (rt1', θ1') eq3 :=
          isconv_prog Γ leq rt1' (θ1' +++ θ1) t2 π2 aux
        }
      } ;
    | @exist None _ with inspect (reducible_head Γ t2 π2 h2) := {
      | @exist (Some (rt2, ρ2)) eq1 with inspect (decompose_stack ρ2) := {
        | @exist (l2, θ2) eq2
          with inspect (reduce_stack nodelta_flags Σ hΣ (Γ ,,, stack_context ρ2) rt2 (appstack l2 ε) _) := {
          | @exist (rt2', θ2') eq3 :=
            isconv_prog Γ leq t1 π1 rt2' (θ2' +++ θ2) aux
          }
        } ;
      | @exist None _ :=
        match leq with
        | Conv => exist (eqb_term (zippx t1 π1) (zippx t2 π2)) _
        | Cumul => exist (leqb_term (zippx t1 π1) (zippx t2 π2)) _
        end
      }
    }.
  Next Obligation.
    cbn. rewrite zipc_appstack. cbn.
    apply wellformed_zipx in h1 as hh1; tas.
    apply reducible_head_red_zippx in eq1 as r.
    unfold zippx in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π1). intros l1' ρ1' e1.
    rewrite e1 in r.
    apply wellformed_zipc_zippx in hh1 ; auto.
    apply decompose_stack_eq in e1 as ?. subst.
    unfold zippx in hh1. rewrite e1 in hh1.
    pose proof (red_wellformed _ hΣ hh1 r) as hh.
    apply wellformed_it_mkLambda_or_LetIn in hh; tas.
    symmetry in eq2.
    apply decompose_stack_eq in eq2. subst.
    rewrite stack_context_appstack.
    assumption.
  Qed.
  Next Obligation.
    apply reducible_head_cored in eq1 as r1. apply cored_red in r1.
    destruct r1 as [r1].
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ1'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    rewrite stack_cat_appstack.
    eapply zipx_wellformed ; auto.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    pose proof (eq_sym eq2) as eq2'.
    apply decompose_stack_eq in eq2'. subst.
    rewrite stack_context_appstack in r2.
    eapply red_wellformed ; auto ; revgoals.
    - constructor. zip fold. eapply PCUICPosition.red_context. eassumption.
    - rewrite zipc_appstack in r1. cbn.
      eapply red_wellformed ; auto ; revgoals.
      + constructor. eassumption.
      + eapply wellformed_zipx; assumption.
  Qed.
  Next Obligation.
    eapply R_cored. simpl.
    eapply cored_it_mkLambda_or_LetIn.
    rewrite app_context_nil_l.
    apply reducible_head_cored in eq1 as r1.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π1). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ1'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite 2!zipc_appstack.
    rewrite zipc_appstack in r2. simpl in r2.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite 2!zipc_appstack in r1.
    rewrite stack_context_appstack in r2.
    eapply red_cored_cored ; try eassumption.
    repeat zip fold. eapply PCUICPosition.red_context. assumption.
  Qed.
  Next Obligation.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_isred nodelta_flags _ hΣ _ _ _ h eq_refl) as ir
    end.
    rewrite <- eq3 in ir. destruct ir as [ia il]. simpl in ia, il.
    split.
    - cbn. assumption.
    - simpl. intro hl. specialize (il hl).
      destruct θ1'. all: simpl. all: try reflexivity. all: try discriminate.
      eapply decompose_stack_noStackApp. eauto.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    apply reducible_head_red_zippx in eq1 as r1. destruct r1 as [r1].
    eapply conv_trans' ; try eassumption.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π1). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ1'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    unfold zippx. rewrite e'.
    unfold zippx in r1. rewrite e' in r1. rewrite <- eq2 in r1.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite decompose_stack_appstack.
    erewrite decompose_stack_twice ; eauto. simpl.
    rewrite app_nil_r.
    eapply red_conv_l ; try assumption.
    eapply red_trans ; try eassumption.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite stack_context_appstack in r2.
    rewrite zipc_appstack in r2. cbn in r2.
    eapply red_it_mkLambda_or_LetIn. assumption.
  Qed.
  Next Obligation.
    cbn. rewrite zipc_appstack. cbn.
    apply wellformed_zipx in h2 as hh2; tas.
    apply reducible_head_red_zippx in eq1 as r.
    unfold zippx in r.
    rewrite <- eq2 in r.
    case_eq (decompose_stack π2). intros l2' ρ2' e2.
    rewrite e2 in r.
    apply wellformed_zipc_zippx in hh2 ; auto.
    apply decompose_stack_eq in e2 as ?. subst.
    unfold zippx in hh2. rewrite e2 in hh2.
    pose proof (red_wellformed _ hΣ hh2 r) as hh.
    apply wellformed_it_mkLambda_or_LetIn in hh; tas.
    symmetry in eq2.
    apply decompose_stack_eq in eq2. subst.
    rewrite stack_context_appstack.
    assumption.
  Qed.
  Next Obligation.
    apply reducible_head_cored in eq1 as r1. apply cored_red in r1.
    destruct r1 as [r1].
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    rewrite stack_cat_appstack.
    eapply zipx_wellformed ; auto.
    rewrite zipc_appstack in r2. cbn in r2.
    rewrite zipc_appstack.
    pose proof (eq_sym eq2) as eq2'.
    apply decompose_stack_eq in eq2'. subst.
    rewrite stack_context_appstack in r2.
    eapply red_wellformed ; auto ; revgoals.
    - constructor. zip fold. eapply PCUICPosition.red_context. eassumption.
    - rewrite zipc_appstack in r1. cbn.
      eapply red_wellformed ; auto ; revgoals.
      + constructor. eassumption.
      + eapply wellformed_zipx; assumption.
  Qed.
  Next Obligation.
    eapply R_cored2. all: simpl. all: try reflexivity.
    eapply cored_it_mkLambda_or_LetIn.
    rewrite app_context_nil_l.
    apply reducible_head_cored in eq1 as r1.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π2). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite 2!zipc_appstack.
    rewrite zipc_appstack in r2. simpl in r2.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite 2!zipc_appstack in r1.
    rewrite stack_context_appstack in r2.
    eapply red_cored_cored ; try eassumption.
    repeat zip fold. eapply PCUICPosition.red_context. assumption.
  Qed.
  Next Obligation.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      pose proof (reduce_stack_isred nodelta_flags _ hΣ _ _ _ h eq_refl) as ir
    end.
    rewrite <- eq3 in ir. destruct ir as [ia il]. simpl in ia, il.
    split.
    - cbn. assumption.
    - simpl. intro hl. specialize (il hl).
      destruct θ2'. all: simpl. all: try reflexivity. all: try discriminate.
      eapply decompose_stack_noStackApp. eauto.
  Qed.
  Next Obligation.
    destruct hΣ as [wΣ].
    destruct b ; auto.
    apply reducible_head_red_zippx in eq1 as r1. destruct r1 as [r1].
    eapply conv_trans' ; try eassumption.
    apply reducible_head_decompose in eq1 as d1.
    rewrite <- eq2 in d1. cbn in d1.
    case_eq (decompose_stack π2). intros l' s' e'.
    rewrite e' in d1. cbn in d1. subst.
    match type of eq3 with
    | _ = reduce_stack ?f ?Σ ?hΣ ?Γ ?t ?π ?h =>
      destruct (reduce_stack_sound f Σ hΣ Γ t π h) as [r2] ;
      pose proof (reduce_stack_decompose nodelta_flags _ hΣ _ _ _ h) as d2
    end.
    rewrite <- eq3 in r2. cbn in r2.
    rewrite <- eq3 in d2. cbn in d2.
    rewrite decompose_stack_appstack in d2. cbn in d2.
    rewrite zipc_appstack in r2. cbn in r2.
    case_eq (decompose_stack θ2'). intros l s e.
    rewrite e in d2. cbn in d2. subst.
    unfold zippx. rewrite e'.
    unfold zippx in r1. rewrite e' in r1. rewrite <- eq2 in r1.
    apply decompose_stack_eq in e as ?. subst.
    apply decompose_stack_eq in e' as ?. subst.
    rewrite stack_cat_appstack. rewrite decompose_stack_appstack.
    erewrite decompose_stack_twice ; eauto. simpl.
    rewrite app_nil_r.
    eapply red_conv_r ; try assumption.
    eapply red_trans ; try eassumption.
    clear eq3. symmetry in eq2. apply decompose_stack_eq in eq2. subst.
    rewrite stack_context_appstack in r2.
    rewrite zipc_appstack in r2. cbn in r2.
    eapply red_it_mkLambda_or_LetIn. assumption.
  Qed.
  Next Obligation.
    destruct eqb_term eqn:Heq; [|trivial].
    constructor. constructor. now apply eqb_term_spec.
  Qed.
  Next Obligation.
    destruct leqb_term eqn:Heq; [|trivial]. destruct hΣ.
    constructor. eapply cumul_refl.
    now apply leqb_term_spec.
  Qed.

  Equations _isconv (s : state) (Γ : context)
            (t : term) (π1 : stack) (h1 : wtp Γ t π1)
            (π2 : stack) (h2 : wts Γ s t π2)
            (aux : Aux s Γ t π1 π2 h2)
  : Ret s Γ t π1 π2 :=
    _isconv (Reduction t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq | _ | _ := _isconv_red Γ leq t1 π1 h1 t2 π2 h2 aux } ;

    _isconv (Term t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq | r1 | r2 := _isconv_prog Γ leq t1 π1 h1 t2 π2 h2 r1 r2 aux } ;

    _isconv Args Γ t π1 h1 π2 h2 aux :=
      λ { | _ | _ | _ := _isconv_args Γ t π1 h1 π2 h2 aux } ;

    _isconv (Fallback t2) Γ t1 π1 h1 π2 h2 aux :=
      λ { | leq | r1 | r2 := _isconv_fallback Γ leq t1 π1 h1 t2 π2 h2 r1 r2 aux }.

  Equations(noeqns) isconv_full (s : state) (Γ : context)
            (t : term) (π1 : stack) (h1 : wtp Γ t π1)
            (π2 : stack) (h2 : wts Γ s t π2)
    : Ret s Γ t π1 π2 :=

    isconv_full s Γ t π1 h1 π2 h2 :=
      Fix_F (R := R)
            (fun '(mkpack s' Γ' t' π1' π2' h2') => wtp Γ' t' π1' -> wts Γ' s' t' π2' -> Ret s' Γ' t' π1' π2')
            (fun pp f => _)
            (x := mkpack s Γ t π1 π2 _)
            _ _ _.
  Next Obligation.
    unshelve eapply _isconv ; try assumption.
    apply wellformed_zipx in h1; tas.
    intros s' Γ' t' π1' π2' h1' h2' hR.
    apply wellformed_zipc_zippx in h1 ; auto.
    destruct pp.
    assert (wth0 = zwts H0) by apply wellformed_irr. subst.
    specialize (f (mkpack s' Γ' t' π1' π2' (zwts h2')) hR). cbn in f.
    eapply f ; assumption.
  Qed.
  Next Obligation.
    destruct s ; assumption.
  Qed.
  Next Obligation.
    apply R_Acc. assumption.
  Qed.

  Definition isconv Γ leq t1 π1 h1 t2 π2 h2 :=
    let '(exist b _) := isconv_full (Reduction t2) Γ t1 π1 h1 π2 h2 leq I I in b.

  Theorem isconv_sound :
    forall Γ leq t1 π1 h1 t2 π2 h2,
      isconv Γ leq t1 π1 h1 t2 π2 h2 ->
      conv leq Σ Γ (zippx t1 π1) (zippx t2 π2).
  Proof.
    unfold isconv.
    intros Γ leq t1 π1 h1 t2 π2 h2.
    destruct isconv_full as [[]] ; auto.
    discriminate.
  Qed.

  Definition isconv_term Γ leq t1 (h1 : wellformed Σ Γ t1) t2 (h2 : wellformed Σ Γ t2) :=
    isconv Γ leq t1 ε (zipx_wellformed flags _ hΣ (π := ε) h1) t2 ε (zipx_wellformed flags _ hΣ (π := ε) h2).

  Theorem isconv_term_sound :
    forall Γ leq t1 h1 t2 h2,
      isconv_term Γ leq t1 h1 t2 h2 ->
      conv leq Σ Γ t1 t2.
  Proof.
    intros Γ leq t1 h1 t2 h2.
    unfold isconv_term. intro h.
    apply isconv_sound in h. assumption.
  Qed.

End Conversion.
