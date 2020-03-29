(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Lia.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping
     PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory
     PCUICWcbvEval PCUICSR PCUICValidity.
From MetaCoq.Erasure Require Import EAstUtils ELiftSubst ETyping EWcbvEval Extract Prelim.

From Equations Require Import Equations.

Local Open Scope list_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance default_checker_flags.

(** ** Inversion on eval *)


Notation type_Construct_inv := PCUICInversion.inversion_Construct.
Notation type_tFix_inv := PCUICInversion.inversion_Fix.

Derive Signature for Forall2.
Lemma eval_box_apps:
  forall (Σ' : E.global_declarations) (e : E.term) (x x' : list E.term)
    (r : E.erasure_reason),
    Forall2 (eval Σ') x x' ->
    eval Σ' e (EAst.tBox r) -> eval Σ' (EAst.mkApps e x) (EAst.tBox r).
Proof.
  intros Σ' e x H2. revert e H2; induction x using rev_ind; cbn; intros; eauto using eval.
  eapply Forall2_app_inv_l in H as [l1' [l2' [H [H' eq]]]]. subst H2.
  depelim H'.
  specialize (IHx e _ _ H H0). simpl.
  rewrite mkApps_app. simpl. econstructor; eauto.
Qed.
