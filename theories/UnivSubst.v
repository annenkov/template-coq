(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Template utils Ast univ Induction LiftSubst.
From Template Require AstUtils.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

(** * Universe substitution

  *WIP*

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)

Definition subst_instance_level u l :=
  match l with
  | univ.Level.lSProp | univ.Level.lProp | univ.Level.lSet | univ.Level.Level _ => l
  | univ.Level.Var n => List.nth n u univ.Level.lProp
  end.

Definition subst_instance_cstrs u cstrs :=
  Constraint.fold (fun '(l,d,r) =>
                     Constraint.add (subst_instance_level u l, d, subst_instance_level u r))
                  cstrs Constraint.empty.

Definition subst_instance_level_expr (u : universe_instance) (s : Universe.Expr.t) :=
  let '(l, b) := s in (subst_instance_level u l, b).

Definition subst_instance_univ (u : universe_instance) (s : universe) :=
  List.map (subst_instance_level_expr u) s.

Definition subst_instance_instance (u u' : universe_instance) :=
  List.map (subst_instance_level u) u'.

Fixpoint subst_instance_constr (u : universe_instance) (c : term) :=
  match c with
  | tRel _ | tVar _ | tMeta _ => c
  | tSort s => tSort (subst_instance_univ u s)
  | tConst c u' => tConst c (subst_instance_instance u u')
  | tInd i u' => tInd i (subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (subst_instance_instance u u')
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tLambda na r T M => tLambda na r (subst_instance_constr u T) (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (List.map (subst_instance_constr u) v)
  | tProd na r A B => tProd na r (subst_instance_constr u A) (subst_instance_constr u B)
  | tCast c kind ty => tCast (subst_instance_constr u c) kind (subst_instance_constr u ty)
  | tLetIn na r b ty b' => tLetIn na r (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | tCase ind r p c brs =>
    let brs' := List.map (on_snd (subst_instance_constr u)) brs in
    tCase ind r (subst_instance_constr u p) (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  end.
