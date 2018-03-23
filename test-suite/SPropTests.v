Require Import PeanoNat.

Require Import Template.Ast.
Require Import Template.Template.
Require Import Template.Checker.
Require Import String.

Inductive sle (n : nat) : nat -> SProp :=
  sle_n : sle n n
| sle_S : forall m : nat, sle n m -> sle n (S m).

Quote Recursively Definition q_sle := (sle 0 0).

Example relevance_irrel : relevance_of_type (fst q_sle) nil (snd q_sle) = RelOk Irrelevant.
Proof. reflexivity. Qed.

Quote Recursively Definition q_arrow := (nat -> nat).

Example relevance_rel: relevance_of_type (fst q_arrow) nil (snd q_arrow) = RelOk Relevant.
Proof. reflexivity. Qed.

Quote Recursively Definition q_id := (fun (x : nat) => x).

Example relevance_not_sort :
  exists a, relevance_of_type (fst q_id) nil (snd q_id) = RelNotSort a.
Proof. eexists. reflexivity. Qed.