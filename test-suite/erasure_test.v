From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.
From MetaCoq.SafeChecker Require Import Loader.
Local Open Scope string_scope.

MetaCoq Erase nat.
(*
Environment is well-formed and Ind(Coq.Init.Datatypes.nat,0,[]) has type: ⧆
*)

MetaCoq Erase I.
MetaCoq Erase true.
(*
Environment is well-formed and Construct(Coq.Init.Logic.True,0,0,[]) erases to:
⧆
Environment is well-formed and Construct(Coq.Init.Datatypes.bool,0,0,[]) erases to:
Construct(Coq.Init.Datatypes.bool,0,0)
*)

MetaCoq Erase (exist _ 0 (eq_refl 0) : {x : nat | x = 0}).
(* (* *)
(* Environment is well-formed and exist nat (fun x : nat => eq nat x O) O (eq_refl nat O):sig nat (fun x : nat => eq nat x O) erases to: *)
(* (fun f => f) (exist ∎ ∎ O ∎) *)
(* *) *)
MetaCoq Erase (3 + 1).

Universe i.
MetaCoq Erase ((fun (X : Set) (x : X) => x) nat).
(* (fun X : [Set] => fun x : X => x) nat erases to:
(FUN X => fun x => x) ∎ *)

MetaCoq EraseDebox ((fun (X : Set) (x : X -> unit) (Y : Set) (x0 : X) (Z : Type) =>
                       (x x0, x))).

(* fun X : [Set] => fun x : ∀ H : X, unit => fun Y : [Set] => fun x0 : X => fun Z : [Top.14] => pair unit (∀ H : X, unit) (x x0) x

erases to:

fun x => fun x0 => pair (x x0) x *)

MetaCoq EraseDebox (fun (A B : Type) (f : A -> B) =>
fix map (l : list A) : list B :=
  match l with
  | nil => nil
  | (a :: t)%list => (f a :: map t)%list
  end).

(* fun A : [Top.24] => fun B : [Top.25] => fun f : ∀ H : A, B => let fix map { struct 0 } : ∀ l : list A, list B :=
fun l : list A => match l as l in list return list A with
nil => nil B
 | cons a  t  => cons B (f a) (map t)
end in map

erases to:
fun f => let fix map { struct 0 } :=
fun l => match l with
nil => nil
 | cons a  t  => cons (f a) (map t)
end in map *)

(** Check that optimization of singleton pattern-matchings work *)
MetaCoq Erase ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

(* (** Check the treatment of Prop <= Type *) *)
MetaCoq Erase ((fun (X : Set) (x : X) => x) True I).
Quote Recursively Definition foo := List.map.

Require Import List.
Import ListNotations.
MetaCoq Erase (map negb [true; false]).

Definition bignat := 10000.
MetaCoq Erase bignat.

Require Import vs.
MetaCoq Erase main.
