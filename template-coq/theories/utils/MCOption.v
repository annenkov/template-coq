From Coq Require Import List ssreflect Arith.
From MetaCoq Require Import MCPrelude MCList MCProd.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Definition on_some {A} (P : A -> Type) (o : option A) :=
  match o with
  | Some t => P t
  | None => False
  end.

Definition on_Some {A} (P : A -> Prop) : option A -> Prop :=
  fun x => match x with
        | Some x => P x
        | None => False
        end.

Definition on_Some_or_None {A} (P : A -> Prop) : option A -> Prop :=
  fun x => match x with
        | Some x => P x
        | None => True
        end.

Definition option_default {A B} (f : A -> B) (o : option A) (b : B) :=
  match o with Some x => f x | None => b end.

Lemma some_inj {A} {x y : A} : Some x = Some y -> x = y.
Proof.
  now intros [=].
Qed.


Fixpoint map_option_out {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | hd :: tl => match hd, map_option_out tl with
                | Some hd, Some tl => Some (hd :: tl)
                | _, _ => None
                end
  end.

Lemma map_option_out_map_option_map {A} (l : list (option A)) (f : A -> A) :
  map_option_out (map (option_map f) l) =
  option_map (map f) (map_option_out l).
Proof.
  induction l; simpl; auto.
  destruct (option_map f a) eqn:fa.
  rewrite IHl. destruct (map_option_out l). simpl in *.
  destruct a; simpl in *; congruence.
  simpl. destruct a; reflexivity.
  destruct a; simpl in *; congruence.
Qed.

Lemma option_map_two {A B C} (f : A -> B) (g : B -> C) x
  : option_map g (option_map f x) = option_map (fun x => g (f x)) x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma option_map_ext {A B} (f g : A -> B) (H : forall x, f x = g x)
  : forall z, option_map f z = option_map g z.
Proof.
  intros []; cbn; congruence.
Qed.

Lemma nth_map_option_out {A B} (f : nat -> A -> option B) l l' i t : map_option_out (mapi f l) = Some l' ->
  nth_error l' i = Some t ->
  (∑ x, (nth_error l i = Some x) /\ (f i x = Some t)).
Proof.
  unfold mapi.
  rewrite -{3}(Nat.add_0_r i).
  generalize 0.
  induction l in i, l' |- *; intros n; simpl. intros [= <-]. rewrite nth_error_nil; discriminate.
  simpl. destruct (f n a) eqn:Heq => //.
  destruct (map_option_out (mapi_rec f l (S n))) eqn:Heq' => //.
  intros [= <-].
  destruct i; simpl. intros [= ->]. now exists a.
  specialize (IHl _ i _ Heq').
  now rewrite plus_n_Sm.
Qed.

Lemma map_option_out_length {A} (l : list (option A)) l' : map_option_out l = Some l' -> #|l| = #|l'|.
Proof.
  induction l in l' |- * => /=.
  now move=> [=] <-.
  simpl. destruct a; try discriminate.
  destruct map_option_out eqn:Heq; try discriminate.
  move=> [=] <-. by rewrite (IHl l0 eq_refl).
Qed.

Lemma option_map_Some {A B} (f : A -> B) (o : option A) x : 
  option_map f o = Some x ->
  ∑ y, (o = Some y) /\ (x = f y).
Proof.
  destruct o => /= //.
  move=> [] <-. exists a; auto.
Qed.

(** Analogous to Forall, but for the [option] type *)
(* Helpful for induction principles and predicates on [term] *)
Inductive ForOption {A} (P : A -> Prop) : option A -> Prop :=
| fo_Some : forall t, P t -> ForOption P (Some t)
| fo_None : ForOption P None.

Definition foroptb {A : Type} (p : A -> bool) (o : option A) : bool :=
  option_get true (option_map p o).

Definition foroptb2 {A : Type} (p : A -> A -> bool) (o o': option A) : bool :=
  match o, o' with
  | Some v, Some v' => p v v'
  | None, None => true
  | _, _ => false
  end.
