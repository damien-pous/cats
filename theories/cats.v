(** * enriched categories *)

Require Export ssreflect ssrfun ssrbool.
From HB Require Export structures.
From elpi Require Import elpi coercion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Unset Universe Checking. *)

(** reserved notations *)

Reserved Notation "A ≃ B" (at level 70, format "A  ≃  B").
Reserved Notation "A ≃_ 𝐂 B" (at level 70, 𝐂 at level 0, format "A  ≃_ 𝐂  B").

Reserved Notation "a ↪ b" (at level 99, b at level 200, format "a  ↪  b").
Reserved Notation "a ↪_ C b" (at level 99, C at level 0).

Reserved Notation "a ↠ b" (at level 99, b at level 200, format "a  ↠  b").
Reserved Notation "a ↠_ C b" (at level 99, C at level 0).

Reserved Notation "a ⥲ b" (at level 99, b at level 200, format "a  ⥲  b").
Reserved Notation "a ⥲_ C b" (at level 99, C at level 0).

Reserved Notation "F ⋅ f" (at level 35, right associativity).

Reserved Notation "f ∘ g" (at level 40, left associativity).
Reserved Notation "f ∘[ C ] g" (at level 40).

Declare Scope cat_scope.
Delimit Scope cat_scope with Cat.
Local Open Scope cat_scope.


(** concrete types *)
#[primitive] HB.mixin Record IsConcrete C := {
    #[canonical=no] el : C -> Type;
  }.
#[short(type="concrete")]
HB.structure Definition Concrete := { C of IsConcrete C }.
Coercion el: Concrete.sort >-> Sortclass.
Elpi Accumulate coercion.db lp:"
coercion _ V T E R :- coq.unify-eq T {{Concrete.sort _}} ok, E = {{Type}}, !, R = {{@el _ lp:V}}.
".

(** * categories *)

(** V-quivers *)
#[primitive] HB.mixin Record IsQuiver (V: Type) C := {
    #[canonical=no] hom : C -> C -> V
  }.
#[short(type="quiver")]
HB.structure Definition Quiver V := { C of IsQuiver V C }.


Bind Scope cat_scope with quiver.
Bind Scope cat_scope with hom.
Arguments hom {_ _}.
Notation "a ~> b" := (hom a b)
   (at level 99, b at level 200, format "a  ~>  b") : cat_scope.
Notation "a ~>_ C b" := (@hom _ C a b)
  (at level 99, C at level 0, only parsing) : cat_scope.
Notation bare f := (f: hom _ _).

#[short(type="concretequiver")]
HB.structure Definition ConcreteQuiver V := { C of Quiver V C & Concrete C }.

#[primitive] HB.mixin Record HasId (V: concrete) C of Quiver V C := {
  #[canonical=no] idmap : forall {a : C}, a ~>_C a;
}.
#[short(type="prerg")]
  HB.structure Definition PreRG V := { C of HasId V C & }.
Arguments idmap {_ _ _}.
Notation "1" := idmap: cat_scope.
Notation "1_ A" := (@idmap _ _ A) (only parsing, at level 0) : cat_scope.
Bind Scope cat_scope with prerg.

(** concrete V-quivers *)
#[primitive] HB.mixin Record IsFunConcreteQuiver (V: concrete) Q of Quiver V Q & Concrete Q := {
    #[canonical=no] fn : forall A B: Q, (A ~> B) -> A -> B;
  }.
#[short(type="funconcretequiver")]
HB.structure Definition FunConcreteQuiver V :=
  { C of IsFunConcreteQuiver V C & Quiver V C & Concrete C }.
Arguments fn {_ _ _ _}.
Coercion fn: el >-> Funclass.

(** concrete V-quivers *)
#[primitive] HB.mixin Record IsRelConcreteQuiver (V: concrete) Q of Quiver V Q & Concrete Q := {
    #[canonical=no] rl : forall A B: Q, (A ~> B) -> A -> B -> Type;
  }.
#[short(type="relconcretequiver")]
HB.structure Definition RelConcreteQuiver V :=
   { C of IsRelConcreteQuiver V C & Quiver V C & Concrete C }.
Arguments rl {_ _ _ _}.

#[short(type="t10concretequiver")]
HB.structure Definition T10ConcreteQuiver V :=
   { C of RelConcreteQuiver V C & FunConcreteQuiver V C & Quiver V C & Concrete C }.

#[short(type="concreteprerg")]
HB.structure Definition ConcretePreRG V :=
   { C of PreRG V C & ConcreteQuiver V C }.

#[short(type="relconcreteprerg")]
HB.structure Definition RelConcretePreRG V :=
   { C of PreRG V C & RelConcreteQuiver V C }.

#[short(type="funconcreteprerg")]
HB.structure Definition FunConcretePreRG V :=
   { C of PreRG V C & FunConcreteQuiver V C }.

#[short(type="t10concreteprerg")]
HB.structure Definition T10ConcretePreRG V :=
   { C of PreRG V C & T10ConcreteQuiver V C }.

HB.instance Definition _ V (C : @relconcreteprerg V) (a : C) :=
  IsQuiver.Build Type (el a) (fun f g : a => rl 1_a f g).


(* HB.instance Definition _ V := IsConcrete.Build (quiver V) (@Quiver.sort V). *)

(* HB.instance Definition _ := IsConcrete.Build Type id. *)

(* Definition elts (Q: Type) := Q. *)

(* HB.instance Definition _ V (Q: funconcretequiver V) := *)
(*   IsQuiver.Build Type (elts Q) (fun x y: Q => x ~> y). *)

(** premonoidal V-quivers *)
#[primitive] HB.mixin Record IsPreMonoidal T := {
    (* #[canonical=no] unit : T; *)
    #[canonical=no] tensor : T -> T -> T;
  }.

#[short(type="premonoidal")]
HB.structure Definition PreMonoidal := { C of IsPreMonoidal C }.
Notation "X ⊗ Y" := (tensor X Y) (at level 29): cat_scope.

#[short(type="premonoidalquiver")]
  HB.structure Definition PreMonoidalQuiver V :=
  { C of PreMonoidal C & Quiver V C }.

(** concrete premonoidal V-quivers *)
#[primitive] HB.mixin Record IsConcretePreMonoidal T of PreMonoidal T & Concrete T := {
    (* #[canonical=no] el_unit : @unit T; *)
    #[canonical=no] el_tensor : forall {A B: T}, A -> B -> A ⊗ B;
  }.

#[short(type="concretepremonoidalquiver")]
  HB.structure Definition ConcretePreMonoidalQuiver V :=
  { C of IsConcretePreMonoidal C & ConcreteQuiver V C & PreMonoidalQuiver V C }.
Arguments el_tensor {_ _ _ _}.

#[short(type="funconcretepremonoidalquiver")]
  HB.structure Definition FunConcretePreMonoidalQuiver V :=
  { C of IsConcretePreMonoidal C & FunConcreteQuiver V C & PreMonoidalQuiver V C }.

#[short(type="relconcretepremonoidalquiver")]
  HB.structure Definition RelConcretePreMonoidalQuiver V :=
  { C of IsConcretePreMonoidal C & RelConcreteQuiver V C & PreMonoidalQuiver V C }.

#[short(type="t10concretepremonoidalquiver")]
  HB.structure Definition T10ConcretePreMonoidalQuiver V :=
  { C of IsConcretePreMonoidal C & T10ConcreteQuiver V C & PreMonoidalQuiver V C }.

#[short(type="concretepremonoidalprerg")]
  HB.structure Definition ConcretePreMonoidalPreRG V :=
  { C of IsConcretePreMonoidal C & ConcretePreRG V C & PreMonoidalQuiver V C }.

#[short(type="funconcretepremonoidalprerg")]
  HB.structure Definition FunConcretePreMonoidalPreRG V :=
  { C of IsConcretePreMonoidal C & FunConcretePreRG V C & PreMonoidalQuiver V C }.

#[short(type="relconcretepremonoidalprerg")]
  HB.structure Definition RelConcretePreMonoidalPreRG V :=
  { C of IsConcretePreMonoidal C & RelConcretePreRG V C & PreMonoidalQuiver V C }.

#[short(type="t10concretepremonoidalprerg")]
  HB.structure Definition T10ConcretePreMonoidalPreRG V :=
  { C of IsConcretePreMonoidal C & T10ConcretePreRG V C & PreMonoidalQuiver V C }.

(** precategories: quivers + id and comp *)
#[primitive] HB.mixin Record HasComp
  (W: concrete) (V: concretepremonoidalquiver W) C of Quiver V C := {
  #[canonical=no] comp_ : forall {a b c : C}, (b ~>_C c) ⊗ (a ~>_C b) ~>_V (a ~>_C c);
}.
#[short(type="precat")]
  HB.structure Definition PreCat W V := { C of HasComp W V C & HasId V C }.
Arguments comp_ {_ _ _ _ _ _}.
Bind Scope cat_scope with precat.

(** precategories: quivers + id and comp *)
#[primitive] HB.factory Record IsPreCat
  (W: concrete) (V: concretepremonoidalquiver W) C of Quiver V C := {
  #[canonical=no] comp_ : forall {a b c : C}, (b ~>_C c) ⊗ (a ~>_C b) ~>_V (a ~>_C c);
  #[canonical=no] idmap : forall {a : C}, a ~>_C a;
}.
HB.builders Context W V C of IsPreCat W V C.
  HB.instance Definition _ := HasId.Build V C idmap.
  HB.instance Definition _ := HasComp.Build W V C comp_.
HB.end.

#[short(type="concreteprecat")]
HB.structure Definition ConcretePreCat W V := {C of Concrete C & @IsPreCat W V C}.
#[short(type="relconcreteprecat")]
HB.structure Definition RelConcretePreCat W V :=
   {C of @ConcretePreCat W V C & @RelConcreteQuiver V C}.

#[primitive] HB.mixin Record HasInv
  (W: concrete) (V: quiver W) C of Quiver V C := {
  #[canonical=no] inv : forall {a b : C}, (a ~>_C b) ~>_V (b ~>_C a);
}.
#[short(type="setoid")]
  HB.structure Definition Setoid W V := { C of IsPreCat W V C & HasInv W V C }.
Arguments inv {_ _ _ _ _}.
Notation "f '⁻¹'" := (inv f) (at level 9, format "f '⁻¹'"): cat_scope.
Bind Scope cat_scope with setoid.


Definition comp {W: concrete} {V: funconcretepremonoidalquiver W} {C: precat V}
    {a b c: C} (g: b ~> c) (f: a ~> b): a ~> c :=
  comp_ (el_tensor g f).
Definition is_comp {W: concrete} {V: relconcretepremonoidalquiver W} {C: precat V}
    {a b c: C} (g: b ~> c) (f: a ~> b) (h: a ~> c): Type :=
  rl comp_ (el_tensor g f) h.

Notation "g ∘ f" := (comp g f) : cat_scope.
Notation "g ∘[ C ] f" := (@comp _ _ C _ _ _ g f) (only parsing): cat_scope.

(** prefunctor: a functor without laws *)
HB.mixin Record IsPreFunctor (W: concrete) (V: concretequiver W)
  (C D: quiver V) (F : C -> D) := {
    #[canonical=no] Fhom : forall (a b : C), (a ~> b) ~>_V (F a ~> F b)
  }.
#[short(type="prefunctor")]
HB.structure Definition PreFunctor (W: concrete) (V: concretequiver W) (C D : quiver V) :=
  { F of IsPreFunctor W V C D F }.
Arguments Fhom {_ _ _ _} _ {_ _}.
Notation "F ⋅ f" := (@Fhom _ _ _ _ F _ _ f) : cat_scope.

(* Check fun W (V: funconcretepremonoidalquiver W) (C D : precat V) => *)
(*         fun (a: D) (f: a ~> a) => Quiver.sort (elts D). *)

(** functor: prefunctor + laws *)
HB.mixin Record PreFunctor_IsFunctor
  W (V: t10concretepremonoidalprerg W) (C D: precat V)
  F of @PreFunctor W V C D F := {
    #[canonical=no] F1 : forall (a : C),
      (F ⋅ 1_a) ~> 1_(F a);
    #[canonical=no] Fcomp : forall (a b c : C) (g : b ~> c) (f : a ~> b),
      (F ⋅ (g ∘ f)) ~> (F⋅g ∘ F⋅f);
}.
#[short(type="Functor")]
HB.structure Definition functor W (V: t10concretepremonoidalprerg W) (C D : precat V) :=
  { F of PreFunctor_IsFunctor W V C D F & }.

(** categories: precategories + laws *)
HB.mixin Record IsCat (W: concrete) (V: t10concretepremonoidalprerg W) C of PreCat W V C := {
  #[canonical=no] comp1o : forall (a b : C) (f : a ~> b), 1 ∘ f ~> f;
  #[canonical=no] compo1 : forall (a b : C) (f : a ~> b), f ∘ 1 ~> f;
  #[canonical=no] compoA : forall (a b c d : C) (h : c ~> d) (g : b ~> c) (f : a ~> b), h ∘ (g ∘ f) ~> (h ∘ g) ∘ f;
}.
#[short(type="cat")]
HB.structure Definition Cat W V := { C of @IsCat W V C & }.
Bind Scope cat_scope with cat.
Arguments compo1 {_ _ _ _ _}.
Arguments comp1o {_ _ _ _ _}.
Arguments compoA {_ _ _ _ _ _ _}.

(** groupoids: setoid + laws *)
HB.mixin Record InverseLaws (W: concrete) (V: t10concretepremonoidalprerg W) C of Setoid W V C := {
  #[canonical=no] compVo : forall (a b : C) (f : a ~> b), f⁻¹ ∘ f ~> 1;
  #[canonical=no] compoV : forall (a b : C) (f : a ~> b), f ∘ f⁻¹ ~> 1;
}.
#[short(type="groupoid")]
HB.structure Definition Groupoid W V := { C of IsCat W V C & InverseLaws W V C }.
Bind Scope cat_scope with Groupoid.
Arguments compVo {_ _ _ _ _}.
Arguments compoV {_ _ _ _ _}.

Definition TypeFun := Type.
Definition TypeRel := Type.
Definition TypeEq := Type.

(* General structures on Type *)
HB.instance Definition _ := IsConcrete.Build Type (fun T => T).
HB.instance Definition _ := IsQuiver.Build Type TypeFun (fun A B => A -> B).
HB.instance Definition _ := IsQuiver.Build Type TypeRel (fun A B => A -> B -> Type).
HB.instance Definition _ := IsQuiver.Build Type TypeEq (fun A B => A = B).
HB.instance Definition _ := IsPreMonoidal.Build Type (fun A B => A * B)%type.

(* TypeFun specific structures *)
HB.instance Definition _ := Concrete.on TypeFun.
HB.instance Definition _ := PreMonoidal.on TypeFun.
HB.instance Definition _ := IsConcretePreMonoidal.Build TypeFun (fun A B a b => (a, b)).
HB.instance Definition _ := HasId.Build Type TypeFun (fun A a => a).
HB.instance Definition _ := IsFunConcreteQuiver.Build Type TypeFun (fun A B f => f).
HB.instance Definition _ := IsRelConcreteQuiver.Build Type TypeFun (fun A B f x y => f x = y).

(* TypeRel specific structures *)
HB.instance Definition _ := Concrete.on TypeRel.
HB.instance Definition _ := PreMonoidal.on TypeRel.

(* TypeEq specific structures *)
HB.instance Definition _ := Concrete.on TypeEq.
HB.instance Definition _ := PreMonoidal.on TypeEq.

(* HB.instance Definition _ := IsFunConcreteQuiver.Build Type *)
(*    (fun A B (e : A ~> B) => eq_rect Type (fun T : Type => T) A B e). *)
Definition strictcat := cat TypeFun.

Lemma test (C : strictcat) (a b : C) (f g : el (a ~> b)) (e : f ~> g) : False.
cbn in e.


STOP.

(* CONTINUE FROM HERE *)

(** duality: opposite category *)
Definition catop (C : Type) : Type := C.
Notation "C ^op" := (catop C) (at level 2, format "C ^op") : cat_scope.
HB.instance Definition _ (C : Quiver) :=
  IsQuiver.Build C^op (fun a b => hom b a).
HB.instance Definition _ (C : PreCat) :=
  IsPreCat.Build (C^op) (fun=> idmap) (fun _ _ _ f g => g \; f).
HB.instance Definition _ (C : Cat) := IsCat.Build (C^op)
  (fun _ _ => compo1) (fun _ _ => comp1o) (fun _ _ _ _ _ _ _ => eqv_sym (compoA _ _ _))
  (fun _ _ _ _ _ H _ _ H' => compoE _ _ H' _ _ H).
Definition morphop {C: Quiver} [x y: C] (f: x ~> y): y ~>_(C^op) x := f.

(** full sub-categories: from functions into categories *)
HB.instance Definition _ A (C : Quiver) (f: A -> C) :=
  IsQuiver.Build (kernel f) (fun a b => f a ~>_C f b).
HB.instance Definition _ A (C : PreCat) (f: A -> C) :=
  IsPreCat.Build (kernel f) (fun a=> \idmap (f a)) (fun a b c => @comp C (f a) (f b) (f c)).
HB.instance Definition _ A (C : Cat) (f: A -> C) :=
  IsCat.Build (kernel f)
    (fun a b => @comp1o C (f a) (f b))
    (fun a b => @compo1 C (f a) (f b))
    (fun a b c d => @compoA C (f a) (f b) (f c) (f d))
%    (fun a b c => @compoE C (f a) (f b) (f c)).

(* the category of setoids and extensional functions *)
(* commented out for now: needs Setoid.type to be universe polymorphic, which is not supported by HB *)
(*
HB.instance Definition _ := @IsPreCat.Build Setoid.type (fun A B => A -eqv-> B)
  (fun a => setoid_id) (fun a b c f g => setoid_comp g f).
Program Definition _setoid_cat := PreCat_IsCat.Build Setoid.type _ _ _ _.
Next Obligation. move=>??????. exact: setoid_comp_eqv. Qed.
HB.instance Definition _ := _setoid_cat.
*)

(** * subcategories *)


(** full subcategories: with sig types *)
HB.instance Definition _ (𝐂: Quiver) (fsobj: 𝐂 -> Prop) :=
  quiver.copy (sig fsobj) (kernel sval).
HB.instance Definition _ (𝐂: PreCat) (fsobj: 𝐂 -> Prop) :=
  precat.copy (sig fsobj) (kernel sval).
HB.instance Definition _ (𝐂: Cat) (fsobj: 𝐂 -> Prop) :=
  cat.copy (sig fsobj) (kernel sval).

(** full subcategories: with sigT types
    we tag those instances explicitly since they are generally not the right ones
    (the morphisms do not preserve the additional structure)
 *)
Definition sigT_cat A P := @sigT A P.
HB.instance Definition _ (𝐂: Quiver) (fsobj: 𝐂 -> Type) :=
  quiver.copy (sigT_cat fsobj) (kernel (@projT1 _ fsobj)).
HB.instance Definition _ (𝐂: PreCat) (fsobj: 𝐂 -> Type) :=
  precat.copy (sigT_cat fsobj) (kernel (@projT1 _ fsobj)).
HB.instance Definition _ (𝐂: Cat) (fsobj: 𝐂 -> Type) :=
  cat.copy (sigT_cat fsobj) (kernel (@projT1 _ fsobj)).

(** ** wide subcategories *)

(** wide sub categories: from functors into categories *)
Record WSub (C: PreCat) := {
    wshom: C -> C -> Type;
    wsU: forall {a b}, wshom a b -> a ~>_C b;
    wsid: forall a, wshom a a;
    wscomp: forall {a b c}, wshom a b -> wshom b c -> wshom a c;
    wsUid: forall a, wsU (wsid a) ≡ idmap;
    wsUcomp: forall a b c f g , wsU (@wscomp a b c f g) ≡ wsU f \; wsU g;
  }.
Definition wsub (C: PreCat) (P: WSub C): Type := C.
HB.instance Definition _ C (P: WSub C) a b
  := Setoid.copy (wshom P a b) (kernel (@wsU _ P a b)).
HB.instance Definition _ C (P: WSub C)
  := IsQuiver.Build (wsub P) (@wshom _ P).
HB.instance Definition _ C (P: WSub C)
  := IsPreCat.Build (wsub P) (@wsid _ P) (@wscomp _ P).
Lemma _wsub_cat (C: Cat) (P: WSub C): IsCat (wsub P).
Proof.
  split; repeat intro; cbn; rewrite /=!wsUcomp.
  - rewrite wsUid. exact: comp1o.
  - rewrite wsUid. exact: compo1.
  - exact: compoA.
  - by apply: compoE.
Qed.
HB.instance Definition _ (C: Cat) (P: WSub C) := _wsub_cat P.


(** ** general subcategories *)

Definition Sub {𝐂: PreCat} (sobj: 𝐂 -> Prop) (wshom: WSub (sig sobj)) := wsub wshom.


(** * unique existence of morphisms *)

Section s.
Context {𝐂: Quiver} [A B: 𝐂] (P : (A ~> B) → Type).

Definition Unique_morph := Unique P.

Lemma Unicity: Unique_morph -> forall (u v: A ~> B), P u -> P v -> u ≡ v.
Proof.
  intros [w _ U] u v Pu Pv.
  by rewrite -(U _ Pu) (U _ Pv).
Qed.

Definition unique_morph: Unique P -> A ~> B := unique_elt.

End s.
Arguments unique_morph {_ _ _ _}.
Arguments Unicity {_ _ _ _}.

Notation "∃! x .. y , P" := (Unique_morph (fun x => .. (Unique_morph (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : cat_scope.

Lemma unique_morph_eqv {𝐂: Quiver} [A B: 𝐂] (P Q: (A ~> B) → Type):
  (forall f, P f -> Q f) -> forall p: Unique_morph P, forall q: Unique_morph Q, unique_morph p ≡ unique_morph q.
Proof.
  move=>PQ p q. apply: Unicity. eassumption.
  apply: PQ. all: exact: unique_prop.
Qed.

Instance Unique_morph_iff {𝐂: Quiver} [A B: 𝐂]:
  CMorphisms.Proper (pointwise_crelation iffT ==> iffT) (@Unique_morph _ A B).
Proof.
  move=> P Q PQ. split; move=>[f Hf Uf]; exists f; (try by apply PQ);
  move=>g Hg; apply Uf; by apply PQ.
Qed.

(** unique existence in full subcategories *)
Lemma Unique_Full_eq {𝐂: Quiver} (P: 𝐂 -> Prop) (x y: 𝐂) (Px: P x) (Py: P y)
  (Q: (x ~> y) -> Type):
  (∃! a: (exist _ x Px) ~>_(sig P) (exist _ y Py), Q a) ↔
  ∃! a: x ~> y, Q a.
Proof.
  split.
    intros a.
    exists (unique_morph a).
      apply ('a).
    apply (''a).
  intros a.
  exists (unique_morph a).
    apply ('a).
  apply (''a).
Qed.

(** ad-hoc promotion tactic *)
Tactic Notation "promote" hyp(f) "with" uconstr(t) "in" hyp_list(H) "/" hyp_list(H') :=
  let f_old := fresh f in
  rename f into f_old;
  pose f := t;
  change (bare f_old) with (bare f) in H |- *;
  try clearbody f; clear f_old H'.
