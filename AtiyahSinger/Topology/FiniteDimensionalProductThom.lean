/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.TrivialCohomologyThomCup

/-!
# Product Thom isomorphism in a specified finite-dimensional vector space

Public module ID: M1852.

A specified real linear coordinate equivalence transports the original
Euclidean product Thom theorem to the original vector space. The base
parameter and coefficient ring remain arbitrary. The fiber generator is
tested on the original vector space itself, and the map is the original
pullback followed by right relative cup.

The coordinate adapter keeps the vector space in the same universe as
the base while the Euclidean model may be small; no universe restriction
is placed on the original space.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]
  {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

private def productCoordinateIso (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    relativeSingularCohomology R {z : X × EuclideanSpace ℝ (Fin n) | z.2 ≠ 0} k ≅
      relativeSingularCohomology R {z : X × V | z.2 ≠ 0} k := by
  let f := (ContinuousMap.id X).prodMap ⟨e, e.continuous⟩
  let g := (ContinuousMap.id X).prodMap ⟨e.symm, e.symm.continuous⟩
  have hf : Set.MapsTo f {z | z.2 ≠ 0} {z | z.2 ≠ 0} :=
    fun _ hz ↦ e.map_ne_zero_iff.mpr hz
  have hg : Set.MapsTo g {z | z.2 ≠ 0} {z | z.2 ≠ 0} :=
    fun _ hz ↦ e.symm.map_ne_zero_iff.mpr hz
  have hgf : g.comp f = ContinuousMap.id _ := by ext z <;> simp [f, g]
  have hfg : f.comp g = ContinuousMap.id _ := by ext z <;> simp [f, g]
  have : IsIso (relativeSingularCohomologyPullback R f hf k) :=
    isIso_relativeSingularCohomologyPullback_of_inverse R f g hf hg hgf hfg k
  exact asIso (relativeSingularCohomologyPullback R f hf k)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A specified linear coordinate model gives the original product Thom cup bijection. -/
theorem relativeSingularCohomologyAction_prod_bijective_of_linearEquiv
    (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : relativeSingularCohomology R {z : X × V | z.2 ≠ 0} n)
    (hU : ∀ x : X, Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R
        (⟨fun v : V ↦ (x, v), continuous_const.prodMk continuous_id⟩ : C(V, X × V))
        (A := {v | v ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hv ↦ hv) n U)) (p : ℕ) :
    Function.Bijective (fun a : singularCohomology R X p ↦
      relativeSingularCohomologyAction R {z : X × V | z.2 ≠ 0} p n
        (singularCohomologyPullback R (ContinuousMap.fst : C(X × V, X)) p a) U) := by
  let F := EuclideanSpace ℝ (Fin n)
  let A : Set (X × V) := {z | z.2 ≠ 0}
  let B : Set (X × F) := {z | z.2 ≠ 0}
  let f := (ContinuousMap.id X).prodMap ⟨e, e.continuous⟩
  have hf : Set.MapsTo f A B := fun _ hz ↦ e.map_ne_zero_iff.mpr hz
  let J (k : ℕ) := productCoordinateIso R X n e k
  let c := (J n).inv U
  have hc : (J n).hom c = U := Iso.inv_hom_id_apply _ _
  -- Restrict the same product coordinates to the original chosen fiber.
  have hpoint (x : X) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R
        ((ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id F))
        (A := {z | z.2 ≠ 0}) (B := B) (fun _ hz ↦ hz) n c) := by
    let l : C(PUnit.{u + 1} × F, V) :=
      ⟨fun z ↦ e.symm z.2, e.symm.continuous.comp continuous_snd⟩
    let k : C(V, PUnit.{u + 1} × F) :=
      ⟨fun v ↦ (PUnit.unit, e v), continuous_const.prodMk e.continuous⟩
    have hl : Set.MapsTo l {z | z.2 ≠ 0} {v | v ≠ 0} :=
      fun _ hz ↦ e.symm.map_ne_zero_iff.mpr hz
    have hk : Set.MapsTo k {v | v ≠ 0} {z | z.2 ≠ 0} :=
      fun _ hz ↦ e.map_ne_zero_iff.mpr hz
    have hkl : k.comp l = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro z
      exact Prod.ext (Subsingleton.elim _ _) (e.apply_symm_apply z.2)
    have hlk : l.comp k = ContinuousMap.id _ := by
      ext v
      exact e.symm_apply_apply v
    let L := relativeSingularCohomologyPullback R l hl n
    have : IsIso L := isIso_relativeSingularCohomologyPullback_of_inverse R l k hl hk hkl hlk n
    let j : C(V, X × V) := ⟨fun v ↦ (x, v), continuous_const.prodMk continuous_id⟩
    have hj : Set.MapsTo j {v | v ≠ 0} A := fun _ hz ↦ hz
    let t := (ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id F)
    have hft : f.comp (j.comp l) = t := by
      apply ContinuousMap.ext
      intro z
      exact Prod.ext rfl (e.apply_symm_apply z.2)
    have hsquare : (J n).hom ≫ relativeSingularCohomologyPullback R j hj n ≫ L =
        relativeSingularCohomologyPullback R t
          (A := {z | z.2 ≠ 0}) (B := B) (fun _ hz ↦ hz) n := by
      change relativeSingularCohomologyPullback R f hf n ≫
        relativeSingularCohomologyPullback R j hj n ≫ L = _
      dsimp only [L]
      rw [← relativeSingularCohomologyPullback_comp, ← relativeSingularCohomologyPullback_comp]
      congr 1
    have hvalue := congrArg (fun g ↦ g c) hsquare
    change L (relativeSingularCohomologyPullback R j hj n ((J n).hom c)) = _ at hvalue
    rw [hc] at hvalue
    have hgen := (ConcreteCategory.bijective_of_isIso L).comp (hU x)
    have hformula (a : R) : L (a • relativeSingularCohomologyPullback R j hj n U) =
        a • relativeSingularCohomologyPullback R t
          (A := {z | z.2 ≠ 0}) (B := B) (fun _ hz ↦ hz) n c := by
      rw [map_smul, hvalue]
    exact (congrArg Function.Bijective (funext hformula)).mp hgen
  have hb := relativeSingularCohomologyAction_prod_euclidean_bijective R X n c hpoint p
  have hcomp := (ConcreteCategory.bijective_of_isIso (J (p + n)).hom).comp hb
  -- Naturality of the actual pair pullback preserves both ordered factors of the cup.
  have hformula (a : singularCohomology R X p) :
      (J (p + n)).hom (relativeSingularCohomologyAction R B p n
        (singularCohomologyPullback R (ContinuousMap.fst : C(X × F, X)) p a) c) =
      relativeSingularCohomologyAction R A p n
        (singularCohomologyPullback R (ContinuousMap.fst : C(X × V, X)) p a) U := by
    have h := relativeSingularCohomologyPullback_action R f hf p n
      (singularCohomologyPullback R (ContinuousMap.fst : C(X × F, X)) p a) c
    have hbase : singularCohomologyPullback R f p
        (singularCohomologyPullback R (ContinuousMap.fst : C(X × F, X)) p a) =
          singularCohomologyPullback R (ContinuousMap.fst : C(X × V, X)) p a := by
      let H := singularCohomologyFunctor R p
      change (H.map (TopCat.ofHom (ContinuousMap.fst : C(X × F, X))).op ≫
        H.map (TopCat.ofHom f).op) a = _
      rw [← H.map_comp, ← op_comp]
      rfl
    change (J (p + n)).hom _ = relativeSingularCohomologyAction R A p n _ ((J n).hom c) at h
    rw [hbase, hc] at h
    exact h
  exact (congrArg Function.Bijective (funext hformula)).mp hcomp

/-- The original punctured vector-space product has no relative cohomology below its dimension. -/
theorem subsingleton_relativeSingularCohomology_prod_below_of_linearEquiv
    (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k < n) :
    Subsingleton (relativeSingularCohomology R {z : X × V | z.2 ≠ 0} k) := by
  let := subsingleton_relativeSingularCohomology_prod_euclidean_below_dim R X n k hk
  exact (ConcreteCategory.bijective_of_isIso
    (productCoordinateIso R X n e k).hom).surjective.subsingleton

end AtiyahSinger
