/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteDimensionalProductThom
public import AtiyahSinger.Topology.HermitianProjectiveLocalCohomology

/-!
# Relative projective cup comparison with an arbitrary parameter

Public module ID: M1901.

A class supported at the specified projective point gives the relative
product Thom isomorphism whenever its image in the same affine chart is
a generator. Excision and the original product Thom theorem preserve
the arbitrary base parameter, the coefficient ring and the order of cup.
The lower-degree vanishing follows from the same affine excision map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open CategoryTheory Opposite

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]
  {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A generator in the actual affine chart gives the projective relative cup bijection. -/
theorem relativeProjectiveProdAction_bijective
    (r : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (l : (innerSL ℂ e).ker ≃L[ℝ] EuclideanSpace ℝ (Fin r))
    (τ : relativeSingularCohomology R
      {P : HermitianProjectiveSpace V InnerProductSpace.toCore | P ≠ ofVector e hne} r)
    (hτ : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (chartEmbedding e he)
        (A := {v : (innerSL ℂ e).ker | v ≠ 0})
        (B := {P | P ≠ ofVector e hne})
        (fun v hv hz ↦ hv ((chartEmbedding_eq_ofVector_iff e he hne v).mp hz)) r τ))
    (p : ℕ) :
    Function.Bijective (fun a : singularCohomology R X p ↦
      relativeSingularCohomologyAction R
        {z : X × HermitianProjectiveSpace V InnerProductSpace.toCore | z.2 ≠ ofVector e hne} p r
        (singularCohomologyPullback R (ContinuousMap.fst :
          C(X × HermitianProjectiveSpace V InnerProductSpace.toCore, X)) p a)
        (relativeSingularCohomologyPullback R (ContinuousMap.snd :
          C(X × HermitianProjectiveSpace V InnerProductSpace.toCore,
            HermitianProjectiveSpace V InnerProductSpace.toCore))
          (A := {z : X × HermitianProjectiveSpace V InnerProductSpace.toCore |
            z.2 ≠ ofVector e hne}) (B := {P | P ≠ ofVector e hne}) (fun _ hz ↦ hz) r τ)) := by
  let Q := HermitianProjectiveSpace V InnerProductSpace.toCore
  let K := (innerSL ℂ e).ker
  let B : Set Q := {P | P ≠ ofVector e hne}
  let A : Set (X × Q) := {z | z.2 ≠ ofVector e hne}
  let D : Set (X × K) := {z | z.2 ≠ 0}
  let f := (ContinuousMap.id X).prodMap (chartEmbedding e he)
  have hf : Set.MapsTo f D A :=
    fun z hz h ↦ hz ((chartEmbedding_eq_ofVector_iff e he hne z.2).mp h)
  let I (k : ℕ) := puncturedProdCohomologyIso R X e he hne k
  let T := relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Q, Q))
    (A := A) (B := B) (fun _ hz ↦ hz) r τ
  let U := (I r).hom T
  -- Fiber restriction of the same product chart is exactly the original affine embedding.
  have hpoint (x : X) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R
        (⟨fun v : K ↦ (x, v), continuous_const.prodMk continuous_id⟩ : C(K, X × K))
        (A := {v | v ≠ 0}) (B := D) (fun _ hz ↦ hz) r U) := by
    let j : C(K, X × K) := ⟨fun v ↦ (x, v), continuous_const.prodMk continuous_id⟩
    have hj : Set.MapsTo j {v : K | v ≠ 0} D := fun _ hz ↦ hz
    have hvalue : relativeSingularCohomologyPullback R j hj r U =
        relativeSingularCohomologyPullback R (chartEmbedding e he)
          (A := {v : K | v ≠ 0}) (B := B)
          (fun v hv hz ↦ hv ((chartEmbedding_eq_ofVector_iff e he hne v).mp hz)) r τ := by
      change relativeSingularCohomologyPullback R j hj r
        (relativeSingularCohomologyPullback R f hf r
          (relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Q, Q))
            (A := A) (B := B) (fun _ hz ↦ hz) r τ)) = _
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp,
        ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      rfl
    have hformula (a : R) : a • relativeSingularCohomologyPullback R j hj r U =
        a • relativeSingularCohomologyPullback R (chartEmbedding e he)
          (A := {v : K | v ≠ 0}) (B := B)
          (fun v hv hz ↦ hv ((chartEmbedding_eq_ofVector_iff e he hne v).mp hz)) r τ :=
      congrArg (fun z ↦ a • z) hvalue
    exact (congrArg Function.Bijective (funext hformula)).mpr hτ
  have hmodel := relativeSingularCohomologyAction_prod_bijective_of_linearEquiv R X r l U hpoint p
  have hformula (a : singularCohomology R X p) :
      (I (p + r)).hom (relativeSingularCohomologyAction R A p r
        (singularCohomologyPullback R (ContinuousMap.fst : C(X × Q, X)) p a) T) =
      relativeSingularCohomologyAction R D p r
        (singularCohomologyPullback R (ContinuousMap.fst : C(X × K, X)) p a) U := by
    have h := relativeSingularCohomologyPullback_action R f hf p r
      (singularCohomologyPullback R (ContinuousMap.fst : C(X × Q, X)) p a) T
    have hbase : singularCohomologyPullback R f p
        (singularCohomologyPullback R (ContinuousMap.fst : C(X × Q, X)) p a) =
        singularCohomologyPullback R (ContinuousMap.fst : C(X × K, X)) p a := by
      let F := singularCohomologyFunctor R p
      change (F.map (TopCat.ofHom (ContinuousMap.fst : C(X × Q, X))).op ≫
        F.map (TopCat.ofHom f).op) a = _
      rw [← F.map_comp, ← op_comp]
      rfl
    rw [hbase] at h
    exact h
  have hcomp : Function.Bijective ((I (p + r)).hom ∘
      fun a : singularCohomology R X p ↦ relativeSingularCohomologyAction R A p r
        (singularCohomologyPullback R ContinuousMap.fst p a) T) :=
    (congrArg Function.Bijective (funext hformula)).mpr hmodel
  exact hcomp.of_comp_left (ConcreteCategory.bijective_of_isIso (I (p + r)).hom).injective

/-- The same projective affine excision has no relative classes below the real chart dimension. -/
theorem subsingleton_relativeProjectiveProd_below_dim
    (r : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (l : (innerSL ℂ e).ker ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (k : ℕ) (hk : k < r) :
    Subsingleton (relativeSingularCohomology R
      {z : X × HermitianProjectiveSpace V InnerProductSpace.toCore | z.2 ≠ ofVector e hne} k) := by
  let := subsingleton_relativeSingularCohomology_prod_below_of_linearEquiv R X r l k hk
  exact (ConcreteCategory.bijective_of_isIso
    (puncturedProdCohomologyIso R X e he hne k).hom).injective.subsingleton

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
