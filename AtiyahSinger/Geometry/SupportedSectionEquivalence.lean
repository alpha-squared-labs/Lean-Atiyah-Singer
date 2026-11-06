/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothBundlePullback

/-!
# Actual equivalences of supported smooth sections

Public module ID: M1468.

D01/E01/UL03: restrict a specified smooth fiber equivalence to sections supported
in K, and identify ambient supported sections with those on an open neighborhood.
Both forward and inverse maps are explicit. These are the standard section maps
used in SG III.13.4, pp.248--249; no additional kernel or index assertion is built in.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

/-- A specified smooth fiber equivalence preserves the same support constraint both ways. -/
def supportedSmoothSectionEquiv (K : Set M) (e : ∀ x, E x ≃ₗ[ℂ] F x)
    (he : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (e x).toLinearMap)) :
    supportedSmoothSections (n := n) (r := r) E K ≃ₗ[ℂ]
      supportedSmoothSections (n := n) (r := q) F K where
  toFun s := ⟨smoothSectionEquiv e he s.val, by
    intro x hx
    change e x (s.val.val x) = 0
    rw [s.property x hx]
    exact (e x).map_zero⟩
  invFun t := ⟨(smoothSectionEquiv e he).symm t.val, by
    intro x hx
    change (e x).symm (t.val.val x) = 0
    rw [t.property x hx]
    exact (e x).symm.map_zero⟩
  left_inv s := by
    apply Subtype.ext
    exact (smoothSectionEquiv e he).symm_apply_apply s.val
  right_inv t := by
    apply Subtype.ext
    exact (smoothSectionEquiv e he).apply_symm_apply t.val
  map_add' s t := by
    apply Subtype.ext
    exact (smoothSectionEquiv e he).map_add s.val t.val
  map_smul' c s := by
    apply Subtype.ext
    exact (smoothSectionEquiv e he).map_smul c s.val

open scoped Classical in
/-- Restriction and actual zero extension identify supported sections on an open neighborhood. -/
def supportedSmoothSectionRestrictionEquiv (E : M → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
    (U : Opens M) (K : Set M) (hK : IsClosed K) (hKU : K ⊆ (U : Set M)) :
    supportedSmoothSections (n := n) (r := r) E K ≃ₗ[ℂ]
      supportedSmoothSections (n := n) (r := r) (M := U)
        ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
        ((Subtype.val : U → M) ⁻¹' K) where
  toFun s := ⟨smoothSectionRestriction E U s.val, fun x hx ↦ s.property x.val hx⟩
  invFun t := ⟨smoothSectionZeroExtension E U K hK hKU t, by
    intro x hx
    change (if hxU : x ∈ U then t.val.val ⟨x, hxU⟩ else (0 : E x)) = 0
    by_cases hxU : x ∈ U
    · erw [dite_eq_left hxU]
      exact t.property ⟨x, hxU⟩ hx
    · erw [dite_eq_right hxU]⟩
  left_inv s := by
    -- Ambient-closed support supplies smoothness; here the two fiber formulas are inverse.
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (if hxU : x ∈ U then s.val.val x else (0 : E x)) = s.val.val x
    by_cases hxU : x ∈ U
    · erw [dite_eq_left hxU]
    · erw [dite_eq_right hxU]
      exact (s.property x (fun hxK ↦ hxU (hKU hxK))).symm
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change (if hxU : x.val ∈ U then t.val.val ⟨x.val, hxU⟩ else (0 : E x.val)) =
      t.val.val x
    erw [dite_eq_left x.property]
  map_add' s t := by
    apply Subtype.ext
    exact (smoothSectionRestriction E U).map_add s.val t.val
  map_smul' c s := by
    apply Subtype.ext
    exact (smoothSectionRestriction E U).map_smul c s.val

end AtiyahSinger
