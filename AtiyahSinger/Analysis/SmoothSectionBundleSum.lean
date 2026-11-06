/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothBundleSumDecomposition

/-!
# Smooth sections of a specified bundle sum

Public module ID: M0977.

The original two inclusions and their inverse projections give the section
isomorphism of a native smooth sum. This retains the exact pointwise sum
coordinates for the finite-matrix PDO construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r₁ r₂ r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E₁ E₂ E : M → Type*}
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₂)) E₂)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₂)) E₂]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₂)) E₂]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Smooth sections of the specified native sum are exactly pairs of its original sections. -/
def smoothSectionSumEquiv
    (e : ∀ x, (E₁ x × E₂ x) ≃ₗ[ℂ] E x)
    (h₁ : IsSmoothBundleMap (n := n) (r := r₁) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))))
    (h₂ : IsSmoothBundleMap (n := n) (r := r₂) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x)))) :
    (smoothSections (n := n) (r := r₁) E₁ × smoothSections (n := n) (r := r₂) E₂) ≃ₗ[ℂ]
      smoothSections (n := n) (r := r) E := by
  let i₁ := smoothSectionMap
    (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))) h₁
  let i₂ := smoothSectionMap
    (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x))) h₂
  let p₁ := smoothSectionMap
    (fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
    (isSmoothBundleMap_sumInverse e h₁ h₂).1
  let p₂ := smoothSectionMap
    (fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
    (isSmoothBundleMap_sumInverse e h₁ h₂).2
  refine { (i₁.coprod i₂) with
    invFun := fun u ↦ (p₁ u, p₂ u)
    left_inv := ?_
    right_inv := ?_ }
  · -- The original inverse kills the off-diagonal inclusion and recovers each component.
    intro u
    apply Prod.ext
    · apply Subtype.ext
      funext x
      change ((e x).symm (e x (u.1.val x, 0) + e x (0, u.2.val x))).1 = u.1.val x
      rw [← map_add, (e x).symm_apply_apply]
      simp only [Prod.mk_add_mk, add_zero]
    · apply Subtype.ext
      funext x
      change ((e x).symm (e x (u.1.val x, 0) + e x (0, u.2.val x))).2 = u.2.val x
      rw [← map_add, (e x).symm_apply_apply]
      simp only [Prod.mk_add_mk, zero_add]
  · -- Recombining the two exact projections gives the initial native section.
    intro u
    apply Subtype.ext
    funext x
    change e x (((e x).symm (u.val x)).1, 0) +
      e x (0, ((e x).symm (u.val x)).2) = u.val x
    rw [← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using
      (e x).apply_symm_apply (u.val x)

/-- The native section equivalence uses the original pointwise sum map. -/
theorem smoothSectionSumEquiv_apply
    (e : ∀ x, (E₁ x × E₂ x) ≃ₗ[ℂ] E x)
    (h₁ : IsSmoothBundleMap (n := n) (r := r₁) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))))
    (h₂ : IsSmoothBundleMap (n := n) (r := r₂) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x))))
    (u : smoothSections (n := n) (r := r₁) E₁)
    (v : smoothSections (n := n) (r := r₂) E₂) (x : M) :
    (smoothSectionSumEquiv e h₁ h₂ (u, v)).val x = e x (u.val x, v.val x) := by
  change e x (u.val x, 0) + e x (0, v.val x) = _
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

end AtiyahSinger
