/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMapContinuity
public import AtiyahSinger.Geometry.SmoothBundleMapFromSections

/-!
# Recovering the specified bundle isomorphism from its section coordinates

Public module ID: M1373.

On a Hausdorff smooth manifold, when a section equivalence is given pointwise
by the specified fiber equivalences, those same fiber maps are smooth and give
an actual continuous
bundle isomorphism. The original native total-space topologies are retained.
This supplies coordinate transport for finite differential-form realizations.

Source: the local-frame criterion for smooth bundle maps, SG I.9 and III.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- Pointwise section coordinates give smoothness and a continuous iso of the same fiber maps. -/
theorem exists_smoothBundleIso_of_sectionEquiv
    (e : ∀ x, E x ≃ₗ[ℂ] F x)
    (Φ : smoothSections (n := n) (r := r) E ≃ₗ[ℂ]
      smoothSections (n := n) (r := q) F)
    (hΦ : ∀ u x, (Φ u).val x = e x (u.val x)) :
    IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (e x).toLinearMap) ∧
      (letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
       letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
       ∃ b : Iso E F, ∀ (x : M) (v : E x), b.linearEquiv x v = e x v) := by
  -- Every original smooth section is sent to the prescribed original smooth section.
  have he : IsSmoothBundleMap (n := n) (r := r) (q := q)
      (fun x ↦ (e x).toLinearMap) := by
    apply (isSmoothBundleMap_iff_map_smoothSections _).mpr
    intro u
    change IsSmoothSection (n := n) (r := q) F (fun x ↦ e x (u.val x))
    have h : (fun x ↦ e x (u.val x)) = (Φ u).val :=
      funext fun x ↦ (hΦ u x).symm
    rw [h]
    exact (Φ u).property
  -- The original local finite-rank criterion makes this very forward map an actual bundle iso.
  exact ⟨he, IsSmoothBundleMap.exists_iso e he⟩

end AtiyahSinger
