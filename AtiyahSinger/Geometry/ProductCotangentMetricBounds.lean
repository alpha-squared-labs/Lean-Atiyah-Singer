/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CosphereBundle
public import AtiyahSinger.Geometry.ProductCovectorCoordinates

/-!
# Uniform metric control under the native cotangent product splitting

Public module ID: M1347.

On a compact Hausdorff product base, the sum of the two specified factor lengths controls
any specified smooth cotangent metric on the concatenated product atlas. This
allows the same finite-atlas cutoff symbol to be homogenized using the metric
of its actual global operator. No product-norm isometry is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [CompactSpace M] [T2Space N] [CompactSpace N]

set_option backward.isDefEq.respectTransparency false in
/-- The sum of the factor lengths uniformly controls the given product metric. -/
theorem exists_product_cotangent_length_le
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N)) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    ∀ h : SmoothCotangentMetric (n := n + m) (M := M × N),
      ∃ C : ℝ, 0 < C ∧ ∀ z : CotangentTotalSpace (n := n + m) (M := M × N),
        let w := cotangentProductHomeomorph (n := n) (m := m) M N z
        h.length z.proj z.snd ≤
          C * (g.length w.1.proj w.1.snd + k.length w.2.proj w.2.snd) := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  intro h
  let e := cotangentProductHomeomorph (n := n) (m := m) M N
  let f (z : CotangentTotalSpace (n := n + m) (M := M × N)) : ℝ :=
    g.length (e z).1.proj (e z).1.snd + k.length (e z).2.proj (e z).2.snd
  have hf : Continuous f :=
    (g.continuous_length.comp e.continuous.fst).add
      (k.continuous_length.comp e.continuous.snd)
  -- Splitting is fiberwise linear, so the length sum scales by the absolute scalar.
  have hfsmul (p : M × N) (ξ : CotangentFiber (n := n + m) p) (t : ℝ) :
      f ⟨p, t • ξ⟩ = |t| * f ⟨p, ξ⟩ := by
    dsimp only [f, e]
    rw [cotangentProductHomeomorph_apply, cotangentProductHomeomorph_apply]
    change g.length p.1 (t • ((ξ.comp
        EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m))))) +
      k.length p.2 (t • ((ξ.comp
        EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m))))) = _
    rw [g.length_smul, k.length_smul]
    ring
  have hfpos (z : CosphereBundle h) : 0 < f z.val := by
    have hnonneg₁ := g.length_nonneg (e z.val).1.proj (e z.val).1.snd
    have hnonneg₂ := k.length_nonneg (e z.val).2.proj (e z.val).2.snd
    by_contra hpos
    have hsum : g.length (e z.val).1.proj (e z.val).1.snd +
        k.length (e z.val).2.proj (e z.val).2.snd ≤ 0 := le_of_not_gt hpos
    have hzero₁ := (g.length_eq_zero_iff _ _).mp (by linarith :
      g.length (e z.val).1.proj (e z.val).1.snd = 0)
    have hzero₂ := (k.length_eq_zero_iff _ _).mp (by linarith :
      k.length (e z.val).2.proj (e z.val).2.snd = 0)
    have heq : e z.val = e ⟨z.val.proj, 0⟩ := by
      rw [show e = cotangentProductHomeomorph (n := n) (m := m) M N from rfl,
        cotangentProductHomeomorph_apply] at hzero₁ hzero₂ ⊢
      rw [cotangentProductHomeomorph_apply]
      dsimp only
      exact Prod.ext (congrArg (TotalSpace.mk z.val.proj.1) hzero₁)
        (congrArg (TotalSpace.mk z.val.proj.2) hzero₂)
    exact h.cosphere_ne_zero z (TotalSpace.mk_injective z.val.proj (e.injective heq))
  -- The reciprocal is bounded on the compact cosphere, even when that sphere is empty.
  let := h.compactSpace_cosphere
  have hcont : Continuous (fun z : CosphereBundle h ↦ (f z.val)⁻¹) :=
    (hf.comp continuous_subtype_val).inv₀ (fun z ↦ (hfpos z).ne')
  obtain ⟨B, hB⟩ := (isCompact_univ.image hcont).bddAbove
  let C := max B 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro z
  change h.length z.proj z.snd ≤ C * f z
  by_cases hz : z.snd = 0
  · have hfzero : f z = 0 := by
      have hzero := hfsmul z.proj z.snd 0
      change f ⟨z.proj, z.snd⟩ = 0
      simpa only [hz, smul_zero, abs_zero, zero_mul] using hzero
    rw [(h.length_eq_zero_iff _ _).mpr hz, hfzero, mul_zero]
  · let u : CosphereBundle h :=
      ⟨⟨z.proj, h.normalize z.proj z.snd⟩, h.length_normalize _ _ hz⟩
    have hbound : (f u.val)⁻¹ ≤ C :=
      (hB (Set.mem_image_of_mem _ (Set.mem_univ u))).trans (le_max_left _ _)
    have hone : 1 ≤ C * f u.val := by
      have hmul := mul_le_mul_of_nonneg_right hbound (hfpos u).le
      rwa [inv_mul_cancel₀ (hfpos u).ne'] at hmul
    -- Reconstruct the original covector from its length and normalized direction.
    have hscale : f z = h.length z.proj z.snd * f u.val := by
      have hscale := hfsmul z.proj (h.normalize z.proj z.snd)
        (h.length z.proj z.snd)
      rw [h.length_smul_normalize, abs_of_nonneg (h.length_nonneg _ _)] at hscale
      exact hscale
    rw [hscale]
    nlinarith [h.length_nonneg z.proj z.snd]

end AtiyahSinger
