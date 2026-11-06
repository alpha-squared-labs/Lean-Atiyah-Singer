/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasCovariantSobolev
public import AtiyahSinger.Analysis.AtlasJointL2Realization
public import AtiyahSinger.Geometry.TangentConnectionExistence

/-!
# The original atlas zero-order norm and its specified metric completion

Public module ID: M0259.

For any original finite atlas presentation, the zero-order Fourier norm is
equivalent to the integral norm in the supplied native model. The same bundle
isomorphism and transported metric determine the inclusion. The geometric
zero-order energy is exactly the original metric integral, independently of
the auxiliary connections chosen to apply the existing norm comparison.
No identification with a different native atlas presentation is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- Compare both original order-zero norms through the same atlas and metric-preserving map.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- The original atlas H0 norm and the specified native integral norm bound one another. -/
theorem exists_sobolevZero_l2_comparison (A : SmoothComplexBundleAtlas (n := n) E)
    (L : AtlasBundlePresentation A) (h : ContinuousHermitianMetric E)
    (hh : A.IsSmoothHermitianMetric h) (N : SmoothFiniteComplexBundle (n := n) M)
    (k : SmoothHermitianMetric (n := n) (r := N.rank) N.Fiber)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] :
    letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
    ∀ (e : Iso E N.Fiber)
      (he : IsSmoothAtlasBundleMap A (nativeSmoothComplexBundleAtlas N.Fiber)
        e.toHom.linearMap)
      (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) A
        e.symm.toHom.linearMap),
      (∀ (x : M) (v w : E x),
        k.pairing x (e.linearEquiv x v) (e.linearEquiv x w) = (h.toCore x).inner v w) →
      let S := (atlasSmoothSectionEquiv A (nativeSmoothComplexBundleAtlas N.Fiber)
        e he hi).trans (nativeSmoothSectionLinearEquiv N.Fiber)
      let i := (k.smoothToL2 μ).comp S.toLinearMap
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ u : A.smoothSections,
        ‖L.smoothToSobolev 0 u‖ ≤ C * ‖i u‖ ∧
        ‖i u‖ ≤ D * ‖L.smoothToSobolev 0 u‖ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  intro e he hi hk S i
  -- These genuine connections only enter the existing comparison theorem; order zero ignores them.
  obtain ⟨cov⟩ := nonempty_atlasComplexConnection A
  obtain ⟨covT, hcovT⟩ := exists_smooth_tangent_connection (n := n) (M := M)
  obtain ⟨g⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
  have hnorm (u : A.smoothSections) :
      L.covariantSobolevNorm μ g h cov covT 0 u = ‖i u‖ := by
    have hzero (a : Fin L.size) (x : M)
        (hx : x ∈ (L.chart a).source ∩ (A.chart (L.frameIndex a)).baseSet) :
        cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
          (L.frameIndex a) g h 0 u x = ((h.toCore x).inner (u.val x) (u.val x)).re := by
      have hcoord :
          (A.frameLinearEquiv (L.frameIndex a) x hx.2).symm
            ((EuclideanSpace.equiv (Fin (A.rank (L.frameIndex a))) ℂ)
              (atlasSectionInChart A (L.chart a) (L.frameIndex a) u.val (L.chart a x))) =
            u.val x := by
        unfold atlasSectionInChart
        rw [(L.chart a).left_inv hx.1, ContinuousLinearEquiv.apply_symm_apply]
        exact (A.frameLinearEquiv (L.frameIndex a) x hx.2).symm_apply_apply (u.val x)
      simp only [AtlasComplexConnection.localCovariantDerivativeNormSq, dite_eq_left hx,
        AtlasComplexConnection.localIteratedCovariantDerivative, Fintype.sum_unique,
        Fin.prod_univ_zero, one_mul, hcoord]
    have henergy (x : M) :
        (∑ a : Fin L.size, L.cutoff a x *
          cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
            (L.frameIndex a) g h 0 u x) = ((h.toCore x).inner (u.val x) (u.val x)).re := by
      calc
        _ = ∑ a : Fin L.size, L.cutoff a x *
            ((h.toCore x).inner (u.val x) (u.val x)).re := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : L.cutoff a x = 0
          · simp only [ha, zero_mul]
          · rw [hzero a x (L.support_subset a (subset_tsupport (L.cutoff a) ha))]
        _ = _ := by rw [← Finset.sum_mul, L.sum_cutoff, one_mul]
    have hpair : inner ℂ (i u) (i u) =
        ∫ x, (h.toCore x).inner (u.val x) (u.val x) ∂μ := by
      change inner ℂ (k.smoothToL2 μ (S u)) (k.smoothToL2 μ (S u)) = _
      rw [k.inner_smoothToL2]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ hk x (u.val x) (u.val x)
    have hint : Integrable (fun x ↦ (h.toCore x).inner (u.val x) (u.val x)) μ :=
      (A.contMDiff_pairing h hh u u).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      L.covariantSobolevNorm μ g h cov covT 0 u =
          Real.sqrt (∫ x, ((h.toCore x).inner (u.val x) (u.val x)).re ∂μ) := by
        change Real.sqrt (∑ j : Fin 1, ∫ x,
          ∑ a : Fin L.size, L.cutoff a x *
            cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
              (L.frameIndex a) g h j.val u x ∂μ) = _
        rw [Fin.sum_univ_one]
        simp only [Fin.val_zero, henergy]
      _ = ‖i u‖ := by
        change Real.sqrt (∫ x, RCLike.re ((h.toCore x).inner (u.val x) (u.val x)) ∂μ) = _
        rw [integral_re hint, ← hpair, ← norm_sq_eq_re_inner (𝕜 := ℂ),
          Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  -- Both comparison constants were chosen before the original section.
  obtain ⟨c, C, hc, hC, hcomp⟩ :=
    L.exists_covariantSobolevNorm_comparison μ g h cov covT hcovT hh 0
  refine ⟨c⁻¹, C, inv_pos.mpr hc, hC, ?_⟩
  intro u
  have hb : c * ‖L.smoothToSobolev 0 u‖ ≤ ‖i u‖ ∧
      ‖i u‖ ≤ C * ‖L.smoothToSobolev 0 u‖ := by
    have hindex : ‖L.smoothToSobolev ((0 : ℕ) : ℝ) u‖ = ‖L.smoothToSobolev 0 u‖ :=
      congrArg (fun s : ℝ ↦ ‖L.smoothToSobolev s u‖) (Nat.cast_zero (R := ℝ))
    have hb := hcomp u
    rw [hindex, hnorm] at hb
    exact hb
  refine ⟨?_, hb.2⟩
  calc
    ‖L.smoothToSobolev 0 u‖ = c⁻¹ * (c * ‖L.smoothToSobolev 0 u‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ c⁻¹ * ‖i u‖ := mul_le_mul_of_nonneg_left hb.1 (inv_nonneg.mpr hc.le)

end AtiyahSinger.SmoothComplexBundleAtlas
