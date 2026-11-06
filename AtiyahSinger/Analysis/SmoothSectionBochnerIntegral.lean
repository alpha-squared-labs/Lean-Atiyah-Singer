/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CkSections
public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Geometry.ComplexConnection

/-!
# Identifying actual section integrals in Sobolev and metric completions

Public module ID: M0976.

Point evaluation is bounded on the original finite-order section spaces. A
Bochner-integrable family in Sobolev order above the continuous embedding
threshold therefore retains its actual fiber integrals. The same identity passes
through the original Sobolev inclusion and metric L2 equivalence. No pointwise
evaluation on an L2 equivalence class is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped ContDiff Manifold Topology

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- Evaluation on actual finite-order sections is a bounded map into the specified fiber. -/
theorem exists_ck_evaluation (k : ℕ) (x : M) :
    ∃ T : A.CkSectionSpace k →L[ℂ] E x, ∀ u : A.CkSectionSpace k, T u = u.val x := by
  classical
  -- One nonzero original partition weight recovers the fiber from a bounded coordinate value.
  have hchoose : ∃ j : Fin A.size, A.cutoff j x ≠ 0 := by
    by_contra! h
    have hsum := A.sum_cutoff x
    simp only [h, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨j, hj⟩ := hchoose
  have hx := A.support_subset j (subset_tsupport _ hj)
  let := A.frame_mem_atlas j
  let ev : A.CkSectionSpace k →ₗ[ℂ] EuclideanSpace ℂ (Fin r) :=
    { toFun := fun w ↦ (A.cutoff j x : ℂ) •
        ((A.frame j).linearEquivAt ℂ x hx.2) (w.val x)
      map_add' := by
        intro v w
        change (A.cutoff j x : ℂ) •
          ((A.frame j).linearEquivAt ℂ x hx.2) (v.val x + w.val x) = _
        rw [map_add, smul_add]
      map_smul' := by
        intro c w
        change (A.cutoff j x : ℂ) •
          ((A.frame j).linearEquivAt ℂ x hx.2) (c • w.val x) = _
        rw [map_smul, smul_comm]
        rfl }
  have heval (w : A.CkSectionSpace k) :
      ev w = A.localizedCkFunction k j w (A.chart j x) := by
    have hpair : (⟨(A.chart j).symm (A.chart j x),
        w.val ((A.chart j).symm (A.chart j x))⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, w.val x⟩ :=
      congrArg (fun y ↦ (⟨y, w.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
        ((A.chart j).left_inv hx.1)
    simp only [localizedCkFunction, ite_eq_left ((A.chart j).map_source hx.1),
      sectionInChart, hpair, (A.chart j).left_inv hx.1]
    rfl
  have hbound (w : A.CkSectionSpace k) : ‖ev w‖ ≤ 1 * ‖w‖ := by
    rw [one_mul, heval]
    change ‖A.localizedCkFunction k j w (A.chart j x)‖ ≤ A.ckNorm k w
    have h := le_csSup (A.bddAbove_ckNorm_values k w)
      (show ‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j w) (A.chart j x)‖ ∈
        {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k ∧
          ∃ z : EuclideanSpace ℝ (Fin n),
            a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j w) z‖} from
          ⟨j, 0, Nat.zero_le k, A.chart j x, rfl⟩)
    change ‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j w) (A.chart j x)‖ ≤
      A.ckNorm k w at h
    simpa only [norm_iteratedFDeriv_zero] using h
  let e := (A.frame j).continuousLinearEquivAt ℂ x hx.2
  let T : A.CkSectionSpace k →L[ℂ] E x :=
    e.symm.toContinuousLinearMap.comp
      (((A.cutoff j x : ℂ)⁻¹ • ContinuousLinearMap.id ℂ
        (EuclideanSpace ℂ (Fin r))).comp (ev.mkContinuous 1 hbound))
  have hχ : (A.cutoff j x : ℂ) ≠ 0 := by exact_mod_cast hj
  refine ⟨T, ?_⟩
  intro w
  change e.symm ((A.cutoff j x : ℂ)⁻¹ • ((A.cutoff j x : ℂ) • e (w.val x))) = _
  rw [smul_smul, inv_mul_cancel₀ hχ, one_smul, e.symm_apply_apply]

/-- Above the continuous Sobolev threshold, a specified fiber integral identifies the
Bochner integral in the original Sobolev completion. -/
theorem smoothToSobolev_eq_integral_of_pointwise {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (s : ℝ) (hs : (n : ℝ) / 2 < s)
    (f : Y → smoothSections (n := n) (r := r) E)
    (hf : Integrable (fun y ↦ A.smoothToSobolev s (f y)) ν)
    (u : smoothSections (n := n) (r := r) E)
    (hpoint : ∀ x : M, u.val x = ∫ y, (f y).val x ∂ν) :
    A.smoothToSobolev s u = ∫ y, A.smoothToSobolev s (f y) ∂ν := by
  have hs₀ : (n : ℝ) / 2 + (0 : ℕ) < s := by simpa only [Nat.cast_zero, add_zero] using hs
  apply A.sobolevToCk_injective 0 s hs₀
  rw [A.sobolevToCk_smoothToSobolev]
  apply Subtype.ext
  funext x
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  obtain ⟨ev, hev⟩ := A.exists_ck_evaluation 0 x
  let T := ev.comp (A.sobolevToCk 0 s hs₀)
  have hT (v : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s v) = v.val x := by
    change ev (A.sobolevToCk 0 s hs₀ (A.smoothToSobolev s v)) = _
    rw [A.sobolevToCk_smoothToSobolev, hev]
    rfl
  change u.val x = (A.sobolevToCk 0 s hs₀ (∫ y, A.smoothToSobolev s (f y) ∂ν)).val x
  calc
    _ = ∫ y, (f y).val x ∂ν := hpoint x
    _ = ∫ y, T (A.smoothToSobolev s (f y)) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y ↦ (hT (f y)).symm)
    _ = T (∫ y, A.smoothToSobolev s (f y) ∂ν) := T.integral_comp_comm hf
    _ = _ := hev _

end SmoothBundlePresentation

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- The same high-order section integral is the original metric L2 Bochner integral. -/
theorem SmoothHermitianMetric.integrable_and_smoothToL2_eq_integral_of_pointwise
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (s : ℝ) (hs : (n : ℝ) / 2 < s)
    (f : Y → smoothSections (n := n) (r := r) E)
    (hf : Integrable (fun y ↦ A.smoothToSobolev s (f y)) ν)
    (u : smoothSections (n := n) (r := r) E)
    (hpoint : ∀ x : M, u.val x = ∫ y, (f y).val x ∂ν) :
    Integrable (fun y ↦ h.smoothToL2 μ (f y)) ν ∧
      h.smoothToL2 μ u = ∫ y, h.smoothToL2 μ (f y) ∂ν := by
  have hs₀ : 0 ≤ s := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let T := (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
    (A.sobolevInclusion s 0 hs₀)
  have hT (v : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s v) = h.smoothToL2 μ v := by
    change h.sobolevZeroEquivL2 (μ := μ) A
      (A.sobolevInclusion s 0 hs₀ (A.smoothToSobolev s v)) = _
    rw [A.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth]
  have heq : (fun y ↦ T (A.smoothToSobolev s (f y))) =ᵐ[ν]
      (fun y ↦ h.smoothToL2 μ (f y)) := Filter.Eventually.of_forall (fun y ↦ hT (f y))
  refine ⟨(T.integrable_comp hf).congr heq, ?_⟩
  calc
    _ = T (A.smoothToSobolev s u) := (hT u).symm
    _ = T (∫ y, A.smoothToSobolev s (f y) ∂ν) :=
      congrArg T (A.smoothToSobolev_eq_integral_of_pointwise ν s hs f hf u hpoint)
    _ = ∫ y, T (A.smoothToSobolev s (f y)) ∂ν := (T.integral_comp_comm hf).symm
    _ = _ := integral_congr_ae heq

end AtiyahSinger
