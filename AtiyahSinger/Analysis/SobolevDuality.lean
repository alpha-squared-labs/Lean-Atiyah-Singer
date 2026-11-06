/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.L2Sections
public import AtiyahSinger.Analysis.SobolevMaps
public import Mathlib.Analysis.InnerProductSpace.Dual

import AtiyahSinger.Analysis.SobolevEvaluationLocal
import AtiyahSinger.Analysis.SobolevMultiplication
import AtiyahSinger.Geometry.HermitianMetricDual

/-!
# The geometric pairing and opposite-order Sobolev duality

Public module ID: M0995.

A01/SR03. The pairing extends the actual integral Hermitian pairing on smooth sections.
It gives a conjugate-linear continuous equivalence H^(-s)(E) ≃ (H^s(E))' for every
real s. The first argument is conjugate-linear, in accordance with mathlib's inner
product convention. Spin Geometry III.2.8/2.15(2) uses the bilinear E–E* pairing;
a smooth Hermitian metric identifies E with its complex dual conjugate-linearly.
The two formulations are therefore equivalent after this identification, not literally
identical scalar conventions. No isometry is claimed for the chosen localized norms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothHermitianBundle (n := n) (r := r) E]
  [IsSmoothPositiveMeasure (n := n) μ]

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The geometric integral pairing is bounded for opposite Sobolev orders. -/
theorem exists_sobolev_pairing_bound (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : smoothSections (n := n) (r := r) E,
      ‖smoothSectionPairing μ E v u‖ ≤
        C * ‖A.smoothToSobolev (-s) v‖ * ‖A.smoothToSobolev s u‖ := by
  open Set in
  open scoped SchwartzMap FourierTransform ENNReal Matrix.Norms.Elementwise in
  /- Localize the actual integral with the supplied partition. The native Gram
  matrix and the positive chart density become one supported matrix multiplier.
  Opposite-order Fourier duality bounds each summand in the original norms. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  -- Each original cutoff receives a plateau within its own chart/frame overlap.
  let U (j : Fin A.size) :=
    (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.frame j).baseSet
  let K (j : Fin A.size) := (A.chart j) '' tsupport (A.cutoff j)
  have hU (j : Fin A.size) : IsOpen (U j) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage
      (A.chart j).open_target (A.frame j).open_baseSet
  have hK (j : Fin A.size) : IsCompact (K j) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  have hKU (j : Fin A.size) : K j ⊆ U j := by
    rintro _ ⟨x, hx, rfl⟩
    have hs := (A.support_subset j hx).1
    exact ⟨(A.chart j).map_source hs, by
      change (A.chart j).symm ((A.chart j) x) ∈ (A.frame j).baseSet
      rw [(A.chart j).left_inv hs]
      exact (A.support_subset j hx).2⟩
  have hplateau (j : Fin A.size) : ∃ η : X → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U j ∧
        ∀ z ∈ K j, η z = 1 := by
    obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
      exists_open_between_and_isCompact_closure (hK j) (hU j) (hKU j)
    obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo (hK j).isClosed hKO
    have hs : tsupport η = closure O := congrArg closure hsη
    refine ⟨η, hη, by simpa [HasCompactSupport, hs] using hOc, by rwa [hs], ?_⟩
    exact fun z hz ↦ (honeη z).mp hz
  choose η hη hcη hsη honeη using hplateau
  let κ (j : Fin A.size) (z : X) := η j z * A.cutoff j ((A.chart j).symm z)
  have hκ (j : Fin A.size) : ContDiff ℝ ∞ (κ j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport (η j)
    · have hzt := (hsη j hz).1
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞)
          (A.chart_mem_atlas j)) hzt
      exact (hη j).contDiffAt.mul
        ((A.smooth_cutoff j).contMDiffAt.comp z hchart).contDiffAt
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (η j)).isOpen_compl.mem_nhds hz] with y hy
      simp [κ, image_eq_zero_of_notMem_tsupport hy]
  have hsκ (j : Fin A.size) : tsupport (κ j) ⊆ K j := by
    apply closure_minimal ?_ (hK j).isClosed
    intro z hz
    have hηz : η j z ≠ 0 := left_ne_zero_of_mul (show κ j z ≠ 0 from hz)
    have hχz : A.cutoff j ((A.chart j).symm z) ≠ 0 :=
      right_ne_zero_of_mul (show κ j z ≠ 0 from hz)
    have hzt := (hsη j (subset_tsupport _ hηz)).1
    exact ⟨(A.chart j).symm z, subset_tsupport _ hχz, (A.chart j).right_inv hzt⟩
  have hcκ (j : Fin A.size) : HasCompactSupport (κ j) :=
    (hK j).of_isClosed_subset (isClosed_tsupport _) (hsκ j)
  have hκtarget (j : Fin A.size) (z : X) (hz : z ∈ (A.chart j).target) :
      κ j z = A.cutoff j ((A.chart j).symm z) := by
    by_cases hχ : A.cutoff j ((A.chart j).symm z) = 0
    · simp [κ, hχ]
    · have hzK : z ∈ K j :=
        ⟨(A.chart j).symm z, subset_tsupport _ hχ, (A.chart j).right_inv hz⟩
      simp [κ, honeη j z hzK]
  let L (j : Fin A.size) : BundleChartCutoff (r := r) E (A.chart j) :=
    { frame := A.frame j
      frame_mem_atlas := A.frame_mem_atlas j
      cutoff := κ j
      smooth_cutoff := hκ j
      compact_support := hcκ j
      support_subset := (hsκ j).trans (hKU j) }
  let B (j : Fin A.size) : BundleChartCutoff (r := r) E (A.chart j) :=
    { frame := A.frame j
      frame_mem_atlas := A.frame_mem_atlas j
      cutoff := η j
      smooth_cutoff := hη j
      compact_support := hcη j
      support_subset := hsη j }
  have hLlocal (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) :
      (L j).localize (A.chart_mem_atlas j) u = A.localize j u := by
    apply SchwartzMap.ext
    intro z
    change (if z ∈ (A.chart j).target then
      (κ j z : ℂ) • sectionInChart E (A.chart j) (A.frame j) u.val z else 0) = _
    by_cases hz : z ∈ (A.chart j).target
    · simp [SmoothBundlePresentation.localize, SmoothBundlePresentation.localizedFunction,
        hz, hκtarget j z hz]
    · simp [SmoothBundlePresentation.localize, SmoothBundlePresentation.localizedFunction, hz]
  let D (j : Fin A.size) : BundleChartCutoff (r := r) (DualBundle E) (A.chart j) :=
    { frame := by
        let := A.frame_mem_atlas j
        exact dualFrame E (A.frame j)
      frame_mem_atlas := by
        let := A.frame_mem_atlas j
        exact memTrivializationAtlas_dualFrame E (A.frame j)
      cutoff := κ j
      smooth_cutoff := hκ j
      compact_support := hcκ j
      support_subset := by
        let := A.frame_mem_atlas j
        simpa only [dualFrame_baseSet] using (hsκ j).trans (hKU j) }
  choose ρ hρ hρpos hρmap using
    (fun j : Fin A.size ↦ IsSmoothPositiveMeasure.exists_smooth_density
      (μ := μ) (A.chart j) (A.chart_mem_atlas j))
  let toOp : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (V →L[ℂ] V) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap.toLinearMap.comp
        Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
  let G (j : Fin A.size) (z : X) : V →L[ℂ] V := by
    let := A.frame_mem_atlas j
    exact toOp (h.gramMatrix (A.frame j) ((A.chart j).symm z))
  have hG (j : Fin A.size) (z : X) (hz : z ∈ U j) : ContDiffAt ℝ ∞ (G j) z := by
    let := A.frame_mem_atlas j
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞)
        (A.chart_mem_atlas j)) hz.1
    apply toOp.contDiff.contDiffAt.comp z
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro k
    exact (((h.contMDiffOn_gram (A.frame j) i k).contMDiffAt
      ((A.frame j).open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
  let W (j : Fin A.size) : X → V →L[ℂ] V :=
    cutoffMatrix (η j) (fun z ↦ ρ j z • G j z)
  have hW (j : Fin A.size) : ContDiff ℝ ∞ (W j) :=
    contDiff_cutoffMatrix (U j) (hU j) _
      (((hρ j).mono (fun _ hz ↦ hz.1)).smul
        (fun z hz ↦ (hG j z hz).contDiffWithinAt)) (η j) (hη j) (hsη j)
  have hcW (j : Fin A.size) : HasCompactSupport (W j) :=
    hasCompactSupport_cutoffMatrix (η j) _ (hcη j)
  -- Frame evaluation retains the exact native Gram convention.
  have hcoords (j : Fin A.size) (z : X) (hz : z ∈ U j)
      (v : smoothSections (n := n) (r := r) E) (w : V) :
      letI := A.frame_mem_atlas j
      (∑ i, dualSectionInFrame E (A.frame j)
        (smoothHermitianDualEquiv E v).val ((A.chart j).symm z) i * w i) =
        inner ℂ ((A.frame j) ⟨(A.chart j).symm z, v.val ((A.chart j).symm z)⟩).2
          (G j z w) := by
    let e := A.frame j
    let := A.frame_mem_atlas j
    let x := (A.chart j).symm z
    have hexpand : e.symmL ℂ x w =
        ∑ i : Fin r, w i • e.symmL ℂ x (EuclideanSpace.single i 1) := by
      have heq := congrArg (e.symmL ℂ x)
        ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr w)
      simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq.symm
    have hframe : (e ⟨x, e.symmL ℂ x w⟩).2 = w := by
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
      exact e.continuousLinearMapAt_symmL hz.2 w
    calc
      _ = inner ℂ (v.val x) (e.symmL ℂ x w) := by
        rw [hexpand, inner_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [dualSectionInFrame, smoothHermitianDualEquiv_apply, inner_smul_right,
          mul_comm, e, x]
      _ = _ := by
        have hp := h.pairing_eq_gramMatrix e x hz.2 (v.val x) (e.symmL ℂ x w)
        rw [hframe] at hp
        simp only [h, SmoothHermitianMetric.pairing_ofInnerProduct] at hp
        rw [hp]
        simp only [PiLp.inner_apply, RCLike.inner_apply]
        change (∑ i, ∑ k, conj ((e ⟨x, v.val x⟩).2 i) * h.gramMatrix e x i k * w k) =
          ∑ i, (∑ k, h.gramMatrix e x i k * w k) * conj ((e ⟨x, v.val x⟩).2 i)
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        ring
  -- The extension/localization pair reconstructs each original partition summand.
  have hpiece (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) (x : M) :
      ((L j).extend (A.chart_mem_atlas j) ((B j).localize (A.chart_mem_atlas j) u)).val x =
        (A.cutoff j x : ℂ) • u.val x := by
    let := A.frame_mem_atlas j
    change (if x ∈ (A.chart j).source then
      (κ j ((A.chart j) x) : ℂ) • (A.frame j).symmL ℂ x
        ((B j).localizedFunction u ((A.chart j) x)) else 0) = _
    by_cases hx : x ∈ (A.chart j).source
    · simp only [ite_eq_left hx, hκtarget j _ ((A.chart j).map_source hx),
        (A.chart j).left_inv hx, BundleChartCutoff.localizedFunction,
        ite_eq_left ((A.chart j).map_source hx)]
      by_cases hχ : A.cutoff j x = 0
      · simp [hχ]
      have hxK : (A.chart j) x ∈ K j := ⟨x, subset_tsupport _ hχ, rfl⟩
      have hxe := (A.support_subset j (subset_tsupport _ hχ)).2
      change (A.cutoff j x : ℂ) • (A.frame j).symmL ℂ x
        ((η j ((A.chart j) x) : ℂ) • sectionInChart E (A.chart j) (A.frame j) u.val
          ((A.chart j) x)) = _
      rw [honeη j _ hxK]
      simp only [Complex.ofReal_one, one_smul, sectionInChart]
      have hpoint : (⟨(A.chart j).symm ((A.chart j) x),
          u.val ((A.chart j).symm ((A.chart j) x))⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, u.val x⟩ :=
        congrArg (fun y ↦ (⟨y, u.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
          ((A.chart j).left_inv hx)
      rw [hpoint]
      rw [← (A.frame j).continuousLinearMapAt_apply_of_mem ℂ hxe,
        (A.frame j).symmL_continuousLinearMapAt hxe]
    · have hχ : A.cutoff j x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hxK ↦ hx (A.support_subset j hxK).1)
      simp [hx, hχ]
  have hsum (u : smoothSections (n := n) (r := r) E) :
      ∑ j, (L j).extend (A.chart_mem_atlas j) ((B j).localize (A.chart_mem_atlas j) u) = u := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply, hpiece]
    rw [← Finset.sum_smul]
    have hχ : ∑ j, (A.cutoff j x : ℂ) = 1 := by exact_mod_cast A.sum_cutoff x
    rw [hχ, one_smul]
  have hpairingSum (v u : smoothSections (n := n) (r := r) E) :
      smoothSectionPairing μ E v u = ∑ j, ∫ z,
        inner ℂ (A.localize j v z)
          (matrixMultiplierCLM (W j) (hW j) (hcW j)
            ((B j).localize (A.chart_mem_atlas j) u) z) := by
    let α := smoothHermitianDualEquiv E v
    let uj (j : Fin A.size) :=
      (L j).extend (A.chart_mem_atlas j) ((B j).localize (A.chart_mem_atlas j) u)
    rw [← smoothDualSectionPairing_hermitian E μ v u]
    calc
      _ = ∫ x, ∑ j, α.val x ((uj j).val x) ∂μ := by
        unfold smoothDualSectionPairing
        apply integral_congr_ae
        filter_upwards [] with x
        have hp := congrArg (fun w : smoothSections (n := n) (r := r) E ↦ w.val x) (hsum u)
        rw [← hp]
        simp only [Submodule.coe_sum, Finset.sum_apply, map_sum, uj, α]
      _ = ∑ j, ∫ x, α.val x ((uj j).val x) ∂μ :=
        integral_finsetSum _ (fun j _ ↦ integrable_dualSection_eval E μ α (uj j))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        have heq := (L j).integral_extendDual_eq (D j) (A.chart_mem_atlas j) rfl rfl μ (ρ j)
          (hρ j).continuousOn (fun z hz ↦ (hρpos j z hz).le) (hρmap j)
          (dualSectionsEquiv E α) ((B j).localize (A.chart_mem_atlas j) u)
        change (∫ x, α.val x ((uj j).val x) ∂μ) = _ at heq
        rw [heq]
        apply integral_congr_ae
        filter_upwards [] with z
        rw [matrixMultiplierCLM_apply]
        by_cases hz : z ∈ K j
        · have hzU := hKU j hz
          let := A.frame_mem_atlas j
          change (ρ j z : ℂ) * ∑ i,
            (D j).localizedFunction (dualSectionsEquiv E α) z i *
              (B j).localize (A.chart_mem_atlas j) u z i = _
          simp only [BundleChartCutoff.localizedFunction, ite_eq_left hzU.1]
          change (ρ j z : ℂ) * ∑ i,
            ((κ j z : ℂ) • (dualFrame E (A.frame j)
              ⟨(A.chart j).symm z, α.val ((A.chart j).symm z)⟩).2) i *
                (B j).localize (A.chart_mem_atlas j) u z i = _
          rw [dualFrame_apply_snd E (A.frame j) α.val _ hzU.2]
          change (ρ j z : ℂ) * ∑ i,
            ((κ j z : ℂ) * dualSectionInFrame E (A.frame j) α.val
              ((A.chart j).symm z) i) * (B j).localize (A.chart_mem_atlas j) u z i = _
          simp only [mul_assoc, ← Finset.mul_sum]
          rw [hcoords j z hzU v, hκtarget j z hzU.1]
          change _ = inner ℂ (A.localizedFunction j v z)
            (η j z • (ρ j z • G j z ((B j).localize (A.chart_mem_atlas j) u z)))
          rw [honeη j z hz, one_smul]
          simp [SmoothBundlePresentation.localizedFunction, hzU.1, sectionInChart,
            inner_smul_left_eq_smul, inner_smul_right_eq_smul, Algebra.smul_def]
        · have hv : A.localize j v z = 0 := image_eq_zero_of_notMem_tsupport
            (fun hz' ↦ hz (A.tsupport_localizedFunction_subset j v hz'))
          have hκz : κ j z = 0 := image_eq_zero_of_notMem_tsupport
            (fun hz' ↦ hz (hsκ j hz'))
          simp [hv, BundleChartCutoff.localize, BundleChartCutoff.localizedFunction, D, hκz]
  -- A finite sum of multiplier/localization bounds controls the two original norms.
  have hbound (j : Fin A.size) : ∃ c : ℝ, 0 ≤ c ∧ ∀ u,
      ‖schwartzSobolevCoordinate s
        (matrixMultiplierCLM (W j) (hW j) (hcW j)
          ((B j).localize (A.chart_mem_atlas j) u))‖ ≤ c * ‖A.smoothToSobolev s u‖ := by
    obtain ⟨a, ha, hba⟩ := (B j).exists_norm_localize_sobolev_le (A.chart_mem_atlas j) A s
    obtain ⟨b, hb, hbb⟩ := exists_norm_matrixMultiplier_sobolev_le (W j) (hW j) (hcW j) s
    refine ⟨b * a, mul_nonneg hb ha, fun u ↦ ?_⟩
    exact (hbb _).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hba u) hb)
  choose c hc hcb using hbound
  refine ⟨∑ j, c j, Finset.sum_nonneg (fun j _ ↦ hc j), ?_⟩
  intro u v
  rw [hpairingSum]
  calc
    _ ≤ ∑ j, ‖∫ z, inner ℂ (A.localize j v z)
        (matrixMultiplierCLM (W j) (hW j) (hcW j)
          ((B j).localize (A.chart_mem_atlas j) u) z)‖ := norm_sum_le _ _
    _ ≤ ∑ j, c j * ‖A.smoothToSobolev (-s) v‖ * ‖A.smoothToSobolev s u‖ := by
      apply Finset.sum_le_sum
      intro j _
      have hf := sobolev_pairing_schwartz (-s) (A.localize j v)
        (matrixMultiplierCLM (W j) (hW j) (hcW j)
          ((B j).localize (A.chart_mem_atlas j) u))
      simp only [neg_neg] at hf
      rw [← hf]
      have hv : ‖schwartzSobolevCoordinate (-s) (A.localize j v)‖ ≤
          ‖A.smoothToSobolev (-s) v‖ := PiLp.norm_apply_le (A.sobolevCoordinates (-s) v) j
      calc
        _ ≤ ‖schwartzSobolevCoordinate (-s) (A.localize j v)‖ *
            ‖schwartzSobolevCoordinate s
              (matrixMultiplierCLM (W j) (hW j) (hcW j)
                ((B j).localize (A.chart_mem_atlas j) u))‖ := norm_inner_le_norm _ _
        _ ≤ ‖A.smoothToSobolev (-s) v‖ * (c j * ‖A.smoothToSobolev s u‖) :=
          mul_le_mul hv (hcb j u) (norm_nonneg _) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

set_option maxHeartbeats 1000000 in
-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- SG III.2.15(2), Hermitian form: the opposite order represents exactly all continuous duals. -/
theorem existsUnique_sobolevDuality (s : ℝ) :
    ∃! T : A.SobolevSpace (-s) ≃L⋆[ℂ] StrongDual ℂ (A.SobolevSpace s),
      ∀ u v : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev (-s) v) (A.smoothToSobolev s u) =
          smoothSectionPairing μ E v u := by
  open Set in
  open scoped SchwartzMap FourierTransform ENNReal Matrix.Norms.Elementwise in
  /- Extend the actual pairing at every real order. Riesz is used only in the
  specified closed Hilbert coordinate space; inverse-density and inverse-Gram
  extension reconstructs a section representing each functional. Surjectivity
  at the opposite order and conjugate symmetry then imply injectivity. -/
  classical
  have hsurj (t : ℝ) :
      ∃ T : A.SobolevSpace (-t) →L⋆[ℂ] StrongDual ℂ (A.SobolevSpace t),
        (∀ u v : smoothSections (n := n) (r := r) E,
          T (A.smoothToSobolev (-t) v) (A.smoothToSobolev t u) =
            smoothSectionPairing μ E v u) ∧ Function.Surjective T := by
    -- Extend the original scalar pairing in each variable using its proven bound.
    obtain ⟨C, hC, hbound⟩ := A.exists_sobolev_pairing_bound μ t
    let f (v : smoothSections (n := n) (r := r) E) :
        smoothSections (n := n) (r := r) E →ₗ[ℂ] ℂ :=
      (innerSL ℂ (smoothToL2 μ E v)).toLinearMap.comp (smoothToL2 μ E)
    have hf (v u : smoothSections (n := n) (r := r) E) :
        f v u = smoothSectionPairing μ E v u := inner_smoothToL2 μ E v u
    let F (v : smoothSections (n := n) (r := r) E) : StrongDual ℂ (A.SobolevSpace t) :=
      (f v).extendOfNorm (A.smoothToSobolev t)
    have hF (v u : smoothSections (n := n) (r := r) E) :
        F v (A.smoothToSobolev t u) = smoothSectionPairing μ E v u := by
      rw [LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev t)
        ⟨C * ‖A.smoothToSobolev (-t) v‖, fun w ↦ by rw [hf]; exact hbound w v⟩, hf]
    let f₁ : smoothSections (n := n) (r := r) E →ₗ⋆[ℂ] StrongDual ℂ (A.SobolevSpace t) :=
      { toFun := F
        map_add' := by
          intro v w
          apply ContinuousLinearMap.ext
          intro u
          exact (A.denseRange_smoothToSobolev t).induction_on u
            (isClosed_eq (F (v + w)).continuous ((F v).continuous.add (F w).continuous))
            (fun z ↦ by
              simp only [add_apply, hF, smoothSectionPairing_add_left])
        map_smul' := by
          intro c v
          apply ContinuousLinearMap.ext
          intro u
          exact (A.denseRange_smoothToSobolev t).induction_on u
            (isClosed_eq (F (c • v)).continuous ((F v).continuous.const_smul (conj c)))
            (fun z ↦ by
              simp only [smul_apply, hF,
                smoothSectionPairing_smul_left, smul_eq_mul]) }
    have hf₁ (v : smoothSections (n := n) (r := r) E) :
        ‖f₁ v‖ ≤ C * ‖A.smoothToSobolev (-t) v‖ :=
      (f v).opNorm_extendOfNorm_le (A.denseRange_smoothToSobolev t)
        (mul_nonneg hC (norm_nonneg _)) (fun u ↦ by rw [hf]; exact hbound u v)
    let T : A.SobolevSpace (-t) →L⋆[ℂ] StrongDual ℂ (A.SobolevSpace t) :=
      f₁.extendOfNorm (A.smoothToSobolev (-t))
    have hT (u v : smoothSections (n := n) (r := r) E) :
        T (A.smoothToSobolev (-t) v) (A.smoothToSobolev t u) =
          smoothSectionPairing μ E v u := by
      rw [LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev (-t)) ⟨C, hf₁⟩]
      exact hF v u
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
    -- Each original cutoff receives a plateau within its own chart/frame overlap.
    let U (j : Fin A.size) :=
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.frame j).baseSet
    let K (j : Fin A.size) := (A.chart j) '' tsupport (A.cutoff j)
    have hU (j : Fin A.size) : IsOpen (U j) :=
      (A.chart j).continuousOn_symm.isOpen_inter_preimage
        (A.chart j).open_target (A.frame j).open_baseSet
    have hK (j : Fin A.size) : IsCompact (K j) :=
      (A.compact_support j).image_of_continuousOn
        ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
    have hKU (j : Fin A.size) : K j ⊆ U j := by
      rintro _ ⟨x, hx, rfl⟩
      have hs := (A.support_subset j hx).1
      exact ⟨(A.chart j).map_source hs, by
        change (A.chart j).symm ((A.chart j) x) ∈ (A.frame j).baseSet
        rw [(A.chart j).left_inv hs]
        exact (A.support_subset j hx).2⟩
    have hplateau (j : Fin A.size) : ∃ η : X → ℝ,
        ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U j ∧
          ∀ z ∈ K j, η z = 1 := by
      obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
        exists_open_between_and_isCompact_closure (hK j) (hU j) (hKU j)
      obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
        (n := (⊤ : ℕ∞)) hOo (hK j).isClosed hKO
      have hs : tsupport η = closure O := congrArg closure hsη
      refine ⟨η, hη, by simpa [HasCompactSupport, hs] using hOc, by rwa [hs], ?_⟩
      exact fun z hz ↦ (honeη z).mp hz
    choose η hη hcη hsη honeη using hplateau
    let κ (j : Fin A.size) (z : X) := η j z * A.cutoff j ((A.chart j).symm z)
    have hκ (j : Fin A.size) : ContDiff ℝ ∞ (κ j) := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z ∈ tsupport (η j)
      · have hzt := (hsη j hz).1
        have hchart := contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞)
            (A.chart_mem_atlas j)) hzt
        exact (hη j).contDiffAt.mul
          ((A.smooth_cutoff j).contMDiffAt.comp z hchart).contDiffAt
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport (η j)).isOpen_compl.mem_nhds hz] with y hy
        simp [κ, image_eq_zero_of_notMem_tsupport hy]
    have hsκ (j : Fin A.size) : tsupport (κ j) ⊆ K j := by
      apply closure_minimal ?_ (hK j).isClosed
      intro z hz
      have hηz : η j z ≠ 0 := left_ne_zero_of_mul (show κ j z ≠ 0 from hz)
      have hχz : A.cutoff j ((A.chart j).symm z) ≠ 0 :=
        right_ne_zero_of_mul (show κ j z ≠ 0 from hz)
      have hzt := (hsη j (subset_tsupport _ hηz)).1
      exact ⟨(A.chart j).symm z, subset_tsupport _ hχz, (A.chart j).right_inv hzt⟩
    have hcκ (j : Fin A.size) : HasCompactSupport (κ j) :=
      (hK j).of_isClosed_subset (isClosed_tsupport _) (hsκ j)
    have hκtarget (j : Fin A.size) (z : X) (hz : z ∈ (A.chart j).target) :
        κ j z = A.cutoff j ((A.chart j).symm z) := by
      by_cases hχ : A.cutoff j ((A.chart j).symm z) = 0
      · simp [κ, hχ]
      · have hzK : z ∈ K j :=
          ⟨(A.chart j).symm z, subset_tsupport _ hχ, (A.chart j).right_inv hz⟩
        simp [κ, honeη j z hzK]
    let L (j : Fin A.size) : BundleChartCutoff (r := r) E (A.chart j) :=
      { frame := A.frame j
        frame_mem_atlas := A.frame_mem_atlas j
        cutoff := κ j
        smooth_cutoff := hκ j
        compact_support := hcκ j
        support_subset := (hsκ j).trans (hKU j) }
    let D (j : Fin A.size) : BundleChartCutoff (r := r) (DualBundle E) (A.chart j) :=
      { frame := by
          let := A.frame_mem_atlas j
          exact dualFrame E (A.frame j)
        frame_mem_atlas := by
          let := A.frame_mem_atlas j
          exact memTrivializationAtlas_dualFrame E (A.frame j)
        cutoff := κ j
        smooth_cutoff := hκ j
        compact_support := hcκ j
        support_subset := by
          let := A.frame_mem_atlas j
          simpa only [dualFrame_baseSet] using (hsκ j).trans (hKU j) }
    choose ρ hρ hρpos hρmap using
      (fun j : Fin A.size ↦ IsSmoothPositiveMeasure.exists_smooth_density
        (μ := μ) (A.chart j) (A.chart_mem_atlas j))
    let toOp : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (V →L[ℂ] V) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (j : Fin A.size) (z : X) : V →L[ℂ] V := by
      let := A.frame_mem_atlas j
      exact toOp (h.gramMatrix (A.frame j) ((A.chart j).symm z))
    have hG (j : Fin A.size) (z : X) (hz : z ∈ U j) : ContDiffAt ℝ ∞ (G j) z := by
      let := A.frame_mem_atlas j
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞)
          (A.chart_mem_atlas j)) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro k
      exact (((h.contMDiffOn_gram (A.frame j) i k).contMDiffAt
        ((A.frame j).open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    -- Frame evaluation retains the exact native Gram convention.
    have hcoords (j : Fin A.size) (z : X) (hz : z ∈ U j)
        (v : smoothSections (n := n) (r := r) E) (w : V) :
        letI := A.frame_mem_atlas j
        (∑ i, dualSectionInFrame E (A.frame j)
          (smoothHermitianDualEquiv E v).val ((A.chart j).symm z) i * w i) =
          inner ℂ ((A.frame j) ⟨(A.chart j).symm z, v.val ((A.chart j).symm z)⟩).2
            (G j z w) := by
      let e := A.frame j
      let := A.frame_mem_atlas j
      let x := (A.chart j).symm z
      have hexpand : e.symmL ℂ x w =
          ∑ i : Fin r, w i • e.symmL ℂ x (EuclideanSpace.single i 1) := by
        have heq := congrArg (e.symmL ℂ x)
          ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr w)
        simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq.symm
      have hframe : (e ⟨x, e.symmL ℂ x w⟩).2 = w := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 w
      calc
        _ = inner ℂ (v.val x) (e.symmL ℂ x w) := by
          rw [hexpand, inner_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp [dualSectionInFrame, smoothHermitianDualEquiv_apply, inner_smul_right,
            mul_comm, e, x]
        _ = _ := by
          have hp := h.pairing_eq_gramMatrix e x hz.2 (v.val x) (e.symmL ℂ x w)
          rw [hframe] at hp
          simp only [h, SmoothHermitianMetric.pairing_ofInnerProduct] at hp
          rw [hp]
          simp only [PiLp.inner_apply, RCLike.inner_apply]
          change (∑ i, ∑ k, conj ((e ⟨x, v.val x⟩).2 i) * h.gramMatrix e x i k * w k) =
            ∑ i, (∑ k, h.gramMatrix e x i k * w k) * conj ((e ⟨x, v.val x⟩).2 i)
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          ring
    -- The actual inverse Gram matrix and density reconstruct local Fourier representatives.
    have hequiv (j : Fin A.size) (z : X) (hz : z ∈ U j) :
        ∃ Q : V ≃L[ℂ] V, Q.toContinuousLinearMap = G j z := by
      let := A.frame_mem_atlas j
      let P := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
      have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
        (h.isUnit_det_gramMatrix (A.frame j) ((A.chart j).symm z) hz.2)
      let Q := (LinearEquiv.ofBijective
        (h.gramMatrix (A.frame j) ((A.chart j).symm z)).mulVecLin
        ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
          Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
      refine ⟨P.trans (Q.trans P.symm), ?_⟩
      ext v i
      rfl
    have hGi (j : Fin A.size) : ContDiffOn ℝ ∞ (fun z ↦ (G j z).inverse) (U j) := by
      intro z hz
      obtain ⟨Q, hQ⟩ := hequiv j z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G j z) := by
        rw [← hQ]
        exact (contDiffAt_map_inverse Q).restrict_scalars ℝ
      exact (hi.comp z (hG j z hz)).contDiffWithinAt
    let R (j : Fin A.size) : X → V →L[ℂ] V :=
      cutoffMatrix (η j) (fun z ↦ (ρ j z)⁻¹ • (G j z).inverse)
    have hR (j : Fin A.size) : ContDiff ℝ ∞ (R j) :=
      contDiff_cutoffMatrix (U j) (hU j) _
        ((((hρ j).mono (fun _ hz ↦ hz.1)).inv
          (fun z hz ↦ (hρpos j z hz.1).ne')).smul (hGi j)) (η j) (hη j) (hsη j)
    have hcR (j : Fin A.size) : HasCompactSupport (R j) :=
      hasCompactSupport_cutoffMatrix (η j) _ (hcη j)
    have hcancel (j : Fin A.size) (z : X) (hz : z ∈ K j) (w : V) :
        ρ j z • G j z (R j z w) = w := by
      obtain ⟨Q, hQ⟩ := hequiv j z (hKU j hz)
      have hρz : ρ j z ≠ 0 := (hρpos j z (hKU j hz).1).ne'
      have hsmul : G j z ((ρ j z)⁻¹ • (G j z).inverse w) =
          (ρ j z)⁻¹ • G j z ((G j z).inverse w) :=
        ((G j z).restrictScalars ℝ).map_smul ((ρ j z)⁻¹) ((G j z).inverse w)
      change ρ j z • G j z (η j z • ((ρ j z)⁻¹ • (G j z).inverse w)) = w
      rw [honeη j z hz, one_smul, hsmul, smul_smul, mul_inv_cancel₀ hρz, one_smul,
        ← hQ, ContinuousLinearMap.inverse_equiv]
      exact Q.apply_symm_apply w
    have htest (j : Fin A.size) (u : smoothSections (n := n) (r := r) E)
        (v : 𝓢(X, V)) :
        smoothSectionPairing μ E u
          ((L j).extend (A.chart_mem_atlas j) (matrixMultiplierCLM (R j) (hR j) (hcR j) v)) =
          ∫ z, inner ℂ (A.localize j u z) (v z) := by
      let α := smoothHermitianDualEquiv E u
      rw [← smoothDualSectionPairing_hermitian E μ u]
      have heq := (L j).integral_extendDual_eq (D j) (A.chart_mem_atlas j) rfl rfl μ (ρ j)
        (hρ j).continuousOn (fun z hz ↦ (hρpos j z hz).le) (hρmap j)
        (dualSectionsEquiv E α) (matrixMultiplierCLM (R j) (hR j) (hcR j) v)
      change (∫ x, α.val x (((L j).extend (A.chart_mem_atlas j)
        (matrixMultiplierCLM (R j) (hR j) (hcR j) v)).val x) ∂μ) = _ at heq
      change (∫ x, α.val x (((L j).extend (A.chart_mem_atlas j)
        (matrixMultiplierCLM (R j) (hR j) (hcR j) v)).val x) ∂μ) = _
      rw [heq]
      apply integral_congr_ae
      filter_upwards [] with z
      rw [matrixMultiplierCLM_apply]
      by_cases hz : z ∈ K j
      · have hzU := hKU j hz
        let := A.frame_mem_atlas j
        change (ρ j z : ℂ) * ∑ i,
          (D j).localizedFunction (dualSectionsEquiv E α) z i * (R j z (v z)) i = _
        simp only [BundleChartCutoff.localizedFunction, ite_eq_left hzU.1]
        change (ρ j z : ℂ) * ∑ i,
          ((κ j z : ℂ) • (dualFrame E (A.frame j)
            ⟨(A.chart j).symm z, α.val ((A.chart j).symm z)⟩).2) i * (R j z (v z)) i = _
        rw [dualFrame_apply_snd E (A.frame j) α.val _ hzU.2]
        change (ρ j z : ℂ) * ∑ i,
          ((κ j z : ℂ) * dualSectionInFrame E (A.frame j) α.val
            ((A.chart j).symm z) i) * (R j z (v z)) i = _
        simp only [mul_assoc, ← Finset.mul_sum]
        rw [hcoords j z hzU u, hκtarget j z hzU.1]
        change ρ j z • (A.cutoff j ((A.chart j).symm z) •
          inner ℂ ((A.frame j) ⟨(A.chart j).symm z, u.val ((A.chart j).symm z)⟩).2
            (G j z (R j z (v z)))) = _
        rw [← inner_smul_left_eq_smul, ← inner_smul_right_eq_smul, hcancel j z hz]
        simp [SmoothBundlePresentation.localize, SmoothBundlePresentation.localizedFunction,
          hzU.1, sectionInChart]
      · have hu : A.localize j u z = 0 := image_eq_zero_of_notMem_tsupport
          (fun hz' ↦ hz (A.tsupport_localizedFunction_subset j u hz'))
        have hκz : κ j z = 0 := image_eq_zero_of_notMem_tsupport
          (fun hz' ↦ hz (hsκ j hz'))
        simp [hu, BundleChartCutoff.localize, BundleChartCutoff.localizedFunction, D, hκz]
    let Q (j : Fin A.size) : 𝓢(X, V) →ₗ[ℂ] A.SobolevSpace (-t) :=
      (A.smoothToSobolev (-t)).comp
        (((L j).extendLinearMap (A.chart_mem_atlas j)).comp
          (matrixMultiplierCLM (R j) (hR j) (hcR j)).toLinearMap)
    have hQbound (j : Fin A.size) : ∃ c : ℝ,
        ∀ v, ‖Q j v‖ ≤ c * ‖schwartzSobolevCoordinate (-t) v‖ := by
      obtain ⟨a, ha, hba⟩ := (L j).exists_norm_extend_sobolev_le (A.chart_mem_atlas j) A (-t)
      obtain ⟨b, hb, hbb⟩ := exists_norm_matrixMultiplier_sobolev_le (R j) (hR j) (hcR j) (-t)
      refine ⟨a * b, fun v ↦ ?_⟩
      exact (hba _).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hbb v) ha)
    let Q₁ (j : Fin A.size) : Lp V 2 volume →L[ℂ] A.SobolevSpace (-t) :=
      (Q j).extendOfNorm (schwartzSobolevCoordinateLinearMap n r (-t))
    have hQ₁ (j : Fin A.size) (v : 𝓢(X, V)) :
        Q₁ j (schwartzSobolevCoordinate (-t) v) = Q j v :=
      (Q j).extendOfNorm_eq (denseRange_schwartzSobolevCoordinate n r (-t)) (hQbound j) v
    let e (j : Fin A.size) : A.SobolevSpace t →L[ℂ] Lp V 2 volume :=
      (PiLp.proj 2 _ j).comp (A.sobolevCoordinates t).range.topologicalClosure.subtypeL
    have hQpair_smooth (j : Fin A.size) (v : 𝓢(X, V))
        (u : smoothSections (n := n) (r := r) E) :
        T (Q j v) (A.smoothToSobolev t u) =
          inner ℂ (schwartzSobolevCoordinate (-t) v) (e j (A.smoothToSobolev t u)) := by
      change T (A.smoothToSobolev (-t) ((L j).extend (A.chart_mem_atlas j)
        (matrixMultiplierCLM (R j) (hR j) (hcR j) v))) _ = _
      rw [hT]
      rw [← smoothSectionPairing_conj_symm μ E, htest]
      rw [← sobolev_pairing_schwartz t (A.localize j u) v]
      exact inner_conj_symm _ _
    have hQpair (j : Fin A.size) (z : Lp V 2 volume) (u : A.SobolevSpace t) :
        T (Q₁ j z) u = inner ℂ z (e j u) := by
      have hdense (v : 𝓢(X, V)) :
          T (Q₁ j (schwartzSobolevCoordinate (-t) v)) u =
            inner ℂ (schwartzSobolevCoordinate (-t) v) (e j u) := by
        rw [hQ₁]
        exact (A.denseRange_smoothToSobolev t).induction_on u
          (isClosed_eq (T (Q j v)).continuous
            (continuous_const.inner (e j).continuous)) (hQpair_smooth j v)
      exact (denseRange_schwartzSobolevCoordinate n r (-t)).induction_on z
        (isClosed_eq ((T.continuous.comp (Q₁ j).continuous).clm_apply continuous_const)
          (continuous_id.inner continuous_const)) hdense
    refine ⟨T, hT, ?_⟩
    intro f
    let y : A.SobolevSpace t := (InnerProductSpace.toDual ℂ (A.SobolevSpace t)).symm f
    refine ⟨∑ j, Q₁ j (e j y), ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    simp only [map_sum, sum_apply, hQpair]
    change (∑ j, inner ℂ (y.val j) (u.val j)) = f u
    rw [← PiLp.inner_apply]
    change inner ℂ y u = f u
    exact InnerProductSpace.toDual_symm_apply
  obtain ⟨T, hT, hTsurj⟩ := hsurj s
  have hopposite : ∃ U : A.SobolevSpace s →L⋆[ℂ] StrongDual ℂ (A.SobolevSpace (-s)),
      (∀ u v : smoothSections (n := n) (r := r) E,
        U (A.smoothToSobolev s v) (A.smoothToSobolev (-s) u) =
          smoothSectionPairing μ E v u) ∧ Function.Surjective U := by
    have htransport (a b : ℝ) (hab : -a = b) :
        ∃ U : A.SobolevSpace b →L⋆[ℂ] StrongDual ℂ (A.SobolevSpace a),
          (∀ u v : smoothSections (n := n) (r := r) E,
            U (A.smoothToSobolev b v) (A.smoothToSobolev a u) =
              smoothSectionPairing μ E v u) ∧ Function.Surjective U := by
      subst b
      exact hsurj a
    exact htransport (-s) s (neg_neg s)
  obtain ⟨U, hU, hUsurj⟩ := hopposite
  -- The two extensions are conjugate transposes because their original integrals are.
  have hsymm (v : A.SobolevSpace (-s)) (u : A.SobolevSpace s) :
      U u v = conj (T v u) := by
    have hv (w : smoothSections (n := n) (r := r) E) :
        U u (A.smoothToSobolev (-s) w) = conj (T (A.smoothToSobolev (-s) w) u) := by
      exact (A.denseRange_smoothToSobolev s).induction_on u
        (isClosed_eq (U.continuous.clm_apply continuous_const)
          (Complex.continuous_conj.comp (T (A.smoothToSobolev (-s) w)).continuous))
        (fun z ↦ by rw [hU, hT]; exact (smoothSectionPairing_conj_symm μ E z w).symm)
    exact (A.denseRange_smoothToSobolev (-s)).induction_on v
      (isClosed_eq (U u).continuous
        (Complex.continuous_conj.comp (T.continuous.clm_apply continuous_const))) hv
  have hTinj : Function.Injective T := by
    apply (injective_iff_map_eq_zero T).mpr
    intro v hv
    obtain ⟨u, hu⟩ := hUsurj (InnerProductSpace.toDual ℂ (A.SobolevSpace (-s)) v)
    have hz : inner ℂ v v = 0 := by
      change (InnerProductSpace.toDual ℂ (A.SobolevSpace (-s)) v) v = 0
      rw [← hu, hsymm, hv]
      simp
    exact inner_self_eq_zero.mp hz
  let Q : A.SobolevSpace (-s) ≃L⋆[ℂ] StrongDual ℂ (A.SobolevSpace s) :=
    ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hTinj)
      (LinearMap.range_eq_top.mpr hTsurj)
  refine ⟨Q, hT, ?_⟩
  intro S hS
  apply ContinuousLinearEquiv.ext
  funext v
  exact (A.denseRange_smoothToSobolev (-s)).induction_on v
    (isClosed_eq S.continuous Q.continuous) (fun w ↦ by
      apply ContinuousLinearMap.ext
      intro u
      exact (A.denseRange_smoothToSobolev s).induction_on u
        (isClosed_eq (S _).continuous (Q _).continuous)
        (fun z ↦ (hS z w).trans (hT z w).symm))

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The geometric duality equivalence uniquely specified by its integral values on smooth inputs. -/
def sobolevDuality (s : ℝ) :
    A.SobolevSpace (-s) ≃L⋆[ℂ] StrongDual ℂ (A.SobolevSpace s) :=
  Classical.choose (A.existsUnique_sobolevDuality μ s).exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The actual opposite-order sesquilinear pairing, evaluated through its duality map. -/
def sobolevPairing (s : ℝ) (v : A.SobolevSpace (-s)) (u : A.SobolevSpace s) : ℂ :=
  A.sobolevDuality μ s v u

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- On smooth inputs Sobolev duality gives the original geometric integral. -/
theorem sobolevPairing_smoothToSobolev (s : ℝ)
    (u v : smoothSections (n := n) (r := r) E) :
    A.sobolevPairing μ s (A.smoothToSobolev (-s) v) (A.smoothToSobolev s u) =
      smoothSectionPairing μ E v u := by
  /- Read the smooth specification of the unique geometric equivalence. -/
  exact (A.existsUnique_sobolevDuality μ s).exists.choose_spec u v

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The opposite-order pairing agrees with the actual L² inner product at order zero. -/
theorem sobolevPairing_zero (u v : A.SobolevSpace 0) :
    A.sobolevPairing μ 0 (by simpa using v) u =
      inner ℂ (A.sobolevZeroEquivL2 μ v) (A.sobolevZeroEquivL2 μ u) := by
  /- Both sides are continuous in each variable and agree on the two original
  dense smooth images. Keep the order-zero transport explicit throughout. -/
  let e (v : A.SobolevSpace 0) : A.SobolevSpace (-0) :=
    (congrArg (fun t : ℝ ↦ A.SobolevSpace t) (neg_zero : -(0 : ℝ) = 0)).mpr v
  change A.sobolevPairing μ 0 (e v) u = _
  have he : Continuous e := by
    have htransport (a b : ℝ) (hab : a = b) :
        Continuous (fun v : A.SobolevSpace b ↦
          (congrArg (fun t ↦ A.SobolevSpace t) hab).mpr v) := by
      subst b
      exact continuous_id
    exact htransport (-0) 0 neg_zero
  have he_smooth (z : smoothSections (n := n) (r := r) E) :
      e (A.smoothToSobolev 0 z) = A.smoothToSobolev (-0) z := by
    have htransport (a b : ℝ) (hab : a = b)
        (x : smoothSections (n := n) (r := r) E) :
        (congrArg (fun t ↦ A.SobolevSpace t) hab).mpr (A.smoothToSobolev b x) =
          A.smoothToSobolev a x := by
      subst b
      rfl
    exact htransport (-0) 0 neg_zero z
  refine (A.denseRange_smoothToSobolev 0).induction_on u
    (isClosed_eq (A.sobolevDuality μ 0 _).continuous
      (continuous_const.inner (A.sobolevZeroEquivL2 μ).continuous)) ?_
  intro w
  refine (A.denseRange_smoothToSobolev 0).induction_on v
    (isClosed_eq (((A.sobolevDuality μ 0).continuous.comp he).clm_apply continuous_const)
      ((A.sobolevZeroEquivL2 μ).continuous.inner continuous_const)) ?_
  intro z
  rw [he_smooth, sobolevZeroEquivL2_smoothToSobolev, sobolevZeroEquivL2_smoothToSobolev,
    inner_smoothToL2]
  exact A.sobolevPairing_smoothToSobolev μ 0 w z

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Natural Sobolev inclusions are transposes under the geometric opposite-order pairing. -/
theorem sobolevPairing_inclusion (s t : ℝ) (hst : t ≤ s)
    (v : A.SobolevSpace (-t)) (u : A.SobolevSpace s) :
    A.sobolevPairing μ s (A.sobolevInclusion (-t) (-s) (neg_le_neg hst) v) u =
      A.sobolevPairing μ t v (A.sobolevInclusion s t hst u) := by
  /- The inclusions retain the original smooth sections. Extend their common
  integral identity first in the positive-order input, then in the opposite input. -/
  change A.sobolevDuality μ s (A.sobolevInclusion (-t) (-s) (neg_le_neg hst) v) u =
    A.sobolevDuality μ t v (A.sobolevInclusion s t hst u)
  refine (A.denseRange_smoothToSobolev (-t)).induction_on v
    (isClosed_eq
      (((A.sobolevDuality μ s).continuous.comp
        (A.sobolevInclusion (-t) (-s) (neg_le_neg hst)).continuous).clm_apply continuous_const)
      ((A.sobolevDuality μ t).continuous.clm_apply continuous_const)) ?_
  intro w
  refine (A.denseRange_smoothToSobolev s).induction_on u
    (isClosed_eq (A.sobolevDuality μ s _).continuous
      ((A.sobolevDuality μ t _).continuous.comp (A.sobolevInclusion s t hst).continuous)) ?_
  intro z
  simp only [sobolevInclusion_smoothToSobolev]
  exact (A.sobolevPairing_smoothToSobolev μ s z w).trans
    (A.sobolevPairing_smoothToSobolev μ t z w).symm

end SmoothBundlePresentation

end AtiyahSinger
