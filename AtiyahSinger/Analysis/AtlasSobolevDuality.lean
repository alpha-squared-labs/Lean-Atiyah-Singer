/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSobolev
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.Analysis.InnerProductSpace.Dual

import AtiyahSinger.Analysis.AtlasHermitianLocalization
import AtiyahSinger.Analysis.SobolevMultiplication

/-!
# Geometric Sobolev duality for locally varying-rank bundles

Public module ID: M0305.

A01: the original smooth positive measure and smooth Hermitian form specify the
integral pairing on the original atlas sections. Its unique extension identifies
H^(-s) conjugate-linearly with the continuous complex dual of H^s. This is a
topological equivalence, not an isometry for the auxiliary Fourier norms.

Spin Geometry III.2, Theorem 2.15(2), pp.176-177, uses the bilinear E--E* integral.
The actual smooth Hermitian metric gives the conjugate-linear identification with
E*, producing precisely the displayed first-conjugate-linear convention. The
equivalence is specified by that geometric integral, rather than by an unrelated
Riesz map for the localization Hilbert norm. Local ranks may vary throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.AtlasBundlePresentation

set_option maxSynthPendingDepth 40

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff ComplexConjugate SchwartzMap FourierTransform ENNReal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  {A : SmoothComplexBundleAtlas (n := n) E}
  (L : AtlasBundlePresentation A) (μ : Measure M)
  [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)

include hM hT hSC hC hμ hh

set_option maxHeartbeats 1000000 in
-- The extended limit accommodates finite chart/frame duality and its integral pairing.
/-- The original integral pairing uniquely gives the opposite-order continuous duality. -/
theorem existsUnique_sobolevDuality (s : ℝ) :
    ∃! T : L.SobolevSpace (-s) ≃L⋆[ℂ] StrongDual ℂ (L.SobolevSpace s),
      ∀ u v : A.smoothSections,
        T (L.smoothToSobolev (-s) v) (L.smoothToSobolev s u) =
          ∫ x : M, (h.toCore x).inner (v.val x) (u.val x) ∂μ := by
  classical
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let X := EuclideanSpace ℝ (Fin n)
  let V (j : Fin L.size) := EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))
  let pair (v u : A.smoothSections) : ℂ := ∫ x, (h.toCore x).inner (v.val x) (u.val x) ∂μ
  have hint (v u : A.smoothSections) :
      Integrable (fun x ↦ (h.toCore x).inner (v.val x) (u.val x)) μ :=
    (A.contMDiff_pairing h hh v u).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Each original cutoff receives a plateau inside precisely its own chart/frame overlap.
  let U (j : Fin L.size) :=
    (L.chart j).target ∩ (L.chart j).symm ⁻¹' (A.chart (L.frameIndex j)).baseSet
  let K (j : Fin L.size) := (L.chart j) '' tsupport (L.cutoff j)
  have hU (j : Fin L.size) : IsOpen (U j) :=
    (L.chart j).continuousOn_symm.isOpen_inter_preimage
      (L.chart j).open_target (A.chart (L.frameIndex j)).open_baseSet
  have hK (j : Fin L.size) : IsCompact (K j) :=
    (L.compact_support j).image_of_continuousOn
      ((L.chart j).continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
  have hKU (j : Fin L.size) : K j ⊆ U j := by
    rintro _ ⟨x, hx, rfl⟩
    have hs := (L.support_subset j hx).1
    exact ⟨(L.chart j).map_source hs, by
      change (L.chart j).symm ((L.chart j) x) ∈ (A.chart (L.frameIndex j)).baseSet
      rw [(L.chart j).left_inv hs]
      exact (L.support_subset j hx).2⟩
  have hplateau (j : Fin L.size) : ∃ η : X → ℝ,
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
  let κ (j : Fin L.size) (z : X) := η j z * L.cutoff j ((L.chart j).symm z)
  have hκ (j : Fin L.size) : ContDiff ℝ ∞ (κ j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport (η j)
    · have hzt := (hsη j hz).1
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞)
          (L.chart_mem_atlas j)) hzt
      exact (hη j).contDiffAt.mul
        ((L.smooth_cutoff j).contMDiffAt.comp z hchart).contDiffAt
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (η j)).isOpen_compl.mem_nhds hz] with y hy
      simp [κ, image_eq_zero_of_notMem_tsupport hy]
  have hsκ (j : Fin L.size) : tsupport (κ j) ⊆ K j := by
    apply closure_minimal ?_ (hK j).isClosed
    intro z hz
    have hηz : η j z ≠ 0 := left_ne_zero_of_mul (show κ j z ≠ 0 from hz)
    have hχz : L.cutoff j ((L.chart j).symm z) ≠ 0 :=
      right_ne_zero_of_mul (show κ j z ≠ 0 from hz)
    have hzt := (hsη j (subset_tsupport _ hηz)).1
    exact ⟨(L.chart j).symm z, subset_tsupport _ hχz, (L.chart j).right_inv hzt⟩
  have hcκ (j : Fin L.size) : HasCompactSupport (κ j) :=
    (hK j).of_isClosed_subset (isClosed_tsupport _) (hsκ j)
  have hκtarget (j : Fin L.size) (z : X) (hz : z ∈ (L.chart j).target) :
      κ j z = L.cutoff j ((L.chart j).symm z) := by
    by_cases hχ : L.cutoff j ((L.chart j).symm z) = 0
    · simp [κ, hχ]
    · have hzK : z ∈ K j :=
        ⟨(L.chart j).symm z, subset_tsupport _ hχ, (L.chart j).right_inv hz⟩
      simp [κ, honeη j z hzK]
  let D (j : Fin L.size) : AtlasChartCutoff A (L.chart j) :=
    { frameIndex := L.frameIndex j
      cutoff := κ j
      smooth_cutoff := hκ j
      compact_support := hcκ j
      support_subset := (hsκ j).trans (hKU j) }
  let B (j : Fin L.size) : AtlasChartCutoff A (L.chart j) :=
    { frameIndex := L.frameIndex j
      cutoff := η j
      smooth_cutoff := hη j
      compact_support := hcη j
      support_subset := hsη j }
  have hDlocal (j : Fin L.size) (u : A.smoothSections) :
      (D j).localize (L.chart_mem_atlas j) u = L.localize j u := by
    apply SchwartzMap.ext
    intro z
    change (if z ∈ (L.chart j).target then
      (κ j z : ℂ) • atlasSectionInChart A (L.chart j) (L.frameIndex j) u.val z else 0) = _
    by_cases hz : z ∈ (L.chart j).target
    · simp [AtlasBundlePresentation.localize, AtlasBundlePresentation.localizedFunction,
        hz, hκtarget j z hz]
    · simp [AtlasBundlePresentation.localize, AtlasBundlePresentation.localizedFunction, hz]
  choose ρ hρ hρpos hρmap using
    (fun j : Fin L.size ↦ IsSmoothPositiveMeasure.exists_smooth_density
      (μ := μ) (L.chart j) (L.chart_mem_atlas j))
  let G (j : Fin L.size) (z : X) : V j →L[ℂ] V j :=
    A.hermitianGramOperator h (L.frameIndex j) ((L.chart j).symm z)
  have hG (j : Fin L.size) (z : X) (hz : z ∈ U j) : ContDiffAt ℝ ∞ (G j) z := by
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞)
        (L.chart_mem_atlas j)) hz.1
    exact (((A.contMDiffOn_hermitianGramOperator h hh (L.frameIndex j)).contMDiffAt
      ((A.chart (L.frameIndex j)).open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
  let W (j : Fin L.size) : X → V j →L[ℂ] V j :=
    cutoffMatrix (η j) (fun z ↦ ρ j z • G j z)
  have hW (j : Fin L.size) : ContDiff ℝ ∞ (W j) :=
    contDiff_cutoffMatrix (U j) (hU j) _
      (((hρ j).mono (fun _ hz ↦ hz.1)).smul
        (fun z hz ↦ (hG j z hz).contDiffWithinAt)) (η j) (hη j) (hsη j)
  have hcW (j : Fin L.size) : HasCompactSupport (W j) :=
    hasCompactSupport_cutoffMatrix (η j) _ (hcη j)
  -- Extension of each plateau localization is exactly the original partition summand.
  have hpiece (j : Fin L.size) (u : A.smoothSections) (x : M) :
      ((D j).extend (L.chart_mem_atlas j) ((B j).localize (L.chart_mem_atlas j) u)).val x =
        (L.cutoff j x : ℂ) • u.val x := by
    change (D j).extendedFunction ((B j).localize (L.chart_mem_atlas j) u) x = _
    by_cases hx : x ∈ (L.chart j).source ∩ (A.chart (L.frameIndex j)).baseSet
    · rw [AtlasChartCutoff.extendedFunction, dite_eq_left hx]
      change (κ j ((L.chart j) x) : ℂ) • (A.frameLinearEquiv (L.frameIndex j) x hx.2).symm
        ((EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ)
          ((B j).localizedFunction u ((L.chart j) x))) = _
      rw [hκtarget j _ ((L.chart j).map_source hx.1), (L.chart j).left_inv hx.1]
      by_cases hχ : L.cutoff j x = 0
      · simp [hχ]
      have hxK : (L.chart j) x ∈ K j := ⟨x, subset_tsupport _ hχ, rfl⟩
      rw [AtlasChartCutoff.localizedFunction, ite_eq_left ((L.chart j).map_source hx.1)]
      change _ • (A.frameLinearEquiv (L.frameIndex j) x hx.2).symm
        ((EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ)
          ((η j ((L.chart j) x) : ℂ) •
            atlasSectionInChart A (L.chart j) (L.frameIndex j) u.val ((L.chart j) x))) = _
      rw [honeη j _ hxK]
      simp only [Complex.ofReal_one, one_smul, atlasSectionInChart,
        ContinuousLinearEquiv.apply_symm_apply]
      have hpoint : (⟨(L.chart j).symm ((L.chart j) x),
          u.val ((L.chart j).symm ((L.chart j) x))⟩ : TotalSpace Unit E) = ⟨x, u.val x⟩ :=
        congrArg (fun y ↦ (⟨y, u.val y⟩ : TotalSpace Unit E)) ((L.chart j).left_inv hx.1)
      rw [hpoint]
      change _ • (A.frameLinearEquiv (L.frameIndex j) x hx.2).symm
        ((A.frameLinearEquiv (L.frameIndex j) x hx.2) (u.val x)) = _
      rw [LinearEquiv.symm_apply_apply]
    · have hχ : L.cutoff j x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hxK ↦ hx (L.support_subset j hxK))
      simp [AtlasChartCutoff.extendedFunction, D, hx, hχ]
  have hsum (u : A.smoothSections) :
      ∑ j, (D j).extend (L.chart_mem_atlas j) ((B j).localize (L.chart_mem_atlas j) u) = u := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply, hpiece]
    rw [← Finset.sum_smul]
    have hχ : ∑ j, (L.cutoff j x : ℂ) = 1 := by exact_mod_cast L.sum_cutoff x
    rw [hχ, one_smul]
  have hpairingSum (v u : A.smoothSections) :
      pair v u = ∑ j, ∫ z, inner ℂ (L.localize j v z)
        (matrixMultiplierCLM (W j) (hW j) (hcW j)
          ((B j).localize (L.chart_mem_atlas j) u) z) := by
    let uj (j : Fin L.size) :=
      (D j).extend (L.chart_mem_atlas j) ((B j).localize (L.chart_mem_atlas j) u)
    have heval (x : M) :
        (h.toCore x).inner (v.val x) (u.val x) =
          ∑ j, (h.toCore x).inner (v.val x) ((uj j).val x) := by
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      have hp := congrArg (fun w : A.smoothSections ↦ w.val x) (hsum u)
      rw [← hp]
      simp only [Submodule.coe_sum, Finset.sum_apply]
      let bx : E x →ₗ[ℂ] ℂ :=
        { toFun := (h.toCore x).inner (v.val x)
          map_add' := fun a b ↦ InnerProductSpace.Core.inner_add_right _ a b
          map_smul' := fun c a ↦ InnerProductSpace.Core.inner_smul_right _ a }
      exact map_sum bx _ _
    calc
      pair v u = ∫ x, ∑ j, (h.toCore x).inner (v.val x) ((uj j).val x) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall heval)
      _ = ∑ j, ∫ x, (h.toCore x).inner (v.val x) ((uj j).val x) ∂μ :=
        integral_finsetSum _ (fun j _ ↦ hint v (uj j))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [(D j).integral_pairing_extend (L.chart_mem_atlas j) μ h hh (ρ j)
          (hρ j).continuousOn (fun z hz ↦ (hρpos j z hz).le) (hρmap j)]
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hDlocal, matrixMultiplierCLM_apply]
        by_cases hz : z ∈ K j
        · change ρ j z • inner ℂ (L.localize j v z)
            (G j z ((B j).localize (L.chart_mem_atlas j) u z)) =
          inner ℂ (L.localize j v z)
            (η j z • (ρ j z • G j z ((B j).localize (L.chart_mem_atlas j) u z)))
          rw [honeη j z hz, one_smul, inner_smul_right_eq_smul]
        · have hv : L.localize j v z = 0 := image_eq_zero_of_notMem_tsupport
            (fun hz' ↦ hz ((L.localizedFunction_properties j v).2.1 hz'))
          simp [hv]
  -- Local Fourier duality and bounded coordinate reconstruction control the original pairing.
  have hbound (s : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : A.smoothSections,
      ‖pair v u‖ ≤ C * ‖L.smoothToSobolev (-s) v‖ * ‖L.smoothToSobolev s u‖ := by
    have hlocal (j : Fin L.size) : ∃ c : ℝ, 0 ≤ c ∧ ∀ u,
        ‖schwartzSobolevCoordinate s
          (matrixMultiplierCLM (W j) (hW j) (hcW j)
            ((B j).localize (L.chart_mem_atlas j) u))‖ ≤ c * ‖L.smoothToSobolev s u‖ := by
      obtain ⟨a, ha, hba⟩ := (B j).exists_norm_localize_sobolev_le (L.chart_mem_atlas j) L s
      obtain ⟨b, hb, hbb⟩ := exists_norm_matrixMultiplier_sobolev_le (W j) (hW j) (hcW j) s
      refine ⟨b * a, mul_nonneg hb ha, fun u ↦ ?_⟩
      exact (hbb _).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hba u) hb)
    choose c hc hcb using hlocal
    refine ⟨∑ j, c j, Finset.sum_nonneg (fun j _ ↦ hc j), ?_⟩
    intro u v
    rw [hpairingSum]
    calc
      _ ≤ ∑ j, ‖∫ z, inner ℂ (L.localize j v z)
          (matrixMultiplierCLM (W j) (hW j) (hcW j)
            ((B j).localize (L.chart_mem_atlas j) u) z)‖ := norm_sum_le _ _
      _ ≤ ∑ j, c j * ‖L.smoothToSobolev (-s) v‖ * ‖L.smoothToSobolev s u‖ := by
        apply Finset.sum_le_sum
        intro j _
        have hf := sobolev_pairing_schwartz (-s) (L.localize j v)
          (matrixMultiplierCLM (W j) (hW j) (hcW j)
            ((B j).localize (L.chart_mem_atlas j) u))
        simp only [neg_neg] at hf
        rw [← hf]
        have hv : ‖schwartzSobolevCoordinate (-s) (L.localize j v)‖ ≤
            ‖L.smoothToSobolev (-s) v‖ := PiLp.norm_apply_le (L.sobolevCoordinates (-s) v) j
        calc
          _ ≤ ‖schwartzSobolevCoordinate (-s) (L.localize j v)‖ *
              ‖schwartzSobolevCoordinate s
                (matrixMultiplierCLM (W j) (hW j) (hcW j)
                  ((B j).localize (L.chart_mem_atlas j) u))‖ := norm_inner_le_norm _ _
          _ ≤ ‖L.smoothToSobolev (-s) v‖ * (c j * ‖L.smoothToSobolev s u‖) :=
            mul_le_mul hv (hcb j u) (norm_nonneg _) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]
  -- The inverse of the actual Gram operator and density recovers local dual representatives.
  have hequiv (j : Fin L.size) (z : X) (hz : z ∈ U j) :
      ∃ Q : V j ≃L[ℂ] V j, Q.toContinuousLinearMap = G j z :=
    A.exists_equiv_hermitianGramOperator h (L.frameIndex j) ((L.chart j).symm z) hz.2
  have hGi (j : Fin L.size) : ContDiffOn ℝ ∞ (fun z ↦ (G j z).inverse) (U j) := by
    intro z hz
    obtain ⟨Q, hQ⟩ := hequiv j z hz
    have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G j z) := by
      rw [← hQ]
      exact (contDiffAt_map_inverse Q).restrict_scalars ℝ
    exact (hi.comp z (hG j z hz)).contDiffWithinAt
  let R (j : Fin L.size) : X → V j →L[ℂ] V j :=
    cutoffMatrix (η j) (fun z ↦ (ρ j z)⁻¹ • (G j z).inverse)
  have hR (j : Fin L.size) : ContDiff ℝ ∞ (R j) :=
    contDiff_cutoffMatrix (U j) (hU j) _
      ((((hρ j).mono (fun _ hz ↦ hz.1)).inv
        (fun z hz ↦ (hρpos j z hz.1).ne')).smul (hGi j)) (η j) (hη j) (hsη j)
  have hcR (j : Fin L.size) : HasCompactSupport (R j) :=
    hasCompactSupport_cutoffMatrix (η j) _ (hcη j)
  have hcancel (j : Fin L.size) (z : X) (hz : z ∈ K j) (w : V j) :
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
  have htest (j : Fin L.size) (u : A.smoothSections) (v : 𝓢(X, V j)) :
      pair u ((D j).extend (L.chart_mem_atlas j)
        (matrixMultiplierCLM (R j) (hR j) (hcR j) v)) =
          ∫ z, inner ℂ (L.localize j u z) (v z) := by
    change (∫ x, (h.toCore x).inner (u.val x)
      (((D j).extend (L.chart_mem_atlas j)
        (matrixMultiplierCLM (R j) (hR j) (hcR j) v)).val x) ∂μ) = _
    rw [(D j).integral_pairing_extend (L.chart_mem_atlas j) μ h hh (ρ j)
      (hρ j).continuousOn (fun z hz ↦ (hρpos j z hz).le) (hρmap j)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hDlocal, matrixMultiplierCLM_apply]
    by_cases hz : z ∈ K j
    · change ρ j z • inner ℂ (L.localize j u z) (G j z (R j z (v z))) = _
      rw [← inner_smul_right_eq_smul, hcancel j z hz]
    · have hu : L.localize j u z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz ((L.localizedFunction_properties j u).2.1 hz'))
      simp [hu]
  -- Sesquilinearity passes to the integral on these original smooth sections.
  let b (x : M) : E x →ₗ⋆[ℂ] E x →ₗ[ℂ] ℂ := by
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact LinearMap.mk₂'ₛₗ _ _ (h.toCore x).inner
      (fun a b c ↦ (h.toCore x).add_left a b c)
      (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
      (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
      (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
  have hconj (u v : A.smoothSections) : conj (pair v u) = pair u v := by
    dsimp only [pair]
    rw [← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ (h.toCore x).conj_inner_symm (u.val x) (v.val x)
  have hadd (u v w : A.smoothSections) : pair (u + v) w = pair u w + pair v w := by
    change (∫ x, b x (u.val x + v.val x) (w.val x) ∂μ) = _
    simp only [map_add, LinearMap.add_apply]
    exact integral_add (hint u w) (hint v w)
  have hsmul (c : ℂ) (u v : A.smoothSections) : pair (c • u) v = conj c * pair u v := by
    change (∫ x, b x (c • u.val x) (v.val x) ∂μ) = _
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    exact integral_const_mul (conj c) _
  let f (v : A.smoothSections) : A.smoothSections →ₗ[ℂ] ℂ :=
    { toFun := pair v
      map_add' := by
        intro u w
        change (∫ x, b x (v.val x) (u.val x + w.val x) ∂μ) = _
        simp only [map_add]
        exact integral_add (hint v u) (hint v w)
      map_smul' := by
        intro c u
        change (∫ x, b x (v.val x) (c • u.val x) ∂μ) = _
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hf (v u : A.smoothSections) : f v u = pair v u := rfl
  have hsurj (t : ℝ) :
      ∃ T : L.SobolevSpace (-t) →L⋆[ℂ] StrongDual ℂ (L.SobolevSpace t),
        (∀ u v : A.smoothSections,
          T (L.smoothToSobolev (-t) v) (L.smoothToSobolev t u) =
            pair v u) ∧ Function.Surjective T := by
    -- Extend the original scalar pairing in each variable using its proven bound.
    obtain ⟨C, hC, hbound⟩ := hbound t
    let F (v : A.smoothSections) : StrongDual ℂ (L.SobolevSpace t) :=
      (f v).extendOfNorm (L.smoothToSobolev t)
    have hF (v u : A.smoothSections) :
        F v (L.smoothToSobolev t u) = pair v u := by
      rw [LinearMap.extendOfNorm_eq (L.denseRange_smoothToSobolev t)
        ⟨C * ‖L.smoothToSobolev (-t) v‖, fun w ↦ by rw [hf]; exact hbound w v⟩, hf]
    let f₁ : A.smoothSections →ₗ⋆[ℂ] StrongDual ℂ (L.SobolevSpace t) :=
      { toFun := F
        map_add' := by
          intro v w
          apply ContinuousLinearMap.ext
          intro u
          exact (L.denseRange_smoothToSobolev t).induction_on u
            (isClosed_eq (F (v + w)).continuous ((F v).continuous.add (F w).continuous))
            (fun z ↦ by
              simp only [add_apply, hF, hadd])
        map_smul' := by
          intro c v
          apply ContinuousLinearMap.ext
          intro u
          exact (L.denseRange_smoothToSobolev t).induction_on u
            (isClosed_eq (F (c • v)).continuous ((F v).continuous.const_smul (conj c)))
            (fun z ↦ by
              simp only [smul_apply, hF,
                hsmul, smul_eq_mul]) }
    have hf₁ (v : A.smoothSections) :
        ‖f₁ v‖ ≤ C * ‖L.smoothToSobolev (-t) v‖ :=
      (f v).opNorm_extendOfNorm_le (L.denseRange_smoothToSobolev t)
        (mul_nonneg hC (norm_nonneg _)) (fun u ↦ by rw [hf]; exact hbound u v)
    let T : L.SobolevSpace (-t) →L⋆[ℂ] StrongDual ℂ (L.SobolevSpace t) :=
      f₁.extendOfNorm (L.smoothToSobolev (-t))
    have hT (u v : A.smoothSections) :
        T (L.smoothToSobolev (-t) v) (L.smoothToSobolev t u) =
          pair v u := by
      rw [LinearMap.extendOfNorm_eq (L.denseRange_smoothToSobolev (-t)) ⟨C, hf₁⟩]
      exact hF v u
    let Q (j : Fin L.size) : 𝓢(X, V j) →ₗ[ℂ] L.SobolevSpace (-t) :=
      (L.smoothToSobolev (-t)).comp
        (((D j).extendLinearMap (L.chart_mem_atlas j)).comp
          (matrixMultiplierCLM (R j) (hR j) (hcR j)).toLinearMap)
    have hQbound (j : Fin L.size) : ∃ c : ℝ,
        ∀ v, ‖Q j v‖ ≤ c * ‖schwartzSobolevCoordinate (-t) v‖ := by
      obtain ⟨a, ha, hba⟩ := (D j).exists_norm_extend_sobolev_le (L.chart_mem_atlas j) L (-t)
      obtain ⟨b, hb, hbb⟩ := exists_norm_matrixMultiplier_sobolev_le (R j) (hR j) (hcR j) (-t)
      refine ⟨a * b, fun v ↦ ?_⟩
      exact (hba _).trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hbb v) ha)
    let Q₁ (j : Fin L.size) : Lp (V j) 2 volume →L[ℂ] L.SobolevSpace (-t) :=
      (Q j).extendOfNorm (schwartzSobolevCoordinateLinearMap n (A.rank (L.frameIndex j)) (-t))
    have hQ₁ (j : Fin L.size) (v : 𝓢(X, V j)) :
        Q₁ j (schwartzSobolevCoordinate (-t) v) = Q j v :=
      (Q j).extendOfNorm_eq
        (denseRange_schwartzSobolevCoordinate n (A.rank (L.frameIndex j)) (-t)) (hQbound j) v
    let e (j : Fin L.size) : L.SobolevSpace t →L[ℂ] Lp (V j) 2 volume :=
      (PiLp.proj 2 _ j).comp (L.sobolevCoordinates t).range.topologicalClosure.subtypeL
    have hQpair_smooth (j : Fin L.size) (v : 𝓢(X, V j))
        (u : A.smoothSections) :
        T (Q j v) (L.smoothToSobolev t u) =
          inner ℂ (schwartzSobolevCoordinate (-t) v) (e j (L.smoothToSobolev t u)) := by
      change T (L.smoothToSobolev (-t) ((D j).extend (L.chart_mem_atlas j)
        (matrixMultiplierCLM (R j) (hR j) (hcR j) v))) _ = _
      rw [hT]
      rw [← hconj, htest]
      rw [← sobolev_pairing_schwartz t (L.localize j u) v]
      exact inner_conj_symm _ _
    have hQpair (j : Fin L.size) (z : Lp (V j) 2 volume) (u : L.SobolevSpace t) :
        T (Q₁ j z) u = inner ℂ z (e j u) := by
      have hdense (v : 𝓢(X, V j)) :
          T (Q₁ j (schwartzSobolevCoordinate (-t) v)) u =
            inner ℂ (schwartzSobolevCoordinate (-t) v) (e j u) := by
        rw [hQ₁]
        exact (L.denseRange_smoothToSobolev t).induction_on u
          (isClosed_eq (T (Q j v)).continuous
            (continuous_const.inner (e j).continuous)) (hQpair_smooth j v)
      exact (denseRange_schwartzSobolevCoordinate n (A.rank (L.frameIndex j)) (-t)).induction_on z
        (isClosed_eq ((T.continuous.comp (Q₁ j).continuous).clm_apply continuous_const)
          (continuous_id.inner continuous_const)) hdense
    refine ⟨T, hT, ?_⟩
    intro f
    let y : L.SobolevSpace t := (InnerProductSpace.toDual ℂ (L.SobolevSpace t)).symm f
    refine ⟨∑ j, Q₁ j (e j y), ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    simp only [map_sum, sum_apply, hQpair]
    change (∑ j, inner ℂ (y.val j) (u.val j)) = f u
    rw [← PiLp.inner_apply]
    change inner ℂ y u = f u
    exact InnerProductSpace.toDual_symm_apply
  obtain ⟨T, hT, hTsurj⟩ := hsurj s
  have hopposite : ∃ U : L.SobolevSpace s →L⋆[ℂ] StrongDual ℂ (L.SobolevSpace (-s)),
      (∀ u v : A.smoothSections,
        U (L.smoothToSobolev s v) (L.smoothToSobolev (-s) u) =
          pair v u) ∧ Function.Surjective U := by
    have htransport (a b : ℝ) (hab : -a = b) :
        ∃ U : L.SobolevSpace b →L⋆[ℂ] StrongDual ℂ (L.SobolevSpace a),
          (∀ u v : A.smoothSections,
            U (L.smoothToSobolev b v) (L.smoothToSobolev a u) =
              pair v u) ∧ Function.Surjective U := by
      subst b
      exact hsurj a
    exact htransport (-s) s (neg_neg s)
  obtain ⟨U, hU, hUsurj⟩ := hopposite
  -- The two extensions are conjugate transposes because their original integrals are.
  have hsymm (v : L.SobolevSpace (-s)) (u : L.SobolevSpace s) :
      U u v = conj (T v u) := by
    have hv (w : A.smoothSections) :
        U u (L.smoothToSobolev (-s) w) = conj (T (L.smoothToSobolev (-s) w) u) := by
      exact (L.denseRange_smoothToSobolev s).induction_on u
        (isClosed_eq (U.continuous.clm_apply continuous_const)
          (Complex.continuous_conj.comp (T (L.smoothToSobolev (-s) w)).continuous))
        (fun z ↦ by rw [hU, hT]; exact (hconj z w).symm)
    exact (L.denseRange_smoothToSobolev (-s)).induction_on v
      (isClosed_eq (U u).continuous
        (Complex.continuous_conj.comp (T.continuous.clm_apply continuous_const))) hv
  have hTinj : Function.Injective T := by
    apply (injective_iff_map_eq_zero T).mpr
    intro v hv
    obtain ⟨u, hu⟩ := hUsurj (InnerProductSpace.toDual ℂ (L.SobolevSpace (-s)) v)
    have hz : inner ℂ v v = 0 := by
      change (InnerProductSpace.toDual ℂ (L.SobolevSpace (-s)) v) v = 0
      rw [← hu, hsymm, hv]
      simp
    exact inner_self_eq_zero.mp hz
  let Q : L.SobolevSpace (-s) ≃L⋆[ℂ] StrongDual ℂ (L.SobolevSpace s) :=
    ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hTinj)
      (LinearMap.range_eq_top.mpr hTsurj)
  refine ⟨Q, hT, ?_⟩
  intro S hS
  apply ContinuousLinearEquiv.ext
  funext v
  exact (L.denseRange_smoothToSobolev (-s)).induction_on v
    (isClosed_eq S.continuous Q.continuous) (fun w ↦ by
      apply ContinuousLinearMap.ext
      intro u
      exact (L.denseRange_smoothToSobolev s).induction_on u
        (isClosed_eq (S _).continuous (Q _).continuous)
        (fun z ↦ (hS z w).trans (hT z w).symm))

/-- Opposite-order duality selected by its values on the original smooth sections. -/
def sobolevDuality (s : ℝ) :
    L.SobolevSpace (-s) ≃L⋆[ℂ] StrongDual ℂ (L.SobolevSpace s) :=
  Classical.choose (L.existsUnique_sobolevDuality μ h hh s).exists

/-- The completed geometric Hermitian pairing, conjugate-linear in its first argument. -/
def sobolevPairing (s : ℝ) (v : L.SobolevSpace (-s)) (u : L.SobolevSpace s) : ℂ :=
  L.sobolevDuality μ h hh s v u

/-- The chosen Sobolev pairing retains the exact original metric integral on smooth inputs. -/
theorem sobolevPairing_smoothToSobolev (s : ℝ) (u v : A.smoothSections) :
    L.sobolevPairing μ h hh s (L.smoothToSobolev (-s) v) (L.smoothToSobolev s u) =
      ∫ x : M, (h.toCore x).inner (v.val x) (u.val x) ∂μ := by
  /- Apply the specifying property of the selected equivalence. Both source
  vectors are the original smooth sections included through the same L.
  No measure, metric, presentation, or opposite-order sign is changed. -/
  exact (L.existsUnique_sobolevDuality μ h hh s).exists.choose_spec u v

end AtiyahSinger.AtlasBundlePresentation
