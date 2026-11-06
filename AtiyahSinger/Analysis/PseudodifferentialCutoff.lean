/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialRegularity

/-!
# Scalar cutoffs and smoothing away from the diagonal

Public module ID: M0888.

A local pseudodifferential piece absorbs arbitrary smooth scalar input and output
cutoffs in its original chart and frames. The action remains exactly the original
section-map composite. If the two scalar functions have pointwise zero product,
every coefficient of the diagonal amplitude expansion vanishes. The resulting
operator belongs to every order and therefore has an actual smooth kernel for
the original positive density. Nested cutoffs give both usual off-diagonal forms.

This is the standard localization argument of SG III.3, needed independently by
global composition, local regularity and asymptotic summation. It uses the proved
all-order kernel characterization and does not assume global PDO composition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

variable {E F}

namespace BundleChartCutoff

variable {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (C : BundleChartCutoff (r := r) E c)
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)

/-- Multiply the original chart cutoff by a smooth scalar function on the base.
The original frame and compact chart support are retained. -/
def mulSmooth
    (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ) : BundleChartCutoff (r := r) E c := by
  have hsmooth : ContDiff ℝ ∞ (fun z ↦ C.cutoff z * ψ (c.symm z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport C.cutoff
    · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) hc) (C.support_subset hz).1
      exact C.smooth_cutoff.contDiffAt.mul ((hψ.contMDiffAt.comp z hchart).contDiffAt)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport C.cutoff).isOpen_compl.mem_nhds hz] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  exact { C with
    cutoff := fun z ↦ C.cutoff z * ψ (c.symm z)
    smooth_cutoff := hsmooth
    compact_support := C.compact_support.of_isClosed_subset isClosed_closure
      tsupport_mul_subset_left
    support_subset := tsupport_mul_subset_left.trans C.support_subset }

/-- Localization with the multiplied cutoff localizes the same product section. -/
theorem localize_mulSmooth
    (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (u : smoothSections (n := n) (r := r) E) :
    (C.mulSmooth hc ψ hψ).localize hc u =
      C.localize hc (smoothSectionMul E (fun x ↦ (ψ x : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hψ) u) := by
  apply SchwartzMap.ext
  intro z
  by_cases hz : z ∈ tsupport C.cutoff
  · have hzc := (C.support_subset hz).1
    have hzf := (C.support_subset hz).2
    let := C.frame_mem_atlas
    change (C.mulSmooth hc ψ hψ).localizedFunction u z =
      C.localizedFunction (smoothSectionMul E (fun x ↦ (ψ x : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hψ) u) z
    simp only [localizedFunction, hzc, ↓reduceIte]
    change ((C.cutoff z * ψ (c.symm z) : ℝ) : ℂ) •
      (C.frame.linearEquivAt ℂ (c.symm z) hzf) (u.val (c.symm z)) =
      (C.cutoff z : ℂ) • (C.frame.linearEquivAt ℂ (c.symm z) hzf)
        ((ψ (c.symm z) : ℂ) • u.val (c.symm z))
    rw [map_smul, Complex.ofReal_mul, smul_smul]
  · simp [localize, localizedFunction, mulSmooth, image_eq_zero_of_notMem_tsupport hz]

/-- Extending with the multiplied cutoff multiplies the original extended section. -/
theorem extend_mulSmooth
    (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    (C.mulSmooth hc ψ hψ).extend hc v =
      smoothSectionMul E (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)
        (C.extend hc v) := by
  apply Subtype.ext
  funext x
  change (C.mulSmooth hc ψ hψ).extendedFunction v x = (ψ x : ℂ) • C.extendedFunction v x
  by_cases hx : x ∈ c.source
  · simp only [extendedFunction, hx, ↓reduceIte]
    dsimp only [mulSmooth]
    rw [c.left_inv hx, Complex.ofReal_mul, smul_smul, mul_comm]
  · simp [extendedFunction, hx]

end BundleChartCutoff

namespace PseudodifferentialPiece

variable {m : ℝ} (R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)

/-- Absorb the output and input scalar cutoffs in the same original local piece. -/
def cutoff
    (χ ψ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ) :
    PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
  { R with
    input := R.input.mulSmooth R.chart_mem_atlas ψ hψ
    output := R.output.mulSmooth R.chart_mem_atlas χ hχ
    input_support_in_output_frame :=
      tsupport_mul_subset_left.trans R.input_support_in_output_frame
    output_support_in_input_frame :=
      tsupport_mul_subset_left.trans R.output_support_in_input_frame }

/-- The cutoff piece is exactly the original section map between its two multipliers. -/
theorem toLinearMap_cutoff
    (χ ψ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ) :
    (R.cutoff χ ψ hχ hψ).toLinearMap =
      (smoothSectionMul F (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)).comp
        (R.toLinearMap.comp
          (smoothSectionMul E (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ))) := by
  -- The two multiplication identities act on the same original intermediate Schwartz function.
  apply LinearMap.ext
  intro u
  change (R.output.mulSmooth R.chart_mem_atlas χ hχ).extend R.chart_mem_atlas
    (R.operator ((R.input.mulSmooth R.chart_mem_atlas ψ hψ).localize R.chart_mem_atlas u)) = _
  rw [BundleChartCutoff.localize_mulSmooth, BundleChartCutoff.extend_mulSmooth]
  rfl

variable [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- Scalar cutoffs with zero product leave an actual smooth-kernel operator.
This includes either side of the usual nested-cutoff off-diagonal remainder. -/
theorem isSmoothingOperator_cutoff_of_mul_eq_zero
    (χ ψ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (hzero : ∀ x, χ x * ψ x = 0) :
    IsSmoothingOperator μ
      ((smoothSectionMul F (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)).comp
        (R.toLinearMap.comp
          (smoothSectionMul E (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)))) := by
  classical
  -- Preserve the exact compact coordinate operator while lowering its declared symbol order.
  have hpieceLower {m l : ℝ}
      (R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (hR : IsSymbol Set.univ l (cutoffSymbol R.output.cutoff R.input.cutoff R.symbol)) :
      IsPseudodifferentialOperator E F μ l R.toLinearMap := by
    let := R.input.frame_mem_atlas
    let := R.output.frame_mem_atlas
    let X := EuclideanSpace ℝ (Fin n)
    let U := R.chart.target ∩ R.chart.symm ⁻¹' (R.input.frame.baseSet ∩ R.output.frame.baseSet)
    let K := tsupport R.output.cutoff ∪ tsupport R.input.cutoff
    have hU : IsOpen U := R.chart.isOpen_inter_preimage_symm
      (R.input.frame.open_baseSet.inter R.output.frame.open_baseSet)
    have hK : IsCompact K := R.output.compact_support.union R.input.compact_support
    have hKU : K ⊆ U := by
      intro z hz
      rcases hz with hz | hz
      · exact ⟨(R.output.support_subset hz).1, R.output_support_in_input_frame hz,
          (R.output.support_subset hz).2⟩
      · exact ⟨(R.input.support_subset hz).1, (R.input.support_subset hz).2,
          R.input_support_in_output_frame hz⟩
    obtain ⟨O, hOo, hKO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨δ, hδ, _, hsδ, honeδ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo hK.isClosed hKO
    have hδsupport : tsupport δ = closure O := congrArg closure hsδ
    have hcδ : HasCompactSupport δ := by simpa [HasCompactSupport, hδsupport] using hOc
    have hδU : tsupport δ ⊆ U := by rwa [hδsupport]
    have hδone (z : X) (hz : z ∈ K) : δ z = 1 := (honeδ z).mp hz
    let A : BundleChartCutoff (r := r) E R.chart :=
      { frame := R.input.frame
        frame_mem_atlas := R.input.frame_mem_atlas
        cutoff := δ
        smooth_cutoff := hδ
        compact_support := hcδ
        support_subset := fun z hz ↦ ⟨(hδU hz).1, (hδU hz).2.1⟩ }
    let B : BundleChartCutoff (r := q) F R.chart :=
      { frame := R.output.frame
        frame_mem_atlas := R.output.frame_mem_atlas
        cutoff := δ
        smooth_cutoff := hδ
        compact_support := hcδ
        support_subset := fun z hz ↦ ⟨(hδU hz).1, (hδU hz).2.2⟩ }
    let L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F l :=
      { chart := R.chart
        chart_mem_atlas := R.chart_mem_atlas
        input := A
        output := B
        input_support_in_output_frame := fun z hz ↦ (hδU hz).2.2
        output_support_in_input_frame := fun z hz ↦ (hδU hz).2.1
        operator := R.coordinateOperator
        symbol := cutoffSymbol R.output.cutoff R.input.cutoff R.symbol
        isSymbol := hR
        operator_apply := R.coordinateOperator_eq_quantize }
    have hg : (fun z ↦ (R.input.cutoff z : ℂ)).HasTemperateGrowth :=
      (R.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp R.input.smooth_cutoff)
    have hinput (u : smoothSections (n := n) (r := r) E) :
        SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
          (fun z ↦ (R.input.cutoff z : ℂ)) (A.localize R.chart_mem_atlas u) =
            R.input.localize R.chart_mem_atlas u := by
      apply SchwartzMap.ext
      intro z
      rw [SchwartzMap.smulLeftCLM_apply_apply hg]
      change (R.input.cutoff z : ℂ) • A.localizedFunction u z = R.input.localizedFunction u z
      by_cases hz : z ∈ tsupport R.input.cutoff
      · have hzt := (R.input.support_subset hz).1
        have hone : δ z = 1 := hδone z (Or.inr hz)
        simp only [BundleChartCutoff.localizedFunction, hzt, ↓reduceIte]
        change (R.input.cutoff z : ℂ) • ((δ z : ℂ) • _) = _
        rw [hone, Complex.ofReal_one, one_smul]
      · simp [BundleChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
    have heq : L.toLinearMap = R.toLinearMap := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      change B.extendedFunction (R.coordinateOperator (A.localize R.chart_mem_atlas u)) x =
        R.output.extendedFunction (R.operator (R.input.localize R.chart_mem_atlas u)) x
      by_cases hx : x ∈ R.chart.source
      · simp only [BundleChartCutoff.extendedFunction, hx, ↓reduceIte]
        change (δ (R.chart x) : ℂ) • R.output.frame.symmL ℂ x
          (R.coordinateOperator (A.localize R.chart_mem_atlas u) (R.chart x)) = _
        rw [R.coordinateOperator_apply, hinput, ← Complex.coe_smul, map_smul, smul_smul]
        by_cases hz : R.chart x ∈ tsupport R.output.cutoff
        · rw [hδone _ (Or.inl hz), Complex.ofReal_one, one_mul]
        · simp [image_eq_zero_of_notMem_tsupport hz]
      · simp only [BundleChartCutoff.extendedFunction, hx, ↓reduceIte]
    rw [← heq]
    exact L.isPseudodifferentialOperator l
  let L := R.cutoff χ ψ hχ hψ
  have hproduct (z : EuclideanSpace ℝ (Fin n)) : L.output.cutoff z * L.input.cutoff z = 0 := by
    change (R.output.cutoff z * χ (R.chart.symm z)) *
      (R.input.cutoff z * ψ (R.chart.symm z)) = 0
    calc
      _ = (R.output.cutoff z * R.input.cutoff z) *
          (χ (R.chart.symm z) * ψ (R.chart.symm z)) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  -- Every diagonal expansion coefficient vanishes, including all derivative terms.
  have hnear (x ξ : EuclideanSpace ℝ (Fin n)) :
      (fun y ↦ cutoffAmplitude L.output.cutoff L.input.cutoff L.symbol x y ξ) =ᶠ[nhds x]
        (fun _ ↦ 0) := by
    by_cases hx : L.output.cutoff x = 0
    · exact Filter.Eventually.of_forall (fun y ↦ by simp [cutoffAmplitude, hx])
    · filter_upwards [L.output.smooth_cutoff.continuous.continuousAt.eventually_ne hx] with y hy
      have hinput : L.input.cutoff y = 0 := (mul_eq_zero.mp (hproduct y)).resolve_left hy
      simp [cutoffAmplitude, hinput]
  have hterms (j : ℕ) :
      amplitudeExpansionTerm (cutoffAmplitude L.output.cutoff L.input.cutoff L.symbol) j = 0 := by
    by_cases hj : j = 0
    · subst j
      rw [amplitudeExpansionTerm_zero]
      funext x ξ
      exact (hnear x ξ).eq_of_nhds
    · funext x ξ
      have hy (η : EuclideanSpace ℝ (Fin n)) :
          iteratedFDeriv ℝ j
            (fun y ↦ cutoffAmplitude L.output.cutoff L.input.cutoff L.symbol x y η) x = 0 := by
        simpa only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply] using
          ((hnear x η).iteratedFDeriv ℝ j).eq_of_nhds
      simp [amplitudeExpansionTerm, hy]
  -- All orders concern the same section map.
  -- The original density-specific criterion now gives its actual smooth kernel.
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  rw [← R.toLinearMap_cutoff χ ψ hχ hψ]
  apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ L.toLinearMap A B).mpr
  intro l
  obtain ⟨N, hN⟩ := exists_nat_gt (m - l)
  have h := hasSymbolExpansion_cutoffSymbol m L.symbol L.isSymbol
    L.output.cutoff L.input.cutoff L.output.smooth_cutoff L.input.smooth_cutoff
    L.output.compact_support L.input.compact_support N
  simp only [hterms, Finset.sum_const_zero, sub_zero] at h
  exact hpieceLower L (h.mono (by linarith))

end PseudodifferentialPiece

end AtiyahSinger
