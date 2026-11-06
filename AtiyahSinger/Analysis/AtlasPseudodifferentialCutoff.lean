/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialSobolev
public import AtiyahSinger.Geometry.AtlasSectionMaps

import AtiyahSinger.Analysis.CompactQuantization
import AtiyahSinger.Analysis.TwoSidedCutoff

/-!
# Scalar cutoffs for actual atlas pseudodifferential pieces

Public module ID: M0282.

The original atlas frames and independent local ranks are retained when a piece
absorbs smooth scalar multipliers. If their pointwise product vanishes, all
coefficients of the diagonal amplitude expansion vanish. The same section map
then has bounded extensions between every pair of real Sobolev orders.

This is the standard off-diagonal localization argument of SG III.3, adapted to
the finite-rank atlas model. It supplies global composition and later local
regularity, without assuming the composition theorem or a global fiber norm.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

namespace AtlasChartCutoff

variable {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (C : AtlasChartCutoff A c)
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)

/-- Multiply the original chart cutoff by a smooth scalar function on the base.
The original frame and compact chart support are retained. -/
def mulSmooth
    (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ) : AtlasChartCutoff A c where
  frameIndex := C.frameIndex
  cutoff := fun z ↦ C.cutoff z * ψ (c.symm z)
  smooth_cutoff := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport C.cutoff
    · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) hc) (C.support_subset hz).1
      exact C.smooth_cutoff.contDiffAt.mul ((hψ.contMDiffAt.comp z hchart).contDiffAt)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport C.cutoff).isOpen_compl.mem_nhds hz] with y hy
      have hzero : C.cutoff y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp only [hzero, zero_mul]
  compact_support := C.compact_support.of_isClosed_subset isClosed_closure
    tsupport_mul_subset_left
  support_subset := tsupport_mul_subset_left.trans C.support_subset

/-- Localization with the multiplied cutoff localizes the same product section. -/
theorem localize_mulSmooth
    (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (u : A.smoothSections) :
    (C.mulSmooth hc ψ hψ).localize hc u =
      C.localize hc (atlasSectionMul A (fun x ↦ (ψ x : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hψ) u) := by
  classical
  apply SchwartzMap.ext
  intro z
  by_cases hz : z ∈ tsupport C.cutoff
  · have hzc := (C.support_subset hz).1
    have hzf := (C.support_subset hz).2
    change (C.mulSmooth hc ψ hψ).localizedFunction u z =
      C.localizedFunction (atlasSectionMul A (fun x ↦ (ψ x : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hψ) u) z
    simp only [localizedFunction, hzc, ↓reduceIte]
    change ((C.cutoff z * ψ (c.symm z) : ℝ) : ℂ) •
      (EuclideanSpace.equiv (Fin (A.rank C.frameIndex)) ℂ).symm
        ((A.frameLinearEquiv C.frameIndex (c.symm z) hzf) (u.val (c.symm z))) =
      (C.cutoff z : ℂ) • (EuclideanSpace.equiv (Fin (A.rank C.frameIndex)) ℂ).symm
        ((A.frameLinearEquiv C.frameIndex (c.symm z) hzf)
          ((ψ (c.symm z) : ℂ) • u.val (c.symm z)))
    rw [map_smul, map_smul, Complex.ofReal_mul, smul_smul]
  · change (C.mulSmooth hc ψ hψ).localizedFunction u z =
      C.localizedFunction (atlasSectionMul A (fun x ↦ (ψ x : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hψ) u) z
    have hzero : C.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hz
    change (if z ∈ c.target then ((C.cutoff z * ψ (c.symm z) : ℝ) : ℂ) •
      atlasSectionInChart A c C.frameIndex u.val z else 0) = _
    simp only [localizedFunction, hzero, zero_mul, Complex.ofReal_zero, zero_smul, ite_self]

/-- Extending with the multiplied cutoff multiplies the original extended section. -/
theorem extend_mulSmooth
    (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank C.frameIndex)))) :
    (C.mulSmooth hc ψ hψ).extend hc v =
      atlasSectionMul A (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)
        (C.extend hc v) := by
  apply Subtype.ext
  funext x
  change (C.mulSmooth hc ψ hψ).extendedFunction v x = (ψ x : ℂ) • C.extendedFunction v x
  by_cases hx : x ∈ c.source ∩ (A.chart C.frameIndex).baseSet
  · simp only [extendedFunction, mulSmooth, dite_eq_left hx]
    rw [c.left_inv hx.1, Complex.ofReal_mul, smul_smul, mul_comm]
    exact dite_eq_left hx
  · simp [extendedFunction, mulSmooth, hx]

open scoped Classical in
/-- Localization followed by extension has exactly the two original cutoff factors. -/
theorem extend_localize_apply (u : A.smoothSections) (x : M) :
    (C.extend hc (C.localize hc u)).val x =
      if _hx : x ∈ c.source ∩ (A.chart C.frameIndex).baseSet then
        (C.cutoff (c x) : ℂ) • ((C.cutoff (c x) : ℂ) • u.val x) else 0 := by
  classical
  by_cases hx : x ∈ c.source ∩ (A.chart C.frameIndex).baseSet
  · rw [dite_eq_left hx]
    change C.extendedFunction (C.localize hc u) x = _
    simp only [extendedFunction, dite_eq_left hx]
    change (C.cutoff (c x) : ℂ) • (A.frameLinearEquiv C.frameIndex x hx.2).symm
      ((EuclideanSpace.equiv (Fin (A.rank C.frameIndex)) ℂ)
        (C.localizedFunction u (c x))) = _
    have hcoord : atlasSectionInChart A c C.frameIndex u.val (c x) =
        (EuclideanSpace.equiv (Fin (A.rank C.frameIndex)) ℂ).symm
          ((A.chart C.frameIndex ⟨x, u.val x⟩).2) := by
      unfold atlasSectionInChart
      congr 2
      exact congrArg (fun y ↦ A.chart C.frameIndex (⟨y, u.val y⟩ : TotalSpace Unit E))
        (c.left_inv hx.1)
    simp only [localizedFunction, ite_eq_left (c.map_source hx.1), hcoord, map_smul,
      ContinuousLinearEquiv.apply_symm_apply]
    change (C.cutoff (c x) : ℂ) • ((C.cutoff (c x) : ℂ) •
      (A.frameLinearEquiv C.frameIndex x hx.2).symm
        ((A.frameLinearEquiv C.frameIndex x hx.2) (u.val x))) = _
    rw [LinearEquiv.symm_apply_apply]
  · change C.extendedFunction (C.localize hc u) x = _
    simp only [extendedFunction, dite_eq_right hx]

end AtlasChartCutoff

namespace AtlasPseudodifferentialPiece

variable {m : ℝ} (R : AtlasPseudodifferentialPiece A B m)

/-- Absorb the output and input scalar cutoffs in the same original local piece. -/
def cutoff
    (χ ψ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ) :
    AtlasPseudodifferentialPiece A B m :=
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
      (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)).comp
        (R.toLinearMap.comp
          (atlasSectionMul A (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ))) := by
  -- The two multiplication identities act on the same original intermediate Schwartz function.
  apply LinearMap.ext
  intro u
  change (R.output.mulSmooth R.chart_mem_atlas χ hχ).extend R.chart_mem_atlas
    (R.operator ((R.input.mulSmooth R.chart_mem_atlas ψ hψ).localize R.chart_mem_atlas u)) = _
  rw [AtlasChartCutoff.localize_mulSmooth, AtlasChartCutoff.extend_mulSmooth]
  rfl

variable [SecondCountableTopology M] [CompactSpace M]

/-- Scalar cutoffs with zero product give an all-order Sobolev smoothing map.
This includes either side of the usual nested-cutoff off-diagonal remainder. -/
theorem isAtlasSmoothingOperator_cutoff_of_mul_eq_zero
    (χ ψ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
    (hzero : ∀ x, χ x * ψ x = 0) :
    IsAtlasSmoothingOperator A B
      ((atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)).comp
        (R.toLinearMap.comp
          (atlasSectionMul A (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)))) := by
  classical
  -- Retain the exact coordinate action while lowering its full symbol order.
  have hpieceLower {m l : ℝ}
      (R : AtlasPseudodifferentialPiece A B m)
      (hR : IsSymbol Set.univ l (cutoffSymbol R.output.cutoff R.input.cutoff R.symbol)) :
      IsAtlasPseudodifferentialOperator A B l R.toLinearMap := by
    let X := EuclideanSpace ℝ (Fin n)
    let U := R.chart.target ∩ R.chart.symm ⁻¹'
      ((A.chart R.input.frameIndex).baseSet ∩ (B.chart R.output.frameIndex).baseSet)
    let K := tsupport R.output.cutoff ∪ tsupport R.input.cutoff
    have hU : IsOpen U := R.chart.isOpen_inter_preimage_symm
      ((A.chart R.input.frameIndex).open_baseSet.inter (B.chart R.output.frameIndex).open_baseSet)
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
    let D₀ : AtlasChartCutoff A R.chart :=
      { frameIndex := R.input.frameIndex
        cutoff := δ
        smooth_cutoff := hδ
        compact_support := hcδ
        support_subset := fun z hz ↦ ⟨(hδU hz).1, (hδU hz).2.1⟩ }
    let K₀ : AtlasChartCutoff B R.chart :=
      { frameIndex := R.output.frameIndex
        cutoff := δ
        smooth_cutoff := hδ
        compact_support := hcδ
        support_subset := fun z hz ↦ ⟨(hδU hz).1, (hδU hz).2.2⟩ }
    let T := amplitudeOperator m (cutoffAmplitude R.output.cutoff R.input.cutoff R.symbol)
      (isAmplitude_cutoffAmplitude m R.symbol R.isSymbol _ _
        R.output.smooth_cutoff R.input.smooth_cutoff)
      (hasCompactSupport_cutoffAmplitude R.symbol _ _
        R.output.compact_support R.input.compact_support)
    have hTquant : ∀ u z, T u z =
        quantize (cutoffSymbol R.output.cutoff R.input.cutoff R.symbol) u z := by
      intro u z
      rw [amplitudeOperator_apply]
      exact (congrFun (quantize_amplitudeSymbol m _
        (isAmplitude_cutoffAmplitude m R.symbol R.isSymbol _ _
          R.output.smooth_cutoff R.input.smooth_cutoff)
        (hasCompactSupport_cutoffAmplitude R.symbol _ _
          R.output.compact_support R.input.compact_support) u) z).symm
    have hTapply (u) (z) : T u z = R.output.cutoff z • R.operator
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank R.input.frameIndex)))
          (fun w ↦ (R.input.cutoff w : ℂ)) u) z := by
      rw [hTquant, quantize_cutoffSymbol m R.symbol R.isSymbol _ _
        R.output.smooth_cutoff R.input.smooth_cutoff
        R.output.compact_support R.input.compact_support, R.operator_apply]
    let L : AtlasPseudodifferentialPiece A B l :=
      { chart := R.chart
        chart_mem_atlas := R.chart_mem_atlas
        input := D₀
        output := K₀
        input_support_in_output_frame := fun z hz ↦ (hδU hz).2.2
        output_support_in_input_frame := fun z hz ↦ (hδU hz).2.1
        operator := T
        symbol := cutoffSymbol R.output.cutoff R.input.cutoff R.symbol
        isSymbol := hR
        operator_apply := hTquant }
    have hg : (fun z ↦ (R.input.cutoff z : ℂ)).HasTemperateGrowth :=
      (R.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp R.input.smooth_cutoff)
    have hinput (u : A.smoothSections) :
        SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank R.input.frameIndex)))
          (fun z ↦ (R.input.cutoff z : ℂ)) (D₀.localize R.chart_mem_atlas u) =
            R.input.localize R.chart_mem_atlas u := by
      apply SchwartzMap.ext
      intro z
      rw [SchwartzMap.smulLeftCLM_apply_apply hg]
      change (R.input.cutoff z : ℂ) • D₀.localizedFunction u z = R.input.localizedFunction u z
      by_cases hz : z ∈ tsupport R.input.cutoff
      · have hzt := (R.input.support_subset hz).1
        have hone : δ z = 1 := hδone z (Or.inr hz)
        simp only [AtlasChartCutoff.localizedFunction, hzt, ↓reduceIte]
        change (R.input.cutoff z : ℂ) • ((δ z : ℂ) • _) = _
        rw [hone, Complex.ofReal_one, one_smul]
      · simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
    have heq : L.toLinearMap = R.toLinearMap := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      change K₀.extendedFunction (T (D₀.localize R.chart_mem_atlas u)) x =
        R.output.extendedFunction (R.operator (R.input.localize R.chart_mem_atlas u)) x
      by_cases hx : x ∈ R.chart.source ∩ (B.chart R.output.frameIndex).baseSet
      · simp only [AtlasChartCutoff.extendedFunction, K₀, dite_eq_left hx]
        rw [hTapply, hinput, ← Complex.coe_smul, map_smul, map_smul, smul_smul]
        by_cases hz : R.chart x ∈ tsupport R.output.cutoff
        · rw [hδone _ (Or.inl hz), Complex.ofReal_one, one_mul]
        · simp [image_eq_zero_of_notMem_tsupport hz]
      · simp only [AtlasChartCutoff.extendedFunction, K₀, dite_eq_right hx]
    rw [← heq]
    refine ⟨1, fun _ ↦ L, ?_⟩
    simp only [Fin.sum_univ_one, sub_self]
    intro D K s t
    exact ⟨0, by intro u; simp⟩
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
  -- Every bounded realization comes from this same section map at the required real order.
  rw [← R.toLinearMap_cutoff χ ψ hχ hψ]
  intro D K s t
  have hlower : IsAtlasPseudodifferentialOperator A B (s - t) L.toLinearMap := by
    obtain ⟨N, hN⟩ := exists_nat_gt (m - (s - t))
    have h := hasSymbolExpansion_cutoffSymbol m L.symbol L.isSymbol
      L.output.cutoff L.input.cutoff L.output.smooth_cutoff L.input.smooth_cutoff
      L.output.compact_support L.input.compact_support N
    simp only [hterms, Finset.sum_const_zero, sub_zero] at h
    exact hpieceLower L (h.mono (by linarith))
  let T : AtlasPseudodifferentialOperator A B (s - t) := ⟨L.toLinearMap, hlower⟩
  refine ⟨(K.sobolevInclusion (s - (s - t)) t (by linarith)).comp
    (T.sobolevExtension D K s), ?_⟩
  intro u
  simp only [ContinuousLinearMap.comp_apply, T.sobolevExtension_smoothToSobolev,
    K.sobolevInclusion_smoothToSobolev]
  rfl

end AtlasPseudodifferentialPiece

end AtiyahSinger
