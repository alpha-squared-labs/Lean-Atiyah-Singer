/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompatibleChartSmoothing
public import AtiyahSinger.Analysis.TwoSidedCutoff

/-!
# Off-diagonal smoothing in a compatible chart

Public module ID: M0371.

When the two actual cutoffs have zero product, every diagonal coefficient
of the full amplitude expansion vanishes. Its reduced symbol has all real
orders, giving a smoothing map in the unchanged original atlas. The complete
operator is retained, including its off-diagonal action.

Source: SG III.3.8--3.15, two-sided cutoffs and the amplitude expansion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

set_option maxHeartbeats 600000 in

/-- Cutoffs with pointwise zero product give a smoothing operator in the original atlas. -/
theorem isAtlasSmoothingOperator_of_compatible_chart_cutoff_eq_zero {m : ℝ}
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : AtlasChartCutoff A c) (Dout : AtlasChartCutoff B c)
    (hio : tsupport Din.cutoff ⊆ c.symm ⁻¹' (B.chart Dout.frameIndex).baseSet)
    (hoi : tsupport Dout.cutoff ⊆ c.symm ⁻¹' (A.chart Din.frameIndex).baseSet)
    (hzero : ∀ z, Dout.cutoff z * Din.cutoff z = 0)
    (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
      →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))))
    (a : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex))
    (ha : IsSymbol univ m a)
    (hT : ∀ u x, T u x = quantize a u x)
    (I : A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))))
    (O : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
      →ₗ[ℂ] B.smoothSections)
    (hI : ∀ u z, I u z = Din.localizedFunction u z)
    (hO : ∀ v x, (O v).val x = Dout.extendedFunction v x) :
    IsAtlasSmoothingOperator A B (O.comp (T.toLinearMap.comp I)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let p := cutoffSymbol Dout.cutoff Din.cutoff a
  -- Every diagonal amplitude coefficient vanishes; retain the full reduced symbol.
  have hnear (x ξ : X) :
      (fun y ↦ cutoffAmplitude Dout.cutoff Din.cutoff a x y ξ) =ᶠ[nhds x]
        (fun _ ↦ 0) := by
    by_cases hx : Dout.cutoff x = 0
    · exact Filter.Eventually.of_forall (fun y ↦ by simp [cutoffAmplitude, hx])
    · filter_upwards [Dout.smooth_cutoff.continuous.continuousAt.eventually_ne hx] with y hy
      have hi : Din.cutoff y = 0 := (mul_eq_zero.mp (hzero y)).resolve_left hy
      simp [cutoffAmplitude, hi]
  have hterms (j : ℕ) :
      amplitudeExpansionTerm (cutoffAmplitude Dout.cutoff Din.cutoff a) j = 0 := by
    by_cases hj : j = 0
    · subst j
      rw [amplitudeExpansionTerm_zero]
      funext x ξ
      exact (hnear x ξ).eq_of_nhds
    · funext x ξ
      have hy (η : X) :
          iteratedFDeriv ℝ j (fun y ↦ cutoffAmplitude Dout.cutoff Din.cutoff a x y η) x = 0 := by
        simpa only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply] using
          ((hnear x η).iteratedFDeriv ℝ j).eq_of_nhds
      simp [amplitudeExpansionTerm, hy]
  have hp (l : ℝ) : IsSymbol univ l p := by
    obtain ⟨N, hN⟩ := exists_nat_gt (m - l)
    have h := hasSymbolExpansion_cutoffSymbol m a ha Dout.cutoff Din.cutoff
      Dout.smooth_cutoff Din.smooth_cutoff Dout.compact_support Din.compact_support N
    simp only [hterms, Finset.sum_const_zero, sub_zero] at h
    exact h.mono (by linarith)
  have hcp : HasCompactSupport p := hasCompactSupport_amplitudeSymbol _
    (hasCompactSupport_cutoffAmplitude a _ _ Dout.compact_support Din.compact_support)
  let P := amplitudeOperator m (cutoffAmplitude Dout.cutoff Din.cutoff a)
    (isAmplitude_cutoffAmplitude m a ha _ _ Dout.smooth_cutoff Din.smooth_cutoff)
    (hasCompactSupport_cutoffAmplitude a _ _ Dout.compact_support Din.compact_support)
  have hP : ∀ u z, P u z = quantize p u z := by
    intro u z
    rw [amplitudeOperator_apply]
    exact (congrFun (quantize_amplitudeSymbol m _
      (isAmplitude_cutoffAmplitude m a ha _ _ Dout.smooth_cutoff Din.smooth_cutoff)
      (hasCompactSupport_cutoffAmplitude a _ _ Dout.compact_support Din.compact_support) u)
        z).symm
  have hPa (u) (z) : P u z = Dout.cutoff z • T
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
        (fun w ↦ (Din.cutoff w : ℂ)) u) z := by
    rw [amplitudeOperator_apply, amplitudeApply_cutoffAmplitude m a ha _ _
      Dout.smooth_cutoff Din.smooth_cutoff Dout.compact_support Din.compact_support, hT]
  -- A common plateau reconstructs the original two cutoffs without squaring either.
  let U := c.target ∩ c.symm ⁻¹'
    ((A.chart Din.frameIndex).baseSet ∩ (B.chart Dout.frameIndex).baseSet)
  let K := tsupport Dout.cutoff ∪ tsupport Din.cutoff
  have hU : IsOpen U := c.isOpen_inter_preimage_symm
    ((A.chart Din.frameIndex).open_baseSet.inter (B.chart Dout.frameIndex).open_baseSet)
  have hK : IsCompact K := Dout.compact_support.union Din.compact_support
  have hKU : K ⊆ U := by
    intro z hz
    rcases hz with hz | hz
    · exact ⟨(Dout.support_subset hz).1, hoi hz, (Dout.support_subset hz).2⟩
    · exact ⟨(Din.support_subset hz).1, (Din.support_subset hz).2, hio hz⟩
  obtain ⟨V, hV, hKV, hVU, hcV⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hV hK.isClosed hKV
  have hs : tsupport χ = closure V := congrArg closure hsχ
  have hcχ : HasCompactSupport χ := by simpa [HasCompactSupport, hs] using hcV
  have hχU : tsupport χ ⊆ U := by rwa [hs]
  have hχone (z : X) (hz : z ∈ K) : χ z = 1 := (honeχ z).mp hz
  let Di : AtlasChartCutoff A c :=
    ⟨Din.frameIndex, χ, hχ, hcχ, fun z hz ↦ ⟨(hχU hz).1, (hχU hz).2.1⟩⟩
  let Do : AtlasChartCutoff B c :=
    ⟨Dout.frameIndex, χ, hχ, hcχ, fun z hz ↦ ⟨(hχU hz).1, (hχU hz).2.2⟩⟩
  obtain ⟨L⟩ := nonempty_atlasBundlePresentation A
  obtain ⟨H⟩ := nonempty_atlasBundlePresentation B
  obtain ⟨I₀, hI₀, _⟩ := Di.exists_localize_sobolev_of_mem_maximalAtlas hc L 0
  obtain ⟨O₀, hO₀, _⟩ := Do.exists_extend_sobolev_of_mem_maximalAtlas hc H 0
  have hinput (u : A.smoothSections) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
        (fun z ↦ (Din.cutoff z : ℂ)) (I₀ u) = I u := by
    apply SchwartzMap.ext
    intro z
    have hg : (fun z ↦ (Din.cutoff z : ℂ)).HasTemperateGrowth :=
      (Din.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp Din.smooth_cutoff)
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, hI₀, hI]
    by_cases hz : z ∈ tsupport Din.cutoff
    · simp [AtlasChartCutoff.localizedFunction, Di, (Din.support_subset hz).1,
        hχone z (Or.inr hz)]
    · simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
  have hmap : O₀.comp (P.toLinearMap.comp I₀) = O.comp (T.toLinearMap.comp I) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change (O₀ (P (I₀ u))).val x = (O (T (I u))).val x
    rw [hO₀, hO]
    by_cases hx : x ∈ c.source ∩ (B.chart Dout.frameIndex).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, Do, dite_eq_left hx]
      rw [hPa, hinput, ← Complex.coe_smul, map_smul, map_smul, smul_smul]
      by_cases hz : c x ∈ tsupport Dout.cutoff
      · rw [hχone _ (Or.inl hz), Complex.ofReal_one, one_mul]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    · simp [AtlasChartCutoff.extendedFunction, Do, hx]
  rw [← hmap]
  exact isAtlasSmoothingOperator_of_compatible_chart_symbol A B c hc Di Do P p hp hcp
    hP I₀ O₀ hI₀ hO₀

end AtiyahSinger
