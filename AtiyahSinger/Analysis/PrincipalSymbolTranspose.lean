/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import AtiyahSinger.Analysis.GlobalSymbolTranspose
public import AtiyahSinger.Analysis.GlobalTranspose

import AtiyahSinger.Analysis.CompactQuantization
import AtiyahSinger.Analysis.PseudodifferentialSpace

/-!
# The principal symbol of the actual global PDO transpose

Public module ID: M0872.

D02/D05/A02: combine the bilinear version of SG III.3.11 with (3.18), 3.17(iv),
and the actual principal quotient of 3.19. A local transpose representation must
retain both its actual smoothing remainder and its reflected dual principal class.
Finite assembly then identifies the principal class of the previously constructed
operator transpose. This is a consequence of the cited calculus, not a separately
numbered lemma in the book. Changes of positive density preserve this class while
in general changing the actual transpose map. The same local construction supplies
the map and its principal comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 2200000 in
-- The local representation keeps its actual chart pairing and all principal remainders together.
set_option maxRecDepth 4000 in
/-- A local transpose representation retains its actual map and reflected dual principal class. -/
theorem PseudodifferentialPiece.exists_representation_formalTranspose {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E))
    (hT : IsFormalTranspose μ L.toLinearMap T) :
    ∃ (N : ℕ) (L' : Fin N → PseudodifferentialPiece (n := n) (r := q) (q := r)
        (DualBundle F) (DualBundle E) m),
      IsSmoothingOperator μ (T - ∑ j, (L' j).toLinearMap) ∧
        globalPrincipalSymbolClass (DualBundle F) (DualBundle E) m
            (∑ j, (L' j).globalSymbol) =
          globalPrincipalSymbolTranspose (globalPrincipalSymbolClass E F m L.globalSymbol) := by
  classical
  let hμ : IsSmoothPositiveMeasure (n := n) μ := inferInstance
  let V := EuclideanSpace ℝ (Fin n)
  let H (s : ℕ) := EuclideanSpace ℂ (Fin s)
  let c := L.chart
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  -- A common plateau lies strictly inside the original chart and both original frames.
  let K := tsupport L.input.cutoff ∪ tsupport L.output.cutoff
  let U := c.target ∩ c.symm ⁻¹' (L.input.frame.baseSet ∩ L.output.frame.baseSet)
  have hK : IsCompact K := L.input.compact_support.union L.output.compact_support
  have hU : IsOpen U := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    (L.input.frame.open_baseSet.inter L.output.frame.open_baseSet)
  have hKU : K ⊆ U := by
    rintro z (hz | hz)
    · exact ⟨(L.input.support_subset hz).1, (L.input.support_subset hz).2,
        L.input_support_in_output_frame hz⟩
    · exact ⟨(L.output.support_subset hz).1, L.output_support_in_input_frame hz,
        (L.output.support_subset hz).2⟩
  have hcutoff (S O : Set V) (hS : IsCompact S) (hO : IsOpen O) (hSO : S ⊆ O) :
      ∃ β : V → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ O ∧
        S ⊆ interior {z | β z = 1} := by
    obtain ⟨W, hW, hSW, hWO, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure hS hO hSO
    obtain ⟨D, hD, hWD, hDO, hDcompact⟩ :=
      exists_open_between_and_isCompact_closure hWcompact hO hWO
    obtain ⟨β, hβ, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hD isClosed_closure hWD
    have hts : tsupport β = closure D := congrArg closure hsupp
    refine ⟨β, hβ, ?_, ?_, ?_⟩
    · change IsCompact (tsupport β)
      rwa [hts]
    · rwa [hts]
    · apply hSW.trans
      apply interior_maximal ?_ hW
      intro z hz
      exact (hone z).mp (subset_closure hz)
  obtain ⟨β, hβ, hcβ, hsβ, honeβ⟩ := hcutoff K U hK hU hKU
  have hβK (z : V) (hz : z ∈ K) : β z = 1 :=
    (interior_subset (s := {z : V | β z = 1})) (honeβ hz)
  obtain ⟨χ, hχ, hcχ, _, honeχ⟩ :=
    hcutoff (tsupport β) Set.univ hcβ isOpen_univ (Set.subset_univ _)
  -- Compactify the original Schwartz operator before transposing it.
  let p₀ := cutoffSymbol β β L.symbol
  have hp₀ : IsSymbol Set.univ m p₀ :=
    isSymbol_cutoffSymbol m L.symbol L.isSymbol β β hβ hβ hcβ hcβ
  let P₀ := amplitudeOperator m (cutoffAmplitude β β L.symbol)
    (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ)
    (hasCompactSupport_cutoffAmplitude L.symbol β β hcβ hcβ)
  have hP₀ (v : 𝓢(V, H r)) (z : V) : P₀ v z = quantize p₀ v z := by
    rw [show P₀ v z = amplitudeApply (cutoffAmplitude β β L.symbol) v z from
      amplitudeOperator_apply m _ _ _ v z]
    exact (congrFun (quantize_amplitudeSymbol m _
      (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ)
      (hasCompactSupport_cutoffAmplitude L.symbol β β hcβ hcβ) v) z).symm
  have hP₀support : HasOperatorSupport (tsupport β) P₀ := by
    simpa only [Set.union_self] using
      hasOperatorSupport_cutoff m L.symbol L.isSymbol β β hβ hβ hcβ hcβ
  have hp₀compact : HasCompactSupport p₀ :=
    hcβ.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_symbol_subset_of_hasOperatorSupport m p₀ hp₀ P₀ hP₀
        (tsupport β) (isClosed_tsupport β) hP₀support)
  let Q := localFormalTranspose m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
  let q₀ := transposeSymbol χ p₀
  have hq₀ : IsSymbol Set.univ m q₀ :=
    isSymbol_transposeSymbol m p₀ hp₀ hp₀compact χ hχ hcχ
  have hQ (v : 𝓢(V, H q)) (z : V) : Q v z = quantize q₀ v z :=
    localFormalTranspose_apply m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
      χ hχ hcχ honeχ v z
  have hQpair : IsSchwartzFormalTranspose P₀ Q :=
    isSchwartzFormalTranspose_localFormalTranspose m p₀ hp₀ P₀ hP₀
      (tsupport β) hcβ hP₀support
  -- The density and its inverse need smoothness only on this chart target.
  obtain ⟨ρ, hρ, hρpos, hρmap⟩ := hμ.exists_smooth_density c L.chart_mem_atlas
  have hβtarget : tsupport β ⊆ c.target := fun z hz ↦ (hsβ hz).1
  let A : V → H r →L[ℂ] H r :=
    cutoffMatrix β (fun z ↦ (ρ z)⁻¹ • ContinuousLinearMap.id ℂ (H r))
  let B : V → H q →L[ℂ] H q :=
    cutoffMatrix β (fun z ↦ ρ z • ContinuousLinearMap.id ℂ (H q))
  have hA : ContDiff ℝ ∞ A := contDiff_cutoffMatrix c.target c.open_target _
    ((hρ.inv (fun z hz ↦ ne_of_gt (hρpos z hz))).smul contDiffOn_const)
    β hβ hβtarget
  have hB : ContDiff ℝ ∞ B := contDiff_cutoffMatrix c.target c.open_target _
    (hρ.smul contDiffOn_const) β hβ hβtarget
  have hcA : HasCompactSupport A := hasCompactSupport_cutoffMatrix β _ hcβ
  have hcB : HasCompactSupport B := hasCompactSupport_cutoffMatrix β _ hcβ
  let W := (matrixMultiplierCLM A hA hcA).comp
    (Q.comp (matrixMultiplierCLM B hB hcB))
  let w := amplitudeSymbol (matrixAmplitude A B q₀)
  have hw : IsSymbol Set.univ m w :=
    isSymbol_amplitudeSymbol m _ (isAmplitude_matrixAmplitude m q₀ hq₀ A B hA hB)
      (hasCompactSupport_matrixAmplitude A B q₀ hcA hcB)
  have hW (v : 𝓢(V, H q)) (z : V) : W v z = quantize w v z := by
    change matrixMultiplierCLM A hA hcA (Q (matrixMultiplierCLM B hB hcB v)) z = _
    rw [matrixMultiplierCLM_apply, hQ]
    exact (quantize_matrixAmplitude m q₀ hq₀ A B hA hcA hB hcB v z).symm
  -- Induced dual frames and the swapped original cutoffs retain exactly the original witnesses.
  let I : BundleChartCutoff (r := q) (DualBundle F) c :=
    { frame := dualFrame F L.output.frame
      frame_mem_atlas := inferInstance
      cutoff := L.output.cutoff
      smooth_cutoff := L.output.smooth_cutoff
      compact_support := L.output.compact_support
      support_subset := by simpa only [dualFrame_baseSet] using L.output.support_subset }
  let O : BundleChartCutoff (r := r) (DualBundle E) c :=
    { frame := dualFrame E L.input.frame
      frame_mem_atlas := inferInstance
      cutoff := L.input.cutoff
      smooth_cutoff := L.input.smooth_cutoff
      compact_support := L.input.compact_support
      support_subset := by simpa only [dualFrame_baseSet] using L.input.support_subset }
  let LT : PseudodifferentialPiece (n := n) (r := q) (q := r)
      (DualBundle F) (DualBundle E) m :=
    { chart := c
      chart_mem_atlas := L.chart_mem_atlas
      input := I
      output := O
      input_support_in_output_frame := by
        simpa only [I, O, dualFrame_baseSet] using L.output_support_in_input_frame
      output_support_in_input_frame := by
        simpa only [I, O, dualFrame_baseSet] using L.input_support_in_output_frame
      operator := W
      symbol := w
      isSymbol := hw
      operator_apply := hW }
  -- Scalar chart transport applies to both actual bundle evaluations.
  have hchartIntegral (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (μ : Measure M)
      (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContinuousOn w c.target)
      (hpos : ∀ z ∈ c.target, 0 ≤ w z)
      (hmap : Measure.map c (μ.restrict c.source) =
        (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
      (f : M → ℂ) (hf : Continuous f) (hsupp : Function.support f ⊆ c.source) :
      (∫ x, f x ∂μ) = ∫ z in c.target, w z • f (c.symm z) := by
    classical
    -- Extend the target test by zero outside the prescribed chart target.
    let g : EuclideanSpace ℝ (Fin n) → ℂ := c.target.piecewise (fun z ↦ f (c.symm z)) (fun _ ↦ 0)
    have hg : Measurable g :=
      (hf.comp_continuousOn c.continuousOn_symm).measurable_piecewise
        continuousOn_const c.open_target.measurableSet
    have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
      ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
        |>.aemeasurable c.open_target.measurableSet
    calc
      (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ Function.notMem_support.mp (fun h ↦ hx (hsupp h)))
      _ = ∫ x in c.source, g (c x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
        simp [g, Set.piecewise_eq_of_mem, c.map_source hx, c.left_inv hx]
      _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
        (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
          hg.aestronglyMeasurable).symm
      _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
        rw [hmap]
        exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
          (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
      _ = ∫ z in c.target, w z • f (c.symm z) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        simp [g, Set.piecewise_eq_of_mem, hz, ENNReal.toReal_ofReal (hpos z hz)]
  have hpair : IsFormalTranspose μ L.toLinearMap LT.toLinearMap := by
    intro α u
    let u₀ := L.input.localize L.chart_mem_atlas u
    let a₀ := I.localize L.chart_mem_atlas α
    let b := matrixMultiplierCLM B hB hcB a₀
    have hu₀zero (z : V) (hz : z ∉ tsupport L.input.cutoff) : u₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz (L.input.tsupport_localizedFunction_subset u hz'))
    have ha₀zero (z : V) (hz : z ∉ tsupport L.output.cutoff) : a₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz (I.tsupport_localizedFunction_subset α hz'))
    have hβgrowth : (fun z : V ↦ (β z : ℂ)).HasTemperateGrowth :=
      (hcβ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hβ)
    have hβu : SchwartzMap.smulLeftCLM (H r) (fun z ↦ (β z : ℂ)) u₀ = u₀ := by
      ext z : 1
      rw [SchwartzMap.smulLeftCLM_apply_apply hβgrowth]
      by_cases hz : z ∈ tsupport L.input.cutoff
      · rw [hβK z (Or.inl hz), Complex.ofReal_one, one_smul]
      · rw [hu₀zero z hz, smul_zero]
    have hP₀apply (z : V) : P₀ u₀ z = β z • L.operator u₀ z := by
      rw [show P₀ u₀ z = amplitudeApply (cutoffAmplitude β β L.symbol) u₀ z from
        amplitudeOperator_apply m _ _ _ u₀ z]
      rw [amplitudeApply_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ hcβ hcβ,
        hβu, ← L.operator_apply]
    have hb (z : V) : b z = ρ z • a₀ z := by
      rw [show b z = B z (a₀ z) from matrixMultiplierCLM_apply B hB hcB a₀ z]
      change β z • (ρ z • a₀ z) = _
      by_cases hz : z ∈ tsupport L.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · rw [ha₀zero z hz, smul_zero, smul_zero]
    have hWapply (z : V) : W a₀ z = β z • ((ρ z)⁻¹ • Q b z) :=
      matrixMultiplierCLM_apply A hA hcA (Q b) z
    have hsmulDot {s : ℕ} (t : ℝ) (v w : H s) :
        (∑ i, (t • v) i * w i) = t • ∑ i, v i * w i := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (t • v i) * w i = t • (v i * w i)
      exact smul_mul_assoc t (v i) (w i)
    -- Both global pairings are transported using the same chart density and induced dual frames.
    have hleftChart :
        (∫ y, (O.extend L.chart_mem_atlas (W a₀)).val y (u.val y) ∂μ) =
          ∫ z, ρ z • ∑ i, W a₀ z i * u₀ z i := by
      let A : BundleChartCutoff (r := r) E c := L.input
      let D := O
      let v := W a₀
      let := A.frame_mem_atlas
      let := D.frame_mem_atlas
      have hframe : D.frame = @dualFrame r M _ E _ _ _ _ _ A.frame A.frame_mem_atlas := rfl
      have hcut : D.cutoff = A.cutoff := rfl
      have hc := L.chart_mem_atlas
      have hρ := hρ.continuousOn
      have hρpos : ∀ z ∈ c.target, 0 ≤ ρ z := fun z hz ↦ (hρpos z hz).le
      have hmap := hρmap
      have hpair (x : M) (hx : x ∈ A.frame.baseSet) (α : DualBundle E x) (w : E x) :
          α w = ∑ i, (dualFrame E A.frame ⟨x, α⟩).2 i * (A.frame ⟨x, w⟩).2 i := by
        have hexpand : ∑ i : Fin r, (A.frame ⟨x, w⟩).2 i •
            A.frame.symmL ℂ x (EuclideanSpace.single i 1) = w := by
          have heq := congrArg (A.frame.symmL ℂ x)
            ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((A.frame ⟨x, w⟩).2))
          calc
            _ = A.frame.symmL ℂ x ((A.frame ⟨x, w⟩).2) := by
              simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
            _ = w := by
              rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ hx]
              exact A.frame.symmL_continuousLinearMapAt hx w
        have hd := dualFrame_apply_snd E A.frame
          (fun y ↦ if h : y = x then h.symm ▸ α else 0) x hx
        simp only [dite_true] at hd
        rw [hd]
        conv_lhs => rw [← hexpand, map_sum]
        simp only [map_smul, smul_eq_mul, dualSectionInFrame, dite_true]
        exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
      rw [hchartIntegral c μ ρ hρ hρpos hmap (fun x ↦ (D.extend hc v).val x (u.val x))
        (by simpa only [dualSectionsEquiv] using
          (contMDiff_dualSection_eval E ⟨(D.extend hc v).val,
            (isSmoothSection_dualBundle_iff E _).1 (D.extend hc v).property⟩ u).continuous)
        (by
          intro x hx
          by_contra hxc
          apply hx
          change (D.extendedFunction v x) (u.val x) = 0
          simp [BundleChartCutoff.extendedFunction, hxc])]
      calc
        _ = ∫ z in c.target, ρ z • ∑ i, v z i * (A.localize hc u) z i := by
          apply setIntegral_congr_fun c.open_target.measurableSet
          intro z hz
          apply congrArg (fun a : ℂ ↦ ρ z • a)
          change (D.extendedFunction v (c.symm z)) (u.val (c.symm z)) =
            ∑ i, v z i * A.localizedFunction u z i
          simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
            c.map_target hz, ite_true, c.right_inv hz, hz]
          by_cases hb : z ∈ tsupport A.cutoff
          · have he := (A.support_subset hb).2
            have hd : c.symm z ∈ D.frame.baseSet := by
              rw [hframe, dualFrame_baseSet]
              exact he
            change (D.cutoff z : ℂ) * (D.frame.symmL ℂ (c.symm z) (v z))
              (u.val (c.symm z)) = _
            rw [hpair _ he, ← hframe]
            rw [← D.frame.continuousLinearMapAt_apply_of_mem ℂ hd,
              D.frame.continuousLinearMapAt_symmL hd]
            simp only [hcut, sectionInChart, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ ↦ by ring)
          · simp [hcut, image_eq_zero_of_notMem_tsupport hb]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro z hz
          change ρ z • ∑ i, v z i * A.localizedFunction u z i = 0
          simp [BundleChartCutoff.localizedFunction, hz])
    have hrightChart :
        (∫ y, α.val y ((L.output.extend L.chart_mem_atlas (L.operator u₀)).val y) ∂μ) =
          ∫ z, ρ z • ∑ j, a₀ z j * L.operator u₀ z j := by
      let A : BundleChartCutoff (r := q) F c := L.output
      let D := I
      let v := L.operator u₀
      let := A.frame_mem_atlas
      let := D.frame_mem_atlas
      have hframe : D.frame = @dualFrame q M _ F _ _ _ _ _ A.frame A.frame_mem_atlas := rfl
      have hcut : D.cutoff = A.cutoff := rfl
      have hc := L.chart_mem_atlas
      have hρ := hρ.continuousOn
      have hρpos : ∀ z ∈ c.target, 0 ≤ ρ z := fun z hz ↦ (hρpos z hz).le
      have hmap := hρmap
      have hpair (x : M) (hx : x ∈ A.frame.baseSet) (α : DualBundle F x) (w : F x) :
          α w = ∑ i, (dualFrame F A.frame ⟨x, α⟩).2 i * (A.frame ⟨x, w⟩).2 i := by
        have hexpand : ∑ i : Fin q, (A.frame ⟨x, w⟩).2 i •
            A.frame.symmL ℂ x (EuclideanSpace.single i 1) = w := by
          have heq := congrArg (A.frame.symmL ℂ x)
            ((EuclideanSpace.basisFun (Fin q) ℂ).sum_repr ((A.frame ⟨x, w⟩).2))
          calc
            _ = A.frame.symmL ℂ x ((A.frame ⟨x, w⟩).2) := by
              simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
            _ = w := by
              rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ hx]
              exact A.frame.symmL_continuousLinearMapAt hx w
        have hd := dualFrame_apply_snd F A.frame
          (fun y ↦ if h : y = x then h.symm ▸ α else 0) x hx
        simp only [dite_true] at hd
        rw [hd]
        conv_lhs => rw [← hexpand, map_sum]
        simp only [map_smul, smul_eq_mul, dualSectionInFrame, dite_true]
        exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
      rw [hchartIntegral c μ ρ hρ hρpos hmap (fun x ↦ α.val x ((A.extend hc v).val x))
        (by simpa only [dualSectionsEquiv] using
          (contMDiff_dualSection_eval F
            ⟨α.val, (isSmoothSection_dualBundle_iff F α.val).1 α.property⟩
            (A.extend hc v)).continuous)
        (by
          intro x hx
          by_contra hxc
          apply hx
          change α.val x (A.extendedFunction v x) = 0
          simp [BundleChartCutoff.extendedFunction, hxc])]
      calc
        _ = ∫ z in c.target, ρ z • ∑ i, (D.localize hc α) z i * v z i := by
          apply setIntegral_congr_fun c.open_target.measurableSet
          intro z hz
          apply congrArg (fun a : ℂ ↦ ρ z • a)
          change α.val (c.symm z) (A.extendedFunction v (c.symm z)) =
            ∑ i, D.localizedFunction α z i * v z i
          simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
            c.map_target hz, ite_true, c.right_inv hz, hz]
          by_cases hb : z ∈ tsupport A.cutoff
          · have he := (A.support_subset hb).2
            rw [map_smul, smul_eq_mul, hpair _ he]
            simp only [hframe, hcut, sectionInChart, PiLp.smul_apply, smul_eq_mul]
            rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
              A.frame.continuousLinearMapAt_symmL he]
            simp only [Finset.mul_sum, mul_assoc]
          · simp [hcut, image_eq_zero_of_notMem_tsupport hb]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro z hz
          change ρ z • ∑ i, D.localizedFunction α z i * v z i = 0
          simp [BundleChartCutoff.localizedFunction, hz])
    have hleft (z : V) : (ρ z • ∑ i, W a₀ z i * u₀ z i) =
        ∑ i, Q b z i * u₀ z i := by
      by_cases hz : z ∈ tsupport L.input.cutoff
      · rw [hWapply, hβK z (Or.inl hz), one_smul, hsmulDot,
          smul_smul, mul_inv_cancel₀ (ne_of_gt (hρpos z (L.input.support_subset hz).1)),
          one_smul]
      · simp [hu₀zero z hz]
    have hright (z : V) : (∑ j, b z j * P₀ u₀ z j) =
        ρ z • ∑ j, a₀ z j * L.operator u₀ z j := by
      rw [hb, hP₀apply]
      by_cases hz : z ∈ tsupport L.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul, hsmulDot]
      · simp [ha₀zero z hz]
    change (∫ y, (O.extend L.chart_mem_atlas (W a₀)).val y (u.val y) ∂μ) =
      ∫ y, α.val y ((L.output.extend L.chart_mem_atlas (L.operator u₀)).val y) ∂μ
    rw [hleftChart, hrightChart]
    simp_rw [hleft]
    exact (hQpair u₀ b).trans (integral_congr_ae (Filter.Eventually.of_forall hright))
  -- The original pairing identifies the supplied map with this very same local piece.
  have hmap : T = LT.toLinearMap :=
    IsFormalTranspose.unique L.toLinearMap T LT.toLinearMap hT hpair
  refine ⟨1, fun _ ↦ LT, ?_, ?_⟩
  · rw [hmap, Fin.sum_univ_one, sub_self]
    let K₀ : SmoothKernel (n := n) (r := q) (q := r) (DualBundle F) (DualBundle E) :=
      { toFun := fun _ _ ↦ 0
        isSmooth := by
          intro e f _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames (DualBundle F) (DualBundle E) (fun _ _ ↦ 0) e f z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
            ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
    refine ⟨K₀, ?_⟩
    ext u x
    simp [SmoothKernel.toLinearMap, SmoothKernel.apply, K₀]
  rw [Fin.sum_univ_one, globalPrincipalSymbolTranspose_class]
  apply (globalPrincipalSymbolClass_eq_iff (DualBundle F) (DualBundle E) m _ _).mpr
  -- Retain all three remainders of order m-1 before canceling the density weights.
  let a : SymbolFunction n r q := fun z ξ ↦ cutoffAmplitude β β L.symbol z z ξ
  have hpLow : IsSymbol Set.univ (m - 1) (p₀ - a) := by
    have h := hasSymbolExpansion_cutoffSymbol m L.symbol L.isSymbol β β hβ hβ hcβ hcβ 1
    simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero] using h
  have hqLow : IsSymbol Set.univ (m - 1) (q₀ - symbolTranspose p₀) :=
    isSymbol_transposeSymbol_sub m p₀ hp₀ hp₀compact χ hχ hcχ (by
      intro z hz
      apply interior_subset (honeχ _)
      exact tsupport_symbol_subset_of_hasOperatorSupport m p₀ hp₀ P₀ hP₀
        (tsupport β) (isClosed_tsupport β) hP₀support hz)
  have htSub (p p' : SymbolFunction n r q) :
      symbolTranspose (p - p') = symbolTranspose p - symbolTranspose p' := by
    ext z ξ v i
    simp only [symbolTranspose_apply, Pi.sub_apply, sub_apply,
      PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  let d : SymbolFunction n q r := w - matrixSymbol A B (symbolTranspose a)
  have hd : IsSymbol Set.univ (m - 1) d := by
    have h₁ := isSymbol_amplitudeSymbol_matrixAmplitude_sub m q₀ hq₀ A B hA hcA hB hcB
    have h₂ := isSymbol_matrixSymbol Set.univ isOpen_univ (m - 1)
      (q₀ - symbolTranspose p₀) hqLow A B hA.contDiffOn hB.contDiffOn
    have h₃ := isSymbol_matrixSymbol Set.univ isOpen_univ (m - 1)
      (symbolTranspose (p₀ - a))
      (isSymbol_symbolTranspose Set.univ isOpen_univ (m - 1) _ hpLow)
      A B hA.contDiffOn hB.contDiffOn
    have heq : d = (w - matrixSymbol A B q₀) +
        matrixSymbol A B (q₀ - symbolTranspose p₀) +
        matrixSymbol A B (symbolTranspose (p₀ - a)) := by
      rw [htSub]
      ext z ξ v
      simp only [d, matrixSymbol, Pi.sub_apply, Pi.add_apply,
        sub_apply, add_apply,
        ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [heq]
    exact (h₁.add isOpen_univ h₂).add isOpen_univ h₃
  -- A final compact plateau packages that lower-order difference as a genuine global symbol.
  let b := zeroExtendedSymbol Set.univ β d
  have hb : IsSymbol Set.univ (m - 1) b :=
    isSymbol_zeroExtendedSymbol Set.univ isOpen_univ (m - 1) β hβ hcβ
      (Set.subset_univ _) d hd
  have hbc : HasCompactSupport b :=
    hasCompactSupport_zeroExtendedSymbol Set.univ β d hcβ
  let R : PseudodifferentialPiece (n := n) (r := q) (q := r)
      (DualBundle F) (DualBundle E) (m - 1) :=
    { chart := c
      chart_mem_atlas := L.chart_mem_atlas
      input := I
      output := O
      input_support_in_output_frame := LT.input_support_in_output_frame
      output_support_in_input_frame := LT.output_support_in_input_frame
      operator := quantizeSchwartz (m - 1) b hb hbc
      symbol := b
      isSymbol := hb
      operator_apply := quantizeSchwartz_apply (m - 1) b hb hbc }
  have heq : LT.globalSymbolFunction - globalSymbolTranspose L.globalSymbolFunction =
      R.globalSymbolFunction := by
    funext x ξ
    let := I.frame_mem_atlas
    let := O.frame_mem_atlas
    by_cases hx : x ∈ c.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
    · have hz : c x ∈ symbolChartDomain E F c L.input.frame L.output.frame :=
        ⟨⟨c.map_source hx.1.1, by simpa only [Set.mem_preimage, c.left_inv hx.1.1] using hx.1.2⟩,
          by simpa only [Set.mem_preimage, c.left_inv hx.1.1] using hx.2⟩
      have hz' : c x ∈ symbolChartDomain (DualBundle F) (DualBundle E)
          c I.frame O.frame := by
        simpa only [I, O, symbolChartDomain_dualFrame] using hz
      have hI : x ∈ I.frame.baseSet := by simpa only [I, dualFrame_baseSet] using hx.2
      have hO : x ∈ O.frame.baseSet := by simpa only [O, dualFrame_baseSet] using hx.1.2
      have hcoord :
          globalSymbolInChart (DualBundle F) (DualBundle E) LT.globalSymbolFunction
              c I.frame O.frame (c x) (covectorInChart c x ξ) -
            globalSymbolInChart (DualBundle F) (DualBundle E)
              (globalSymbolTranspose L.globalSymbolFunction)
              c I.frame O.frame (c x) (covectorInChart c x ξ) =
          globalSymbolInChart (DualBundle F) (DualBundle E) R.globalSymbolFunction
              c I.frame O.frame (c x) (covectorInChart c x ξ) := by
        rw [LT.globalSymbolInChart_globalSymbolFunction _ _ hz',
          R.globalSymbolInChart_globalSymbolFunction _ _ hz']
        change ((L.input.cutoff (c x) * L.output.cutoff (c x) : ℝ) : ℂ) •
            w (c x) (covectorInChart c x ξ) -
            globalSymbolInChart (DualBundle F) (DualBundle E)
              (globalSymbolTranspose L.globalSymbolFunction) c
              (dualFrame F L.output.frame) (dualFrame E L.input.frame)
              (c x) (covectorInChart c x ξ) =
          ((L.input.cutoff (c x) * L.output.cutoff (c x) : ℝ) : ℂ) •
            b (c x) (covectorInChart c x ξ)
        rw [globalSymbolInChart_globalSymbolTranspose _ _ _ _ _ _ hz.1.2 hz.2]
        have htrans (η : V) :
            symbolTranspose (globalSymbolInChart E F L.globalSymbolFunction
                c L.input.frame L.output.frame) (c x) η =
              ((L.input.cutoff (c x) * L.output.cutoff (c x) : ℝ) : ℂ) •
                symbolTranspose L.symbol (c x) η := by
          ext v i
          simp only [symbolTranspose_apply]
          rw [L.globalSymbolInChart_globalSymbolFunction (c x) (-η) hz]
          simp only [smul_apply, PiLp.smul_apply, smul_eq_mul, symbolTranspose_apply,
            mul_assoc, Finset.mul_sum,
            mul_comm (L.output.cutoff (c x))]
        rw [htrans]
        by_cases hin : L.input.cutoff (c x) = 0
        · simp [hin]
        have hone : β (c x) = 1 := hβK _ (Or.inl (subset_tsupport _ hin))
        have ha (η : V) : symbolTranspose a (c x) η =
            symbolTranspose L.symbol (c x) η := by
          ext v i
          simp [symbolTranspose_apply, a, cutoffAmplitude, hone]
        have hdiag (η : V) : matrixSymbol A B (symbolTranspose a) (c x) η =
            symbolTranspose L.symbol (c x) η := by
          rw [show matrixSymbol A B (symbolTranspose a) (c x) η =
            (A (c x)).comp ((symbolTranspose a (c x) η).comp (B (c x))) from rfl, ha]
          ext v
          simp only [A, B, cutoffMatrix, hone, one_smul, ContinuousLinearMap.comp_apply,
            smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.map_smul_of_tower,
            smul_smul, one_mul, inv_mul_cancel₀ (ne_of_gt (hρpos _ (c.map_source hx.1.1))),
            one_smul]
        simp only [b, zeroExtendedSymbol, Set.mem_univ, ite_true, hone,
          Complex.ofReal_one, one_smul, d, Pi.sub_apply, hdiag, smul_sub]
      -- Recover the actual fiber map from its coordinates in these same induced dual frames.
      rw [globalSymbolInChart_covectorInChart _ _ _ c L.chart_mem_atlas I.frame O.frame
          x hx.1.1 ξ,
        globalSymbolInChart_covectorInChart _ _ _ c L.chart_mem_atlas I.frame O.frame
          x hx.1.1 ξ,
        globalSymbolInChart_covectorInChart _ _ _ c L.chart_mem_atlas I.frame O.frame
          x hx.1.1 ξ] at hcoord
      ext α : 1
      have hv := congrArg (fun D : H q →L[ℂ] H r ↦
        O.frame.symmL ℂ x (D (I.frame.continuousLinearMapAt ℂ x α))) hcoord
      simpa only [Pi.sub_apply, sub_apply, ContinuousLinearMap.comp_apply, map_sub,
        I.frame.symmL_continuousLinearMapAt hI,
        O.frame.symmL_continuousLinearMapAt hO] using hv
    · have hx' : x ∉ c.source ∩ (dualFrame F L.output.frame).baseSet ∩
          (dualFrame E L.input.frame).baseSet := by
        simpa only [dualFrame_baseSet, Set.inter_right_comm] using hx
      have hxL : x ∉ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet := hx
      ext α v
      simp only [Pi.sub_apply, sub_apply, globalSymbolTranspose_apply,
        PseudodifferentialPiece.globalSymbolFunction, LT, R, I, O,
        ite_eq_right hxL, ite_eq_right hx', zero_apply, map_zero, sub_zero]
  change IsGlobalSymbol (DualBundle F) (DualBundle E) (m - 1)
    (LT.globalSymbolFunction - globalSymbolTranspose L.globalSymbolFunction)
  rw [heq]
  exact R.isGlobalSymbol_globalSymbolFunction

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- The actual PDO transpose has the reflected dual of the original principal class. -/
theorem principalSymbol_formalTranspose :
    P.formalTranspose.principalSymbol = globalPrincipalSymbolTranspose P.principalSymbol := by
  classical
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  choose T hT horder using fun j : Fin N ↦ (L j).exists_formalTranspose (μ := μ)
  let Q (j : Fin N) : pseudodifferentialSpace (DualBundle F) (DualBundle E) μ m :=
    ⟨T j, horder j⟩
  let R : pseudodifferentialSpace (DualBundle F) (DualBundle E) μ m :=
    ⟨K.transpose.toLinearMap μ,
      IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨K.transpose, rfl⟩⟩
  let S := pseudodifferentialOperatorOfSpace ((∑ j, Q j) + R)
  -- Transpose the actual finite sum using the same density and the same kernel.
  have hadd
      (P₁ P₂ : smoothSections (n := n) (r := r) E →ₗ[ℂ]
        smoothSections (n := n) (r := q) F)
      (T₁ T₂ : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
        smoothSections (n := n) (r := r) (DualBundle E))
      (h₁ : IsFormalTranspose μ P₁ T₁) (h₂ : IsFormalTranspose μ P₂ T₂) :
      IsFormalTranspose μ (P₁ + P₂) (T₁ + T₂) := by
    intro α u
    have hT₁ : Integrable (fun x ↦ (T₁ α).val x (u.val x)) μ :=
      integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T₁ α)) u
    have hT₂ : Integrable (fun x ↦ (T₂ α).val x (u.val x)) μ :=
      integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T₂ α)) u
    have hP₁ : Integrable (fun x ↦ α.val x ((P₁ u).val x)) μ :=
      integrable_dualSection_eval F μ ((dualSectionsEquiv F).symm α) (P₁ u)
    have hP₂ : Integrable (fun x ↦ α.val x ((P₂ u).val x)) μ :=
      integrable_dualSection_eval F μ ((dualSectionsEquiv F).symm α) (P₂ u)
    change (∫ x, ((T₁ α).val x + (T₂ α).val x) (u.val x) ∂μ) =
      ∫ x, α.val x ((P₁ u).val x + (P₂ u).val x) ∂μ
    simp only [add_apply, map_add]
    rw [integral_add hT₁ hT₂, integral_add hP₁ hP₂, h₁ α u, h₂ α u]
  have hsum (s : Finset (Fin N)) :
      IsFormalTranspose μ ((∑ j ∈ s, (L j).toLinearMap) + K.toLinearMap μ)
        ((∑ j ∈ s, T j) + K.transpose.toLinearMap μ) := by
    induction s using Finset.induction_on with
    | empty => simpa using K.isFormalTranspose_toLinearMap (μ := μ)
    | @insert j s hj ih =>
      simpa only [Finset.sum_insert hj, add_assoc] using hadd _ _ _ _ (hT j) ih
  have hrepr : P.toLinearMap = (∑ j, (L j).toLinearMap) + K.toLinearMap μ := by
    rw [hK]
    abel
  have hS : IsFormalTranspose μ P.toLinearMap S.toLinearMap := by
    rw [hrepr]
    simpa only [S, pseudodifferentialOperatorOfSpace, Submodule.coe_add,
      Submodule.coe_sum, Q, R] using hsum Finset.univ
  have heq : P.formalTranspose.toLinearMap = S.toLinearMap :=
    IsFormalTranspose.unique P.toLinearMap _ _ P.isFormalTranspose_formalTransposeLinearMap hS
  rw [P.formalTranspose.principalSymbol_eq_of_toLinearMap_eq μ S heq]
  -- Compute the same assembled map through the linear principal-symbol map.
  let σ := principalSymbolLinearMap (n := n) (r := q) (q := r)
    (DualBundle F) (DualBundle E) μ m
  have hpiece (j : Fin N) : σ (Q j) =
      globalPrincipalSymbolTranspose (globalPrincipalSymbolClass E F m (L j).globalSymbol) := by
    obtain ⟨N', L', hrem, hclass⟩ := (L j).exists_representation_formalTranspose (T j) (hT j)
    exact ((pseudodifferentialOperatorOfSpace (Q j)).principalSymbol_eq_of_representation
      N' L' hrem).trans hclass
  have hkernel : σ R = 0 :=
    (pseudodifferentialOperatorOfSpace R).principalSymbol_eq_zero_of_isSmoothingOperator
      ⟨K.transpose, rfl⟩
  change σ ((∑ j, Q j) + R) = _
  rw [map_add, map_sum, hkernel, add_zero]
  simp_rw [hpiece]
  rw [P.principalSymbol_eq_of_representation N L ⟨K, hK⟩, map_sum]
  have hfinite (s : Finset (Fin N)) :
      globalPrincipalSymbolTranspose
          (∑ j ∈ s, globalPrincipalSymbolClass E F m (L j).globalSymbol) =
        ∑ j ∈ s, globalPrincipalSymbolTranspose
          (globalPrincipalSymbolClass E F m (L j).globalSymbol) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, globalPrincipalSymbolTranspose_zero]
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, globalPrincipalSymbolTranspose_add, ih]
  exact (hfinite Finset.univ).symm

/-- The transpose principal class is independent of positive density for the same original map. -/
theorem principalSymbol_formalTranspose_eq_of_toLinearMap_eq
    (ν : Measure M) [IsSmoothPositiveMeasure (n := n) ν]
    (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F ν m)
    (h : P.toLinearMap = Q.toLinearMap) :
    P.formalTranspose.principalSymbol = Q.formalTranspose.principalSymbol := by
  -- The original maps have one density-independent class before taking its dual transpose.
  rw [P.principalSymbol_formalTranspose, Q.principalSymbol_formalTranspose,
    P.principalSymbol_eq_of_toLinearMap_eq ν Q h]

end PseudodifferentialOperator

end AtiyahSinger
