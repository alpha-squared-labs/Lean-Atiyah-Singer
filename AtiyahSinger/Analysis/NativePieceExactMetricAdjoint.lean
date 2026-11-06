/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricPseudodifferentialAdjoint

/-!
# Exact native adjoints in the original chart with swapped cutoffs

Public module ID: M0813.

The weighted local construction gives the exact metric adjoint as a single
piece in the original chart, with the original input and output cutoffs exchanged.
It retains the complete amplitude-reduced symbol and every lower-order term.
A common plateau supports the local formal adjoint, and the original density
and Gram weights give its global integral adjunction. Uniqueness identifies
this piece with the originally specified native metric adjoint.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate SchwartzMap Matrix.Norms.Elementwise

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

set_option maxHeartbeats 3000000 in
-- Normalize the local Gram weights and adjoint while retaining the chart and cutoffs.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- The full metric adjoint of a native piece retains its chart and swaps its cutoffs. -/
theorem PseudodifferentialPiece.exists_exact_metricFormalAdjoint_piece {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) :
    let Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m :=
      ⟨L.toLinearMap, L.isPseudodifferentialOperator m⟩
    ∃ T : PseudodifferentialPiece (n := n) (r := q) (q := r) F E m,
      T.chart = L.chart ∧ T.input.cutoff = L.output.cutoff ∧
        T.output.cutoff = L.input.cutoff ∧
          T.toLinearMap = (Q.metricFormalAdjoint h k).toLinearMap := by
  intro Q
  classical
  let TModel := EuclideanSpace ℝ (Fin n)
  let SourceModel := EuclideanSpace ℂ (Fin r)
  let TargetModel := EuclideanSpace ℂ (Fin q)
  -- The specified metrics give smooth invertible Gram weights in the chosen frames.
  have hgramE (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (e : Trivialization SourceModel (π SourceModel E)) [MemTrivializationAtlas e] :
      ∃ G : TModel → (SourceModel →L[ℂ] SourceModel),
        ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ∀ z ∈ c.target ∩ c.symm ⁻¹' e.baseSet,
          (∃ L : SourceModel ≃L[ℂ] SourceModel, L.toContinuousLinearMap = G z) ∧
          (∀ u v : SourceModel,
            h.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
              inner ℂ u (G z v)) := by
    classical
    let toOp : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (SourceModel →L[ℂ] SourceModel) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : TModel) : SourceModel →L[ℂ] SourceModel := toOp (h.gramMatrix e (c.symm z))
    have hG (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, TModel)) (n := ∞) hc) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact (((h.contMDiffOn_gram e i j).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hpair (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) (u v : SourceModel) :
        h.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
          inner ℂ u (G z v) := by
      have hcoords (a : SourceModel) : (e ⟨c.symm z, e.symmL ℂ (c.symm z) a⟩).2 = a := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 a
      rw [h.pairing_eq_gramMatrix e _ hz.2, hcoords u, hcoords v, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, conj (u i) * h.gramMatrix e (c.symm z) i j * v j) =
        (∑ j, h.gramMatrix e (c.symm z) i j * v j) * conj (u i)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hequiv (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) :
        ∃ L : SourceModel ≃L[ℂ] SourceModel, L.toContinuousLinearMap = G z := by
      have hinj : Function.Injective (G z) := by
        intro u v huv
        have hzG : G z (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hzpair := hpair z hz (u - v) (u - v)
        rw [hzG, inner_zero_right] at hzpair
        have hzvec : e.symmL ℂ (c.symm z) (u - v) = 0 :=
          (h.toCore _).definite _ hzpair
        have hzcoords := congrArg (e.continuousLinearMapAt ℂ (c.symm z)) hzvec
        rw [e.continuousLinearMapAt_symmL hz.2, map_zero] at hzcoords
        exact sub_eq_zero.mp hzcoords
      exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨G, fun z hz ↦ (hG z hz).contDiffWithinAt, ?_, ?_⟩
    · intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    · intro z hz
      exact ⟨hequiv z hz, hpair z hz⟩
  have hgramF (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (e : Trivialization TargetModel (π TargetModel F)) [MemTrivializationAtlas e] :
      ∃ G : TModel → (TargetModel →L[ℂ] TargetModel),
        ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ∀ z ∈ c.target ∩ c.symm ⁻¹' e.baseSet,
          (∃ L : TargetModel ≃L[ℂ] TargetModel, L.toContinuousLinearMap = G z) ∧
          (∀ u v : TargetModel,
            k.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
              inner ℂ u (G z v)) := by
    classical
    let toOp : Matrix (Fin q) (Fin q) ℂ →L[ℝ] (TargetModel →L[ℂ] TargetModel) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : TModel) : TargetModel →L[ℂ] TargetModel := toOp (k.gramMatrix e (c.symm z))
    have hG (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, TModel)) (n := ∞) hc) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact (((k.contMDiffOn_gram e i j).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hpair (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) (u v : TargetModel) :
        k.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
          inner ℂ u (G z v) := by
      have hcoords (a : TargetModel) : (e ⟨c.symm z, e.symmL ℂ (c.symm z) a⟩).2 = a := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 a
      rw [k.pairing_eq_gramMatrix e _ hz.2, hcoords u, hcoords v, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, conj (u i) * k.gramMatrix e (c.symm z) i j * v j) =
        (∑ j, k.gramMatrix e (c.symm z) i j * v j) * conj (u i)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hequiv (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) :
        ∃ L : TargetModel ≃L[ℂ] TargetModel, L.toContinuousLinearMap = G z := by
      have hinj : Function.Injective (G z) := by
        intro u v huv
        have hzG : G z (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hzpair := hpair z hz (u - v) (u - v)
        rw [hzG, inner_zero_right] at hzpair
        have hzvec : e.symmL ℂ (c.symm z) (u - v) = 0 :=
          (k.toCore _).definite _ hzpair
        have hzcoords := congrArg (e.continuousLinearMapAt ℂ (c.symm z)) hzvec
        rw [e.continuousLinearMapAt_symmL hz.2, map_zero] at hzcoords
        exact sub_eq_zero.mp hzcoords
      exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨G, fun z hz ↦ (hG z hz).contDiffWithinAt, ?_, ?_⟩
    · intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    · intro z hz
      exact ⟨hequiv z hz, hpair z hz⟩
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
  -- A reversed piece uses the same chart and frames, with the prescribed density weights.
  have hpiece (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) :
      ∃ T : PseudodifferentialPiece (n := n) (r := q) (q := r) F E m,
        T.chart = L.chart ∧ T.input.cutoff = L.output.cutoff ∧
          T.output.cutoff = L.input.cutoff ∧
            IsMetricFormalAdjoint h k μ L.toLinearMap T.toLinearMap := by
    classical
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
    -- Apply the common plateau on both sides to obtain compact operator support.
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
    let Q := localFormalAdjoint m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
    let q₀ := adjointSymbol χ p₀
    have hq₀ : IsSymbol Set.univ m q₀ :=
      isSymbol_adjointSymbol m p₀ hp₀ hp₀compact χ hχ hcχ
    have hQ (v : 𝓢(V, H q)) (z : V) : Q v z = quantize q₀ v z :=
      localFormalAdjoint_apply m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
        χ hχ hcχ honeχ v z
    have hQpair : IsSchwartzFormalAdjoint P₀ Q :=
      isSchwartzFormalAdjoint_localFormalAdjoint m p₀ hp₀ P₀ hP₀
        (tsupport β) hcβ hP₀support
    -- The density and its inverse need smoothness only on this chart target.
    obtain ⟨ρ, hρ, hρpos, hρmap⟩ := hμ.exists_smooth_density c L.chart_mem_atlas
    have hβtarget : tsupport β ⊆ c.target := fun z hz ↦ (hsβ hz).1
    obtain ⟨GE, hGE, hGEinv, hGEpair⟩ := hgramE c L.chart_mem_atlas L.input.frame
    obtain ⟨GF, hGF, _, hGFpair⟩ := hgramF c L.chart_mem_atlas L.output.frame
    have hUE : U ⊆ c.target ∩ c.symm ⁻¹' L.input.frame.baseSet :=
      fun z hz ↦ ⟨hz.1, hz.2.1⟩
    have hUF : U ⊆ c.target ∩ c.symm ⁻¹' L.output.frame.baseSet :=
      fun z hz ↦ ⟨hz.1, hz.2.2⟩
    let A : V → H r →L[ℂ] H r := cutoffMatrix β (fun z ↦ (ρ z)⁻¹ • (GE z).inverse)
    let B : V → H q →L[ℂ] H q := cutoffMatrix β (fun z ↦ ρ z • GF z)
    have hA : ContDiff ℝ ∞ A := contDiff_cutoffMatrix U hU _
      (((hρ.mono (fun z hz ↦ hz.1)).inv
        (fun z hz ↦ ne_of_gt (hρpos z hz.1))).smul (hGEinv.mono hUE)) β hβ hsβ
    have hB : ContDiff ℝ ∞ B := contDiff_cutoffMatrix U hU _
      ((hρ.mono (fun z hz ↦ hz.1)).smul (hGF.mono hUF)) β hβ hsβ
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
    let LT : PseudodifferentialPiece (n := n) (r := q) (q := r) F E m :=
      { chart := c
        chart_mem_atlas := L.chart_mem_atlas
        input := L.output
        output := L.input
        input_support_in_output_frame := L.output_support_in_input_frame
        output_support_in_input_frame := L.input_support_in_output_frame
        operator := W
        symbol := w
        isSymbol := hw
        operator_apply := hW }
    refine ⟨LT, rfl, rfl, rfl, ?_⟩
    intro u v
    let u₀ := L.input.localize L.chart_mem_atlas u
    let v₀ := L.output.localize L.chart_mem_atlas v
    let b := matrixMultiplierCLM B hB hcB v₀
    have hu₀zero (z : V) (hz : z ∉ tsupport L.input.cutoff) : u₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz (L.input.tsupport_localizedFunction_subset u hz'))
    have hv₀zero (z : V) (hz : z ∉ tsupport L.output.cutoff) : v₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz (L.output.tsupport_localizedFunction_subset v hz'))
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
    have hb (z : V) : b z = ρ z • GF z (v₀ z) := by
      rw [show b z = B z (v₀ z) from matrixMultiplierCLM_apply B hB hcB v₀ z]
      change β z • (ρ z • GF z (v₀ z)) = _
      by_cases hz : z ∈ tsupport L.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · rw [hv₀zero z hz, map_zero, smul_zero, smul_zero]
    have hWapply (z : V) :
        W v₀ z = β z • ((ρ z)⁻¹ • (GE z).inverse (Q b z)) :=
      matrixMultiplierCLM_apply A hA hcA (Q b) z
    -- Move each global pairing into this single original chart using its prescribed density.
    have hleftChart : k.sectionPairing μ
        (L.output.extend L.chart_mem_atlas (L.operator u₀)) v =
        ∫ z, inner ℂ (L.operator u₀ z) (ρ z • GF z (v₀ z)) := by
      let A := L.output
      let G := GF
      let hc := L.chart_mem_atlas
      let u := v
      let v := L.operator u₀
      let h := k
      have hG : ∀ z ∈ tsupport A.cutoff, ∀ a b : H q,
          h.pairing (L.chart.symm z) (A.frame.symmL ℂ (L.chart.symm z) a)
            (A.frame.symmL ℂ (L.chart.symm z) b) = inner ℂ a (G z b) := by
        intro z hz a b
        exact (hGFpair z (L.output.support_subset hz)).2 a b
      rw [SmoothHermitianMetric.sectionPairing]
      rw [hchartIntegral L.chart μ ρ hρ.continuousOn
        (fun z hz ↦ (hρpos z hz).le) hρmap _
        (h.contMDiff_pairing (A.extend hc v) u).continuous (by
          intro x hx
          by_contra hxc
          apply hx
          change h.pairing x (A.extendedFunction v x) (u.val x) = 0
          rw [show A.extendedFunction v x = 0 by
            simp [BundleChartCutoff.extendedFunction, hxc]]
          let : InnerProductSpace.Core ℂ (F x) := h.toCore x
          exact InnerProductSpace.Core.inner_zero_left _)]
      calc
        _ = ∫ z in L.chart.target, inner ℂ (v z) (ρ z • G z (A.localize hc u z)) := by
          apply setIntegral_congr_fun L.chart.open_target.measurableSet
          intro z hz
          change ρ z • h.pairing (L.chart.symm z) (A.extendedFunction v (L.chart.symm z))
            (u.val (L.chart.symm z)) = inner ℂ (v z) (ρ z • G z (A.localizedFunction u z))
          simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
            L.chart.map_target hz, ite_true, L.chart.right_inv hz, hz]
          by_cases hb : z ∈ tsupport A.cutoff
          · have he := (A.support_subset hb).2
            have hu : u.val (L.chart.symm z) =
                A.frame.symmL ℂ (L.chart.symm z) (sectionInChart F L.chart A.frame u.val z) := by
              symm
              rw [sectionInChart, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
                A.frame.symmL_continuousLinearMapAt he]
            have hsmul : h.pairing (L.chart.symm z)
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z))
                (u.val (L.chart.symm z)) =
                  (A.cutoff z : ℂ) * h.pairing (L.chart.symm z)
                    (A.frame.symmL ℂ (L.chart.symm z) (v z)) (u.val (L.chart.symm z)) := by
              let : InnerProductSpace.Core ℂ (F (L.chart.symm z)) := h.toCore (L.chart.symm z)
              change (h.toCore (L.chart.symm z)).inner
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z))
                (u.val (L.chart.symm z)) =
                  (A.cutoff z : ℂ) * (h.toCore (L.chart.symm z)).inner
                    (A.frame.symmL ℂ (L.chart.symm z) (v z)) (u.val (L.chart.symm z))
              rw [InnerProductSpace.Core.inner_smul_left, Complex.conj_ofReal]
            rw [hsmul, hu, hG z hb, map_smul]
            simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
              smul_eq_mul]
          · rw [image_eq_zero_of_notMem_tsupport hb]
            simp only [Complex.ofReal_zero, zero_smul, map_zero]
            have hzero : h.pairing (L.chart.symm z) 0 (u.val (L.chart.symm z)) = 0 := by
              let : InnerProductSpace.Core ℂ (F (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_zero_left _
            rw [hzero, smul_zero, smul_zero, inner_zero_right]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro z hz
          change inner ℂ (v z) (ρ z • G z (A.localizedFunction u z)) = 0
          simp [BundleChartCutoff.localizedFunction, hz])
    have hrightChart : h.sectionPairing μ u
        (L.input.extend L.chart_mem_atlas (W v₀)) =
        ∫ z, inner ℂ (u₀ z) (ρ z • GE z (W v₀ z)) := by
      let A := L.input
      let G := GE
      let hc := L.chart_mem_atlas
      let v := W v₀
      have hG : ∀ z ∈ tsupport A.cutoff, ∀ a b : H r,
          h.pairing (L.chart.symm z) (A.frame.symmL ℂ (L.chart.symm z) a)
            (A.frame.symmL ℂ (L.chart.symm z) b) = inner ℂ a (G z b) := by
        intro z hz a b
        exact (hGEpair z (L.input.support_subset hz)).2 a b
      rw [SmoothHermitianMetric.sectionPairing]
      rw [hchartIntegral L.chart μ ρ hρ.continuousOn
        (fun z hz ↦ (hρpos z hz).le) hρmap _
        (h.contMDiff_pairing u (A.extend hc v)).continuous (by
          intro x hx
          by_contra hxc
          apply hx
          change h.pairing x (u.val x) (A.extendedFunction v x) = 0
          rw [show A.extendedFunction v x = 0 by
            simp [BundleChartCutoff.extendedFunction, hxc]]
          let : InnerProductSpace.Core ℂ (E x) := h.toCore x
          exact InnerProductSpace.Core.inner_zero_right _)]
      calc
        _ = ∫ z in L.chart.target, inner ℂ (A.localize hc u z) (ρ z • G z (v z)) := by
          apply setIntegral_congr_fun L.chart.open_target.measurableSet
          intro z hz
          change ρ z • h.pairing (L.chart.symm z) (u.val (L.chart.symm z))
            (A.extendedFunction v (L.chart.symm z)) =
              inner ℂ (A.localizedFunction u z) (ρ z • G z (v z))
          simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
            L.chart.map_target hz, ite_true, L.chart.right_inv hz, hz]
          by_cases hb : z ∈ tsupport A.cutoff
          · have he := (A.support_subset hb).2
            have hu : u.val (L.chart.symm z) =
                A.frame.symmL ℂ (L.chart.symm z) (sectionInChart E L.chart A.frame u.val z) := by
              symm
              rw [sectionInChart, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
                A.frame.symmL_continuousLinearMapAt he]
            have hsmul : h.pairing (L.chart.symm z) (u.val (L.chart.symm z))
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z)) =
                  (A.cutoff z : ℂ) * h.pairing (L.chart.symm z)
                    (u.val (L.chart.symm z)) (A.frame.symmL ℂ (L.chart.symm z) (v z)) := by
              let : InnerProductSpace.Core ℂ (E (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_smul_right _ _
            rw [hsmul, hu, hG z hb]
            simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
              inner_smul_right, Complex.conj_ofReal, smul_eq_mul]
          · rw [image_eq_zero_of_notMem_tsupport hb]
            simp only [Complex.ofReal_zero, zero_smul, inner_zero_left]
            have hzero : h.pairing (L.chart.symm z) (u.val (L.chart.symm z)) 0 = 0 := by
              let : InnerProductSpace.Core ℂ (E (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_zero_right _
            rw [hzero, smul_zero]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro z hz
          change inner ℂ (A.localizedFunction u z) (ρ z • G z (v z)) = 0
          simp [BundleChartCutoff.localizedFunction, hz])
    have hleft (z : V) : inner ℂ (P₀ u₀ z) (b z) =
        inner ℂ (L.operator u₀ z) (ρ z • GF z (v₀ z)) := by
      rw [hP₀apply, hb]
      by_cases hz : z ∈ tsupport L.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · simp [hv₀zero z hz]
    have hright (z : V) : inner ℂ (u₀ z) (ρ z • GE z (W v₀ z)) =
        inner ℂ (u₀ z) (Q b z) := by
      by_cases hz : z ∈ tsupport L.input.cutoff
      · have hzE := L.input.support_subset hz
        obtain ⟨J, hJ⟩ := (hGEpair z hzE).1
        have hGI (a : H r) : GE z ((GE z).inverse a) = a := by
          rw [← hJ, ContinuousLinearMap.inverse_equiv]
          exact J.apply_symm_apply a
        rw [hWapply, hβK z (Or.inl hz), one_smul, ContinuousLinearMap.map_smul_of_tower, hGI,
          smul_smul, mul_inv_cancel₀ (ne_of_gt (hρpos z hzE.1)), one_smul]
      · simp [hu₀zero z hz]
    change k.sectionPairing μ (L.output.extend L.chart_mem_atlas (L.operator u₀)) v =
      h.sectionPairing μ u (L.input.extend L.chart_mem_atlas (W v₀))
    rw [hleftChart, hrightChart]
    calc
      _ = ∫ z, inner ℂ (P₀ u₀ z) (b z) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hleft z).symm))
      _ = ∫ z, inner ℂ (u₀ z) (Q b z) := hQpair u₀ b
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hright z).symm))
  -- Full integral adjunction identifies this piece with the originally selected native adjoint.
  obtain ⟨T, hchart, hin, hout, hT⟩ := hpiece L
  exact ⟨T, hchart, hin, hout,
    hT.unique (Q.isMetricFormalAdjoint_metricFormalAdjoint h k)⟩

end AtiyahSinger
