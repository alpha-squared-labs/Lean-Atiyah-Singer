/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalFormalAdjoint
public import AtiyahSinger.Analysis.GlobalTranspose
public import AtiyahSinger.Analysis.HermitianMetricFormalAdjoint
public import AtiyahSinger.Analysis.LocalAdjoint

import AtiyahSinger.Analysis.GlobalSymbolAdjoint

/-!
# Geometric Hermitian adjoints of real-order PDOs

Public module ID: M0884.

D02/A02: globalize SG III.3.11 using smooth density and Gram-matrix weights,
then compare the resulting operator with (3.18) and pp.194-195. The local theorem
and the book's differential Hermitian discussion are distinct inputs; their
real-order global combination is a project bridge. The fixed fiber norms must
come from the specified smooth Hermitian metrics. No arbitrary compatible metric
is chosen. The geometric adjoint is not the Hilbert adjoint for arbitrary Sobolev
norms. The adjoint is constructed on the same-order finite local representation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap Matrix.Norms.Elementwise ComplexConjugate

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hHE : IsSmoothHermitianBundle (n := n) (r := r) E]
  [hHF : IsSmoothHermitianBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

set_option linter.overlappingInstances false in
-- Retain the original explicit and inherited smooth-bundle proofs in this predicate.
/-- The same-density Hermitian integral identity for a real-order PDO and its adjoint. -/
def IsFormalAdjoint
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m) : Prop :=
  ∀ (u : smoothSections (n := n) (r := r) E)
    (v : smoothSections (n := n) (r := q) F),
      smoothSectionPairing μ F (P.toLinearMap u) v =
        smoothSectionPairing μ E u (Q.toLinearMap v)

include hM hT2 hSC hC hBorel hE hF hHE hHF hμ

set_option maxHeartbeats 2500000 in
-- Normalize the original metric Gram weights and the global real-order adjoint.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The local adjoint calculus gives a unique global Hermitian adjoint of the same real order. -/
theorem existsUnique_formalAdjoint :
    ∃! Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m,
      P.IsFormalAdjoint Q := by
  classical
  let TModel := EuclideanSpace ℝ (Fin n)
  let SourceModel := EuclideanSpace ℂ (Fin r)
  let TargetModel := EuclideanSpace ℂ (Fin q)
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let k := SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F
  -- The original installed metrics give smooth invertible Gram weights in the chosen frames.
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
      ∃ T : smoothSections (n := n) (r := q) F →ₗ[ℂ]
          smoothSections (n := n) (r := r) E,
        IsMetricFormalAdjoint h k μ L.toLinearMap T ∧
          IsPseudodifferentialOperator F E μ m T := by
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
    -- Compactify the original Schwartz operator before constructing its Hermitian adjoint.
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
    refine ⟨LT.toLinearMap, ?_, LT.isPseudodifferentialOperator m⟩
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
  -- Smooth kernels are reversed using the same installed metrics and the same measure.
  have hkernelRaw (K : SmoothKernel (n := n) (r := r) (q := q) E F) :
      ∃ J : SmoothKernel (n := n) (r := q) (q := r) F E,
        (∀ (x y : M) (u : E x) (v : F y),
          inner ℂ (K.toFun y x u) v = inner ℂ u (J.toFun x y v)) ∧
        ∀ (u : smoothSections (n := n) (r := r) E)
          (v : smoothSections (n := n) (r := q) F),
          smoothSectionPairing μ F (K.toLinearMap μ u) v =
            smoothSectionPairing μ E u (J.toLinearMap μ v) := by
    classical
    let (x : M) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let (x : M) : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let (x : M) : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
    let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
    let A (x y : M) : F y →L[ℂ] E x := (K.toFun y x).adjoint
    -- Native smooth Gram entries recover the original model-space Gram operator.
    have gramSmooth {s : ℕ} (U : Set M)
        (G : M → EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin s))
        (B : M → Fin s → Fin s → ℂ)
        (hB : ∀ i j, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ B x i j) U)
        (hG : ∀ x i j, inner ℂ (EuclideanSpace.single i 1)
          (G x (EuclideanSpace.single j 1)) = B x i j) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin s)) ∞ G U := by
      let toOp : (Fin s → Fin s → ℂ) →ₗ[ℂ]
          (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin s)) :=
        LinearMap.toContinuousLinearMap.toLinearMap.comp
          (Matrix.toEuclideanLin.toLinearMap.comp (Matrix.ofLinearEquiv ℂ).toLinearMap)
      let toOpC := LinearMap.toContinuousLinearMap (toOp.restrictScalars ℝ)
      have hBsmooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, Fin s → Fin s → ℂ) ∞ B U :=
        contMDiffOn_pi_space.mpr (fun i ↦ contMDiffOn_pi_space.mpr (hB i))
      have heq : (fun x ↦ toOpC (B x)) = G := by
        funext x
        apply ContinuousLinearMap.coe_injective
        apply (EuclideanSpace.basisFun (Fin s) ℂ).toBasis.ext
        intro j
        apply PiLp.ext
        intro i
        have h := hG x i j
        change (Matrix.toEuclideanLin (Matrix.of (B x))
          ((EuclideanSpace.basisFun (Fin s) ℂ).toBasis j)) i = _
        rw [Matrix.toLpLin_apply]
        simpa [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct,
          EuclideanSpace.inner_single_left] using h.symm
      rw [← heq]
      exact toOpC.contDiff.contMDiff.comp_contMDiffOn hBsmooth
    have hA : IsSmoothKernel (n := n) (r := q) (q := r) F E A := by
      intro f e hf he
      let GE := hermitianFrameGram E e
      let GF := hermitianFrameGram F f
      have hGE := gramSmooth e.baseSet GE _
        (IsSmoothHermitianBundle.contMDiffOn_inner e)
        (fun x i j ↦ hermitianFrameGram_inner e x _ _)
      have hGF := gramSmooth f.baseSet GF _
        (IsSmoothHermitianBundle.contMDiffOn_inner f)
        (fun x i j ↦ hermitianFrameGram_inner f x _ _)
      have hGEinv (x : M) (hx : x ∈ e.baseSet) : (GE x).IsInvertible := by
        have hinj : Function.Injective (GE x) := by
          apply (ContinuousLinearMap.adjoint_comp_self_injective_iff (e.symmL ℂ x)).mpr
          exact Function.LeftInverse.injective (e.continuousLinearMapAt_symmL hx)
        exact ⟨(LinearEquiv.ofBijective (GE x).toLinearMap
          ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv, rfl⟩
      have hGEi : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
          (fun x ↦ (GE x).inverse) e.baseSet := by
        intro x hx
        exact ((hGEinv x hx).contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ
          |>.comp_contMDiffWithinAt (hGE x hx)
      let adj : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℝ]
          (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
        { toFun := fun c ↦ c.adjoint
          map_add' := fun c d ↦ map_add _ c d
          map_smul' := by
            intro a c
            simp only [RingHom.id_apply, ← Complex.coe_smul, map_smulₛₗ,
              Complex.conj_ofReal]
          cont := ContinuousLinearMap.adjoint.continuous }
      -- The inverse source Gram is at x; the original target Gram is at y.
      have hleft := hGEi.comp (contMDiffOn_fst (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ hz.1)
      have hright := hGF.comp (contMDiffOn_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ hz.2)
      have hswap := (K.isSmooth e f).comp (contMDiffOn_snd.prodMk contMDiffOn_fst)
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ ⟨hz.2, hz.1⟩)
      have hmiddle := adj.contMDiff.comp_contMDiffOn hswap
      have hcompose {a b c : ℕ} : ContDiff ℝ ∞ (fun z :
          (EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c)) ×
            (EuclideanSpace ℂ (Fin a) →L[ℂ] EuclideanSpace ℂ (Fin b)) ↦ z.1.comp z.2) :=
        (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
      have hweighted := hcompose.contMDiff.comp_contMDiffOn
        (hleft.prodMk_space (hcompose.contMDiff.comp_contMDiffOn
          (hmiddle.prodMk_space hright)))
      apply hweighted.congr
      intro z hz
      apply ContinuousLinearMap.ext
      intro v
      have heq : GE z.1 (kernelInFrames F E A f e z v) =
          (kernelInFrames E F K.toFun e f (z.2, z.1)).adjoint (GF z.2 v) := by
        apply ext_inner_left ℂ
        intro u
        rw [ContinuousLinearMap.adjoint_inner_right, hermitianFrameGram_inner]
        change inner ℂ (e.symmL ℂ z.1 u)
          (e.symmL ℂ z.1 (e.continuousLinearMapAt ℂ z.1
            ((K.toFun z.2 z.1).adjoint (f.symmL ℂ z.2 v)))) = _
        rw [e.symmL_continuousLinearMapAt hz.1,
          ContinuousLinearMap.adjoint_inner_right, hermitianFrameGram_inner]
        change inner ℂ (K.toFun z.2 z.1 (e.symmL ℂ z.1 u)) (f.symmL ℂ z.2 v) =
          inner ℂ (f.symmL ℂ z.2 (f.continuousLinearMapAt ℂ z.2
            (K.toFun z.2 z.1 (e.symmL ℂ z.1 u)))) (f.symmL ℂ z.2 v)
        rw [f.symmL_continuousLinearMapAt hz.2]
      exact ((hGEinv z.1 hz.1).inverse_apply_self _).symm.trans
        (congrArg (GE z.1).inverse heq)
    let J : SmoothKernel (n := n) (r := q) (q := r) F E := ⟨A, hA⟩
    refine ⟨J, ?_, ?_⟩
    · intro x y u v
      exact ((K.toFun y x).adjoint_inner_right u v).symm
    · intro u v
      let α := dualSectionsEquiv F (smoothHermitianDualEquiv F v)
      have hrow (x : M) :
          inner ℂ (u.val x) ((J.toLinearMap μ v).val x) =
            conj ((K.transpose.toLinearMap μ α).val x (u.val x)) := by
        have hJ := J.dual_apply μ v x (innerSL ℂ (u.val x))
        have hT := K.transpose.dual_apply μ α x (ContinuousLinearMap.apply ℂ ℂ (u.val x))
        change inner ℂ (u.val x) ((J.toLinearMap μ v).val x) =
          ∫ y, inner ℂ (u.val x) (A x y (v.val y)) ∂μ at hJ
        change (K.transpose.toLinearMap μ α).val x (u.val x) =
          ∫ y, α.val y (K.toFun y x (u.val x)) ∂μ at hT
        rw [hJ, hT, ← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with y
        change inner ℂ (u.val x) ((K.toFun y x).adjoint (v.val y)) =
          conj ((smoothHermitianDualEquiv F v).val y (K.toFun y x (u.val x)))
        rw [ContinuousLinearMap.adjoint_inner_right, smoothHermitianDualEquiv_apply,
          inner_conj_symm]
      have ht := K.isFormalTranspose_toLinearMap (μ := μ) α u
      change (∫ x, (K.transpose.toLinearMap μ α).val x (u.val x) ∂μ) =
        ∫ x, (smoothHermitianDualEquiv F v).val x ((K.toLinearMap μ u).val x) ∂μ at ht
      simp only [smoothHermitianDualEquiv_apply] at ht
      change (∫ x, inner ℂ ((K.toLinearMap μ u).val x) (v.val x) ∂μ) =
        ∫ x, inner ℂ (u.val x) ((J.toLinearMap μ v).val x) ∂μ
      simp_rw [hrow]
      rw [integral_conj, ht, ← integral_conj]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (inner_conj_symm (𝕜 := ℂ) ((K.toLinearMap μ u).val x) (v.val x)).symm
  have hkernel (K : SmoothKernel (n := n) (r := r) (q := q) E F) :
      ∃ K' : SmoothKernel (n := n) (r := q) (q := r) F E,
        IsMetricFormalAdjoint h k μ (K.toLinearMap μ) (K'.toLinearMap μ) := by
    obtain ⟨J, _, hJ⟩ := hkernelRaw K
    exact ⟨J, hJ⟩
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  choose T hT horder using fun j : Fin N ↦ hpiece (L j)
  obtain ⟨K', hK'⟩ := hkernel K
  have hsum (s : Finset (Fin N)) :
      IsMetricFormalAdjoint h k μ
          ((∑ j ∈ s, (L j).toLinearMap) + K.toLinearMap μ)
          ((∑ j ∈ s, T j) + K'.toLinearMap μ) ∧
        IsPseudodifferentialOperator F E μ m ((∑ j ∈ s, T j) + K'.toLinearMap μ) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty, zero_add] using
        And.intro hK' (IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨K', rfl⟩)
    | @insert j s hjs ih =>
      simpa only [Finset.sum_insert hjs, add_assoc] using
        And.intro ((hT j).add ih.1)
          (IsPseudodifferentialOperator.add m _ _ (horder j) ih.2)
  let Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m :=
    ⟨(∑ j, T j) + K'.toLinearMap μ, (hsum Finset.univ).2⟩
  have hdecomp : P.toLinearMap = (∑ j, (L j).toLinearMap) + K.toLinearMap μ := by
    rw [hK]
    abel
  have hQ : IsMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap := by
    rw [hdecomp]
    exact (hsum Finset.univ).1
  refine ⟨Q, hQ, ?_⟩
  -- Positive definiteness determines the full section map, hence the original PDO structure.
  intro R hR
  have hmaps : R.toLinearMap = Q.toLinearMap :=
    (show IsMetricFormalAdjoint h k μ P.toLinearMap R.toLinearMap from hR).unique hQ
  have hext (R S : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m)
      (heq : R.toLinearMap = S.toLinearMap) : R = S := by
    cases R
    cases S
    cases heq
    rfl
  exact hext R Q hmaps

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The actual Hermitian adjoint, selected from its unique same-order PDO realization. -/
def formalAdjoint :
    PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m :=
  Classical.choose P.existsUnique_formalAdjoint.exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The selected PDO satisfies the geometric Hermitian integral identity. -/
theorem isFormalAdjoint_formalAdjoint : P.IsFormalAdjoint P.formalAdjoint := by
  -- The selected same-order witness retains the original integral characterization.
  exact P.existsUnique_formalAdjoint.exists.choose_spec

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Taking the Hermitian adjoint twice preserves the entire PDO, including its remainder. -/
theorem formalAdjoint_formalAdjoint : P.formalAdjoint.formalAdjoint = P := by
  -- Conjugation reverses the pairing without changing the given density or fiber metrics.
  apply P.formalAdjoint.existsUnique_formalAdjoint.unique
    P.formalAdjoint.isFormalAdjoint_formalAdjoint
  intro v u
  have hpair := congrArg (starRingEnd ℂ) (P.isFormalAdjoint_formalAdjoint u v)
  simpa only [smoothSectionPairing, ← integral_conj, inner_conj_symm] using hpair.symm

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The bilinear transpose becomes the Hermitian adjoint under the two metric identifications. -/
theorem formalTranspose_hermitian (v : smoothSections (n := n) (r := q) F) :
    P.formalTranspose.toLinearMap (dualSectionsEquiv F (smoothHermitianDualEquiv F v)) =
      dualSectionsEquiv E (smoothHermitianDualEquiv E (P.formalAdjoint.toLinearMap v)) := by
  -- Transport the adjoint through the two actual conjugate-linear metric identifications.
  let e := (smoothHermitianDualEquiv (n := n) (r := r) E).trans (dualSectionsEquiv E)
  let f := (smoothHermitianDualEquiv (n := n) (r := q) F).trans (dualSectionsEquiv F)
  let T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E) :=
    e.toLinearMap.comp (P.formalAdjoint.toLinearMap.comp f.symm.toLinearMap)
  have hT : IsFormalTranspose μ P.toLinearMap T := by
    intro α u
    obtain ⟨w, rfl⟩ := f.surjective α
    change smoothDualSectionPairing E μ
      ((dualSectionsEquiv E).symm (T (f w))) u =
      smoothDualSectionPairing F μ ((dualSectionsEquiv F).symm (f w)) (P.toLinearMap u)
    have hTw : T (f w) = e (P.formalAdjoint.toLinearMap w) := by simp [T]
    rw [hTw]
    change smoothDualSectionPairing E μ (smoothHermitianDualEquiv E
      (P.formalAdjoint.toLinearMap w)) u =
      smoothDualSectionPairing F μ (smoothHermitianDualEquiv F w) (P.toLinearMap u)
    rw [smoothDualSectionPairing_hermitian, smoothDualSectionPairing_hermitian]
    have hpair := congrArg (starRingEnd ℂ) (P.isFormalAdjoint_formalAdjoint u w)
    simpa only [smoothSectionPairing, ← integral_conj, inner_conj_symm] using hpair.symm
  -- Smooth primal tests identify the entire transpose map, hence this specified input.
  have hmaps : P.formalTranspose.toLinearMap = T :=
    IsFormalTranspose.unique P.toLinearMap _ _ P.isFormalTranspose_formalTransposeLinearMap hT
  change P.formalTranspose.toLinearMap (f v) = e (P.formalAdjoint.toLinearMap v)
  rw [hmaps]
  simp [T]

end PseudodifferentialOperator

set_option linter.overlappingInstances false in
-- Keep the original explicit and inherited smooth-bundle proofs in this included context.
include hM hT2 hSC hC hBorel hE hF hHE hHF hμ in
/-- For the same differential section map, the PDO and differential adjoints agree exactly. -/
theorem DifferentialOperator.formalAdjoint_eq_of_toLinearMap_eq {k : ℕ}
    (D : DifferentialOperator (n := n) (r := r) (q := q) E F k)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (k : ℝ))
    (h : P.toLinearMap = D.toLinearMap) :
    P.formalAdjoint.toLinearMap = (D.formalAdjoint μ).toLinearMap := by
  -- Both section maps satisfy the same installed-metric adjoint identity for D.
  let hE := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let hF := SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F
  have hP : IsMetricFormalAdjoint hE hF μ D.toLinearMap P.formalAdjoint.toLinearMap := by
    intro u v
    simpa only [hE, hF, sectionPairing_ofInnerProduct, h] using
      P.isFormalAdjoint_formalAdjoint u v
  have hD : IsMetricFormalAdjoint hE hF μ D.toLinearMap (D.formalAdjoint μ).toLinearMap := by
    intro u v
    simpa only [hE, hF, sectionPairing_ofInnerProduct] using
      D.isFormalAdjoint_formalAdjoint μ u v
  exact hP.unique hD

end AtiyahSinger
