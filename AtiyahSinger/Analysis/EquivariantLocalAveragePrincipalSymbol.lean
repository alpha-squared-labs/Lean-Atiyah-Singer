/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAmplitudeFamilies
public import AtiyahSinger.Analysis.EquivariantAveragingAssembly
public import AtiyahSinger.Analysis.EquivariantAveragingCover
public import AtiyahSinger.Analysis.EquivariantSymbolCoordinateFamilies
public import AtiyahSinger.Analysis.EquivariantLocalizedRemainder
public import AtiyahSinger.Analysis.CompactAmplitudePrincipalSymbol

/-!
# Principal representatives in the local Haar construction

Public module ID: M0534.

The actual integral piece determines a principal representative through the
integrated amplitude diagonal in the same target chart, with both original
cutoffs. Adding the weighted conjugate of the fixed original smooth kernel
restores the specified original operator integral and leaves the principal
class unchanged.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set TopologicalSpace Topology
open scoped ContDiff Manifold SchwartzMap

set_option maxSynthPendingDepth 30

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  {m : ℝ}

set_option maxHeartbeats 1200000 in
-- Actual local amplitude integration and the same fixed native kernel are assembled fiberwise.
omit [T2Space G] in
open Classical in
/-- Uniform amplitudes and an exact fixed-kernel splitting realize the weighted local average. -/
theorem PseudodifferentialPiece.exists_weighted_average_of_uniform_amplitudes_with_principalSymbol
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (S : SmoothKernel (n := n) (r := r) (q := q) E F)
    (w : G → ℂ) (hw : Continuous w)
    (a : G → AmplitudeFunction n r q) (ha : ∀ g, IsAmplitude m (a g))
    (T : G → (𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))))
    (hT : ∀ g v z, T g v z = amplitudeApply (a g) v z)
    (hsupp : ∀ g, tsupport (Function.uncurry (a g)) ⊆ tsupport A.cutoff ×ˢ tsupport A.cutoff)
    (hmixed : ∀ i j k : ℕ, Continuous
      (fun p : G × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ amplitudeDerivative (a p.1) i j k
          p.2.1.1 p.2.1.2 p.2.2))
    (hjoint : ∀ l : ℕ, Continuous
      (fun p : G × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ l
          (fun z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
            EuclideanSpace ℝ (Fin n) ↦ a p.1 z.1.1 z.1.2 z.2) p.2))
    (hbound : ∀ i j k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ g x y ξ,
      ‖amplitudeDerivative (a g) i j k x y ξ‖ ≤ D * (1 + ‖ξ‖) ^ (m - (k : ℝ)))
    (hexact : ∀ g (u : smoothSections (n := n) (r := r) E) (x : M),
      (B.extend hc (T g (A.localize hc u))).val x =
        w g • ((σF.smoothSectionRepresentation IG hσF g)
          (L.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x -
        w g • ((σF.smoothSectionRepresentation IG hσF g)
          (S.toLinearMap μ ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x) :
    letI := A.frame_mem_atlas
    letI := B.frame_mem_atlas
    ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m,
      (∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (Q.toLinearMap u).val x =
          ∫ g, w g • ((σF.smoothSectionRepresentation IG hσF g)
            (L.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
            ∂(Measure.haarMeasure (⊤ : PositiveCompacts G))) ∧
      ∃ p : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
        Q.principalSymbol = globalPrincipalSymbolClass E F m p ∧
        IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
          (p.val - fun x ξ ↦
            if x ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet then
              ((B.cutoff (c x) * A.cutoff (c x) : ℝ) : ℂ) •
                (B.frame.symmL ℂ x).comp
                  ((∫ g, a g (c x) (c x) (covectorInChart c x ξ)
                    ∂(Measure.haarMeasure (⊤ : PositiveCompacts G))).comp
                    (A.frame.continuousLinearMapAt ℂ x))
            else 0) := by
  classical
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let ν := Measure.haarMeasure (⊤ : PositiveCompacts G)
  -- A zero piece supplies only the original fixed chart and cutoffs to the integration theorem.
  let C : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { chart := c
      chart_mem_atlas := hc
      input := A
      output := B
      input_support_in_output_frame := fun z hz ↦
        (B.support_subset (by rwa [← hAB])).2
      output_support_in_input_frame := fun z hz ↦
        (A.support_subset (by rwa [hAB])).2
      operator := 0
      symbol := 0
      isSymbol := isSymbol_zero univ m
      operator_apply := by intro v z; simp [quantize] }
  obtain ⟨R, hR, hprincipal⟩ :=
    C.exists_integral_of_uniform_amplitudes_with_principalSymbol ν a ha T hT
      (tsupport A.cutoff ×ˢ tsupport A.cutoff) (A.compact_support.prod A.compact_support)
      hsupp hmixed hjoint (fun K _ i j k ↦ by
        obtain ⟨D, hD, hb⟩ := hbound i j k
        exact ⟨D, hD, fun g x y _ ξ ↦ hb g x y ξ⟩)
  obtain ⟨Sbar, hSbar⟩ := S.exists_weighted_conjugate_integral
    (μ := μ) IG σE σF hσE hσF w hw
  let Qmap := R.toLinearMap + Sbar.toLinearMap μ
  have hQ : IsPseudodifferentialOperator E F μ m Qmap :=
    (pseudodifferentialSpace E F μ m).add_mem (R.isPseudodifferentialOperator m)
      (IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨Sbar, rfl⟩)
  let Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m := ⟨Qmap, hQ⟩
  have hQprincipal : Q.principalSymbol = globalPrincipalSymbolClass E F m R.globalSymbol := by
    have hrem : IsSmoothingOperator μ
        (Q.toLinearMap - ∑ _ : Fin 1, R.toLinearMap) := by
      refine ⟨Sbar, ?_⟩
      change Sbar.toLinearMap μ = (R.toLinearMap + Sbar.toLinearMap μ) -
        ∑ _ : Fin 1, R.toLinearMap
      simp
    simpa using Q.principalSymbol_eq_of_representation 1 (fun _ ↦ R) hrem
  -- Both terms are integrable in the same original fiber, so the fixed kernel cancels exactly.
  obtain ⟨AE⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨BF⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  have hint (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
      (u : smoothSections (n := n) (r := r) E) (x : M) :
      Integrable (fun g ↦ w g • ((σF.smoothSectionRepresentation IG hσF g)
        (P.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x) ν := by
    have hi := (AE.continuous_smoothSectionAction_of_isManifold IG σE hσE).comp
      (continuous_inv.prodMk (continuous_const (y := AE.smoothSectionEquiv.symm u)))
    have hp := (P.continuous_smoothSectionMap AE BF).comp hi
    have ho := (BF.continuous_smoothSectionAction_of_isManifold IG σF hσF).comp
      (continuous_id.prodMk hp)
    exact (hw.smul ((BF.continuous_section_evaluation x).comp ho)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨Q, ?_, R.globalSymbol, hQprincipal, hprincipal⟩
  intro u x
  have hLInt := hint ⟨L.toLinearMap, L.isPseudodifferentialOperator m⟩ u x
  have hSInt := hint ⟨S.toLinearMap μ,
    IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨S, rfl⟩⟩ u x
  change ((R.toLinearMap + Sbar.toLinearMap μ) u).val x = _
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  rw [hR, hSbar]
  change (∫ g, (B.extend hc (T g (A.localize hc u))).val x ∂ν) + _ = _
  simp_rw [hexact]
  rw [integral_sub hLInt hSInt, sub_add_cancel]

set_option maxHeartbeats 1800000 in
-- One normalized source piece supplies every group parameter's diagonal symbol.
omit hG [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
include hμ in
open Classical in
/-- A fixed normalized source symbol computes the global diagonal of all compatible
localized conjugation amplitudes, without changing the original principal class. -/
theorem PseudodifferentialPiece.exists_symbol_equivariantLocalizedAmplitude_diagonal
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (β δ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hβone : ∀ z ∈ tsupport L.output.cutoff ∪ tsupport L.input.cutoff, β z = 1)
    (hδ : ContDiff ℝ ∞ δ) (hcδ : HasCompactSupport δ)
    (hδsupp : tsupport δ ⊆ symbolChartDomain E F L.chart L.input.frame L.output.frame)
    (hδβ : ∀ z ∈ tsupport β, δ z = 1)
    (γ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hγdiag : ∀ z, γ₀ (z, z) = β z * β z) :
    ∃ p : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
      globalPrincipalSymbolClass E F m p = globalPrincipalSymbolClass E F m L.globalSymbol ∧
      ∀ (g : G) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (_hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
        (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c),
        A.cutoff = B.cutoff →
        let d := Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g
        let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
        tsupport β ⊆ t.source →
        (∀ z ∈ t '' tsupport β, A.cutoff z = 1) →
        tsupport A.cutoff ⊆ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
          (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet) →
        letI := A.frame_mem_atlas
        letI := B.frame_mem_atlas
        ∀ x ξ,
          (if x ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet then
            ((B.cutoff (c x) * A.cutoff (c x) : ℝ) : ℂ) •
              (B.frame.symmL ℂ x).comp
                ((L.equivariantLocalizedAmplitude IG σE σF c A B γ₀ g
                  (c x) (c x) (covectorInChart c x ξ)).comp
                  (A.frame.continuousLinearMapAt ℂ x))
          else 0) = equivariantGlobalSymbolLinearMap IG σE σF g p.val x ξ := by
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let K := tsupport L.output.cutoff ∪ tsupport L.input.cutoff
  have hK : IsCompact K := L.output.compact_support.union L.input.compact_support
  have hKβ : K ⊆ tsupport β := by
    intro z hz
    apply subset_tsupport β
    change β z ≠ 0
    rw [hβone z hz]
    exact one_ne_zero
  let p₀ := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  have hp₀ : IsSymbol univ m p₀ := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff
    L.output.compact_support L.input.compact_support
  have hp₀supp : tsupport p₀ ⊆ K :=
    tsupport_symbol_subset_of_hasOperatorSupport m p₀ hp₀ L.coordinateOperator
      L.coordinateOperator_eq_quantize K hK.isClosed L.hasOperatorSupport_coordinateOperator
  -- The larger original-frame plateaus reconstruct the exact original section operator.
  let C : BundleChartCutoff (r := r) E L.chart := {
    L.input with
    cutoff := δ
    smooth_cutoff := hδ
    compact_support := hcδ
    support_subset := fun z hz ↦ (hδsupp hz).1 }
  let D : BundleChartCutoff (r := q) F L.chart := {
    L.output with
    cutoff := δ
    smooth_cutoff := hδ
    compact_support := hcδ
    support_subset := fun z hz ↦ ⟨(hδsupp hz).1.1, (hδsupp hz).2⟩ }
  let R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m := {
    chart := L.chart
    chart_mem_atlas := L.chart_mem_atlas
    input := C
    output := D
    input_support_in_output_frame := fun z hz ↦ (hδsupp hz).2
    output_support_in_input_frame := fun z hz ↦ (hδsupp hz).1.2
    operator := L.coordinateOperator
    symbol := p₀
    isSymbol := hp₀
    operator_apply := L.coordinateOperator_eq_quantize }
  have hR : R.toLinearMap = L.toLinearMap :=
    L.extend_coordinateOperator_localize C D rfl rfl
      (fun z hz ↦ hδβ z (hKβ (Or.inr hz)))
      (fun z hz ↦ hδβ z (hKβ (Or.inl hz)))
  have hclass : globalPrincipalSymbolClass E F m R.globalSymbol =
      globalPrincipalSymbolClass E F m L.globalSymbol := by
    have hrem : IsSmoothingOperator μ
        ((∑ _ : Fin 1, R.toLinearMap) - ∑ _ : Fin 1, L.toLinearMap) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hR, sub_self]
      let Z : SmoothKernel (n := n) (r := r) (q := q) E F := {
        toFun := fun _ _ ↦ 0
        isSmooth := by
          intro e f _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames E F (fun _ _ ↦ 0) e f z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
            ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
      refine ⟨Z, ?_⟩
      ext u x
      change Z.apply μ u x = 0
      simp [SmoothKernel.apply, Z]
    simpa using globalPrincipalSymbolClass_sum_eq_of_isSmoothingOperator
      (μ := μ) m 1 1 (fun _ ↦ R) (fun _ ↦ L) hrem
  let K₀ := L.chart.symm '' tsupport β
  have hzero (x : M) (hx : x ∉ K₀) : R.globalSymbolFunction x = 0 := by
    funext ξ
    by_cases hxD : x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
    · have hz : p₀ (L.chart x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hp
        exact hx ⟨L.chart x, hKβ (hp₀supp hp), L.chart.left_inv hxD.1.1⟩
      simp only [PseudodifferentialPiece.globalSymbolFunction, R, C, D, hz,
        Pi.zero_apply, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, smul_zero,
        ite_self]
    · simp only [PseudodifferentialPiece.globalSymbolFunction, R, C, D, hxD, ite_false,
        Pi.zero_apply]
  refine ⟨R.globalSymbol, hclass, ?_⟩
  intro g c hc A B hAB
  dsimp only
  intro hβt hAone hoverlap
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let d := Diffeomorph.smul (M := M) IG 𝓘(ℝ, X) ∞ g
  let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
  let old (z : X) := g⁻¹ • c.symm z
  let Ro (z : X) := (B.frame.continuousLinearMapAt ℂ (g • old z)).comp
    ((σF.linearMap g (old z)).toContinuousLinearMap.comp (L.output.frame.symmL ℂ (old z)))
  let Ri (z : X) := (L.input.frame.continuousLinearMapAt ℂ (old z)).comp
    ((σE.linearMap g⁻¹ (c.symm z)).toContinuousLinearMap.comp (A.frame.symmL ℂ (c.symm z)))
  have htarget (x : M) (hx : x ∈ (fun y : M ↦ g • y) '' K₀) :
      x ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet ∧ A.cutoff (c x) = 1 := by
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
    have ht := hβt hz
    have hone : A.cutoff (t z) = 1 := hAone _ ⟨z, hz, rfl⟩
    have hs : t z ∈ tsupport A.cutoff := subset_tsupport _ (by
      change A.cutoff (t z) ≠ 0
      rw [hone]
      exact one_ne_zero)
    have hback : c.symm (t z) = g • L.chart.symm z := c.left_inv ht.2.2
    refine ⟨⟨⟨ht.2.2, ?_⟩, ?_⟩, hone⟩
    · change g • L.chart.symm z ∈ A.frame.baseSet
      rw [← hback]
      exact (A.support_subset hs).2
    · change g • L.chart.symm z ∈ B.frame.baseSet
      rw [← hback]
      exact (B.support_subset (by rwa [← hAB])).2
  have horbitZero (x : M) (hx : x ∉ (fun y : M ↦ g • y) '' K₀)
      (ξ : TangentSpace 𝓘(ℝ, X) x →L[ℝ] ℝ) :
      equivariantGlobalSymbolLinearMap IG σE σF g R.globalSymbolFunction x ξ = 0 := by
    have hnot : g⁻¹ • x ∉ K₀ := fun h ↦ hx ⟨g⁻¹ • x, h, smul_inv_smul g x⟩
    simp only [equivariantGlobalSymbolLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      hzero _ hnot]
    change (_ : F (g • g⁻¹ • x) →L[ℂ] F x).comp
      ((_ : F (g⁻¹ • x) →L[ℂ] F (g • g⁻¹ • x)).comp
        ((0 : E (g⁻¹ • x) →L[ℂ] F (g⁻¹ • x)).comp _)) = 0
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  have hchart (z η : X) (hz : z ∈ tsupport A.cutoff) :
      ((B.cutoff z * A.cutoff z : ℝ) : ℂ) •
          L.equivariantLocalizedAmplitude IG σE σF c A B γ₀ g z z η =
        globalSymbolInChart E F
          (equivariantGlobalSymbolLinearMap IG σE σF g R.globalSymbolFunction) c A.frame B.frame
          z η := by
    have hzD : z ∈ symbolChartDomain E F c A.frame B.frame :=
      ⟨A.support_subset hz, (B.support_subset (by rwa [← hAB])).2⟩
    have hOld := hoverlap hz
    have hzT : z ∈ t.target := ⟨⟨hzD.1.1, mem_univ _⟩, hOld.1.1⟩
    have hsource : t.symm z ∈ symbolChartDomain E F L.chart L.input.frame L.output.frame := by
      refine ⟨⟨L.chart.map_source hOld.1.1, ?_⟩, ?_⟩
      · change L.chart.symm (L.chart (g⁻¹ • c.symm z)) ∈ L.input.frame.baseSet
        rw [L.chart.left_inv hOld.1.1]
        exact hOld.1.2
      · change L.chart.symm (L.chart (g⁻¹ • c.symm z)) ∈ L.output.frame.baseSet
        rw [L.chart.left_inv hOld.1.1]
        exact hOld.2
    have hq (ζ : X) : globalSymbolInChart E F R.globalSymbolFunction
        L.chart L.input.frame L.output.frame (t.symm z) ζ =
          ((δ (t.symm z) * δ (t.symm z) : ℝ) : ℂ) • p₀ (t.symm z) ζ :=
      R.globalSymbolInChart_globalSymbolFunction _ _ hsource
    have hcov := equivariantGlobalSymbolInChart_eq IG σE σF g R.globalSymbolFunction
      L.chart c L.chart_mem_atlas hc L.input.frame A.frame L.output.frame B.frame
      z hzD hOld η
    have hcM := IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) hc
    have hdM := IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) L.chart_mem_atlas
    have ht : ContDiffOn ℝ ∞ t t.source := by
      intro y hy
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1
      have hmove := d.contMDiffAt.comp y hchart
      exact ((contMDiffAt_of_mem_maximalAtlas hcM hy.2.2).comp y hmove).contDiffAt.contDiffWithinAt
    have hts : ContDiffOn ℝ ∞ t.symm t.target := by
      intro y hy
      have hyc : y ∈ c.target := hy.1.1
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas hcM hyc
      have hmove := d.symm.contMDiffAt.comp y hchart
      exact ((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y hmove).contDiffAt.contDiffWithinAt
    let γ (w : X × X) := A.cutoff w.1 * A.cutoff w.2 * γ₀ (t.symm w.1, t.symm w.2)
    have hdiag := coordinateAmplitude_diag t ht hts γ p₀ z η hzT
    change _ = (Ro z).comp
      ((globalSymbolInChart E F R.globalSymbolFunction L.chart L.input.frame L.output.frame
        (t.symm z) ((fderiv ℝ t (t.symm z)).adjoint η)).comp (Ri z)) at hcov
    rw [hcov, hq]
    change ((B.cutoff z * A.cutoff z : ℝ) : ℂ) •
      (cutoffMatrix A.cutoff Ro z).comp
        ((coordinateAmplitude t γ p₀ z z η).comp (cutoffMatrix A.cutoff Ri z)) = _
    rw [hdiag]
    by_cases hp : p₀ (t.symm z) ((fderiv ℝ t (t.symm z)).adjoint η) = 0
    · simp only [cotangentSymbol, hp, smul_zero, ContinuousLinearMap.zero_comp,
        ContinuousLinearMap.comp_zero]
    · have hpbase : t.symm z ∈ tsupport p₀ := subset_tsupport _ (by
        intro h
        exact hp (congrFun h _))
      have hβ : β (t.symm z) = 1 := hβone _ (hp₀supp hpbase)
      have hδz : δ (t.symm z) = 1 := hδβ _ (hKβ (hp₀supp hpbase))
      have hAz : A.cutoff z = 1 := by
        have h := hAone _ ⟨t.symm z, hKβ (hp₀supp hpbase), rfl⟩
        rwa [t.right_inv hzT] at h
      have hBz : B.cutoff z = 1 := hAB ▸ hAz
      simp only [γ, hγdiag, hβ, hδz, hAz, hBz, mul_one, Complex.ofReal_one,
        one_smul, cutoffMatrix, cotangentSymbol]
  intro x ξ
  by_cases hx : x ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet
  · rw [ite_eq_left hx]
    by_cases hcut : A.cutoff (c x) = 0
    · have hnot : x ∉ (fun y : M ↦ g • y) '' K₀ := by
        intro h
        exact zero_ne_one (hcut.symm.trans (htarget x h).2)
      rw [hcut, mul_zero, Complex.ofReal_zero, zero_smul]
      exact (horbitZero x hnot ξ).symm
    · let Cx := ((A.frame.linearEquivAt ℂ x hx.1.2).toContinuousLinearEquiv).arrowCongr
        ((B.frame.linearEquivAt ℂ x hx.2).toContinuousLinearEquiv)
      apply Cx.injective
      have hq := globalSymbolInChart_covectorInChart E F
        (equivariantGlobalSymbolLinearMap IG σE σF g R.globalSymbolFunction)
        c hc A.frame B.frame x hx.1.1 ξ
      have h := hchart (c x) (covectorInChart c x ξ) (subset_tsupport _ hcut)
      apply ContinuousLinearMap.ext
      intro v
      have hval := congrArg (fun T : EuclideanSpace ℂ (Fin r) →L[ℂ]
        EuclideanSpace ℂ (Fin q) ↦ T v) (h.trans hq)
      simp only [Cx, ContinuousLinearEquiv.arrowCongr_apply,
        ContinuousLinearMap.comp_apply, smul_apply, map_smul]
      change ((B.cutoff (c x) * A.cutoff (c x) : ℝ) : ℂ) •
        B.frame.linearEquivAt ℂ x hx.2
          ((B.frame.symmL ℂ x)
            (L.equivariantLocalizedAmplitude IG σE σF c A B γ₀ g
              (c x) (c x) (covectorInChart c x ξ)
              ((A.frame.continuousLinearMapAt ℂ x)
                ((A.frame.linearEquivAt ℂ x hx.1.2).symm v)))) =
        B.frame.linearEquivAt ℂ x hx.2
          ((equivariantGlobalSymbolLinearMap IG σE σF g R.globalSymbolFunction x ξ)
            ((A.frame.linearEquivAt ℂ x hx.1.2).symm v))
      simp only [Trivialization.linearEquivAt_symm_apply,
        Trivialization.linearEquivAt_apply, ← A.frame.symmL_apply (R := ℂ) hx.1.2,
        ← B.frame.continuousLinearMapAt_apply_of_mem ℂ hx.2,
        B.frame.continuousLinearMapAt_symmL hx.2,
        A.frame.continuousLinearMapAt_symmL hx.1.2]
      simpa only [smul_apply, ContinuousLinearMap.comp_apply] using hval
  · rw [ite_eq_right hx]
    have hnot : x ∉ (fun y : M ↦ g • y) '' K₀ := fun h ↦ hx (htarget x h).1
    exact (horbitZero x hnot ξ).symm

set_option maxHeartbeats 1500000 in

/-- Every chart-fitting piece has a neighborhood on which all supported continuous weights
admit the actual native pseudodifferential average. -/
theorem PseudodifferentialPiece.exists_local_weighted_average_with_principalSymbol
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) (g₀ : G)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (hbase : (fun x : M ↦ g₀ • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
        c.source ∩ e.baseSet ∩ f.baseSet) :
    ∃ U : Set G, IsOpen U ∧ g₀ ∈ U ∧
      ∃ p : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
      globalPrincipalSymbolClass E F m p = globalPrincipalSymbolClass E F m L.globalSymbol ∧
      ∀ w : G → ℂ, Continuous w → tsupport w ⊆ U →
      ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m,
        (∀ (u : smoothSections (n := n) (r := r) E) (x : M),
          (Q.toLinearMap u).val x =
            ∫ g, w g • ((σF.smoothSectionRepresentation IG hσF g)
              (L.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
              ∂(Measure.haarMeasure (⊤ : PositiveCompacts G))) ∧
        ∃ pbar : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
          Q.principalSymbol = globalPrincipalSymbolClass E F m pbar ∧
          IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
            (pbar.val - fun x ξ ↦ ∫ g, w g •
              equivariantGlobalSymbolLinearMap IG σE σF g p.val x ξ
                ∂(Measure.haarMeasure (⊤ : PositiveCompacts G))) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let d (g : G) := Diffeomorph.smul (M := M) IG 𝓘(ℝ, X) ∞ g
  let t (g : G) := L.chart.symm.trans
    ((d g).toHomeomorph.toOpenPartialHomeomorph.trans c)
  -- Fix the native splitting once, before introducing a parameter weight.
  obtain ⟨A, B, β, δ, γ₀, U, W, hAB, hβ, hcβ, hβone, hδ, hcδ, hδsupp, hδone,
    hγ₀, hcγ₀, hγ₀supp, hoff, hU, hg₀U, hW, hvalid, hlocal⟩ :=
    L.exists_equivariant_averaging_cutoffs IG g₀ c hc e f hbase
  have hδβ : tsupport β ⊆ {x | δ x = 1} := hδone.trans interior_subset
  have hγdiag (z : X) : γ₀ (z, z) = β z * β z := by
    have h := (hoff z).eq_of_nhds
    exact (sub_eq_zero.mp h).symm
  obtain ⟨p, hp, hdiag⟩ :=
    L.exists_symbol_equivariantLocalizedAmplitude_diagonal (μ := μ) IG σE σF
      β δ (fun z hz ↦ interior_subset (s := {z | β z = 1}) (hβone hz)) hδ hcδ hδsupp
      (fun z hz ↦ hδβ hz) γ₀ hγdiag
  obtain ⟨C, D, N, Q₀, S, hCframe, hDframe, hCcut, hDcut, hN, hNsupp,
    _, _, _, hsplit⟩ := L.exists_fixed_native_kernel_remainder μ β δ hβ hcβ hβone
      hδ hcδ hδsupp hδβ γ₀ hγ₀ hcγ₀ hγ₀supp hoff
  let γ (g : G) (z : X × X) :=
    A.cutoff z.1 * A.cutoff z.2 * γ₀ ((t g).symm z.1, (t g).symm z.2)
  have hβt (g : G) (hg : g ∈ U) : tsupport β ⊆ (t g).source := by
    intro y hy
    apply (hlocal g hg).1
    apply subset_tsupport δ
    change δ y ≠ 0
    rw [hδβ hy]
    exact one_ne_zero
  -- The same target cutoff is smooth on its actual inverse-chart domain and zero off it.
  have hγdata (g : G) (hg : g ∈ U) : ContDiff ℝ ∞ (γ g) ∧
      HasCompactSupport (γ g) ∧ tsupport (γ g) ⊆ {z | (g, z) ∈ W} := by
    have hAt : tsupport A.cutoff ⊆ (t g).target := by
      intro y hy
      exact ⟨⟨(A.support_subset hy).1, mem_univ _⟩, ((hlocal g hg).2.1 hy).1.1⟩
    have hψ : ContDiffOn ℝ ∞ (t g).symm (t g).target := by
      intro y hy
      have hcM := IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) hc
      have hdM := IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) L.chart_mem_atlas
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1
      have hmove := (d g).symm.contMDiffAt.comp y hchart
      exact ((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y hmove).contDiffAt.contDiffWithinAt
    have hsA : tsupport (γ g) ⊆ tsupport A.cutoff ×ˢ tsupport A.cutoff := by
      apply closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
      intro z hz
      by_contra h
      rcases not_and_or.mp h with h | h
      · exact hz (by simp [γ, image_eq_zero_of_notMem_tsupport h])
      · exact hz (by simp [γ, image_eq_zero_of_notMem_tsupport h])
    have hγsmooth : ContDiff ℝ ∞ (γ g) := by
      apply contDiff_iff_contDiffAt.mpr
      intro z
      by_cases hz : z ∈ tsupport (γ g)
      · have hx := hAt (hsA hz).1
        have hy := hAt (hsA hz).2
        have hpair := ((hψ.contDiffAt ((t g).open_target.mem_nhds hx)).comp z
          contDiffAt_fst).prodMk
            ((hψ.contDiffAt ((t g).open_target.mem_nhds hy)).comp z contDiffAt_snd)
        exact ((A.smooth_cutoff.contDiffAt.comp z contDiffAt_fst).mul
          (A.smooth_cutoff.contDiffAt.comp z contDiffAt_snd)).mul
            (hγ₀.contDiffAt.comp z hpair)
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        exact notMem_tsupport_iff_eventuallyEq.mp hz
    have hγsrc : tsupport γ₀ ⊆ (t g).source ×ˢ (t g).source :=
      fun z hz ↦ ⟨((hlocal g hg).2.2.2 z hz).1, ((hlocal g hg).2.2.2 z hz).2.1⟩
    let K := (fun z : X × X ↦ (t g z.1, t g z.2)) '' tsupport γ₀
    have hK : IsCompact K := hcγ₀.image_of_continuousOn
      (((t g).continuousOn.prodMap (t g).continuousOn).mono hγsrc)
    have hsK : tsupport (γ g) ⊆ K := by
      apply closure_minimal ?_ hK.isClosed
      intro z hz
      have hleft : A.cutoff z.1 ≠ 0 := fun h ↦ hz (by simp [γ, h])
      have hright : A.cutoff z.2 ≠ 0 := fun h ↦ hz (by simp [γ, h])
      have hγz : γ₀ ((t g).symm z.1, (t g).symm z.2) ≠ 0 :=
        fun h ↦ hz (by simp [γ, h])
      exact ⟨((t g).symm z.1, (t g).symm z.2), subset_tsupport _ hγz,
        by simp only [(t g).right_inv (hAt (subset_tsupport _ hleft)),
          (t g).right_inv (hAt (subset_tsupport _ hright)), Prod.eta]⟩
    refine ⟨hγsmooth, (A.compact_support.prod A.compact_support).of_isClosed_subset
      (isClosed_tsupport _) hsA, hsK.trans ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact ((hlocal g hg).2.2.2 y hy).2.2
  refine ⟨U, hU, hg₀U, p, hp, ?_⟩
  intro w hw hwU
  -- The family certificate and the exact operator formula use this identical weighted amplitude.
  let a : G → AmplitudeFunction n r q := fun g x y ξ ↦
    w g • L.equivariantLocalizedAmplitude IG σE σF c A B γ₀ g x y ξ
  obtain ⟨ha, hsupp, hjoint, hmixed, hbound⟩ := L.uniform_equivariantLocalizedAmplitude
    IG σE σF hσE hσF c hc A B hAB γ₀ hγ₀ hcγ₀ U hU W hW w hw hwU
    hvalid (fun g hg ↦ (hlocal g hg).2.1) (fun g hg ↦ (hlocal g hg).2.2.2)
  have hca (g : G) : HasCompactSupport (Function.uncurry (a g)) :=
    (A.compact_support.prod A.compact_support).of_isClosed_subset (isClosed_tsupport _) (hsupp g)
  let T (g : G) := amplitudeOperator m (a g) (ha g) (hca g)
  have hT (g : G) (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      T g v z = amplitudeApply (a g) v z := amplitudeOperator_apply m (a g) (ha g) (hca g) v z
  have hscalar (g : G) (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      amplitudeApply (a g) v z = w g •
        amplitudeApply (L.equivariantLocalizedAmplitude IG σE σF c A B γ₀ g) v z := by
    unfold amplitudeApply
    simp only [a, smul_apply]
    have hcomm (ξ y : X) :
        Complex.exp (Complex.I * (inner ℝ (z - y) ξ : ℂ)) •
          (w g • L.equivariantLocalizedAmplitude IG σE σF c A B γ₀ g z y ξ (v y)) =
        w g • (Complex.exp (Complex.I * (inner ℝ (z - y) ξ : ℂ)) •
          L.equivariantLocalizedAmplitude IG σE σF c A B γ₀ g z y ξ (v y)) := smul_comm _ _ _
    simp_rw [hcomm]
    simp_rw [integral_smul]
    rw [smul_comm]
  have hexact : ∀ g (u : smoothSections (n := n) (r := r) E) (x : M),
      (B.extend hc (T g (A.localize hc u))).val x =
        w g • ((σF.smoothSectionRepresentation IG hσF g)
          (L.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x -
        w g • ((σF.smoothSectionRepresentation IG hσF g)
          (S.toLinearMap μ ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x := by
    intro g u x
    by_cases hg : g ∈ U
    · have hnear : ∀ v z, amplitudeApply
          (L.equivariantLocalizedAmplitude IG σE σF c A B γ₀ g) v z =
          B.localize hc (σF.smoothSectionRepresentation IG hσF g
            (D.extend L.chart_mem_atlas (N (C.localize L.chart_mem_atlas
              (σE.smoothSectionRepresentation IG hσE g⁻¹ (A.extend hc v)))))) z :=
        L.amplitudeApply_equivariantLocalizedAmplitude IG σE σF hσE hσF β δ hδβ
          C D hCframe hDframe hCcut hDcut γ₀ hγ₀ hcγ₀ hγ₀supp N hN hNsupp g c hc A B hAB
          (hlocal g hg).2.1 {z | (g, z) ∈ W} (hW.preimage (continuous_const.prodMk continuous_id))
          (hlocal g hg).1 (fun z hz ↦ (hvalid (g, z) hz).1)
          (fun z hz ↦ (hvalid (g, z) hz).2) (hγdata g hg).1
          (hγdata g hg).2.1 (hγdata g hg).2.2
          (fun z hz ↦ interior_subset (s := {z | A.cutoff z = 1}) ((hlocal g hg).2.2.1 hz))
      have hTnear : T g (A.localize hc u) = w g • B.localize hc
          (σF.smoothSectionRepresentation IG hσF g
            (D.extend L.chart_mem_atlas (N (C.localize L.chart_mem_atlas
              (σE.smoothSectionRepresentation IG hσE g⁻¹ (A.extend hc (A.localize hc u))))))) := by
        apply SchwartzMap.ext
        intro z
        rw [hT, hscalar, hnear]
        rfl
      have hshell := L.extend_localize_equivariant_near IG σE σF hσE hσF β hcβ C D N hNsupp
        g c hc A B hAB (hβt g hg) (hlocal g hg).2.2.1 u
      have hsplitu := congrArg (fun P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
          smoothSections (n := n) (r := q) F ↦
          σF.smoothSectionRepresentation IG hσF g
            (P (σE.smoothSectionRepresentation IG hσE g⁻¹ u))) hsplit
      simp only [LinearMap.add_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        map_add] at hsplitu
      have hsplitx := congrArg (fun s : smoothSections (n := n) (r := q) F ↦ s.val x) hsplitu
      simp only [Submodule.coe_add, Pi.add_apply] at hsplitx
      rw [hTnear]
      change ((B.extendLinearMap hc) (w g • _)).val x = _
      rw [map_smul]
      change (w g • B.extend hc _).val x = _
      rw [hshell]
      simp only [Submodule.coe_smul, Pi.smul_apply]
      rw [hsplitx, smul_add, add_sub_cancel_right]
      rfl
    · have hwzero : w g = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hg (hwU h))
      have hTzero : T g (A.localize hc u) = 0 := by
        apply SchwartzMap.ext
        intro z
        rw [hT, hscalar, hwzero, zero_smul]
        rfl
      rw [hTzero]
      change ((B.extendLinearMap hc) 0).val x = _
      simp [hwzero]
  obtain ⟨Q, hQ, pbar, hr, hlower⟩ :=
    L.exists_weighted_average_of_uniform_amplitudes_with_principalSymbol
      IG σE σF hσE hσF c hc A B hAB S w hw a ha T hT hsupp hmixed hjoint hbound hexact
  refine ⟨Q, hQ, pbar, hr, ?_⟩
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let ν := Measure.haarMeasure (⊤ : PositiveCompacts G)
  -- Before integration the weighted diagonal equals the geometric orbit of one fixed symbol.
  have hpoint (g : G) (x : M) (ξ : TangentSpace 𝓘(ℝ, X) x →L[ℝ] ℝ) :
      (if x ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet then
        ((B.cutoff (c x) * A.cutoff (c x) : ℝ) : ℂ) •
          (B.frame.symmL ℂ x).comp
            ((a g (c x) (c x) (covectorInChart c x ξ)).comp
              (A.frame.continuousLinearMapAt ℂ x))
      else 0) = w g • equivariantGlobalSymbolLinearMap IG σE σF g p.val x ξ := by
    by_cases hg : g ∈ U
    · have h := hdiag g c hc A B hAB (hβt g hg)
        (fun z hz ↦ interior_subset (s := {z | A.cutoff z = 1}) ((hlocal g hg).2.2.1 hz))
        (hlocal g hg).2.1 x ξ
      have hscaled := congrArg (fun T : E x →L[ℂ] F x ↦ w g • T) h
      simpa only [a, smul_ite, smul_zero, ContinuousLinearMap.comp_smul,
        ContinuousLinearMap.smul_comp, smul_comm (w g)] using hscaled
    · have hwzero : w g = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hg (hwU h))
      simp only [a, hwzero, zero_smul, ContinuousLinearMap.zero_comp,
        ContinuousLinearMap.comp_zero, smul_zero, ite_self]
  -- The original target-frame equivalence commutes with this same Hom-fiber integral.
  have hglobal : (fun x ξ ↦
        if x ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet then
          ((B.cutoff (c x) * A.cutoff (c x) : ℝ) : ℂ) •
            (B.frame.symmL ℂ x).comp
              ((∫ g, a g (c x) (c x) (covectorInChart c x ξ) ∂ν).comp
                (A.frame.continuousLinearMapAt ℂ x))
        else 0) = (fun x ξ ↦ ∫ g, w g •
          equivariantGlobalSymbolLinearMap IG σE σF g p.val x ξ ∂ν) := by
    funext x ξ
    rw [show (∫ g, w g • equivariantGlobalSymbolLinearMap IG σE σF g p.val x ξ ∂ν) =
      ∫ g, (if x ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet then
        ((B.cutoff (c x) * A.cutoff (c x) : ℝ) : ℂ) •
          (B.frame.symmL ℂ x).comp
            ((a g (c x) (c x) (covectorInChart c x ξ)).comp
              (A.frame.continuousLinearMapAt ℂ x))
      else 0) ∂ν from integral_congr_ae (Filter.Eventually.of_forall (fun g ↦ (hpoint g x ξ).symm))]
    by_cases hx : x ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet
    · simp only [hx, ite_true]
      let Cx := ((A.frame.linearEquivAt ℂ x hx.1.2).toContinuousLinearEquiv).symm.arrowCongr
        ((B.frame.linearEquivAt ℂ x hx.2).toContinuousLinearEquiv).symm
      have hCx (v : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) :
          Cx v = (B.frame.symmL ℂ x).comp (v.comp (A.frame.continuousLinearMapAt ℂ x)) := by
        ext z
        change (B.frame.linearEquivAt ℂ x hx.2).symm
          (v (A.frame.linearEquivAt ℂ x hx.1.2 z)) = _
        simp only [ContinuousLinearMap.comp_apply]
        rw [Trivialization.linearEquivAt_symm_apply,
          B.frame.symmL_apply (R := ℂ) hx.2]
        rw [A.frame.continuousLinearMapAt_apply_of_mem ℂ hx.1.2]
        rfl
      rw [← hCx]
      simp_rw [← hCx]
      rw [integral_smul, Cx.integral_comp_comm]
    · simp only [hx, ite_false, integral_zero]
  change IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1)
    (pbar.val - fun x ξ ↦ ∫ g, w g •
      equivariantGlobalSymbolLinearMap IG σE σF g p.val x ξ ∂ν)
  rw [← hglobal]
  exact hlower

end AtiyahSinger
