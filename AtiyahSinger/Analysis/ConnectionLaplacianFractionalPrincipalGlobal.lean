/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianFractionalPrincipalLocal
public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol
public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import AtiyahSinger.Analysis.HomogeneousSymbolTopology

/-!
# Global principal reconstruction of the normalized first resolvent term

Public module ID: M0386.

In one fixed patch, compare the actual integrated symbol with the regularized
radial symbol multiplied by the original partition weight. The difference has
bounded frequency support before transporting charts. Its actual low-order
piece therefore gives the global symbol difference without transporting
frequency radii through unrelated coordinate charts.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

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
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

/-- The normalized first integrated patch has the original weighted radial principal symbol. -/
theorem isGlobalSymbol_normalized_integratedTerm_zero_sub
    (P : FiniteResolventPatch (connectionLaplacian μ g h cov hcov hcomplex))
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (R : QuantizationPresentation (n := n) (r := r) (q := r) E E)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E (-2 * p))
    (ha : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      a.val x ξ = (g.length x ξ ^ (-2 * p) : ℝ) • ContinuousLinearMap.id ℂ (E x)) :
    let C : ℝ := ∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
    IsGlobalSymbol (n := n) (r := r) (q := r) E E (-2 * p - 1)
      (((C⁻¹ : ℝ) : ℂ) • (P.integratedTerm 0 p hp hp1).globalSymbolFunction -
        fun x ξ ↦ (P.weight x : ℂ) •
          (R.regularizedSymbol (-2 * p) a.val a.property.1 a.property.2).val x ξ) := by
  classical
  let := P.cutoff.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let m : ℝ := -2 * p
  let C : ℝ := ∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
  let D := P.chart '' P.domain
  let ψ := P.cutoff.cutoff
  let χ := P.coordinateWeight
  let A := R.regularizedSymbol m a.val a.property.1 a.property.2
  let b₀ := globalSymbolInChart E E A.val P.chart P.cutoff.frame P.cutoff.frame
  let b := zeroExtendedSymbol D (fun x ↦ ψ x * χ x) b₀
  let L₀ := P.integratedTerm 0 p hp hp1
  let q : SymbolFunction n r r := ((C⁻¹ : ℝ) : ℂ) • L₀.symbol - b
  have hD : IsOpen D := P.chart.isOpen_image_of_subset_source P.isOpen_domain
    (fun x hx ↦ (P.hasCoordinateExpression.1 hx).1.1)
  have hDD : D ⊆ symbolChartDomain E E P.chart P.cutoff.frame P.cutoff.frame := by
    rintro _ ⟨x, hx, rfl⟩
    have hs := P.hasCoordinateExpression.1 hx
    have hframe : P.chart.symm (P.chart x) ∈ P.cutoff.frame.baseSet := by
      rw [P.chart.left_inv hs.1.1]
      exact hs.1.2
    exact ⟨⟨P.chart.map_source hs.1.1, hframe⟩, hframe⟩
  have hb₀ : IsSymbol D m b₀ := by
    have hs := A.property P.chart P.chart_mem_atlas P.cutoff.frame P.cutoff.frame
    exact ⟨hs.1.mono (Set.prod_mono hDD (Set.Subset.rfl)),
      fun K hKD hK i j ↦ hs.2 K (hKD.trans hDD) hK i j⟩
  have hψχ : HasCompactSupport (fun x ↦ ψ x * χ x) := P.cutoff.compact_support.mul_right
  have hsψχ : tsupport (fun x ↦ ψ x * χ x) ⊆ D :=
    (tsupport_mul_subset_left (f := ψ) (g := χ)).trans P.support_cutoff
  have hb : IsSymbol Set.univ m b := isSymbol_zeroExtendedSymbol D hD m _
    (P.cutoff.smooth_cutoff.mul P.smooth_coordinateWeight) hψχ hsψχ b₀ hb₀
  have hcb : HasCompactSupport b := hasCompactSupport_zeroExtendedSymbol D _ b₀ hψχ
  have hcL : HasCompactSupport L₀.symbol :=
    hasCompactSupport_zeroExtendedSymbol D ψ (P.integratedSymbol 0 p) P.cutoff.compact_support
  have hq : ContDiffOn ℝ ∞ (Function.uncurry q) (Set.univ ×ˢ Set.univ) :=
    ((L₀.isSymbol.smul isOpen_univ ((C⁻¹ : ℝ) : ℂ)).1).sub hb.1
  have hcq : HasCompactSupport q := hcL.smul_left.sub hcb
  -- On the same compact cutoff support, both symbols are exactly radial at high frequency.
  obtain ⟨R₁, hR₁, hfirst⟩ := exists_radius_normalized_integratedSymbol_zero_eq
    μ g h cov hcov hcomplex P p hp hp1 (tsupport ψ) P.support_cutoff P.cutoff.compact_support
  obtain ⟨R₂, _, hregularized⟩ := R.regularizedSymbolFunction_eq_inChart_at_high_frequency
    a.val P.chart P.chart_mem_atlas P.cutoff.frame P.cutoff.frame (tsupport ψ)
      P.cutoff.compact_support (P.support_cutoff.trans hDD)
  have hhigh : ∀ x ∈ Set.univ, ∀ ξ, max R₁ R₂ ≤ ‖ξ‖ → q x ξ = 0 := by
    intro x _ ξ hξ
    by_cases hx : x ∈ tsupport ψ
    · have hxD := P.support_cutoff hx
      have hxfull := hDD hxD
      have hξ₁ := (le_max_left R₁ R₂).trans hξ
      have hξ₂ := (le_max_right R₁ R₂).trans hξ
      have hne : covectorFromChart P.chart (P.chart.symm x) ξ ≠ 0 := by
        intro heq
        have hc := covectorInChart_covectorFromChart P.chart P.chart_mem_atlas
          (P.chart.symm x) (P.chart.map_target hxfull.1.1) ξ
        rw [heq] at hc
        have hz : covectorInChart P.chart (P.chart.symm x) 0 = 0 := by ext i; rfl
        have hξzero : ξ = 0 := hc.symm.trans hz
        rw [hξzero, norm_zero] at hξ₁
        exact (not_le_of_gt hR₁) hξ₁
      have hhomogeneous : globalSymbolInChart E E a.val
          P.chart P.cutoff.frame P.cutoff.frame x ξ =
            (g.length (P.chart.symm x)
              (covectorFromChart P.chart (P.chart.symm x) ξ) ^ m : ℝ) •
                ContinuousLinearMap.id ℂ V := by
        apply ContinuousLinearMap.ext
        intro v
        change P.cutoff.frame.continuousLinearMapAt ℂ (P.chart.symm x)
          (a.val (P.chart.symm x) (covectorFromChart P.chart (P.chart.symm x) ξ)
            (P.cutoff.frame.symmL ℂ (P.chart.symm x) v)) = _
        rw [ha _ _ hne]
        simp only [smul_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.map_smul_of_tower, P.cutoff.frame.continuousLinearMapAt_symmL
            hxfull.1.2]
        rfl
      have hrec : b₀ x ξ =
          (g.length (P.chart.symm x)
            (covectorFromChart P.chart (P.chart.symm x) ξ) ^ m : ℝ) •
              ContinuousLinearMap.id ℂ V :=
        (hregularized x hx ξ hξ₂).trans hhomogeneous
      have hnorm : ((C⁻¹ : ℝ) : ℂ) • P.integratedSymbol 0 p x ξ =
          ((χ x * g.length (P.chart.symm x)
            (covectorFromChart P.chart (P.chart.symm x) ξ) ^ m : ℝ) : ℂ) •
              ContinuousLinearMap.id ℂ V := by
        simpa only [Complex.coe_smul] using hfirst x hx ξ hξ₁
      change ((C⁻¹ : ℝ) : ℂ) •
        zeroExtendedSymbol D ψ (P.integratedSymbol 0 p) x ξ -
          zeroExtendedSymbol D (fun y ↦ ψ y * χ y) b₀ x ξ = 0
      unfold zeroExtendedSymbol
      rw [ite_eq_left (show x ∈ D from hxD), ite_eq_left (show x ∈ D from hxD)]
      rw [smul_comm ((C⁻¹ : ℝ) : ℂ) (ψ x : ℂ), hnorm, hrec]
      simp only [← Complex.coe_smul, Complex.ofReal_mul, smul_smul, mul_assoc, sub_self]
    · have hzero := image_eq_zero_of_notMem_tsupport hx
      change ((C⁻¹ : ℝ) : ℂ) •
        zeroExtendedSymbol D ψ (P.integratedSymbol 0 p) x ξ -
          zeroExtendedSymbol D (fun y ↦ ψ y * χ y) b₀ x ξ = 0
      simp [zeroExtendedSymbol, hzero]
  have hlow : IsSymbol Set.univ (m - 1) q :=
    isSmoothingSymbol_of_frequency_support isOpen_univ q (max R₁ R₂) hq hhigh (m - 1)
  let L : PseudodifferentialPiece (n := n) (r := r) (q := r) E E (m - 1) :=
    { L₀ with
      symbol := q
      isSymbol := hlow
      operator := quantizeSchwartz (m - 1) q hlow hcq
      operator_apply := quantizeSchwartz_apply (m - 1) q hlow hcq }
  -- The reference symbol transports back exactly; its three plateau factors reduce to one.
  have hb_apply (z η : X) : b z η = ((ψ z * χ z : ℝ) : ℂ) • b₀ z η := by
    by_cases hz : z ∈ D
    · simp only [b, zeroExtendedSymbol, ite_eq_left hz]
    · have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hz (P.support_cutoff h))
      simp [b, zeroExtendedSymbol, hz, hzero]
  have hglobal : L.globalSymbolFunction =
      ((C⁻¹ : ℝ) : ℂ) • L₀.globalSymbolFunction -
        fun x ξ ↦ (P.weight x : ℂ) • A.val x ξ := by
    funext x ξ
    by_cases hx : x ∈ P.chart.source ∩ P.cutoff.frame.baseSet ∩ P.cutoff.frame.baseSet
    · have htransport : (P.cutoff.frame.symmL ℂ x).comp
          ((b₀ (P.chart x) (covectorInChart P.chart x ξ)).comp
            (P.cutoff.frame.continuousLinearMapAt ℂ x)) = A.val x ξ := by
        rw [show b₀ (P.chart x) (covectorInChart P.chart x ξ) =
          (P.cutoff.frame.continuousLinearMapAt ℂ x).comp
            ((A.val x ξ).comp (P.cutoff.frame.symmL ℂ x)) from
              globalSymbolInChart_covectorInChart E E A.val P.chart P.chart_mem_atlas
                P.cutoff.frame P.cutoff.frame x hx.1.1 ξ]
        apply ContinuousLinearMap.ext
        intro v
        simp only [ContinuousLinearMap.comp_apply,
          P.cutoff.frame.symmL_continuousLinearMapAt hx.1.2]
      have hweight : (ψ (P.chart x) * ψ (P.chart x)) *
          (ψ (P.chart x) * χ (P.chart x)) = P.weight x := by
        rw [← P.coordinateWeight_apply x hx.1.1]
        change (ψ (P.chart x) * ψ (P.chart x)) * (ψ (P.chart x) * χ (P.chart x)) =
          χ (P.chart x)
        by_cases hz : χ (P.chart x) = 0
        · simp [hz]
        · obtain ⟨O, _, hχO, hψO⟩ := P.cutoff_eq_one
          have hψ := hψO _ (hχO (subset_tsupport χ hz))
          simp only [ψ, hψ, one_mul, mul_one]
      have hreference : ((ψ (P.chart x) * ψ (P.chart x) : ℝ) : ℂ) •
          (P.cutoff.frame.symmL ℂ x).comp
            ((b (P.chart x) (covectorInChart P.chart x ξ)).comp
              (P.cutoff.frame.continuousLinearMapAt ℂ x)) =
            (P.weight x : ℂ) • A.val x ξ := by
        rw [hb_apply, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
          htransport, smul_smul, ← Complex.ofReal_mul, hweight]
      simp only [Pi.sub_apply, Pi.smul_apply, PseudodifferentialPiece.globalSymbolFunction]
      rw [ite_eq_left (show x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
        from hx), ite_eq_left (show
          x ∈ L₀.chart.source ∩ L₀.input.frame.baseSet ∩ L₀.output.frame.baseSet from hx)]
      change ((ψ (P.chart x) * ψ (P.chart x) : ℝ) : ℂ) •
        (P.cutoff.frame.symmL ℂ x).comp
          ((q (P.chart x) (covectorInChart P.chart x ξ)).comp
            (P.cutoff.frame.continuousLinearMapAt ℂ x)) =
        ((C⁻¹ : ℝ) : ℂ) •
          (((ψ (P.chart x) * ψ (P.chart x) : ℝ) : ℂ) •
            (P.cutoff.frame.symmL ℂ x).comp
              ((L₀.symbol (P.chart x) (covectorInChart P.chart x ξ)).comp
                (P.cutoff.frame.continuousLinearMapAt ℂ x))) -
          (P.weight x : ℂ) • A.val x ξ
      simp only [q, Pi.sub_apply, Pi.smul_apply, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_sub, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_smul, smul_sub, hreference,
        smul_comm ((ψ (P.chart x) * ψ (P.chart x) : ℝ) : ℂ) ((C⁻¹ : ℝ) : ℂ)]
    · have hweight : P.weight x = 0 := P.weight_eq_zero x (fun h ↦
        hx (P.hasCoordinateExpression.1 h))
      simp only [Pi.sub_apply, Pi.smul_apply, PseudodifferentialPiece.globalSymbolFunction]
      rw [ite_eq_right (show
        x ∉ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet from hx),
        ite_eq_right (show
          x ∉ L₀.chart.source ∩ L₀.input.frame.baseSet ∩ L₀.output.frame.baseSet from hx)]
      simp only [hweight, Complex.ofReal_zero, zero_smul, smul_zero, sub_zero]
  have hresult := L.isGlobalSymbol_globalSymbolFunction
  rw [hglobal] at hresult
  exact hresult

end AtiyahSinger
