/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianFiniteResolvent
public import AtiyahSinger.Analysis.JointFrequencyQuantizationIntegral

/-!
# Actual integrated pieces of the finite Laplacian parametrix

Public module ID: M0390.

Each fixed joint symbol is integrated before quantization and then realized by the
same compact cutoffs and original frame. The resulting piece has its fractional
symbol order. Its actual action is the convergent pointwise integral of the same
finite-family term, with no assumed PDO or integral identity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap Topology

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
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace FiniteResolventPatch

variable {L : DifferentialOperator (n := n) (r := r) (q := r) E E 2}
  (P : FiniteResolventPatch L)

/-- The exact fractional integral of the specified recursive joint symbol. -/
def integratedSymbol (j : ℕ) (p : ℝ) : SymbolFunction n r r :=
  fun x ξ ↦ ∫ t in Ioi (0 : ℝ), t ^ (-p) • jointFrequencySymbolSlice (P.symbol j) t x ξ

/-- The integrated recursive term is an actual PDO piece with the same chart and cutoffs. -/
def integratedTerm (j : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    PseudodifferentialPiece (n := n) (r := r) (q := r) E E (-2 * p - (j : ℝ)) := by
  let D := P.chart '' P.domain
  have hD : IsOpen D := P.chart.isOpen_image_of_subset_source P.isOpen_domain
    (fun x hx ↦ (P.hasCoordinateExpression.1 hx).1.1)
  let b := zeroExtendedSymbol D P.cutoff.cutoff (P.integratedSymbol j p)
  have hlocal : IsSymbol D (-2 * p - (j : ℝ)) (P.integratedSymbol j p) :=
    isSymbol_integral_jointFrequencySymbolSlice hD (P.symbol j) j
      (P.isSymbol_symbol j) p hp hp1
  have hb : IsSymbol Set.univ (-2 * p - (j : ℝ)) b :=
    isSymbol_zeroExtendedSymbol D hD _ P.cutoff.cutoff P.cutoff.smooth_cutoff
      P.cutoff.compact_support P.support_cutoff _ hlocal
  have hbc : HasCompactSupport b :=
    hasCompactSupport_zeroExtendedSymbol D P.cutoff.cutoff _ P.cutoff.compact_support
  exact
    { chart := P.chart
      chart_mem_atlas := P.chart_mem_atlas
      input := P.cutoff
      output := P.cutoff
      input_support_in_output_frame := fun _ hz ↦ (P.cutoff.support_subset hz).2
      output_support_in_input_frame := fun _ hz ↦ (P.cutoff.support_subset hz).2
      operator := quantizeSchwartz _ b hb hbc
      symbol := b
      isSymbol := hb
      operator_apply := quantizeSchwartz_apply _ b hb hbc }

/-- The original positive-parameter term is extended by zero outside its integration domain. -/
def positiveTerm (j : ℕ) (t : ℝ) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E :=
  if ht : 0 < t then P.term j t ht else 0

omit [SecondCountableTopology M] in
/-- The actual fractional piece is the convergent fiberwise integral of the same finite term. -/
theorem integrableOn_smul_term_and_integratedTerm_apply (j : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (u : smoothSections (n := n) (r := r) E) (x : M) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-p) • (P.positiveTerm j t u).val x) (Ioi 0) ∧
      ((P.integratedTerm j p hp hp1).toLinearMap u).val x =
        ∫ t in Ioi (0 : ℝ), t ^ (-p) • (P.positiveTerm j t u).val x := by
  classical
  let := P.cutoff.frame_mem_atlas
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let D := P.chart '' P.domain
  let u₀ := P.cutoff.localize P.chart_mem_atlas u
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let m : ℝ := -2 - (j : ℝ)
  have hm : m ≤ 0 :=
    sub_nonpos.mpr ((by norm_num : (-2 : ℝ) ≤ 0).trans (Nat.cast_nonneg j))
  have hD : IsOpen D := P.chart.isOpen_image_of_subset_source P.isOpen_domain
    (fun y hy ↦ (P.hasCoordinateExpression.1 hy).1.1)
  -- Both operators use exactly the original inverse-frame extension of their quantizers.
  have hterm (t : ℝ) (ht : 0 < t) :
      (P.positiveTerm j t u).val x =
        if x ∈ P.chart.source then (P.cutoff.cutoff (P.chart x) : ℂ) •
          P.cutoff.frame.symmL ℂ x (quantize
            (zeroExtendedSymbol D P.cutoff.cutoff (jointFrequencySymbolSlice (P.symbol j) t))
            u₀ (P.chart x)) else 0 := by
    rw [positiveTerm, dite_eq_left ht]
    change P.cutoff.extendedFunction
      ((P.piece m hm (P.symbol j) (P.isSymbol_symbol j) t ht).operator u₀) x = _
    simp only [BundleChartCutoff.extendedFunction]
    split_ifs with hx
    · rw [(P.piece m hm (P.symbol j) (P.isSymbol_symbol j) t ht).operator_apply]
      rfl
    · rfl
  have hintegrated : ((P.integratedTerm j p hp hp1).toLinearMap u).val x =
      if x ∈ P.chart.source then (P.cutoff.cutoff (P.chart x) : ℂ) •
        P.cutoff.frame.symmL ℂ x (quantize
          (zeroExtendedSymbol D P.cutoff.cutoff (P.integratedSymbol j p)) u₀ (P.chart x))
      else 0 := by
    change P.cutoff.extendedFunction ((P.integratedTerm j p hp hp1).operator u₀) x = _
    simp only [BundleChartCutoff.extendedFunction]
    split_ifs with hx
    · rw [(P.integratedTerm j p hp hp1).operator_apply]
      rfl
    · rfl
  by_cases hx : x ∈ P.chart.source
  · rw [ite_eq_left hx] at hintegrated
    by_cases hz : P.chart x ∈ D
    · -- On the coordinate domain, factor only fixed continuous linear maps through the integral.
      have hquant (a : SymbolFunction n r r) :
          quantize (zeroExtendedSymbol D P.cutoff.cutoff a) u₀ (P.chart x) =
            (P.cutoff.cutoff (P.chart x) : ℂ) • quantize a u₀ (P.chart x) := by
        simp only [quantize, zeroExtendedSymbol, ite_eq_left hz, smul_apply]
        simp_rw [smul_comm _ (P.cutoff.cutoff (P.chart x) : ℂ)]
        rw [integral_smul]
        exact smul_comm _ _ _
      let T : V →L[ℝ] E x :=
        (((P.cutoff.cutoff (P.chart x) : ℂ) • P.cutoff.frame.symmL ℂ x).comp
          ((P.cutoff.cutoff (P.chart x) : ℂ) • ContinuousLinearMap.id ℂ V)).restrictScalars ℝ
      have htermT (t : ℝ) (ht : 0 < t) :
          (P.positiveTerm j t u).val x =
            T (quantize (jointFrequencySymbolSlice (P.symbol j) t) u₀ (P.chart x)) := by
        rw [hterm t ht, ite_eq_left hx, hquant]
        rfl
      have hintegratedT : ((P.integratedTerm j p hp hp1).toLinearMap u).val x =
          T (quantize (P.integratedSymbol j p) u₀ (P.chart x)) := by
        rw [hintegrated, hquant]
        rfl
      have hint : Integrable (fun t : ℝ ↦ t ^ (-p) •
          quantize (jointFrequencySymbolSlice (P.symbol j) t) u₀ (P.chart x)) μ :=
        integrableOn_smul_quantize_jointFrequencySymbolSlice hD (P.symbol j) j
          (P.isSymbol_symbol j) p hp hp1 u₀ (P.chart x) hz
      have heq : (fun t : ℝ ↦ T (t ^ (-p) •
          quantize (jointFrequencySymbolSlice (P.symbol j) t) u₀ (P.chart x))) =ᵐ[μ]
          (fun t : ℝ ↦ t ^ (-p) • (P.positiveTerm j t u).val x) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [T.map_smul, htermT t ht]
      refine ⟨(T.integrable_comp hint).congr heq, ?_⟩
      rw [hintegratedT]
      have hF := quantize_integral_jointFrequencySymbolSlice hD (P.symbol j) j
        (P.isSymbol_symbol j) p hp hp1 u₀ (P.chart x) hz
      change quantize (P.integratedSymbol j p) u₀ (P.chart x) = _ at hF
      rw [hF, ← T.integral_comp_comm hint]
      exact integral_congr_ae heq
    · -- Both actual compact symbols vanish if their coordinate point is outside the domain.
      have htermzero : (fun t : ℝ ↦ t ^ (-p) • (P.positiveTerm j t u).val x) =ᵐ[μ] 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [hterm t ht, ite_eq_left hx]
        simp [quantize, zeroExtendedSymbol, hz]
      refine ⟨(integrable_zero ℝ (E x) μ).congr htermzero.symm, ?_⟩
      rw [integral_congr_ae htermzero]
      simp only [Pi.zero_apply, integral_zero, hintegrated]
      simp [quantize, zeroExtendedSymbol, hz]
  · -- The original chart-boundary extension is zero before and after integration.
    have htermzero : (fun t : ℝ ↦ t ^ (-p) • (P.positiveTerm j t u).val x) =ᵐ[μ] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hterm t ht, ite_eq_right hx]
      simp
    refine ⟨(integrable_zero ℝ (E x) μ).congr htermzero.symm, ?_⟩
    rw [integral_congr_ae htermzero]
    simp only [Pi.zero_apply, integral_zero, hintegrated, ite_eq_right hx]

end FiniteResolventPatch

end AtiyahSinger
