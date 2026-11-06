/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Analysis.SelfAdjointEllipticCorrection

/-!
# Invertible elliptic operators for changing order

Public module ID: M0841.

A09: the order-reducing isomorphism used in SG III.13, p.247. Its actual section
map, homogeneous principal symbol and every Sobolev realization are specified
together for the same operator.

SG describes integer shifts by powers of a connection Laplacian; real powers
are treated in TA XII.1, Theorem 1.3. For the existence statement below, we use
a standard Fredholm correction instead: quantize the real scalar homogeneous
symbol, symmetrize in one smooth Hermitian metric, and add the smooth orthogonal
projection onto its kernel. This retains the supplied regularization class and
constructs the required all-orders isomorphisms. It does not identify a chosen
spectral power; that separate obligation remains in the spectral-power modules.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT hSC hC hE hB hμ in
/-- An elliptic order shift is an actual smooth and all-orders Sobolev isomorphism.

The same operator has principal symbol `length^l` times the identity off zero.
The Sobolev equivalences are required to act by its existing Sobolev extension.
-/
theorem exists_elliptic_orderReduction
    (g : SmoothCotangentMetric (n := n) (M := M))
    (R : QuantizationPresentation (n := n) (r := r) (q := r) E E) (l : ℝ) :
    ∃ (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E l)
      (J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ l)
      (U : smoothSections (n := n) (r := r) E ≃ₗ[ℂ]
        smoothSections (n := n) (r := r) E),
      (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        a.val x ξ = (g.length x ξ ^ l : ℝ) • ContinuousLinearMap.id ℂ (E x)) ∧
      J.principalSymbol = globalPrincipalSymbolClass E E l
        (R.regularizedSymbol l a.val a.property.1 a.property.2) ∧
      J.toLinearMap = U.toLinearMap ∧ J.IsElliptic ∧
      ∀ (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ),
        ∃ V : A.SobolevSpace s ≃L[ℂ] A.SobolevSpace (s - l),
          V.toContinuousLinearMap = J.sobolevExtension A A s := by
  classical
  -- Radial extension of the identity gives the requested scalar symbol at every real order.
  let a₀ := cosphereRestriction g (globalSymbolId (n := n) E)
  have hs₀ : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := r)
      E E (globalSymbolId E) := by
    intro c hc e f _ _
    exact ((isGlobalSymbol_globalSymbolId (E := E) (r := r)) c hc e f).1.mono
      (fun _ hp ↦ ⟨hp.1, Set.mem_univ _⟩)
  let a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E l :=
    ⟨cosphereExtension g l a₀,
      (isSmoothOffZeroGlobalSymbol_cosphereExtension_iff g l a₀).mpr
        (isSmoothCosphereSymbol_restriction g _ hs₀),
      isHomogeneousGlobalSymbol_cosphereExtension g l a₀⟩
  have ha (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      a.val x ξ = (g.length x ξ ^ l : ℝ) • ContinuousLinearMap.id ℂ (E x) := by
    change cosphereExtension g l a₀ x ξ = _
    rw [cosphereExtension_of_ne_zero g l a₀ x ξ hξ]
    simp only [a₀, cosphereRestriction, globalSymbolId, ← Complex.coe_smul]
    rfl
  have he : IsEllipticGlobalSymbol E E a.val := by
    intro x ξ hξ
    rw [ha x ξ hξ]
    exact (IsUnit.smul_bijective
      (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (g.length_pos x ξ hξ) l).ne')).comp
      Function.bijective_id
  let p := R.regularizedSymbol l a.val a.property.1 a.property.2
  let P := R.quantize μ p
  have hP : P.IsElliptic :=
    (PseudodifferentialOperator.isElliptic_quantize_iff (μ := μ) R p).mpr
      ((isEllipticFullGlobalSymbol_regularizedSymbol_iff R l a.val
        a.property.1 a.property.2).mpr he)
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) (E := E)
  -- Every regularization weight is real, so adjunction fixes this actual symbol function.
  have haself (x : M) (ξ : CotangentFiber (n := n) x) :
      h.adjoint h x (a.val x ξ) = a.val x ξ := by
    by_cases hξ : ξ = 0
    · subst ξ
      simp only [a, cosphereExtension_zero_covector, h.adjoint_zero]
    · rw [ha x ξ hξ, ← Complex.coe_smul, h.adjoint_smul, h.adjoint_id,
        Complex.conj_ofReal]
  have hpself : h.symbolSpaceAdjoint h p = p := by
    apply Subtype.ext
    funext x ξ
    change h.adjoint h x (R.regularizedSymbolFunction a.val x ξ) =
      R.regularizedSymbolFunction a.val x ξ
    unfold QuantizationPresentation.regularizedSymbolFunction
    induction (Finset.univ : Finset (Fin R.size)) using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, h.adjoint_zero]
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, h.adjoint_add, ih, h.adjoint_smul, haself,
        Complex.conj_ofReal]
  have hPadj : (P.metricFormalAdjoint h h).principalSymbol = P.principalSymbol := by
    rw [P.principalSymbol_metricFormalAdjoint, R.principalSymbol_quantize,
      h.principalSymbolAdjoint_class, hpself]
  let D := (P.add (P.metricFormalAdjoint h h)).smul (1 / 2)
  have hDclass : D.principalSymbol = P.principalSymbol := by
    rw [PseudodifferentialOperator.principalSymbol_smul,
      PseudodifferentialOperator.principalSymbol_add, hPadj, ← two_smul ℂ _, smul_smul]
    norm_num
  have hD : D.IsElliptic :=
    (P.isElliptic_iff_of_principalSymbol_eq_operator D hDclass.symm).mp hP
  have hDself : IsMetricFormalAdjoint h h μ D.toLinearMap D.toLinearMap := by
    have hpair := P.isMetricFormalAdjoint_metricFormalAdjoint h h
    have hsum : IsMetricFormalAdjoint h h μ
        (P.toLinearMap + (P.metricFormalAdjoint h h).toLinearMap)
        (P.toLinearMap + (P.metricFormalAdjoint h h).toLinearMap) := by
      convert hpair.add hpair.symm using 1
      exact add_comm _ _
    change IsMetricFormalAdjoint h h μ
      ((1 / 2 : ℂ) • (P.toLinearMap + (P.metricFormalAdjoint h h).toLinearMap))
      ((1 / 2 : ℂ) • (P.toLinearMap + (P.metricFormalAdjoint h h).toLinearMap))
    simpa only [map_div₀, map_one, map_ofNat] using hsum.smul (1 / 2 : ℂ)
  -- A smoothing correction of this same symmetric operator removes its kernel and cokernel.
  obtain ⟨J, hJD, hJ, hbij, hSobolev⟩ :=
    D.exists_bijective_of_isMetricFormalAdjoint μ h hD hDself
  refine ⟨a, J, LinearEquiv.ofBijective J.toLinearMap hbij, ha,
    hJD.trans (hDclass.trans (R.principalSymbol_quantize μ p)), rfl, hJ, ?_⟩
  intro A s
  exact ⟨ContinuousLinearEquiv.ofBijective (J.sobolevExtension A A s)
    (LinearMap.ker_eq_bot.mpr (hSobolev A s).1)
    (LinearMap.range_eq_top.mpr (hSobolev A s).2), rfl⟩

end AtiyahSinger
