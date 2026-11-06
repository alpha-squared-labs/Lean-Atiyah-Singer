/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianFractionalExpansion
public import AtiyahSinger.Analysis.ConnectionLaplacianFractionalPrincipalGlobal
public import AtiyahSinger.Analysis.CosphereRegularity
public import AtiyahSinger.Analysis.GlobalEllipticSymbol
public import AtiyahSinger.Analysis.PseudodifferentialSpace

/-!
# The original fractional spectral power and its metric principal class

Public module ID: M0385.

The first term of the same fixed parametrix family has the radial metric principal
class. The original spectral power differs from this actual term by one lower
order, so its PDO realization has that same class. The radial representative is
the existing cosphere extension of the identity, with the prescribed regularization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped ContDiff Manifold

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

/-- The original fractional spectral action has a PDO realization with the metric radial
principal class, without additional symbol estimates or operator identities as inputs. -/
theorem exists_connectionLaplacianSmoothPower_fractional_principal
    (R : QuantizationPresentation (n := n) (r := r) (q := r) E E)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E (-2 * p),
      ∃ J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ (-2 * p),
        (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
          a.val x ξ = (g.length x ξ ^ (-2 * p) : ℝ) • ContinuousLinearMap.id ℂ (E x)) ∧
        J.toLinearMap =
          (connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-2 * p)).toLinearMap ∧
        J.principalSymbol = globalPrincipalSymbolClass E E (-2 * p)
          (R.regularizedSymbol (-2 * p) a.val a.property.1 a.property.2) := by
  classical
  let m : ℝ := -2 * p
  let C : ℝ := ∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ p t 1
  let c : ℂ := (C⁻¹ : ℝ)
  -- Use the existing homogeneous extension of the identity on the original metric cosphere.
  let a₀ := cosphereRestriction g (globalSymbolId (n := n) E)
  have hs₀ : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := r)
      E E (globalSymbolId E) := by
    intro d hd e f _ _
    exact ((isGlobalSymbol_globalSymbolId (E := E) (r := r)) d hd e f).1.mono
      (fun _ hz ↦ ⟨hz.1, Set.mem_univ _⟩)
  let a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E m :=
    ⟨cosphereExtension g m a₀,
      (isSmoothOffZeroGlobalSymbol_cosphereExtension_iff g m a₀).mpr
        (isSmoothCosphereSymbol_restriction g _ hs₀),
      isHomogeneousGlobalSymbol_cosphereExtension g m a₀⟩
  have ha (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      a.val x ξ = (g.length x ξ ^ m : ℝ) • ContinuousLinearMap.id ℂ (E x) := by
    change cosphereExtension g m a₀ x ξ = _
    rw [cosphereExtension_of_ne_zero g m a₀ x ξ hξ]
    simp only [a₀, cosphereRestriction, globalSymbolId, ← Complex.coe_smul]
    rfl
  let σ := R.regularizedSymbol m a.val a.property.1 a.property.2
  -- Select the actual patches only once, and retain them in both expansion comparisons.
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨k, P, hpartition⟩ :=
    exists_connectionLaplacian_finite_resolvent_patches μ g h cov hcov hcomplex
  have hexp := connectionLaplacianSmoothPower_has_fractional_expansion
    μ g h cov hcov hcomplex A P hpartition p hp hp1
  let L (i : Fin k) : PseudodifferentialPiece (n := n) (r := r) (q := r) E E m :=
    { (P i).integratedTerm 0 p hp hp1 with
      isSymbol := by
        simpa only [Nat.cast_zero, sub_zero] using ((P i).integratedTerm 0 p hp hp1).isSymbol }
  have hzero : IsSmoothingOperator μ
      (0 : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E) := by
    let K : SmoothKernel (n := n) (r := r) (q := r) E E :=
      { toFun := fun _ _ ↦ 0
        isSmooth := by
          intro e f _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames E E (fun _ _ ↦ 0) e f z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
            ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
    refine ⟨K, ?_⟩
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change (∫ y, (0 : E y →L[ℂ] E x) (u.val y) ∂μ) = 0
    simp
  let Q₀ : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ m :=
    { toLinearMap := ∑ i, (L i).toLinearMap
      isPseudodifferentialOperator := ⟨k, L, by simpa only [sub_self] using hzero⟩ }
  let Q := Q₀.smul c
  let J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ m :=
    { toLinearMap := (connectionLaplacianSmoothPower μ g h cov hcov hcomplex m).toLinearMap
      isPseudodifferentialOperator := by
        simpa only [Nat.cast_zero, sub_zero, Finset.sum_range_zero] using hexp 0 }
  have hQmap : Q.toLinearMap = FiniteResolventPatch.fractionalTerm P p hp hp1 0 := rfl
  have hJQ : J.principalSymbol = Q.principalSymbol := by
    apply (J.principalSymbol_eq_iff Q).mpr
    change IsPseudodifferentialOperator E E μ (m - 1)
      ((connectionLaplacianSmoothPower μ g h cov hcov hcomplex m).toLinearMap - Q.toLinearMap)
    rw [hQmap]
    simpa only [Nat.cast_one, Finset.sum_range_one] using hexp 1
  -- The global comparison of each same first piece adds to the prescribed radial symbol.
  let b : globalSymbolSpace (n := n) (r := r) (q := r) E E m := ∑ i, (L i).globalSymbol
  have hweights (x : M) (ξ : CotangentFiber (n := n) x) :
      (∑ i, ((P i).weight x : ℂ) • σ.val x ξ) = σ.val x ξ := by
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hpartition, Complex.ofReal_one, one_smul]
  have hlow : IsGlobalSymbol (n := n) (r := r) (q := r) E E (m - 1)
      ((c • b).val - σ.val) := by
    have hsum : IsGlobalSymbol (n := n) (r := r) (q := r) E E (m - 1)
        (∑ i, (c • (L i).globalSymbolFunction -
          fun x ξ ↦ ((P i).weight x : ℂ) • σ.val x ξ)) := by
      change (∑ i, (c • (L i).globalSymbolFunction -
        fun x ξ ↦ ((P i).weight x : ℂ) • σ.val x ξ)) ∈ globalSymbolSpace E E (m - 1)
      apply Submodule.sum_mem
      intro i _
      exact isGlobalSymbol_normalized_integratedTerm_zero_sub
        μ g h cov hcov hcomplex (P i) p hp hp1 R a ha
    have heq : (∑ i, (c • (L i).globalSymbolFunction -
        fun x ξ ↦ ((P i).weight x : ℂ) • σ.val x ξ)) = (c • b).val - σ.val := by
      funext x ξ
      simp only [b, Submodule.coe_smul, Submodule.coe_sum, Pi.sub_apply, Pi.smul_apply,
        Finset.sum_apply, Finset.sum_sub_distrib, Finset.smul_sum, hweights]
      rfl
    rwa [heq] at hsum
  have hQprincipal : Q.principalSymbol = globalPrincipalSymbolClass E E m (c • b) := by
    change (Q₀.smul c).principalSymbol = _
    rw [Q₀.principalSymbol_smul]
    have hrep : IsSmoothingOperator μ (Q₀.toLinearMap - ∑ i, (L i).toLinearMap) := by
      simpa only [Q₀, sub_self] using hzero
    rw [Q₀.principalSymbol_eq_of_representation k L hrep]
    exact (map_smul (globalPrincipalSymbolClass E E m) c b).symm
  refine ⟨a, J, ha, rfl, ?_⟩
  exact hJQ.trans (hQprincipal.trans ((globalPrincipalSymbolClass_eq_iff E E m _ _).mpr hlow))

end AtiyahSinger
