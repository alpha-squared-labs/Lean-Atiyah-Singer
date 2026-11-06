/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianFractionalPrincipal
public import AtiyahSinger.Analysis.ConnectionLaplacianPowerGroup
public import AtiyahSinger.Analysis.HomogeneousSymbolOperations

/-!
# The homogeneous principal symbol of every specified real spectral power

Public module ID: M0395.

The same fractional powers supply the negative generator, while the original
positive differential operator supplies the positive generator. Composition
preserves the radial principal term and the original smooth spectral action.
The ceiling decomposition then covers every real order without replacing the
specified spectral map by an independently chosen elliptic operator.
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

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the original real spectral power and radial principal
-- representative.
/-- The specified real spectral power has its radial homogeneous principal representative. -/
theorem exists_connectionLaplacianSmoothPower_principal
    (R : QuantizationPresentation (n := n) (r := r) (q := r) E E) (l : ℝ) :
    ∃ (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E l)
      (J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ l),
      (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        a.val x ξ = (g.length x ξ ^ l : ℝ) • ContinuousLinearMap.id ℂ (E x)) ∧
      J.toLinearMap =
        (connectionLaplacianSmoothPower μ g h cov hcov hcomplex l).toLinearMap ∧
      J.principalSymbol = globalPrincipalSymbolClass E E l
        (R.regularizedSymbol l a.val a.property.1 a.property.2) := by
  classical
  let U := connectionLaplacianSmoothPower μ g h cov hcov hcomplex
  let H (d : ℝ) : Prop :=
    ∃ (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E d)
      (J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ d),
      (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        a.val x ξ = (g.length x ξ ^ d : ℝ) • ContinuousLinearMap.id ℂ (E x)) ∧
      J.toLinearMap = (U d).toLinearMap ∧
      J.principalSymbol = globalPrincipalSymbolClass E E d
        (R.regularizedSymbol d a.val a.property.1 a.property.2)
  -- Compose the same smooth powers and their actual homogeneous symbols.
  have hadd (d e : ℝ) (hd : H d) (he : H e) : H (d + e) := by
    obtain ⟨a, P, ha, hP, hPa⟩ := hd
    obtain ⟨b, Q, hb, hQ, hQb⟩ := he
    let c : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E (d + e) :=
      ⟨globalSymbolComp a.val b.val, a.property.1.globalSymbolComp b.property.1,
        a.property.2.globalSymbolComp b.property.2⟩
    refine ⟨c, P.comp Q, ?_, ?_, ?_⟩
    · intro x ξ hξ
      change (a.val x ξ).comp (b.val x ξ) = _
      rw [ha x ξ hξ, hb x ξ hξ, ← Complex.coe_smul, ← Complex.coe_smul,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
        ContinuousLinearMap.id_comp, smul_smul, ← Complex.ofReal_mul,
        ← Real.rpow_add (g.length_pos x ξ hξ), Complex.coe_smul]
    · change P.toLinearMap.comp Q.toLinearMap = (U (d + e)).toLinearMap
      rw [hP, hQ]
      have hU : U (d + e) = (U e).trans (U d) :=
        connectionLaplacianSmoothPower_add μ g h cov hcov hcomplex d e
      rw [hU]
      rfl
    · rw [P.principalSymbol_comp Q, hPa, hQb]
      exact globalPrincipalSymbolComp_regularizedSymbol_eq R R R b a c (fun _ _ _ ↦ rfl)
  have hfraction (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : H (-2 * p) :=
    exists_connectionLaplacianSmoothPower_fractional_principal
      μ g h cov hcov hcomplex R p hp hp1
  -- The positive generator is exactly identity plus the original differential Laplacian.
  have htwo : H 2 := by
    let D := connectionLaplacian μ g h cov hcov hcomplex
    let P := D.toPseudodifferentialOperator μ
    let I : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ (2 : ℝ) :=
      ⟨LinearMap.id, IsPseudodifferentialOperator.mono (by norm_num : (0 : ℝ) ≤ 2)
        LinearMap.id (isPseudodifferentialOperator_id μ)⟩
    let J := I.add P
    let a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E (2 : ℝ) :=
      ⟨D.principalSymbolFunction, D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction,
        D.isHomogeneousGlobalSymbol_principalSymbolFunction⟩
    have ha (x : M) (ξ : CotangentFiber (n := n) x) (_hξ : ξ ≠ 0) :
        a.val x ξ = (g.length x ξ ^ (2 : ℝ) : ℝ) • ContinuousLinearMap.id ℂ (E x) := by
      apply ContinuousLinearMap.ext
      intro v
      change D.principalSymbol x ξ v = _
      rw [connectionLaplacian_principalSymbol]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_apply,
        ContinuousLinearMap.id_apply, Real.rpow_two, ← Complex.ofReal_pow, Complex.coe_smul]
    let B := connectionLaplacianInverse μ g h cov hcov hcomplex
    let f := h.smoothToL2 μ
    have hBinj := (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).2.1
    have hBnegative (u : smoothSections (n := n) (r := r) E) :
        f (U (-2) u) = B (f u) := by
      have hg := connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex (-2) u
      rw [connectionLaplacianSpectralPower, ite_eq_left (by norm_num : (-2 : ℝ) ≤ 0)] at hg
      have hexp : -(-2 : ℝ) / 2 = 1 := by norm_num
      rw [hexp] at hg
      have hone : CFC.rpow (connectionLaplacianInverse μ g h cov hcov hcomplex) 1 =
          connectionLaplacianInverse μ g h cov hcov hcomplex :=
        CFC.rpow_one _ (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).1
      rw [hone] at hg
      obtain ⟨v, hv, hw⟩ := (LinearPMap.mem_graph_iff _).mp hg
      change (v : h.L2SectionSpace μ) = f u at hv
      change B (v : h.L2SectionSpace μ) = f (U (-2) u) at hw
      rw [hv] at hw
      exact hw.symm
    have hBJ (u : smoothSections (n := n) (r := r) E) :
        B (f (J.toLinearMap u)) = f u := by
      apply (connectionLaplacianInverse_graph μ g h cov hcov hcomplex _ _).mp
      let T := connectionLaplacianSmoothCore μ g h cov hcov hcomplex
      apply LinearPMap.le_graph_of_le T.le_closure
      let e := LinearEquiv.ofInjective f (h.smoothToL2_injective μ)
      refine T.mem_graph_iff.mpr ⟨e u, rfl, ?_⟩
      change f (e.symm (e u) + D.toLinearMap (e.symm (e u))) = f (J.toLinearMap u)
      rw [e.symm_apply_apply]
      rfl
    have hJU : J.toLinearMap = (U 2).toLinearMap := by
      apply LinearMap.ext
      intro u
      apply h.smoothToL2_injective μ
      apply hBinj
      rw [hBJ]
      have heq := hBnegative (U 2 u)
      have hnegative : U (-2) = (U 2).symm :=
        connectionLaplacianSmoothPower_neg μ g h cov hcov hcomplex 2
      rw [hnegative, LinearEquiv.symm_apply_apply] at heq
      exact heq
    have hI : I.principalSymbol = 0 := by
      apply I.principalSymbol_eq_zero_iff.mpr
      exact IsPseudodifferentialOperator.mono (by norm_num : (0 : ℝ) ≤ 2 - 1)
        LinearMap.id (isPseudodifferentialOperator_id μ)
    refine ⟨a, J, ha, hJU, ?_⟩
    rw [PseudodifferentialOperator.principalSymbol_add, hI, zero_add]
    exact D.principalSymbol_eq_regularizedSymbol μ R
  -- Two copies of the already constructed half inverse give the negative generator.
  have hminusOne : H (-1) := by
    have hh := hfraction (1 / 2) (by norm_num) (by norm_num)
    norm_num only at hh
    exact hh
  have hminusTwo : H (-2) := by
    have hh := hadd (-1) (-1) hminusOne hminusOne
    norm_num only at hh
    exact hh
  have hzero : H 0 := by
    have hh := hadd 2 (-2) htwo hminusTwo
    norm_num only at hh
    exact hh
  have hnat (d : ℝ) (hd : H d) (k : ℕ) : H (d * (k : ℝ)) := by
    induction k with
    | zero => simpa only [Nat.cast_zero, mul_zero] using hzero
    | succ k hk =>
      have heq : d * ((k + 1 : ℕ) : ℝ) = d + d * (k : ℝ) := by push_cast; ring
      rw [heq]
      exact hadd _ _ hd hk
  have hint (z : ℤ) : H (2 * (z : ℝ)) := by
    cases z with
    | ofNat k => exact hnat 2 htwo k
    | negSucc k =>
      have heq : 2 * ((Int.negSucc k : ℤ) : ℝ) = (-2 : ℝ) * ((k + 1 : ℕ) : ℝ) := by
        rw [Int.cast_negSucc]
        push_cast
        ring
      rw [heq]
      exact hnat (-2) hminusTwo (k + 1)
  -- The same ceiling decomposition covers every signed real order and the integer endpoints.
  let z : ℤ := ⌈l / 2⌉
  let p : ℝ := (z : ℝ) - l / 2
  have hp : 0 ≤ p := sub_nonneg.mpr (Int.le_ceil (l / 2))
  have hp1 : p < 1 := by
    dsimp only [p, z]
    linarith [Int.ceil_lt_add_one (l / 2)]
  have hord : l = 2 * (z : ℝ) + -2 * p := by dsimp only [p]; ring
  change H l
  rcases eq_or_lt_of_le hp with hzero | hpos
  · have heq : l = 2 * (z : ℝ) := by rw [← hzero] at hord; simpa using hord
    rw [heq]
    exact hint z
  · rw [hord]
    exact hadd _ _ (hint z) (hfraction p hpos hp1)

end AtiyahSinger
