/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianIntegerPowers
public import AtiyahSinger.Analysis.ConnectionLaplacianResolventIntegral

/-!
# Uniform integer Sobolev estimates for the original spectral resolvent

Public module ID: M0398.

Every bounded operator commuting with the original positive inverse preserves
its smooth-section image. The smooth restriction has an even-order Sobolev bound
proportional to the original L2 norm, with a constant chosen before the commuting
operator. The specified scaled resolvent therefore has uniform bounds at each
nonnegative even Sobolev level.

The argument uses integer PDO powers and the original spectral graphs. These
estimates control the actual finite-resolvent remainders in the construction of
fractional powers, without using fractional PDO membership or interpolation.
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

/-- The bounded commutant preserves smooth sections with uniform even Sobolev control. -/
theorem exists_connectionLaplacian_commutant_sobolev_bound
    (A : SmoothBundlePresentation (n := n) (r := r) E) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : h.L2SectionSpace μ →L[ℂ] h.L2SectionSpace μ,
      Commute T (connectionLaplacianInverse μ g h cov hcov hcomplex) →
      ∃! U : smoothSections (n := n) (r := r) E →ₗ[ℂ]
          smoothSections (n := n) (r := r) E,
        (∀ u : smoothSections (n := n) (r := r) E,
          h.smoothToL2 μ (U u) = T (h.smoothToL2 μ u)) ∧
        ∀ u : smoothSections (n := n) (r := r) E,
          ‖A.smoothToSobolev (2 * (k : ℝ)) (U u)‖ ≤
            C * ‖T‖ * ‖A.smoothToSobolev (2 * (k : ℝ)) u‖ := by
  classical
  let H := h.L2SectionSpace μ
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  let f := h.smoothToL2 μ
  let W := connectionLaplacianSmoothPower μ g h cov hcov hcomplex
  let a : ℝ := 2 * (k : ℝ)
  have hf : Function.Injective f := h.smoothToL2_injective μ
  have hB : 0 ≤ B :=
    (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).1
  -- The integer graphs identify the original inverse powers, including k = 0.
  have hnegative (u : smoothSections (n := n) (r := r) E) :
      f (W (-a) u) = (B ^ k) (f u) := by
    have hg := connectionLaplacianSmoothPower_graph μ g h cov hcov hcomplex (-a) u
    have hsign : -a ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg k))
    have hexp : -(-a) / 2 = (k : ℝ) := by dsimp [a]; ring
    rw [connectionLaplacianSpectralPower, ite_eq_left hsign, hexp] at hg
    change (f u, f (W (-a) u)) ∈
      ((CFC.rpow B (k : ℝ)).toLinearMap.toPMap ⊤).graph at hg
    have hnat : CFC.rpow B (k : ℝ) = B ^ k := CFC.rpow_natCast B k hB
    rw [hnat] at hg
    obtain ⟨x, hx, hy⟩ := (LinearPMap.mem_graph_iff _).mp hg
    change (x : H) = f u at hx
    change (B ^ k) (x : H) = f (W (-a) u) at hy
    rw [hx] at hy
    exact hy.symm
  have hinverse (u : smoothSections (n := n) (r := r) E) : W (-a) (W a u) = u := by
    change connectionLaplacianSmoothPower μ g h cov hcov hcomplex (-a)
      (connectionLaplacianSmoothPower μ g h cov hcov hcomplex a u) = u
    rw [connectionLaplacianSmoothPower_neg]
    exact (W a).symm_apply_apply u
  have hpositive (u : smoothSections (n := n) (r := r) E) :
      (B ^ k) (f (W a u)) = f u := by
    simpa only [hinverse u] using (hnegative (W a u)).symm
  have hpowinj : Function.Injective ((B ^ k : H →L[ℂ] H) : H → H) := by
    rw [← CFC.rpow_natCast B k hB]
    exact (connectionLaplacianInverse_rpow_properties μ g h cov hcov hcomplex
      (k : ℝ) (Nat.cast_nonneg k)).2.1
  -- Choose all Sobolev and metric comparison constants before choosing T.
  have hplus : IsPseudodifferentialOperator E E μ a (W a).toLinearMap := by
    simpa only [Int.cast_natCast, a] using
      isPseudodifferentialOperator_connectionLaplacianSmoothPower_int
        μ g h cov hcov hcomplex (k : ℤ)
  have hminus : IsPseudodifferentialOperator E E μ (-a) (W (-a)).toLinearMap := by
    simpa only [Int.cast_neg, Int.cast_natCast, mul_neg, a] using
      isPseudodifferentialOperator_connectionLaplacianSmoothPower_int
        μ g h cov hcov hcomplex (-(k : ℤ))
  let P : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ a :=
    ⟨(W a).toLinearMap, hplus⟩
  let Q : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ (-a) :=
    ⟨(W (-a)).toLinearMap, hminus⟩
  obtain ⟨Cp, hCp, hP⟩ := P.exists_norm_smoothToSobolev_apply_le A A a
  obtain ⟨Cq, hCq, hQ⟩ := Q.exists_norm_smoothToSobolev_apply_le A A 0
  have hPbound (u : smoothSections (n := n) (r := r) E) :
      ‖A.smoothToSobolev 0 (W a u)‖ ≤ Cp * ‖A.smoothToSobolev a u‖ := by
    have hp := hP u
    change ‖A.smoothToSobolev (a - a) (W a u)‖ ≤
      Cp * ‖A.smoothToSobolev a u‖ at hp
    rw [show a - a = 0 from sub_self a] at hp
    exact hp
  have hQbound (u : smoothSections (n := n) (r := r) E) :
      ‖A.smoothToSobolev a (W (-a) u)‖ ≤ Cq * ‖A.smoothToSobolev 0 u‖ := by
    have hq := hQ u
    change ‖A.smoothToSobolev (0 - -a) (W (-a) u)‖ ≤
      Cq * ‖A.smoothToSobolev 0 u‖ at hq
    rw [show (0 : ℝ) - -a = a by ring] at hq
    exact hq
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  have he (u : smoothSections (n := n) (r := r) E) : e (A.smoothToSobolev 0 u) = f u :=
    h.sobolevZeroEquivL2_smooth (μ := μ) A u
  have hforward (u : smoothSections (n := n) (r := r) E) :
      ‖f u‖ ≤ ‖e.toContinuousLinearMap‖ * ‖A.smoothToSobolev 0 u‖ := by
    rw [← he u]
    exact e.toContinuousLinearMap.le_opNorm _
  have hbackward (u : smoothSections (n := n) (r := r) E) :
      ‖A.smoothToSobolev 0 u‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖f u‖ := by
    rw [← he u]
    have hb := e.symm.toContinuousLinearMap.le_opNorm (e (A.smoothToSobolev 0 u))
    change ‖e.symm (e (A.smoothToSobolev 0 u))‖ ≤
      ‖e.symm.toContinuousLinearMap‖ * ‖e (A.smoothToSobolev 0 u)‖ at hb
    rw [e.symm_apply_apply] at hb
    exact hb
  let C : ℝ := Cq * ‖e.symm.toContinuousLinearMap‖ * ‖e.toContinuousLinearMap‖ * Cp
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T hTB
  -- Commutation preserves each integer inverse range and hence the smooth image.
  have hW (x : H) : x ∈ Set.range f ↔
      ∀ j : ℕ, x ∈ Set.range (B ^ j : H →L[ℂ] H) :=
    mem_range_smoothToL2_iff_forall_mem_range_pow_connectionLaplacianInverse
      μ g h cov hcov hcomplex x
  let S : smoothSections (n := n) (r := r) E →ₗ[ℂ] H := T.toLinearMap.comp f
  have hS (u : smoothSections (n := n) (r := r) E) : S u ∈ f.range := by
    change T (f u) ∈ Set.range f
    apply (hW _).mpr
    intro j
    obtain ⟨y, hy⟩ := (hW (f u)).mp ⟨u, rfl⟩ j
    refine ⟨T y, ?_⟩
    have hc := congrArg (fun R : H →L[ℂ] H ↦ R y) (hTB.pow_right j).eq
    change T ((B ^ j) y) = (B ^ j) (T y) at hc
    rw [hy] at hc
    exact hc.symm
  let ef := LinearEquiv.ofInjective f hf
  let U := ef.symm.toLinearMap.comp (S.codRestrict f.range hS)
  have hU (u : smoothSections (n := n) (r := r) E) : f (U u) = T (f u) :=
    congrArg Subtype.val (ef.apply_symm_apply ⟨S u, hS u⟩)
  -- Cancel the same injective B^k to commute T with the positive smooth power.
  have hcommute (u : smoothSections (n := n) (r := r) E) :
      f (W a (U u)) = T (f (W a u)) := by
    apply hpowinj
    have hc := congrArg (fun R : H →L[ℂ] H ↦ R (f (W a u))) (hTB.pow_right k).eq
    change T ((B ^ k) (f (W a u))) = (B ^ k) (T (f (W a u))) at hc
    rw [hpositive u] at hc
    exact (hpositive (U u)).trans ((hU u).trans hc)
  refine ⟨U, ⟨hU, ?_⟩, ?_⟩
  · intro u
    change ‖A.smoothToSobolev a (U u)‖ ≤ C * ‖T‖ * ‖A.smoothToSobolev a u‖
    calc
      _ = ‖A.smoothToSobolev a (W (-a) (W a (U u)))‖ := by rw [hinverse]
      _ ≤ Cq * ‖A.smoothToSobolev 0 (W a (U u))‖ := hQbound _
      _ ≤ Cq * (‖e.symm.toContinuousLinearMap‖ * ‖f (W a (U u))‖) :=
        mul_le_mul_of_nonneg_left (hbackward _) hCq.le
      _ = Cq * (‖e.symm.toContinuousLinearMap‖ * ‖T (f (W a u))‖) := by
        rw [hcommute]
      _ ≤ Cq * (‖e.symm.toContinuousLinearMap‖ * (‖T‖ * ‖f (W a u)‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)) hCq.le
      _ ≤ Cq * (‖e.symm.toContinuousLinearMap‖ *
          (‖T‖ * (‖e.toContinuousLinearMap‖ * ‖A.smoothToSobolev 0 (W a u)‖))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hforward _) (norm_nonneg _))
            (norm_nonneg _)) hCq.le
      _ ≤ Cq * (‖e.symm.toContinuousLinearMap‖ *
          (‖T‖ * (‖e.toContinuousLinearMap‖ * (Cp * ‖A.smoothToSobolev a u‖)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hPbound u) (norm_nonneg _))
              (norm_nonneg _)) (norm_nonneg _)) hCq.le
      _ = C * ‖T‖ * ‖A.smoothToSobolev a u‖ := by dsimp [C]; ring
  · intro V hV
    apply LinearMap.ext
    intro u
    apply hf
    exact (hV.1 u).trans (hU u).symm

/-- The original scaled resolvent has uniform bounds at every nonnegative even Sobolev order. -/
theorem exists_connectionLaplacianScaledResolvent_sobolev_bound
    (A : SmoothBundlePresentation (n := n) (r := r) E) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      ∃ U : smoothSections (n := n) (r := r) E →ₗ[ℂ]
          smoothSections (n := n) (r := r) E,
        (∀ u : smoothSections (n := n) (r := r) E,
          h.smoothToL2 μ (U u) =
            connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t
              (h.smoothToL2 μ u)) ∧
        ∀ u : smoothSections (n := n) (r := r) E,
          ‖A.smoothToSobolev (2 * (k : ℝ)) (U u)‖ ≤
            (C / (1 + t)) * ‖A.smoothToSobolev (2 * (k : ℝ)) u‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_connectionLaplacian_commutant_sobolev_bound μ g h cov hcov hcomplex A k
  refine ⟨C, hC, ?_⟩
  intro t ht
  let H := h.L2SectionSpace μ
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  let D : H →L[ℂ] H := t • (1 : H →L[ℂ] H) + B
  have hDB : Commute D B := by
    change (t • (1 : H →L[ℂ] H) + B) * B = B * (t • (1 : H →L[ℂ] H) + B)
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hIB : Commute (Ring.inverse D) B := by
    by_cases hD : IsUnit D
    · obtain ⟨d, hd⟩ := hD
      rw [← hd, Ring.inverse_unit]
      exact (show Commute (d : H →L[ℂ] H) B from hd.symm ▸ hDB).units_inv_left
    · rw [Ring.inverse_non_unit D hD]
      exact Commute.zero_left B
  have hcommute : Commute
      (connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t) B := by
    change (B * Ring.inverse D) * B = B * (B * Ring.inverse D)
    rw [mul_assoc, hIB.eq, ← mul_assoc]
  obtain ⟨U, hU, _⟩ :=
    hbound (connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t) hcommute
  refine ⟨U, hU.1, ?_⟩
  intro u
  have hnorm :=
    (connectionLaplacianScaledResolvent_properties μ g h cov hcov hcomplex t ht).2
  calc
    _ ≤ C * ‖connectionLaplacianScaledResolvent μ g h cov hcov hcomplex t‖ *
        ‖A.smoothToSobolev (2 * (k : ℝ)) u‖ := hU.2 u
    _ ≤ C * (1 + t)⁻¹ * ‖A.smoothToSobolev (2 * (k : ℝ)) u‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hC) (norm_nonneg _)
    _ = (C / (1 + t)) * ‖A.smoothToSobolev (2 * (k : ℝ)) u‖ := by rw [div_eq_mul_inv]

end AtiyahSinger
