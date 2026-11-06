/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.L2Sections
public import AtiyahSinger.Analysis.PseudodifferentialDensity
public import AtiyahSinger.Analysis.SmoothSectionMultiplication

/-!
# Density changes in the integral L² model

Public module ID: M0776.

The identity on smooth sections extends to a canonical bounded equivalence
of the two L² completions on a compact base. A different comparison,
multiplication by sqrt(dμ/dν), is unitary. It usually does not intertwine
the unchanged operator. Order-zero PDOs have bounded L² realizations;
ellipticity gives the Fredholm and smooth-index comparisons. Positive-order
PDOs are not claimed to be bounded L² maps.
Sources: SG III.2 (2.17), III.5.2--5.3; the two density transports are project comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hHE : IsSmoothHermitianBundle (n := n) (r := r) E]
  (μ ν : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hT2 hSC hC hE hHE hμ hν


set_option linter.unusedSectionVars false in
-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Changing density inserts the positive ratio in the second slot of the Hermitian pairing. -/
theorem smoothSectionPairing_changeMeasure
    (u v : smoothSections (n := n) (r := r) E) :
    smoothSectionPairing ν E u v = smoothSectionPairing μ E u
      (smoothSectionMul (n := n) (r := r) E
        (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
        (contMDiff_complex_smoothDensityRatio μ ν) v) := by
  /- Write the ν integral as the μ integral weighted by dν/dμ. The Hermitian
  pairing is linear in its second slot, so the real weight is multiplication
  of v. The first slot remains conjugate-linear under the mathlib convention. -/
  unfold smoothSectionPairing
  rw [integral_smoothDensityRatio (n := n) μ ν]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change (smoothDensityRatio (n := n) μ ν x : ℂ) * inner ℂ (u.val x) (v.val x) =
      inner ℂ (u.val x) ((smoothDensityRatio (n := n) μ ν x : ℂ) • v.val x)
    rw [inner_smul_right]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Two positive smooth densities give equivalent integral norms on the same smooth sections. -/
theorem exists_l2_density_norm_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      c * ‖smoothToL2 μ E u‖ ≤ ‖smoothToL2 ν E u‖ ∧
        ‖smoothToL2 ν E u‖ ≤ C * ‖smoothToL2 μ E u‖ := by
  /- Bound dν/dμ uniformly above and away from zero on the compact base.
  Multiply these inequalities by the nonnegative squared pointwise norm and
  integrate against μ. The exact integral norm formulas and positive square
  roots give the two bounds. On an empty base all section norms are zero. -/
  obtain ⟨c, C, hc, hC, hbound⟩ := exists_smoothDensityRatio_bounds (n := n) μ ν
  refine ⟨Real.sqrt c, Real.sqrt C, Real.sqrt_pos.mpr hc, Real.sqrt_pos.mpr hC, ?_⟩
  intro u
  -- Both real integrands are integrable for the same original section and density.
  have hint : Integrable (fun x ↦ ‖u.val x‖ ^ 2) μ := by
    simpa [← Complex.ofReal_pow] using (integrable_inner_smoothSections (n := n) μ E u u).re
  let v := smoothSectionMul (n := n) (r := r) E
    (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
    (contMDiff_complex_smoothDensityRatio μ ν) u
  have hweighted :
      Integrable (fun x ↦ smoothDensityRatio (n := n) μ ν x * ‖u.val x‖ ^ 2) μ := by
    apply (integrable_inner_smoothSections (n := n) μ E u v).re.congr
    exact Filter.Eventually.of_forall fun x ↦ by
      change (inner ℂ (u.val x)
        ((smoothDensityRatio (n := n) μ ν x : ℂ) • u.val x)).re = _
      rw [inner_smul_right]
      simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hchange : ‖smoothToL2 ν E u‖ ^ 2 =
      ∫ x, smoothDensityRatio (n := n) μ ν x * ‖u.val x‖ ^ 2 ∂μ := by
    rw [norm_smoothToL2_sq]
    conv_lhs => rw [← withDensity_smoothDensityRatio (n := n) μ ν]
    rw [integral_withDensity_eq_integral_toReal_smul
      (contMDiff_smoothDensityRatio (n := n) μ ν).continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      dsimp only
      rw [ENNReal.toReal_ofReal (smoothDensityRatio_pos (n := n) μ ν x).le]
      rfl
  -- Integrating the positive lower and upper bounds compares the squared norms.
  have hlower : c * ‖smoothToL2 μ E u‖ ^ 2 ≤ ‖smoothToL2 ν E u‖ ^ 2 := by
    calc
      c * ‖smoothToL2 μ E u‖ ^ 2 = ∫ x, c * ‖u.val x‖ ^ 2 ∂μ := by
        rw [norm_smoothToL2_sq, integral_const_mul]
      _ ≤ ∫ x, smoothDensityRatio (n := n) μ ν x * ‖u.val x‖ ^ 2 ∂μ :=
        integral_mono (hint.const_mul c) hweighted
          (fun x ↦ mul_le_mul_of_nonneg_right (hbound x).1 (sq_nonneg _))
      _ = ‖smoothToL2 ν E u‖ ^ 2 := hchange.symm
  have hupper : ‖smoothToL2 ν E u‖ ^ 2 ≤ C * ‖smoothToL2 μ E u‖ ^ 2 := by
    calc
      ‖smoothToL2 ν E u‖ ^ 2 =
          ∫ x, smoothDensityRatio (n := n) μ ν x * ‖u.val x‖ ^ 2 ∂μ := hchange
      _ ≤ ∫ x, C * ‖u.val x‖ ^ 2 ∂μ :=
        integral_mono hweighted (hint.const_mul C)
          (fun x ↦ mul_le_mul_of_nonneg_right (hbound x).2 (sq_nonneg _))
      _ = C * ‖smoothToL2 μ E u‖ ^ 2 := by
        rw [integral_const_mul, norm_smoothToL2_sq]
  -- Nonnegativity permits taking square roots without changing either actual norm.
  constructor
  · apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _))
      (norm_nonneg _)).mp
    simpa only [mul_pow, Real.sq_sqrt hc.le] using hlower
  · apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hC.le] using hupper

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Multiplication by sqrt(dμ/dν) preserves the integral norm when the target density is ν. -/
theorem norm_smoothToL2_sqrt_densityRatio (u : smoothSections (n := n) (r := r) E) :
    ‖smoothToL2 ν E (smoothSectionMul (n := n) (r := r) E
        (fun x ↦ (Real.sqrt (smoothDensityRatio (n := n) ν μ x) : ℂ))
        (contMDiff_complex_sqrt_smoothDensityRatio ν μ) u)‖ = ‖smoothToL2 μ E u‖ := by
  /- Square both nonnegative norms and use their actual integral formulas.
  The multiplier has squared modulus dμ/dν by positivity. This factor cancels
  the target density change, giving the original integral. Take nonnegative roots. -/
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_smoothToL2_sq, norm_smoothToL2_sq]
  have hchange : (∫ x, ‖u.val x‖ ^ 2 ∂μ) =
      ∫ x, smoothDensityRatio (n := n) ν μ x * ‖u.val x‖ ^ 2 ∂ν := by
    conv_lhs => rw [← withDensity_smoothDensityRatio (n := n) ν μ]
    rw [integral_withDensity_eq_integral_toReal_smul
      (contMDiff_smoothDensityRatio (n := n) ν μ).continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      dsimp only
      rw [ENNReal.toReal_ofReal (smoothDensityRatio_pos (n := n) ν μ x).le]
      rfl
  rw [hchange]
  -- The original positive ratio fixes the square root and its squared fiber multiplier.
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖(Real.sqrt (smoothDensityRatio (n := n) ν μ x) : ℂ) • u.val x‖ ^ 2 =
      smoothDensityRatio (n := n) ν μ x * ‖u.val x‖ ^ 2
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (smoothDensityRatio_pos (n := n) ν μ x).le]

namespace SmoothBundlePresentation

variable {E} (A : SmoothBundlePresentation (n := n) (r := r) E)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The bounded L² comparison extends identity on the underlying smooth sections. -/
def l2ChangeMeasure : L2SectionSpace (n := n) (r := r) μ E ≃L[ℂ]
    L2SectionSpace (n := n) (r := r) ν E :=
  (A.sobolevZeroEquivL2 μ).symm.trans (A.sobolevZeroEquivL2 ν)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The canonical bounded comparison preserves the actual smooth section. -/
theorem l2ChangeMeasure_smoothToL2 (u : smoothSections (n := n) (r := r) E) :
    A.l2ChangeMeasure μ ν (smoothToL2 μ E u) = smoothToL2 ν E u := by
  /- The inverse H⁰--L² comparison sends the μ embedding to the original
  H⁰ smooth vector. The forward comparison at ν sends that vector to the
  ν embedding of the same section. No scalar multiplier is inserted. -/
  change A.sobolevZeroEquivL2 ν ((A.sobolevZeroEquivL2 μ).symm (smoothToL2 μ E u)) =
    smoothToL2 ν E u
  rw [← A.sobolevZeroEquivL2_smoothToSobolev μ u,
    ContinuousLinearEquiv.symm_apply_apply, A.sobolevZeroEquivL2_smoothToSobolev ν u]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The identity comparison is independent of the presentation used to construct it. -/
theorem l2ChangeMeasure_eq (B : SmoothBundlePresentation (n := n) (r := r) E) :
    A.l2ChangeMeasure μ ν = B.l2ChangeMeasure μ ν := by
  /- Both continuous maps agree on the dense μ-smooth image by the preceding
  formula. Their underlying maps therefore agree everywhere; the inverse maps
  and continuity proofs are determined by this continuous linear equivalence. -/
  apply ContinuousLinearEquiv.ext
  apply (denseRange_smoothToL2 μ E).equalizer
    (A.l2ChangeMeasure μ ν).continuous (B.l2ChangeMeasure μ ν).continuous
  funext u
  change A.l2ChangeMeasure μ ν (smoothToL2 μ E u) = B.l2ChangeMeasure μ ν (smoothToL2 μ E u)
  rw [A.l2ChangeMeasure_smoothToL2 μ ν u, B.l2ChangeMeasure_smoothToL2 μ ν u]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Consecutive identity comparisons agree with direct change of density. -/
theorem l2ChangeMeasure_trans (κ : Measure M) [IsSmoothPositiveMeasure (n := n) κ] :
    (A.l2ChangeMeasure μ ν).trans (A.l2ChangeMeasure ν κ) = A.l2ChangeMeasure μ κ := by
  /- In the concrete construction the middle H⁰--L² maps cancel. Alternatively
  all maps send a dense smooth section to itself, so continuity gives equality.
  This identity is for bounded equivalences, without an isometry assertion. -/
  apply ContinuousLinearEquiv.ext
  funext u
  change A.sobolevZeroEquivL2 κ
      ((A.sobolevZeroEquivL2 ν).symm
        (A.sobolevZeroEquivL2 ν ((A.sobolevZeroEquivL2 μ).symm u))) =
    A.sobolevZeroEquivL2 κ ((A.sobolevZeroEquivL2 μ).symm u)
  rw [ContinuousLinearEquiv.symm_apply_apply]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
omit hν in
/-- Comparing a density with itself gives the identity continuous linear equivalence. -/
theorem l2ChangeMeasure_self :
    A.l2ChangeMeasure μ μ = ContinuousLinearEquiv.refl ℂ
      (L2SectionSpace (n := n) (r := r) μ E) := by
  /- The defining continuous equivalence is one fixed H⁰--L² equivalence
  composed with its inverse. Its function is the identity on the entire completion. -/
  apply ContinuousLinearEquiv.ext
  funext u
  exact (A.sobolevZeroEquivL2 μ).apply_symm_apply u

end SmoothBundlePresentation

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- There is a unique unitary comparison extending the positive square-root multiplier. -/
theorem existsUnique_l2DensityIsometry :
    ∃! T : L2SectionSpace (n := n) (r := r) μ E ≃ₗᵢ[ℂ]
        L2SectionSpace (n := n) (r := r) ν E,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (smoothToL2 μ E u) = smoothToL2 ν E
          (smoothSectionMul (n := n) (r := r) E
        (fun x ↦ (Real.sqrt (smoothDensityRatio (n := n) ν μ x) : ℂ))
        (contMDiff_complex_sqrt_smoothDensityRatio ν μ) u) := by
  /- The multiplier is linear and preserves the integral norm by the exact
  density cancellation. Extend it isometrically to the completion. The positive
  reciprocal square-root multiplier provides the inverse on the dense smooth
  images, then everywhere by continuity. Density gives uniqueness of the isometry. -/
  let f := smoothSectionMul (n := n) (r := r) E
    (fun x ↦ (Real.sqrt (smoothDensityRatio (n := n) ν μ x) : ℂ))
    (contMDiff_complex_sqrt_smoothDensityRatio ν μ)
  have hbijective : Function.Bijective f :=
    smoothSectionMul_bijective (n := n) (r := r) E _ _ (fun x ↦
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
        (smoothDensityRatio_pos (n := n) ν μ x)).ne')
  let e := LinearEquiv.ofBijective f hbijective
  have hnorm (u : smoothSections (n := n) (r := r) E) :
      ‖smoothToL2 ν E (e u)‖ = ‖smoothToL2 μ E u‖ :=
    norm_smoothToL2_sqrt_densityRatio E μ ν u
  -- Extend this actual invertible multiplier, rather than an arbitrary Hilbert isomorphism.
  let T := e.extendOfIsometry (smoothToL2 μ E) (smoothToL2 ν E)
    (denseRange_smoothToL2 μ E) (denseRange_smoothToL2 ν E) hnorm
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (smoothToL2 μ E u) = smoothToL2 ν E (f u) :=
    e.extendOfIsometry_eq _ _ _ _ _ u
  refine ⟨T, hT, ?_⟩
  -- The original smooth image is dense in the same μ completion.
  intro S hS
  have heq : (S : L2SectionSpace (n := n) (r := r) μ E →
      L2SectionSpace (n := n) (r := r) ν E) = T := by
    apply (denseRange_smoothToL2 μ E).equalizer S.continuous T.continuous
    funext u
    exact (hS u).trans (hT u).symm
  exact LinearIsometryEquiv.ext (congrFun heq)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The canonical unitary density comparison, distinct from identity transport. -/
def l2DensityIsometry : L2SectionSpace (n := n) (r := r) μ E ≃ₗᵢ[ℂ]
    L2SectionSpace (n := n) (r := r) ν E :=
  Classical.choose (existsUnique_l2DensityIsometry E μ ν).exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The unitary comparison has the prescribed square-root weight on actual smooth sections. -/
theorem l2DensityIsometry_smoothToL2 (u : smoothSections (n := n) (r := r) E) :
    l2DensityIsometry E μ ν (smoothToL2 μ E u) = smoothToL2 ν E
      (smoothSectionMul (n := n) (r := r) E
        (fun x ↦ (Real.sqrt (smoothDensityRatio (n := n) ν μ x) : ℂ))
        (contMDiff_complex_sqrt_smoothDensityRatio ν μ) u) := by
  /- Apply the witness property of the unique isometric equivalence. The
  positive real square root fixes the phase; an arbitrary unitary identification
  of Hilbert spaces would not satisfy this specific geometric formula. -/
  exact Classical.choose_spec (existsUnique_l2DensityIsometry E μ ν).exists u

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The positive square-root isometry has the reverse-density isometry as its inverse. -/
theorem l2DensityIsometry_symm :
    (l2DensityIsometry (n := n) (r := r) E μ ν).symm = l2DensityIsometry E ν μ := by
  /- On smooth sections the two positive square-root factors multiply to one.
  Their extensions therefore compose to identity on dense subspaces and hence
  everywhere. Uniqueness identifies the reversed map with the inverse isometry. -/
  have heq : ((l2DensityIsometry E μ ν).symm : L2SectionSpace (n := n) (r := r) ν E →
      L2SectionSpace (n := n) (r := r) μ E) = l2DensityIsometry E ν μ := by
    apply (denseRange_smoothToL2 ν E).equalizer
      (l2DensityIsometry E μ ν).symm.continuous (l2DensityIsometry E ν μ).continuous
    funext u
    change (l2DensityIsometry E μ ν).symm (smoothToL2 ν E u) =
      l2DensityIsometry E ν μ (smoothToL2 ν E u)
    -- Test the inverse law on this same ν-smooth section using the original forward map.
    apply (l2DensityIsometry E μ ν).injective
    rw [LinearIsometryEquiv.apply_symm_apply, l2DensityIsometry_smoothToL2,
      l2DensityIsometry_smoothToL2]
    congr 1
    apply Subtype.ext
    funext x
    have hratio : smoothDensityRatio (n := n) ν μ x *
        smoothDensityRatio (n := n) μ ν x = 1 := by
      rw [← smoothDensityRatio_mul (n := n) ν μ ν x, smoothDensityRatio_self]
    have hsqrt : Real.sqrt (smoothDensityRatio (n := n) ν μ x) *
        Real.sqrt (smoothDensityRatio (n := n) μ ν x) = 1 := by
      rw [← Real.sqrt_mul (smoothDensityRatio_pos (n := n) ν μ x).le,
        hratio, Real.sqrt_one]
    change u.val x = (Real.sqrt (smoothDensityRatio (n := n) ν μ x) : ℂ) •
      ((Real.sqrt (smoothDensityRatio (n := n) μ ν x) : ℂ) • u.val x)
    rw [smul_smul, ← Complex.ofReal_mul, hsqrt, Complex.ofReal_one, one_smul]
  exact LinearIsometryEquiv.ext (congrFun heq)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The chosen positive square roots make the unitary comparisons obey a cocycle law. -/
theorem l2DensityIsometry_trans (κ : Measure M) [IsSmoothPositiveMeasure (n := n) κ] :
    (l2DensityIsometry (n := n) (r := r) E μ ν).trans (l2DensityIsometry E ν κ) =
      l2DensityIsometry E μ κ := by
  /- On the dense smooth image the product sqrt(dμ/dν) sqrt(dν/dκ) is
  sqrt(dμ/dκ), by strict positivity and the density cocycle. Extend the resulting
  multiplier equality to the completions by continuity and the unique specification. -/
  have heq : ((l2DensityIsometry E μ ν).trans (l2DensityIsometry E ν κ) :
      L2SectionSpace (n := n) (r := r) μ E → L2SectionSpace (n := n) (r := r) κ E) =
        l2DensityIsometry E μ κ := by
    apply (denseRange_smoothToL2 μ E).equalizer
      ((l2DensityIsometry E μ ν).trans (l2DensityIsometry E ν κ)).continuous
      (l2DensityIsometry E μ κ).continuous
    funext u
    change l2DensityIsometry E ν κ
        (l2DensityIsometry E μ ν (smoothToL2 μ E u)) =
      l2DensityIsometry E μ κ (smoothToL2 μ E u)
    rw [l2DensityIsometry_smoothToL2, l2DensityIsometry_smoothToL2,
      l2DensityIsometry_smoothToL2]
    congr 1
    apply Subtype.ext
    funext x
    -- The κ-to-μ ratio factors in precisely the order of the two fiber multipliers.
    change (Real.sqrt (smoothDensityRatio (n := n) κ ν x) : ℂ) •
        ((Real.sqrt (smoothDensityRatio (n := n) ν μ x) : ℂ) • u.val x) =
      (Real.sqrt (smoothDensityRatio (n := n) κ μ x) : ℂ) • u.val x
    rw [smul_smul, ← Complex.ofReal_mul,
      ← Real.sqrt_mul (smoothDensityRatio_pos (n := n) κ ν x).le,
      ← smoothDensityRatio_mul (n := n) κ ν μ x]
  exact LinearIsometryEquiv.ext (congrFun heq)

variable {q : ℕ} {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hHF : IsSmoothHermitianBundle (n := n) (r := q) F]

include hF hHF

omit hν

namespace PseudodifferentialOperator

variable {E μ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- An order-zero PDO extends uniquely to the actual integral L² completions. -/
theorem existsUnique_l2Extension :
    ∃! T : L2SectionSpace (n := n) (r := r) μ E →L[ℂ]
        L2SectionSpace (n := n) (r := q) μ F,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (smoothToL2 μ E u) = smoothToL2 μ F (P.toLinearMap u) := by
  /- Choose finite presentations and conjugate P's H⁰ to H^(0-0) extension
  by the two canonical H⁰--L² comparisons, identifying 0-0 with 0.
  This gives a bounded map with the displayed smooth action. The dense smooth
  input forces uniqueness. This argument does not assert boundedness for positive order. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let e := A.sobolevZeroEquivL2 μ
  let f := B.sobolevZeroEquivL2 μ
  -- Both comparisons carry the original smooth section to its own integral completion.
  let T := f.toContinuousLinearMap.comp
    ((P.sobolevRealization A B 0 0 (by simp)).comp e.symm.toContinuousLinearMap)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (smoothToL2 μ E u) = smoothToL2 μ F (P.toLinearMap u) := by
    have he : e (A.smoothToSobolev 0 u) = smoothToL2 μ E u :=
      A.sobolevZeroEquivL2_smoothToSobolev μ u
    change f (P.sobolevRealization A B 0 0 (by simp)
      (e.symm (smoothToL2 μ E u))) = _
    rw [← he, e.symm_apply_apply, P.sobolevRealization_smoothToSobolev]
    exact B.sobolevZeroEquivL2_smoothToSobolev μ (P.toLinearMap u)
  refine ⟨T, hT, ?_⟩
  -- The same dense smooth image determines every bounded realization uniquely.
  intro S hS
  apply DFunLike.coe_injective
  apply (denseRange_smoothToL2 μ E).equalizer S.continuous T.continuous
  funext u
  exact (hS u).trans (hT u).symm

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The order-zero PDO realization on the actual integral L² spaces. -/
def l2Extension : L2SectionSpace (n := n) (r := r) μ E →L[ℂ]
    L2SectionSpace (n := n) (r := q) μ F :=
  Classical.choose P.existsUnique_l2Extension.exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The L² realization extends exactly the given smooth-section action. -/
theorem l2Extension_smoothToL2 (u : smoothSections (n := n) (r := r) E) :
    P.l2Extension (smoothToL2 μ E u) = smoothToL2 μ F (P.toLinearMap u) := by
  /- Extract the unique extension's action specification. The result retains
  the original PDO map, rather than an operator with only the same principal class. -/
  exact P.existsUnique_l2Extension.exists.choose_spec u

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
include hν in
/-- Identity density comparisons intertwine the unchanged order-zero operator. -/
theorem l2Extension_changeMeasure
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) :
    (B.l2ChangeMeasure μ ν).toContinuousLinearMap.comp P.l2Extension =
      (P.changeMeasure ν).l2Extension.comp (A.l2ChangeMeasure μ ν).toContinuousLinearMap := by
  /- Both sides send each dense smooth input to the ν embedding of Pu.
  Use the smooth-input formulas and equality of the two original PDO maps.
  Continuous extension gives equality. The square-root isometry would instead
  conjugate P by multiplication and cannot replace the identity comparison here. -/
  apply DFunLike.coe_injective
  apply (denseRange_smoothToL2 μ E).equalizer
    ((B.l2ChangeMeasure μ ν).toContinuousLinearMap.comp P.l2Extension).continuous
    ((P.changeMeasure ν).l2Extension.comp
      (A.l2ChangeMeasure μ ν).toContinuousLinearMap).continuous
  funext u
  change B.l2ChangeMeasure μ ν (P.l2Extension (smoothToL2 μ E u)) =
    (P.changeMeasure ν).l2Extension (A.l2ChangeMeasure μ ν (smoothToL2 μ E u))
  -- Identity density comparisons preserve the section both before and after P acts.
  rw [P.l2Extension_smoothToL2, B.l2ChangeMeasure_smoothToL2 μ ν,
    A.l2ChangeMeasure_smoothToL2 μ ν, (P.changeMeasure ν).l2Extension_smoothToL2]
  rfl

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- An elliptic order-zero PDO is Fredholm in the integral L² model. -/
theorem isFredholm_l2Extension (hP : P.IsElliptic) : P.l2Extension.IsFredholm := by
  /- Its Sobolev extension at order zero is Fredholm by elliptic regularity
  and the two-sided parametrix theorem. The H⁰--L² comparisons conjugate that
  exact extension to l2Extension. Continuous equivalences preserve the kernel,
  range closedness and finite-dimensional cokernel. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let e := A.sobolevZeroEquivL2 μ
  have hfExists : ∃ f : B.SobolevSpace (0 - 0) ≃L[ℂ]
      L2SectionSpace (n := n) (r := q) μ F,
      ∀ v : smoothSections (n := n) (r := q) F,
        f (B.smoothToSobolev (0 - 0) v) = smoothToL2 μ F v := by
    rw [sub_self]
    exact ⟨B.sobolevZeroEquivL2 μ, B.sobolevZeroEquivL2_smoothToSobolev μ⟩
  obtain ⟨f, hf⟩ := hfExists
  let T := P.sobolevExtension A B 0
  have hFred : T.IsFredholm := P.isFredholm_sobolevExtension_of_isElliptic A B hP 0
  -- Density identifies the exact bounded operator with this conjugated critical extension.
  have hconj : P.l2Extension =
      f.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap) := by
    apply DFunLike.coe_injective
    apply (denseRange_smoothToL2 μ E).equalizer P.l2Extension.continuous
      (f.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)).continuous
    funext u
    change P.l2Extension (smoothToL2 μ E u) = f (T (e.symm (smoothToL2 μ E u)))
    rw [P.l2Extension_smoothToL2, ← A.sobolevZeroEquivL2_smoothToSobolev μ u]
    rw [show e.symm (e (A.smoothToSobolev 0 u)) = A.smoothToSobolev 0 u from
      e.symm_apply_apply _, P.sobolevExtension_smoothToSobolev]
    exact (hf (P.toLinearMap u)).symm
  rw [hconj]
  exact f.isFredholm.comp (hFred.comp e.symm.isFredholm)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The order-zero integral L² Fredholm index equals the original smooth index. -/
theorem index_l2Extension (hP : P.IsElliptic) :
    P.l2Extension.toLinearMap.index = P.toLinearMap.index := by
  /- Use the H⁰--L² equivalences to identify the Fredholm kernels and cokernels,
  then apply the original Sobolev/smooth index comparison for elliptic P.
  The smooth operator remains fixed, so the resulting integer has no density choice. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let e := A.sobolevZeroEquivL2 μ
  have hfExists : ∃ f : B.SobolevSpace (0 - 0) ≃L[ℂ]
      L2SectionSpace (n := n) (r := q) μ F,
      ∀ v : smoothSections (n := n) (r := q) F,
        f (B.smoothToSobolev (0 - 0) v) = smoothToL2 μ F v := by
    rw [sub_self]
    exact ⟨B.sobolevZeroEquivL2 μ, B.sobolevZeroEquivL2_smoothToSobolev μ⟩
  obtain ⟨f, hf⟩ := hfExists
  let T := P.sobolevExtension A B 0
  have hFred : T.IsFredholm := P.isFredholm_sobolevExtension_of_isElliptic A B hP 0
  -- Density identifies the exact bounded operator with this conjugated critical extension.
  have hconj : P.l2Extension =
      f.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap) := by
    apply DFunLike.coe_injective
    apply (denseRange_smoothToL2 μ E).equalizer P.l2Extension.continuous
      (f.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)).continuous
    funext u
    change P.l2Extension (smoothToL2 μ E u) = f (T (e.symm (smoothToL2 μ E u)))
    rw [P.l2Extension_smoothToL2, ← A.sobolevZeroEquivL2_smoothToSobolev μ u]
    rw [show e.symm (e (A.smoothToSobolev 0 u)) = A.smoothToSobolev 0 u from
      e.symm_apply_apply _, P.sobolevExtension_smoothToSobolev]
    exact (hf (P.toLinearMap u)).symm
  have he : e.symm.toContinuousLinearMap.index = 0 :=
    LinearMap.index_of_bijective e.symm.bijective
  have hf : f.toContinuousLinearMap.index = 0 := LinearMap.index_of_bijective f.bijective
  have hindex : T.index = P.toLinearMap.index :=
    P.index_sobolevExtension_eq_of_isElliptic A B hP 0
  -- The same two comparison maps have zero index, so index additivity removes them.
  change P.l2Extension.index = P.toLinearMap.index
  rw [hconj, f.isFredholm.index_comp (hFred.comp e.symm.isFredholm),
    hFred.index_comp e.symm.isFredholm, he, hf, zero_add, add_zero, hindex]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
include hν in
/-- The integral L² index is unchanged under an auxiliary positive density change. -/
theorem index_l2Extension_changeMeasure (hP : P.IsElliptic) :
    (P.changeMeasure ν).l2Extension.toLinearMap.index = P.l2Extension.toLinearMap.index := by
  /- The identity density comparisons intertwine these exact bounded operators.
  Restrict the source comparison to their kernels and descend the target comparison
  to their actual cokernels. The resulting linear equivalences preserve both
  finranks in the algebraic index. No Fredholm or parametrix theorem is needed. -/
  have _elliptic := hP
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  let e := A.l2ChangeMeasure μ ν
  let f := B.l2ChangeMeasure μ ν
  let T := P.l2Extension.toLinearMap
  let S := (P.changeMeasure ν).l2Extension.toLinearMap
  have hcomm (x : L2SectionSpace (n := n) (r := r) μ E) : f (T x) = S (e x) :=
    DFunLike.congr_fun (P.l2Extension_changeMeasure ν A B) x
  -- The same intertwining identifies the full kernels, without a dimension assumption.
  have hker : T.ker.map e.toLinearMap = S.ker := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change S (e x) = 0
      rw [← hcomm, show T x = 0 from hx, map_zero]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change T (e.symm y) = 0
      apply f.injective
      rw [hcomm, e.apply_symm_apply, map_zero]
      exact hy
  -- The target comparison maps the actual range onto the actual range.
  have hrange : T.range.map f.toLinearMap = S.range := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, (hcomm x).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨T (e.symm x), ⟨e.symm x, rfl⟩, ?_⟩
      exact (hcomm (e.symm x)).trans (congrArg S (e.apply_symm_apply x))
  let kerEquiv := e.toLinearEquiv.ofSubmodules T.ker S.ker hker
  let cokerEquiv := Submodule.Quotient.equiv T.range S.range f.toLinearEquiv hrange
  change S.index = T.index
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    kerEquiv.finrank_eq, cokerEquiv.finrank_eq]

end PseudodifferentialOperator

end AtiyahSinger
