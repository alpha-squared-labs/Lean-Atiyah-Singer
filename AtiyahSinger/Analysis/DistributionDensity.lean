/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DistributionEllipticRegularity
public import AtiyahSinger.Analysis.PseudodifferentialDensity
public import AtiyahSinger.Analysis.SmoothSectionMultiplication

import AtiyahSinger.Analysis.FormalAdjointDensity

/-!
# Density conventions for distribution sections

Public module ID: M0439.

D02/D04/A01/A02: when dν=w dμ, the same section distribution is transported by
D ↦ (α ↦ D(w α)). Although the functional carriers are definitionally identical,
the identity function does not preserve their embeddings of nonzero sections.
Sobolev compatibility, local regularity, presentation changes and PDO action are
compared using this actual weighted test map. No topology on distributions is claimed.
Sources: Taylor I.1 (1.7); SG III.3 (3.18), III.5 (5.1)--(5.2).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  (μ ν : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hT2 hSC hC hE hμ hν

namespace SmoothBundlePresentation

variable {E} (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- Density transport is concrete precomposition by multiplication of covector tests by dν/dμ. -/
def distributionChangeMeasure : A.DistributionSection μ →ₗ[ℂ] A.DistributionSection ν where
  toFun D := D.comp (A.dualPresentation.smoothMul
    (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
    (contMDiff_complex_smoothDensityRatio μ ν))
  map_add' D G := by
    ext α
    rfl
  map_smul' c D := by
    ext α
    rfl


set_option linter.unusedSectionVars false in
/-- Evaluation explicitly displays the forward density ratio multiplying the test. -/
theorem distributionChangeMeasure_apply (D : A.DistributionSection μ)
    (α : A.dualPresentation.SmoothSectionSpace) :
    A.distributionChangeMeasure μ ν D α = D (A.dualPresentation.smoothMul
      (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
      (contMDiff_complex_smoothDensityRatio μ ν) α) := by
  /- Unfold the precomposition defining density transport. The test weight
  is dν/dμ, in contrast to the reciprocal input weight used to change an integral
  kernel while preserving its section map. No complex conjugation appears. -/
  rfl

omit hν in
/-- Transport at a fixed density is the identity on its distribution functionals. -/
theorem distributionChangeMeasure_self : A.distributionChangeMeasure μ μ = LinearMap.id := by
  /- The density ratio is one. Pointwise test multiplication is therefore
  identity; evaluating on every test proves equality of the distribution maps. -/
  apply LinearMap.ext
  intro D
  apply ContinuousLinearMap.ext
  intro α
  rw [distributionChangeMeasure_apply]
  change D _ = D α
  congr 1
  apply A.dualPresentation.smoothSectionEquiv.injective
  apply Subtype.ext
  funext x
  change (smoothDensityRatio (n := n) μ μ x : ℂ) •
    (A.dualPresentation.smoothSectionEquiv α).val x = _
  rw [smoothDensityRatio_self]
  simp

/-- Density transport of distributions obeys the cocycle law. -/
theorem distributionChangeMeasure_trans (κ : Measure M)
    [IsSmoothPositiveMeasure (n := n) κ] (D : A.DistributionSection μ) :
    A.distributionChangeMeasure ν κ (A.distributionChangeMeasure μ ν D) =
      A.distributionChangeMeasure μ κ D := by
  /- The nested evaluations multiply each test by (dν/dμ)(dκ/dν).
  The ratio cocycle identifies this pointwise with dκ/dμ. Equality of smooth
  tests gives equality of their evaluations by every continuous functional. -/
  apply ContinuousLinearMap.ext
  intro α
  -- Evaluate both transports on the same test before comparing its pointwise weights.
  rw [distributionChangeMeasure_apply, distributionChangeMeasure_apply,
    distributionChangeMeasure_apply]
  congr 1
  apply A.dualPresentation.smoothSectionEquiv.injective
  apply Subtype.ext
  funext x
  change (smoothDensityRatio (n := n) μ ν x : ℂ) •
      ((smoothDensityRatio (n := n) ν κ x : ℂ) •
        (A.dualPresentation.smoothSectionEquiv α).val x) =
    (smoothDensityRatio (n := n) μ κ x : ℂ) •
      (A.dualPresentation.smoothSectionEquiv α).val x
  rw [smul_smul, smoothDensityRatio_mul (n := n) μ ν κ x, Complex.ofReal_mul]

/-- Reversing the density change recovers the original distribution exactly. -/
theorem distributionChangeMeasure_swap (D : A.DistributionSection μ) :
    A.distributionChangeMeasure ν μ (A.distributionChangeMeasure μ ν D) = D := by
  /- Apply the cocycle law with final density μ and then the identity law.
  The ratio is positive everywhere, so inverse cancellation holds on all tests,
  not only outside a measure-zero exceptional set. -/
  rw [A.distributionChangeMeasure_trans μ ν μ D, A.distributionChangeMeasure_self μ]
  rfl

/-- The actual weighted test maps give the canonical linear density equivalence. -/
def distributionDensityEquiv : A.DistributionSection μ ≃ₗ[ℂ] A.DistributionSection ν where
  toLinearMap := A.distributionChangeMeasure μ ν
  invFun := A.distributionChangeMeasure ν μ
  left_inv := A.distributionChangeMeasure_swap μ ν
  right_inv := A.distributionChangeMeasure_swap ν μ

/-- Density transport sends the distribution of a smooth section to that same section. -/
theorem distributionChangeMeasure_smoothToDistribution
    (u : smoothSections (n := n) (r := r) E) :
    A.distributionChangeMeasure μ ν (A.smoothToDistribution μ u) =
      A.smoothToDistribution ν u := by
  /- On any covector test the left side integrates (dν/dμ) times its evaluation
  on u against μ. The change-of-density formula gives exactly the ν integral.
  Bilinearity of covector evaluation preserves the scalar without conjugation. -/
  apply ContinuousLinearMap.ext
  intro α
  rw [A.distributionChangeMeasure_apply μ ν, A.smoothToDistribution_apply μ,
    A.smoothToDistribution_apply ν]
  change (∫ x, ((smoothDensityRatio (n := n) μ ν x : ℂ) •
      (A.dualPresentation.smoothSectionEquiv α).val x) (u.val x) ∂μ) =
    ∫ x, (A.dualPresentation.smoothSectionEquiv α).val x (u.val x) ∂ν
  rw [integral_smoothDensityRatio (n := n) μ ν]
  rfl

/-- Every real-order Sobolev embedding is compatible with this same density transport. -/
theorem distributionChangeMeasure_sobolevToDistribution (s : ℝ) (u : A.SobolevSpace s) :
    A.distributionChangeMeasure μ ν (A.sobolevToDistribution μ s u) =
      A.sobolevToDistribution ν s u := by
  /- For each fixed smooth test, both sides are continuous linear functionals
  of u in the same density-free Sobolev completion. On the dense smooth image
  the preceding integral calculation identifies them. Extend equality by density,
  then use extensionality over tests. No choice of a representative order is involved. -/
  apply ContinuousLinearMap.ext
  intro α
  let β := A.dualPresentation.smoothMul
    (fun x ↦ (smoothDensityRatio (n := n) μ ν x : ℂ))
    (contMDiff_complex_smoothDensityRatio μ ν) α
  change A.sobolevToDistribution μ s u β = A.sobolevToDistribution ν s u α
  have hleft : Continuous (fun v : A.SobolevSpace s ↦ A.sobolevToDistribution μ s v β) :=
    (A.sobolevEvaluationDuality μ s (A.dualTestToSobolev (-s) β)).continuous
  have hright : Continuous (fun v : A.SobolevSpace s ↦ A.sobolevToDistribution ν s v α) :=
    (A.sobolevEvaluationDuality ν s (A.dualTestToSobolev (-s) α)).continuous
  refine (A.denseRange_smoothToSobolev s).induction_on u (isClosed_eq hleft hright) ?_
  intro v
  rw [A.sobolevToDistribution_smoothToSobolev, A.sobolevToDistribution_smoothToSobolev]
  exact congrArg (fun D : A.DistributionSection ν ↦ D α)
    (A.distributionChangeMeasure_smoothToDistribution μ ν v)

/-- Changing density preserves each local Sobolev regularity condition. -/
theorem memSobolevOn_distributionChangeMeasure_iff (D : A.DistributionSection μ)
    (s : ℝ) (U : Set M) :
    DistributionSection.MemSobolevOn A ν (A.distributionChangeMeasure μ ν D) s U ↔
      DistributionSection.MemSobolevOn A μ D s U := by
  /- Use the same actual Sobolev vector as a witness and transport its embedding
  by the preceding formula. The local predicate on that vector has no density
  parameter. Reversing transport proves the converse for arbitrary subsets U. -/
  constructor
  · rintro ⟨l, u, hu, hlocal⟩
    have h := congrArg (A.distributionChangeMeasure ν μ) hu
    rw [A.distributionChangeMeasure_sobolevToDistribution ν μ,
      A.distributionChangeMeasure_swap μ ν] at h
    exact ⟨l, u, h, hlocal⟩
  · rintro ⟨l, u, hu, hlocal⟩
    refine ⟨l, u, ?_, hlocal⟩
    rw [← A.distributionChangeMeasure_sobolevToDistribution μ ν, hu]

/-- Local smoothness is a property of the represented section, independent of density convention. -/
theorem isSmoothOn_distributionChangeMeasure_iff (D : A.DistributionSection μ) (U : Set M) :
    DistributionSection.IsSmoothOn A ν (A.distributionChangeMeasure μ ν D) U ↔
      DistributionSection.IsSmoothOn A μ D U := by
  /- Keep a Sobolev witness for the distribution and transport its embedding.
  Its original local smoothness is unchanged. Reverse the two measures for the
  other implication, without extending any local representative globally. -/
  constructor
  · rintro ⟨l, u, hu, hlocal⟩
    have h := congrArg (A.distributionChangeMeasure ν μ) hu
    rw [A.distributionChangeMeasure_sobolevToDistribution ν μ,
      A.distributionChangeMeasure_swap μ ν] at h
    exact ⟨l, u, h, hlocal⟩
  · rintro ⟨l, u, hu, hlocal⟩
    refine ⟨l, u, ?_, hlocal⟩
    rw [← A.distributionChangeMeasure_sobolevToDistribution μ ν, hu]

/-- The transported distribution has the identical singular support in the same base. -/
theorem singularSupport_distributionChangeMeasure (D : A.DistributionSection μ) :
    DistributionSection.singularSupport A ν (A.distributionChangeMeasure μ ν D) =
      DistributionSection.singularSupport A μ D := by
  /- At each point, the smoothness comparison identifies every open smooth
  neighborhood. Negating the existence of such a neighborhood gives the same set. -/
  ext x
  change (¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      DistributionSection.IsSmoothOn A ν (A.distributionChangeMeasure μ ν D) U) ↔
    ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ DistributionSection.IsSmoothOn A μ D U
  simp only [A.isSmoothOn_distributionChangeMeasure_iff μ ν]

/-- Changing a finite presentation commutes with changing the density convention. -/
theorem distributionEquiv_distributionChangeMeasure
    (B : SmoothBundlePresentation (n := n) (r := r) E) (D : A.DistributionSection μ) :
    A.distributionEquiv ν B (A.distributionChangeMeasure μ ν D) =
      B.distributionChangeMeasure μ ν (A.distributionEquiv μ B D) := by
  /- Presentation change keeps the underlying covector section, while density
  change multiplies it by the same scalar function on M. These operations commute
  pointwise; evaluation on every B test gives the desired distribution identity. -/
  apply ContinuousLinearMap.ext
  intro α
  -- The presentation identity retains the same covector before and after multiplication.
  rw [distributionEquiv_apply, distributionChangeMeasure_apply,
    distributionChangeMeasure_apply, distributionEquiv_apply]
  congr 1

end SmoothBundlePresentation

variable {q : ℕ} {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hF

namespace PseudodifferentialOperator

variable {E μ} {m : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The genuine distribution action commutes with density transport of both bundles. -/
theorem distributionExtension_changeMeasure (D : A.DistributionSection μ) :
    (P.changeMeasure ν).distributionExtension A B (A.distributionChangeMeasure μ ν D) =
      B.distributionChangeMeasure μ ν (P.distributionExtension A B D) := by
  /- The new-density transpose is reciprocal conjugation of the old transpose.
  On a fixed test its output reciprocal cancels the forward density weight.
  This uses the actual test maps and does not require a Sobolev representative. -/
  apply ContinuousLinearMap.ext
  intro α
  rw [distributionExtension_apply, SmoothBundlePresentation.distributionChangeMeasure_apply,
    SmoothBundlePresentation.distributionChangeMeasure_apply, distributionExtension_apply]
  congr 1
  apply A.dualPresentation.smoothSectionEquiv.injective
  rw [P.formalTranspose_changeMeasure ν]
  apply Subtype.ext
  funext x
  change (smoothDensityRatio (n := n) μ ν x : ℂ) •
      ((smoothDensityRatio (n := n) ν μ x : ℂ) • _) = _
  rw [smul_smul, smoothDensityRatio_swap (n := n) μ ν x, Complex.ofReal_inv,
    mul_inv_cancel₀ (by exact_mod_cast (smoothDensityRatio_pos (n := n) μ ν x).ne'), one_smul]
  rfl

end PseudodifferentialOperator

end AtiyahSinger
