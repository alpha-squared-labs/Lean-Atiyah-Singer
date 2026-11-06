/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DualSobolevBridge
public import AtiyahSinger.Analysis.SmoothSectionTopology

/-!
# Distribution sections on a compact base

Public module ID: M0443.

D04/A01/A06: the continuous dual of smooth covector tests, with the actual smooth
seminorm topology. A positive smooth density identifies these functionals with
E-valued distributions; without that identification they are naturally dual to
covectors, hence density-valued. The measure parameter labels this identification.
No Hermitian metric or conjugation is involved. Since the base is compact, all
smooth tests have compact support. No topology on the distribution space is asserted.
Sources: Taylor I.1 Definitions 1.1--1.3 and (1.7); SG III.2.15(2).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- The actual inclusion of smooth dual tests in their independent Sobolev completion. -/
def dualTestToSobolev (s : ℝ) :
    A.dualPresentation.SmoothSectionSpace →L[ℂ] A.DualSobolevSpace s :=
  (A.dualSobolevEquiv s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.dualPresentation.smoothSectionToSobolev s)

/-- The dual-test inclusion agrees with the earlier embedding of the same covector section. -/
theorem dualTestToSobolev_apply (s : ℝ) (α : A.dualPresentation.SmoothSectionSpace) :
    A.dualTestToSobolev s α = A.dualSmoothToSobolev s
      ((dualSectionsEquiv E).symm (A.dualPresentation.smoothSectionEquiv α)) := by
  /- Apply the smooth-input specification of dualSobolevEquiv and its inverse.
  Both sides localize the same actual covector, using the identical charts and cutoffs. -/
  apply (A.dualSobolevEquiv s).injective
  change A.dualSobolevEquiv s ((A.dualSobolevEquiv s).symm
      (A.dualPresentation.smoothToSobolev s (A.dualPresentation.smoothSectionEquiv α))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, A.dualSobolevEquiv_smooth]
  rfl

variable [MeasurableSpace M] (μ : Measure M)

/-- Distributions relative to μ, acting complex-linearly on actual smooth covector tests. -/
abbrev DistributionSection (_μ : Measure M) : Type _ :=
  A.dualPresentation.SmoothSectionSpace →L[ℂ] ℂ

variable [BorelSpace M] [hC : CompactSpace M]
  [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hE hC hμ

/-- A Sobolev section acts on smooth dual tests by the existing opposite-order bilinear pairing. -/
def sobolevToDistribution (s : ℝ) :
    A.SobolevSpace s →ₗ[ℂ] A.DistributionSection μ where
  toFun u := ((A.sobolevEvaluationDuality μ s).toContinuousLinearMap.flip u).comp
    (A.dualTestToSobolev (-s))
  map_add' u v := by
    ext α
    exact map_add (A.sobolevEvaluationDuality μ s (A.dualTestToSobolev (-s) α)) u v
  map_smul' c u := by
    ext α
    exact map_smul (A.sobolevEvaluationDuality μ s (A.dualTestToSobolev (-s) α)) c u

/-- The distribution embedding evaluates by the actual completed geometric pairing. -/
theorem sobolevToDistribution_apply (s : ℝ) (u : A.SobolevSpace s)
    (α : A.dualPresentation.SmoothSectionSpace) :
    A.sobolevToDistribution μ s u α =
      A.sobolevEvaluationPairing μ s (A.dualTestToSobolev (-s) α) u := by
  /- Unfold the flip and precomposition in the definition. The dual test has
  order -s and evaluates on the original order-s vector; no conjugation appears. -/
  rfl

/-- Smooth tests distinguish different vectors in each Sobolev completion. -/
theorem sobolevToDistribution_injective (s : ℝ) :
    Function.Injective (A.sobolevToDistribution μ s) := by
  /- Equal functionals agree on all smooth dual tests. Density of those tests
  in the opposite-order dual completion extends equality to every dual vector.
  The perfect Sobolev pairing then separates the original primal vectors. -/
  intro u v huv
  -- Extend equality on smooth covector tests to the full opposite-order dual space.
  have heq := (A.denseRange_dualSmoothToSobolev (-s)).equalizer
    ((A.sobolevEvaluationDuality μ s).toContinuousLinearMap.flip u).continuous
    ((A.sobolevEvaluationDuality μ s).toContinuousLinearMap.flip v).continuous (by
      funext α
      let β : A.dualPresentation.SmoothSectionSpace :=
        A.dualPresentation.smoothSectionEquiv.symm (dualSectionsEquiv E α)
      have h := congrArg (fun D : A.DistributionSection μ ↦ D β) huv
      simp only [A.sobolevToDistribution_apply, A.dualTestToSobolev_apply,
        β, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h
      exact h)
  -- Perfect evaluation supplies every continuous functional, hence separates u and v.
  apply ext_inner_left ℂ
  intro w
  obtain ⟨α, hα⟩ := (A.sobolevEvaluationDuality μ s).surjective
    (InnerProductSpace.toDual ℂ (A.SobolevSpace s) w)
  have h := congrFun heq α
  change A.sobolevEvaluationDuality μ s α u = A.sobolevEvaluationDuality μ s α v at h
  rw [hα] at h
  exact h

/-- The distribution of an actual smooth section, using its order-zero realization. -/
def smoothToDistribution :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] A.DistributionSection μ :=
  (A.sobolevToDistribution μ 0).comp (A.smoothToSobolev 0)

/-- On smooth sections, the distribution is the same-point evaluation integral against μ. -/
theorem smoothToDistribution_apply (u : smoothSections (n := n) (r := r) E)
    (α : A.dualPresentation.SmoothSectionSpace) :
    A.smoothToDistribution μ u α = smoothDualSectionPairing E μ
      ((dualSectionsEquiv E).symm (A.dualPresentation.smoothSectionEquiv α)) u := by
  /- Use the dual-test embedding formula, then the smooth-input formula for
  the completed pairing at order zero. The positive density supplies integration;
  covector evaluation is bilinear and does not use a Hermitian identification. -/
  change A.sobolevToDistribution μ 0 (A.smoothToSobolev 0 u) α = _
  rw [A.sobolevToDistribution_apply, A.dualTestToSobolev_apply]
  exact A.sobolevEvaluationPairing_smooth μ 0 _ u

/-- Every Sobolev realization of a smooth section gives the same distribution. -/
theorem sobolevToDistribution_smoothToSobolev (s : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    A.sobolevToDistribution μ s (A.smoothToSobolev s u) = A.smoothToDistribution μ u := by
  /- Test against an arbitrary smooth covector. At either Sobolev order the
  smooth pairing formula gives the identical same-point integral. Extensionality
  of continuous linear functionals yields the asserted equality. -/
  apply ContinuousLinearMap.ext
  intro α
  rw [A.sobolevToDistribution_apply, A.dualTestToSobolev_apply,
    A.sobolevEvaluationPairing_smooth, A.smoothToDistribution_apply]

/-- Natural order-decreasing inclusion preserves the represented distribution. -/
theorem sobolevToDistribution_sobolevInclusion (s t : ℝ) (hts : t ≤ s)
    (u : A.SobolevSpace s) :
    A.sobolevToDistribution μ t (A.sobolevInclusion s t hts u) =
      A.sobolevToDistribution μ s u := by
  /- For a fixed smooth test, both sides are continuous functionals of the
  original order-s vector. They agree on dense smooth inputs by the preceding
  integral formula and the smooth-input inclusion identity; pass to the limit. -/
  apply ContinuousLinearMap.ext
  intro α
  -- With the test fixed, continuity and the dense smooth image compare the two scalar maps.
  have heq := (A.denseRange_smoothToSobolev s).equalizer
    ((A.sobolevEvaluationDuality μ t (A.dualTestToSobolev (-t) α)).continuous.comp
      (A.sobolevInclusion s t hts).continuous)
    (A.sobolevEvaluationDuality μ s (A.dualTestToSobolev (-s) α)).continuous (by
      funext w
      simp only [Function.comp_apply]
      change A.sobolevToDistribution μ t
        (A.sobolevInclusion s t hts (A.smoothToSobolev s w)) α =
          A.sobolevToDistribution μ s (A.smoothToSobolev s w) α
      rw [A.sobolevInclusion_smoothToSobolev,
        A.sobolevToDistribution_smoothToSobolev, A.sobolevToDistribution_smoothToSobolev])
  exact congrFun heq u

end SmoothBundlePresentation

end AtiyahSinger
