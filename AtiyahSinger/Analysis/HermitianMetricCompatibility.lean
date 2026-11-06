/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.L2Density
public import AtiyahSinger.Analysis.PseudodifferentialSobolevAdjoint

/-!
# Compatibility of explicit metrics with the installed inner products

Public module ID: M0720.

D02/A07: specialize the supplied smooth Hermitian metrics to the installed
fiber inner products. The symbol adjoints, smooth and Sobolev dualities,
formal adjoints and L² realizations agree with the corresponding operations
for those inner products. These are compatibility deductions from their defining
characterizations and the canonical completion comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hHE : IsSmoothHermitianBundle (n := n) (r := r) E]
  [hHF : IsSmoothHermitianBundle (n := n) (r := q) F]

include hM hHE hHF


set_option linter.unusedSectionVars false in
/-- Explicit fiber-symbol adjunction specializes to the original installed-metric operation. -/
theorem symbolAdjoint_ofInnerProduct (p : GlobalSymbolFunction (n := n) E F) :
    (SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E).symbolAdjoint
      (SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F) p =
        globalSymbolAdjoint (r := r) (q := q) p := by
  /- At each fiber the explicit adjunction pairing is the installed
  inner product. The ordinary continuous Hilbert adjoint satisfies precisely
  that identity, so finite-dimensional uniqueness identifies the symbol maps. -/
  funext x ξ
  apply (SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E).adjoint_eq
    (SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F) x
  intro u v
  simpa only [SmoothHermitianMetric.pairing_ofInnerProduct] using
    globalSymbolAdjoint_inner (r := r) (q := q) p x ξ u v

/-- The principal quotient operations agree for the installed metrics. -/
theorem principalSymbolAdjoint_ofInnerProduct {m : ℝ}
    (p : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E).principalSymbolAdjoint
      (SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F) p =
        globalPrincipalSymbolAdjoint p := by
  /- Choose a representative and evaluate both quotient lifts. The
  previous actual symbol equality identifies the resulting representatives;
  projecting and using quotient surjectivity gives equality for every class. -/
  refine Quotient.inductionOn p ?_
  intro a
  change globalPrincipalSymbolClass F E m
      ((SmoothHermitianMetric.ofInnerProduct E).symbolSpaceAdjoint
        (SmoothHermitianMetric.ofInnerProduct F) a) =
    globalPrincipalSymbolClass F E m (globalSymbolSpaceAdjoint a)
  apply congrArg (globalPrincipalSymbolClass F E m)
  apply Subtype.ext
  exact symbolAdjoint_ofInnerProduct a.val

variable [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hT2 hSC hE hF

set_option linter.overlappingInstances false in
-- Keep the original explicit and inherited smooth-bundle proofs in this omitted context.
omit hHF hF in
/-- Specializing the explicit metric recovers the original smooth metric dual. -/
theorem dualSectionsEquiv_ofInnerProduct :
    (SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E).dualSectionsEquiv =
      smoothHermitianDualEquiv (n := n) (r := r) E := by
  /- Evaluate both maps on a smooth section, a base point, and a fiber
  test vector. Both yield the same installed Hermitian inner product. Covector,
  section and semilinear-map extensionality identify the actual equivalences. -/
  apply LinearEquiv.ext
  intro u
  apply Subtype.ext
  funext x
  apply ContinuousLinearMap.ext
  intro v
  rw [SmoothHermitianMetric.dualSectionsEquiv_apply, smoothHermitianDualEquiv_apply,
    SmoothHermitianMetric.pairing_ofInnerProduct]

set_option linter.overlappingInstances false in
-- Keep the original explicit and inherited smooth-bundle proofs in this omitted context.
omit hHF hF in
/-- The explicit Sobolev metric map agrees with the installed conjugate-linear equivalence. -/
theorem sobolevDual_ofInnerProduct (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ) :
    (SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E).sobolevDual A s =
      A.sobolevHermitianDual s := by
  /- Both continuous semilinear equivalences send each smooth vector
  to its original smooth metric dual in the same completion. Use the smooth
  compatibility and density to identify the equivalences, with no density measure. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    ((SmoothHermitianMetric.ofInnerProduct E).sobolevDual A s).continuous
    (A.sobolevHermitianDual s).continuous
  funext u
  simp only [Function.comp_apply]
  rw [SmoothHermitianMetric.sobolevDual_smooth, A.sobolevHermitianDual_smooth,
    dualSectionsEquiv_ofInnerProduct]

variable [hC : CompactSpace M] [MeasurableSpace M] [hBorel : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hC hBorel hμ

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The differential construction specializes to the original same-density formal adjoint. -/
theorem DifferentialOperator.metricFormalAdjoint_ofInnerProduct {d : ℕ}
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F d) :
    P.metricFormalAdjoint (μ := μ) (SmoothHermitianMetric.ofInnerProduct E)
      (SmoothHermitianMetric.ofInnerProduct F) = P.formalAdjoint μ := by
  -- The same installed forms identify the two integral characterizations pointwise.
  apply P.metricFormalAdjoint_eq
  intro u v
  simpa only [sectionPairing_ofInnerProduct] using
    P.isFormalAdjoint_formalAdjoint μ u v

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The real-order PDO construction specializes to the original Hermitian formal adjoint. -/
theorem PseudodifferentialOperator.metricFormalAdjoint_ofInnerProduct {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) :
    P.metricFormalAdjoint (SmoothHermitianMetric.ofInnerProduct E)
      (SmoothHermitianMetric.ofInnerProduct F) = P.formalAdjoint := by
  -- The installed metrics reproduce the native integral relation with the identical density.
  apply P.metricFormalAdjoint_eq
  intro u v
  simpa only [sectionPairing_ofInnerProduct] using P.isFormalAdjoint_formalAdjoint u v

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The original L² realization is recovered through the canonical completion isometries. -/
theorem PseudodifferentialOperator.metricL2Extension_ofInnerProduct
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0) :
    (l2OfInnerProductEquiv μ F).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (P.metricL2Extension (SmoothHermitianMetric.ofInnerProduct E)
          (SmoothHermitianMetric.ofInnerProduct F)) =
      P.l2Extension.comp
        (l2OfInnerProductEquiv μ E).toContinuousLinearEquiv.toContinuousLinearMap := by
  /- On the dense explicit smooth inputs both sides return the old L²
  embedding of the exact section Pu. The two canonical comparison isometries
  preserve smooth sections. Continuity extends this equality to the whole
  source completion, retaining the actual previously constructed realization. -/
  apply DFunLike.coe_injective
  apply ((SmoothHermitianMetric.ofInnerProduct E).denseRange_smoothToL2 μ).equalizer
    ((l2OfInnerProductEquiv μ F).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (P.metricL2Extension (SmoothHermitianMetric.ofInnerProduct E)
        (SmoothHermitianMetric.ofInnerProduct F))).continuous
    (P.l2Extension.comp
      (l2OfInnerProductEquiv μ E).toContinuousLinearEquiv.toContinuousLinearMap).continuous
  funext u
  change l2OfInnerProductEquiv μ F
      (P.metricL2Extension (SmoothHermitianMetric.ofInnerProduct E)
        (SmoothHermitianMetric.ofInnerProduct F)
        ((SmoothHermitianMetric.ofInnerProduct E).smoothToL2 μ u)) =
    P.l2Extension (l2OfInnerProductEquiv μ E
      ((SmoothHermitianMetric.ofInnerProduct E).smoothToL2 μ u))
  rw [P.metricL2Extension_smooth, l2OfInnerProductEquiv_smoothToL2,
    l2OfInnerProductEquiv_smoothToL2, P.l2Extension_smoothToL2]

end AtiyahSinger
