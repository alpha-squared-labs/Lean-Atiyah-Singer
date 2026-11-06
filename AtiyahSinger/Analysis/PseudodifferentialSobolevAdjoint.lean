/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialAdjoint

/-!
# Opposite-order Sobolev realizations of geometric PDO adjoints

Public module ID: M0900.

D02/A07: the Hermitian form of SG III.(5.1) for arbitrary real-order PDOs.
The map is the existing Sobolev extension of the actual geometric adjoint,
transported across an equality of target orders. Bilinear transposition and
conjugate-linear metric duality supply its continuous-dual interpretation.
Ellipticity and closed range are not assumptions of this module.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hHE : IsSmoothHermitianBundle (n := n) (r := r) E]
  [hHF : IsSmoothHermitianBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

include hM hT2 hSC hC hBorel hE hF hHE hHF hμ

variable (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Extend the geometric adjoint and normalize its target to the opposite input order. -/
def sobolevFormalAdjoint (s : ℝ) :
    B.SobolevSpace (-(s - m)) →L[ℂ] A.SobolevSpace (-s) := by
  have h : -(s - m) - m = -s := by ring
  exact h ▸ P.formalAdjoint.sobolevExtension B A (-(s - m))

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The opposite-order adjoint realization acts on smooth sections by the geometric adjoint. -/
theorem sobolevFormalAdjoint_smooth (s : ℝ)
    (v : smoothSections (n := n) (r := q) F) :
    P.sobolevFormalAdjoint A B s (B.smoothToSobolev (-(s - m)) v) =
      A.smoothToSobolev (-s) (P.formalAdjoint.toLinearMap v) := by
  /- Apply the smooth-input identity for the PDO extension of P†. Transport
  across the real-order equality -(s-m)-m=-s in the definition of this map. -/
  have htransport (t : ℝ) (ht : -(s - m) - m = t) :
      (ht ▸ P.formalAdjoint.sobolevExtension B A (-(s - m)))
          (B.smoothToSobolev (-(s - m)) v) =
        A.smoothToSobolev t (P.formalAdjoint.toLinearMap v) := by
    subst t
    exact P.formalAdjoint.sobolevExtension_smoothToSobolev B A (-(s - m)) v
  exact htransport (-s) (by ring)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The opposite-order Hermitian realization agrees with the bilinear transpose via the metrics. -/
theorem sobolevTranspose_hermitian (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    P.sobolevTranspose A B s (B.sobolevHermitianDual (-(s - m)) v) =
      A.sobolevHermitianDual (-s) (P.sobolevFormalAdjoint A B s v) := by
  /- All maps preserve the original dense smooth inputs. Their continuity extends
  the native metric intertwining identity to the two specified completions. -/
  refine (B.denseRange_smoothToSobolev (-(s - m))).induction_on v
    (isClosed_eq ((P.sobolevTranspose A B s).continuous.comp
      (B.sobolevHermitianDual (-(s - m))).continuous)
      ((A.sobolevHermitianDual (-s)).continuous.comp
        (P.sobolevFormalAdjoint A B s).continuous)) ?_
  intro w
  rw [B.sobolevHermitianDual_smooth, P.sobolevTranspose_smooth,
    P.sobolevFormalAdjoint_smooth, A.sobolevHermitianDual_smooth]
  rw [P.formalTranspose_hermitian, LinearEquiv.symm_apply_apply]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- SG (5.1) after Hermitian identification, with the actual continuous dual and orders. -/
theorem sobolevDuality_formalAdjoint (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    A.sobolevDuality μ s (P.sobolevFormalAdjoint A B s v) =
      (B.sobolevDuality μ (s - m) v).comp (P.sobolevExtension A B s) := by
  /- Insert the same native metric maps into the proven evaluation diagram.
  Its output is the original geometric adjoint, with the displayed opposite orders. -/
  apply ContinuousLinearMap.ext
  intro u
  change A.sobolevPairing μ s (P.sobolevFormalAdjoint A B s v) u =
    B.sobolevPairing μ (s - m) v (P.sobolevExtension A B s u)
  rw [← A.sobolevEvaluationPairing_hermitian μ s,
    ← B.sobolevEvaluationPairing_hermitian μ (s - m)]
  change A.sobolevEvaluationDuality μ s
    (A.sobolevHermitianDual (-s) (P.sobolevFormalAdjoint A B s v)) u = _
  rw [← P.sobolevTranspose_hermitian]
  exact congrArg (fun f : StrongDual ℂ (A.SobolevSpace s) ↦ f u)
    (P.sobolevEvaluationDuality_transpose A B s
      (B.sobolevHermitianDual (-(s - m)) v))

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The weak geometric adjoint kernel is precisely the annihilator of the Sobolev range. -/
theorem sobolevFormalAdjoint_eq_zero_iff (s : ℝ) (v : B.SobolevSpace (-(s - m))) :
    P.sobolevFormalAdjoint A B s v = 0 ↔
      ∀ u : A.SobolevSpace s,
        B.sobolevPairing μ (s - m) v (P.sobolevExtension A B s u) = 0 := by
  /- The native perfect pairing is injective. The precomposition diagram turns
  zero adjoint output into vanishing on the actual Sobolev range, and conversely. -/
  constructor
  · intro h u
    change ((B.sobolevDuality μ (s - m) v).comp (P.sobolevExtension A B s)) u = 0
    rw [← P.sobolevDuality_formalAdjoint A B s v, h, map_zero]
    rfl
  · intro h
    apply (A.sobolevDuality μ s).injective
    rw [P.sobolevDuality_formalAdjoint, map_zero]
    apply ContinuousLinearMap.ext
    exact h

end PseudodifferentialOperator

end AtiyahSinger
