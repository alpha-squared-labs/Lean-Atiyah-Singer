/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactTestFormalAdjoint
public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Geometry.HermitianPairing

import AtiyahSinger.Analysis.DifferentialParametrix
import AtiyahSinger.Analysis.SmoothAdjointCokernel
import AtiyahSinger.Geometry.HermitianMetricAdjoint

/-!
# Global formal adjoints and the smooth cokernel

Public module ID: M0670.

On compact manifolds without boundary, the formal adjoint acts on global smooth
sections and is characterized by the integral Hermitian pairing. It is constructed
from its existence and uniqueness theorem. It is not an unspecified bounded
Hilbert-space adjoint.

For an elliptic operator, the natural map from the adjoint kernel to the smooth
cokernel is bijective. This identifies the algebraic index with the formula in
Spin Geometry III.5.2–5.3 and pp. 194–195. Sobolev realizations and independence
of Sobolev order are treated separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothHermitianBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothHermitianBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable {E F} (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

set_option linter.overlappingInstances false in
-- Retain the original explicit and inherited smooth-bundle proofs in this predicate.
/-- The defining integral identity for a formal adjoint on a closed manifold. -/
def IsFormalAdjoint (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (Q : DifferentialOperator (n := n) (r := q) (q := r) F E m) : Prop :=
  ∀ (s : smoothSections (n := n) (r := r) E)
    (t : smoothSections (n := n) (r := q) F),
      smoothSectionPairing μ F (P.toLinearMap s) t =
        smoothSectionPairing μ E s (Q.toLinearMap t)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The global formal adjoint exists uniquely as an operator on smooth sections. -/
theorem existsUnique_formalAdjoint
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) :
    ∃! Q : DifferentialOperator (n := n) (r := q) (q := r) F E m,
      P.IsFormalAdjoint μ Q := by
  -- Regard the installed fiber inner products as the same explicit smooth metrics.
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let k := SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F
  obtain ⟨Q, hQ, huniq⟩ := P.existsUnique_compactTestMetricFormalAdjoint (μ := μ) h k
  refine ⟨Q, ?_, ?_⟩
  · intro u v
    exact hQ Set.univ Set.univ isCompact_univ isCompact_univ
      ⟨u, fun x hx ↦ (hx (Set.mem_univ x)).elim⟩
      ⟨v, fun x hx ↦ (hx (Set.mem_univ x)).elim⟩
  · -- Every compact test is one of the original global smooth inputs.
    intro R hR
    apply huniq R
    intro K L _ _ u v
    exact hR u.val v.val

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The formal adjoint selected by its unique integral identity.
Its construction uses the preceding existence and uniqueness theorem. -/
def formalAdjoint (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) :
    DifferentialOperator (n := n) (r := q) (q := r) F E m :=
  Classical.choose (P.existsUnique_formalAdjoint μ).exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The constructed formal adjoint satisfies the integral identity. -/
theorem isFormalAdjoint_formalAdjoint
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) :
    P.IsFormalAdjoint μ (P.formalAdjoint μ) := by
  -- The selected witness retains the exact global pairing identity.
  exact (P.existsUnique_formalAdjoint μ).exists.choose_spec

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Taking the formal adjoint twice returns the original global operator. -/
theorem formalAdjoint_formalAdjoint
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) :
    (P.formalAdjoint μ).formalAdjoint μ = P := by
  -- Conjugation reverses the original pairing and leaves the density unchanged.
  apply ((P.formalAdjoint μ).existsUnique_formalAdjoint μ).unique
    ((P.formalAdjoint μ).isFormalAdjoint_formalAdjoint μ)
  intro v u
  have hpair := congrArg (starRingEnd ℂ) (P.isFormalAdjoint_formalAdjoint μ u v)
  simpa only [smoothSectionPairing, ← integral_conj, inner_conj_symm] using hpair.symm

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- At each real covector the symbol of the formal adjoint is the Hermitian adjoint.
With D_j=-i∂_j there is no extra factor (-1)^m in this identity. -/
theorem principalSymbol_formalAdjoint_inner
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
    (u : E x) (v : F x) :
    inner ℂ (P.principalSymbol x ξ u) v =
      inner ℂ u ((P.formalAdjoint μ).principalSymbol x ξ v) := by
  -- The installed inner products are exactly the two explicit metrics in the compact-test formula.
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let k := SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F
  have hPQ : IsCompactTestMetricFormalAdjoint h k μ P.toLinearMap
      (P.formalAdjoint μ).toLinearMap := by
    intro K L _ _ s t
    exact P.isFormalAdjoint_formalAdjoint μ s.val t.val
  exact IsCompactTestMetricFormalAdjoint.principalSymbol_pairing h k hPQ x ξ u v

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Ellipticity is preserved by taking the global formal adjoint. -/
theorem isElliptic_formalAdjoint_iff
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) :
    (P.formalAdjoint μ).IsElliptic ↔ P.IsElliptic := by
  -- Use the installed fiber forms as explicit metrics, retaining both original norms.
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let k := SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F
  have hbij (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      Function.Bijective ((P.formalAdjoint μ).principalSymbol x ξ) ↔
        Function.Bijective (P.principalSymbol x ξ) := by
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let A : E x →L[ℂ] F x := (P.principalSymbol x ξ).toContinuousLinearMap
    let B : F x →L[ℂ] E x :=
      ((P.formalAdjoint μ).principalSymbol x ξ).toContinuousLinearMap
    have hB : h.adjoint k x A = B := h.adjoint_eq k x A B
      (P.principalSymbol_formalAdjoint_inner μ x ξ)
    have hh := h.bijective_adjoint_iff k x A
    rw [hB] at hh
    exact hh
  -- The equivalence is pointwise, with precisely the original exclusion of the zero covector.
  constructor
  · intro hP x ξ hξ
    exact (hbij x ξ).mp (hP x ξ hξ)
  · intro hP x ξ hξ
    exact (hbij x ξ).mpr (hP x ξ hξ)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Including the adjoint kernel and then taking the smooth quotient is bijective. -/
theorem bijective_ker_formalAdjoint_to_coker
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) (hP : P.IsElliptic) :
    Function.Bijective
      (P.toLinearMap.range.mkQ.comp (P.formalAdjoint μ).toLinearMap.ker.subtype) := by
  -- Use the actual differential parametrix and the original smooth section map.
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let k := SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F
  -- The installed pairings are exactly these explicit metrics; no norm is replaced.
  exact (P.toPseudodifferentialOperator μ).bijective_adjointKer_to_coker_of_isParametrix
    h k A B Q hQ (P.formalAdjoint μ).toLinearMap
    (P.isFormalAdjoint_formalAdjoint μ)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The actual identification of the smooth adjoint kernel with the smooth cokernel. -/
def kerFormalAdjointEquivCoker
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) (hP : P.IsElliptic) :
    (P.formalAdjoint μ).toLinearMap.ker ≃ₗ[ℂ]
      (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) :=
  LinearEquiv.ofBijective
    (P.toLinearMap.range.mkQ.comp (P.formalAdjoint μ).toLinearMap.ker.subtype)
    (P.bijective_ker_formalAdjoint_to_coker μ hP)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The analytic index equals the difference of the two smooth kernel dimensions. -/
theorem analyticIndex_eq_finrank_ker_sub_finrank_ker_formalAdjoint
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m) (hP : P.IsElliptic) :
    P.analyticIndex hP = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ (P.formalAdjoint μ).toLinearMap.ker := by
  -- The same natural quotient equivalence identifies the original cokernel dimension.
  rw [P.analyticIndex_eq_finrank_sub hP,
    ← (P.kerFormalAdjointEquivCoker μ hP).finrank_eq]

end DifferentialOperator

end AtiyahSinger
