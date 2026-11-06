/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialParametrix
public import AtiyahSinger.Analysis.PseudodifferentialIndex

/-!
# Finite smooth kernels and cokernels of elliptic differential operators

Public module ID: M0433.

A06/A07: compatible auxiliary norms are constructed on the original fibers from
their given continuous frames. An auxiliary positive density and finite
presentations then give a two-sided parametrix for the same smooth section map.
Sobolev Fredholmness and the natural smooth embeddings prove finiteness of its
actual smooth kernel and algebraic range quotient, without adding norms or a
density to the public hypotheses.

Source: SG III.5.2--5.3. The original differential operator, principal symbol,
ellipticity and algebraic index definitions are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]


variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable {E F} {m : ℕ}

/-- The same compatible-norm and parametrix construction proves both finiteness claims. -/
private theorem finiteDimensional_kernel_cokernel [CompactSpace M]
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (hP : P.IsElliptic) :
    FiniteDimensional ℂ P.toLinearMap.ker ∧
      FiniteDimensional ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) := by
  classical
  -- Each original continuous frame gives a fiber norm with exactly the given topology.
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin q)
  let e (x : M) : E x ≃L[ℂ] V := VectorBundle.continuousLinearEquivAt ℂ V E x
  let f (x : M) : F x ≃L[ℂ] W := VectorBundle.continuousLinearEquivAt ℂ W F x
  let nE (x : M) : NormedAddCommGroup (E x) :=
    NormedAddCommGroup.induced (E x) V (e x).toLinearMap (e x).injective
  let nF (x : M) : NormedAddCommGroup (F x) :=
    NormedAddCommGroup.induced (F x) W (f x).toLinearMap (f x).injective
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦
    { (nE x).toMetricSpace.replaceTopology (e x).toHomeomorph.isInducing.eq_induced,
      nE x with }
  let : ∀ x, NormedSpace ℂ (E x) := fun x ↦
    { norm_smul_le a v := by
        change ‖e x (a • v)‖ ≤ ‖a‖ * ‖e x v‖
        rw [map_smul]
        exact norm_smul_le a (e x v) }
  let : ∀ x, NormedAddCommGroup (F x) := fun x ↦
    { (nF x).toMetricSpace.replaceTopology (f x).toHomeomorph.isInducing.eq_induced,
      nF x with }
  let : ∀ x, NormedSpace ℂ (F x) := fun x ↦
    { norm_smul_le a v := by
        change ‖f x (a • v)‖ ≤ ‖a‖ * ‖f x v‖
        rw [map_smul]
        exact norm_smul_le a (f x v) }
  -- The auxiliary smooth density and presentations do not change the section map.
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let : IsSmoothPositiveMeasure (n := n) μ := hμ
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  -- The original smooth kernel and quotient inherit finiteness from their natural embeddings.
  exact ⟨(P.toPseudodifferentialOperator μ).finiteDimensional_ker_of_isParametrix A B Q hQ,
    (P.toPseudodifferentialOperator μ).finiteDimensional_coker_of_isParametrix A B Q hQ⟩

/-- A06: the smooth kernel of a global elliptic differential operator is finite-dimensional. -/
theorem finiteDimensional_ker [CompactSpace M]
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (hP : P.IsElliptic) : FiniteDimensional ℂ P.toLinearMap.ker := by
  /- Use the shared compatible-norm and parametrix construction above. The
  two-sided parametrix makes a Sobolev realization Fredholm at one order. Its
  finite-dimensional kernel receives the natural injective embedding of the
  original smooth kernel, so finiteness transfers to the kernel in this statement. -/
  exact (finiteDimensional_kernel_cokernel P hP).1

/-- A06/A07: the quotient of smooth sections by the smooth image is finite-dimensional. -/
theorem finiteDimensional_coker [CompactSpace M]
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (hP : P.IsElliptic) :
    FiniteDimensional ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) := by
  /- Sobolev Fredholmness gives a finite-dimensional quotient by the actual
  Sobolev range. The natural map from the smooth quotient is injective: a smooth
  right-hand side with a Sobolev preimage has a smooth preimage, using the left
  smoothing residual. Finiteness therefore transfers to the displayed smooth
  algebraic quotient. No formal-adjoint cokernel identification is used here. -/
  exact (finiteDimensional_kernel_cokernel P hP).2

end DifferentialOperator

end AtiyahSinger
