/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Complex connections on the original smooth complex bundles

Public module ID: M1134.

E01: use mathlib's real covariant derivatives on the same complex fibers over
the real base. Restriction of scalars retains the original bundle atlas and
total-space topology. Complex linearity in the section is the additional
standard compatibility condition; the tangent argument remains real linear.
The condition is local and is imposed only on sections differentiable at the
point, as in the native `IsCovariantDerivativeOn` definition. Arbitrary values
on nondifferentiable sections are not part of a mathematical connection.

Smoothness and the real Leibniz rule remain the existing mathlib predicates
`ContMDiffCovariantDerivativeOn` and `IsCovariantDerivativeOn`; globally one
uses `CovariantDerivative` and its native smoothness class. No second bundled
connection type, new section space, or changed bundle atlas is introduced.
These scalar-role adapters implement the usual complex connections used in
SG Chapter II and in the relative construction of III.13.3, pp.245--246.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {M : Type*} (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]

/-- Restrict the existing complex scalar action to real scalars on the same normed fiber.
This is an implementation adapter, not an additional mathematical bundle structure. -/
@[reducible]
def complexBundleRealNormedSpace (x : M) : NormedSpace ℝ (E x) :=
  NormedSpace.restrictScalars ℝ ℂ (E x)

attribute [local instance] complexBundleRealNormedSpace

variable {r : ℕ} [TopologicalSpace M]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- Scalar restriction makes the original complex bundle a real vector bundle in the same atlas. -/
theorem vectorBundle_real_of_complex : VectorBundle ℝ (EuclideanSpace ℂ (Fin r)) E := by
  /- Stage 1: restrict each original complex-linear local fiber chart to real
  scalars. Its underlying function, inverse, base set and continuity remain
  unchanged; in particular this uses the given FiberBundle atlas.
  Stage 2: on every overlap the real transition operator is the scalar
  restriction of the original complex transition operator. Scalar restriction
  is a continuous linear map on the finite-dimensional operator spaces, so
  the original continuous transition function remains continuous. Package
  these certificates without selecting a new total-space topology. -/
  have hlinear (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e] : e.IsLinear ℝ := by
    constructor
    intro x hx
    exact ((e.linearEquivAt ℂ x hx).toLinearMap.restrictScalars ℝ).isLinear
  refine ⟨hlinear, ?_⟩
  intro e e' he he'
  let := hlinear e
  let := hlinear e'
  -- Restriction changes only scalar compatibility, not either transition's value.
  have hcontinuous := (ContinuousLinearMap.restrictScalarsL ℂ
    (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin r)) ℝ ℝ).continuous.comp_continuousOn
      (continuousOn_coordChange (R := ℂ) e e')
  apply hcontinuous.congr
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  exact (e.coordChangeL_apply (R := ℝ) e' hx v).trans
    (e.coordChangeL_apply (R := ℂ) e' hx v).symm

attribute [local instance] vectorBundle_real_of_complex

variable {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The original real-smooth complex transitions give the native real smooth bundle structure. -/
theorem contMDiffVectorBundle_real_of_complex
    [IsSmoothComplexBundle (n := n) (r := r) E] :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℂ (Fin r)) E
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) := by
  /- Stage 1: the preceding certificate views the same complex atlas as a
  real vector bundle. Both versions of every transition have exactly the
  same action on the same model fiber at every point of the overlap.
  Stage 2: compose each original smooth complex operator-valued transition
  with continuous real-linear restriction of scalars. This gives precisely
  the real operator-valued transition required by ContMDiffVectorBundle.
  The argument changes neither the atlas nor the smooth base model. -/
  constructor
  intro e e' he he'
  -- Apply the real continuous linear scalar-restriction map to the original smooth family.
  have hsmooth := (ContinuousLinearMap.restrictScalarsL ℂ
    (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin r)) ℝ ℝ).contMDiff.comp_contMDiffOn
      (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e e')
  apply hsmooth.congr
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  exact (e.coordChangeL_apply (R := ℝ) e' hx v).trans
    (e.coordChangeL_apply (R := ℂ) e' hx v).symm

/-- A real connection is complex linear in differentiable sections at points of the given set.
The native real Leibniz law and smoothness conditions are imposed separately. -/
def IsComplexLinearConnectionOn
    (cov : (∀ x : M, E x) → ∀ x : M,
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] E x)
    (s : Set M := Set.univ) : Prop :=
  ∀ (σ : ∀ x : M, E x) (x : M),
    MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r)))
      (fun y ↦ (⟨y, σ y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) x →
    x ∈ s → ∀ (c : ℂ) (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
      cov (fun y ↦ c • σ y) x v = c • cov σ x v

end AtiyahSinger
