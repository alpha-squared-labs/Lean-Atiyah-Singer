/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ComplexCovectorExteriorEquiv
public import AtiyahSinger.Algebra.FiniteAlternatingContinuity
public import AtiyahSinger.Geometry.ComplexifiedTangentCovectors
public import AtiyahSinger.Geometry.DifferentialForms

/-!
# The metric exterior identification with the original differential form fibers

Public module ID: M1136.

The exterior power of the original complexified tangent fiber is identified with
the original complex-valued continuous alternating form fiber. This is the exterior
power of the specified musical map followed by the determinant pairing. The
forward evaluation has no coordinate choice and no factorial factor.

Source: Lawson--Michelsohn, Spin Geometry, II.5, metric exterior realization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Module
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical metric exterior map to the actual continuous differential form fiber. -/
def complexifiedTangentExteriorEquiv (g : SmoothTangentMetric (n := n) (M := M))
    (p : ℕ) (x : M) :
    (⋀[ℂ]^p (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) ≃ₗ[ℂ]
      DifferentialFormFiber (n := n) p x := by
  let V := EuclideanSpace ℝ (Fin n)
  let e : (ℂ ⊗[ℝ] V) ≃ₗ[ℂ] (V →ₗ[ℝ] ℂ) := complexifiedTangentCovectorEquiv g x
  let f : (⋀[ℂ]^p (ℂ ⊗[ℝ] V)) ≃ₗ[ℂ] (⋀[ℂ]^p (V →ₗ[ℝ] ℂ)) :=
    LinearEquiv.ofBijective (exteriorPower.map p e.toLinearMap)
      ⟨exteriorPower.map_injective_field e.injective, exteriorPower.map_surjective e.surjective⟩
  exact (f.trans (complexCovectorExteriorEquiv p)).trans (realAlternatingContinuousEquiv p)

set_option backward.isDefEq.respectTransparency false in
/-- The metric exterior identification is the determinant pairing on the same ordered tensors. -/
theorem complexifiedTangentExteriorEquiv_ιMulti
    (g : SmoothTangentMetric (n := n) (M := M)) (p : ℕ) (x : M)
    (a : Fin p → ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
    (w : Fin p → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    complexifiedTangentExteriorEquiv g p x (exteriorPower.ιMulti ℂ p a) w =
      Matrix.det (Matrix.of (fun i j ↦ complexifiedTangentCovectorMap g x (a i) (w j))) := by
  change complexCovectorExteriorMap p
    (exteriorPower.map p (complexifiedTangentCovectorMap g x)
      (exteriorPower.ιMulti ℂ p a)) w = _
  rw [exteriorPower.map_apply_ιMulti]
  exact complexCovectorExteriorMap_ιMulti p _ w

end AtiyahSinger
