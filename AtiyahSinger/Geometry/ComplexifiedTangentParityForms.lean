/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorParityDegrees
public import AtiyahSinger.Geometry.ComplexifiedTangentExteriorForms

/-!
# The actual complexified tangent parity spaces and finite form fibers

Public module ID: M1139.

Compose the canonical homogeneous decomposition with the degreewise metric
exterior map to obtain the finite even and odd differential form fibers.
The index reordering only replaces equality in ZMod 2 by the equivalent
Even or Odd predicate. These are the pointwise maps used with the specified
native Hodge bundle coordinates; smoothness of the resulting bundle maps and
the Clifford symbol comparison are separate assertions about these same maps.

Source: SG II.5 and Appendix C, the exterior description of differential forms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators DirectSum Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical metric exterior map on the actual even complexified tangent carrier. -/
def complexifiedTangentEvenFormEquiv (g : SmoothTangentMetric (n := n) (M := M)) (x : M) :
    CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) 0 ≃ₗ[ℂ]
      ((p : {p : Fin (n + 1) // Even p.val}) → DifferentialFormFiber (n := n) p.val.val x) := by
  let V := ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x
  have hdim : Module.finrank ℂ V = n := by
    change Module.finrank ℂ (ℂ ⊗[ℝ] EuclideanSpace ℝ (Fin n)) = n
    rw [Module.finrank_baseChange, finrank_euclideanSpace_fin]
  let e : {p : Fin (n + 1) // (p.val : ZMod 2) = 0} ≃
      {p : Fin (n + 1) // Even p.val} :=
    Equiv.subtypeEquivProp (by funext p; exact propext ZMod.natCast_eq_zero_iff_even)
  exact ((exteriorParityDegreesEquiv V n hdim 0).trans
    (LinearEquiv.piCongrRight (fun p ↦ complexifiedTangentExteriorEquiv g p.val.val x))).trans
      (LinearEquiv.piCongrLeft ℂ (fun p : {p : Fin (n + 1) // Even p.val} ↦
        DifferentialFormFiber (n := n) p.val.val x) e)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical metric exterior map on the actual odd complexified tangent carrier. -/
def complexifiedTangentOddFormEquiv (g : SmoothTangentMetric (n := n) (M := M)) (x : M) :
    CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) 1 ≃ₗ[ℂ]
      ((p : {p : Fin (n + 1) // Odd p.val}) → DifferentialFormFiber (n := n) p.val.val x) := by
  let V := ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x
  have hdim : Module.finrank ℂ V = n := by
    change Module.finrank ℂ (ℂ ⊗[ℝ] EuclideanSpace ℝ (Fin n)) = n
    rw [Module.finrank_baseChange, finrank_euclideanSpace_fin]
  let e : {p : Fin (n + 1) // (p.val : ZMod 2) = 1} ≃
      {p : Fin (n + 1) // Odd p.val} :=
    Equiv.subtypeEquivProp (by funext p; exact propext ZMod.natCast_eq_one_iff_odd)
  exact ((exteriorParityDegreesEquiv V n hdim 1).trans
    (LinearEquiv.piCongrRight (fun p ↦ complexifiedTangentExteriorEquiv g p.val.val x))).trans
      (LinearEquiv.piCongrLeft ℂ (fun p : {p : Fin (n + 1) // Odd p.val} ↦
        DifferentialFormFiber (n := n) p.val.val x) e)

/-- The even form coordinates are the original homogeneous projections and metric pairing. -/
theorem complexifiedTangentEvenFormEquiv_apply
    (g : SmoothTangentMetric (n := n) (M := M)) (x : M)
    (a : CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) 0)
    (p : {p : Fin (n + 1) // Even p.val}) :
    complexifiedTangentEvenFormEquiv g x a p = complexifiedTangentExteriorEquiv g p.val.val x
      (DirectSum.decompose (fun k : ℕ ↦
        ⋀[ℂ]^k (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
          a.val p.val.val) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inverse even form coordinates sum the specified inverse metric exterior maps. -/
theorem complexifiedTangentEvenFormEquiv_symm_coe
    (g : SmoothTangentMetric (n := n) (M := M)) (x : M)
    (u : (p : {p : Fin (n + 1) // Even p.val}) →
      DifferentialFormFiber (n := n) p.val.val x) :
    ((complexifiedTangentEvenFormEquiv g x).symm u :
        ExteriorAlgebra ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) =
      ∑ p, ((complexifiedTangentExteriorEquiv g p.val.val x).symm (u p) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) := by
  classical
  let e : {p : Fin (n + 1) // (p.val : ZMod 2) = 0} ≃
      {p : Fin (n + 1) // Even p.val} :=
    Equiv.subtypeEquivProp (by funext p; exact propext ZMod.natCast_eq_zero_iff_even)
  change (∑ p : {p : Fin (n + 1) // (p.val : ZMod 2) = 0},
    ((complexifiedTangentExteriorEquiv g p.val.val x).symm (u (e p)) :
      ExteriorAlgebra ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))) = _
  exact e.sum_comp (fun p ↦ ((complexifiedTangentExteriorEquiv g p.val.val x).symm (u p) :
    ExteriorAlgebra ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)))

/-- The odd form coordinates are the original homogeneous projections and metric pairing. -/
theorem complexifiedTangentOddFormEquiv_apply
    (g : SmoothTangentMetric (n := n) (M := M)) (x : M)
    (a : CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) 1)
    (p : {p : Fin (n + 1) // Odd p.val}) :
    complexifiedTangentOddFormEquiv g x a p = complexifiedTangentExteriorEquiv g p.val.val x
      (DirectSum.decompose (fun k : ℕ ↦
        ⋀[ℂ]^k (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
          a.val p.val.val) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inverse odd form coordinates sum the specified inverse metric exterior maps. -/
theorem complexifiedTangentOddFormEquiv_symm_coe
    (g : SmoothTangentMetric (n := n) (M := M)) (x : M)
    (u : (p : {p : Fin (n + 1) // Odd p.val}) →
      DifferentialFormFiber (n := n) p.val.val x) :
    ((complexifiedTangentOddFormEquiv g x).symm u :
        ExteriorAlgebra ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) =
      ∑ p, ((complexifiedTangentExteriorEquiv g p.val.val x).symm (u p) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) := by
  classical
  let e : {p : Fin (n + 1) // (p.val : ZMod 2) = 1} ≃
      {p : Fin (n + 1) // Odd p.val} :=
    Equiv.subtypeEquivProp (by funext p; exact propext ZMod.natCast_eq_one_iff_odd)
  change (∑ p : {p : Fin (n + 1) // (p.val : ZMod 2) = 1},
    ((complexifiedTangentExteriorEquiv g p.val.val x).symm (u (e p)) :
      ExteriorAlgebra ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))) = _
  exact e.sum_comp (fun p ↦ ((complexifiedTangentExteriorEquiv g p.val.val x).symm (u p) :
    ExteriorAlgebra ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)))

end AtiyahSinger
