/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasUnitaryConnection
public import AtiyahSinger.Geometry.SmoothSpinCliffordSymbol
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# The original local formula for the induced half-spin connection

Public module ID: M1463.

In each of the same compatible spin charts, the lifted orthonormal frame
is e_a and the connection form is one quarter of the sum
< nabla_X e_a, e_b > c(e_a)c(e_b). Here nabla is mathlib's actual
Levi-Civita connection for the supplied original tangent metric. The
ordering of the two frame indices fixes the sign of this formula.

The derivative is specified on the original associated half-spin sections.
Its model coordinates use the original exterior basis and the same inverse
principal chart. Comparing in the full exterior coordinates avoids any
new identification of the two parity spaces. The coefficients away from
valid chart domains have no geometric meaning; uniqueness is therefore
not claimed for the entire AtlasComplexConnection record.

Sources: Spin Geometry II.4, the spin lift of a metric connection, and
II.4 Proposition 4.11, Clifford compatibility of the spin connection. Smoothness follows
from the Koszul coefficients of the specified smooth tangent metric;
no smoothness of a separately chosen tangent connection is assumed.
This file specifies the local formula; existence, metric preservation and
Clifford compatibility are proved separately on these same objects.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

set_option maxSynthPendingDepth 50

variable {m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m}
  {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => (TangentSpace I : M → Type _)
local notation "TModel" => EuclideanSpace ℝ (Fin (2 * m))

namespace TopologicalSpinStructure

open Classical in
/-- The standard spin-connection formula in the same lifted frames and exterior coordinates. -/
def IsInducedHalfSpinorConnection :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  (S : TopologicalSpinStructure m TM o hm hP) → (i : ZMod 2) →
    AtlasComplexConnection (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i) →
      Prop :=
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  fun S i cov ↦
    let A := S.smoothPrincipalAtlas I
    let H := halfSpinorBundleSmoothAtlas m hP A i
    let c := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra.equivFun
    ∀ (b x : M) (hx : x ∈ (A.trivialization b).baseSet) (u : H.smoothSections)
      (X : TangentSpace I x),
      let t := A.trivialization b
      let p := t.toPartialEquiv.symm (x, 1)
      let hp : projection p = x := t.proj_symm_apply' hx
      let coordinates : M → (Finset (Fin m) → ℂ) := fun y ↦
        if hy : y ∈ t.baseSet then
          c (((associatedVectorFiberMkLinearEquiv hP
            (complexSpinParityContRepresentation m i)
            (t.toPartialEquiv.symm (y, 1)) (t.proj_symm_apply' hy)).symm (u.val y)).val)
        else 0
      let frame : Fin (2 * m) → ∀ y : M, TangentSpace I y := fun a y ↦
        if hy : y ∈ t.baseSet then
          S.frame (t.toPartialEquiv.symm (y, 1)) y (t.proj_symm_apply' hy)
            (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a)
        else 0
      c (((associatedVectorFiberMkLinearEquiv hP
        (complexSpinParityContRepresentation m i) p hp).symm
          (cov.covariantDerivative u x X)).val) =
        NormedSpace.fromTangentSpace (𝕜 := ℝ) (coordinates x)
          (mfderiv I 𝓘(ℝ, Finset (Fin m) → ℂ) coordinates x X) +
          c ((1 / 4 : ℂ) • ∑ a : Fin (2 * m), ∑ b : Fin (2 * m),
            (g.inner x (CovariantDerivative.leviCivitaConnection I M (frame a) x X)
              (frame b x) : ℂ) •
                cliffordSymbol
                  (realSpinorCoordinateIsometry m (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a))
                  (cliffordSymbol
                    (realSpinorCoordinateIsometry m (EuclideanSpace.basisFun (Fin (2 * m)) ℝ b))
                    (c.symm (coordinates x))))

end TopologicalSpinStructure

end AtiyahSinger
