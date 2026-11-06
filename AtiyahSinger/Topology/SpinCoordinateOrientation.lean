/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinCoordinates
public import AtiyahSinger.Geometry.SpinFrame
public import AtiyahSinger.Topology.ComplexBundleRealOrientation

/-!
# The fixed spin coordinates and the canonical complex orientation

Public module ID: M2167.

The original spin coordinate isometry sends the standard real basis to the
actual interleaved realification of the standard complex basis. This fixes the
orientation needed to compare the spin Thom symbol with the complex Thom symbol.
The comparison uses the original coordinate map, with no determinant sign chosen.

Source: the interleaved basis convention in SG I.5 and the canonical complex
orientation in Milnor--Stasheff, Section 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The original spin coordinates retain the canonical interleaved complex frame. -/
theorem realSpinorCoordinateIsometry_basis (m : ℕ) :
    (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.map
        (realSpinorCoordinateIsometry m).toLinearEquiv =
      complexBasisRealification (EuclideanSpace.basisFun (Fin m) ℂ).toBasis := by
  classical
  apply DFunLike.ext
  intro i
  simp only [Module.Basis.map_apply, realSpinorCoordinateIsometry,
    OrthonormalBasis.coe_toBasis, LinearIsometryEquiv.coe_toLinearEquiv,
    EuclideanSpace.basisFun_apply, OrthonormalBasis.repr_symm_single,
    OrthonormalBasis.reindex_apply, Pi.orthonormalBasis_apply,
    complexBasisRealification, Module.Basis.reindex_apply, Module.Basis.smulTower'_apply]
  ext j
  simp [Complex.orthonormalBasisOneI, Complex.basisOneI]

open Bundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

variable {m : ℕ} {B P : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

/-- The original spin frame sends the canonical complex orientation to the given orientation. -/
theorem TopologicalSpinStructure.frame_complexOrientation
    (S : TopologicalSpinStructure m E o hm hP) (p : P) (b : B) (hp : projection p = b) :
    Orientation.map (Fin (2 * m))
        ((realSpinorCoordinateIsometry m).symm.trans (S.frame p b hp)).toLinearEquiv
        (complexBasisRealification (EuclideanSpace.basisFun (Fin m) ℂ).toBasis).orientation =
      o b := by
  have hframe : ((EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.map
      (S.frame p b hp).toLinearEquiv).orientation = o b := by
    cases (S.frameMap_projection p).trans hp
    change ((EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.map
      (S.frameMap p).val.2.toLinearEquiv).orientation = _
    exact ((EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.orientation_map
      (S.frameMap p).val.2.toLinearEquiv).trans (S.frameMap p).property
  rw [← realSpinorCoordinateIsometry_basis, ← Module.Basis.orientation_map]
  convert hframe using 2
  apply DFunLike.ext
  intro i
  simp only [Module.Basis.map_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]

end AtiyahSinger
