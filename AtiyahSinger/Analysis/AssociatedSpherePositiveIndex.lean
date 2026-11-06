/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereIndexEqualities

/-!
# The positive-dimensional associated-sphere index

Public module ID: M0127.

The intrinsic analytic index is compared with the cutoff, coordinate and kernel
indices, then with the base index whose coefficient class is associated to the
full equivariant sphere index.
-/

@[expose] public noncomputable section

set_option Elab.async false

section PositiveIndex

namespace AtiyahSinger

open Bundle ComplexBundle Filter MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct ComplexConjugate
  SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology sumTopology continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent
  lieGroup_orthogonalGroup t2Space_cotangent locallyCompactSpace_cotangent

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Enr" => EuclideanSpace ℝ (Fin (n + r))
local notation "Sphere" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Sphere
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := Sphere)

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 80000000 in
-- The extended limit accommodates the original positive-dimensional associated product-index
-- assembly.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the original positive-dimensional associated product-index
-- assembly.
/-- The twisted-product index formula for positive base and sphere dimensions. -/
theorem analyticIndex_associatedSphereTwistedProduct_of_pos (hn : 0 < n) (hr : 0 < r)
    (u : CompactSupportKZero BaseCot) (v : EquivariantSupportTripleKZero G SphereCot) :
    associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
      analyticIndexOfComponents μ
        (complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
          (associatedRepresentationKZero S.toIsPrincipalBundle
            (orthogonalSphereAnalyticIndex r v)) u) := by
  calc
    associatedSphereAnalyticIndex S (associatedSphereTwistedProduct S u v) =
        associatedSphereSelectedCutoffIndex S μ hn hr u v :=
      associatedSphere_intrinsicIndex_eq_cutoffIndex S μ hn hr u v
    _ = associatedSphereSelectedCoordinateIndex S μ hn hr u v :=
      associatedSphere_cutoffIndex_eq_coordinateIndex S μ hn hr u v
    _ = associatedSphereSelectedKernelIndex S μ hn hr u v :=
      associatedSphere_coordinateIndex_eq_kernelIndex S μ hn hr u v
    _ = _ := associatedSphere_kernelIndex_eq_coefficientIndex S μ hn hr u v


end AtiyahSinger

end PositiveIndex

