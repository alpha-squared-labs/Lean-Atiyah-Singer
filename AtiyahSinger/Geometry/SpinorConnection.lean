/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasUnitaryConnection
public import AtiyahSinger.Geometry.InducedSpinorUnitary
public import AtiyahSinger.Geometry.SmoothSpinCliffordSymbol
public import AtiyahSinger.Geometry.SpinAssociatedConnection
public import AtiyahSinger.Geometry.SpinorConnectionFormula
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# The Levi-Civita induced connection on the original half-spin bundles

Public module ID: M1462.

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
The induced connection preserves the original Fock metric and obeys the
Clifford Leibniz rule. No curvature or Lichnerowicz formula is claimed.
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

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1000000 in
-- The assembly matches all original metric, principal and associated-atlas instances.
/-- The actual Levi-Civita lift induces a unitary connection on each original half-spin atlas. -/
theorem exists_halfSpinorConnection :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ (S : TopologicalSpinStructure m TM o hm hP) (i : ZMod 2),
    ∃ cov : AtlasComplexConnection
        (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i),
      S.IsInducedHalfSpinorConnection g i cov ∧
        cov.IsUnitary (halfSpinorHermitianMetric m hP (S.smoothPrincipalAtlas I) i) := by
  /- Stage 1: the actual Levi-Civita connection preserves the supplied
  metric and is torsion free, by mathlib. Its Koszul formula in the smooth
  lifted orthonormal frames expresses its coefficients through the smooth
  metric and first derivatives of those same frames. Thus the real matrix
  omega_ab(X)=g(nabla_X e_a,e_b) is smooth and skew in a,b.
  Stage 2: the differential of the original Spin representation sends
  that skew matrix to one quarter of sum omega_ab c_a c_b. The Clifford
  commutator [c_a c_b,c_k]=2 delta_ak c_b-2 delta_bk c_a checks both
  this coefficient and its sign. Each product preserves exterior parity.
  The lift of the Levi-Civita frame connection therefore supplies these
  exact half-spin connection forms in the same principal charts.
  Stage 3: differentiating the actual original Spin transition matrices
  gives the standard connection gauge law. Consequently d plus this form
  agrees on all overlaps on original quotient sections, and transforms
  smoothly into every chart of the selected associated half-spin atlas.
  Package precisely these compatible forms in AtlasComplexConnection.
  Stage 4: real skew omega makes the displayed bivector action skew for
  the original Fock pairing. The product rule for that fixed form proves
  the unitary identity in the original fibers. No target Dirac operator,
  assumed compatibility identity or different connection is an input. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S i
  let A := S.smoothPrincipalAtlas I
  let H := halfSpinorBundleSmoothAtlas m hP A i
  -- The actual associated atlas receives the smooth, gauge-compatible spin lift.
  obtain ⟨cov, hcov⟩ := exists_associatedSpinConnection hP
    (complexSpinParityContRepresentation m i) A H
    ((spinorBundleSmoothAtlases_compatibility m hP A).2.1 i)
    (S.liftedHalfSpinConnectionForm i)
    (S.contDiffOn_liftedHalfSpinConnectionForm i)
    (A.mdifferentiableAt_halfSpinTransition i)
    (S.liftedHalfSpinConnectionForm_gauge i)
  refine ⟨cov, ?_, S.isUnitary_of_halfSpinorConnection_coordinates i cov hcov⟩
  -- The full original exterior-coordinate predicate uses precisely the same form.
  exact (isInducedHalfSpinorConnection_iff_coordinates g S i cov).mpr hcov

/-- The canonical half-spin connection selected from its actual Levi-Civita local formula. -/
def halfSpinorConnection :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  (S : TopologicalSpinStructure m TM o hm hP) → (i : ZMod 2) →
    AtlasComplexConnection (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i) :=
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  fun S i ↦ (S.exists_halfSpinorConnection g i).choose

set_option linter.defProp false in
/-- The selected connection retains the same local spin formula and original unitary metric. -/
def halfSpinorConnection_properties :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ (S : TopologicalSpinStructure m TM o hm hP) (i : ZMod 2),
    S.IsInducedHalfSpinorConnection g i (S.halfSpinorConnection g i) ∧
      (S.halfSpinorConnection g i).IsUnitary
        (halfSpinorHermitianMetric m hP (S.smoothPrincipalAtlas I) i) :=
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  fun S i ↦ (S.exists_halfSpinorConnection g i).choose_spec

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced half-spin connections satisfy the original Clifford-module Leibniz rule. -/
theorem halfSpinorConnection_clifford :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ (S : TopologicalSpinStructure m TM o hm hP) (i : ZMod 2),
    let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
    ∀ (Y : ∀ y : M, TangentSpace I y)
      (_hY : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))).tangent ∞
        (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)))
      (u : (H i).smoothSections),
      ∃ v : (H (i + 1)).smoothSections,
        (∀ x : M, v.val x = S.cliffordParity x (Y x) i (u.val x)) ∧
          ∀ (x : M) (X : TangentSpace I x),
            (S.halfSpinorConnection g (i + 1)).covariantDerivative v x X =
              S.cliffordParity x
                (CovariantDerivative.leviCivitaConnection I M Y x X) i (u.val x) +
              S.cliffordParity x (Y x) i
                ((S.halfSpinorConnection g i).covariantDerivative u x X) := by
  /- Stage 1: in the same lifted spin frame, the original Clifford action
  is the standard bilinear action of tangent coordinates on the exterior
  model. The given smooth tangent field and half-spin section therefore
  yield a smooth section in the opposite parity. Its values are exactly
  the original associated quotient action, not an auxiliary representative.
  Stage 2: use the exact local formulas retained by both selected spin
  connections. The commutator of one quarter of sum omega_ab c_a c_b
  with c(Y) equals c of the Levi-Civita connection part of Y. The ordinary
  derivative product rule supplies the derivative of Y and of u.
  Stage 3: identify their sum with the actual native Levi-Civita derivative
  of this smooth Y and descend through the same local quotient frames.
  This proves SG II.4 Proposition 4.11 on the original parity bundles;
  neither Clifford compatibility nor smoothness of the output is assumed. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S i
  dsimp only
  intro Y hY u
  exact inducedHalfSpinorConnections_clifford g S i
    (S.halfSpinorConnection g i) (S.halfSpinorConnection g (i + 1))
    (S.halfSpinorConnection_properties g i).1
    (S.halfSpinorConnection_properties g (i + 1)).1 Y hY u

end TopologicalSpinStructure

end AtiyahSinger
