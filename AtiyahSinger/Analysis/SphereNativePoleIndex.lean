/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalComplexification
public import AtiyahSinger.Analysis.SphereCotangentPoleClass
public import AtiyahSinger.Topology.EquivariantOpenActionTransport

/-!
# The native index of the original sphere pole class

Public module ID: M1011.

Equality of the round musical and native cotangent actions identifies the
original pole class with the same exterior Bott generator in the specified
open cotangent chart. The index comparison uses that action equality.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 40

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent compactSpace_orthogonalGroup

private theorem transport_index_open
    {G X Y C : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
    [MulAction G X] [ContinuousSMul G X] [AddCommGroup C]
    (A B : MulAction G Y)
    (hA : letI := A; ContinuousSMul G Y)
    (hB : letI := B; ContinuousSMul G Y) (h : A = B)
    (f : (letI := A; letI := hA; EquivariantSupportTripleKZero G Y) →+ C)
    (j : C(X, Y)) (hj : Topology.IsOpenEmbedding j)
    (heA : letI := A; ∀ (g : G) (x : X), j (g • x) = g • j x)
    (heB : letI := B; ∀ (g : G) (x : X), j (g • x) = g • j x)
    (v : EquivariantSupportTripleKZero G X) :
    (by
      have transport (a b : MulAction G Y)
          (ha : letI := a; letI := a.toSMul; ContinuousSMul G Y)
          (hb : letI := b; letI := b.toSMul; ContinuousSMul G Y) (hab : a = b) :
          ((letI := a; letI := a.toSMul; letI := ha;
              EquivariantSupportTripleKZero G Y) →+ C) →
            ((letI := b; letI := b.toSMul; letI := hb;
              EquivariantSupportTripleKZero G Y) →+ C) := by
        cases hab
        exact id
      exact transport A B hA hB h f :
      (letI := B; letI := hB; EquivariantSupportTripleKZero G Y) →+ C)
      (letI := B; letI := hB; equivariantSupportTripleKZeroOpenPushforward j hj heB v) =
        f (letI := A; letI := hA; equivariantSupportTripleKZeroOpenPushforward j hj heA v) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Use equality of the two cotangent actions on the same equivariant support quotient.
/-- The same original musical pole index is evaluated on its native open cotangent class. -/
theorem orthogonalSpherePoleIndex_eq_nativeOpenIndex (r : ℕ) (atInfinity : Bool) :
    letI := lieGroup_orthogonalGroup r
    letI : MeasurableSpace (Matrix.orthogonalGroup (Fin r) ℝ) :=
      borel (Matrix.orthogonalGroup (Fin r) ℝ)
    letI : BorelSpace (Matrix.orthogonalGroup (Fin r) ℝ) := ⟨rfl⟩
    letI : MeasurableSpace (OrthogonalSphere r) := borel (OrthogonalSphere r)
    letI : BorelSpace (OrthogonalSphere r) := ⟨rfl⟩
    letI := smoothCotangentMulAction (n := r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      𝓘(ℝ, OrthogonalGroupModel r)
    letI : SMul (Matrix.orthogonalGroup (Fin r) ℝ)
        (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
      (smoothCotangentMulAction (n := r)
        (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r)).toSMul
    letI := contMDiffSMul_smoothCotangent (n := r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      𝓘(ℝ, OrthogonalGroupModel r)
    letI : ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
        (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel r))
        (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
    ∀ (he : ∀ (a : Matrix.orthogonalGroup (Fin r) ℝ) (z : EuclideanSpace ℂ (Fin r)),
      orthogonalSphereCotangentChart r atInfinity
        (orthogonalComplexificationRepresentation r a z) =
        a • orthogonalSphereCotangentChart r atInfinity z),
      orthogonalSphereTangentAnalyticIndex r
        (orthogonalSpherePolePushforward r atInfinity 1) =
      equivariantAnalyticIndexMap (n := r) (VG := OrthogonalGroupModel r)
        (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
        (equivariantSupportTripleKZeroOpenPushforward
          (orthogonalSphereCotangentChart r atInfinity)
          (orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity) he
          (equivariantExteriorBottClass (orthogonalComplexification_unitary r))) := by
  let := lieGroup_orthogonalGroup r
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin r) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin r) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin r) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere r) := borel (OrthogonalSphere r)
  let : BorelSpace (OrthogonalSphere r) := ⟨rfl⟩
  let A := smoothCotangentMulAction (n := r)
    (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
    𝓘(ℝ, OrthogonalGroupModel r)
  let B := orthogonalSphereCotangentMulAction r
  let := A
  let : SMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) := A.toSMul
  let := contMDiffSMul_smoothCotangent (n := r)
    (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
    𝓘(ℝ, OrthogonalGroupModel r)
  let hA : ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel r))
      (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
  let := hA
  intro he
  -- Equality is established on the actual inverse differentials, before using the quotient.
  have hLift : A = B := by
    apply MulAction.ext
    funext a z
    have hd : Diffeomorph.smul (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r) (𝓡 r) ∞ a = orthogonalSphereDiffeomorph r a := by
      apply Diffeomorph.ext
      intro x
      rfl
    exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) hd
  change orthogonalSphereAnalyticIndex r
    (orthogonalSphereMusicalKMap r (orthogonalSpherePolePushforward r atInfinity 1)) = _
  rw [orthogonalSphereMusicalKMap_polePushforward]
  -- Evaluate through the definition's action transport using its abstract equality rule.
  unfold orthogonalSphereAnalyticIndex
  exact transport_index_open A B hA (continuousSMul_orthogonalSphereCotangent r) hLift
    (equivariantAnalyticIndexMap (n := r) (VG := OrthogonalGroupModel r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r))
    (orthogonalSphereCotangentChart r atInfinity)
    (orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity) he
    (orthogonalSphereCotangentChart_equivariant r atInfinity)
    (equivariantExteriorBottClass (orthogonalComplexification_unitary r))

end AtiyahSinger
