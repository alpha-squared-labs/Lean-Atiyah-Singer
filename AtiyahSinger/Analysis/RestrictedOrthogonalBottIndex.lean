/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantOpenIndexRestriction
public import AtiyahSinger.Analysis.OrthogonalPointIndex
public import AtiyahSinger.Analysis.SphereNativePoleIndex
public import AtiyahSinger.Topology.EquivariantBottRestriction

/-!
# An analytic left inverse for restricted orthogonal Bott maps (M2324)

A specified smooth homomorphism from a compact Lie group H to O(r) restricts
the original real representation and its complexification. Open extension
through the original sphere cotangent pole chart, followed by the H-equivariant
analytic index, is a left inverse for that actual Bott map.

Only the unit normalization is restricted from O(r). The original H-index is
linear over R(H), so its value on every representation coefficient is recovered
without assuming that restriction from R(O(r)) is surjective. Both sphere poles
and dimension zero are retained. The injectivity conclusion includes dimension
zero and assumes no Bott surjectivity.

This is a consequence of the independently proved P07 normalization, with the
original native cotangent action and complete representation coefficients.
It does not replace the separate independent inverse obligation in AB01, or
claim bijectivity for a general complex representation. Smoothness of the
specified homomorphism and the standard finite-dimensional Lie model are
explicit assumptions. No automatic change of the original group model is used.

Sources: Atiyah--Singer I, Proposition 4.4 and Lemma 4.7, pp.505,507--508,
for the established orthogonal normalization, and the original representation
linearity and restriction properties of the equivariant analytic index.
The left-inverse conclusion is a project supplementary consequence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 40

attribute [local instance] lieGroup_orthogonalGroup compactSpace_orthogonalGroup
  continuousSMul_orthogonalSphere t2Space_cotangent locallyCompactSpace_cotangent

variable {VH H : Type*} [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [LieGroup 𝓘(ℝ, VH) ∞ H]

variable [FiniteDimensional ℝ VH] [CompactSpace H] [T2Space H]

/-- The original H-index after open extension through the specified native cotangent pole chart. -/
def restrictedOrthogonalBottIndex (r : ℕ) (atInfinity : Bool)
    (φ : H →ₜ* Matrix.orthogonalGroup (Fin r) ℝ)
    (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, OrthogonalGroupModel r) ∞ φ) :
    letI : DistribMulAction H (EuclideanSpace ℂ (Fin r)) :=
      DistribMulAction.compHom _ φ.toMonoidHom
    letI : ContinuousSMul H (EuclideanSpace ℂ (Fin r)) :=
      MulAction.continuousSMul_compHom φ.continuous
    EquivariantSupportTripleKZero H (EuclideanSpace ℂ (Fin r)) →+
      RepresentationGrothendieckGroup H := by
  let : DistribMulAction H (EuclideanSpace ℂ (Fin r)) :=
    DistribMulAction.compHom _ φ.toMonoidHom
  let : ContinuousSMul H (EuclideanSpace ℂ (Fin r)) :=
    MulAction.continuousSMul_compHom φ.continuous
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere r) := borel (OrthogonalSphere r)
  let : BorelSpace (OrthogonalSphere r) := ⟨rfl⟩
  let : MulAction H (OrthogonalSphere r) := MulAction.compHom _ φ.toMonoidHom
  let : ContinuousSMul H (OrthogonalSphere r) :=
    MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) (𝓡 r) ∞ H (OrthogonalSphere r) :=
    MulAction.contMDiffSMul_compHom hφ
  let := smoothCotangentMulAction (n := r) (G := H)
    (M := OrthogonalSphere r) 𝓘(ℝ, VH)
  let : SMul H (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    (smoothCotangentMulAction (n := r) (G := H)
      (M := OrthogonalSphere r) 𝓘(ℝ, VH)).toSMul
  let : ContMDiffSMul 𝓘(ℝ, VH) ((𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞ H
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    contMDiffSMul_smoothCotangent (n := r) (G := H)
      (M := OrthogonalSphere r) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
  -- The same base action has the same inverse differential on every covector.
  have he (h : H) (z : EuclideanSpace ℂ (Fin r)) :
      orthogonalSphereCotangentChart r atInfinity (h • z) =
        h • orthogonalSphereCotangentChart r atInfinity z := by
    have hd : Diffeomorph.smul (M := OrthogonalSphere r) 𝓘(ℝ, VH) (𝓡 r) ∞ h =
        orthogonalSphereDiffeomorph r (φ h) := by
      apply Diffeomorph.ext
      intro x
      rfl
    change orthogonalSphereCotangentChart r atInfinity
      (orthogonalComplexificationRepresentation r (φ h) z) =
        cotangentDiffeomorphMap
          (Diffeomorph.smul (M := OrthogonalSphere r) 𝓘(ℝ, VH) (𝓡 r) ∞ h)
          (orthogonalSphereCotangentChart r atInfinity z)
    rw [hd]
    exact orthogonalSphereCotangentChart_equivariant r atInfinity (φ h) z
  exact (equivariantAnalyticIndexMap (n := r) (VG := VH) (G := H)
    (M := OrthogonalSphere r)).comp
      (equivariantSupportTripleKZeroOpenPushforward
        (orthogonalSphereCotangentChart r atInfinity)
        (orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity)
        he)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the native restricted index and all original representation
-- coefficients.
/-- The native restricted index recovers every original R(H) coefficient of the Bott map. -/
theorem restrictedOrthogonalBottIndex_bott (r : ℕ) (atInfinity : Bool)
    (φ : H →ₜ* Matrix.orthogonalGroup (Fin r) ℝ)
    (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, OrthogonalGroupModel r) ∞ φ)
    (a : RepresentationGrothendieckGroup H) :
    letI : DistribMulAction H (EuclideanSpace ℂ (Fin r)) :=
      DistribMulAction.compHom _ φ.toMonoidHom
    letI : SMulCommClass H ℂ (EuclideanSpace ℂ (Fin r)) :=
      ⟨fun h c v ↦ smul_comm (φ h) c v⟩
    letI : ContinuousSMul H (EuclideanSpace ℂ (Fin r)) :=
      MulAction.continuousSMul_compHom φ.continuous
    restrictedOrthogonalBottIndex r atInfinity φ hφ
        (equivariantBottLinearMap
          (fun h u v ↦ orthogonalComplexification_unitary r (φ h) u v) a) = a := by
  classical
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin r) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin r) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin r) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere r) := borel (OrthogonalSphere r)
  let : BorelSpace (OrthogonalSphere r) := ⟨rfl⟩
  let : DistribMulAction H (EuclideanSpace ℂ (Fin r)) :=
    DistribMulAction.compHom _ φ.toMonoidHom
  let : SMulCommClass H ℂ (EuclideanSpace ℂ (Fin r)) :=
    ⟨fun h c v ↦ smul_comm (φ h) c v⟩
  let : ContinuousSMul H (EuclideanSpace ℂ (Fin r)) :=
    MulAction.continuousSMul_compHom φ.continuous
  let : MulAction H (OrthogonalSphere r) := MulAction.compHom _ φ.toMonoidHom
  let : ContinuousSMul H (OrthogonalSphere r) :=
    MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) (𝓡 r) ∞ H (OrthogonalSphere r) :=
    MulAction.contMDiffSMul_compHom hφ
  -- Fix both original native cotangent actions before invoking their restriction comparison.
  let := smoothCotangentMulAction (n := r)
    (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
    𝓘(ℝ, OrthogonalGroupModel r)
  let : SMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    (smoothCotangentMulAction (n := r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      𝓘(ℝ, OrthogonalGroupModel r)).toSMul
  let : ContMDiffSMul 𝓘(ℝ, OrthogonalGroupModel r)
      ((𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞ (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    contMDiffSMul_smoothCotangent (n := r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      𝓘(ℝ, OrthogonalGroupModel r)
  let : ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel r))
      (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
  let := smoothCotangentMulAction (n := r) (G := H)
    (M := OrthogonalSphere r) 𝓘(ℝ, VH)
  let : SMul H (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    (smoothCotangentMulAction (n := r) (G := H)
      (M := OrthogonalSphere r) 𝓘(ℝ, VH)).toSMul
  let : ContMDiffSMul 𝓘(ℝ, VH) ((𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞ H
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    contMDiffSMul_smoothCotangent (n := r) (G := H)
      (M := OrthogonalSphere r) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
  let j : C(EuclideanSpace ℂ (Fin r),
      CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    orthogonalSphereCotangentChart r atInfinity
  have heO (g : Matrix.orthogonalGroup (Fin r) ℝ) (z : EuclideanSpace ℂ (Fin r)) :
      j (orthogonalComplexificationRepresentation r g z) = g • j z := by
    have hd : Diffeomorph.smul (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r) (𝓡 r) ∞ g = orthogonalSphereDiffeomorph r g := by
      apply Diffeomorph.ext
      intro x
      rfl
    change j (orthogonalComplexificationRepresentation r g z) = cotangentDiffeomorphMap
      (Diffeomorph.smul (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r) (𝓡 r) ∞ g) (j z)
    rw [hd]
    exact orthogonalSphereCotangentChart_equivariant r atInfinity g z
  have heH (h : H) (z : EuclideanSpace ℂ (Fin r)) : j (h • z) = h • j z := by
    have hd : Diffeomorph.smul (M := OrthogonalSphere r) 𝓘(ℝ, VH) (𝓡 r) ∞ h =
        orthogonalSphereDiffeomorph r (φ h) := by
      apply Diffeomorph.ext
      intro x
      rfl
    change j (orthogonalComplexificationRepresentation r (φ h) z) =
      cotangentDiffeomorphMap
        (Diffeomorph.smul (M := OrthogonalSphere r) 𝓘(ℝ, VH) (𝓡 r) ∞ h) (j z)
    rw [hd]
    exact orthogonalSphereCotangentChart_equivariant r atInfinity (φ h) z
  let βO : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
      (EuclideanSpace ℂ (Fin r)) :=
    equivariantExteriorBottClass (orthogonalComplexification_unitary r)
  let βH : EquivariantSupportTripleKZero H (EuclideanSpace ℂ (Fin r)) :=
    equivariantExteriorBottClass
      (fun h u v ↦ orthogonalComplexification_unitary r (φ h) u v)
  let IH : EquivariantSupportTripleKZero H
      (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) →+
        RepresentationGrothendieckGroup H :=
    equivariantAnalyticIndexMap (n := r) (VG := VH) (G := H) (M := OrthogonalSphere r)
  -- Restrict the unit normalization only, using the same open map and native lifts.
  have hO : equivariantAnalyticIndexMap (n := r) (VG := OrthogonalGroupModel r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      (equivariantSupportTripleKZeroOpenPushforward j
        (orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity) heO βO) = 1 :=
    (orthogonalSpherePoleIndex_eq_nativeOpenIndex r atInfinity heO).symm.trans
      (orthogonalSpherePoleIndex_eq_one r atInfinity)
  have hrestrict := representationRestriction_equivariantAnalyticIndexMap_openPushforward
    (n := r) (M := OrthogonalSphere r) (VG := OrthogonalGroupModel r) (VH := VH)
    φ hφ j (orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity) heO heH βO
  have hunit : IH (equivariantSupportTripleKZeroOpenPushforward j
      (orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity) heH βH) = 1 := by
    rw [hO, map_one, equivariantExteriorBottClass_restrict] at hrestrict
    exact hrestrict.symm
  -- H-linearity supplies every coefficient, including those not restricted from O(r).
  change IH (equivariantSupportTripleKZeroOpenPushforward j
    (orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity) heH (a • βH)) = a
  rw [equivariantSupportTripleKZeroOpenPushforward_smul,
    equivariantAnalyticIndexMap_smul, hunit]
  exact mul_one a

/-- The original Bott map for a specified restricted orthogonal complexification is injective. -/
theorem equivariantBottLinearMap_orthogonalRestriction_injective (r : ℕ)
    (φ : H →ₜ* Matrix.orthogonalGroup (Fin r) ℝ)
    (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, OrthogonalGroupModel r) ∞ φ) :
    letI : DistribMulAction H (EuclideanSpace ℂ (Fin r)) :=
      DistribMulAction.compHom _ φ.toMonoidHom
    letI : SMulCommClass H ℂ (EuclideanSpace ℂ (Fin r)) :=
      ⟨fun h c v ↦ smul_comm (φ h) c v⟩
    letI : ContinuousSMul H (EuclideanSpace ℂ (Fin r)) :=
      MulAction.continuousSMul_compHom φ.continuous
    Function.Injective (equivariantBottLinearMap
      (fun h u v ↦ orthogonalComplexification_unitary r (φ h) u v)) := by
  let : DistribMulAction H (EuclideanSpace ℂ (Fin r)) :=
    DistribMulAction.compHom _ φ.toMonoidHom
  let : SMulCommClass H ℂ (EuclideanSpace ℂ (Fin r)) :=
    ⟨fun h c v ↦ smul_comm (φ h) c v⟩
  let : ContinuousSMul H (EuclideanSpace ℂ (Fin r)) :=
    MulAction.continuousSMul_compHom φ.continuous
  -- The already constructed left inverse acts on the same two original Bott values.
  exact Function.LeftInverse.injective
    (restrictedOrthogonalBottIndex_bott r false φ hφ)

end AtiyahSinger
