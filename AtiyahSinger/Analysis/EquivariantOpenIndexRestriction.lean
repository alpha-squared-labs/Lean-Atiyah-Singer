/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRingRestriction
public import AtiyahSinger.Analysis.CotangentOpenRestriction

/-!
# Restriction of the full index of an open support class

Public module ID: M0544.

Native cotangent restriction and analytic-index restriction are composed
before specializing geometric data. Both sides retain the same open map
and source class, including the explicit equality of the two native lifts.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G]
  {VH H : Type*} [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [LieGroup 𝓘(ℝ, VH) ∞ H]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]


variable [CompactSpace G] [T2Space G] [CompactSpace H] [T2Space H] [T2Space M]
  {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [MulAction G X] [ContinuousSMul G X]

variable [FiniteDimensional ℝ VG] [FiniteDimensional ℝ VH]
  [CompactSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of the full index commutes with extension through the same equivariant open map. -/
theorem representationRestriction_equivariantAnalyticIndexMap_openPushforward (φ : H →ₜ* G)
    (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, VG) ∞ φ)
    (j : C(X, CotangentTotalSpace (n := n) (M := M))) (hj : Topology.IsOpenEmbedding j)
    (heqG : letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
      ∀ (g : G) (x : X), j (g • x) = g • j x) :
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ (heqH : ∀ (h : H) (x : X), j (h • x) = h • j x)
      (a : EquivariantSupportTripleKZero G X),
      representationRestrictionRingHom φ
          (equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G)
            (equivariantSupportTripleKZeroOpenPushforward j hj heqG a)) =
        equivariantAnalyticIndexMap (n := n) (M := M) (VG := VH) (G := H)
          (equivariantSupportTripleKZeroOpenPushforward j hj heqH
            (equivariantSupportTripleKZeroRestrict φ a)) := by
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  let RX : MulAction H X := MulAction.compHom X φ.toMonoidHom
  let := RX
  let CX : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  let := CX
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let AH := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let := AH
  let := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let CH : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := CH
  intro heqH a
  -- The same native restriction is used in both established naturality formulas.
  have hindex := DFunLike.congr_fun
    (representationRestriction_equivariantAnalyticIndexMap (n := n) (M := M)
      (VG := VG) (VH := VH) φ hφ)
    (equivariantSupportTripleKZeroOpenPushforward j hj heqG a)
  have hopen := equivariantCotangentKZeroRestrict_openPushforward
    (n := n) (M := M) (VG := VG) (VH := VH) φ hφ j hj heqG heqH a
  exact hindex.trans (congrArg
    (equivariantAnalyticIndexMap (n := n) (M := M) (VG := VH) (G := H)) hopen)

end AtiyahSinger
