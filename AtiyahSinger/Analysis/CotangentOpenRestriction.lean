/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentRestrictionTransport
public import AtiyahSinger.Topology.EquivariantOpenActionTransport
public import AtiyahSinger.Topology.EquivariantOpenRestriction

/-!
# Native cotangent restriction and open extension

Public module ID: M0423.

The original group restriction and the original controlled open extension
commute after the explicit equality between the restricted and native
cotangent lifts. The same open map and the same support class are retained.
This is used in the common-open sphere comparison.
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

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native cotangent restriction preserves extension through the same equivariant open map. -/
theorem equivariantCotangentKZeroRestrict_openPushforward (φ : H →ₜ* G)
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
      equivariantCotangentKZeroRestrict (n := n) (M := M) φ hφ
          (equivariantSupportTripleKZeroOpenPushforward j hj heqG a) =
        equivariantSupportTripleKZeroOpenPushforward j hj heqH
          (equivariantSupportTripleKZeroRestrict φ a) := by
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
  let AR := MulAction.compHom (CotangentTotalSpace (n := n) (M := M)) φ.toMonoidHom
  let := AH
  let := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let CH : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := CH
  let CR : letI := AR
      ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom φ.continuous
  intro heqH a
  -- Compare the actual base diffeomorphisms before taking their inverse differentials.
  have hLift : AH = AR := by
    apply MulAction.ext
    funext h z
    have he : Diffeomorph.smul (M := M) 𝓘(ℝ, VH)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h =
        Diffeomorph.smul (M := M) 𝓘(ℝ, VG)
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (φ h) := by
      apply Diffeomorph.ext
      intro x
      rfl
    exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) he
  have hmap := equivariantCotangentKZeroRestrict_eq_actionTransport
    (n := n) (M := M) φ hφ hLift.symm
  have hraw := equivariantSupportTripleKZeroRestrict_openPushforward φ j hj heqG a
  have htransport := kActionTransport_openPushforward RX RX AR AH CX CX CR CH
    rfl hLift.symm j hj (fun h x ↦ heqG (φ h) x) heqH
  -- Transport the same restricted open class; the source action transport is the identity.
  exact (DFunLike.congr_fun hmap _).trans
    ((congrArg (kActionTransport AR AH CR CH hLift.symm) hraw).trans
      (DFunLike.congr_fun htransport (equivariantSupportTripleKZeroRestrict φ a)))

end AtiyahSinger
