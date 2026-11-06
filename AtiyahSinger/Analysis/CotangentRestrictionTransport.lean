/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndexRestriction

/-!
# The action transport in native cotangent restriction

Public module ID: M0424.

This implementation adapter exposes the already defined restriction as the
original support restriction followed by the same action transport. It allows
open-class comparisons to retain the specified cotangent lift without repeatedly
unfolding its dependent transport inside geometric index proofs.
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The native restriction uses exactly the supplied equality of the same two cotangent actions. -/
theorem equivariantCotangentKZeroRestrict_eq_actionTransport (φ : H →ₜ* G)
    (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, VG) ∞ φ) :
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let AH := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    let AR := MulAction.compHom (CotangentTotalSpace (n := n) (M := M)) φ.toMonoidHom
    letI := AH
    letI := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    let CH : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let CR : letI := AR
        ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
      MulAction.continuousSMul_compHom φ.continuous
    ∀ h : AR = AH,
      equivariantCotangentKZeroRestrict (n := n) (M := M) φ hφ =
        (kActionTransport AR AH CR CH h).comp (equivariantSupportTripleKZeroRestrict φ) := by
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
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
  let CR : letI := AR
      ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom φ.continuous
  dsimp only
  intro h
  -- The definition's equality proof has the same endpoints, so proof irrelevance identifies it.
  unfold equivariantCotangentKZeroRestrict
  exact transport_hom_eq_comp AR AH CR CH h _

end AtiyahSinger
