/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClopenSymbolIndex
public import AtiyahSinger.Analysis.EquivariantPiecewiseSymbol
public import AtiyahSinger.Geometry.EquivariantClopenPartition

/-!
# Whole finite families of the original equivariant elliptic symbols

Public module ID: M0484.

These implementation packages let dependent choice retain the partition,
actions, symbols and certificates together. The associated K class uses the
original clopen restriction equivalence, and the value is the finite sum of
the original full symbol indices. No independence or additivity is built into
the data. Those remain the mathematical descent conclusions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

/-- Implementation type retaining one complete original symbol on each actual piece. -/
def EquivariantClopenPartition.Symbols
    (P : EquivariantClopenPartition (G := G) (M := M)) : Type _ :=
  letI := P.mulAction
  letI := P.continuousSMul
  letI := P.contMDiffSMul (VG := VG) (n := n)
  ∀ i, EquivariantEllipticSymbolData (n := n) (M := P.piece i) (VG := VG) (G := G)

/-- Implementation package for choosing an actual partition and all of its original symbols. -/
structure EquivariantClopenSymbolFamily where
  /-- The actual finite invariant clopen partition. -/
  partition : EquivariantClopenPartition (G := G) (M := M)
  /-- The original symbols with the induced ambient actions. -/
  symbols : partition.Symbols (VG := VG) (n := n)

variable [CompactSpace M]

/-- Reconstruct the original K class from precisely the displayed local symbols. -/
def EquivariantClopenSymbolFamily.kClass
    (a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) := by
  let P := a.partition
  letI := P.mulAction
  letI := P.continuousSMul
  letI := P.contMDiffSMul (VG := VG) (n := n)
  letI := P.compactSpace
  exact (equivariantCotangentClopenEquiv 𝓘(ℝ, VG) P.piece P.isClosed
    P.equivariant P.disjoint P.cover).symm (fun i ↦ (a.symbols i).kClass)

variable [hGC : CompactSpace G] [hGT : T2Space G] [MeasurableSpace G] [BorelSpace G]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The sum of the existing full symbol indices; independence is proved separately. -/
def EquivariantClopenSymbolFamily.index
    (a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G)) :
    RepresentationGrothendieckGroup G := by
  let P := a.partition
  letI := P.mulAction
  letI := P.continuousSMul
  letI := P.contMDiffSMul (VG := VG) (n := n)
  letI := P.compactSpace
  exact ∑ i, (a.symbols i).index

variable [hDim : FiniteDimensional ℝ VG]

omit [MeasurableSpace G] [BorelSpace G] [MeasurableSpace M] [BorelSpace M]

include hGC hGT hT hSC hDim in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original K class is represented by one complete finite family of original symbols. -/
theorem exists_equivariantClopenSymbolFamily :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      ∃ a : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VG) (G := G),
        a.kClass = z := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro z
  -- Retain the exact witnesses of the original piecewise representative theorem.
  obtain ⟨k, U, _hne, hc, hd, hcov, actions, continuousActions, smoothActions,
    heq, compactPieces, b, hb, hr, _hrec⟩ :=
      exists_piecewise_equivariant_homogeneous_symbol (VG := VG) z
  let := actions
  let := continuousActions
  let := smoothActions
  let := compactPieces
  have hinv (i : Fin k) (g : G) (x : M) : g • x ∈ U i ↔ x ∈ U i := by
    constructor
    · intro hx
      have h := (g⁻¹ • (⟨g • x, hx⟩ : U i)).property
      simpa only [heq, inv_smul_smul] using h
    · intro hx
      have h := (g • (⟨x, hx⟩ : U i)).property
      simpa only [heq] using h
  let P : EquivariantClopenPartition (G := G) (M := M) := {
    size := k
    piece := U
    isClosed := hc
    disjoint := hd
    cover := hcov
    invariant := hinv
    mulAction := actions
    equivariant := heq }
  choose E F σE σF hσE hσF s hi hs hbi hbeq using hb
  let a : P.Symbols (n := n) (VG := VG) := fun i ↦ {
    source := E i
    target := F i
    sourceAction := σE i
    targetAction := σF i
    source_smooth := hσE i
    target_smooth := hσF i
    symbol := s i
    elliptic := hi i
    equivariant := hs i }
  refine ⟨⟨P, a⟩, ?_⟩
  -- The same original clopen restriction identifies every displayed coordinate.
  let Φ := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) U hc heq hd hcov
  apply Φ.injective
  change Φ (Φ.symm (fun i ↦ (a i).kClass)) = Φ z
  rw [Φ.apply_symm_apply]
  funext i
  change (a i).kClass = equivariantCotangentClopenRestrict 𝓘(ℝ, VG) U hc heq z i
  rw [hr, hbeq]
  rfl

end AtiyahSinger
