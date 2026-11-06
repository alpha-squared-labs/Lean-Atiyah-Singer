/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantClopenFamilyDiffeomorph

/-!
# Full equivariant analytic-index naturality under diffeomorphisms

Public module ID: M0459.

Represent an arbitrary original K class by its actual finite clopen symbol
family. Transport that whole family along the same diffeomorphism, preserving
its native cotangent class and full representation-valued index. Evaluate both
families by the original analytic index. No global fixed-rank representative
or injectivity of representation dimension is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [CompactSpace N] [T2Space N] [SecondCountableTopology N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original full index is natural for the actual proper cotangent pullback. -/
theorem equivariantAnalyticIndexMap_diffeomorphPullback
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N)
    (he : ∀ (g : G) (x : M), e (g • x) = g • e x)
    (hcot : letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
      letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
      ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := N)),
        cotangentDiffeomorph e.symm (g • z) = g • cotangentDiffeomorph e.symm z) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := N)
        (equivariantSupportTripleKZeroPullback
          ⟨cotangentDiffeomorph e.symm, (cotangentDiffeomorph e.symm).continuous⟩
          hcot (cotangentDiffeomorph e.symm).isProperMap z) =
        equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M) z := by
  classical
  let IG := 𝓘(ℝ, VG)
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := N) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro z
  -- Keep one original representative family and transport those same symbol data.
  obtain ⟨a, ha⟩ := exists_equivariantClopenSymbolFamily
    (n := n) (M := M) (VG := VG) (G := G) z
  obtain ⟨b, hi, hb⟩ := a.exists_diffeomorph_pullback e he hcot
  have haEval : equivariantAnalyticIndexMap
      (n := n) (M := M) (VG := VG) (G := G) a.kClass = a.index := by
    let P := a.partition
    let := P.mulAction
    let := P.continuousSMul
    let := P.contMDiffSMul (n := n) (VG := VG)
    let := P.compactSpace
    exact equivariantAnalyticIndexMap_clopen (n := n) (M := M) (VG := VG) (G := G)
      P.size P.piece P.isClosed P.disjoint P.cover P.mulAction P.continuousSMul
      (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
      (fun i ↦ (a.symbols i).source) (fun i ↦ (a.symbols i).target)
      (fun i ↦ (a.symbols i).sourceAction) (fun i ↦ (a.symbols i).targetAction)
      (fun i ↦ (a.symbols i).source_smooth) (fun i ↦ (a.symbols i).target_smooth)
      (fun i ↦ (a.symbols i).symbol) (fun i ↦ (a.symbols i).elliptic)
      (fun i ↦ (a.symbols i).equivariant)
  have hbEval : equivariantAnalyticIndexMap
      (n := n) (M := N) (VG := VG) (G := G) b.kClass = b.index := by
    let P := b.partition
    let := P.mulAction
    let := P.continuousSMul
    let := P.contMDiffSMul (n := n) (VG := VG)
    let := P.compactSpace
    exact equivariantAnalyticIndexMap_clopen (n := n) (M := N) (VG := VG) (G := G)
      P.size P.piece P.isClosed P.disjoint P.cover P.mulAction P.continuousSMul
      (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
      (fun i ↦ (b.symbols i).source) (fun i ↦ (b.symbols i).target)
      (fun i ↦ (b.symbols i).sourceAction) (fun i ↦ (b.symbols i).targetAction)
      (fun i ↦ (b.symbols i).source_smooth) (fun i ↦ (b.symbols i).target_smooth)
      (fun i ↦ (b.symbols i).symbol) (fun i ↦ (b.symbols i).elliptic)
      (fun i ↦ (b.symbols i).equivariant)
  -- The two original full index maps evaluate precisely these matching families.
  rw [← ha, ← hb]
  exact hbEval.trans (hi.trans haEval.symm)

end AtiyahSinger
