/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolKIndexInvariance

/-!
# Bundled data for the original equivariant elliptic symbols

Public module ID: M0502.

This implementation record stores the same small smooth bundles, actions,
homogeneous symbol, and certificates used by the existing symbol K class and
canonical index. It permits dependent choice of whole symbol families during
finite clopen refinement. It introduces no new quotient, index law, or model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
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

/-- Implementation package retaining every datum of one original degree-zero elliptic symbol. -/
structure EquivariantEllipticSymbolData where
  /-- The original smooth source bundle, with its independent rank. -/
  source : SmoothFiniteComplexBundle (n := n) M
  /-- The original smooth target bundle, with its independent rank. -/
  target : SmoothFiniteComplexBundle (n := n) M
  /-- The specified action on the original source bundle. -/
  sourceAction : letI := modelTopology (EuclideanSpace ℂ (Fin source.rank)) source.Fiber
    EquivariantStructure G source.Fiber
  /-- The specified action on the original target bundle. -/
  targetAction : letI := modelTopology (EuclideanSpace ℂ (Fin target.rank)) target.Fiber
    EquivariantStructure G target.Fiber
  /-- Joint smoothness of that same source action. -/
  source_smooth : sourceAction.IsSmooth (n := n) (r := source.rank) 𝓘(ℝ, VG)
  /-- Joint smoothness of that same target action. -/
  target_smooth : targetAction.IsSmooth (n := n) (r := target.rank) 𝓘(ℝ, VG)
  /-- The original degree-zero homogeneous symbol. -/
  symbol : homogeneousGlobalSymbolSpace (n := n) (r := source.rank) (q := target.rank)
    source.Fiber target.Fiber 0
  /-- Off-zero ellipticity of precisely that symbol. -/
  elliptic : IsEllipticGlobalSymbol source.Fiber target.Fiber symbol.val
  /-- Off-zero equivariance for the specified source and target actions. -/
  equivariant : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
    equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) sourceAction targetAction g symbol.val x ξ =
      symbol.val x ξ

variable [CompactSpace M]

/-- The existing K class of these exact stored data, with the native cotangent action. -/
def EquivariantEllipticSymbolData.kClass
    (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G)) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) :=
  equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) a.sourceAction a.targetAction
    0 a.symbol a.elliptic a.equivariant

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The existing full representation-valued canonical index of these same stored data. -/
def EquivariantEllipticSymbolData.index
    (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G)) :
    RepresentationGrothendieckGroup G :=
  equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG) a.sourceAction a.targetAction
    a.source_smooth a.target_smooth a.symbol a.elliptic a.equivariant

end AtiyahSinger
