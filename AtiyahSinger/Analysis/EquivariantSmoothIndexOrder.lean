/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndexOrder
public import AtiyahSinger.Analysis.EquivariantSmoothSymbolIndex
public import AtiyahSinger.Geometry.InvariantCotangentMetric

/-!
# Full equivariant index of a homogeneous operator at arbitrary real order

Public module ID: M0576.

An actual elliptic equivariant PDO computes the original supported K index
with its smooth kernel and actual range quotient at every real order.
Invariant metrics and density are constructed on the same actions; density
transport preserves the original smooth section operator and principal class.
No auxiliary invariant metric, density or radial symbol is required as input.

Source: SG III.9 and III.13, with the actual density and order transports.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

section

/- The order comparison is universe-polymorphic in the group model and base.
The supported K model keeps its fiber types in Type; the second interface
specializes the same comparison to a Type-valued group model. -/
variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [MeasurableSpace G] [hGB : BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hMB : BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

include hDim hLie hGC hGT hGB hM hT hSC hC hMB hAction

variable {r q : ℕ} {E : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) 𝓘(ℝ, VG))
  (hσF : σF.IsSmooth (n := n) (r := q) 𝓘(ℝ, VG))

variable (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1000000 in
-- Keep the same actions and operator through density change and the all-order comparison.
/-- Every real-order homogeneous realization computes the original full smooth equivariant index. -/
theorem equivariantAnalyticIndexMap_eq_smooth_of_homogeneous_universe {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPg : P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2))
    (hi : IsEllipticGlobalSymbol E F a.val)
    (ha : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF γ a.val x ξ = a.val x ξ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    equivariantAnalyticIndexMap (VG := VG) (G := G)
        (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF m a hi ha) =
      P.smoothEquivariantAnalyticIndex 𝓘(ℝ, VG) σE σF hσE hσF hPg
        ((P.isElliptic_iff_homogeneous R a hp).mpr hi) := by
  -- Choose invariant auxiliary data on the original bundles and original action.
  obtain ⟨ν, hν, hνInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G 𝓘(ℝ, VG) (n := n) (M := M)
  let := hν
  obtain ⟨h, hh⟩ := exists_invariant_smoothHermitianMetric 𝓘(ℝ, VG) σE hσE
  obtain ⟨k, hk⟩ := exists_invariant_smoothHermitianMetric 𝓘(ℝ, VG) σF hσF
  obtain ⟨g, hg⟩ := exists_invariant_smoothCotangentMetric (G := G) (n := n) (M := M) 𝓘(ℝ, VG)
  have hlength (γ : G) (x : M) (ξ : CotangentFiber (n := n) x) :
      g.length (γ • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ)
            ⟨x, ξ⟩).snd = g.length x ξ :=
    congrArg Real.sqrt (hg γ x ξ ξ)
  -- The density transport is exactly the same section map, hence the same smooth index.
  let Q := P.changeMeasure ν
  have hQg : Q.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF := hPg
  have hq := (P.principalSymbol_changeMeasure ν).trans hp
  exact equivariantAnalyticIndexMap_homogeneous_universe σE σF hσE hσF
    ν h k hh hk hνInvariant Q hQg g hlength R a hq hi ha

end

variable {VG : Type} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [MeasurableSpace G] [hGB : BorelSpace G]
  {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hMB : BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

include hDim hLie hGC hGT hGB hM hT hSC hC hMB hAction

variable {r q : ℕ} {E : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) 𝓘(ℝ, VG))
  (hσF : σF.IsSmooth (n := n) (r := q) 𝓘(ℝ, VG))

variable (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 1000000 in
-- Keep the same actions and operator through density change and the all-order comparison.
/-- Every real-order homogeneous realization computes the original full smooth equivariant index. -/
theorem equivariantAnalyticIndexMap_eq_smooth_of_homogeneous {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPg : P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2))
    (hi : IsEllipticGlobalSymbol E F a.val)
    (ha : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF γ a.val x ξ = a.val x ξ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    equivariantAnalyticIndexMap (VG := VG) (G := G)
        (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF m a hi ha) =
      P.smoothEquivariantAnalyticIndex 𝓘(ℝ, VG) σE σF hσE hσF hPg
        ((P.isElliptic_iff_homogeneous R a hp).mpr hi) := by
  -- Retain the original universe-zero interface as the specialization of the same proof.
  exact equivariantAnalyticIndexMap_eq_smooth_of_homogeneous_universe
    σE σF hσE hσF μ P hPg R a hp hi ha

end AtiyahSinger
