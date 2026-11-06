/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClopenIndexDescent
public import AtiyahSinger.Analysis.EquivariantPiecewiseSymbol
public import AtiyahSinger.Analysis.EquivariantSymbolKIndexInvariance

/-!
# The full analytic-index homomorphism on original equivariant cotangent K theory

Public module ID: M0458.

The original equivariant compact-support K group of a compact smooth manifold
has a unique additive analytic index with values in the full representation
Grothendieck group. Its defining evaluation uses any finite invariant clopen
partition and the original smooth homogeneous symbol representatives on its
pieces. The two model ranks may depend independently on the piece. Existence,
additivity and independence of this partition are conclusions, not data in an
assumed index service or a newly defined quotient.

Sources: SG III.13 (13.7)--(13.8), printed pp.246--247, gives ordinary analytic
index descent; SG III.9, Definition 9.3 and Proposition 9.4, pp.212--213, gives
the full equivariant Fredholm index and its compact-perturbation invariance.
The original equivariant compact-support presentation is ASI I Section 2.
This finite invariant clopen assembly of the full equivariant index is a
project supplement; no exact independent source has been identified.
The source coverage of the stable-germ and continuous-homotopy comparisons,
bundle smoothing and uniform lower-order averaging also remains unresolved.

The standard finite-dimensional Lie-group model is retained explicitly from
the equivariant representative and K-relation comparison theorems. No fixed
global bundle rank, connectedness, invariant connected-component assumption,
positive dimension, or nonempty-piece condition is imposed. In particular,
dimension zero still permits unequal source and target ranks. The proof retains
the actual construction, common refinements, and comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff BigOperators

set_option maxSynthPendingDepth 30

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

/-- A unique additive full index evaluates every original invariant clopen symbol family. -/
theorem existsUnique_equivariantAnalyticIndexMap :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∃! I : EquivariantSupportTripleKZero G
        (CotangentTotalSpace (n := n) (M := M)) →+ RepresentationGrothendieckGroup G,
      ∀ (k : ℕ) (U : Fin k → Opens M)
        (hclosed : ∀ i, IsClosed (U i : Set M))
        (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
        (hcover : (⋃ i, (U i : Set M)) = Set.univ)
        (actions : ∀ i, MulAction G (U i)),
        letI := actions
        ∀ continuousActions : ∀ i, ContinuousSMul G (U i),
          letI := continuousActions
          ∀ smoothActions : ∀ i,
            ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (U i),
            letI := smoothActions
            ∀ (heq : ∀ (i : Fin k) (g : G) (x : U i),
              ((g • x : U i) : M) = g • (x : M))
              (compactPieces : ∀ i, CompactSpace (U i)),
              letI := compactPieces
              letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
                fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) 𝓘(ℝ, VG)
              letI : ∀ i, ContMDiffSMul 𝓘(ℝ, VG)
                  (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
                  (CotangentTotalSpace (n := n) (M := U i)) :=
                fun i ↦ contMDiffSMul_smoothCotangent
                  (n := n) (G := G) (M := U i) 𝓘(ℝ, VG)
              letI : ∀ i, ContinuousSMul G
                  (CotangentTotalSpace (n := n) (M := U i)) :=
                fun _i ↦ ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
                  (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
              ∀ (E F : ∀ i, SmoothFiniteComplexBundle (n := n) (U i))
                (σE : ∀ i,
                  letI := modelTopology
                    (EuclideanSpace ℂ (Fin (E i).rank)) (E i).Fiber
                  EquivariantStructure G (E i).Fiber)
                (σF : ∀ i,
                  letI := modelTopology
                    (EuclideanSpace ℂ (Fin (F i).rank)) (F i).Fiber
                  EquivariantStructure G (F i).Fiber)
                (hσE : ∀ i, (σE i).IsSmooth (n := n) (r := (E i).rank) 𝓘(ℝ, VG))
                (hσF : ∀ i, (σF i).IsSmooth (n := n) (r := (F i).rank) 𝓘(ℝ, VG))
                (s : ∀ i, homogeneousGlobalSymbolSpace
                  (n := n) (r := (E i).rank) (q := (F i).rank) (E i).Fiber (F i).Fiber 0)
                (hi : ∀ i, IsEllipticGlobalSymbol (E i).Fiber (F i).Fiber (s i).val)
                (hs : ∀ (i : Fin k) (g : G) (x : U i)
                  (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
                    equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG)
                      (σE i) (σF i) g (s i).val x ξ = (s i).val x ξ),
                I ((equivariantCotangentClopenEquiv
                  (n := n) (G := G) 𝓘(ℝ, VG) U hclosed heq hdisjoint hcover).symm
                    (fun i ↦ equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG)
                      (σE i) (σF i) 0 (s i) (hi i) (hs i))) =
                  ∑ i, equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG)
                    (σE i) (σF i) (hσE i) (hσF i) (s i) (hi i) (hs i) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  obtain ⟨I, hI, hunique⟩ :=
    existsUnique_equivariantClopenIndex (n := n) (M := M) (VG := VG) (G := G)
  refine ⟨I, ?_, ?_⟩
  · -- Package the supplied family without changing any piece, action, symbol or rank.
    dsimp only
    intro k U hclosed hdisjoint hcover actions continuousActions smoothActions heq
      compactPieces E F σE σF hσE hσF s hi hs
    let := actions
    let := continuousActions
    let := smoothActions
    let := compactPieces
    have hinvariant (i : Fin k) (g : G) (x : M) : g • x ∈ U i ↔ x ∈ U i := by
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
      isClosed := hclosed
      disjoint := hdisjoint
      cover := hcover
      invariant := hinvariant
      mulAction := actions
      equivariant := heq }
    let b : P.Symbols (n := n) (VG := VG) := fun i ↦ {
      source := E i
      target := F i
      sourceAction := σE i
      targetAction := σF i
      source_smooth := hσE i
      target_smooth := hσF i
      symbol := s i
      elliptic := hi i
      equivariant := hs i }
    exact hI ⟨P, b⟩
  · -- Conversely every complete family is an instance of this original universal property.
    intro J hJ
    apply hunique
    intro b
    let P := b.partition
    let := P.mulAction
    let := P.continuousSMul
    let := P.contMDiffSMul (n := n) (VG := VG)
    let := P.compactSpace
    exact hJ P.size P.piece P.isClosed P.disjoint P.cover P.mulAction
      P.continuousSMul (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
      (fun i ↦ (b.symbols i).source) (fun i ↦ (b.symbols i).target)
      (fun i ↦ (b.symbols i).sourceAction) (fun i ↦ (b.symbols i).targetAction)
      (fun i ↦ (b.symbols i).source_smooth) (fun i ↦ (b.symbols i).target_smooth)
      (fun i ↦ (b.symbols i).symbol) (fun i ↦ (b.symbols i).elliptic)
      (fun i ↦ (b.symbols i).equivariant)

/-- The full additive analytic index on the original equivariant cotangent support K group. -/
def equivariantAnalyticIndexMap :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →+
      RepresentationGrothendieckGroup G :=
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  (existsUnique_equivariantAnalyticIndexMap (n := n) (M := M)
    (VG := VG) (G := G)).exists.choose

/-- The full index of any original finite invariant clopen symbol family is its local sum. -/
theorem equivariantAnalyticIndexMap_clopen :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      ∀ (k : ℕ) (U : Fin k → Opens M)
        (hclosed : ∀ i, IsClosed (U i : Set M))
        (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
        (hcover : (⋃ i, (U i : Set M)) = Set.univ)
        (actions : ∀ i, MulAction G (U i)),
        letI := actions
        ∀ continuousActions : ∀ i, ContinuousSMul G (U i),
          letI := continuousActions
          ∀ smoothActions : ∀ i,
            ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (U i),
            letI := smoothActions
            ∀ (heq : ∀ (i : Fin k) (g : G) (x : U i),
              ((g • x : U i) : M) = g • (x : M))
              (compactPieces : ∀ i, CompactSpace (U i)),
              letI := compactPieces
              letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
                fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) 𝓘(ℝ, VG)
              letI : ∀ i, ContMDiffSMul 𝓘(ℝ, VG)
                  (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
                  (CotangentTotalSpace (n := n) (M := U i)) :=
                fun i ↦ contMDiffSMul_smoothCotangent
                  (n := n) (G := G) (M := U i) 𝓘(ℝ, VG)
              letI : ∀ i, ContinuousSMul G
                  (CotangentTotalSpace (n := n) (M := U i)) :=
                fun _i ↦ ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
                  (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
              ∀ (E F : ∀ i, SmoothFiniteComplexBundle (n := n) (U i))
                (σE : ∀ i,
                  letI := modelTopology
                    (EuclideanSpace ℂ (Fin (E i).rank)) (E i).Fiber
                  EquivariantStructure G (E i).Fiber)
                (σF : ∀ i,
                  letI := modelTopology
                    (EuclideanSpace ℂ (Fin (F i).rank)) (F i).Fiber
                  EquivariantStructure G (F i).Fiber)
                (hσE : ∀ i, (σE i).IsSmooth (n := n) (r := (E i).rank) 𝓘(ℝ, VG))
                (hσF : ∀ i, (σF i).IsSmooth (n := n) (r := (F i).rank) 𝓘(ℝ, VG))
                (s : ∀ i, homogeneousGlobalSymbolSpace
                  (n := n) (r := (E i).rank) (q := (F i).rank) (E i).Fiber (F i).Fiber 0)
                (hi : ∀ i, IsEllipticGlobalSymbol (E i).Fiber (F i).Fiber (s i).val)
                (hs : ∀ (i : Fin k) (g : G) (x : U i)
                  (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
                    equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG)
                      (σE i) (σF i) g (s i).val x ξ = (s i).val x ξ),
                equivariantAnalyticIndexMap (VG := VG) (G := G) ((equivariantCotangentClopenEquiv
                  (n := n) (G := G) 𝓘(ℝ, VG) U hclosed heq hdisjoint hcover).symm
                    (fun i ↦ equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG)
                      (σE i) (σF i) 0 (s i) (hi i) (hs i))) =
                  ∑ i, equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG)
                    (σE i) (σF i) (hσE i) (hσF i) (s i) (hi i) (hs i) := by
  -- Use precisely the existence witness selected by the original map definition.
  exact (existsUnique_equivariantAnalyticIndexMap (n := n) (M := M)
    (VG := VG) (G := G)).exists.choose_spec

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

/-- The full K-theory index evaluates the original global homogeneous elliptic symbol. -/
theorem equivariantAnalyticIndexMap_symbol
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF g s.val x ξ = s.val x ξ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    equivariantAnalyticIndexMap (VG := VG) (G := G)
        (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF 0 s hi hs) =
      equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG) σE σF hσE hσF s hi hs := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let A : SmoothFiniteComplexBundle (n := n) M := { rank := r, Fiber := E }
  let B : SmoothFiniteComplexBundle (n := n) M := { rank := q, Fiber := F }
  let a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G) := {
    source := A
    target := B
    sourceAction := σE
    targetAction := σF
    source_smooth := hσE
    target_smooth := hσF
    symbol := s
    elliptic := hi
    equivariant := hs }
  obtain ⟨b, hb⟩ := exists_equivariantClopenSymbolFamily
    (n := n) (M := M) (VG := VG) a.kClass
  let P := b.partition
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (n := n) (VG := VG)
  let := P.compactSpace
  let Φ := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) P.piece P.isClosed
    P.equivariant P.disjoint P.cover
  have hclasses (i : Fin P.size) : (b.symbols i).kClass =
      equivariantCotangentClopenRestrict 𝓘(ℝ, VG) P.piece P.isClosed P.equivariant a.kClass i := by
    rw [← hb]
    change (b.symbols i).kClass = Φ (Φ.symm (fun j ↦ (b.symbols j).kClass)) i
    rw [Φ.apply_symm_apply]
  -- Finite clopen additivity compares this global symbol with those exact same-class pieces.
  have hsum := a.index_eq_sum_of_clopen P.piece P.isClosed P.disjoint P.cover P.equivariant
    b.symbols hclasses
  have heval := equivariantAnalyticIndexMap_clopen (n := n) (M := M) (VG := VG) (G := G)
    P.size P.piece P.isClosed P.disjoint P.cover P.mulAction P.continuousSMul
    (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
    (fun i ↦ (b.symbols i).source) (fun i ↦ (b.symbols i).target)
    (fun i ↦ (b.symbols i).sourceAction) (fun i ↦ (b.symbols i).targetAction)
    (fun i ↦ (b.symbols i).source_smooth) (fun i ↦ (b.symbols i).target_smooth)
    (fun i ↦ (b.symbols i).symbol) (fun i ↦ (b.symbols i).elliptic)
    (fun i ↦ (b.symbols i).equivariant)
  change equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) a.kClass = a.index
  change equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) b.kClass = b.index at heval
  rw [← hb]
  exact heval.trans hsum.symm

end AtiyahSinger
