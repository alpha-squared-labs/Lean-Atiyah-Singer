/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndex

/-!
# Evaluation of the original equivariant K index on an actual elliptic operator

Public module ID: M0461.

The full analytic-index homomorphism evaluates the original equivariant class
of a displayed homogeneous principal symbol to the full index of the supplied
equivariant elliptic PDO. The original bundles, actions, measure, metrics,
regularization and operator all remain specified. The K class uses the same
symbol, rather than a separately chosen representative after forgetting G.

Sources: SG III.9 Definition 9.3 and Corollary 9.6, and the ordinary analytic
index construction in III.13 (13.7)--(13.8), pp.246--247. The exact equivariant
K-map evaluation combines the canonical symbol evaluation with the
partition-independent map, retaining the same supplied operator throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) 𝓘(ℝ, VG))
  (hσF : σF.IsSmooth (n := n) (r := q) 𝓘(ℝ, VG))

/-- The original K-index value is the full index of this actual elliptic realization. -/
theorem PseudodifferentialOperator.equivariantAnalyticIndexMap_symbolKClass
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF g s.val x ξ = s.val x ξ)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (g : G) (x : M) (u v : E x),
        h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
    (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (g : G) (x : M) (u v : F x),
        k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
    (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (hPg : P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF) (hP : P.IsElliptic)
    (hprincipal : P.principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 s.val s.property.1 s.property.2)) :
    equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M)
        (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF 0 s hi hs) =
      P.equivariantAnalyticIndex 𝓘(ℝ, VG) σE σF hσE hσF
        h k hInvariant kInvariant hμInvariant hPg hP := by
  -- Evaluate the exact original symbol class, with the native cotangent action.
  have hsymbol := equivariantAnalyticIndexMap_symbol σE σF hσE hσF s hi hs
  -- The canonical value is computed by this same realization and all its supplied data.
  have hoperator := equivariantHomogeneousAnalyticIndex_eq 𝓘(ℝ, VG)
    σE σF hσE hσF s hi hs μ inferInstance h k hInvariant kInvariant hμInvariant
    R P hPg hP hprincipal
  exact hsymbol.trans hoperator

end AtiyahSinger
