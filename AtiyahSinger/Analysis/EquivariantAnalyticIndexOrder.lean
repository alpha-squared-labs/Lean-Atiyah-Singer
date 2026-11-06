/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantOperatorOrderShift

/-!
# The full K index of an actual equivariant elliptic PDO of any order

Public module ID: M0463.

The same invariant radial order shift produces an actual order-zero operator.
Its original equivariant support class and smooth kernel-minus-cokernel
representation are unchanged. The existing order-zero evaluation and regularity
comparison therefore evaluate the original operator at arbitrary real order.
This uses existence of an equivariant invertible shift, without a spectral-power
identification and without assuming positive-order boundedness on L².

Source: SG III.9 and III.13, with the original support and smooth models retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

section

/- This order comparison allows arbitrary universes for the base and group carriers.
The support K model retains fiber types in Type; the specialized interface below uses
universe-zero base and group types. -/
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

variable (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (γ : G) (x : M) (u v : E x),
      h.pairing (γ • x) (σE.linearMap γ x u) (σE.linearMap γ x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (γ : G) (x : M) (u v : F x),
      k.pairing (γ • x) (σF.linearMap γ x u) (σF.linearMap γ x v) = k.pairing x u v)
  (hμInvariant : ∀ γ : G, Measure.map (fun x : M ↦ γ • x) μ = μ)

set_option maxHeartbeats 1000000 in
-- Keep the same invariant metrics, density, symbol class and actual smooth operator index.
include h k hInvariant kInvariant hμInvariant in
/-- The original K index evaluates an actual equivariant elliptic PDO at every real order. -/
theorem equivariantAnalyticIndexMap_homogeneous_universe {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPg : P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hg : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (γ • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ)
            ⟨x, ξ⟩).snd = g.length x ξ)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
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
        ((P.isElliptic_iff_homogeneous R a hP).mpr hi) := by
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  -- Choose one actual shift and keep its original principal representative and full smooth index.
  obtain ⟨Q, b, hb, hbg, hQg, hQ, _, _, _, hprincipal, _, hindex, hclass⟩ :=
    P.exists_equivariant_orderShift_universe 𝓘(ℝ, VG) σE σF hσE hσF h hInvariant hμInvariant
      hPg g hg R a hP hi ha 0
  rw [← hclass, equivariantAnalyticIndexMap_symbol σE σF hσE hσF b hb hbg]
  have heval := equivariantHomogeneousAnalyticIndex_eq 𝓘(ℝ, VG) σE σF hσE hσF
    b hb hbg μ hμ h k hInvariant kInvariant hμInvariant R Q hQg hQ hprincipal
  exact heval.trans ((Q.equivariantAnalyticIndex_eq_smoothEquivariantAnalyticIndex
    𝓘(ℝ, VG) σE σF hσE hσF hQg hQ h k hInvariant kInvariant hμInvariant).trans hindex)

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

variable (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (γ : G) (x : M) (u v : E x),
      h.pairing (γ • x) (σE.linearMap γ x u) (σE.linearMap γ x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (γ : G) (x : M) (u v : F x),
      k.pairing (γ • x) (σF.linearMap γ x u) (σF.linearMap γ x v) = k.pairing x u v)
  (hμInvariant : ∀ γ : G, Measure.map (fun x : M ↦ γ • x) μ = μ)

set_option maxHeartbeats 1000000 in
-- Keep the same invariant metrics, density, symbol class and actual smooth operator index.
include h k hInvariant kInvariant hμInvariant in
/-- The original K index evaluates an actual equivariant elliptic PDO at every real order. -/
theorem equivariantAnalyticIndexMap_homogeneous {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPg : P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hg : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (γ • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ)
            ⟨x, ξ⟩).snd = g.length x ξ)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
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
        ((P.isElliptic_iff_homogeneous R a hP).mpr hi) := by
  -- Retain the original universe-zero interface as the specialization of the same proof.
  exact equivariantAnalyticIndexMap_homogeneous_universe σE σF hσE hσF
    μ h k hInvariant kInvariant hμInvariant P hPg g hg R a hP hi ha

end AtiyahSinger
