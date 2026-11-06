/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousAnalyticIndex
public import AtiyahSinger.Analysis.SmoothEquivariantIndex

/-!
# The full symbol index from its original smooth realization

Public module ID: M0580.

The canonical homogeneous-symbol index is the kernel-minus-cokernel class of
any actual smooth equivariant elliptic realization, even when its auxiliary
density is not invariant. Transport that same section operator to one invariant
density, apply the established canonical and smooth-index comparisons, and
retain the unchanged finite smooth representations. This lets clopen pieces
use their actual restricted measures without making new averaging choices.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hLie : LieGroup IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [hGM : MeasurableSpace G] [hGB : BorelSpace G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)


/-- Any actual smooth realization computes the full homogeneous-symbol index. -/
theorem equivariantHomogeneousAnalyticIndex_eq_smooth
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 s.val s.property.1 s.property.2)) :
    equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs =
      P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP := by
  -- Only the density certificate changes; the section map and both actions stay fixed.
  obtain ⟨ν, hν, hνInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hν
  obtain ⟨h, hh⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, hk⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  let Q := P.changeMeasure ν
  have hQg : Q.IsEquivariant IG σE σF hσE hσF := hPg
  have hQ : Q.IsElliptic := (P.isElliptic_changeMeasure_iff ν).mpr hP
  have hpQ := (P.principalSymbol_changeMeasure ν).trans hp
  calc
    equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs =
        Q.equivariantAnalyticIndex IG σE σF hσE hσF h k hh hk hνInvariant hQg hQ :=
      equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF s hi hs
        ν hν h k hh hk hνInvariant R Q hQg hQ hpQ
    _ = Q.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hQg hQ :=
      Q.equivariantAnalyticIndex_eq_smoothEquivariantAnalyticIndex
        IG σE σF hσE hσF hQg hQ h k hh hk hνInvariant
    _ = P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP := rfl

end AtiyahSinger
