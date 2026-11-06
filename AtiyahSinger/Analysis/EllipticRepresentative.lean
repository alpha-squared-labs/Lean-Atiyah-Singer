/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ContinuousEllipticSmoothing
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Geometry.FixedRankSmoothModel
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.CotangentRepresentative
public import AtiyahSinger.Topology.EquivariantRankStrata

/-!
# Smooth homogeneous and elliptic operator representatives of cotangent K classes

Public module ID: M0454.

P01 and the realization step preceding A10: SG III.13 Lemma 13.3 and the paragraph
leading to (13.7), pp.245--246. Preconnectedness makes the source and target ranks
globally constant, as required by the current analysis interfaces. It allows the
empty base, handled separately. Smoothing the continuous bundle and cosphere
data is an explicit project supplement, not an assumption on the input K class.
Arbitrary real orders use the existing real homogeneous quantization interfaces.
No stable-equivalence invariance of the analytic index is asserted here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hC : CompactSpace M] [hSC : SecondCountableTopology M]
  [hP : PreconnectedSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  ComplexBundle.isFiniteRank_pullback

include hM hT hC hSC hP in
/-- A compact preconnected base admits a smooth elliptic representative of any real degree. -/
theorem exists_smooth_elliptic_representative_of_preconnected
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) (m : ℝ) :
    ∃ E F : SmoothFiniteComplexBundle (n := n) M,
      ∃ a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber m,
      ∃ hi : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val,
        homogeneousSymbolKClass m a hi = u := by
  classical
  -- Obtain the original continuous triple, including its exact zero control and ray law.
  obtain ⟨E, F, a, hzero, hhom, hclass⟩ := exists_homogeneous_cotangent_representative u
  obtain ⟨r, hr⟩ := (ComplexBundle.isLocallyConstant_finrank E.Fiber).exists_eq_const
  obtain ⟨q, hq⟩ := (ComplexBundle.isLocallyConstant_finrank F.Fiber).exists_eq_const
  have hrankE (x : M) : Module.finrank ℂ (E.Fiber x) = r := congrFun hr x
  have hrankF (x : M) : Module.finrank ℂ (F.Fiber x) = q := congrFun hq x
  -- Smooth the two bundles through specified continuous isomorphisms of the actual fibers.
  obtain ⟨E', _, he⟩ := ComplexBundle.exists_smooth_model_of_rank
    (n := n) (E := E.Fiber) r hrankE
  obtain ⟨F', _, hf⟩ := ComplexBundle.exists_smooth_model_of_rank
    (n := n) (E := F.Fiber) q hrankF
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := ComplexBundle.isFiniteRank_model (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := ComplexBundle.isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  obtain ⟨e⟩ := he
  obtain ⟨f⟩ := hf
  let eπ := e.pullback (cotangentProjection (n := n) (M := M))
  let fπ := f.pullback (cotangentProjection (n := n) (M := M))
  let b := a.congr eπ fπ
  have hbzero : b.control = cotangentZeroSet := hzero
  have hbhom (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ) (ht : 0 < t)
      (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ b.controlᶜ)
      (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ b.controlᶜ) :
      b.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
        b.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ := by
    apply LinearEquiv.ext
    intro v
    change f.linearEquiv x (a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩
      ((e.linearEquiv x).symm v)) =
        f.linearEquiv x (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩
          ((e.linearEquiv x).symm v))
    rw [hhom x ξ t ht hξ htξ]
    rfl
  -- The same conjugated boundary is smoothed on the cosphere, then extended with degree m.
  obtain ⟨c, hi, hc⟩ := exists_smooth_homogeneousSymbol_of_continuousTriple E' F' m b
    hbzero hbhom
  refine ⟨E', F', c, hi, ?_⟩
  exact hc.trans ((a.compactSupportClass_congr eπ fπ).trans hclass)

variable [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT hC hSC hP hB hμ in
/-- Every K class on a compact preconnected base is the displayed symbol class of a PDO. -/
theorem exists_elliptic_pseudodifferential_representative_of_preconnected
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) (m : ℝ) :
    ∃ E F : SmoothFiniteComplexBundle (n := n) M,
      ∃ R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber,
      ∃ a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber m,
      ∃ P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber μ m,
      ∃ hprincipal : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber m
        (R.regularizedSymbol m a.val a.property.1 a.property.2),
      ∃ hi : P.IsElliptic, P.symbolKClassOfHomogeneous R a hprincipal hi = u := by
  obtain ⟨E, F, a, ha, hclass⟩ :=
    exists_smooth_elliptic_representative_of_preconnected u m
  -- Retain one actual presentation for both regularization and quantization.
  obtain ⟨R⟩ := nonempty_quantizationPresentation (n := n) (r := E.rank) (q := F.rank)
    (E := E.Fiber) (F := F.Fiber)
  let P := R.quantizeHomogeneous R μ m a.val a.property.1 a.property.2
  have hp : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber m
      (R.regularizedSymbol m a.val a.property.1 a.property.2) :=
    R.principalSymbol_quantizeHomogeneous R μ m a.val a.property.1 a.property.2
  have hi : P.IsElliptic := (P.isElliptic_iff_homogeneous R a hp).mpr ha
  -- The displayed operator class uses exactly this homogeneous representative.
  exact ⟨E, F, R, a, P, hp, hi, (P.symbolKClassOfHomogeneous_eq R a hp hi).trans hclass⟩

end AtiyahSinger
