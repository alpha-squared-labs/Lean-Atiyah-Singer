/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol
public import AtiyahSinger.Topology.CotangentRepresentative

import AtiyahSinger.Analysis.AtlasQuantization
import AtiyahSinger.Analysis.ContinuousEllipticSmoothing
import AtiyahSinger.Geometry.FixedRankSmoothModel
import AtiyahSinger.Topology.FixedRankCotangentRepresentative

/-!
# Elliptic representatives for compact cotangent K classes

Public module ID: M0240.

P01/A10: quantization of a supplied smooth homogeneous atlas symbol realizes
its radial regularization as the principal class, without an ellipticity
hypothesis. Every compact cotangent K class has an elliptic representative
of each real order and a PDO with that regularized principal class.

In positive dimension, common stabilization and smooth bundle models permit
smoothing the transported symbol while retaining its K class. In dimension
zero, the empty punctured cotangent space permits retaining the two finite
bundles and their difference directly. The statements allow locally varying
ranks and a disconnected base.

Sources: SG III.13 Lemma 13.3 and the construction preceding (13.7),
pp.245--246, with III.3.19. Continuous-to-smooth bundle and symbol
approximation are project supplements to the book's smooth setting.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hC : CompactSpace M] [hSC : SecondCountableTopology M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

include hM hT hC hSC

/-- Quantization realizes the exact homogeneous principal class on the specified atlases. -/
theorem exists_atlasPseudodifferentialOperator_of_homogeneousSymbol
    {E F : M → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)]
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (g : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a) :
    ∃ P : AtlasPseudodifferentialOperator A B m,
      P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
        (atlasRegularizedSymbol A B g m a hs hh) := by
  -- Quantize this specified regularization using one finite common frame presentation.
  obtain ⟨R⟩ := nonempty_atlasQuantizationPresentation A B
  let p := atlasRegularizedSymbol A B g m a hs hh
  exact ⟨R.quantize p, R.principalSymbol_quantize p⟩


set_option linter.unusedVariables false in
/-- Every original compact cotangent K class has a smooth atlas representative of any order. -/
theorem exists_smooth_atlas_elliptic_representative
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) (m : ℝ) :
    ∃ E F : FiniteBundle M,
      ∃ A : SmoothComplexBundleAtlas (n := n) E.Fiber,
      ∃ B : SmoothComplexBundleAtlas (n := n) F.Fiber,
      ∃ a : AtlasSymbolFunction (n := n) E.Fiber F.Fiber,
      ∃ hs : IsSmoothOffZeroAtlasSymbol A B a,
      ∃ hh : IsHomogeneousAtlasSymbol m a,
      ∃ hi : IsEllipticAtlasSymbol a,
        atlasSymbolKClass A B a hs hi = u := by
  classical
  by_cases hn : n = 0
  · -- The punctured space is empty: retain the original two bundles and their difference.
    obtain ⟨E, F, a, ha, _, hclass⟩ := exists_homogeneous_cotangent_representative u
    obtain ⟨A₀⟩ := nonempty_smoothComplexBundleAtlas (n := n) (E := E.Fiber)
    obtain ⟨B₀⟩ := nonempty_smoothComplexBundleAtlas (n := n) (E := F.Fiber)
    let A : SmoothComplexBundleAtlas (n := n) E.Fiber := {
      Index := ULift A₀.Index
      rank i := A₀.rank i.down
      chart i := A₀.chart i.down
      covers x := by
        obtain ⟨i, hi⟩ := A₀.covers x
        exact ⟨⟨i⟩, hi⟩
      linear i := A₀.linear i.down
      contMDiffOn_coordChange i j := A₀.contMDiffOn_coordChange i.down j.down }
    let B : SmoothComplexBundleAtlas (n := n) F.Fiber := {
      Index := ULift B₀.Index
      rank i := B₀.rank i.down
      chart i := B₀.chart i.down
      covers x := by
        obtain ⟨i, hi⟩ := B₀.covers x
        exact ⟨⟨i⟩, hi⟩
      linear i := B₀.linear i.down
      contMDiffOn_coordChange i j := B₀.contMDiffOn_coordChange i.down j.down }
    let b : AtlasSymbolFunction (n := n) E.Fiber F.Fiber := 0
    have hs : IsSmoothOffZeroAtlasSymbol A B b := by
      intro c hc i j
      have he : (atlasSymbolChartDomain A B c i j ×ˢ
          {ξ : EuclideanSpace ℝ (Fin n) | ξ ≠ 0}) = ∅ := by
        subst n
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hz.2 (Subsingleton.elim _ _)
      rw [he]
      exact contDiffOn_empty
    have hh : IsHomogeneousAtlasSymbol m b := by
      intro x ξ hξ
      exact (hξ (cotangentFiber_eq_zero_of_dim_zero hn x ξ)).elim
    have hi : IsEllipticAtlasSymbol b := by
      intro x ξ hξ
      exact (hξ (cotangentFiber_eq_zero_of_dim_zero hn x ξ)).elim
    refine ⟨E, F, A, B, b, hs, hh, hi, ?_⟩
    have htriple : atlasEllipticSymbolTriple A B b hs hi = a := by
      rcases a with ⟨K, hK, τ⟩
      dsimp only at ha
      subst K
      change CompactSupportTriple.mk cotangentZeroSet _ _ =
        CompactSupportTriple.mk cotangentZeroSet _ _
      congr 1
      apply Iso.ext
      intro z
      exact (z.property (cotangentFiber_eq_zero_of_dim_zero hn z.val.proj z.val.snd)).elim
    change (atlasEllipticSymbolTriple A B b hs hi).compactSupportClass = u
    rw [htriple]
    exact hclass
  · -- In positive dimension one common stabilization gives fixed global ranks.
    obtain ⟨E, F, r, hE, hF, a, ha, hhom, hclass⟩ :=
      exists_fixedRank_homogeneous_cotangent_representative (Nat.pos_of_ne_zero hn) u
    obtain ⟨V, _, ⟨e⟩⟩ := exists_smooth_model_of_rank (n := n) (E := E.Fiber) r hE
    obtain ⟨W, _, ⟨f⟩⟩ := exists_smooth_model_of_rank (n := n) (E := F.Fiber) r hF
    let := modelTopology (EuclideanSpace ℂ (Fin V.rank)) V.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin W.rank)) W.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin V.rank)) V.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin W.rank)) W.Fiber
    let πM := cotangentProjection (n := n) (M := M)
    let d := a.congr (e.pullback πM) (f.pullback πM)
    have hd : d.control = cotangentZeroSet := ha
    have hdRay (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ) (ht : 0 < t)
        (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ d.controlᶜ)
        (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ d.controlᶜ) :
        d.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
          d.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ := by
      apply LinearEquiv.ext
      intro v
      change f.linearEquiv x
        (a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ ((e.linearEquiv x).symm v)) =
        f.linearEquiv x
          (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ ((e.linearEquiv x).symm v))
      rw [hhom x ξ t ht hξ htξ]
      rfl
    -- Smooth the same transported boundary on the cosphere and extend with the requested degree.
    obtain ⟨b, hi, hb⟩ := exists_smooth_homogeneousSymbol_of_continuousTriple V W m d hd hdRay
    let A₁ := nativeSmoothComplexBundleAtlas (n := n) (r := V.rank) V.Fiber
    let B₁ := nativeSmoothComplexBundleAtlas (n := n) (r := W.rank) W.Fiber
    let A₀ := A₁.finiteSubatlas
    let B₀ := B₁.finiteSubatlas
    -- Finite subatlases and index lifts retain the selected native smooth charts.
    let A : SmoothComplexBundleAtlas (n := n) V.Fiber := {
      Index := ULift A₀.Index
      rank i := A₀.rank i.down
      chart i := A₀.chart i.down
      covers x := by
        obtain ⟨i, hi⟩ := A₀.covers x
        exact ⟨⟨i⟩, hi⟩
      linear i := A₀.linear i.down
      contMDiffOn_coordChange i j := A₀.contMDiffOn_coordChange i.down j.down }
    let B : SmoothComplexBundleAtlas (n := n) W.Fiber := {
      Index := ULift B₀.Index
      rank i := B₀.rank i.down
      chart i := B₀.chart i.down
      covers x := by
        obtain ⟨i, hi⟩ := B₀.covers x
        exact ⟨⟨i⟩, hi⟩
      linear i := B₀.linear i.down
      contMDiffOn_coordChange i j := B₀.contMDiffOn_coordChange i.down j.down }
    let b' := nativeAtlasSymbolFunction b.val
    have hprops := nativeAtlasSymbolFunction_homogeneous_properties m b.val
      b.property.1 b.property.2 hi
    have hs : IsSmoothOffZeroAtlasSymbol A B b' := by
      intro c hc i j
      exact hprops.1 c hc _ _
    refine ⟨FiniteBundle.ofFamily V.Fiber, FiniteBundle.ofFamily W.Fiber,
      A, B, b', hs, hprops.2.1, hprops.2.2, ?_⟩
    -- Changing chart indices changes no boundary vector; the original K class survives both steps.
    calc
      atlasSymbolKClass A B b' hs hprops.2.2 =
          atlasSymbolKClass A₁ B₁ b' hprops.1 hprops.2.2 := rfl
      _ = homogeneousSymbolKClass m b hi :=
        atlasSymbolKClass_native m b.val b.property.1 b.property.2 hi
      _ = d.compactSupportClass := hb
      _ = a.compactSupportClass := a.compactSupportClass_congr _ _
      _ = u := hclass

/-- Every cotangent K class has a smooth elliptic symbol with a PDO realization. -/
theorem exists_atlas_elliptic_pseudodifferential_representative
    (g : SmoothCotangentMetric (n := n) (M := M))
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) (m : ℝ) :
    ∃ E F : FiniteBundle M,
      ∃ A : SmoothComplexBundleAtlas (n := n) E.Fiber,
      ∃ B : SmoothComplexBundleAtlas (n := n) F.Fiber,
      ∃ a : AtlasSymbolFunction (n := n) E.Fiber F.Fiber,
      ∃ hs : IsSmoothOffZeroAtlasSymbol A B a,
      ∃ hh : IsHomogeneousAtlasSymbol m a,
      ∃ hi : IsEllipticAtlasSymbol a,
      ∃ P : AtlasPseudodifferentialOperator A B m,
        P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
          (atlasRegularizedSymbol A B g m a hs hh) ∧
        atlasSymbolKClass A B a hs hi = u := by
  -- Keep the representative and its precise fiber maps in the quantization witness.
  obtain ⟨E, F, A, B, a, hs, hh, hi, hclass⟩ :=
    exists_smooth_atlas_elliptic_representative u m
  obtain ⟨P, hP⟩ := exists_atlasPseudodifferentialOperator_of_homogeneousSymbol A B g m a hs hh
  exact ⟨E, F, A, B, a, hs, hh, hi, P, hP, hclass⟩

end AtiyahSinger
