/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactSourceExcision
public import AtiyahSinger.Analysis.RelativeExcisionIndexRealization
public import AtiyahSinger.Analysis.RelativeSymbolRepresentative

/-!
# Analytic excision on a preconnected source

Public module ID: M0860.

For a source of finite CW homotopy type, one relative representative and
one finite correction family supply both compact environments. The exact
supported realizations have equal full
indices, and density independence recovers the prescribed ambient measures.
Compact sources are handled by clopen excision; noncompact sources have a
nonempty exterior, so their relative frames enforce equal bundle ranks.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {O M N Y : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [T2Space O] [SecondCountableTopology O] [PreconnectedSpace O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [TopologicalSpace Y] [T2Space Y]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_model isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
-- The same raw representative, compact support and source correction serve both environments.
/-- Excision holds for a preconnected source of finite CW homotopy type. -/
theorem analyticIndexOfComponents_excision_of_preconnected
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (hType : ContinuousMap.HomotopyEquiv O C)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]
    (U : Opens M) (V : Opens N)
    (f : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (g : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V) :
    (analyticIndexOfComponents μ).comp (cotangentKZeroOpenEmbedding U f) =
      (analyticIndexOfComponents ν).comp (cotangentKZeroOpenEmbedding V g) := by
  classical
  by_cases hcompact : IsCompact (Set.univ : Set O)
  · let : CompactSpace O := ⟨hcompact⟩
    exact analyticIndexOfComponents_excision_of_compactSpace μ ν U V f g
  · let : MeasurableSpace O := borel O
    let : BorelSpace O := ⟨rfl⟩
    apply AddMonoidHom.ext
    intro u
    obtain ⟨E, F, K, hK, τE, τF, hτE, hτF, c, hc, a, ha, haext, hτ, hu⟩ :=
      exists_smooth_relative_cotangent_representative C hType u
    -- A noncompact source has an exterior point; its original frame fixes the common rank.
    obtain ⟨x, hx⟩ : ∃ x : O, x ∉ K := by
      by_contra hn
      have hKall : K = Set.univ := Set.eq_univ_of_forall (by simpa using hn)
      exact hcompact (hKall ▸ hK)
    have hEF : E.rank = F.rank := by
      have hfib : Module.finrank ℂ (F.Fiber x) = F.rank := by
        simpa using VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x
      have hframe : Module.finrank ℂ (F.Fiber x) = E.rank := by
        simpa using (τF ⟨x, hx⟩).finrank_eq
      exact hframe.symm.trans hfib
    obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := E.rank) (E := E.Fiber)
    obtain ⟨k⟩ := nonempty_smoothHermitianMetric (n := n) (r := F.rank) (E := F.Fiber)
    obtain ⟨ν₀, hν₀⟩ := exists_smoothPositiveMeasure (n := n) (M := O)
    let : IsSmoothPositiveMeasure (n := n) ν₀ := hν₀
    obtain ⟨g₀⟩ := SmoothCotangentMetric.nonempty (n := n) (M := O)
    have haoutside (x : O) (hx : x ∉ K) (ξ : CotangentFiber (n := n) x) :
        a.val x ξ = c x := haext ⟨x, hx⟩ ξ
    -- Quantize once. Both environments will use these identical pieces and the same larger support.
    obtain ⟨b₀, _, hbrecover, d₀, T, hsymbol, L, hL, hKL, _, hPieces, hTsupport, _⟩ :=
      exists_relative_quantization_pieces E F a c hc K hK haoutside
        Set.univ isOpen_univ (Set.subset_univ _) g₀
    have hprincipal (x : O) (ξ : CotangentFiber (n := n) x) (hξ : 1 ≤ g₀.length x ξ) :
        (∑ j, (T j).globalSymbol).val x ξ + c x = a.val x ξ := by
      rw [hsymbol]
      exact hbrecover x ξ hξ
    let P₀ := smoothSectionMap (fun x ↦ (c x).toLinearMap) hc + ∑ j, (T j).toLinearMap
    have hP₀ (s : supportedSmoothSections (n := n) (r := E.rank) E.Fiber L) :
        P₀ s.val ∈ supportedSmoothSections (n := n) (r := F.rank) F.Fiber L := by
      intro x hx
      have hzero : ((∑ j, (T j).toLinearMap) s.val).val x = 0 := by
        by_contra hne
        exact hx (hTsupport.1 s.val (subset_closure hne))
      change c x (s.val.val x) + ((∑ j, (T j).toLinearMap) s.val).val x = 0
      rw [s.property x hx, map_zero, hzero, add_zero]
    let D : supportedSmoothSections (n := n) (r := E.rank) E.Fiber L →ₗ[ℂ]
        supportedSmoothSections (n := n) (r := F.rank) F.Fiber L :=
      (P₀.comp (Submodule.subtype _)).codRestrict _ hP₀
    have hD (s : supportedSmoothSections (n := n) (r := E.rank) E.Fiber L) :
        (D s).val = P₀ s.val := rfl
    -- Enlarge only the zero-section control; retain the original exterior boundary and K class.
    let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    obtain ⟨b, hbcontrol, hbboundary, hbclass⟩ := hu
    have hzeroL : IsCompact (cotangentZeroSection (n := n) '' L) :=
      hL.image continuous_cotangentZeroSection
    have hcontrol : b.control ⊆ cotangentZeroSection '' L := by
      rw [hbcontrol]
      exact Set.image_mono hKL
    let bL := b.enlarge (cotangentZeroSection '' L) hzeroL hcontrol
    have hbL : ∃ q : CompactSupportTriple
        ((cotangentProjection (n := n) (M := O) : _ → O) *ᵖ E.Fiber)
        ((cotangentProjection (n := n) (M := O) : _ → O) *ᵖ F.Fiber),
        q.control = cotangentZeroSection '' L ∧
        (∀ (z : (q.controlᶜ : Set (CotangentTotalSpace (n := n) (M := O))))
          (v : E.Fiber z.val.proj), q.boundary.linearEquiv z v = a.val z.val.proj z.val.snd v) ∧
        q.compactSupportClass = u := by
      refine ⟨bL, rfl, ?_, (b.compactSupportClass_enlarge _ _ _).trans hbclass⟩
      intro z v
      exact (b.enlarge_apply _ _ _ z v).trans
        (hbboundary ⟨z.val, fun hz ↦ z.property (hcontrol hz)⟩ v)
    obtain ⟨X⟩ := nonempty_relativeExcisionIndexModel E F hEF K L hK hL hKL h k ν₀ c hc a ha
      haoutside g₀ d₀ T hPieces hprincipal D hD u hbL U f τE τF hτE hτF hτ
    obtain ⟨Z⟩ := nonempty_relativeExcisionIndexModel E F hEF K L hK hL hKL h k ν₀ c hc a ha
      haoutside g₀ d₀ T hPieces hprincipal D hD u hbL V g τE τF hτE hτF hτ
    -- Full-kernel comparison uses that one source model; density independence restores μ and ν.
    change analyticIndexOfComponents μ (cotangentKZeroOpenEmbedding U f u) =
      analyticIndexOfComponents ν (cotangentKZeroOpenEmbedding V g u)
    calc
      _ = X.operator.toLinearMap.index := by
        rw [analyticIndexOfComponents_independent_measure μ X.measure]
        exact X.class_eq_index
      _ = Z.operator.toLinearMap.index :=
        RelativeExcisionIndexModel.index_eq E F h k ν₀ L hL D u U V f g X Z
      _ = _ := by
        rw [analyticIndexOfComponents_independent_measure ν Z.measure]
        exact Z.class_eq_index.symm

end AtiyahSinger
