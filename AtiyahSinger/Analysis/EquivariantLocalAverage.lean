/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAmplitudeFamilies
public import AtiyahSinger.Analysis.EquivariantAveragingAssembly
public import AtiyahSinger.Analysis.EquivariantAveragingCover
public import AtiyahSinger.Analysis.EquivariantLocalizedRemainder
public import AtiyahSinger.Analysis.EquivariantLocalAveragePrincipalSymbol
public import AtiyahSinger.Analysis.PseudodifferentialIntegral

/-!
# Realize a weighted local conjugate from its fixed kernel splitting

Public module ID: M0533.

The same uniformly controlled amplitude family gives an actual native PDO
piece. Adding the weighted conjugate of the fixed original smooth kernel
recovers the specified local integral. All integrals remain in the original
finite-dimensional fibers and use the same positive base density.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set TopologicalSpace Topology
open scoped ContDiff Manifold SchwartzMap

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  {m : ℝ}

set_option maxHeartbeats 1200000 in
-- Actual local amplitude integration and the same fixed native kernel are assembled fiberwise.
omit [T2Space G] in
/-- Uniform amplitudes and an exact fixed-kernel splitting realize the weighted local average. -/
theorem PseudodifferentialPiece.exists_weighted_average_of_uniform_amplitudes
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (S : SmoothKernel (n := n) (r := r) (q := q) E F)
    (w : G → ℂ) (hw : Continuous w)
    (a : G → AmplitudeFunction n r q) (ha : ∀ g, IsAmplitude m (a g))
    (T : G → (𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))))
    (hT : ∀ g v z, T g v z = amplitudeApply (a g) v z)
    (hsupp : ∀ g, tsupport (Function.uncurry (a g)) ⊆ tsupport A.cutoff ×ˢ tsupport A.cutoff)
    (hmixed : ∀ i j k : ℕ, Continuous
      (fun p : G × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ amplitudeDerivative (a p.1) i j k
          p.2.1.1 p.2.1.2 p.2.2))
    (hjoint : ∀ l : ℕ, Continuous
      (fun p : G × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ l
          (fun z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
            EuclideanSpace ℝ (Fin n) ↦ a p.1 z.1.1 z.1.2 z.2) p.2))
    (hbound : ∀ i j k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ g x y ξ,
      ‖amplitudeDerivative (a g) i j k x y ξ‖ ≤ D * (1 + ‖ξ‖) ^ (m - (k : ℝ)))
    (hexact : ∀ g (u : smoothSections (n := n) (r := r) E) (x : M),
      (B.extend hc (T g (A.localize hc u))).val x =
        w g • ((σF.smoothSectionRepresentation IG hσF g)
          (L.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x -
        w g • ((σF.smoothSectionRepresentation IG hσF g)
          (S.toLinearMap μ ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (Q.toLinearMap u).val x =
          ∫ g, w g • ((σF.smoothSectionRepresentation IG hσF g)
            (L.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
            ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  obtain ⟨Q, hQ, _⟩ := L.exists_weighted_average_of_uniform_amplitudes_with_principalSymbol
    IG σE σF hσE hσF c hc A B hAB S w hw a ha T hT hsupp hmixed hjoint hbound hexact
  exact ⟨Q, hQ⟩

set_option maxHeartbeats 1500000 in

/-- Every chart-fitting piece has a neighborhood on which all supported continuous weights
admit the actual native pseudodifferential average. -/
theorem PseudodifferentialPiece.exists_local_weighted_average
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) (g₀ : G)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (hbase : (fun x : M ↦ g₀ • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
        c.source ∩ e.baseSet ∩ f.baseSet) :
    ∃ U : Set G, IsOpen U ∧ g₀ ∈ U ∧
      ∀ w : G → ℂ, Continuous w → tsupport w ⊆ U →
      ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m,
        ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
          (Q.toLinearMap u).val x =
            ∫ g, w g • ((σF.smoothSectionRepresentation IG hσF g)
              (L.toLinearMap ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
              ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  obtain ⟨U, hU, hg₀U, _, _, hweighted⟩ :=
    L.exists_local_weighted_average_with_principalSymbol
      (μ := μ) IG σE σF hσE hσF g₀ c hc e f hbase
  refine ⟨U, hU, hg₀U, ?_⟩
  intro w hw hwsupp
  obtain ⟨Q, hQ, _⟩ := hweighted w hw hwsupp
  exact ⟨Q, hQ⟩

end AtiyahSinger
