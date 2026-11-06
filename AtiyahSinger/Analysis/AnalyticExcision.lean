/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticIndexDiffeomorph
public import AtiyahSinger.Analysis.OpenExtensionIndex
public import AtiyahSinger.Analysis.PreconnectedExcision
public import AtiyahSinger.Analysis.RelativeEllipticRealization
public import AtiyahSinger.Analysis.RelativeSymbolRepresentative
public import AtiyahSinger.Geometry.RelativeExcisionData
public import AtiyahSinger.Topology.FiniteCotangentComponents
public import AtiyahSinger.Topology.OpenCotangentRestriction
public import AtiyahSinger.Topology.RelativeSymbolExtension

/-!
# Analytic excision for a source of finite CW homotopy type

Public module ID: M0077.

P02: SG III.13 Excision Property 13.4, pp.248--249. The two actual open
cotangent pushforwards have the same analytic index in their compact targets.
Finite topological type is expressed by an explicit finite CW homotopy model.
The source need not be compact or connected; the target indices are the existing
componentwise homomorphisms and may use unrelated positive smooth densities.

The proof assembles the same supported operator in both environments, then
uses the actual finite component decomposition. Arbitrary open sources without
the finite CW witness require
an additional compact-support localization argument, not included here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ} {O M N Y : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [hO : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [hTO : T2Space O] [hSO : SecondCountableTopology O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [TopologicalSpace Y] [hTY : T2Space Y]
  (C : Set Y) [hCW : Topology.CWComplex C] [hfin : Topology.CWComplex.Finite C]
  (hType : ContinuousMap.HomotopyEquiv O C)

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

include hO hTO hSO hTY hCW hfin hType

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1000000 in
-- The extended limit accommodates the original open source and its two compact analytic
-- environments.
/-- SG Excision Property 13.4: two compact environments give the same index on the open source. -/
theorem analyticIndexOfComponents_excision
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]
    (U : Opens M) (V : Opens N)
    (f : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (g : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V) :
    (analyticIndexOfComponents μ).comp (cotangentKZeroOpenEmbedding U f) =
      (analyticIndexOfComponents ν).comp (cotangentKZeroOpenEmbedding V g) := by
  classical
  -- The given finite model yields finitely many actual open source components.
  let : Finite (ConnectedComponents O) :=
    finite_connectedComponents_of_homotopyEquiv_finiteCW (n := n) C hType
  let : Fintype (ConnectedComponents O) := Fintype.ofFinite _
  apply AddMonoidHom.ext
  intro u
  have hsum := sum_cotangentOpenPushforward_components (n := n) u
  rw [← hsum]
  simp only [AddMonoidHom.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  -- Restrict the original homotopy equivalence and both actual cotangent embeddings.
  obtain ⟨D, hD, hDf, ⟨hComponent⟩⟩ :=
    exists_homotopyEquiv_finiteCW_manifoldComponent (n := n) C hType c
  let := hD
  let := hDf
  obtain ⟨W, fC, _, hmapf⟩ := exists_cotangentKZeroOpenEmbedding_restriction U f
    (manifoldComponent (n := n) c)
  obtain ⟨Z, gC, _, hmapg⟩ := exists_cotangentKZeroOpenEmbedding_restriction V g
    (manifoldComponent (n := n) c)
  -- Each summand uses one common relative representative and one supported source operator.
  -- Compact components, including zero-dimensional ones, use the clopen branch of that theorem.
  have hindex := analyticIndexOfComponents_excision_of_preconnected
    D hComponent μ ν W Z fC gC
  have hvalue := DFunLike.congr_fun hindex (cotangentKZeroComponents (n := n) u c)
  rw [hmapf, hmapg] at hvalue
  exact hvalue

end AtiyahSinger
