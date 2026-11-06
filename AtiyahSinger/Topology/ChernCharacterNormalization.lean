/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTrivial
public import AtiyahSinger.Topology.GlobalChernLocalComparison
public import AtiyahSinger.Topology.RelativeSingularCohomologyVanishing
public import AtiyahSinger.Topology.SingularHomologyContraction
public import AtiyahSinger.Topology.VariableRankChernOperations

/-!
# Rank and trivial-line normalization of the original global Chern character

Public module ID: M1607.

The zeroth component recovers the rank on a bundle of constant rank. The trivial
line has unit zeroth component and vanishing higher components, by its actual
pullback from a point. These formulas supply the unit calculation for the
geometric K-theory character, retaining arbitrary fiber universes and metrics.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u v

variable {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original degree-zero character of a constant-rank bundle is its rank times the unit. -/
theorem globalChernCharacterComponent_zero_of_finrank
    (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) :
    globalChernCharacterComponent E h 0 = (r : ℚ) • singularCohomologyOne ℚ X := by
  -- The fixed-rank presentation is the specified model of the original family and metric.
  let M := CohomologyModel E
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  let hM := cohomologyModelMetric E h
  have hMrank (x : X) : Module.finrank ℂ (M x) = r :=
    (cohomologyModelLinearEquiv E x).finrank_eq.trans (hr x)
  let e : Iso M (((ContinuousMap.id X : C(X, X)) : X → X) *ᵖ E) :=
    (cohomologyModelIso E).trans (pullbackIdIso (E := E)).symm
  have hc := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    E h (ContinuousMap.id X) M hM r hMrank e 0
  have hid : singularCohomologyPullback ℚ (ContinuousMap.id X) 0 =
      𝟙 (singularCohomology ℚ X 0) := by
    exact (singularCohomologyFunctor ℚ 0).map_id _
  rw [hid, ModuleCat.id_apply] at hc
  rw [hc]
  let : ∀ x, NormedAddCommGroup (M x) := hM.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (M x) := hM.fiberInnerProductSpace
  let := nativeModelTopology M (EuclideanSpace ℂ (Fin r))
  let := hM.nativeFiberBundle r hMrank
  let := hM.nativeVectorBundle r hMrank
  exact chernCharacterComponent_zero r M (hM.nativeModelMetric r)

attribute [local instance] trivialTopology isFiniteRank_trivial

/-- The original trivial line has unit zeroth component and zero positive components. -/
theorem globalChernCharacterComponent_trivial_line
    (h : ContinuousHermitianMetric (Bundle.Trivial X (Fin 1 → ℂ))) (k : ℕ) :
    globalChernCharacterComponent (Bundle.Trivial X (Fin 1 → ℂ)) h k =
      singularCohomologyDegreeTwoPow ℚ X (0 : singularCohomology ℚ X 2) k := by
  classical
  cases k with
  | zero =>
    -- The rank computation uses the actual one-dimensional coordinate fiber.
    have hr (x : X) : Module.finrank ℂ (Bundle.Trivial X (Fin 1 → ℂ) x) = 1 := by
      simp [Bundle.Trivial]
    simpa [singularCohomologyDegreeTwoPow] using
      globalChernCharacterComponent_zero_of_finrank _ h 1 hr
  | succ k =>
    -- The same trivial line is pulled back from a point, where positive cohomology vanishes.
    let P := PUnit.{u + 1}
    let E := Bundle.Trivial P (Fin 1 → ℂ)
    let hP := (nonempty_continuousHermitianMetric E).some
    let f : C(X, P) := ContinuousMap.const _ PUnit.unit
    have hn : 0 < 2 * (k + 1) := by omega
    let := subsingleton_singularHomology_of_subsingleton ℚ P (2 * (k + 1)) hn
    let : Subsingleton (singularCohomology ℚ P (2 * (k + 1))) :=
      subsingleton_singularCochainDualHomology_of_subsingleton ℚ
        (singularChains ℚ P) (2 * (k + 1))
    have hpoint : globalChernCharacterComponent E hP (k + 1) = 0 :=
      Subsingleton.elim _ _
    rw [globalChernCharacterComponent_pullback E hP f
      (Bundle.Trivial X (Fin 1 → ℂ)) h (pullbackTrivialIso f 1).symm,
      hpoint, map_zero]
    simp [singularCohomologyDegreeTwoPow]

end AtiyahSinger.ComplexBundle
