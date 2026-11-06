/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialFamily

/-!
# Whole atlas PDO families over an original manifold parameter

Public module ID: M0290.

Joint smoothness of the same whole operator is local in an arbitrary smooth
parameter manifold. Original parameter charts reduce to the proved open
Euclidean result and are then inverted exactly near the chosen point.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set
open scoped Manifold ContDiff SchwartzMap Topology

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

local notation "Y" => EuclideanSpace ℝ (Fin k)
local notation "X" => EuclideanSpace ℝ (Fin n)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

variable [SecondCountableTopology M] [CompactSpace M]

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin k)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ N]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole original PDO preserves joint smoothness over any original parameter manifold. -/
theorem AtlasPseudodifferentialOperator.contMDiffOn_apply_manifold_parameter {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m) (U : Set N) (hU : IsOpen U)
    (u : N → A.smoothSections)
    (hu : ∀ i : A.Index,
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun p : N × M ↦ (A.chart i ⟨p.2, (u p.1).val p.2⟩).2)
        (U ×ˢ (A.chart i).baseSet)) (j : B.Index) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
      (fun p : N × M ↦ (B.chart j ⟨p.2, (P.toLinearMap (u p.1)).val p.2⟩).2)
      (U ×ˢ (B.chart j).baseSet) := by
  intro p hp
  let c := chartAt Y p.1
  have hcp : p.1 ∈ c.source := mem_chart_source Y p.1
  have hca := IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Y)) (n := ∞)
    (chart_mem_atlas Y p.1)
  let V := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.isOpen_inter_preimage_symm hU
  let v (y : Y) := u (c.symm y)
  -- Retain the given input family on the unchanged original parameter chart.
  have hv (i : A.Index) :
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun z : Y × M ↦ (A.chart i ⟨z.2, (v z.1).val z.2⟩).2)
        (V ×ˢ (A.chart i).baseSet) := by
    have hpair : ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X))
        ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) ∞
        (fun z : Y × M ↦ (c.symm z.1, z.2)) (V ×ˢ (A.chart i).baseSet) :=
      ((contMDiffOn_symm_of_mem_maximalAtlas hca).comp contMDiffOn_fst
        (fun _ hz ↦ hz.1.1)).prodMk contMDiffOn_snd
    exact (hu i).comp hpair (fun _ hz ↦ ⟨hz.1.2, hz.2⟩)
  have hresult := P.contMDiffOn_apply_parameter_of_isOpen A B V hV v hv j
  have hmem : (c p.1, p.2) ∈ V ×ˢ (B.chart j).baseSet := by
    refine ⟨⟨c.map_source hcp, ?_⟩, hp.2⟩
    change c.symm (c p.1) ∈ U
    rw [c.left_inv hcp]
    exact hp.1
  have hparam : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X))
      ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) ∞ (fun z : N × M ↦ (c z.1, z.2)) p :=
    ((contMDiffAt_of_mem_maximalAtlas hca hcp).comp p contMDiffAt_fst).prodMk
      contMDiffAt_snd
  have hlocal := (hresult.contMDiffAt
    ((hV.prod (B.chart j).open_baseSet).mem_nhds hmem)).comp p hparam
  -- Inverse-chart cancellation identifies the actual output near the original point.
  apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [continuous_fst.continuousAt (c.open_source.mem_nhds hcp)] with z hz
  change (B.chart j ⟨z.2, (P.toLinearMap (u z.1)).val z.2⟩).2 =
    (B.chart j ⟨z.2, (P.toLinearMap (u (c.symm (c z.1)))).val z.2⟩).2
  rw [c.left_inv hz]

end AtiyahSinger
