/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialParameter
public import AtiyahSinger.Geometry.TensorSectionOperator

/-!
# Joint smoothness of the actual horizontal tensor action

Public module ID: M0891.

The canonical finite tensor extension of a local PDO preserves joint
smoothness in every specified family of fiber dual coordinates. The
coefficient fibers may vary with the parameter. The action is the same
original input localization, Schwartz operator and output extension on the
base, tensored with the identity on the entire coefficient fiber.

This is the analytic local action used in original principal charts. No
parameter cutoff occurs in its definition. Assembly in the associated
atlas and commutation with the full vertical PDO remain separate steps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold
open scoped ContDiff Manifold TensorProduct

variable {n k r q : ℕ} {M : Type*} [TopologicalSpace M]
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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

local notation "Y" => EuclideanSpace ℝ (Fin k)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Vin" => EuclideanSpace ℂ (Fin r)
local notation "Vout" => EuclideanSpace ℂ (Fin q)

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original fiber dual coordinate of the horizontal tensor action is jointly smooth. -/
theorem PseudodifferentialPiece.contMDiffOn_tensorSectionOperator {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    {N : Type*} [TopologicalSpace N] [ChartedSpace Y N] [IsManifold 𝓘(ℝ, Y) ∞ N]
    (D : N → Type*) [∀ y, AddCommGroup (D y)] [∀ y, Module ℂ (D y)]
    [∀ y, FiniteDimensional ℂ (D y)] (U : Set N) (hU : IsOpen U)
    (w : ∀ y, dualTensorSections (D y) (smoothSections (n := n) (r := r) E))
    (l : ∀ y, D y →ₗ[ℂ] ℂ)
    (hw : ∀ (e : Trivialization Vin (π Vin E)), MemTrivializationAtlas e →
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vin) ∞
        (fun p : N × M ↦ (e ⟨p.2, TensorProduct.lid ℂ (E p.2)
          (TensorProduct.map (l p.1) LinearMap.id ((w p.1).val p.2))⟩).2)
        (U ×ˢ e.baseSet))
    (e : Trivialization Vout (π Vout F)) (he : MemTrivializationAtlas e) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vout) ∞
      (fun p : N × M ↦ (e ⟨p.2, TensorProduct.lid ℂ (F p.2)
        (TensorProduct.map (l p.1) LinearMap.id
          ((tensorSectionOperator (D p.1) (smoothSections (n := n) (r := r) E)
            (smoothSections (n := n) (r := q) F) L.toLinearMap (w p.1)).val p.2))⟩).2)
      (U ×ˢ e.baseSet) := by
  -- Contract in the specified fiber coordinate, retaining the original base sections.
  let u (y : N) : smoothSections (n := n) (r := r) E :=
    ⟨fun x ↦ TensorProduct.lid ℂ (E x)
      (TensorProduct.map (l y) LinearMap.id ((w y).val x)), (w y).property (l y)⟩
  intro p hp
  let c := chartAt Y p.1
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Y) ∞ N :=
    IsManifold.chart_mem_maximalAtlas p.1
  have hsource : p.1 ∈ c.source := mem_chart_source Y p.1
  let O := c.target ∩ c.symm ⁻¹' U
  have hO : IsOpen O := c.isOpen_inter_preimage_symm hU
  -- The actual inverse parameter chart reduces joint smoothness to the Euclidean theorem.
  have hv (d : Trivialization Vin (π Vin E)) (hd : MemTrivializationAtlas d) :
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vin) ∞
        (fun z : Y × M ↦ (d ⟨z.2, (u (c.symm z.1)).val z.2⟩).2)
        (O ×ˢ d.baseSet) := by
    have hpair : ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X))
        ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) ∞
        (fun z : Y × M ↦ (c.symm z.1, z.2)) (O ×ˢ d.baseSet) :=
      ((contMDiffOn_symm_of_mem_maximalAtlas hc).comp contMDiffOn_fst
        (fun z hz ↦ hz.1.1)).prodMk contMDiffOn_snd
    exact (hw d hd).comp hpair (fun z hz ↦ ⟨hz.1.2, hz.2⟩)
  have hlocal := L.contMDiffOn_apply_parameter_of_isOpen O hO
    (fun y ↦ u (c.symm y)) hv e he
  have hpoint : (c p.1, p.2) ∈ O ×ˢ e.baseSet := by
    refine ⟨⟨c.map_source hsource, ?_⟩, hp.2⟩
    change c.symm (c p.1) ∈ U
    rw [c.left_inv hsource]
    exact hp.1
  have hlocalAt := hlocal.contMDiffAt ((hO.prod e.open_baseSet).mem_nhds hpoint)
  have hchart : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X))
      ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) ∞
      (fun z : N × M ↦ (c z.1, z.2)) p :=
    ((contMDiffAt_of_mem_maximalAtlas hc hsource).comp p contMDiffAt_fst).prodMk
      contMDiffAt_snd
  -- Returning through the same chart cancels exactly; the tensor action is unchanged.
  apply ((hlocalAt.comp p hchart).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [continuous_fst.continuousAt (c.open_source.mem_nhds hsource)] with z hz
  dsimp only [Function.comp_apply]
  rw [c.left_inv hz]
  have h := congrFun (tensorSectionOperator_contract (D z.1)
    (smoothSections (n := n) (r := r) E) (smoothSections (n := n) (r := q) F)
    L.toLinearMap (w z.1) (l z.1)) z.2
  exact congrArg (fun v : F z.2 ↦ (e ⟨z.2, v⟩).2) h

end AtiyahSinger
