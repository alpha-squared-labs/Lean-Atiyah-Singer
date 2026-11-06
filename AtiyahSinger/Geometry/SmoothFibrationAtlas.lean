/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Topology.FiberBundle.Trivialization

-- The global submersion predicate has no exposed body or public introduction lemma.
import all Mathlib.Geometry.Manifold.Submersion

/-!
# Smooth atlases from compatible local products

Public module ID: M1396.

Smooth transitions between actual local product trivializations determine a
smooth atlas on the existing total topology. The original projection is a
submersion, and all the supplied trivializations and their inverses are smooth.
The final model is identified with the product model by a specified continuous
linear equivalence. No separation or countability hypothesis is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff Topology

variable {EB EF G : Type}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EF] [NormedSpace ℝ EF]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {B F X : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace X]
  [ChartedSpace EB B] [ChartedSpace EF F]
  [IsManifold 𝓘(ℝ, EB) ∞ B] [IsManifold 𝓘(ℝ, EF) ∞ F]

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible smooth local products give the original projection its smooth fibration atlas. -/
theorem exists_smoothFibrationAtlas {ι : Type*} (p : X → B)
    (e : ι → Trivialization F p) (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (htransition : ∀ i j,
      ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, EF)) (𝓘(ℝ, EB).prod 𝓘(ℝ, EF)) ∞
        ((e i).toOpenPartialHomeomorph.symm.trans (e j).toOpenPartialHomeomorph)
        ((e i).toOpenPartialHomeomorph.symm.trans (e j).toOpenPartialHomeomorph).source)
    (g : (EB × EF) ≃L[ℝ] G) :
    ∃ C : ChartedSpace G X, letI := C
      IsManifold 𝓘(ℝ, G) ∞ X ∧ ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, EB) ∞ p ∧
        Manifold.IsSubmersion 𝓘(ℝ, G) 𝓘(ℝ, EB) ∞ p ∧
          ∀ i, ContMDiffOn 𝓘(ℝ, G) (𝓘(ℝ, EB).prod 𝓘(ℝ, EF)) ∞ (e i) (e i).source ∧
            ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, EF)) 𝓘(ℝ, G) ∞
              (e i).toOpenPartialHomeomorph.symm (e i).target := by
  classical
  let H := ModelProd EB EF
  let J := 𝓘(ℝ, EB).prod 𝓘(ℝ, EF)
  have hIJ : J = 𝓘(ℝ, EB × EF) := modelWithCornersSelf_prod.symm
  let Y := B × F
  let K := ι × {φ : OpenPartialHomeomorph Y H // φ ∈ atlas H Y}
  let c (k : K) : OpenPartialHomeomorph X G :=
    ((e k.1).toOpenPartialHomeomorph.trans k.2.val).trans g.toHomeomorph.toOpenPartialHomeomorph
  choose index hindex using hcover
  let center (x : X) : K :=
    ⟨index x, chartAt H (e (index x) x), chart_mem_atlas H (e (index x) x)⟩
  have hcenter (x : X) : x ∈ (c (center x)).source := by
    exact ⟨⟨hindex x, mem_chart_source H (e (index x) x)⟩, mem_univ _⟩
  let C : ChartedSpace G X :=
    { atlas := range c
      chartAt := fun x ↦ c (center x)
      mem_chart_source := hcenter
      chart_mem_atlas := fun x ↦ ⟨center x, rfl⟩ }
  let := C
  -- Every total chart change is the same smooth product transition in base/fiber coordinates.
  have hm : IsManifold 𝓘(ℝ, G) ∞ X := by
    apply isManifold_of_contDiffOn
    rintro _ _ ⟨k, rfl⟩ ⟨l, rfl⟩
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, preimage_id, range_id, inter_univ]
    intro z hz
    have ht := (htransition k.1 l.1).contMDiffAt
      (((e k.1).toOpenPartialHomeomorph.symm.trans
        (e l.1).toOpenPartialHomeomorph).open_source.mem_nhds
          ⟨hz.1.2.2, hz.2.1.1⟩)
    have hφ := contMDiffAt_symm_of_mem_maximalAtlas (I := J) (n := ∞)
      (IsManifold.subset_maximalAtlas k.2.property) hz.1.2.1
    have hψ := contMDiffAt_of_mem_maximalAtlas (I := J) (n := ∞)
      (IsManifold.subset_maximalAtlas l.2.property) hz.2.1.2
    change ContMDiffAt J J ∞ _ _ at ht
    rw [hIJ] at ht hφ hψ
    have hs := g.contDiff.contMDiff.contMDiffAt.comp z
      (hψ.comp z (ht.comp z (hφ.comp z g.symm.contDiff.contMDiff.contMDiffAt)))
    simpa only [c, Function.comp_apply, mfld_simps, Function.comp_assoc,
      ContinuousLinearEquiv.coe_toHomeomorph] using hs.contDiffAt.contDiffWithinAt
  let := hm
  have hmem (k : K) : c k ∈ IsManifold.maximalAtlas 𝓘(ℝ, G) ∞ X :=
    IsManifold.subset_maximalAtlas ⟨k, rfl⟩
  -- Recover each supplied local product from one of its coordinate charts.
  have hlocal (i : ι) :
      ContMDiffOn 𝓘(ℝ, G) J ∞ (e i) (e i).source ∧
        ContMDiffOn J 𝓘(ℝ, G) ∞
          (e i).toOpenPartialHomeomorph.symm (e i).target := by
    constructor
    · intro x hx
      rw [hIJ]
      let φ := chartAt H (e i x)
      let k : K := ⟨i, φ, chart_mem_atlas H (e i x)⟩
      have hxC : x ∈ (c k).source := ⟨⟨hx, mem_chart_source H (e i x)⟩, mem_univ _⟩
      have hd := contMDiffAt_of_mem_maximalAtlas (hmem k) hxC
      have hinv := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := J) (n := ∞) (e i x))
        (φ.map_source (mem_chart_source H (e i x)))
      rw [hIJ] at hinv
      have hcoord : (g.symm ∘ c k) x = φ (e i x) := by
        change g.symm (g (φ (e i x))) = _
        exact g.symm_apply_apply _
      rw [← hcoord] at hinv
      have hs := hinv.comp x (g.symm.contDiff.contMDiff.contMDiffAt.comp x hd)
      apply hs.contMDiffWithinAt.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds ((c k).open_source.mem_nhds hxC)] with y _ hy
        change e i y = φ.symm (g.symm (g (φ (e i y))))
        rw [g.symm_apply_apply]
        exact (φ.left_inv hy.1.2).symm
      · change e i x = φ.symm (g.symm (g (φ (e i x))))
        rw [g.symm_apply_apply]
        exact (φ.left_inv (mem_chart_source H (e i x))).symm
    · intro y hy
      rw [hIJ]
      let φ := chartAt H y
      let k : K := ⟨i, φ, chart_mem_atlas H y⟩
      have hxC : (e i).toOpenPartialHomeomorph.symm y ∈ (c k).source := by
        refine ⟨⟨(e i).toOpenPartialHomeomorph.map_target hy, ?_⟩, mem_univ _⟩
        change (e i).toOpenPartialHomeomorph
          ((e i).toOpenPartialHomeomorph.symm y) ∈ φ.source
        rw [(e i).toOpenPartialHomeomorph.right_inv hy]
        exact mem_chart_source H y
      have hyC : g (φ y) ∈ (c k).target := by
        have h := (c k).map_source hxC
        change g (φ ((e i).toOpenPartialHomeomorph
          ((e i).toOpenPartialHomeomorph.symm y))) ∈ (c k).target at h
        rwa [(e i).toOpenPartialHomeomorph.right_inv hy] at h
      have hd := contMDiffAt_symm_of_mem_maximalAtlas (hmem k) hyC
      have hφ := contMDiffAt_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := J) (n := ∞) y) (mem_chart_source H y)
      rw [hIJ] at hφ
      have hs := hd.comp y (g.contDiff.contMDiff.contMDiffAt.comp y hφ)
      apply hs.contMDiffWithinAt.congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds
          (φ.open_source.mem_nhds (mem_chart_source H y))] with z hz
        change (e i).toOpenPartialHomeomorph.symm z =
          (e i).toOpenPartialHomeomorph.symm (φ.symm (g.symm (g (φ z))))
        rw [g.symm_apply_apply, φ.left_inv hz]
      · change (e i).toOpenPartialHomeomorph.symm y =
          (e i).toOpenPartialHomeomorph.symm (φ.symm (g.symm (g (φ y))))
        rw [g.symm_apply_apply, φ.left_inv (mem_chart_source H y)]
  -- In a product chart the original projection is the first-coordinate projection.
  have hp : Manifold.IsSubmersion 𝓘(ℝ, G) 𝓘(ℝ, EB) ∞ p := by
    unfold Manifold.IsSubmersion
    refine ⟨EF, inferInstance, inferInstance, ?_⟩
    intro x
    let i := index x
    let b := chartAt EB (p x)
    let f := chartAt EF ((e i x).2)
    let φ := b.prod f
    have hφ : φ ∈ atlas H Y := by
      exact ⟨b, chart_mem_atlas EB (p x), f, chart_mem_atlas EF ((e i x).2), rfl⟩
    let k : K := ⟨i, φ, hφ⟩
    have hx : x ∈ (e i).source := hindex x
    have hxC : x ∈ (c k).source := by
      refine ⟨⟨hx, ?_⟩, mem_univ _⟩
      change (e i x).1 ∈ b.source ∧ (e i x).2 ∈ f.source
      rw [(e i).coe_fst hx]
      exact ⟨mem_chart_source EB (p x), mem_chart_source EF ((e i x).2)⟩
    apply Manifold.IsSubmersionAtOfComplement.mk_of_charts g.symm (c k) b hxC
      (mem_chart_source EB (p x)) (hmem k) (IsManifold.chart_mem_maximalAtlas (p x))
    · intro y hy
      have h := hy.1.2.1
      change (e i y).1 ∈ b.source at h
      rwa [(e i).coe_fst hy.1.1] at h
    · intro z hz
      have hz' : z ∈ (c k).target := by simpa only [mfld_simps] using hz
      have hφtarget : g.symm z ∈ φ.target := hz'.2.1
      have heTarget : φ.symm (g.symm z) ∈ (e i).target := hz'.2.2
      simp only [Function.comp_apply, OpenPartialHomeomorph.extend, PartialEquiv.trans_apply]
      change b (p ((e i).toOpenPartialHomeomorph.symm (φ.symm (g.symm z)))) = (g.symm z).1
      rw [(e i).proj_symm_apply heTarget]
      exact b.right_inv hφtarget.1
  exact ⟨C, hm, hp.contMDiff, hp, hlocal⟩

end AtiyahSinger
