/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactEuclideanEmbedding

/-!
# Embedded atlases from local ambient coordinates

Public module ID: M1170.

Local charts of a subtype with smooth ambient coordinate extensions and smooth
ambient inverses give the embedded smooth structure on its original topology.
The ambient coordinate extension is a local left inverse of each parametrization;
differentiating this identity proves injectivity of the inclusion differential.
This is the standard local parametrization criterion for embedded submanifolds.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

/-- Smooth local ambient parametrizations determine the original subtype's embedded atlas. -/
theorem exists_embeddedAtlas {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (s : Set F)
    (h : ∀ x : s, ∃ c : OpenPartialHomeomorph s E, x ∈ c.source ∧
      ∃ f : F → E, (∀ y, c y = f y.val) ∧
        (∀ y ∈ c.source, ContDiffAt ℝ ∞ f y.val) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (c.symm z).val) c.target) :
    ∃ C : ChartedSpace E s, letI := C
      IsManifold 𝓘(ℝ, E) ∞ s ∧
        Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (Subtype.val : s → F) := by
  classical
  choose c hx f hc hf hg using h
  let C : ChartedSpace E s :=
    { atlas := Set.range c
      chartAt := c
      mem_chart_source := hx
      chart_mem_atlas := fun x ↦ ⟨x, rfl⟩ }
  let := C
  -- Chart changes are an ambient smooth coordinate map after a smooth parametrization.
  have hm : IsManifold 𝓘(ℝ, E) ∞ s := by
    apply isManifold_of_contDiffOn
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
    change ContDiffOn ℝ ∞ (fun z ↦ c y ((c x).symm z))
      ((c x).target ∩ (c x).symm ⁻¹' (c y).source)
    intro z hz
    have hi := (hg x).contDiffAt ((c x).open_target.mem_nhds hz.1)
    have ho := hf y ((c x).symm z) hz.2
    have hs : ContDiffWithinAt ℝ ∞ (f y ∘ fun z ↦ ((c x).symm z).val)
        ((c x).target ∩ (c x).symm ⁻¹' (c y).source) z :=
      (ho.comp z hi).contDiffWithinAt
    apply hs.congr
    · intro w _
      exact hc y ((c x).symm w)
    · exact hc y ((c x).symm z)
  let := hm
  have hparam (x : s) : ContDiffAt ℝ ∞ (fun z ↦ ((c x).symm z).val) (c x x) :=
    (hg x).contDiffAt ((c x).open_target.mem_nhds ((c x).map_source (hx x)))
  -- In the chosen full charts the inclusion is precisely the same parametrization.
  have hsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (Subtype.val : s → F) := by
    intro x
    apply contMDiffAt_iff.mpr
    refine ⟨continuous_subtype_val.continuousAt, ?_⟩
    exact (hparam x).contDiffWithinAt
  have hd (x : s) : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, F) (Subtype.val : s → F) x
      (fderiv ℝ (fun z ↦ ((c x).symm z).val) (c x x)) := by
    refine ⟨continuous_subtype_val.continuousAt, ?_⟩
    exact ((hparam x).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj (x : s) : Function.Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (Subtype.val : s → F) x) := by
    rw [(hd x).mfderiv]
    let g : E → F := fun z ↦ ((c x).symm z).val
    have hgx : g (c x x) = x.val := congrArg Subtype.val ((c x).left_inv (hx x))
    have hdf : DifferentiableAt ℝ (f x) (g (c x x)) := by
      rw [hgx]
      exact (hf x x (hx x)).differentiableAt (by simp)
    have hdg : DifferentiableAt ℝ g (c x x) := (hparam x).differentiableAt (by simp)
    have hlocal : (f x ∘ g) =ᶠ[𝓝 (c x x)] id := by
      filter_upwards [(c x).open_target.mem_nhds ((c x).map_source (hx x))] with z hz
      change f x ((c x).symm z).val = z
      rw [← hc x ((c x).symm z), (c x).right_inv hz]
    -- Differentiate the genuine local inverse identity on the open chart target.
    have hi := (hasFDerivAt_id (𝕜 := ℝ) (c x x)).congr_of_eventuallyEq hlocal
    have he := (hdf.hasFDerivAt.comp (c x x) hdg.hasFDerivAt).unique hi
    have hl : Function.LeftInverse (fderiv ℝ (f x) (g (c x x))) (fderiv ℝ g (c x x)) := by
      intro v
      exact congrArg (fun L : E →L[ℝ] E ↦ L v) he
    exact hl.injective
  exact ⟨C, hm, isImmersion_of_injective_mfderiv ⟨Subtype.val, hsmooth⟩ hinj,
    Topology.IsEmbedding.subtypeVal⟩

end AtiyahSinger
