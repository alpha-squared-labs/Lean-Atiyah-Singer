/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# The tangent map of a smooth proper embedding

Public module ID: M1477.

The map is mathlib's original `tangentMap`, with its actual differential in each
fiber. For finite-dimensional real manifolds without boundary, a smooth
embedding induces a smooth embedding of tangent bundles. Properness of the
original embedding implies properness of this induced embedding when both
bases are Hausdorff.

These are the geometric assertions used in SG III.12, printed p.241, before
constructing the tangent-bundle pushforward. They do not identify its normal
bundle with a direct sum: that comparison requires a splitting, and a complex
structure cannot be read off arbitrary tangent-bundle coordinates without one.
The chart argument and local-retraction closed-image argument below are explicit
project supplements to the source's summary; both assertions are proved here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Set Topology
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  {f : M → N}

-- Retain the declared finite-dimensional models in the public interface.
set_option linter.unusedSectionVars false in
/-- The original tangent map of a smooth embedding is a smooth embedding. -/
theorem isSmoothEmbedding_tangentMap
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    IsSmoothEmbedding (𝓘(ℝ, E)).tangent (𝓘(ℝ, F)).tangent ∞
      (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f) := by
  -- Lift each original maximal chart to its actual derivative chart. The two local
  -- constructions retain the independently quantified source and target model universes.
  have chartLiftM (c : OpenPartialHomeomorph M E)
      (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
      ∃ d : OpenPartialHomeomorph (TangentBundle 𝓘(ℝ, E) M) (ModelProd E E),
        d.source = (fun z ↦ z.proj) ⁻¹' c.source ∧
        d.target = Prod.fst ⁻¹' c.target ∧
        (∀ z, d z = (c z.proj, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c z.proj z.snd)) ∧
        (∀ p, d.symm p = tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm
          ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm p)) ∧
        d ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)).tangent ∞
          (TangentBundle 𝓘(ℝ, E) M) := by
    let e := tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)
    let forward := e ∘ tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) c
    let backward := tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm ∘ e.symm
    have hleft (z : TangentBundle 𝓘(ℝ, E) M) (hz : z.proj ∈ c.source) :
        backward (forward z) = z := by
      change tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm
        (e.symm (e (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) c z))) = z
      rw [e.symm_apply_apply]
      have hcc := contMDiffAt_of_mem_maximalAtlas hc hz
      have hci := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hz)
      rw [← tangentMap_comp_at z (hci.mdifferentiableAt (by simp))
        (hcc.mdifferentiableAt (by simp))]
      have heq : (c.symm ∘ c : M → M) =ᶠ[𝓝 z.proj] id :=
        Filter.eventuallyEq_of_mem (c.open_source.mem_nhds hz) (fun x hx ↦ c.left_inv hx)
      have hder := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
      simp only [mfderiv_id] at hder
      simp only [tangentMap]
      rw [hder]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      exact TotalSpace.ext (c.left_inv hz) (by rfl)
    have hright (p : ModelProd E E) (hp : p.1 ∈ c.target) : forward (backward p) = p := by
      change e (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) c
        (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (e.symm p))) = p
      have hci := contMDiffAt_symm_of_mem_maximalAtlas hc hp
      have hcc := contMDiffAt_of_mem_maximalAtlas hc (c.map_target hp)
      rw [← tangentMap_comp_at (e.symm p) (hcc.mdifferentiableAt (by simp))
        (hci.mdifferentiableAt (by simp))]
      have heq : (c ∘ c.symm : E → E) =ᶠ[𝓝 p.1] id :=
        Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hp) (fun x hx ↦ c.right_inv hx)
      have hder := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
      simp only [mfderiv_id] at hder
      change (c (c.symm p.1), (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (c ∘ c.symm) p.1) p.2) = p
      rw [hder]
      exact Prod.ext (c.right_inv hp) rfl
    have hforward : ContMDiffOn (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)).tangent ∞ forward
        ((fun z ↦ z.proj) ⁻¹' c.source) := by
      intro z hz
      exact ((contMDiff_tangentBundleModelSpaceHomeomorph (I := 𝓘(ℝ, E))).contMDiffAt.comp z
        ((contMDiffAt_of_mem_maximalAtlas hc hz).contMDiffAt_tangentMap
          (m := ∞) (by simp))).contMDiffWithinAt
    have hbackward : ContMDiffOn (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)).tangent ∞ backward
        (Prod.fst ⁻¹' c.target) := by
      intro p hp
      exact (((contMDiffAt_symm_of_mem_maximalAtlas hc hp).contMDiffAt_tangentMap
        (X := e.symm p) (m := ∞) (by simp)).comp p
          (contMDiff_tangentBundleModelSpaceHomeomorph_symm
            (I := 𝓘(ℝ, E))).contMDiffAt).contMDiffWithinAt
    let d : OpenPartialHomeomorph (TangentBundle 𝓘(ℝ, E) M) (ModelProd E E) :=
      { toFun := forward
        invFun := backward
        source := (fun z ↦ z.proj) ⁻¹' c.source
        target := Prod.fst ⁻¹' c.target
        map_source' := fun z hz ↦ c.map_source hz
        map_target' := fun p hp ↦ c.map_target hp
        left_inv' := hleft
        right_inv' := hright
        open_source := c.open_source.preimage (FiberBundle.continuous_proj _ _)
        open_target := c.open_target.preimage continuous_fst
        continuousOn_toFun := hforward.continuousOn
        continuousOn_invFun := hbackward.continuousOn }
    exact ⟨d, rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl,
      d.mem_maximalAtlas_of_contMDiffOn hforward hbackward⟩
  have chartLiftN (c : OpenPartialHomeomorph N F)
      (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N) :
      ∃ d : OpenPartialHomeomorph (TangentBundle 𝓘(ℝ, F) N) (ModelProd F F),
        d.source = (fun z ↦ z.proj) ⁻¹' c.source ∧
        d.target = Prod.fst ⁻¹' c.target ∧
        (∀ z, d z = (c z.proj, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c z.proj z.snd)) ∧
        (∀ p, d.symm p = tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) c.symm
          ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm p)) ∧
        d ∈ IsManifold.maximalAtlas (𝓘(ℝ, F)).tangent ∞
          (TangentBundle 𝓘(ℝ, F) N) := by
    let e := tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)
    let forward := e ∘ tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) c
    let backward := tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) c.symm ∘ e.symm
    have hleft (z : TangentBundle 𝓘(ℝ, F) N) (hz : z.proj ∈ c.source) :
        backward (forward z) = z := by
      change tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) c.symm
        (e.symm (e (tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) c z))) = z
      rw [e.symm_apply_apply]
      have hcc := contMDiffAt_of_mem_maximalAtlas hc hz
      have hci := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hz)
      rw [← tangentMap_comp_at z (hci.mdifferentiableAt (by simp))
        (hcc.mdifferentiableAt (by simp))]
      have heq : (c.symm ∘ c : N → N) =ᶠ[𝓝 z.proj] id :=
        Filter.eventuallyEq_of_mem (c.open_source.mem_nhds hz) (fun x hx ↦ c.left_inv hx)
      have hder := heq.mfderiv_eq (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F))
      simp only [mfderiv_id] at hder
      simp only [tangentMap]
      rw [hder]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      exact TotalSpace.ext (c.left_inv hz) (by rfl)
    have hright (p : ModelProd F F) (hp : p.1 ∈ c.target) : forward (backward p) = p := by
      change e (tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) c
        (tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) c.symm (e.symm p))) = p
      have hci := contMDiffAt_symm_of_mem_maximalAtlas hc hp
      have hcc := contMDiffAt_of_mem_maximalAtlas hc (c.map_target hp)
      rw [← tangentMap_comp_at (e.symm p) (hcc.mdifferentiableAt (by simp))
        (hci.mdifferentiableAt (by simp))]
      have heq : (c ∘ c.symm : F → F) =ᶠ[𝓝 p.1] id :=
        Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hp) (fun x hx ↦ c.right_inv hx)
      have hder := heq.mfderiv_eq (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F))
      simp only [mfderiv_id] at hder
      change (c (c.symm p.1), (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (c ∘ c.symm) p.1) p.2) = p
      rw [hder]
      exact Prod.ext (c.right_inv hp) rfl
    have hforward : ContMDiffOn (𝓘(ℝ, F)).tangent (𝓘(ℝ, F)).tangent ∞ forward
        ((fun z ↦ z.proj) ⁻¹' c.source) := by
      intro z hz
      exact ((contMDiff_tangentBundleModelSpaceHomeomorph (I := 𝓘(ℝ, F))).contMDiffAt.comp z
        ((contMDiffAt_of_mem_maximalAtlas hc hz).contMDiffAt_tangentMap
          (m := ∞) (by simp))).contMDiffWithinAt
    have hbackward : ContMDiffOn (𝓘(ℝ, F)).tangent (𝓘(ℝ, F)).tangent ∞ backward
        (Prod.fst ⁻¹' c.target) := by
      intro p hp
      exact (((contMDiffAt_symm_of_mem_maximalAtlas hc hp).contMDiffAt_tangentMap
        (X := e.symm p) (m := ∞) (by simp)).comp p
          (contMDiff_tangentBundleModelSpaceHomeomorph_symm
            (I := 𝓘(ℝ, F))).contMDiffAt).contMDiffWithinAt
    let d : OpenPartialHomeomorph (TangentBundle 𝓘(ℝ, F) N) (ModelProd F F) :=
      { toFun := forward
        invFun := backward
        source := (fun z ↦ z.proj) ⁻¹' c.source
        target := Prod.fst ⁻¹' c.target
        map_source' := fun z hz ↦ c.map_source hz
        map_target' := fun p hp ↦ c.map_target hp
        left_inv' := hleft
        right_inv' := hright
        open_source := c.open_source.preimage (FiberBundle.continuous_proj _ _)
        open_target := c.open_target.preimage continuous_fst
        continuousOn_toFun := hforward.continuousOn
        continuousOn_invFun := hbackward.continuousOn }
    exact ⟨d, rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl,
      d.mem_maximalAtlas_of_contMDiffOn hforward hbackward⟩
  -- In the lifted immersion charts, the tangent map is inclusion with doubled complement.
  have hImm : IsImmersion (𝓘(ℝ, E)).tangent (𝓘(ℝ, F)).tangent ∞
      (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f) := by
    let C := hf.isImmersion.complement
    let := hf.isImmersion.instNormedAddCommGroupComplement
    let := hf.isImmersion.instNormedSpaceComplement
    apply IsImmersionOfComplement.isImmersion (F := C × C)
    intro z
    let h := hf.isImmersion.isImmersionOfComplement_complement z.proj
    obtain ⟨d, hdsource, hdtarget, hd, hdi, hdmax⟩ :=
      chartLiftM h.domChart h.domChart_mem_maximalAtlas
    obtain ⟨c, hcsource, hctarget, hc, hci, hcmax⟩ :=
      chartLiftN h.codChart h.codChart_mem_maximalAtlas
    let L : E →L[ℝ] F := h.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E C)
    let D : ((E × E) × (C × C)) ≃L[ℝ] (F × F) :=
      (ContinuousLinearEquiv.prodProdProdComm ℝ E E C C).trans (h.equiv.prodCongr h.equiv)
    apply IsImmersionAtOfComplement.mk_of_charts D d c
    · rw [hdsource]
      exact h.mem_domChart_source
    · rw [hcsource]
      exact h.mem_codChart_source
    · exact hdmax
    · exact hcmax
    · intro w hw
      rw [hdsource] at hw
      rw [hcsource]
      exact h.source_subset_preimage_source hw
    · have hcoords : EqOn (h.codChart ∘ f ∘ h.domChart.symm) L h.domChart.target := by
        intro x hx
        have hx' : x ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
          simpa only [mfld_simps] using hx
        have hv := h.writtenInCharts hx'
        change h.codChart (f (h.domChart.symm x)) = h.equiv (x, 0) at hv
        exact hv
      intro p hp
      change c (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f (d.symm p)) = D (p, 0)
      have hp' : p.1 ∈ h.domChart.target := by
        simp only [mfld_simps] at hp
        change p ∈ d.target at hp
        rwa [hdtarget] at hp
      rw [hdi]
      let v : TangentBundle 𝓘(ℝ, E) E := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm p
      have hdom := contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hp'
      have hf' := hf.isImmersion.contMDiff (h.domChart.symm p.1)
      have hout : f (h.domChart.symm p.1) ∈ h.codChart.source :=
        h.source_subset_preimage_source (h.domChart.map_target hp')
      have hcod := contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hout
      have hevent : (h.codChart ∘ f ∘ h.domChart.symm) =ᶠ[𝓝 p.1] L :=
        Filter.eventuallyEq_of_mem (h.domChart.open_target.mem_nhds hp') hcoords
      have hder := hevent.fderiv_eq (𝕜 := ℝ)
      rw [L.fderiv] at hder
      have ht : tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart
          (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f
            (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart.symm v)) =
          tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) (h.codChart ∘ f ∘ h.domChart.symm) v := by
        rw [← tangentMap_comp_at v (hf'.mdifferentiableAt (by simp))
          (hdom.mdifferentiableAt (by simp))]
        rw [← tangentMap_comp_at v (hcod.mdifferentiableAt (by simp))
          ((hf'.comp _ hdom).mdifferentiableAt (by simp))]
      rw [hc]
      have hvalues := congrArg (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)) ht
      change (h.codChart (f (h.domChart.symm p.1)), _) = _ at hvalues
      exact hvalues.trans (by
        change (h.codChart (f (h.domChart.symm p.1)),
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (h.codChart ∘ f ∘ h.domChart.symm) p.1) p.2) = D (p, 0)
        rw [mfderiv_eq_fderiv]
        change (h.codChart (f (h.domChart.symm p.1)),
          (fderiv ℝ (h.codChart ∘ f ∘ h.domChart.symm) p.1) p.2) = D (p, 0)
        rw [hder]
        exact Prod.ext (hcoords hp') rfl)
  -- Projecting the immersion normal coordinates gives a smooth left inverse near each base.
  have localRetraction (x : M) :
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : N → M,
        (∀ y ∈ U, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ g (f y)) ∧ EqOn (g ∘ f) id U := by
    let h := hf.isImmersion.isImmersionOfComplement_complement x
    let A : F →L[ℝ] E := (ContinuousLinearMap.fst ℝ E hf.isImmersion.complement).comp
      h.equiv.symm.toContinuousLinearMap
    let g : N → M := h.domChart.symm ∘ A ∘ h.codChart
    have hbase (y : M) (hy : y ∈ h.domChart.source) :
        h.codChart (f y) = h.equiv (h.domChart y, 0) := by
      have hcy : h.domChart y ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
        simpa only [mfld_simps] using h.domChart.map_source hy
      have hv := h.writtenInCharts hcy
      change h.codChart (f (h.domChart.symm (h.domChart y))) = h.equiv (h.domChart y, 0) at hv
      rwa [h.domChart.left_inv hy] at hv
    refine ⟨h.domChart.source, h.domChart.open_source, h.mem_domChart_source, g, ?_, ?_⟩
    · intro y hy
      have hA : A (h.codChart (f y)) = h.domChart y := by
        rw [hbase y hy]
        change (h.equiv.symm (h.equiv (h.domChart y, 0))).1 = _
        rw [h.equiv.symm_apply_apply]
      have hcs := contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
        (h.domChart.map_source hy)
      have hAcs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h.domChart.symm
          (A (h.codChart (f y))) := hA ▸ hcs
      exact hAcs.comp (f y) (A.contMDiff.contMDiffAt.comp (f y)
        (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
          (h.source_subset_preimage_source hy)))
    · intro y hy
      change h.domChart.symm (A (h.codChart (f y))) = y
      rw [hbase y hy]
      change h.domChart.symm ((h.equiv.symm (h.equiv (h.domChart y, 0))).1) = y
      rw [h.equiv.symm_apply_apply]
      exact h.domChart.left_inv hy
  -- The same left inverse controls convergence in the original total-space topology.
  have hEmbedding : IsEmbedding (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f) := by
    let T := tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f
    have hcont : Continuous T := hf.contMDiff.continuous_tangentMap (by simp)
    have hinj : Function.Injective T := by
      rintro ⟨x, v⟩ ⟨y, w⟩ heq
      have hxy := hf.isEmbedding.injective (congrArg TotalSpace.proj heq)
      change x = y at hxy
      subst y
      have hvw : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v =
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x w := by
        exact eq_of_heq (TotalSpace.mk.inj heq).2
      have hvw' := hf.isImmersion.mfderiv_injective (by simp) x hvw
      subst w
      rfl
    refine ⟨isInducing_iff_nhds.mpr (fun z ↦ le_antisymm ?_ ?_), hinj⟩
    · exact hcont.continuousAt.le_comap
    · let L := Filter.comap T (𝓝 (T z))
      have hT : Filter.Tendsto T L (𝓝 (T z)) := Filter.tendsto_comap
      have hbase : Filter.Tendsto (fun w : TangentBundle 𝓘(ℝ, E) M ↦ w.proj) L (𝓝 z.proj) :=
        hf.isEmbedding.tendsto_nhds_iff.mpr
          ((FiberBundle.continuous_proj F (TangentSpace 𝓘(ℝ, F))).continuousAt.tendsto.comp hT)
      obtain ⟨U, hU, hz, g, hg, hgf⟩ := localRetraction z.proj
      have htg : ContinuousAt (tangentMap 𝓘(ℝ, F) 𝓘(ℝ, E) g) (T z) :=
        (hg z.proj hz).continuousAt_tangentMap (by simp)
      have hleft (w : TangentBundle 𝓘(ℝ, E) M) (hw : w.proj ∈ U) :
          tangentMap 𝓘(ℝ, F) 𝓘(ℝ, E) g (T w) = w := by
        have hgg : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) g (f w.proj) :=
          (hg w.proj hw).mdifferentiableAt (by simp)
        rw [← tangentMap_comp_at w hgg (hf.contMDiff.mdifferentiable (by simp) w.proj)]
        have heq := Filter.eventuallyEq_of_mem (hU.mem_nhds hw) hgf
        have hder := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
        simp only [mfderiv_id] at hder
        simp only [tangentMap]
        rw [hder]
        exact TotalSpace.ext (hgf hw) (by rfl)
      have hlim := htg.tendsto.comp hT
      rw [hleft z hz] at hlim
      have hevent : (tangentMap 𝓘(ℝ, F) 𝓘(ℝ, E) g ∘ T) =ᶠ[L] id := by
        filter_upwards [hbase.eventually (hU.mem_nhds hz)] with w hw
        exact hleft w hw
      exact (hlim.congr' hevent)
  exact ⟨hImm, hEmbedding⟩

/-- Properness passes to the actual tangent map of a finite-dimensional smooth embedding. -/
theorem isProperMap_tangentMap [T2Space M] [T2Space N]
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (hp : IsProperMap f) :
    IsProperMap (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f) := by
  /- A proper embedding has closed base image. Over a limit point of its tangent image,
  a local smooth retraction recovers a limit in the source tangent bundle. Uniqueness of
  limits in the Hausdorff target then proves that the tangent image is closed. The already
  established tangent embedding is therefore a closed embedding, hence a proper map. -/
  have localRetraction (x : M) :
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : N → M,
        (∀ y ∈ U, ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ g (f y)) ∧ EqOn (g ∘ f) id U := by
    let h := hf.isImmersion.isImmersionOfComplement_complement x
    let A : F →L[ℝ] E := (ContinuousLinearMap.fst ℝ E hf.isImmersion.complement).comp
      h.equiv.symm.toContinuousLinearMap
    let g : N → M := h.domChart.symm ∘ A ∘ h.codChart
    have hbase (y : M) (hy : y ∈ h.domChart.source) :
        h.codChart (f y) = h.equiv (h.domChart y, 0) := by
      have hcy : h.domChart y ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
        simpa only [mfld_simps] using h.domChart.map_source hy
      have hv := h.writtenInCharts hcy
      change h.codChart (f (h.domChart.symm (h.domChart y))) = h.equiv (h.domChart y, 0) at hv
      rwa [h.domChart.left_inv hy] at hv
    refine ⟨h.domChart.source, h.domChart.open_source, h.mem_domChart_source, g, ?_, ?_⟩
    · intro y hy
      have hA : A (h.codChart (f y)) = h.domChart y := by
        rw [hbase y hy]
        change (h.equiv.symm (h.equiv (h.domChart y, 0))).1 = _
        rw [h.equiv.symm_apply_apply]
      have hcs := contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
        (h.domChart.map_source hy)
      have hAcs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ h.domChart.symm
          (A (h.codChart (f y))) := hA ▸ hcs
      exact hAcs.comp (f y) (A.contMDiff.contMDiffAt.comp (f y)
        (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
          (h.source_subset_preimage_source hy)))
    · intro y hy
      change h.domChart.symm (A (h.codChart (f y))) = y
      rw [hbase y hy]
      change h.domChart.symm ((h.equiv.symm (h.equiv (h.domChart y, 0))).1) = y
      rw [h.equiv.symm_apply_apply]
      exact h.domChart.left_inv hy
  let TM := TangentBundle 𝓘(ℝ, E) M
  let TN := TangentBundle 𝓘(ℝ, F) N
  let T : TM → TN := tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f
  have hcont : Continuous T := hf.contMDiff.continuous_tangentMap (by simp)
  -- The actual target tangent bundle is Hausdorff in its native bundle charts.
  have hT2 : T2Space TN := by
    let e := fun x : N ↦ trivializationAt F (TangentSpace 𝓘(ℝ, F) : N → Type _) x
    have hproj : Continuous (fun z : TN ↦ z.proj) := FiberBundle.continuous_proj _ _
    apply t2Space_iff_disjoint_nhds.mpr
    intro z w hzw
    by_cases hbase : z.proj = w.proj
    · have hz : z ∈ (e z.proj).source := (e z.proj).mem_source.mpr
        (mem_baseSet_trivializationAt _ _ _)
      have hw : w ∈ (e z.proj).source := (e z.proj).mem_source.mpr
        (hbase ▸ mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj)
      exact ((e z.proj).continuousAt hz).disjoint
        (disjoint_nhds_nhds.mpr (fun he ↦ hzw ((e z.proj).injOn hz hw he)))
        ((e z.proj).continuousAt hw)
    · exact hproj.continuousAt.disjoint (disjoint_nhds_nhds.mpr hbase) hproj.continuousAt
  let := hT2
  have hclosed : IsClosed (Set.range T) := by
    apply isClosed_iff_clusterPt.mpr
    intro w hw
    let L := Filter.comap T (𝓝 w)
    let : L.NeBot := Filter.comap_neBot (by
      intro s hs
      obtain ⟨y, hys, hy⟩ := clusterPt_principal_iff.mp hw s hs
      obtain ⟨v, rfl⟩ := hy
      exact ⟨v, hys⟩)
    have hT : Filter.Tendsto T L (𝓝 w) := Filter.tendsto_comap
    have hproj : Continuous (fun z : TN ↦ z.proj) := FiberBundle.continuous_proj _ _
    have hwbase : w.proj ∈ Set.range f := hp.isClosed_range.mem_of_tendsto
      (hproj.continuousAt.tendsto.comp hT) (Filter.Eventually.of_forall
        (fun v ↦ ⟨v.proj, rfl⟩))
    obtain ⟨x, hfx⟩ := hwbase
    have hbase : Filter.Tendsto (fun v : TM ↦ v.proj) L (𝓝 x) := by
      apply hf.isEmbedding.tendsto_nhds_iff.mpr
      rw [hfx]
      exact hproj.continuousAt.tendsto.comp hT
    obtain ⟨U, hU, hx, g, hg, hgf⟩ := localRetraction x
    let G := tangentMap 𝓘(ℝ, F) 𝓘(ℝ, E) g
    have hg' : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ g w.proj := hfx ▸ hg x hx
    have hG : ContinuousAt G w := hg'.continuousAt_tangentMap (by simp)
    have hleft (v : TM) (hv : v.proj ∈ U) : G (T v) = v := by
      have hgg := (hg v.proj hv).mdifferentiableAt (by simp)
      change tangentMap 𝓘(ℝ, F) 𝓘(ℝ, E) g
        (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f v) = v
      rw [← tangentMap_comp_at v hgg (hf.contMDiff.mdifferentiable (by simp) v.proj)]
      have heq := Filter.eventuallyEq_of_mem (hU.mem_nhds hv) hgf
      have hder := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
      simp only [mfderiv_id] at hder
      simp only [tangentMap]
      rw [hder]
      exact TotalSpace.ext (hgf hv) (by rfl)
    have hevent : (G ∘ T) =ᶠ[L] id := by
      filter_upwards [hbase.eventually (hU.mem_nhds hx)] with v hv
      exact hleft v hv
    have hsource : Filter.Tendsto id L (𝓝 (G w)) := (hG.tendsto.comp hT).congr' hevent
    have heq : T (G w) = w := tendsto_nhds_unique
      (hcont.continuousAt.tendsto.comp hsource) hT
    exact ⟨G w, heq⟩
  have hclosedEmbedding : IsClosedEmbedding T :=
    ⟨(isSmoothEmbedding_tangentMap hf).isEmbedding, hclosed⟩
  exact hclosedEmbedding.isProperMap

end AtiyahSinger
