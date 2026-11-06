/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Compactness.Paracompact

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# The actual vertical tangent bundle of a smooth submersion

Public module ID: M1513.

The fiber over z is the kernel of the original manifold derivative at z.
Its carrier is the actual submodule subtype of T_z M. The total topology is
induced by the original inclusion into TM, retaining all original tangent
operations and topologies. Submersion normal charts supply one native smooth
vector-bundle atlas together with smoothness of that same inclusion.

A separate existence theorem constructs a smooth linear right inverse of
the actual derivative over a Hausdorff paracompact source. It uses local
normal-chart lifts and a smooth partition of unity. No horizontal complement
is assumed, and no metric, compactness, properness or global frame is needed.

Sources: HU III.8.2 for kernels and subbundles, III.9.6 for continuous splitting,
and SG III.13, p.251, for the vertical geometry preceding (13.16). The smooth
kernel atlas and smooth splitting argument are explicit project supplements.
The proofs differentiate the supplied submersion normal forms to identify
the kernel coordinates and obtain local derivative right inverses.

This is the vertical tangent kernel. SG's quotient T*M modulo the pulled
cotangent bundle is canonically the dual of this kernel, not this kernel
itself without further identification. That dual comparison and a choice of
cotangent splitting remain separate downstream constructions. The actual kernel
atlas and smooth horizontal lift are constructed below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

/-- The standard finite coordinate model for the vertical dimension; an implementation adapter. -/
abbrev VerticalTangentModel (E F : Type*) [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] : Type :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ F))

section Kernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

/-- The vertical fiber is the actual kernel subtype of the original manifold derivative. -/
abbrev VerticalTangentFiber (f : M → N) (z : M) : Type _ :=
  LinearMap.ker (mfderiv I J f z).toLinearMap

/-- The actual vertical vector is included in its original tangent fiber over the same point. -/
def verticalTangentInclusion (V : Type*) (f : M → N) :
    TotalSpace V (VerticalTangentFiber I J f) → TangentBundle I M :=
  fun z ↦ ⟨z.proj, z.snd.val⟩

/-- The vertical total topology is induced by inclusion into the original tangent bundle. -/
@[reducible]
def verticalTangentTopology [IsManifold I 1 M] (V : Type*) (f : M → N) :
    TopologicalSpace (TotalSpace V (VerticalTangentFiber I J f)) :=
  TopologicalSpace.induced (verticalTangentInclusion I J V f) inferInstance

end Kernel

attribute [local instance] verticalTangentTopology

section SmoothAtlas

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

open Manifold Set Topology in
set_option linter.unusedSectionVars false in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- A smooth submersion gives the actual derivative kernel its smooth subbundle atlas. -/
theorem exists_verticalTangent_atlas
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ∃ hB : FiberBundle (VerticalTangentModel E F)
        (VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f),
      letI := hB
      ∃ hV : VectorBundle ℝ (VerticalTangentModel E F)
          (VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f),
        letI := hV
        ContMDiffVectorBundle ∞ (VerticalTangentModel E F)
            (VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f) 𝓘(ℝ, E) ∧
          ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, VerticalTangentModel E F))
            (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
            (verticalTangentInclusion 𝓘(ℝ, E) 𝓘(ℝ, F) (VerticalTangentModel E F) f) := by
  classical
  -- The original complement has the prescribed vertical dimension at every existing point.
  have hmodel (x : M) :
      IsSubmersionAtOfComplement (VerticalTangentModel E F) 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
    let C := hf.complement
    let := hf.instNormedAddCommGroupComplement
    let := hf.instNormedSpaceComplement
    let h := hf.isSubmersionOfComplement_complement.isSubmersionAt x
    let : FiniteDimensional ℝ (F × C) := h.equiv.toLinearEquiv.finiteDimensional
    let : FiniteDimensional ℝ C := FiniteDimensional.of_injective
      (LinearMap.inr ℝ F C) (fun _ _ h ↦ congrArg Prod.snd h)
    have heq := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at heq
    change Module.finrank ℝ E = Module.finrank ℝ F + Module.finrank ℝ C at heq
    have hdim : Module.finrank ℝ C = Module.finrank ℝ (VerticalTangentModel E F) := by
      simp only [VerticalTangentModel, finrank_euclideanSpace_fin]
      omega
    exact h.trans_F
      (LinearEquiv.ofFinrankEq C (VerticalTangentModel E F) hdim).toContinuousLinearEquiv
  -- Differentiate the exact submersion chart equation on its original open source.
  have hderivative (x y : M) (hy : y ∈ (hmodel x).domChart.source) :
      let h := hmodel x
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart (f y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y) =
        ((ContinuousLinearMap.fst ℝ F (VerticalTangentModel E F)).comp
          h.equiv.toContinuousLinearMap).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart y) := by
    let h := hmodel x
    let L := (ContinuousLinearMap.fst ℝ F (VerticalTangentModel E F)).comp
      h.equiv.toContinuousLinearMap
    have hbase (z : M) (hz : z ∈ h.domChart.source) :
        h.codChart (f z) = L (h.domChart z) := by
      have hcz : h.domChart z ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
        simpa only [mfld_simps] using h.domChart.map_source hz
      have hv := h.writtenInCharts hcz
      change h.codChart (f (h.domChart.symm (h.domChart z))) = (h.equiv (h.domChart z)).1 at hv
      rwa [h.domChart.left_inv hz] at hv
    have hevent : (h.codChart ∘ f : M → F) =ᶠ[𝓝 y] L ∘ h.domChart :=
      Filter.eventuallyEq_of_mem (h.domChart.open_source.mem_nhds hy) hbase
    have hder := hevent.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    rw [mfderiv_comp y
        ((contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
          (h.source_subset_preimage_source hy)).mdifferentiableAt (by simp))
        (f.contMDiff.mdifferentiable (by simp) y),
      mfderiv_comp y ((L.contMDiff (n := ∞)).mdifferentiableAt (by simp))
        ((contMDiffAt_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hy).mdifferentiableAt
          (by simp))] at hder
    rw [mfderiv_eq_fderiv] at hder
    change _ = (fderiv ℝ L (h.domChart y)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart y) at hder
    simpa only [L.fderiv, L, h] using hder
  -- The second source-chart factor is the actual kernel, with its native submodule topology.
  have hFiber (x y : M) (hy : y ∈ (hmodel x).domChart.source) :
      let h := hmodel x
      ∃ e : VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f y ≃L[ℝ]
          VerticalTangentModel E F,
        (∀ v, e v = (h.equiv (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart y v.val)).2) ∧
        (∀ w, (e.symm w).val =
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart.symm
            (h.domChart y) (h.equiv.symm (0, w))) := by
    let h := hmodel x
    have hd : h.domChart.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
      ⟨fun z hz ↦ (contMDiffAt_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hz
          |>.mdifferentiableAt (by simp)).mdifferentiableWithinAt,
        fun z hz ↦ (contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hz
          |>.mdifferentiableAt (by simp)).mdifferentiableWithinAt⟩
    have hc : h.codChart.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F) :=
      ⟨fun z hz ↦ (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hz
          |>.mdifferentiableAt (by simp)).mdifferentiableWithinAt,
        fun z hz ↦ (contMDiffAt_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hz
          |>.mdifferentiableAt (by simp)).mdifferentiableWithinAt⟩
    let A := (hd.mfderiv hy).trans h.equiv
    let B := hc.mfderiv (h.source_subset_preimage_source hy)
    let S := LinearMap.ker (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y).toLinearMap
    have hcoord (v : TangentSpace 𝓘(ℝ, E) y) :
        B (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y v) = (A v).1 :=
      congrArg (fun L ↦ L v) (hderivative x y hy)
    have hfst (v : S) : (A v.val).1 = 0 := by
      exact (hcoord v.val).symm.trans
        ((congrArg B (show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y v.val = 0 from v.property)).trans
          (map_zero B))
    let Q : S →L[ℝ] VerticalTangentModel E F :=
      ((ContinuousLinearMap.snd ℝ F (VerticalTangentModel E F)).comp
        A.toContinuousLinearMap).comp S.subtypeL
    have hinj : Function.Injective Q := by
      intro u v huv
      apply Subtype.ext
      apply A.injective
      exact Prod.ext ((hfst u).trans (hfst v).symm) huv
    have hmem (w : VerticalTangentModel E F) : A.symm (0, w) ∈ S := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y (A.symm (0, w)) = 0
      apply B.injective
      exact (hcoord (A.symm (0, w))).trans
        ((congrArg Prod.fst (A.apply_symm_apply (0, w))).trans (map_zero B).symm)
    have hright (w : VerticalTangentModel E F) : Q ⟨A.symm (0, w), hmem w⟩ = w := by
      change (A (A.symm (0, w))).2 = w
      rw [A.apply_symm_apply]
    let e := (LinearEquiv.ofBijective Q.toLinearMap
      ⟨hinj, fun w ↦ ⟨⟨A.symm (0, w), hmem w⟩, hright w⟩⟩).toContinuousLinearEquiv
    refine ⟨e, fun _ ↦ rfl, ?_⟩
    intro w
    have heq : e.symm w = ⟨A.symm (0, w), hmem w⟩ := by
      apply e.injective
      exact (e.apply_symm_apply w).trans (hright w).symm
    exact congrArg Subtype.val heq
  -- The complementary component of the original smooth chart derivative gives forward coordinates.
  have hForward (x : M) :
      let h := hmodel x
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (𝓘(ℝ, E).prod 𝓘(ℝ, VerticalTangentModel E F)) ∞
        (fun z : TangentBundle 𝓘(ℝ, E) M ↦
          (z.proj, (h.equiv
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart z.proj z.snd)).2))
        ((fun z ↦ z.proj) ⁻¹' h.domChart.source) := by
    let h := hmodel x
    dsimp only
    intro z hz
    have hcod := contMDiffAt_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      hz
    have ht := hcod.contMDiffAt_tangentMap (X := (⟨z.proj, z.snd⟩ :
      TangentBundle 𝓘(ℝ, E) M)) (m := ∞) (by simp)
    have hv := (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).contMDiffAt.comp _ ht
    let P := (ContinuousLinearMap.snd ℝ F (VerticalTangentModel E F)).comp
      h.equiv.toContinuousLinearMap
    exact ((Bundle.contMDiffAt_proj (TangentSpace 𝓘(ℝ, E) (M := M))).prodMk
      (P.contMDiff.contMDiffAt.comp z hv)).contMDiffWithinAt
  -- The inverse chart derivative gives a smooth representative for every complementary vector.
  have hBackward (x : M) :
      let h := hmodel x
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, VerticalTangentModel E F))
        (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun p : M × VerticalTangentModel E F ↦
          (⟨p.1, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart.symm
            (h.domChart p.1) (h.equiv.symm (0, p.2))⟩ :
            TangentBundle 𝓘(ℝ, E) M))
        (h.domChart.source ×ˢ univ) := by
    let h := hmodel x
    dsimp only
    intro p hp
    have hcod := contMDiffAt_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      hp.1
    have hci := contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
      (h.domChart.map_source hp.1)
    let k (q : M × VerticalTangentModel E F) : TangentBundle 𝓘(ℝ, E) E :=
      ⟨h.domChart q.1, h.equiv.symm (0, q.2)⟩
    have hk : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, VerticalTangentModel E F))
        (𝓘(ℝ, E)).tangent ∞ k p :=
      by
        let L := h.equiv.symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ F (VerticalTangentModel E F))
        have hfirst : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, VerticalTangentModel E F)) 𝓘(ℝ, E) ∞
            (fun q : M × VerticalTangentModel E F ↦ h.domChart q.1) p :=
          hcod.comp p contMDiffAt_fst
        have hsecond : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, VerticalTangentModel E F)) 𝓘(ℝ, E) ∞
            (fun q : M × VerticalTangentModel E F ↦ L q.2) p :=
          L.contMDiff.contMDiffAt.comp p contMDiffAt_snd
        apply Bundle.contMDiffAt_totalSpace.mpr
        refine ⟨hfirst, ?_⟩
        simpa only [trivializationAt_model_space_apply, k, L, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe] using hsecond
    have ht := (hci.contMDiffAt_tangentMap (X := k p) (m := ∞) (by simp)).comp p hk
    have htarget : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, VerticalTangentModel E F)) (𝓘(ℝ, E)).tangent ∞
        (fun q : M × VerticalTangentModel E F ↦
          (⟨q.1, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart.symm
            (h.domChart q.1) (h.equiv.symm (0, q.2))⟩ : TangentBundle 𝓘(ℝ, E) M)) p := by
      apply ht.congr_of_eventuallyEq
      filter_upwards [(h.domChart.open_source.preimage continuous_fst).mem_nhds hp.1] with q hq
      exact TotalSpace.ext
        (h.domChart.left_inv hq).symm (by rfl)
    exact htarget.contMDiffWithinAt
  -- The original total topology is induced by the actual inclusion into TM.
  let G := VerticalTangentModel E F
  let V := VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let J := verticalTangentInclusion 𝓘(ℝ, E) 𝓘(ℝ, F) G f
  have hJ : IsInducing J := ⟨rfl⟩
  have hproj : Continuous (TotalSpace.proj : TotalSpace G V → M) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E) (M := M))).comp hJ.continuous
  let C (x : M) (z : TangentBundle 𝓘(ℝ, E) M) : M × G :=
    (z.proj, ((hmodel x).equiv
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hmodel x).domChart z.proj z.snd)).2)
  let R (x : M) (p : M × G) : TangentBundle 𝓘(ℝ, E) M :=
    ⟨p.1, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hmodel x).domChart.symm
      ((hmodel x).domChart p.1) ((hmodel x).equiv.symm (0, p.2))⟩
  -- The linear kernel coordinates are genuine trivializations for that fixed topology.
  have hTriv (x : M) :
      ∃ e : Trivialization G (TotalSpace.proj : TotalSpace G V → M),
        e.baseSet = (hmodel x).domChart.source ∧ e.IsLinear ℝ ∧
        (∀ z : TotalSpace G V, z.proj ∈ (hmodel x).domChart.source → e z = C x (J z)) ∧
        (∀ p : M × G, p.1 ∈ (hmodel x).domChart.source →
          J (e.toOpenPartialHomeomorph.symm p) = R x p) := by
    let h := hmodel x
    let e (y : M) (hy : y ∈ h.domChart.source) : V y ≃L[ℝ] G :=
      (hFiber x y hy).choose
    have he (y : M) (hy : y ∈ h.domChart.source) := (hFiber x y hy).choose_spec
    let forward (z : TotalSpace G V) : M × G :=
      (z.proj, if hz : z.proj ∈ h.domChart.source then e z.proj hz z.snd else 0)
    let backward (p : M × G) : TotalSpace G V :=
      ⟨p.1, if hp : p.1 ∈ h.domChart.source then (e p.1 hp).symm p.2 else 0⟩
    have hforwardJ (z : TotalSpace G V) (hz : z.proj ∈ h.domChart.source) :
        forward z = C x (J z) := by
      apply Prod.ext
      · rfl
      change (if hz : z.proj ∈ h.domChart.source then e z.proj hz z.snd else 0) = _
      rw [dite_eq_left hz]
      exact (he z.proj hz).1 z.snd
    have hbackwardJ (p : M × G) (hp : p.1 ∈ h.domChart.source) :
        J (backward p) = R x p := by
      apply congrArg (TotalSpace.mk p.1)
      change (if hp : p.1 ∈ h.domChart.source then (e p.1 hp).symm p.2 else 0).val = _
      rw [dite_eq_left hp]
      exact (he p.1 hp).2 p.2
    have hforward : ContinuousOn forward ((fun z ↦ z.proj) ⁻¹' h.domChart.source) :=
      ((hForward x).continuousOn.comp hJ.continuous.continuousOn (fun _ hz ↦ hz)).congr
        (fun z hz ↦ hforwardJ z hz)
    have hbackward : ContinuousOn backward (h.domChart.source ×ˢ univ) := by
      apply hJ.continuousOn_iff.mpr
      exact (hBackward x).continuousOn.congr (fun p hp ↦ hbackwardJ p hp.1)
    let t : Trivialization G (TotalSpace.proj : TotalSpace G V → M) :=
      { toFun := forward
        invFun := backward
        source := (fun z ↦ z.proj) ⁻¹' h.domChart.source
        target := h.domChart.source ×ˢ univ
        map_source' := fun _ hz ↦ ⟨hz, mem_univ _⟩
        map_target' := fun _ hp ↦ hp.1
        left_inv' := by
          intro z hz
          change z.proj ∈ h.domChart.source at hz
          apply congrArg (TotalSpace.mk z.proj)
          change (if hh : z.proj ∈ h.domChart.source then (e z.proj hh).symm
            (if hh : z.proj ∈ h.domChart.source then e z.proj hh z.snd else 0) else 0) = z.snd
          rw [dite_eq_left hz, dite_eq_left hz, ContinuousLinearEquiv.symm_apply_apply]
        right_inv' := by
          intro p hp
          apply Prod.ext
          · rfl
          change (if hh : p.1 ∈ h.domChart.source then e p.1 hh
            (if hh : p.1 ∈ h.domChart.source then (e p.1 hh).symm p.2 else 0) else 0) = p.2
          rw [dite_eq_left hp.1, dite_eq_left hp.1, ContinuousLinearEquiv.apply_symm_apply]
        open_source := h.domChart.open_source.preimage hproj
        open_target := h.domChart.open_source.prod isOpen_univ
        continuousOn_toFun := hforward
        continuousOn_invFun := hbackward
        baseSet := h.domChart.source
        open_baseSet := h.domChart.open_source
        source_eq := rfl
        target_eq := rfl
        proj_toFun := fun _ _ ↦ rfl }
    refine ⟨t, rfl, ?_, hforwardJ, hbackwardJ⟩
    constructor
    intro y hy
    change y ∈ h.domChart.source at hy
    change IsLinearMap ℝ (fun v : V y ↦
      if hh : y ∈ h.domChart.source then e y hh v else 0)
    simp only [dite_eq_left hy]
    exact (e y hy).toLinearMap.isLinear
  -- The induced total topology restricts to the original submodule topology on every fiber.
  have hInducing (x : M) : IsInducing (TotalSpace.mk x : V x → TotalSpace G V) := by
    apply hJ.of_comp_iff.mp
    exact (FiberBundle.totalSpaceMk_isInducing E (TangentSpace 𝓘(ℝ, E) (M := M)) x).comp
      IsInducing.subtypeVal
  -- Smooth original forward and inverse derivatives give smooth operator transitions.
  have hTransitions (x y : M) :
      let e := (hTriv x).choose
      let e' := (hTriv y).choose
      let := (hTriv x).choose_spec.2.1
      let := (hTriv y).choose_spec.2.1
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] G) ∞
        (fun b ↦ (e.coordChangeL ℝ e' b : G →L[ℝ] G))
        (e.baseSet ∩ e'.baseSet) := by
    let e := (hTriv x).choose
    let e' := (hTriv y).choose
    have he := (hTriv x).choose_spec
    have he' := (hTriv y).choose_spec
    let := he.2.1
    let := he'.2.1
    let h := hmodel x
    let h' := hmodel y
    dsimp only
    intro b hb
    have heval (v : G) :
        ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞
          (fun q ↦ e.coordChangeL ℝ e' q v) (e.baseSet ∩ e'.baseSet) b := by
      have hb₁ : b ∈ h.domChart.source := he.1 ▸ hb.1
      have hb₂ : b ∈ h'.domChart.source := he'.1 ▸ hb.2
      have hlift : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
          (fun q ↦ R x (q, v)) b :=
        ((hBackward x).contMDiffAt
          ((h.domChart.open_source.prod isOpen_univ).mem_nhds ⟨hb₁, mem_univ v⟩)).comp b
            (contMDiffAt_id.prodMk contMDiffAt_const)
      have hforward := ((hForward y).contMDiffAt
        ((h'.domChart.open_source.preimage (FiberBundle.continuous_proj E
          (TangentSpace 𝓘(ℝ, E) (M := M)))).mem_nhds hb₂)).comp b hlift
      have heq (q : M) (hq : q ∈ e.baseSet ∩ e'.baseSet) :
          e.coordChangeL ℝ e' q v = (C y (R x (q, v))).2 := by
        rw [e.coordChangeL_apply' e' hq v]
        have hq' : (e.toOpenPartialHomeomorph.symm (q, v)).proj ∈ h'.domChart.source := by
          rw [e.proj_symm_apply' hq.1]
          exact he'.1 ▸ hq.2
        rw [he'.2.2.1 _ hq', he.2.2.2 (q, v) (he.1 ▸ hq.1)]
      exact hforward.snd.contMDiffWithinAt.congr (fun q hq ↦ heq q hq) (heq b hb)
    rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
    apply contDiffWithinAt_clm_apply.mpr
    intro v
    have hv := heval v
    rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
    exact hv
  -- Select one coherent atlas and verify smoothness of its actual kernel inclusion.
  let e (x : M) := (hTriv x).choose
  have he (x : M) := (hTriv x).choose_spec
  let B : FiberBundle G V :=
    { totalSpaceMk_isInducing' := hInducing
      trivializationAtlas' := Set.range e
      trivializationAt' := e
      mem_baseSet_trivializationAt' := fun x ↦ (he x).1.symm ▸
        (hmodel x).mem_domChart_source
      trivialization_mem_atlas' := fun x ↦ ⟨x, rfl⟩ }
  let := B
  have hlin (t : Trivialization G (TotalSpace.proj : TotalSpace G V → M))
      [ht : MemTrivializationAtlas t] : t.IsLinear ℝ := by
    obtain ⟨x, rfl⟩ := ht.out
    exact (he x).2.1
  let := hlin
  have htrans (t t' : Trivialization G (TotalSpace.proj : TotalSpace G V → M))
      [ht : MemTrivializationAtlas t] [ht' : MemTrivializationAtlas t'] :
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] G) ∞
        (fun b ↦ (t.coordChangeL ℝ t' b : G →L[ℝ] G)) (t.baseSet ∩ t'.baseSet) := by
    obtain ⟨x, rfl⟩ := ht.out
    obtain ⟨y, rfl⟩ := ht'.out
    exact hTransitions x y
  let W : VectorBundle ℝ G V :=
    { trivialization_linear' := hlin
      continuousOn_coordChange' := fun t t' _ _ ↦ (htrans t t').continuousOn }
  let := W
  have hSmooth : ContMDiffVectorBundle ∞ G V 𝓘(ℝ, E) := ⟨htrans⟩
  let := hSmooth
  have hinclusion : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G))
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ J := by
    intro z
    let h := hmodel z.proj
    have hz : z.proj ∈ h.domChart.source := h.mem_domChart_source
    have hcoord := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        id z from contMDiffAt_id)).2
    have hback := ((hBackward z.proj).contMDiffAt
      ((h.domChart.open_source.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩)).comp z
        ((Bundle.contMDiffAt_proj V).prodMk hcoord)
    apply hback.congr_of_eventuallyEq
    filter_upwards [(h.domChart.open_source.preimage hproj).mem_nhds hz] with w hw
    have hwe : w ∈ (e z.proj).source := (e z.proj).mem_source.mpr ((he z.proj).1.symm ▸ hw)
    have hEq := (he z.proj).2.2.2 (w.proj, (e z.proj w).2) hw
    rw [(e z.proj).symm_apply_mk_proj hwe] at hEq
    exact hEq
  exact ⟨B, W, hSmooth, hinclusion⟩


/-- The chosen native kernel atlas comes from the single vertical-bundle existence witness. -/
@[reducible]
def verticalTangentFiberBundle
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    FiberBundle (VerticalTangentModel E F)
      (VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f) :=
  (exists_verticalTangent_atlas f hf).choose

/-- Linear triviality uses precisely that selected vertical kernel atlas. -/
instance verticalTangentVectorBundle
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    letI := verticalTangentFiberBundle f hf
    VectorBundle ℝ (VerticalTangentModel E F)
      (VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f) :=
  (exists_verticalTangent_atlas f hf).choose_spec.choose

/-- Smooth transition functions retain the same atlas and its selected linearity certificate. -/
instance verticalTangentContMDiffVectorBundle
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    letI := verticalTangentFiberBundle f hf
    letI := verticalTangentVectorBundle f hf
    ContMDiffVectorBundle ∞ (VerticalTangentModel E F)
      (VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f) 𝓘(ℝ, E) :=
  (exists_verticalTangent_atlas f hf).choose_spec.choose_spec.1

/-- The original vertical inclusion, bundled with smoothness from the same selected atlas. -/
def smoothVerticalTangentInclusion
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    letI := verticalTangentFiberBundle f hf
    ContMDiffMap (𝓘(ℝ, E).prod 𝓘(ℝ, VerticalTangentModel E F))
      (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (TotalSpace (VerticalTangentModel E F)
        (VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f))
      (TangentBundle 𝓘(ℝ, E) M) ∞ :=
  ⟨verticalTangentInclusion 𝓘(ℝ, E) 𝓘(ℝ, F) (VerticalTangentModel E F) f,
    (exists_verticalTangent_atlas f hf).choose_spec.choose_spec.2⟩

open Function Manifold Set Topology in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual derivative of a smooth submersion admits a smooth linear horizontal right inverse. -/
theorem exists_smooth_horizontalLift [T2Space M] [ParacompactSpace M]
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ∃ h : ∀ z, TangentSpace 𝓘(ℝ, F) (f z) →L[ℝ] TangentSpace 𝓘(ℝ, E) z,
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
          (fun z : TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) ↦
            (⟨z.proj, h z.proj z.snd⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        ∀ z, Function.RightInverse (h z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z) := by
  classical
  let V := ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))
  let W := TangentSpace 𝓘(ℝ, E) (M := M)
  -- Expose the existing pullback fiber algebra while retaining its native topology.
  let (y : M) : AddCommGroup (((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) y) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, F) (f y))
    infer_instance
  let (y : M) : Module ℝ (((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) y) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, F) (f y))
    infer_instance
  let (y : M) : IsTopologicalAddGroup (((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) y) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, F) (f y))
    infer_instance
  let (y : M) : ContinuousSMul ℝ (((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) y) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, F) (f y))
    infer_instance
  let Q (y : M) : W y →L[ℝ] V y := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y
  -- The smooth tangent map has the same fiber coordinates in the native pullback bundle.
  have hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
      (fun z : TangentBundle 𝓘(ℝ, E) M ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace F V)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj W, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (f.contMDiff.contMDiff_tangentMap (m := ∞) (by simp) z)).2
  -- Surjectivity follows from the exact normal-chart equation for the original map.
  have hqsurj (x : M) : Function.Surjective (Q x) := by
    let C := hf.complement
    let := hf.instNormedAddCommGroupComplement
    let := hf.instNormedSpaceComplement
    let h := hf.isSubmersionOfComplement_complement.isSubmersionAt x
    have hx := h.mem_domChart_source
    have hd : h.domChart.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
      ⟨fun z hz ↦ (contMDiffAt_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hz
          |>.mdifferentiableAt (by simp)).mdifferentiableWithinAt,
        fun z hz ↦ (contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hz
          |>.mdifferentiableAt (by simp)).mdifferentiableWithinAt⟩
    have hc : h.codChart.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F) :=
      ⟨fun z hz ↦ (contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hz
          |>.mdifferentiableAt (by simp)).mdifferentiableWithinAt,
        fun z hz ↦ (contMDiffAt_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hz
          |>.mdifferentiableAt (by simp)).mdifferentiableWithinAt⟩
    let A := (hd.mfderiv hx).trans h.equiv
    let B := hc.mfderiv h.mem_codChart_source
    let L := (ContinuousLinearMap.fst ℝ F C).comp h.equiv.toContinuousLinearMap
    have hbase (z : M) (hz : z ∈ h.domChart.source) :
        h.codChart (f z) = L (h.domChart z) := by
      have hcz : h.domChart z ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
        simpa only [mfld_simps] using h.domChart.map_source hz
      have hv := h.writtenInCharts hcz
      change h.codChart (f (h.domChart.symm (h.domChart z))) = (h.equiv (h.domChart z)).1 at hv
      rwa [h.domChart.left_inv hz] at hv
    have hevent : (h.codChart ∘ f : M → F) =ᶠ[𝓝 x] L ∘ h.domChart :=
      Filter.eventuallyEq_of_mem (h.domChart.open_source.mem_nhds hx) hbase
    have hder := hevent.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    rw [mfderiv_comp x
        ((contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
          h.mem_codChart_source).mdifferentiableAt (by simp))
        (f.contMDiff.mdifferentiable (by simp) x),
      mfderiv_comp x ((L.contMDiff (n := ∞)).mdifferentiableAt (by simp))
        ((contMDiffAt_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hx).mdifferentiableAt
          (by simp))] at hder
    rw [mfderiv_eq_fderiv] at hder
    change _ = (fderiv ℝ L (h.domChart x)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart x) at hder
    rw [L.fderiv] at hder
    have hcoord (v : W x) : B (Q x v) = (A v).1 := congrArg (fun D ↦ D v) hder
    intro v
    refine ⟨A.symm (B v, 0), B.injective ?_⟩
    exact (hcoord _).trans (congrArg Prod.fst (A.apply_symm_apply (B v, 0)))
  have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ s : ∀ y, V y →L[ℝ] W y,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] E)) ∞
          (fun y ↦ TotalSpace.mk' (F →L[ℝ] E) y (s y)) U ∧
        ∀ y, y ∈ U → ∀ v, Q y (s y v) = v := by
    let a := trivializationAt E W x
    let b := trivializationAt F V x
    let A (y : M) : E →L[ℝ] F :=
      (b.continuousLinearMapAt ℝ y).comp ((Q y).comp (a.symmL ℝ y))
    let U := a.baseSet ∩ b.baseSet
    have hU : IsOpen U := a.open_baseSet.inter b.open_baseSet
    have hx : x ∈ U := ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
    have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] F) ∞ A U := by
      intro y hy
      have heval (v : E) : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞
          (fun z ↦ A z v) U y := by
        have hs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
            (fun z ↦ (⟨z, a.symmL ℝ z v⟩ : TotalSpace E W)) y := by
          apply a.contMDiffAt_iff (a.mem_source.mpr hy.1) |>.mpr
          refine ⟨contMDiffAt_id, ?_⟩
          apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
          filter_upwards [a.open_baseSet.mem_nhds hy.1] with z hz
          rw [← a.continuousLinearMapAt_apply_of_mem ℝ hz]
          exact a.continuousLinearMapAt_symmL hz v
        have hq := hQ.contMDiffAt.comp y hs
        have hb := (b.contMDiffAt_iff (b.mem_source.mpr hy.2)).mp hq
        apply hb.2.contMDiffWithinAt.congr
        · intro z hz
          change (b.continuousLinearMapAt ℝ z) (Q z (a.symmL ℝ z v)) = _
          exact b.continuousLinearMapAt_apply_of_mem ℝ hz.2 _
        · exact b.continuousLinearMapAt_apply_of_mem ℝ hy.2 _
      rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
      apply contDiffWithinAt_clm_apply.mpr
      intro v
      have hv := heval v
      rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
      exact hv
    -- Choose one right inverse at the center; nearby invertible corrections vary smoothly.
    have hsurj : Function.Surjective (A x) := by
      intro v
      obtain ⟨w, hw⟩ := hqsurj x (b.symmL ℝ x v)
      refine ⟨a.continuousLinearMapAt ℝ x w, ?_⟩
      change (b.continuousLinearMapAt ℝ x) (Q x (a.symmL ℝ x
        (a.continuousLinearMapAt ℝ x w))) = v
      erw [a.symmL_continuousLinearMapAt (R := ℝ) hx.1]
      rw [hw, b.continuousLinearMapAt_symmL hx.2]
    choose R₀ hR₀ using (A x).toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hsurj)
    let R : F →L[ℝ] E := R₀.toContinuousLinearMap
    let C (y : M) : F →L[ℝ] F := (A y).comp R
    have hCx : C x = ContinuousLinearMap.id ℝ F := by
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun L : F →ₗ[ℝ] F ↦ L v) hR₀
    have hC : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] F) ∞ C U :=
      hA.clm_comp contMDiffOn_const
    have hCAt := (hC x hx).contMDiffAt (hU.mem_nhds hx)
    have hinv : (C x).IsInvertible := by
      rw [hCx]
      exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
    have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (C y).IsInvertible :=
      Filter.inter_mem (hU.mem_nhds hx) (hCAt.continuousAt hinv.eventually_nhds)
    choose U' hsub hU'o hx' using mem_nhds_iff.mp hevent
    let P (y : M) : F →L[ℝ] E := R.comp (C y).inverse
    have hP : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] E) ∞ P U' := by
      intro y hy
      have hCy := (hC y (hsub hy).1).contMDiffAt (hU.mem_nhds (hsub hy).1)
      have hInv := ((hsub hy).2.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp y hCy
      exact (contMDiffAt_const.clm_comp hInv).contMDiffWithinAt
    -- Transport this corrected matrix back through the same two original trivializations.
    let s (y : M) : V y →L[ℝ] W y :=
      (a.symmL ℝ y).comp ((P y).comp (b.continuousLinearMapAt ℝ y))
    let c := b.continuousLinearMap (RingHom.id ℝ) a
    have hs : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun y ↦ TotalSpace.mk' (F →L[ℝ] E) y (s y)) U' := by
      apply (c.contMDiffOn_section_iff hU'o (fun y hy ↦ (hsub hy).1.symm)).mpr
      apply hP.congr
      intro y hy
      ext v
      rw [show c = b.continuousLinearMap (RingHom.id ℝ) a from rfl,
        Trivialization.continuousLinearMap_apply]
      change (a.continuousLinearMapAt ℝ y)
        (a.symmL ℝ y (P y (b.continuousLinearMapAt ℝ y (b.symmL ℝ y v)))) = P y v
      rw [b.continuousLinearMapAt_symmL (hsub hy).1.2,
        a.continuousLinearMapAt_symmL (hsub hy).1.1]
    have hright (y : M) (hy : y ∈ U') (v : V y) : Q y (s y v) = v := by
      have hinj : Function.Injective (b.continuousLinearMapAt ℝ y) := by
        intro u v huv
        have heq := congrArg (b.symmL ℝ y) huv
        simpa only [b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2] using heq
      apply hinj
      change (A y) (R ((C y).inverse (b.continuousLinearMapAt ℝ y v))) =
        b.continuousLinearMapAt ℝ y v
      change (C y) ((C y).inverse (b.continuousLinearMapAt ℝ y v)) =
        b.continuousLinearMapAt ℝ y v
      obtain ⟨e, he⟩ := (hsub hy).2
      rw [← he, ContinuousLinearMap.inverse_equiv]
      exact e.apply_symm_apply _
    exact ⟨U', hU'o, hx', s, hs, hright⟩
  -- Glue the local lifts by a locally finite weighted sum and normalize its total weight.
  choose cover hcovero hcover s hs hQs using hlocal
  have hglobal : ∃ a : ∀ x, V x →L[ℝ] W x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun x ↦ TotalSpace.mk' (F →L[ℝ] E) x (a x)) ∧
      ∀ x v, Q x (a x v) = v := by
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
    have hweights : ∃ φ : M → M → ℝ,
        (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (φ i)) ∧
        (∀ i x, 0 ≤ φ i x) ∧ (∀ x, ∃ i, 0 < φ i x) ∧
        LocallyFinite (fun i ↦ tsupport (φ i)) ∧
        ∀ i, tsupport (φ i) ⊆ cover i := by
      -- Start with compact smooth-bump supports contained in the fixed original frames.
      have hb (x : M) : ∃ b : SmoothBumpFunction 𝓘(ℝ, E) x,
          tsupport b ⊆ cover x :=
        (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp
          ((hcovero x).mem_nhds (hcover x)) |>.imp
            (fun b hb ↦ hb.2)
      choose b hb using hb
      choose U hUo hUc hUf hUb using precise_refinement
        (fun x ↦ support (b x)) (fun x ↦ (b x).isOpen_support)
        (iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, (b x).c_mem_support⟩)
      -- A continuous bump cover supplies compact closed pieces covering the whole base.
      choose ρ hρ using BumpCovering.exists_isSubordinate_of_locallyFinite
        isClosed_univ U hUo hUf hUc.ge
      let K (i : M) : Set M := {x | ρ i x = 1}
      have hKclosed (i : M) : IsClosed (K i) := isClosed_eq (ρ i).continuous continuous_const
      have hKU (i : M) : K i ⊆ U i := by
        intro x hx
        apply hρ i
        apply subset_closure
        change ρ i x ≠ 0
        change ρ i x = 1 at hx
        simp [hx]
      have hKc : (univ : Set M) ⊆ ⋃ i, K i := by
        intro x hx
        exact mem_iUnion.mpr ⟨ρ.ind x hx, (ρ.eventuallyEq_one x hx).eq_of_nhds⟩
      have hKcompact (i : M) : IsCompact (K i) :=
        (b i).hasCompactSupport.of_isClosed_subset (hKclosed i)
          ((hKU i).trans ((hUb i).trans subset_closure))
      -- Sum finitely many smooth bumps on each compact piece, with supports inside U i.
      have hφ (i : M) : ∃ φ : M → ℝ,
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ ∧ (∀ x, 0 ≤ φ x) ∧
          (∀ x ∈ K i, 0 < φ x) ∧ tsupport φ ⊆ U i := by
        have hb' (x : K i) : ∃ b' : SmoothBumpFunction 𝓘(ℝ, E) (x : M),
            tsupport b' ⊆ U i :=
          (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (x : M)).mem_iff.mp
            ((hUo i).mem_nhds (hKU i x.property)) |>.imp (fun b' hb' ↦ hb'.2)
        choose c hc using hb'
        choose t ht using (hKcompact i).elim_finite_subcover
          (fun x : K i ↦ support (c x)) (fun x ↦ (c x).isOpen_support)
          (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, (c ⟨x, hx⟩).c_mem_support⟩)
        refine ⟨fun x ↦ ∑ y ∈ t, c y x, ?_, ?_, ?_, ?_⟩
        · exact contMDiff_finsetSum fun y hy ↦ (c y).contMDiff
        · intro x
          exact Finset.sum_nonneg fun y hy ↦ (c y).nonneg
        · intro x hx
          obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
          exact Finset.sum_pos' (fun z hz ↦ (c z).nonneg)
            ⟨y, hy, lt_of_le_of_ne (c y).nonneg (Ne.symm hxy)⟩
        · apply subset_trans (b := ⋃ y ∈ t, tsupport (c y))
          · apply closure_minimal
            · intro x hx
              by_contra hn
              apply hx
              apply Finset.sum_eq_zero
              intro y hy
              apply image_eq_zero_of_notMem_tsupport
              exact fun hxy ↦ hn (mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
            · exact isClosed_biUnion_finset fun y hy ↦ isClosed_closure
          · exact iUnion₂_subset fun y hy ↦ hc y
      choose φ hφsmooth hφnonneg hφpos hφsupport using hφ
      refine ⟨φ, hφsmooth, hφnonneg, ?_, hUf.subset hφsupport, ?_⟩
      · intro x
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hKc (mem_univ x))
        exact ⟨i, hφpos i x hi⟩
      · intro i
        exact (hφsupport i).trans ((hUb i).trans (subset_closure.trans (hb i)))
    choose φ hφsmooth hφnonneg hφpos hφfinite hφsupport using hweights
    -- Supported local lifts extend by zero, and their locally finite sum is smooth.
    let t (x : M) : V x →L[ℝ] W x := ∑ᶠ i, φ i x • s i x
    have hterm (i : M) : ContMDiff 𝓘(ℝ, E)
        (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun x ↦ TotalSpace.mk' (F →L[ℝ] E) x (φ i x • s i x)) :=
      ContMDiffOn.smul_section_of_tsupport (hφsmooth i).contMDiffOn
        (hcovero i) (hφsupport i) (hs i)
    have ht : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun x ↦ TotalSpace.mk' (F →L[ℝ] E) x (t x)) := by
      apply ContMDiff.finsum_section_of_locallyFinite ?_ hterm
      apply hφfinite.subset
      intro i x hx
      exact subset_closure (show φ i x ≠ 0 from fun hz ↦ hx (by simp [hz]))
    have hfinite (x : M) : (support (fun i ↦ φ i x)).Finite :=
      (hφfinite.point_finite x).subset (fun i hi ↦ subset_closure hi)
    -- Divide by the positive total weight so that the weighted sum is a right inverse.
    let w (x : M) : ℝ := ∑ᶠ i, φ i x
    have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w :=
      contMDiff_finsum hφsmooth (hφfinite.subset fun i ↦ subset_closure)
    have hwpos (x : M) : 0 < w x := finsum_pos (fun i ↦ hφnonneg i x) (hφpos x) (hfinite x)
    let a (x : M) : V x →L[ℝ] W x := (w x)⁻¹ • t x
    have ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun x ↦ TotalSpace.mk' (F →L[ℝ] E) x (a x)) :=
      (hw.inv₀ fun x ↦ (hwpos x).ne').smul_section ht
    refine ⟨a, ha, ?_⟩
    intro x v
    -- All nonzero summands are genuine right inverses of this same Q at x.
    have ht_eval : Q x (t x v) = w x • v := by
      have hsum : t x = ∑ i ∈ (hfinite x).toFinset, φ i x • s i x := by
        apply finsum_eq_sum_of_support_subset
        intro i hi
        exact (hfinite x).mem_toFinset.mpr (left_ne_zero_of_smul hi)
      rw [hsum]
      simp only [sum_apply, smul_apply, map_sum, map_smul]
      calc
        ∑ i ∈ (hfinite x).toFinset, φ i x • Q x (s i x v) =
            ∑ i ∈ (hfinite x).toFinset, φ i x • v := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hQs i x (hφsupport i (subset_closure ((hfinite x).mem_toFinset.mp hi))) v]
        _ = w x • v := by
          rw [← Finset.sum_smul]
          congr 1
          exact (finsum_eq_sum_of_support_subset (fun i ↦ φ i x)
            (fun i hi ↦ (hfinite x).mem_toFinset.mpr hi)).symm
    change Q x ((w x)⁻¹ • t x v) = v
    rw [map_smul, ht_eval, smul_smul, inv_mul_cancel₀ (hwpos x).ne', one_smul]
  -- Evaluation of the smooth Hom-section gives the required original total-space map.
  choose a ha hQa using hglobal
  refine ⟨a, ?_, hQa⟩
  exact (ha.comp (contMDiff_proj (F := F) (E := V))).clm_bundle_apply contMDiff_id



end SmoothAtlas

end AtiyahSinger
