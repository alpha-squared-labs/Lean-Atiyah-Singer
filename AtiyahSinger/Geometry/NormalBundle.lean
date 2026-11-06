/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Compactness.Paracompact

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# The quotient normal bundle of a smooth immersion

Public module ID: M1308.

The fiber at x is the actual quotient of T_(f x)N by the range of df_x.
Its total topology is the quotient topology of the original pulled-back tangent
bundle. A smooth finite-dimensional immersion gives this family its standard
smooth vector-bundle atlas, with the original quotient map smooth. One shared
existence witness supplies all the native mathlib bundle instances.

The local construction needs no properness, ambient embedding, metric or global
countability assumption. Global smooth splitting is a separate result over a
Hausdorff paracompact base. Sources: SG III.12, the normal-bundle construction
preceding (12.7),
and HU III.8.2, III.9.6 and 18.2.6 for cokernels, splitting and normal bundles.
HU III.9.6 gives continuous splitting; the smooth right inverse below is the
standard smooth supplement using local splittings and a smooth partition of unity.
Both the smooth quotient atlas and its global smooth right inverse are constructed below.
The gluing uses arbitrary locally finite refinements, with no countable-cover assumption.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Set Topology
open scoped Manifold ContDiff

/-- The standard finite coordinate model for the codimension; an implementation abbreviation. -/
abbrev NormalModel (E F : Type*) [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] : Type :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ F - Module.finrank ℝ E))

section Quotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F K)
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

/-- The normal fiber is the actual cokernel of the manifold differential. -/
abbrev NormalBundle (f : M → N) (x : M) : Type _ :=
  TangentSpace J (f x) ⧸ LinearMap.range (mfderiv I J f x).toLinearMap

/-- The original pulled-back tangent vector maps to its quotient class over the same point. -/
def normalQuotientMap (G : Type*) (f : M → N) :
    TotalSpace F (f *ᵖ (TangentSpace J)) → TotalSpace G (NormalBundle I J f) :=
  fun z ↦ ⟨z.proj, (LinearMap.range (mfderiv I J f z.proj).toLinearMap).mkQ z.snd⟩

/-- The normal total topology is coinduced by the original fiberwise quotient map. -/
@[reducible]
def normalBundleTopology [IsManifold J 1 N] (G : Type*) (f : M → N) :
    TopologicalSpace (TotalSpace G (NormalBundle I J f)) :=
  TopologicalSpace.coinduced (normalQuotientMap I J G f) inferInstance

/-- The image is closed in the original tangent topology.
After a compatible fiber norm is chosen, this also supports the usual quotient norm. -/
instance normalBundleRangeIsClosed [FiniteDimensional ℝ F] (f : M → N) (x : M) :
    IsClosed (LinearMap.range (mfderiv I J f x).toLinearMap :
      Set (TangentSpace J (f x))) :=
  Submodule.closed_of_finiteDimensional _

end Quotient

attribute [local instance] normalBundleTopology

section SmoothAtlas

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

-- Retain the original manifold interface; local immersion charts already provide base smoothness.
set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- A smooth immersion has its standard smooth quotient normal bundle and quotient map. -/
theorem exists_normalBundle_atlas
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ∃ hB : FiberBundle (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f),
      letI := hB
      ∃ hV : VectorBundle ℝ (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f),
        letI := hV
        ContMDiffVectorBundle ∞ (NormalModel E F)
            (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) 𝓘(ℝ, E) ∧
          ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F))
            (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
            (normalQuotientMap 𝓘(ℝ, E) 𝓘(ℝ, F) (NormalModel E F) f) := by
  classical
  -- The local normal form has the prescribed codimension at every point.
  -- An empty base requires no global dimension inequality.
  have hmodel (x : M) :
      IsImmersionAtOfComplement (NormalModel E F) 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
    let C := hf.complement
    let := hf.instNormedAddCommGroupComplement
    let := hf.instNormedSpaceComplement
    let h := hf.isImmersionOfComplement_complement x
    let : FiniteDimensional ℝ (E × C) := h.equiv.toLinearEquiv.symm.finiteDimensional
    let : FiniteDimensional ℝ C := FiniteDimensional.of_injective
      (LinearMap.inr ℝ E C) (fun _ _ h ↦ congrArg Prod.snd h)
    have heq := h.equiv.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at heq
    change Module.finrank ℝ E + Module.finrank ℝ C = Module.finrank ℝ F at heq
    have hdim : Module.finrank ℝ C = Module.finrank ℝ (NormalModel E F) := by
      simp only [NormalModel, finrank_euclideanSpace_fin]
      omega
    exact h.trans_F (LinearEquiv.ofFinrankEq C (NormalModel E F) hdim).toContinuousLinearEquiv
  -- Differentiate the original chart identity to identify the actual range of the tangent map.
  have hderivative (x y : M)
      (hy : y ∈ (hmodel x).domChart.source) :
      let h := hmodel x
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart (f y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y) =
        (h.equiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.inl ℝ E (NormalModel E F))).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) h.domChart y) := by
    let h := hmodel x
    let L := h.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E (NormalModel E F))
    have hbase (z : M) (hz : z ∈ h.domChart.source) :
        h.codChart (f z) = L (h.domChart z) := by
      have hcz : h.domChart z ∈ (h.domChart.extend 𝓘(ℝ, E)).target := by
        simpa only [mfld_simps] using h.domChart.map_source hz
      have hv := h.writtenInCharts hcz
      change h.codChart (f (h.domChart.symm (h.domChart z))) = h.equiv (h.domChart z, 0) at hv
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
  -- The second chart factor is the actual quotient, with its original quotient topology.
  have hFiber (x y : M)
      (hy : y ∈ (hmodel x).domChart.source) :
      let h := hmodel x
      ∃ e : NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f y ≃L[ℝ] NormalModel E F,
        (∀ v, e ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y).toLinearMap).mkQ v) =
          (h.equiv.symm (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart (f y) v)).2) ∧
        (∀ w, e.symm w =
          (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart.symm
              (h.codChart (f y)) (h.equiv (0, w)))) := by
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
    let A := hd.mfderiv hy
    let B := (hc.mfderiv (h.source_subset_preimage_source hy)).trans h.equiv.symm
    let P := (ContinuousLinearMap.snd ℝ E (NormalModel E F)).comp B.toContinuousLinearMap
    let S := LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y).toLinearMap
    have hcoord (v : TangentSpace 𝓘(ℝ, E) y) :
        B (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y v) = (A v, 0) := by
      have hv := congrArg (fun L ↦ L v) (hderivative x y hy)
      have heq := congrArg h.equiv.symm hv
      exact heq.trans (h.equiv.symm_apply_apply (A v, 0))
    have hker : S = P.toLinearMap.ker := by
      ext v
      constructor
      · rintro ⟨w, rfl⟩
        change (B (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y w)).2 = 0
        rw [hcoord]
      · intro hv
        change (B v).2 = 0 at hv
        obtain ⟨w, hw⟩ := A.surjective (B v).1
        refine ⟨w, B.injective ?_⟩
        change B (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y w) = B v
        rw [hcoord, hw]
        exact Prod.ext rfl hv.symm
    let Q : NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f y →L[ℝ] NormalModel E F :=
      S.liftQL P hker.le
    have hinj : Function.Injective Q :=
      LinearMap.ker_eq_bot.mp (S.ker_liftQ_eq_bot' P.toLinearMap hker)
    have hright (w : NormalModel E F) : Q (S.mkQ (B.symm (0, w))) = w := by
      change (B (B.symm (0, w))).2 = w
      rw [B.apply_symm_apply]
    let e := (LinearEquiv.ofBijective Q.toLinearMap
      ⟨hinj, fun w ↦ ⟨S.mkQ (B.symm (0, w)), hright w⟩⟩).toContinuousLinearEquiv
    refine ⟨e, fun _ ↦ rfl, ?_⟩
    intro w
    apply e.injective
    exact (e.apply_symm_apply w).trans (hright w).symm
  -- The native lift from the pulled-back tangent bundle is smooth in the original bundle charts.
  have hLift :
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, F)).tangent ∞
        (fun z : TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) ↦
          (⟨f z.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, F) N)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact f.contMDiff.contMDiffAt.comp z
        (Bundle.contMDiffAt_proj ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))
    · have h := (Bundle.contMDiffAt_totalSpace.mp
        (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
          id z from contMDiffAt_id)).2
      exact h
  -- Forward normal coordinates are the complementary component of the derivative of a smooth chart.
  have hForward (x : M) :
      let h := hmodel x
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, F))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
        (fun z : TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) ↦
          (z.proj, (h.equiv.symm
            (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart (f z.proj) z.snd)).2))
        ((fun z ↦ z.proj) ⁻¹' h.domChart.source) := by
    let h := hmodel x
    dsimp only
    intro z hz
    have hcod := contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      (h.source_subset_preimage_source hz)
    have ht := hcod.contMDiffAt_tangentMap (X := (⟨f z.proj, z.snd⟩ :
      TangentBundle 𝓘(ℝ, F) N)) (m := ∞) (by simp)
    have hv := ((contMDiff_snd_tangentBundle_modelSpace F 𝓘(ℝ, F)).contMDiffAt.comp _ ht).comp z
      (hLift).contMDiffAt
    let P := (ContinuousLinearMap.snd ℝ E (NormalModel E F)).comp
      h.equiv.symm.toContinuousLinearMap
    exact ((Bundle.contMDiffAt_proj ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))).prodMk
      (P.contMDiff.contMDiffAt.comp z hv)).contMDiffWithinAt
  -- The inverse chart derivative gives a smooth representative for every complementary vector.
  have hBackward (x : M) :
      let h := hmodel x
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
        (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        (fun p : M × NormalModel E F ↦
          (⟨p.1, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart.symm
            (h.codChart (f p.1)) (h.equiv (0, p.2))⟩ :
            TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))))
        (h.domChart.source ×ˢ univ) := by
    let h := hmodel x
    dsimp only
    intro p hp
    have hcod := contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      (h.source_subset_preimage_source hp.1)
    have hci := contMDiffAt_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
      (h.codChart.map_source (h.source_subset_preimage_source hp.1))
    let k (q : M × NormalModel E F) : TangentBundle 𝓘(ℝ, F) F :=
      ⟨h.codChart (f q.1), h.equiv (0, q.2)⟩
    have hk : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
        (𝓘(ℝ, F)).tangent ∞ k p :=
      by
        let L := h.equiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ E (NormalModel E F))
        have hfirst : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F) ∞
            (fun q : M × NormalModel E F ↦ h.codChart (f q.1)) p :=
          (hcod.comp p.1 f.contMDiff.contMDiffAt).comp p contMDiffAt_fst
        have hsecond : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F) ∞
            (fun q : M × NormalModel E F ↦ L q.2) p :=
          L.contMDiff.contMDiffAt.comp p contMDiffAt_snd
        apply Bundle.contMDiffAt_totalSpace.mpr
        refine ⟨hfirst, ?_⟩
        simpa only [trivializationAt_model_space_apply, k, L, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe] using hsecond
    have ht := (hci.contMDiffAt_tangentMap (X := k p) (m := ∞) (by simp)).comp p hk
    have htarget : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) (𝓘(ℝ, F)).tangent ∞
        (fun q : M × NormalModel E F ↦
          (⟨f q.1, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart.symm
            (h.codChart (f q.1)) (h.equiv (0, q.2))⟩ : TangentBundle 𝓘(ℝ, F) N)) p := by
      apply ht.congr_of_eventuallyEq
      filter_upwards [(h.domChart.open_source.preimage continuous_fst).mem_nhds hp.1] with q hq
      exact TotalSpace.ext
        (h.codChart.left_inv (h.source_subset_preimage_source hq)).symm (by rfl)
    apply ContMDiffAt.contMDiffWithinAt
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact contMDiffAt_fst
    · exact (Bundle.contMDiffAt_totalSpace.mp htarget).2
  -- Descend through the coinduced quotient topology to obtain linear local trivializations.
  have hTriv (x : M) :
      let h := hmodel x
      ∃ e : Trivialization (NormalModel E F)
          (Bundle.TotalSpace.proj : TotalSpace (NormalModel E F)
            (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) → M),
        e.baseSet = h.domChart.source ∧ e.IsLinear ℝ ∧
        (∀ z : TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))),
          z.proj ∈ h.domChart.source →
          e (normalQuotientMap 𝓘(ℝ, E) 𝓘(ℝ, F) (NormalModel E F) f z) =
            (z.proj, (h.equiv.symm
              (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart (f z.proj) z.snd)).2)) ∧
        (∀ p : M × NormalModel E F, p.1 ∈ h.domChart.source →
          e.toOpenPartialHomeomorph.symm p =
            normalQuotientMap 𝓘(ℝ, E) 𝓘(ℝ, F) (NormalModel E F) f
              ⟨p.1, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart.symm
                (h.codChart (f p.1)) (h.equiv (0, p.2))⟩) := by
    classical
    let h := hmodel x
    let G := NormalModel E F
    let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
    let Q := normalQuotientMap 𝓘(ℝ, E) 𝓘(ℝ, F) G f
    have hQsurj : Function.Surjective Q := by
      rintro ⟨y, v⟩
      obtain ⟨w, rfl⟩ :=
        (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y).toLinearMap).mkQ_surjective v
      exact ⟨⟨y, w⟩, rfl⟩
    have hQ : IsQuotientMap Q := ⟨⟨rfl⟩, hQsurj⟩
    have hproj : Continuous (Bundle.TotalSpace.proj : TotalSpace G V → M) := by
      apply hQ.continuous_iff.mpr
      exact FiberBundle.continuous_proj F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))
    let e (y : M) (hy : y ∈ h.domChart.source) : V y ≃L[ℝ] G :=
      (hFiber x y hy).choose
    have he (y : M) (hy : y ∈ h.domChart.source) :=
      (hFiber x y hy).choose_spec
    let forward (z : TotalSpace G V) : M × G :=
      (z.proj, if hz : z.proj ∈ h.domChart.source then e z.proj hz z.snd else 0)
    let backward (p : M × G) : TotalSpace G V :=
      ⟨p.1, if hp : p.1 ∈ h.domChart.source then (e p.1 hp).symm p.2 else 0⟩
    have hforwardQ (z : TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))
        (hz : z.proj ∈ h.domChart.source) :
        forward (Q z) = (z.proj, (h.equiv.symm
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart (f z.proj) z.snd)).2) := by
      apply Prod.ext
      · rfl
      change (if hz : z.proj ∈ h.domChart.source then
        e z.proj hz ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ z.snd)
          else 0) = _
      rw [dite_eq_left hz]
      exact (he z.proj hz).1 z.snd
    have hbackwardQ (p : M × G) (hp : p.1 ∈ h.domChart.source) : backward p =
        Q ⟨p.1, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart.symm
          (h.codChart (f p.1)) (h.equiv (0, p.2))⟩ := by
      apply congrArg (TotalSpace.mk p.1)
      rw [dite_eq_left hp]
      exact (he p.1 hp).2 p.2
    have hforward : ContinuousOn forward ((fun z ↦ z.proj) ⁻¹' h.domChart.source) := by
      apply (hQ.continuousOn_isOpen_iff (h.domChart.open_source.preimage hproj)).mpr
      exact (hForward x).continuousOn.congr (fun z hz ↦
        hforwardQ z hz)
    have hbackward : ContinuousOn backward (h.domChart.source ×ˢ univ) := by
      exact (hQ.continuous.comp_continuousOn
        (hBackward x).continuousOn).congr (fun p hp ↦
          hbackwardQ p hp.1)
    let t : Trivialization G (Bundle.TotalSpace.proj : TotalSpace G V → M) :=
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
    refine ⟨t, rfl, ?_, hforwardQ, hbackwardQ⟩
    constructor
    intro y hy
    change y ∈ h.domChart.source at hy
    change IsLinearMap ℝ (fun v : V y ↦
      if hh : y ∈ h.domChart.source then e y hh v else 0)
    simp only [dite_eq_left hy]
    exact (e y hy).toLinearMap.isLinear
  -- These same local charts induce precisely the original topology on each quotient fiber.
  have hInducing (x : M) :
      IsInducing (TotalSpace.mk x : NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x →
        TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) := by
    let h := hmodel x
    let t := (hTriv x).choose
    have ht := (hTriv x).choose_spec
    have hx : x ∈ h.domChart.source := h.mem_domChart_source
    let e := (hFiber x x hx).choose
    have he := (hFiber x x hx).choose_spec
    have hmap : (t : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) →
        M × NormalModel E F) ∘ TotalSpace.mk x = fun v ↦ (x, e v) := by
      funext v
      obtain ⟨w, rfl⟩ :=
        (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ_surjective v
      exact (ht.2.2.1 ⟨x, w⟩ hx).trans (Prod.ext rfl (he.1 w).symm)
    have hsource (v : NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x) :
        (⟨x, v⟩ : TotalSpace (NormalModel E F) _) ∈ t.source := by
      apply t.mem_source.mpr
      rwa [ht.1]
    apply isInducing_iff_nhds.mpr
    intro v
    rw [t.nhds_eq_comap_inf_principal (hsource v), Filter.comap_inf,
      Filter.comap_principal, Filter.comap_comap]
    have hpre : (TotalSpace.mk x) ⁻¹' t.source = univ := eq_univ_of_forall hsource
    rw [hpre, Filter.principal_univ, inf_top_eq]
    change 𝓝 v = Filter.comap (t ∘ TotalSpace.mk x) (𝓝 ((t ∘ TotalSpace.mk x) v))
    rw [hmap]
    exact ((isEmbedding_prodMkRight x).isInducing.comp e.toHomeomorph.isInducing).nhds_eq_comap v
  -- Evaluate transitions on vectors, then use finite dimension to obtain operator smoothness.
  have hTransitions (x y : M) :
      let e := (hTriv x).choose
      let e' := (hTriv y).choose
      let := (hTriv x).choose_spec.2.1
      let := (hTriv y).choose_spec.2.1
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, NormalModel E F →L[ℝ] NormalModel E F) ∞
        (fun b ↦ (e.coordChangeL ℝ e' b : NormalModel E F →L[ℝ] NormalModel E F))
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
    have heval (v : NormalModel E F) :
        ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, NormalModel E F) ∞
          (fun q ↦ e.coordChangeL ℝ e' q v) (e.baseSet ∩ e'.baseSet) b := by
      have hb₁ : b ∈ h.domChart.source := he.1 ▸ hb.1
      have hb₂ : b ∈ h'.domChart.source := he'.1 ▸ hb.2
      let lift (q : M) : TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) :=
        ⟨q, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) h.codChart.symm
          (h.codChart (f q)) (h.equiv (0, v))⟩
      have hlift : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ lift b :=
        ((hBackward x).contMDiffAt
          ((h.domChart.open_source.prod isOpen_univ).mem_nhds ⟨hb₁, mem_univ v⟩)).comp b
            (contMDiffAt_id.prodMk contMDiffAt_const)
      have hforward := ((hForward y).contMDiffAt
        ((h'.domChart.open_source.preimage (FiberBundle.continuous_proj F
          ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))).mem_nhds hb₂)).comp b hlift
      apply hforward.snd.contMDiffWithinAt.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin] with q hq
        rw [e.coordChangeL_apply' e' hq v, he.2.2.2 (q, v) (he.1 ▸ hq.1)]
        exact congrArg Prod.snd (he'.2.2.1 (lift q) (he'.1 ▸ hq.2))
      · rw [e.coordChangeL_apply' e' hb v, he.2.2.2 (b, v) hb₁]
        exact congrArg Prod.snd (he'.2.2.1 (lift b) hb₂)
    rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
    apply contDiffWithinAt_clm_apply.mpr
    intro v
    have hv := heval v
    rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
    exact hv
  -- Assemble one atlas and prove the original quotient smooth in that exact selected atlas.
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let G := NormalModel E F
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
  have hlin (t : Trivialization G (Bundle.TotalSpace.proj : TotalSpace G V → M))
      [ht : MemTrivializationAtlas t] : t.IsLinear ℝ := by
    obtain ⟨x, rfl⟩ := ht.out
    exact (he x).2.1
  let := hlin
  have htrans (t t' : Trivialization G (Bundle.TotalSpace.proj : TotalSpace G V → M))
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
  refine ⟨B, W, ⟨htrans⟩, ?_⟩
  intro z
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · exact Bundle.contMDiffAt_proj ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))
  · let h := hmodel z.proj
    have hz : z.proj ∈ h.domChart.source := h.mem_domChart_source
    have hforward := ((hForward z.proj).contMDiffAt
      ((h.domChart.open_source.preimage (FiberBundle.continuous_proj F
        ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))).mem_nhds hz)).snd
    apply hforward.congr_of_eventuallyEq
    filter_upwards [(h.domChart.open_source.preimage (FiberBundle.continuous_proj F
      ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))).mem_nhds hz] with w hw
    exact congrArg Prod.snd ((he z.proj).2.2.1 w hw)

/-- The chosen native atlas comes from the normal-bundle existence theorem. -/
@[reducible]
def normalBundleFiberBundle
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    FiberBundle (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) :=
  (exists_normalBundle_atlas f hf).choose

/-- Linear triviality uses the same selected normal atlas. -/
instance normalBundleVectorBundle
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    letI := normalBundleFiberBundle f hf
    VectorBundle ℝ (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) :=
  (exists_normalBundle_atlas f hf).choose_spec.choose

/-- Smooth transition functions use that atlas and its selected linearity certificate. -/
instance normalBundleContMDiffVectorBundle
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    ContMDiffVectorBundle ∞ (NormalModel E F)
      (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) 𝓘(ℝ, E) :=
  (exists_normalBundle_atlas f hf).choose_spec.choose_spec.1

/-- The actual smooth quotient map, packaged using the same selected normal atlas. -/
def smoothNormalQuotientMap
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    letI := normalBundleFiberBundle f hf
    ContMDiffMap (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
      (TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))
      (TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) ∞ :=
  ⟨normalQuotientMap 𝓘(ℝ, E) 𝓘(ℝ, F) (NormalModel E F) f,
    (exists_normalBundle_atlas f hf).choose_spec.choose_spec.2⟩

open Function in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- A quotient normal bundle has a smooth linear right inverse over a Hausdorff
paracompact base. -/
theorem exists_smooth_normal_rightInverse [T2Space M] [ParacompactSpace M]
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∃ s : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x →L[ℝ] TangentSpace 𝓘(ℝ, F) (f x),
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
          (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
          (fun z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) ↦
            (⟨z.proj, s z.proj z.snd⟩ :
              TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))) ∧
        ∀ x, Function.RightInverse (s x)
          (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ := by
  classical
  -- Keep the selected normal atlas and the native pulled-back tangent bundle throughout.
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let W := ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))
  -- Expose the native fiber algebra for the Hom-bundle APIs without changing its topology.
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
  let G := NormalModel E F
  let Q (y : M) : W y →L[ℝ] V y :=
    (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y).toLinearMap).mkQL
  -- In fixed local frames, a surjective quotient is a smooth family of matrices.
  have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ s : ∀ y, V y →L[ℝ] W y,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
          (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U ∧
        ∀ y, y ∈ U → ∀ v, Q y (s y v) = v := by
    let a := trivializationAt F W x
    let b := trivializationAt G V x
    let A (y : M) : F →L[ℝ] G :=
      (b.continuousLinearMapAt ℝ y).comp ((Q y).comp (a.symmL ℝ y))
    let U := a.baseSet ∩ b.baseSet
    have hU : IsOpen U := a.open_baseSet.inter b.open_baseSet
    have hx : x ∈ U := ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
    have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] G) ∞ A U := by
      intro y hy
      have heval (v : F) : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞
          (fun z ↦ A z v) U y := by
        have hs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
            (fun z ↦ (⟨z, a.symmL ℝ z v⟩ : TotalSpace F W)) y := by
          apply a.contMDiffAt_iff (a.mem_source.mpr hy.1) |>.mpr
          refine ⟨contMDiffAt_id, ?_⟩
          apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
          filter_upwards [a.open_baseSet.mem_nhds hy.1] with z hz
          rw [← a.continuousLinearMapAt_apply_of_mem ℝ hz]
          exact a.continuousLinearMapAt_symmL hz v
        have hq := (smoothNormalQuotientMap f hf).contMDiff.contMDiffAt.comp y hs
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
      obtain ⟨w, hw⟩ :=
        (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ_surjective
          (b.symmL ℝ x v)
      refine ⟨a.continuousLinearMapAt ℝ x w, ?_⟩
      change (b.continuousLinearMapAt ℝ x) (Q x (a.symmL ℝ x
        (a.continuousLinearMapAt ℝ x w))) = v
      erw [a.symmL_continuousLinearMapAt (R := ℝ) hx.1]
      change (b.continuousLinearMapAt ℝ x)
        ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ w) = v
      rw [hw, b.continuousLinearMapAt_symmL hx.2]
    choose R₀ hR₀ using (A x).toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hsurj)
    let R : G →L[ℝ] F := R₀.toContinuousLinearMap
    let C (y : M) : G →L[ℝ] G := (A y).comp R
    have hCx : C x = ContinuousLinearMap.id ℝ G := by
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun L : G →ₗ[ℝ] G ↦ L v) hR₀
    have hC : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] G) ∞ C U :=
      hA.clm_comp contMDiffOn_const
    have hCAt := (hC x hx).contMDiffAt (hU.mem_nhds hx)
    have hinv : (C x).IsInvertible := by
      rw [hCx]
      exact ⟨ContinuousLinearEquiv.refl ℝ G, rfl⟩
    have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (C y).IsInvertible :=
      Filter.inter_mem (hU.mem_nhds hx) (hCAt.continuousAt hinv.eventually_nhds)
    choose U' hsub hU'o hx' using mem_nhds_iff.mp hevent
    let P (y : M) : G →L[ℝ] F := R.comp (C y).inverse
    have hP : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] F) ∞ P U' := by
      intro y hy
      have hCy := (hC y (hsub hy).1).contMDiffAt (hU.mem_nhds (hsub hy).1)
      have hInv := ((hsub hy).2.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp y hCy
      exact (contMDiffAt_const.clm_comp hInv).contMDiffWithinAt
    -- Transport this corrected matrix back through the same two original trivializations.
    let s (y : M) : V y →L[ℝ] W y :=
      (a.symmL ℝ y).comp ((P y).comp (b.continuousLinearMapAt ℝ y))
    let c := b.continuousLinearMap (RingHom.id ℝ) a
    have hs : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U' := by
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
  -- A locally finite supported convex combination glues these actual quotient lifts.
  choose cover hcovero hcover s hs hQs using hlocal
  have hglobal : ∃ a : ∀ x, V x →L[ℝ] W x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun x ↦ TotalSpace.mk' (G →L[ℝ] F) x (a x)) ∧
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
      -- Smooth finitely many small bumps on each compact piece; their supports stay in U i.
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
        (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun x ↦ TotalSpace.mk' (G →L[ℝ] F) x (φ i x • s i x)) :=
      ContMDiffOn.smul_section_of_tsupport (hφsmooth i).contMDiffOn
        (hcovero i) (hφsupport i) (hs i)
    have ht : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun x ↦ TotalSpace.mk' (G →L[ℝ] F) x (t x)) := by
      apply ContMDiff.finsum_section_of_locallyFinite ?_ hterm
      apply hφfinite.subset
      intro i x hx
      exact subset_closure (show φ i x ≠ 0 from fun hz ↦ hx (by simp [hz]))
    have hfinite (x : M) : (support (fun i ↦ φ i x)).Finite :=
      (hφfinite.point_finite x).subset (fun i hi ↦ subset_closure hi)
    -- A positive scalar sum normalizes the lift to a right inverse of the same quotient.
    let w (x : M) : ℝ := ∑ᶠ i, φ i x
    have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w :=
      contMDiff_finsum hφsmooth (hφfinite.subset fun i ↦ subset_closure)
    have hwpos (x : M) : 0 < w x := finsum_pos (fun i ↦ hφnonneg i x) (hφpos x) (hfinite x)
    let a (x : M) : V x →L[ℝ] W x := (w x)⁻¹ • t x
    have ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun x ↦ TotalSpace.mk' (G →L[ℝ] F) x (a x)) :=
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
  exact (ha.comp (contMDiff_proj (F := G) (E := V))).clm_bundle_apply contMDiff_id


end SmoothAtlas

end AtiyahSinger
