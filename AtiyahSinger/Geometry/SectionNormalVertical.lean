/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalBundle
public import AtiyahSinger.Geometry.SmoothBundleQuotientDescent
public import AtiyahSinger.Geometry.VerticalTangentBundle

/-!
# The actual normal bundle of a section

Public module ID: M1358.

For a section of a smooth submersion, the original quotient normal is
canonically the vertical kernel restricted to that section. The forward map
is the original quotient map on each vertical vector; the inverse subtracts
the actual section differential applied to the base differential.

Both directions are smooth for the already selected normal and vertical
atlases. This supplies the normal identification needed for the south section
of a frame sphere, without changing the normal quotient or choosing a metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology verticalTangentTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1800000 in
-- The same native normal and vertical atlases are retained under pullback by the section.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normal quotient of a section is its pulled vertical kernel,
with the original quotient map. -/
theorem exists_section_normal_vertical_equiv
    (q : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hq : IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ q)
    (j : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, E) N M ∞)
    (hj : IsImmersion 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ j) (hsection : ∀ x, q (j x) = x) :
    letI := normalBundleFiberBundle j hj
    letI := normalBundleVectorBundle j hj
    letI := normalBundleContMDiffVectorBundle j hj
    letI := verticalTangentFiberBundle q hq
    letI := verticalTangentVectorBundle q hq
    letI := verticalTangentContMDiffVectorBundle q hq
    let ν := NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, E) j
    let V := ((j : N → M) *ᵖ (VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) q))
    ∃ e : ∀ x, V x ≃L[ℝ] ν x,
      (∀ x v, e x v =
        (LinearMap.range (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) j x).toLinearMap).mkQ v.val) ∧
      (∀ (x : N) (w : TangentSpace 𝓘(ℝ, E) (j x)),
        ((e x).symm ((LinearMap.range
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) j x).toLinearMap).mkQ w)).val =
            w - mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) j x (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) q (j x) w)) ∧
      ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, VerticalTangentModel E F))
        (𝓘(ℝ, F).prod 𝓘(ℝ, NormalModel F E)) ∞
        (fun z : TotalSpace (VerticalTangentModel E F) V ↦
          (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (NormalModel F E) ν)) ∧
      ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, NormalModel F E))
        (𝓘(ℝ, F).prod 𝓘(ℝ, VerticalTangentModel E F)) ∞
        (fun z : TotalSpace (NormalModel F E) ν ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace (VerticalTangentModel E F) V)) := by
  classical
  let := normalBundleFiberBundle j hj
  let := normalBundleVectorBundle j hj
  let := normalBundleContMDiffVectorBundle j hj
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let ν := NormalBundle J I j
  let K := VerticalTangentFiber I J q
  let V := (j : N → M) *ᵖ K
  let (x : N) : AddCommGroup (V x) := by
    change AddCommGroup (K (j x))
    infer_instance
  let (x : N) : Module ℝ (V x) := by
    change Module ℝ (K (j x))
    infer_instance
  let (x : N) : IsTopologicalAddGroup (V x) := by
    change IsTopologicalAddGroup (K (j x))
    infer_instance
  let (x : N) : ContinuousSMul ℝ (V x) := by
    change ContinuousSMul ℝ (K (j x))
    infer_instance
  let (x : N) : T2Space (V x) := by
    change T2Space (K (j x))
    infer_instance
  let (x : N) : FiniteDimensional ℝ (V x) := by
    change FiniteDimensional ℝ (K (j x))
    infer_instance
  let W := (j : N → M) *ᵖ (TangentSpace I)
  let A (x : N) : F →L[ℝ] E := mfderiv J I j x
  let B (x : N) : E →L[ℝ] F := mfderiv I J q (j x)
  let Q (x : N) : E →L[ℝ] ν x := (LinearMap.range (A x).toLinearMap).mkQL
  have hBA (x : N) (v : F) : B x (A x v) = v := by
    have hf : (q : M → N) ∘ j = id := funext hsection
    have hd := mfderiv_comp x (q.contMDiff.mdifferentiable (by simp) _)
      (j.contMDiff.mdifferentiable (by simp) x)
    rw [hf, mfderiv_id] at hd
    exact (DFunLike.congr_fun hd v).symm
  let L (x : N) : V x →L[ℝ] ν x :=
    (Q x).comp (LinearMap.ker (B x).toLinearMap).subtypeL
  -- Removing the section component gives the unique vertical representative of a normal class.
  have hbij (x : N) : Bijective (L x) := by
    constructor
    · apply (injective_iff_map_eq_zero (L x)).mpr
      intro v hv
      have hm : v.val ∈ LinearMap.range (A x).toLinearMap :=
        (Submodule.Quotient.mk_eq_zero _).mp hv
      obtain ⟨w, hw⟩ := hm
      have hz : w = 0 := by
        calc
          w = B x (A x w) := (hBA x w).symm
          _ = B x v.val := congrArg (B x) hw
          _ = 0 := v.property
      apply Subtype.ext
      exact hw.symm.trans (by rw [hz, map_zero]; rfl)
    · intro v
      obtain ⟨w, rfl⟩ := (LinearMap.range (A x).toLinearMap).mkQ_surjective v
      refine ⟨⟨w - A x (B x w), ?_⟩, ?_⟩
      · change B x (w - A x (B x w)) = 0
        rw [map_sub, hBA, sub_self]
      · change Q x (w - A x (B x w)) = Q x w
        rw [map_sub]
        have hz : Q x (A x (B x w)) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr ⟨B x w, rfl⟩
        rw [hz, sub_zero]
  let e (x : N) : V x ≃L[ℝ] ν x :=
    (LinearEquiv.ofBijective (L x).toLinearMap (hbij x)).toContinuousLinearEquiv
  have he (x : N) (v : V x) : e x v = Q x v.val := rfl
  have hinverse (x : N) (w : E) : ((e x).symm (Q x w)).val = w - A x (B x w) := by
    let v : V x := ⟨w - A x (B x w), by
      change B x (w - A x (B x w)) = 0
      rw [map_sub, hBA, sub_self]⟩
    have hv : e x v = Q x w := by
      rw [he]
      change Q x (w - A x (B x w)) = Q x w
      rw [map_sub]
      have hz : Q x (A x (B x w)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨B x w, rfl⟩
      rw [hz, sub_zero]
    rw [← hv, (e x).symm_apply_apply]
  -- Pull back the original smooth vertical inclusion, then use the original normal quotient.
  have hlift : ContMDiff (J.prod 𝓘(ℝ, VerticalTangentModel E F))
      (I.prod 𝓘(ℝ, VerticalTangentModel E F)) ∞
      (fun z : TotalSpace (VerticalTangentModel E F) V ↦
        (⟨j z.proj, z.snd⟩ : TotalSpace (VerticalTangentModel E F) K)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨j.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj V), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (J.prod 𝓘(ℝ, VerticalTangentModel E F))
        (J.prod 𝓘(ℝ, VerticalTangentModel E F)) ∞ id z from contMDiffAt_id)).2
  have hinc : ContMDiff (J.prod 𝓘(ℝ, VerticalTangentModel E F)) (J.prod 𝓘(ℝ, E)) ∞
      (fun z : TotalSpace (VerticalTangentModel E F) V ↦
        (⟨z.proj, z.snd.val⟩ : TotalSpace E W)) := by
    have hi := (smoothVerticalTangentInclusion q hq).contMDiff.comp hlift
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨Bundle.contMDiffAt_proj V, (Bundle.contMDiffAt_totalSpace.mp (hi z)).2⟩
  have he_smooth : ContMDiff (J.prod 𝓘(ℝ, VerticalTangentModel E F))
      (J.prod 𝓘(ℝ, NormalModel F E)) ∞
      (fun z : TotalSpace (VerticalTangentModel E F) V ↦
        (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (NormalModel F E) ν)) :=
    (smoothNormalQuotientMap j hj).contMDiff.comp hinc
  refine ⟨e, he, hinverse, he_smooth, ?_⟩
  -- The inverse is smooth by descent through this same fiberwise bijective smooth map.
  apply contMDiff_bundleMap_of_comp_surjective
    (fun x ↦ (e x).toContinuousLinearMap) (fun x ↦ (e x).symm.toContinuousLinearMap)
    he_smooth (fun x ↦ (e x).surjective)
  apply contMDiff_id.congr
  intro z
  change (⟨z.proj, (e z.proj).symm (e z.proj z.snd)⟩ :
    TotalSpace (VerticalTangentModel E F) V) = z
  rw [(e z.proj).symm_apply_apply]

end AtiyahSinger
