/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalBundle
public import AtiyahSinger.Geometry.SmoothBundleQuotientDescent

/-!
# Normal quotients in a transverse pullback square

Public module ID: M1502.

The differential of the ambient map in a smooth commuting square induces an
isomorphism of the actual normal bundles when its range preimage is the source
tangent range and its image spans the ambient tangent space modulo the target
tangent range. These are the linear pullback and transversality conditions.

Both directions are smooth in the selected quotient atlases. Smoothness descends
through the original surjective normal quotient map; applying the same descent
criterion to the resulting fiber equivalence proves smoothness of its inverse.
The explicit representative formula fixes the normal identification and its sign.

This standard transverse normal-bundle comparison is used for parameter slices
and the zero-parameter-velocity square of a tangent embedding.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {M N P Q : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold 𝓘(ℝ, H) ∞ Q]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A transverse smooth pullback square identifies the original normal quotient bundles. -/
theorem exists_transverse_normalPullback_equiv
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, G) 𝓘(ℝ, H) P Q ∞)
    (i : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
    (j : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, H) N Q ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsImmersion 𝓘(ℝ, G) 𝓘(ℝ, H) ∞ g)
    (hcomm : ∀ x, j (f x) = g (i x))
    (hpreimage : ∀ (x : M) (v : F),
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f x) v ∈
          LinearMap.range (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x)).toLinearMap ↔
        v ∈ LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap)
    (hspan : ∀ x : M,
      let A : F →L[ℝ] H := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f x)
      let B : G →L[ℝ] H := mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x)
      ∀ w : H, ∃ (v : F) (u : G), w = A v + B u) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    letI := normalBundleFiberBundle g hg
    letI := normalBundleVectorBundle g hg
    letI := normalBundleContMDiffVectorBundle g hg
    ∃ e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ]
        NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x),
      (∀ (x : M) (v : F),
        e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
          (LinearMap.range (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x)).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f x) v)) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel G H)) ∞
        (fun z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) ↦
          (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (NormalModel G H)
            ((i : M → P) *ᵖ (NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g)))) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel G H))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
        (fun z : TotalSpace (NormalModel G H)
            ((i : M → P) *ᵖ (NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g)) ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ :
            TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))) := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := normalBundleFiberBundle g hg
  let := normalBundleVectorBundle g hg
  let := normalBundleContMDiffVectorBundle g hg
  let Vf := NormalModel E F
  let Vg := NormalModel G H
  let νf := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νg := NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g
  let νi := (i : M → P) *ᵖ νg
  let Wf := (f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))
  let Wg := (g : P → Q) *ᵖ (TangentSpace 𝓘(ℝ, H))
  -- Keep the original pullback algebra and its native topology explicit for smooth descent.
  let (x : M) : AddCommGroup (νi x) := by
    change AddCommGroup (νg (i x))
    infer_instance
  let (x : M) : Module ℝ (νi x) := by
    change Module ℝ (νg (i x))
    infer_instance
  let (x : M) : IsTopologicalAddGroup (νi x) := by
    change IsTopologicalAddGroup (νg (i x))
    infer_instance
  let (x : M) : ContinuousSMul ℝ (νi x) := by
    change ContinuousSMul ℝ (νg (i x))
    infer_instance
  let (x : M) : AddCommGroup (Wf x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : Module ℝ (Wf x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : IsTopologicalAddGroup (Wf x) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : ContinuousSMul ℝ (Wf x) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : T2Space (νi x) := by
    change T2Space (νg (i x))
    infer_instance
  let A (x : M) : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  let B (x : M) : G →L[ℝ] H := mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x)
  let J (x : M) : F →L[ℝ] H := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f x)
  let qf (x : M) : F →L[ℝ] νf x := (LinearMap.range (A x).toLinearMap).mkQL
  let qg (x : M) : H →L[ℝ] νi x := (LinearMap.range (B x).toLinearMap).mkQL
  -- The range-preimage condition descends J to an injective quotient map.
  have hwell (x : M) : LinearMap.range (A x).toLinearMap ≤ ((qg x).comp (J x)).ker := by
    intro v hv
    change (LinearMap.range (B x).toLinearMap).mkQ (J x v) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (hpreimage x v).mpr hv
  let D (x : M) : νf x →L[ℝ] νi x :=
    (LinearMap.range (A x).toLinearMap).liftQL ((qg x).comp (J x)) (hwell x)
  have hD (x : M) (v : F) : D x (qf x v) = qg x (J x v) := rfl
  have hbij (x : M) : Function.Bijective (D x) := by
    constructor
    · apply (injective_iff_map_eq_zero (D x)).mpr
      intro w hw
      obtain ⟨v, rfl⟩ := (LinearMap.range (A x).toLinearMap).mkQ_surjective w
      change (LinearMap.range (B x).toLinearMap).mkQ (J x v) = 0 at hw
      change (LinearMap.range (A x).toLinearMap).mkQ v = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (hpreimage x v).mp ((Submodule.Quotient.mk_eq_zero _).mp hw)
    · intro w
      obtain ⟨v, rfl⟩ := (LinearMap.range (B x).toLinearMap).mkQ_surjective w
      obtain ⟨u, a, ha⟩ := hspan x v
      refine ⟨qf x u, ?_⟩
      rw [hD]
      have hzero : qg x (B x a) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
      change qg x (J x u) = qg x v
      change v = J x u + B x a at ha
      rw [ha, map_add, hzero, add_zero]
  let e (x : M) : νf x ≃L[ℝ] νi x :=
    (LinearEquiv.ofBijective (D x).toLinearMap (hbij x)).toContinuousLinearEquiv
  have hQf : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
      (fun z : TotalSpace F Wf ↦ (⟨z.proj, qf z.proj z.snd⟩ : TotalSpace Vf νf)) :=
    (smoothNormalQuotientMap f hf).contMDiff
  have hLift : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, F)).tangent ∞
      (fun z : TotalSpace F Wf ↦
        (⟨f z.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, F) N)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj Wf), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        id z from contMDiffAt_id)).2
  have hTJ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, H)).tangent ∞
      (fun z : TotalSpace F Wf ↦
        (⟨g (i z.proj), J z.proj z.snd⟩ : TangentBundle 𝓘(ℝ, H) Q)) := by
    apply ((j.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hLift).congr
    intro z
    change (⟨g (i z.proj), J z.proj z.snd⟩ : TangentBundle 𝓘(ℝ, H) Q) =
      ⟨j (f z.proj), J z.proj z.snd⟩
    exact TotalSpace.ext (hcomm z.proj).symm (heq_of_eq rfl)
  have hraw : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, G).prod 𝓘(ℝ, H)) ∞
      (fun z : TotalSpace F Wf ↦ (⟨i z.proj, J z.proj z.snd⟩ : TotalSpace H Wg)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨i.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj Wf),
      (Bundle.contMDiffAt_totalSpace.mp (hTJ z)).2⟩
  have hQgJ := (smoothNormalQuotientMap g hg).contMDiff.comp hraw
  have hDQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : TotalSpace F Wf ↦ (⟨z.proj, D z.proj (qf z.proj z.snd)⟩ :
        TotalSpace Vg νi)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj Wf, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp (hQgJ z)).2
  have hforward : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : TotalSpace Vf νf ↦ (⟨z.proj, e z.proj z.snd⟩ : TotalSpace Vg νi)) :=
    contMDiff_bundleMap_of_comp_surjective (F := F) (G := Vf) (H := Vg)
      (W := Wf) (V₀ := νf) (Z := νi) qf D hQf
      (fun x ↦ (LinearMap.range (A x).toLinearMap).mkQ_surjective) hDQ
  have hinverse : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
      (fun z : TotalSpace Vg νi ↦ (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace Vf νf)) := by
    apply contMDiff_bundleMap_of_comp_surjective (F := Vf) (G := Vg) (H := Vf)
      (W := νf) (V₀ := νi) (Z := νf)
      (fun x ↦ (e x).toContinuousLinearMap) (fun x ↦ (e x).symm.toContinuousLinearMap)
      hforward (fun x ↦ (e x).surjective)
    convert (contMDiff_id : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞ (id : TotalSpace Vf νf → TotalSpace Vf νf)) using 1
    funext z
    exact congrArg (TotalSpace.mk z.proj) ((e z.proj).symm_apply_apply z.snd)
  exact ⟨e, hD, hforward, hinverse⟩

end AtiyahSinger
