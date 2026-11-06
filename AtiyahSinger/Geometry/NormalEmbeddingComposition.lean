/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalBundle
public import AtiyahSinger.Geometry.SmoothBundleQuotientDescent

/-!
# The actual normal sequence of successive smooth embeddings

Public module ID: M1309.

For the specified smooth immersions, the derivative of the second map induces
an injection of the first normal into the composite normal. The original
quotient to the second normal gives its cokernel. A smooth splitting of the
second normal quotient produces a splitting of this short exact sequence,
with the first normal preceding the pulled-back second normal.

All fibers are the original derivative cokernels and all smoothness statements
use their selected quotient atlases. The resulting real splitting is the input
to complexification in the tangent pushforward composition law. Sources:
SG III.12 and Karoubi IV.5.19--5.22; the actual quotient and splitting formulas
are the required geometric supplement to those composition arguments.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsImmersion 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)
  (hgf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (g.comp f))

local notation "νf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νg" => NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g
local notation "νgf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f)
local notation "νgP" => ((f : M → N) *ᵖ νg)
local notation "Vf" => NormalModel E F
local notation "Vg" => NormalModel F G
local notation "Vgf" => NormalModel E G

/-- The original normal short exact sequence with a smooth, ordered, normalized splitting. -/
structure NormalEmbeddingCompositionSplitting where
  /-- The map induced by the actual derivative of g. -/
  injection : ∀ x, νf x →L[ℝ] νgf x
  /-- The original quotient to the pulled-back second normal. -/
  projection : ∀ x, νgf x →L[ℝ] νg (f x)
  /-- The ordered comparison with first normal followed by the pulled-back second normal. -/
  equiv : ∀ x, νgf x ≃L[ℝ] (νf x × νg (f x))
  /-- The injection retains the actual tangent representative. -/
  injection_apply : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, F) (f x)),
    injection x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) x).toLinearMap).mkQ
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f x) v)
  /-- The projection retains the same tangent vector in the second quotient. -/
  projection_apply : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, G) (g (f x))),
    projection x
        ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) x).toLinearMap).mkQ v) =
      (LinearMap.range (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f x)).toLinearMap).mkQ v
  /-- Both end maps and exactness are those of the specified quotient sequence. -/
  exact : ∀ x, Function.Injective (injection x) ∧ Function.Surjective (projection x) ∧
    LinearMap.range (injection x).toLinearMap = LinearMap.ker (projection x).toLinearMap
  /-- The injection is smooth in the original normal atlases. -/
  contMDiff_injection :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    letI := normalBundleFiberBundle g hg
    letI := normalBundleVectorBundle g hg
    letI := normalBundleContMDiffVectorBundle g hg
    letI := normalBundleFiberBundle (g.comp f) hgf
    letI := normalBundleVectorBundle (g.comp f) hgf
    letI := normalBundleContMDiffVectorBundle (g.comp f) hgf
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf)) ∞
      (fun z : TotalSpace Vf νf ↦
        (⟨z.proj, injection z.proj z.snd⟩ : TotalSpace Vgf νgf))
  /-- The projection is smooth in the original quotient and pullback atlases. -/
  contMDiff_projection :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    letI := normalBundleFiberBundle g hg
    letI := normalBundleVectorBundle g hg
    letI := normalBundleContMDiffVectorBundle g hg
    letI := normalBundleFiberBundle (g.comp f) hgf
    letI := normalBundleVectorBundle (g.comp f) hgf
    letI := normalBundleContMDiffVectorBundle (g.comp f) hgf
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : TotalSpace Vgf νgf ↦
        (⟨z.proj, projection z.proj z.snd⟩ : TotalSpace Vg νgP))
  /-- The forward splitting is smooth on the actual normal total spaces. -/
  contMDiff_toFun :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    letI := normalBundleFiberBundle g hg
    letI := normalBundleVectorBundle g hg
    letI := normalBundleContMDiffVectorBundle g hg
    letI := normalBundleFiberBundle (g.comp f) hgf
    letI := normalBundleVectorBundle (g.comp f) hgf
    letI := normalBundleContMDiffVectorBundle (g.comp f) hgf
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, (Vf × Vg))) ∞
      (fun z : TotalSpace Vgf νgf ↦
        (⟨z.proj, equiv z.proj z.snd⟩ : TotalSpace (Vf × Vg) (νf ×ᵇ νgP)))
  /-- The inverse splitting is smooth on those same total spaces. -/
  contMDiff_invFun :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    letI := normalBundleFiberBundle g hg
    letI := normalBundleVectorBundle g hg
    letI := normalBundleContMDiffVectorBundle g hg
    letI := normalBundleFiberBundle (g.comp f) hgf
    letI := normalBundleVectorBundle (g.comp f) hgf
    letI := normalBundleContMDiffVectorBundle (g.comp f) hgf
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, (Vf × Vg)))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf)) ∞
      (fun z : TotalSpace (Vf × Vg) (νf ×ᵇ νgP) ↦
        (⟨z.proj, (equiv z.proj).symm z.snd⟩ : TotalSpace Vgf νgf))
  /-- The second coordinate is exactly the original normal projection. -/
  snd_equiv : ∀ (x : M) (v : νgf x), (equiv x v).2 = projection x v
  /-- The canonical injection occupies the first factor with positive sign. -/
  equiv_injection : ∀ (x : M) (v : νf x), equiv x (injection x v) = (v, 0)

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Quotient descent and the smooth inverse keep the same native atlases throughout.
/-- The specified smooth quotient right inverse determines the actual composite normal splitting. -/
theorem exists_normalEmbeddingCompositionSplitting_of_rightInverse
    (s₀ : ∀ y : N, νg y →L[ℝ] TangentSpace 𝓘(ℝ, G) (g y))
    (hs₀ :
      letI := normalBundleFiberBundle g hg
      letI := normalBundleVectorBundle g hg
      letI := normalBundleContMDiffVectorBundle g hg
      ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, Vg)) (𝓘(ℝ, F).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace Vg νg ↦
          (⟨z.proj, s₀ z.proj z.snd⟩ : TotalSpace G ((g : N → P) *ᵖ
            (TangentSpace 𝓘(ℝ, G))))))
    (hqs₀ : ∀ (y : N) (v : νg y),
      (LinearMap.range (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g y).toLinearMap).mkQ (s₀ y v) = v) :
    ∃ S : NormalEmbeddingCompositionSplitting f g hf hg hgf,
      ∀ (x : M) (u : νf x) (v : νg (f x)),
        (S.equiv x).symm (u, v) = S.injection x u +
          (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) x).toLinearMap).mkQ
            (s₀ (f x) v) := by
  classical
  -- Local smooth quotient descent preserves the actual normal atlas without choosing a metric.
  -- The chain rule makes both maps descend from the original tangent representatives.
  let a (x : M) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  let b (x : M) := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f x)
  let c (x : M) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) x
  have hchain (x : M) : c x = (b x).comp (a x) :=
    mfderiv_comp x (g.contMDiff.mdifferentiable (by simp) (f x))
      (f.contMDiff.mdifferentiable (by simp) x)
  let qf (x : M) := (LinearMap.range (a x).toLinearMap).mkQL
  let qg (x : M) := (LinearMap.range (b x).toLinearMap).mkQL
  let qgf (x : M) := (LinearMap.range (c x).toLinearMap).mkQL
  have hiwell (x : M) : LinearMap.range (a x).toLinearMap ≤ ((qgf x).comp (b x)).ker := by
    rintro _ ⟨v, rfl⟩
    change qgf x (b x (a x v)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨v, DFunLike.congr_fun (hchain x) v⟩
  have hpwell (x : M) : LinearMap.range (c x).toLinearMap ≤ (qg x).ker := by
    rintro _ ⟨v, rfl⟩
    change qg x (c x v) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨a x v, (DFunLike.congr_fun (hchain x) v).symm⟩
  let i (x : M) := (LinearMap.range (a x).toLinearMap).liftQL
    ((qgf x).comp (b x)) (hiwell x)
  let p (x : M) := (LinearMap.range (c x).toLinearMap).liftQL (qg x) (hpwell x)
  have hi (x : M) (v : TangentSpace 𝓘(ℝ, F) (f x)) :
      i x (qf x v) = qgf x (b x v) := rfl
  have hp (x : M) (v : TangentSpace 𝓘(ℝ, G) (g (f x))) :
      p x (qgf x v) = qg x v := rfl
  have hinj (x : M) : Function.Injective (i x) := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro u hu
    obtain ⟨v, rfl⟩ := (LinearMap.range (a x).toLinearMap).mkQ_surjective u
    have hzero : qgf x (b x v) = 0 := LinearMap.mem_ker.mp hu
    obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
    have hw' : a x w = v := hg.mfderiv_injective (by simp) (f x) (by
      change b x (a x w) = b x v
      exact (DFunLike.congr_fun (hchain x) w).symm.trans hw)
    change qf x v = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hw'⟩
  have hsurj (x : M) : Function.Surjective (p x) := by
    intro u
    obtain ⟨v, rfl⟩ := (LinearMap.range (b x).toLinearMap).mkQ_surjective u
    exact ⟨qgf x v, rfl⟩
  have hexact (x : M) :
      LinearMap.range (i x).toLinearMap = LinearMap.ker (p x).toLinearMap := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      obtain ⟨v, rfl⟩ := (LinearMap.range (a x).toLinearMap).mkQ_surjective u
      change qg x (b x v) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
    · intro u hu
      obtain ⟨v, rfl⟩ := (LinearMap.range (c x).toLinearMap).mkQ_surjective u
      have hzero : qg x v = 0 := LinearMap.mem_ker.mp hu
      obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
      exact ⟨qf x w, (hi x w).trans (congrArg (qgf x) hw)⟩
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := normalBundleFiberBundle g hg
  let := normalBundleVectorBundle g hg
  let := normalBundleContMDiffVectorBundle g hg
  let := normalBundleFiberBundle (g.comp f) hgf
  let := normalBundleVectorBundle (g.comp f) hgf
  let := normalBundleContMDiffVectorBundle (g.comp f) hgf
  let Wf := ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))
  let Wg := ((g : N → P) *ᵖ (TangentSpace 𝓘(ℝ, G)))
  let Wgf := ((g.comp f : M → P) *ᵖ (TangentSpace 𝓘(ℝ, G)))
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
  let (x : N) : AddCommGroup (Wg x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, G) (g x))
    infer_instance
  let (x : N) : Module ℝ (Wg x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, G) (g x))
    infer_instance
  let (x : N) : IsTopologicalAddGroup (Wg x) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, G) (g x))
    infer_instance
  let (x : N) : ContinuousSMul ℝ (Wg x) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, G) (g x))
    infer_instance
  let (x : M) : AddCommGroup (Wgf x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, G) ((g.comp f) x))
    infer_instance
  let (x : M) : Module ℝ (Wgf x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, G) ((g.comp f) x))
    infer_instance
  let (x : M) : IsTopologicalAddGroup (Wgf x) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, G) ((g.comp f) x))
    infer_instance
  let (x : M) : ContinuousSMul ℝ (Wgf x) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, G) ((g.comp f) x))
    infer_instance
  let (x : M) : AddCommGroup (νgP x) := by
    change AddCommGroup (νg (f x))
    infer_instance
  let (x : M) : Module ℝ (νgP x) := by
    change Module ℝ (νg (f x))
    infer_instance
  let (x : M) : IsTopologicalAddGroup (νgP x) := by
    change IsTopologicalAddGroup (νg (f x))
    infer_instance
  let (x : M) : ContinuousSMul ℝ (νgP x) := by
    change ContinuousSMul ℝ (νg (f x))
    infer_instance
  have hqf : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
      (fun z : TotalSpace F Wf ↦ (⟨z.proj, qf z.proj z.snd⟩ : TotalSpace Vf νf)) :=
    (smoothNormalQuotientMap f hf).contMDiff
  have hqgf : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf)) ∞
      (fun z : TotalSpace G Wgf ↦ (⟨z.proj, qgf z.proj z.snd⟩ : TotalSpace Vgf νgf)) :=
    (smoothNormalQuotientMap (g.comp f) hgf).contMDiff
  have hqg : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : TotalSpace G Wgf ↦ (⟨z.proj, qg z.proj z.snd⟩ : TotalSpace Vg νgP)) := by
    have hLift : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G))
        (𝓘(ℝ, F).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace G Wgf ↦ (⟨f z.proj, z.snd⟩ : TotalSpace G Wg)) := by
      intro z
      apply Bundle.contMDiffAt_totalSpace.mpr
      refine ⟨f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj Wgf), ?_⟩
      exact (Bundle.contMDiffAt_totalSpace.mp
        (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, G))
          (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞ id z from contMDiffAt_id)).2
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj Wgf, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (((smoothNormalQuotientMap g hg).contMDiff.comp hLift) z)).2
  have hblift : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, F).prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace F Wf ↦ (⟨f z.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, F) N)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj Wf), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, F))
        (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ id z from contMDiffAt_id)).2
  have hbsmooth : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace F Wf ↦ (⟨z.proj, b z.proj z.snd⟩ : TotalSpace G Wgf)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj Wf, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      ((g.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hblift).contMDiffAt).2
  have hismooth : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf)) ∞
      (fun z : TotalSpace Vf νf ↦ (⟨z.proj, i z.proj z.snd⟩ : TotalSpace Vgf νgf)) := by
    apply contMDiff_bundleMap_of_comp_surjective (F := F) (G := Vf) (H := Vgf)
      (W := Wf) (V₀ := νf) (Z := νgf) qf i hqf
      (fun x ↦ (LinearMap.range (a x).toLinearMap).mkQ_surjective)
    exact (hqgf.comp hbsmooth).congr (fun z ↦ congrArg
      (fun v ↦ (⟨z.proj, v⟩ : TotalSpace Vgf νgf)) (hi z.proj z.snd))
  have hpsmooth : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : TotalSpace Vgf νgf ↦ (⟨z.proj, p z.proj z.snd⟩ : TotalSpace Vg νgP)) := by
    apply contMDiff_bundleMap_of_comp_surjective (F := G) (G := Vgf) (H := Vg)
      (W := Wgf) (V₀ := νgf) (Z := νgP) qgf p hqgf
      (fun x ↦ (LinearMap.range (c x).toLinearMap).mkQ_surjective)
    exact hqg
  -- The supplied right inverse for the second normal quotient gives this exact splitting.
  let s (x : M) := (qgf x).comp (s₀ (f x))
  have hps (x : M) (v : νg (f x)) : p x (s x v) = v :=
    (hp x (s₀ (f x) v)).trans (hqs₀ (f x) v)
  have hsLift : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vg))
      (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace Vg νgP ↦ (⟨z.proj, s₀ (f z.proj) z.snd⟩ : TotalSpace G Wgf)) := by
    have hLift : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vg))
        (𝓘(ℝ, F).prod 𝓘(ℝ, Vg)) ∞
        (fun z : TotalSpace Vg νgP ↦ (⟨f z.proj, z.snd⟩ : TotalSpace Vg νg)) := by
      intro z
      apply Bundle.contMDiffAt_totalSpace.mpr
      refine ⟨f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj νgP), ?_⟩
      exact (Bundle.contMDiffAt_totalSpace.mp
        (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, Vg))
          (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞ id z from contMDiffAt_id)).2
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj νgP, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp ((hs₀.comp hLift) z)).2
  have hssmooth : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vg))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf)) ∞
      (fun z : TotalSpace Vg νgP ↦ (⟨z.proj, s z.proj z.snd⟩ : TotalSpace Vgf νgf)) :=
    hqgf.comp hsLift
  -- Exactness and the same right inverse give the ordered real comparison.
  let A (x : M) : (νf x × νg (f x)) →L[ℝ] νgf x :=
    (i x).comp (ContinuousLinearMap.fst ℝ _ _) +
      (s x).comp (ContinuousLinearMap.snd ℝ _ _)
  have hpiv (x : M) (v : νf x) : p x (i x v) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [← hexact x]
    exact ⟨v, rfl⟩
  have hpA (x : M) (u : νf x × νg (f x)) : p x (A x u) = u.2 := by
    change p x (i x u.1 + s x u.2) = u.2
    rw [map_add, hpiv, hps, zero_add]
  have hA (x : M) : Function.Bijective (A x) := by
    constructor
    · intro u v huv
      have hsnd : u.2 = v.2 := by simpa only [hpA] using congrArg (p x) huv
      have hfst : u.1 = v.1 := by
        apply hinj x
        change i x u.1 + s x u.2 = i x v.1 + s x v.2 at huv
        rw [hsnd] at huv
        exact add_right_cancel huv
      exact Prod.ext hfst hsnd
    · intro w
      have hker : w - s x (p x w) ∈ LinearMap.ker (p x).toLinearMap := by
        change p x (w - s x (p x w)) = 0
        rw [map_sub, hps, sub_self]
      rw [← hexact x] at hker
      obtain ⟨v, hv⟩ := hker
      change i x v = w - s x (p x w) at hv
      refine ⟨(v, p x w), ?_⟩
      change i x v + s x (p x w) = w
      rw [hv, sub_add_cancel]
  let e (x : M) : νgf x ≃L[ℝ] (νf x × νg (f x)) :=
    (LinearEquiv.ofBijective (A x).toLinearMap (hA x)).toContinuousLinearEquiv.symm
  have hAe (x : M) (v : νf x × νg (f x)) : A x v = (e x).symm v := rfl
  have hesnd (x : M) (v : νgf x) : (e x v).2 = p x v := by
    have h := congrArg (p x) ((e x).symm_apply_apply v)
    change p x (A x (e x v)) = p x v at h
    rwa [hpA] at h
  have hein (x : M) (v : νf x) : e x (i x v) = (v, 0) := by
    apply (e x).symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply, ← hAe]
    change i x v = i x v + s x 0
    rw [map_zero, add_zero]
  -- Smoothness of the inverse uses the original direct sum and its two canonical projections.
  have hfst : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf × Vg))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
      (fun z : TotalSpace (Vf × Vg) (νf ×ᵇ νgP) ↦
        (⟨z.proj, z.snd.1⟩ : TotalSpace Vf νf)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj (νf ×ᵇ νgP), ?_⟩
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, Vf × Vg))
        (𝓘(ℝ, E).prod 𝓘(ℝ, Vf × Vg)) ∞ id z from contMDiffAt_id)).2
    exact (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Vf × Vg → Vf)).contDiffAt.comp_contMDiffAt hc
  have hsnd : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf × Vg))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : TotalSpace (Vf × Vg) (νf ×ᵇ νgP) ↦
        (⟨z.proj, z.snd.2⟩ : TotalSpace Vg νgP)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj (νf ×ᵇ νgP), ?_⟩
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, Vf × Vg))
        (𝓘(ℝ, E).prod 𝓘(ℝ, Vf × Vg)) ∞ id z from contMDiffAt_id)).2
    exact (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Vf × Vg → Vg)).contDiffAt.comp_contMDiffAt hc
  have hAsmooth : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf × Vg))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf)) ∞
      (fun z : TotalSpace (Vf × Vg) (νf ×ᵇ νgP) ↦
        (⟨z.proj, A z.proj z.snd⟩ : TotalSpace Vgf νgf)) := by
    intro z
    have h₁ := ((hismooth.comp hfst) z)
    have h₂ := ((hssmooth.comp hsnd) z)
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj (νf ×ᵇ νgP), ?_⟩
    have hc₁ := (Bundle.contMDiffAt_totalSpace.mp h₁).2
    have hc₂ := (Bundle.contMDiffAt_totalSpace.mp h₂).2
    apply (hc₁.add hc₂).congr_of_eventuallyEq
    let t := trivializationAt Vgf νgf z.proj
    filter_upwards [(FiberBundle.continuous_proj (Vf × Vg)
      (νf ×ᵇ νgP)).continuousAt.preimage_mem_nhds
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with w hw
    change (t ⟨w.proj, i w.proj w.snd.1 + s w.proj w.snd.2⟩).2 =
      (t ⟨w.proj, i w.proj w.snd.1⟩).2 + (t ⟨w.proj, s w.proj w.snd.2⟩).2
    rw [← t.continuousLinearMapAt_apply_of_mem ℝ hw,
      ← t.continuousLinearMapAt_apply_of_mem ℝ hw,
      ← t.continuousLinearMapAt_apply_of_mem ℝ hw, map_add]
  have hforward : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vgf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vf × Vg)) ∞
      (fun z : TotalSpace Vgf νgf ↦
        (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (Vf × Vg) (νf ×ᵇ νgP))) := by
    apply contMDiff_bundleMap_of_comp_surjective (F := Vf × Vg) (G := Vgf) (H := Vf × Vg)
      (W := νf ×ᵇ νgP) (V₀ := νgf) (Z := νf ×ᵇ νgP) A
      (fun x ↦ (e x).toContinuousLinearMap) hAsmooth
    · exact fun x ↦ (hA x).2
    · apply contMDiff_id.congr
      intro z
      exact congrArg (fun v ↦ (⟨z.proj, v⟩ : TotalSpace (Vf × Vg) (νf ×ᵇ νgP)))
        ((e z.proj).apply_symm_apply z.snd)
  refine ⟨{
    injection := i
    projection := p
    equiv := e
    injection_apply := hi
    projection_apply := hp
    exact x := ⟨hinj x, hsurj x, hexact x⟩
    contMDiff_injection := hismooth
    contMDiff_projection := hpsmooth
    contMDiff_toFun := hforward
    contMDiff_invFun := hAsmooth
    snd_equiv := hesnd
    equiv_injection := hein }, ?_⟩
  intro x u v
  rfl

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over a Hausdorff paracompact intermediate manifold, the original normal sequence
of successive immersions admits a smooth splitting. -/
theorem nonempty_normalEmbeddingCompositionSplitting [T2Space N] [ParacompactSpace N] :
    Nonempty (NormalEmbeddingCompositionSplitting f g hf hg hgf) := by
  classical
  let := normalBundleFiberBundle g hg
  let := normalBundleVectorBundle g hg
  let := normalBundleContMDiffVectorBundle g hg
  obtain ⟨s₀, hs₀, hqs₀⟩ := exists_smooth_normal_rightInverse g hg
  obtain ⟨S, _⟩ := exists_normalEmbeddingCompositionSplitting_of_rightInverse
    f g hf hg hgf s₀ hs₀ hqs₀
  exact ⟨S⟩

end AtiyahSinger
