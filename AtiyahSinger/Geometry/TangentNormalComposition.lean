/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalEmbeddingComposition
public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Geometry.TangentVerticalNaturality

/-!
# Naturality of the actual normal composition diagram

Public module ID: M1491.

The chain rule identifies the quotient normal of the composite tangent map
with the normal of the tangent of the original smooth composite. The comparison
retains every tangent representative and is smooth in both directions for the
original quotient atlases. Under this comparison, the injection and projection
of the normal composition sequence commute with the canonical vertical lift
and canonical projection of the tangent-normal sequences.

This is the commutative diagram needed to compare the ordered complexification
with the real normal of a composite tangent embedding. Splitting comparison
and compatible nested tubular geometry remain separate constructions.

Source: the naturality of the tangent exact sequence and quotient-normal
sequence, expanded here as a chain-rule supplement to SG III.12, printed p.241.
The same original quotient representatives and specified maps are used in all
four squares; no rank-only comparison or alternate normal object is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
attribute [local instance] normalBundleTopology

section Composition

variable {E F G M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)
  (hgf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (g.comp f))

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "TP" => TangentBundle 𝓘(ℝ, G) P
local notation "Tf" => smoothTangentMap f
local notation "Tg" => smoothTangentMap g
local notation "Tgf" => smoothTangentMap (g.comp f)
local notation "νf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νg" => NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g
local notation "νgf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f)
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) Tf
local notation "νTg" => NormalBundle 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) Tg
local notation "νTgf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) Tgf
local notation "νTC" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G)
  (ContMDiffMap.comp (smoothTangentMap g) (smoothTangentMap f))

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Compare all four squares in the original selected quotient atlases.
/-- The original normal composition sequence commutes with its vertical and projection maps. -/
theorem exists_tangentNormalComposition_comparison
    (hTC : IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ∞ ((Tg).comp Tf))
    (S : NormalEmbeddingCompositionSplitting f g hf.isImmersion hg.isImmersion hgf.isImmersion)
    (ST : NormalEmbeddingCompositionSplitting Tf Tg
      (isImmersion_smoothTangentMap f hf) (isImmersion_smoothTangentMap g hg) hTC) :
    let V := NormalModel (E × E) (G × G)
    letI := normalBundleFiberBundle ((Tg).comp Tf) hTC
    letI := normalBundleVectorBundle ((Tg).comp Tf) hTC
    letI := normalBundleContMDiffVectorBundle ((Tg).comp Tf) hTC
    letI := normalBundleFiberBundle Tgf (isImmersion_smoothTangentMap (g.comp f) hgf)
    letI := normalBundleVectorBundle Tgf (isImmersion_smoothTangentMap (g.comp f) hgf)
    letI := normalBundleContMDiffVectorBundle Tgf (isImmersion_smoothTangentMap (g.comp f) hgf)
    ∃ c : ∀ z : TM, νTC z ≃L[ℝ] νTgf z,
      (∀ (z : TM) (v : G × G),
        c z ((LinearMap.range
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ((Tg).comp Tf) z).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) Tgf z).toLinearMap).mkQ v) ∧
      (ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
          (fun z : TotalSpace V νTC ↦ (⟨z.proj, c z.proj z.snd⟩ : TotalSpace V νTgf)) ∧
        ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
          (fun z : TotalSpace V νTgf ↦ (⟨z.proj, (c z.proj).symm z.snd⟩ : TotalSpace V νTC))) ∧
      (∀ (z : TM) (v : νTf z),
        tangentNormalProjection (g.comp f) hgf z (c z (ST.injection z v)) =
          S.injection z.proj (tangentNormalProjection f hf z v)) ∧
      (∀ (z : TM) (v : νf z.proj),
        c z (ST.injection z (tangentNormalVerticalMap f hf z v)) =
          tangentNormalVerticalMap (g.comp f) hgf z (S.injection z.proj v)) ∧
      (∀ (z : TM) (v : νTgf z),
        tangentNormalProjection g hg (Tf z) (ST.projection z ((c z).symm v)) =
          S.projection z.proj (tangentNormalProjection (g.comp f) hgf z v)) ∧
      (∀ (z : TM) (v : νgf z.proj),
        ST.projection z ((c z).symm (tangentNormalVerticalMap (g.comp f) hgf z v)) =
          tangentNormalVerticalMap g hg (Tf z) (S.projection z.proj v)) := by
  have hcomp : (Tg).comp Tf = Tgf := by
    apply DFunLike.ext
    intro z
    change (⟨g (f z.proj),
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f z.proj)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj z.snd)⟩ : TP) =
      ⟨g (f z.proj), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) z.proj z.snd⟩
    have hd := mfderiv_comp z.proj
      (g.contMDiff.mdifferentiable (by simp) (f z.proj))
      (f.contMDiff.mdifferentiable (by simp) z.proj)
    rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) z.proj =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f z.proj)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) from hd]
    rfl
  let eqNormal
      (a b : ContMDiffMap 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TM TP ∞) (hab : a = b) (z : TM) :
      NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) a z ≃L[ℝ]
        NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) b z := by
    subst b
    exact ContinuousLinearEquiv.refl ℝ _
  have eqNormal_mk
      (a b : ContMDiffMap 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TM TP ∞) (hab : a = b)
      (z : TM) (v : G × G) :
      eqNormal a b hab z
        ((LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) a z).toLinearMap).mkQ v) =
      (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) b z).toLinearMap).mkQ v := by
    subst b
    rfl
  have eqNormal_smooth
      (a b : ContMDiffMap 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TM TP ∞)
      (ha : IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ∞ a)
      (hb : IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ∞ b) (hab : a = b) :
      let V := NormalModel (E × E) (G × G)
      let A := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) a
      let B := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) b
      letI := normalBundleFiberBundle a ha
      letI := normalBundleVectorBundle a ha
      letI := normalBundleContMDiffVectorBundle a ha
      letI := normalBundleFiberBundle b hb
      letI := normalBundleVectorBundle b hb
      letI := normalBundleContMDiffVectorBundle b hb
      ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
          (fun z : TotalSpace V A ↦ (⟨z.proj, eqNormal a b hab z.proj z.snd⟩ : TotalSpace V B)) ∧
        ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
          (fun z : TotalSpace V B ↦
            (⟨z.proj, (eqNormal a b hab z.proj).symm z.snd⟩ : TotalSpace V A)) := by
    subst b
    let := normalBundleFiberBundle a ha
    let := normalBundleVectorBundle a ha
    let := normalBundleContMDiffVectorBundle a ha
    constructor <;> exact contMDiff_id
  let c (z : TM) : νTC z ≃L[ℝ] νTgf z := eqNormal ((Tg).comp Tf) Tgf hcomp z
  have hc (z : TM) (v : G × G) :
      c z ((LinearMap.range
        (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ((Tg).comp Tf) z).toLinearMap).mkQ v) =
      (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) Tgf z).toLinearMap).mkQ v :=
    eqNormal_mk ((Tg).comp Tf) Tgf hcomp z v
  have hcs (z : TM) (v : G × G) :
      (c z).symm ((LinearMap.range
        (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) Tgf z).toLinearMap).mkQ v) =
      (LinearMap.range
        (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ((Tg).comp Tf) z).toLinearMap).mkQ v := by
    apply (c z).injective
    rw [(c z).apply_symm_apply, hc]
  have hbase (z : TM) : Tg (Tf z) = Tgf z := congrArg (fun k ↦ k z) hcomp
  have hfvertical (z : TangentBundle 𝓘(ℝ, E) M) (w : F) :
      tangentNormalVerticalMap f hf z
        ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ w) =
      (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) Tf z).toLinearMap).mkQ
        (tangentVerticalLift F N (Tf z) w) :=
    (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.1 z w
  have hfprojection (z : TangentBundle 𝓘(ℝ, E) M) (w : F × F) :
      tangentNormalProjection f hf z
        ((LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) Tf z).toLinearMap).mkQ w) =
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ
        (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N) (Tf z) w) :=
    (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.2.1 z w
  have hgvertical (z : TangentBundle 𝓘(ℝ, F) N) (w : G) :
      tangentNormalVerticalMap g hg z
        ((LinearMap.range (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g z.proj).toLinearMap).mkQ w) =
      (LinearMap.range (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) Tg z).toLinearMap).mkQ
        (tangentVerticalLift G P (Tg z) w) :=
    (exists_tangentNormal_exactSequence g hg).choose_spec.choose_spec.2.2.1 z w
  have hgprojection (z : TangentBundle 𝓘(ℝ, F) N) (w : G × G) :
      tangentNormalProjection g hg z
        ((LinearMap.range (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) Tg z).toLinearMap).mkQ w) =
      (LinearMap.range (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g z.proj).toLinearMap).mkQ
        (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, G) (smoothTangentBundleProjection G P) (Tg z) w) :=
    (exists_tangentNormal_exactSequence g hg).choose_spec.choose_spec.2.2.2.1 z w
  have hgfvertical (z : TangentBundle 𝓘(ℝ, E) M) (w : G) :
      tangentNormalVerticalMap (g.comp f) hgf z
        ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) z.proj).toLinearMap).mkQ w) =
      (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) Tgf z).toLinearMap).mkQ
        (tangentVerticalLift G P (Tgf z) w) :=
    (exists_tangentNormal_exactSequence (g.comp f) hgf).choose_spec.choose_spec.2.2.1 z w
  have hgfprojection (z : TangentBundle 𝓘(ℝ, E) M) (w : G × G) :
      tangentNormalProjection (g.comp f) hgf z
        ((LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) Tgf z).toLinearMap).mkQ w) =
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) z.proj).toLinearMap).mkQ
        (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, G) (smoothTangentBundleProjection G P) (Tgf z) w) :=
    (exists_tangentNormal_exactSequence (g.comp f) hgf).choose_spec.choose_spec.2.2.2.1 z w
  let iT (z : TM) : νTf z →L[ℝ] νTgf z :=
    (c z).toContinuousLinearMap.comp (ST.injection z)
  let pT (z : TM) : νTgf z →L[ℝ] νTg (Tf z) :=
    (ST.projection z).comp (c z).symm.toContinuousLinearMap
  have hprojection (z : TM) :
      (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, G) (smoothTangentBundleProjection G P) (Tg (Tf z))).comp
          (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) Tg (Tf z)) =
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f z.proj)).comp
          (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N) (Tf z)) := by
    have hleft := mfderiv_comp (Tf z)
      ((smoothTangentBundleProjection G P).contMDiff.mdifferentiable (by simp) _)
      ((Tg).contMDiff.mdifferentiable (by simp) _)
    have hright := mfderiv_comp (Tf z) (g.contMDiff.mdifferentiable (by simp) _)
      ((smoothTangentBundleProjection F N).contMDiff.mdifferentiable (by simp) _)
    exact hleft.symm.trans hright
  -- The first two squares express naturality of the first normal injection.
  have hi_projection (z : TM) (v : νTf z) :
      tangentNormalProjection (g.comp f) hgf z (iT z v) =
        S.injection z.proj (tangentNormalProjection f hf z v) := by
    obtain ⟨w, rfl⟩ := (LinearMap.range
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) Tf z).toLinearMap).mkQ_surjective v
    dsimp only [iT, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [ST.injection_apply z w, hc z
      (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) Tg (Tf z) w)]
    rw [hgfprojection z (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) Tg (Tf z) w),
      hfprojection z w, S.injection_apply z.proj
        (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N) (Tf z) w)]
    rw [← hbase]
    exact congrArg _ (DFunLike.congr_fun (hprojection z) w)
  have hi_vertical (z : TM) (v : νf z.proj) :
      iT z (tangentNormalVerticalMap f hf z v) =
        tangentNormalVerticalMap (g.comp f) hgf z (S.injection z.proj v) := by
    obtain ⟨w, rfl⟩ := (LinearMap.range
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ_surjective v
    dsimp only [iT, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hfvertical z w, ST.injection_apply z (tangentVerticalLift F N (Tf z) w)]
    rw [hc z (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) Tg (Tf z)
      (tangentVerticalLift F N (Tf z) w))]
    rw [S.injection_apply z.proj w,
      hgfvertical z (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f z.proj) w)]
    rw [← hbase]
    exact congrArg _ (DFunLike.congr_fun (tangentMap_verticalLift g (Tf z)) w)
  -- The last two squares retain the same quotient to the second normal.
  have hp_projection (z : TM) (v : νTgf z) :
      tangentNormalProjection g hg (Tf z) (pT z v) =
        S.projection z.proj (tangentNormalProjection (g.comp f) hgf z v) := by
    obtain ⟨w, rfl⟩ := (LinearMap.range
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) Tgf z).toLinearMap).mkQ_surjective v
    dsimp only [pT, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hcs z w, ST.projection_apply z w, hgprojection (Tf z) w,
      hgfprojection z w, S.projection_apply z.proj
        (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, G) (smoothTangentBundleProjection G P) (Tgf z) w)]
    rw [hbase]
    rfl
  have hp_vertical (z : TM) (v : νgf z.proj) :
      pT z (tangentNormalVerticalMap (g.comp f) hgf z v) =
        tangentNormalVerticalMap g hg (Tf z) (S.projection z.proj v) := by
    obtain ⟨w, rfl⟩ := (LinearMap.range
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) z.proj).toLinearMap).mkQ_surjective v
    dsimp only [pT, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hgfvertical z w, hcs z (tangentVerticalLift G P (Tgf z) w),
      ST.projection_apply z (tangentVerticalLift G P (Tgf z) w),
      S.projection_apply z.proj w]
    have hv := hgvertical (Tf z) (show G from w)
    have hvect := congrArg
      (fun y : TP ↦ (show G × G from tangentVerticalLift G P y (show G from w))) (hbase z)
    exact (congrArg (fun u : G × G ↦ (LinearMap.range
      (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) Tg (Tf z)).toLinearMap).mkQ u)
        hvect.symm).trans hv.symm
  have hcsmooth := eqNormal_smooth ((Tg).comp Tf) Tgf hTC
    (isImmersion_smoothTangentMap (g.comp f) hgf) hcomp
  exact ⟨c, hc, hcsmooth, hi_projection, hi_vertical, hp_projection, hp_vertical⟩

end Composition
end AtiyahSinger
