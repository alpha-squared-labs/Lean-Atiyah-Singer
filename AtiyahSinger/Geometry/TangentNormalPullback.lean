/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentVerticalNaturality
public import AtiyahSinger.Geometry.TransverseNormalPullback

/-!
# Naturality of tangent-normal sequences in a pullback square

Public module ID: M1494.

The quotient maps induced by an ambient smooth map and its tangent map commute
with the original canonical projection and vertical inclusion of the normal
exact sequences. This fixes the ordered normal factors when a tangent-normal
splitting is restricted to a transverse slice. All normal quotients and all
canonical maps are the original ones.

Source: naturality of the tangent exact sequence, made explicit here for the
parameter-slice construction used in SG III.13. The actual quotient formulas
are hypotheses on the supplied comparison maps, not consequences of equal ranks.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
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
/-- The two canonical tangent-normal maps commute with the actual induced quotient maps. -/
theorem tangentNormalPullback_maps_commute
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, G) 𝓘(ℝ, H) P Q ∞)
    (i : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
    (j : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, H) N Q ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsSmoothEmbedding 𝓘(ℝ, G) 𝓘(ℝ, H) ∞ g)
    (hcomm : ∀ x, j (f x) = g (i x))
    (D : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x →L[ℝ]
      NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x))
    (DT : ∀ z : TangentBundle 𝓘(ℝ, E) M,
      NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z →L[ℝ]
        NormalBundle 𝓘(ℝ, G × G) 𝓘(ℝ, H × H) (smoothTangentMap g)
          (smoothTangentMap i z))
    (hD : ∀ (x : M) (v : F),
      D x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g (i x)).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f x) v))
    (hDT : ∀ (z : TangentBundle 𝓘(ℝ, E) M) (v : F × F),
      DT z ((LinearMap.range
        (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, H × H) (smoothTangentMap g)
          (smoothTangentMap i z)).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, H × H) (smoothTangentMap j)
              (smoothTangentMap f z) v)) :
    (∀ (z : TangentBundle 𝓘(ℝ, E) M)
        (v : NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj),
      DT z (tangentNormalVerticalMap f hf z v) =
        tangentNormalVerticalMap g hg (smoothTangentMap i z) (D z.proj v)) ∧
      (∀ (z : TangentBundle 𝓘(ℝ, E) M)
          (v : NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z),
        tangentNormalProjection g hg (smoothTangentMap i z) (DT z v) =
          D z.proj (tangentNormalProjection f hf z v)) := by
  -- The actual tangent square commutes by the chain rule applied to its base square.
  have hTcomm (z : TangentBundle 𝓘(ℝ, E) M) :
      smoothTangentMap j (smoothTangentMap f z) =
        smoothTangentMap g (smoothTangentMap i z) := by
    have heq : (j : N → Q) ∘ f = (g : P → Q) ∘ i := funext hcomm
    have hleft := tangentMap_comp_at z (j.contMDiff.mdifferentiable (by simp) (f z.proj))
      (f.contMDiff.mdifferentiable (by simp) z.proj)
    have hright := tangentMap_comp_at z (g.contMDiff.mdifferentiable (by simp) (i z.proj))
      (i.contMDiff.mdifferentiable (by simp) z.proj)
    rw [heq] at hleft
    exact hleft.symm.trans hright
  have hfvertical (z : TangentBundle 𝓘(ℝ, E) M) (w : F) :
      tangentNormalVerticalMap f hf z
        ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ w) =
      (LinearMap.range
        (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ
          (tangentVerticalLift F N (smoothTangentMap f z) w) :=
    (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.1 z w
  have hfprojection (z : TangentBundle 𝓘(ℝ, E) M) (w : F × F) :
      tangentNormalProjection f hf z
        ((LinearMap.range
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ w) =
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ
        (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N)
          (smoothTangentMap f z) w) :=
    (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.2.1 z w
  have hgvertical (z : TangentBundle 𝓘(ℝ, G) P) (w : H) :
      tangentNormalVerticalMap g hg z
        ((LinearMap.range (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g z.proj).toLinearMap).mkQ w) =
      (LinearMap.range
        (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, H × H) (smoothTangentMap g) z).toLinearMap).mkQ
          (tangentVerticalLift H Q (smoothTangentMap g z) w) :=
    (exists_tangentNormal_exactSequence g hg).choose_spec.choose_spec.2.2.1 z w
  have hgprojection (z : TangentBundle 𝓘(ℝ, G) P) (w : H × H) :
      tangentNormalProjection g hg z
        ((LinearMap.range
          (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, H × H) (smoothTangentMap g) z).toLinearMap).mkQ w) =
      (LinearMap.range (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, H) g z.proj).toLinearMap).mkQ
        (mfderiv 𝓘(ℝ, H × H) 𝓘(ℝ, H) (smoothTangentBundleProjection H Q)
          (smoothTangentMap g z) w) :=
    (exists_tangentNormal_exactSequence g hg).choose_spec.choose_spec.2.2.2.1 z w
  constructor
  · intro z v
    -- Differentiate the affine fiber curve before passing to the normal quotient.
    obtain ⟨w, rfl⟩ := (LinearMap.range
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ_surjective v
    rw [hfvertical z w, hDT z (tangentVerticalLift F N (smoothTangentMap f z) w),
      hD z.proj w]
    have hv := hgvertical (smoothTangentMap i z)
      (show H from mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f z.proj) w)
    apply Eq.trans ?_ hv.symm
    apply congrArg (fun v : H × H ↦ (LinearMap.range
      (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, H × H) (smoothTangentMap g)
        (smoothTangentMap i z)).toLinearMap).mkQ v)
    have hn := DFunLike.congr_fun
      (tangentMap_verticalLift j (smoothTangentMap f z)) (show F from w)
    have hvect := congrArg
      (fun y : TangentBundle 𝓘(ℝ, H) Q ↦
        (show H × H from tangentVerticalLift H Q y
          (show H from mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f z.proj) w))) (hTcomm z)
    exact hn.trans hvect
  · intro z v
    -- Differentiating the projection identity gives the companion square.
    obtain ⟨w, rfl⟩ := (LinearMap.range
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ_surjective v
    rw [hDT, hgprojection, hfprojection, hD]
    have hprojection :
        (mfderiv 𝓘(ℝ, H × H) 𝓘(ℝ, H) (smoothTangentBundleProjection H Q)
          (smoothTangentMap j (smoothTangentMap f z))).comp
            (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, H × H) (smoothTangentMap j)
              (smoothTangentMap f z)) =
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, H) j (f z.proj)).comp
          (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N)
            (smoothTangentMap f z)) := by
      have hleft := mfderiv_comp (smoothTangentMap f z)
        ((smoothTangentBundleProjection H Q).contMDiff.mdifferentiable (by simp) _)
        ((smoothTangentMap j).contMDiff.mdifferentiable (by simp) _)
      have hright := mfderiv_comp (smoothTangentMap f z)
        (j.contMDiff.mdifferentiable (by simp) _)
        ((smoothTangentBundleProjection F N).contMDiff.mdifferentiable (by simp) _)
      exact hleft.symm.trans hright
    rw [← hTcomm]
    exact congrArg _ (DFunLike.congr_fun hprojection w)

section Splitting

variable (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, G) 𝓘(ℝ, H) P Q ∞)
  (i : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsSmoothEmbedding 𝓘(ℝ, G) 𝓘(ℝ, H) ∞ g)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TP" => TangentBundle 𝓘(ℝ, G) P
local notation "νf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νg" => NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "νTg" => NormalBundle 𝓘(ℝ, G × G) 𝓘(ℝ, H × H) (smoothTangentMap g)
local notation "Vf" => NormalModel E F
local notation "Vg" => NormalModel G H
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTg" => NormalModel (G × G) (H × H)
local notation "πM" => smoothTangentBundleProjection E M
local notation "πP" => smoothTangentBundleProjection G P
local notation "Ti" => smoothTangentMap i
local notation "νfP" => ((πM : TM → M) *ᵖ νf)
local notation "νgP" => ((πP : TP → P) *ᵖ νg)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Smooth normal comparisons respecting the canonical maps transport an ordered splitting. -/
theorem exists_tangentNormalSplitting_of_pullback
    (e : ∀ x, νf x ≃L[ℝ] νg (i x))
    (eT : ∀ z : TM, νTf z ≃L[ℝ] νTg (Ti z))
    (hes :
      letI := normalBundleFiberBundle f hf.isImmersion
      letI := normalBundleVectorBundle f hf.isImmersion
      letI := normalBundleContMDiffVectorBundle f hf.isImmersion
      letI := normalBundleFiberBundle g hg.isImmersion
      letI := normalBundleVectorBundle g hg.isImmersion
      letI := normalBundleContMDiffVectorBundle g hg.isImmersion
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
        (fun z : TotalSpace Vg ((i : M → P) *ᵖ νg) ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace Vf νf)))
    (heTs :
      letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
      letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
      letI := normalBundleContMDiffVectorBundle
        (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
      letI := normalBundleFiberBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
      letI := normalBundleVectorBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
      letI := normalBundleContMDiffVectorBundle
        (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
      ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTg)) ∞
        (fun z : TotalSpace VTf νTf ↦
          (⟨z.proj, eT z.proj z.snd⟩ : TotalSpace VTg ((Ti : TM → TP) *ᵖ νTg))))
    (hvertical : ∀ (z : TM) (v : νf z.proj),
      eT z (tangentNormalVerticalMap f hf z v) =
        tangentNormalVerticalMap g hg (Ti z) (e z.proj v))
    (hprojection : ∀ (z : TM) (v : νTf z),
      tangentNormalProjection g hg (Ti z) (eT z v) =
        e z.proj (tangentNormalProjection f hf z v))
    (Sg : TangentNormalSplitting g hg) :
    ∃ S : TangentNormalSplitting f hf, ∀ (z : TM) (v : νTf z),
      S.equiv z v = ((e z.proj).symm (Sg.equiv (Ti z) (eT z v)).1,
        (e z.proj).symm (Sg.equiv (Ti z) (eT z v)).2) := by
  classical
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle g hg.isImmersion
  let := normalBundleVectorBundle g hg.isImmersion
  let := normalBundleContMDiffVectorBundle g hg.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleFiberBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let := normalBundleVectorBundle (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
  let V := νfP ×ᵇ νfP
  let (z : TM) : AddCommGroup (V z) := by
    change AddCommGroup (νf z.proj × νf z.proj)
    infer_instance
  let (z : TM) : Module ℝ (V z) := by
    change Module ℝ (νf z.proj × νf z.proj)
    infer_instance
  let (z : TM) : IsTopologicalAddGroup (V z) := by
    change IsTopologicalAddGroup (νf z.proj × νf z.proj)
    infer_instance
  let (z : TM) : ContinuousSMul ℝ (V z) := by
    change ContinuousSMul ℝ (νf z.proj × νf z.proj)
    infer_instance
  let L (z : TM) : νTf z ≃L[ℝ] (νf z.proj × νf z.proj) :=
    (eT z).trans ((Sg.equiv (Ti z)).trans
      ((e z.proj).symm.prodCongr (e z.proj).symm))
  -- Lift the given pullback map, then apply the supplied splitting on its original base.
  have hLift : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
      (𝓘(ℝ, G × G).prod 𝓘(ℝ, VTg)) ∞
      (fun z : TotalSpace VTf νTf ↦ (⟨Ti z.proj, eT z.proj z.snd⟩ : TotalSpace VTg νTg)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨(Ti).contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj νTf),
      (Bundle.contMDiffAt_totalSpace.mp (heTs z)).2⟩
  have hSplit := Sg.contMDiff_toFun.comp hLift
  have hBase : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) 𝓘(ℝ, E) ∞
      (fun z : TotalSpace VTf νTf ↦ z.proj.proj) :=
    (πM).contMDiff.comp (contMDiff_proj νTf)
  -- Project the two ordered factors and apply the same inverse real normal comparison.
  have hFirst : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : TotalSpace VTf νTf ↦
        (⟨z.proj.proj, (Sg.equiv (Ti z.proj) (eT z.proj z.snd)).1⟩ :
          TotalSpace Vg ((i : M → P) *ᵖ νg))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨hBase z, ?_⟩
    have hcoords := (Bundle.contMDiffAt_totalSpace.mp (hSplit z)).2
    exact (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Vg × Vg → Vg)).contDiffAt.comp_contMDiffAt
      hcoords
  have hSecond : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : TotalSpace VTf νTf ↦
        (⟨z.proj.proj, (Sg.equiv (Ti z.proj) (eT z.proj z.snd)).2⟩ :
          TotalSpace Vg ((i : M → P) *ᵖ νg))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨hBase z, ?_⟩
    have hcoords := (Bundle.contMDiffAt_totalSpace.mp (hSplit z)).2
    exact (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Vg × Vg → Vg)).contDiffAt.comp_contMDiffAt
      hcoords
  have hforward : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, Vf × Vf)) ∞
      (fun z : TotalSpace VTf νTf ↦ (⟨z.proj, L z.proj z.snd⟩ : TotalSpace (Vf × Vf) V)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj νTf, ?_⟩
    have h₁ := (Bundle.contMDiffAt_totalSpace.mp ((hes.comp hFirst) z)).2
    have h₂ := (Bundle.contMDiffAt_totalSpace.mp ((hes.comp hSecond) z)).2
    exact h₁.prodMk_space h₂
  -- A smooth fiber equivalence has a smooth inverse in these same finite-dimensional atlases.
  have hinverse : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, Vf × Vf))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) ∞
      (fun z : TotalSpace (Vf × Vf) V ↦ (⟨z.proj, (L z.proj).symm z.snd⟩ :
        TotalSpace VTf νTf)) := by
    apply contMDiff_bundleMap_of_comp_surjective (F := VTf) (G := Vf × Vf) (H := VTf)
      (W := νTf) (V₀ := V) (Z := νTf)
      (fun z ↦ (L z).toContinuousLinearMap) (fun z ↦ (L z).symm.toContinuousLinearMap)
      hforward (fun z ↦ (L z).surjective)
    apply contMDiff_id.congr
    intro z
    exact congrArg (TotalSpace.mk z.proj) ((L z.proj).symm_apply_apply z.snd)
  let S : TangentNormalSplitting f hf := {
    equiv := L
    contMDiff_toFun := hforward
    contMDiff_invFun := hinverse
    fst_equiv := by
      intro z v
      change (e z.proj).symm (Sg.equiv (Ti z) (eT z v)).1 = _
      rw [Sg.fst_equiv, hprojection, (e z.proj).symm_apply_apply]
    equiv_vertical := by
      intro z v
      change ((e z.proj).symm (Sg.equiv (Ti z)
        (eT z (tangentNormalVerticalMap f hf z v))).1,
        (e z.proj).symm (Sg.equiv (Ti z)
          (eT z (tangentNormalVerticalMap f hf z v))).2) = (0, v)
      rw [hvertical, Sg.equiv_vertical]
      simp only [map_zero, ContinuousLinearEquiv.symm_apply_apply] }
  exact ⟨S, fun _ _ ↦ rfl⟩

end Splitting

end AtiyahSinger
