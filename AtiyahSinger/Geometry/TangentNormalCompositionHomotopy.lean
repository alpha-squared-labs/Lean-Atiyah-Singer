/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DoubleExactSequenceHomotopy
public import AtiyahSinger.Geometry.TangentNormalComposition
public import AtiyahSinger.Geometry.NormalEmbeddingComposition
public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Geometry.TangentVerticalNaturality

/-!
# Actual homotopy between the two ordered normal comparisons

Public module ID: M1492.

The original four normal injection/projection squares identify the two endpoint
splittings in a genuine three-shear homotopy. All maps act on the original
quotients, pullbacks and native product bundles. The resulting whole real
parameter cylinder is a homeomorphism, with a jointly continuous inverse.
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

local notation "Vf" => NormalModel E F
local notation "Vg" => NormalModel F G
local notation "Vgf" => NormalModel E G
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTg" => NormalModel (F × F) (G × G)
local notation "VTgf" => NormalModel (E × E) (G × G)
local notation "AP" => ((smoothTangentBundleProjection E M : TM → M) *ᵖ νf)
local notation "BP" => ((fun z : TM ↦ f (Bundle.TotalSpace.proj z)) *ᵖ νg)
local notation "CP" => ((smoothTangentBundleProjection E M : TM → M) *ᵖ νgf)
local notation "GP" => ((Tf : TM → TN) *ᵖ νTg)
local notation "N₀" => TotalSpace VTgf νTgf
local notation "N₁" => TotalSpace (VTf × VTg) (νTf ×ᵇ GP)
local notation "XX" => TotalSpace ((Vf × Vg) × (Vf × Vg)) ((AP ×ᵇ BP) ×ᵇ (AP ×ᵇ BP))
local notation "YY" => TotalSpace ((Vf × Vf) × (Vg × Vg)) ((AP ×ᵇ AP) ×ᵇ (BP ×ᵇ BP))

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1800000 in
-- Several original quotient and iterated-pullback atlases occur in the same commuting diagram.
/-- The actual normal comparisons are joined by an invertible whole-cylinder homotopy. -/
theorem exists_tangentNormalComposition_homotopy
    (hTC : IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ∞ ((Tg).comp Tf))
    (S : NormalEmbeddingCompositionSplitting f g hf.isImmersion hg.isImmersion hgf.isImmersion)
    (ST : NormalEmbeddingCompositionSplitting Tf Tg
      (isImmersion_smoothTangentMap f hf) (isImmersion_smoothTangentMap g hg) hTC)
    (Sf : TangentNormalSplitting f hf) (Sg : TangentNormalSplitting g hg)
    (Sgf : TangentNormalSplitting (g.comp f) hgf) :
    ∃ (c : ∀ z : TM, νTC z ≃L[ℝ] νTgf z)
      (A : ℝ → ∀ z : TM, νTgf z ≃L[ℝ] (νTf z × νTg (Tf z)))
      (H : (ℝ × N₀) ≃ₜ (ℝ × N₁)),
      (∀ (z : TM) (v : G × G),
        c z ((LinearMap.range
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ((Tg).comp Tf) z).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) Tgf z).toLinearMap).mkQ v) ∧
      (∀ (t : ℝ) (z : N₀), H (t, z) = (t, (⟨z.proj, A t z.proj z.snd⟩ : N₁))) ∧
      (∀ (z : TM) (v : νTgf z), A 0 z v = ST.equiv z ((c z).symm v)) ∧
      (∀ (z : TM) (v : νTgf z), A 1 z v =
        ((Sf.equiv z).symm
          ((S.equiv z.proj (Sgf.equiv z v).1).1,
            (S.equiv z.proj (Sgf.equiv z v).2).1),
          (Sg.equiv (Tf z)).symm
            ((S.equiv z.proj (Sgf.equiv z v).1).2,
              (S.equiv z.proj (Sgf.equiv z v).2).2))) := by
  classical
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle g hg.isImmersion
  let := normalBundleVectorBundle g hg.isImmersion
  let := normalBundleContMDiffVectorBundle g hg.isImmersion
  let := normalBundleFiberBundle (g.comp f) hgf.isImmersion
  let := normalBundleVectorBundle (g.comp f) hgf.isImmersion
  let := normalBundleContMDiffVectorBundle (g.comp f) hgf.isImmersion
  let := normalBundleFiberBundle Tf (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle Tf (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle Tf (isImmersion_smoothTangentMap f hf)
  let := normalBundleFiberBundle Tg (isImmersion_smoothTangentMap g hg)
  let := normalBundleVectorBundle Tg (isImmersion_smoothTangentMap g hg)
  let := normalBundleContMDiffVectorBundle Tg (isImmersion_smoothTangentMap g hg)
  let := normalBundleFiberBundle Tgf (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleVectorBundle Tgf (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleContMDiffVectorBundle Tgf (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleFiberBundle ((Tg).comp Tf) hTC
  let := normalBundleVectorBundle ((Tg).comp Tf) hTC
  let := normalBundleContMDiffVectorBundle ((Tg).comp Tf) hTC
  obtain ⟨c, hc, hcs, hs₁, hs₂, hs₃, hs₄⟩ :=
    exists_tangentNormalComposition_comparison f g hf hg hgf hTC S ST
  let πM := smoothTangentBundleProjection E M
  let πN := smoothTangentBundleProjection F N
  let b : C(TM, N) :=
    ⟨fun z ↦ f z.proj, f.contMDiff.continuous.comp πM.contMDiff.continuous⟩
  let : FiberBundle Vg BP := FiberBundle.pullback (F := Vg) (E := νg) b
  let : VectorBundle ℝ Vg BP := VectorBundle.pullback ℝ b
  -- Expose the original quotient algebra beneath the two pullback abbreviations.
  let (z : TM) : AddCommGroup (AP z) := by
    change AddCommGroup (νf z.proj)
    infer_instance
  let (z : TM) : AddCommGroup (BP z) := by
    change AddCommGroup (νg (f z.proj))
    infer_instance
  let (z : TM) : Module ℝ (AP z) := by
    change Module ℝ (νf z.proj)
    infer_instance
  let (z : TM) : Module ℝ (BP z) := by
    change Module ℝ (νg (f z.proj))
    infer_instance
  let (z : TM) : IsTopologicalAddGroup (AP z) := by
    change IsTopologicalAddGroup (νf z.proj)
    infer_instance
  let (z : TM) : IsTopologicalAddGroup (BP z) := by
    change IsTopologicalAddGroup (νg (f z.proj))
    infer_instance
  let (z : TM) : ContinuousSMul ℝ (AP z) := by
    change ContinuousSMul ℝ (νf z.proj)
    infer_instance
  let (z : TM) : ContinuousSMul ℝ (BP z) := by
    change ContinuousSMul ℝ (νg (f z.proj))
    infer_instance
  -- Pull back S while retaining the literal vectors in its two original normal factors.
  have hS := S.contMDiff_toFun.continuous
  have hSi := S.contMDiff_invFun.continuous
  let K : TotalSpace Vgf CP ≃ₜ TotalSpace (Vf × Vg) (AP ×ᵇ BP) :=
    { toFun z := ⟨z.proj, S.equiv z.proj.proj z.snd⟩
      invFun z := ⟨z.proj, (S.equiv z.proj.proj).symm z.snd⟩
      left_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq ((S.equiv z.proj.proj).symm_apply_apply z.snd)
      right_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq ((S.equiv z.proj.proj).apply_symm_apply z.snd)
      continuous_toFun := by
        have h := hS.comp (Pullback.continuous_lift Vgf νgf πM)
        have hd := (FiberBundle.Prod.isInducing_diag Vf νf Vg ((f : M → N) *ᵖ νg)).continuous.comp h
        apply (FiberBundle.Prod.isInducing_diag Vf AP Vg BP).continuous_iff.mpr
        apply Continuous.prodMk
        · apply (inducing_pullbackTotalSpaceEmbedding Vf νf πM).continuous_iff.mpr
          exact (Pullback.continuous_proj Vgf νgf πM).prodMk hd.fst
        · apply (inducing_pullbackTotalSpaceEmbedding Vg νg
            (fun z : TM ↦ f z.proj)).continuous_iff.mpr
          exact (Pullback.continuous_proj Vgf νgf πM).prodMk
            ((Pullback.continuous_lift Vg νg f).comp hd.snd)
      continuous_invFun := by
        have hd := (FiberBundle.Prod.isInducing_diag Vf AP Vg BP).continuous
        have hb := FiberBundle.continuous_proj (Vf × Vg) (AP ×ᵇ BP)
        have ha := (Pullback.continuous_lift Vf νf πM).comp hd.fst
        have hg := (Pullback.continuous_lift Vg νg (fun z : TM ↦ f z.proj)).comp hd.snd
        have hgp : Continuous (fun z : TotalSpace (Vf × Vg) (AP ×ᵇ BP) ↦
            (⟨z.proj.proj, z.snd.2⟩ : TotalSpace Vg ((f : M → N) *ᵖ νg))) :=
          (inducing_pullbackTotalSpaceEmbedding Vg νg f).continuous_iff.mpr
            ((πM.contMDiff.continuous.comp hb).prodMk hg)
        have hp : Continuous (fun z : TotalSpace (Vf × Vg) (AP ×ᵇ BP) ↦
            (⟨z.proj.proj, z.snd⟩ : TotalSpace (Vf × Vg) (νf ×ᵇ ((f : M → N) *ᵖ νg)))) :=
          (FiberBundle.Prod.isInducing_diag Vf νf Vg ((f : M → N) *ᵖ νg)).continuous_iff.mpr
            (ha.prodMk hgp)
        exact (inducing_pullbackTotalSpaceEmbedding Vgf νgf πM).continuous_iff.mpr
          (hb.prodMk (hSi.comp hp)) }
  let KS : TotalSpace (Vgf × Vgf) (CP ×ᵇ CP) ≃ₜ XX :=
    { toFun z := ⟨z.proj, S.equiv z.proj.proj z.snd.1, S.equiv z.proj.proj z.snd.2⟩
      invFun z := ⟨z.proj, (S.equiv z.proj.proj).symm z.snd.1,
        (S.equiv z.proj.proj).symm z.snd.2⟩
      left_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq (Prod.ext ((S.equiv z.proj.proj).symm_apply_apply _)
            ((S.equiv z.proj.proj).symm_apply_apply _))
      right_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq (Prod.ext ((S.equiv z.proj.proj).apply_symm_apply _)
            ((S.equiv z.proj.proj).apply_symm_apply _))
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag Vgf CP Vgf CP).continuous
        exact (FiberBundle.Prod.isInducing_diag (Vf × Vg) (AP ×ᵇ BP)
          (Vf × Vg) (AP ×ᵇ BP)).continuous_iff.mpr
            ((K.continuous.comp hd.fst).prodMk (K.continuous.comp hd.snd))
      continuous_invFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (Vf × Vg) (AP ×ᵇ BP)
          (Vf × Vg) (AP ×ᵇ BP)).continuous
        exact (FiberBundle.Prod.isInducing_diag Vgf CP Vgf CP).continuous_iff.mpr
          ((K.symm.continuous.comp hd.fst).prodMk (K.symm.continuous.comp hd.snd)) }
  let CS := (Sgf.totalHomeomorph (g.comp f) hgf).trans KS
  -- The second tangent-normal splitting is pulled back through the same actual Tf.
  let KG : TotalSpace VTg GP ≃ₜ TotalSpace (Vg × Vg) (BP ×ᵇ BP) :=
    { toFun z := ⟨z.proj, Sg.equiv (Tf z.proj) z.snd⟩
      invFun z := ⟨z.proj, (Sg.equiv (Tf z.proj)).symm z.snd⟩
      left_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq ((Sg.equiv (Tf z.proj)).symm_apply_apply _)
      right_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq ((Sg.equiv (Tf z.proj)).apply_symm_apply _)
      continuous_toFun := by
        have h := (Sg.totalHomeomorph g hg).continuous.comp
          (Pullback.continuous_lift VTg νTg Tf)
        have hd := (FiberBundle.Prod.isInducing_diag Vg ((πN : TN → N) *ᵖ νg)
          Vg ((πN : TN → N) *ᵖ νg)).continuous.comp h
        have hb := Pullback.continuous_proj VTg νTg Tf
        apply (FiberBundle.Prod.isInducing_diag Vg BP Vg BP).continuous_iff.mpr
        exact ((inducing_pullbackTotalSpaceEmbedding Vg νg
            (fun z : TM ↦ f z.proj)).continuous_iff.mpr
          (hb.prodMk ((Pullback.continuous_lift Vg νg πN).comp hd.fst))).prodMk
            ((inducing_pullbackTotalSpaceEmbedding Vg νg (fun z : TM ↦ f z.proj)).continuous_iff.mpr
              (hb.prodMk ((Pullback.continuous_lift Vg νg πN).comp hd.snd)))
      continuous_invFun := by
        have hd := (FiberBundle.Prod.isInducing_diag Vg BP Vg BP).continuous
        have hb := FiberBundle.continuous_proj (Vg × Vg) (BP ×ᵇ BP)
        have hbase := (Tf).contMDiff.continuous.comp hb
        have h1 := (Pullback.continuous_lift Vg νg (fun z : TM ↦ f z.proj)).comp hd.fst
        have h2 := (Pullback.continuous_lift Vg νg (fun z : TM ↦ f z.proj)).comp hd.snd
        have ht : Continuous (fun z : TotalSpace (Vg × Vg) (BP ×ᵇ BP) ↦
            (⟨Tf z.proj, z.snd⟩ : TotalSpace (Vg × Vg)
              (((πN : TN → N) *ᵖ νg) ×ᵇ ((πN : TN → N) *ᵖ νg)))) :=
          (FiberBundle.Prod.isInducing_diag Vg ((πN : TN → N) *ᵖ νg)
            Vg ((πN : TN → N) *ᵖ νg)).continuous_iff.mpr
              (((inducing_pullbackTotalSpaceEmbedding Vg νg πN).continuous_iff.mpr
                (hbase.prodMk h1)).prodMk
                  ((inducing_pullbackTotalSpaceEmbedding Vg νg πN).continuous_iff.mpr
                    (hbase.prodMk h2)))
        exact (inducing_pullbackTotalSpaceEmbedding VTg νTg Tf).continuous_iff.mpr
          (hb.prodMk ((Sg.totalHomeomorph g hg).symm.continuous.comp ht)) }
  let CT : N₁ ≃ₜ YY :=
    { toFun z := ⟨z.proj, Sf.equiv z.proj z.snd.1, Sg.equiv (Tf z.proj) z.snd.2⟩
      invFun z := ⟨z.proj, (Sf.equiv z.proj).symm z.snd.1,
        (Sg.equiv (Tf z.proj)).symm z.snd.2⟩
      left_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq (Prod.ext ((Sf.equiv z.proj).symm_apply_apply _)
            ((Sg.equiv (Tf z.proj)).symm_apply_apply _))
      right_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq (Prod.ext ((Sf.equiv z.proj).apply_symm_apply _)
            ((Sg.equiv (Tf z.proj)).apply_symm_apply _))
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag VTf νTf VTg GP).continuous
        exact (FiberBundle.Prod.isInducing_diag (Vf × Vf) (AP ×ᵇ AP)
          (Vg × Vg) (BP ×ᵇ BP)).continuous_iff.mpr
            (((Sf.totalHomeomorph f hf).continuous.comp hd.fst).prodMk
              (KG.continuous.comp hd.snd))
      continuous_invFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (Vf × Vf) (AP ×ᵇ AP)
          (Vg × Vg) (BP ×ᵇ BP)).continuous
        exact (FiberBundle.Prod.isInducing_diag VTf νTf VTg GP).continuous_iff.mpr
          (((Sf.totalHomeomorph f hf).symm.continuous.comp hd.fst).prodMk
            (KG.symm.continuous.comp hd.snd)) }
  let C₀ : N₀ ≃ₜ N₁ :=
    { toFun z := ⟨z.proj, ST.equiv z.proj ((c z.proj).symm z.snd)⟩
      invFun z := ⟨z.proj, c z.proj ((ST.equiv z.proj).symm z.snd)⟩
      left_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq (by simp)
      right_inv z := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq (by simp)
      continuous_toFun := ST.contMDiff_toFun.continuous.comp hcs.2.continuous
      continuous_invFun := hcs.1.continuous.comp ST.contMDiff_invFun.continuous }
  let RS (z : TM) := (Sgf.equiv z).trans ((S.equiv z.proj).prodCongr (S.equiv z.proj))
  let RT (z : TM) := (Sf.equiv z).prodCongr (Sg.equiv (Tf z))
  let L (z : TM) := (((RS z).symm.trans (c z).symm).trans (ST.equiv z)).trans (RT z)
  have hL : Continuous (fun z : XX ↦ (⟨z.proj, L z.proj z.snd⟩ : YY)) :=
    ((CS.symm.trans C₀).trans CT).continuous
  have hLi : Continuous (fun z : YY ↦ (⟨z.proj, (L z.proj).symm z.snd⟩ : XX)) :=
    ((CS.symm.trans C₀).trans CT).symm.continuous
  -- The actual four squares become precisely the four three-shear normalization identities.
  have hST (z : TM) (v : νTf z) : (ST.equiv z).symm (v, 0) = ST.injection z v := by
    apply (ST.equiv z).injective
    rw [(ST.equiv z).apply_symm_apply, ST.equiv_injection]
  have hfV (z : TM) (a : νf z.proj) :
      (Sf.equiv z).symm (0, a) = tangentNormalVerticalMap f hf z a := by
    apply (Sf.equiv z).injective
    rw [(Sf.equiv z).apply_symm_apply, Sf.equiv_vertical]
  have hgfV (z : TM) (a : νgf z.proj) :
      (Sgf.equiv z).symm (0, a) = tangentNormalVerticalMap (g.comp f) hgf z a := by
    apply (Sgf.equiv z).injective
    rw [(Sgf.equiv z).apply_symm_apply, Sgf.equiv_vertical]
  have hbase (z : TM) (a d : νf z.proj) : ((L z).symm ((a, d), 0)).1 = (a, 0) := by
    change S.equiv z.proj
      (Sgf.equiv z (c z ((ST.equiv z).symm
        ((Sf.equiv z).symm (a, d), (Sg.equiv (Tf z)).symm 0)))).1 = (a, 0)
    rw [map_zero, hST, Sgf.fst_equiv, hs₁, S.equiv_injection,
      ← Sf.fst_equiv, (Sf.equiv z).apply_symm_apply]
  have hvertical (z : TM) (a : νf z.proj) :
      (L z).symm ((0, a), 0) = ((0, 0), (a, 0)) := by
    change (S.equiv z.proj
        (Sgf.equiv z (c z ((ST.equiv z).symm
          ((Sf.equiv z).symm (0, a), (Sg.equiv (Tf z)).symm 0)))).1,
      S.equiv z.proj
        (Sgf.equiv z (c z ((ST.equiv z).symm
          ((Sf.equiv z).symm (0, a), (Sg.equiv (Tf z)).symm 0)))).2) = _
    rw [map_zero, hfV, hST, hs₂, Sgf.equiv_vertical, map_zero, S.equiv_injection]
    rfl
  have hproj (z : TM) (v : (νf z.proj × νg (f z.proj)) ×
      (νf z.proj × νg (f z.proj))) : (L z v).2.1 = v.1.2 := by
    change (Sg.equiv (Tf z)
      (ST.equiv z ((c z).symm ((RS z).symm v))).2).1 = v.1.2
    rw [Sg.fst_equiv, ST.snd_equiv, hs₃, ← Sgf.fst_equiv]
    change S.projection z.proj
      (Sgf.equiv z ((Sgf.equiv z).symm
        ((S.equiv z.proj).symm v.1, (S.equiv z.proj).symm v.2))).1 = v.1.2
    rw [(Sgf.equiv z).apply_symm_apply, ← S.snd_equiv, (S.equiv z.proj).apply_symm_apply]
  have hprojVertical (z : TM) (v : νf z.proj × νg (f z.proj)) :
      (L z (0, v)).2 = (0, v.2) := by
    change Sg.equiv (Tf z) (ST.equiv z ((c z).symm
      ((Sgf.equiv z).symm ((S.equiv z.proj).symm 0, (S.equiv z.proj).symm v)))).2 = _
    rw [map_zero, hgfV, ST.snd_equiv, hs₄, Sg.equiv_vertical,
      ← S.snd_equiv, (S.equiv z.proj).apply_symm_apply]
  obtain ⟨H, hH⟩ := exists_doubleSplitShearCylinder
    (FA := Vf) (FB := Vg) (V := AP) (W := BP) L hL hLi
  let A (t : ℝ) (z : TM) := ((RS z).trans (doubleSplitShearPath (L z) t)).trans (RT z).symm
  let C := (((Homeomorph.refl ℝ).prodCongr CS).trans H).trans
    ((Homeomorph.refl ℝ).prodCongr CT.symm)
  refine ⟨c, A, C, hc, ?_, ?_, ?_⟩
  · intro t z
    change ((H (t, CS z)).1, CT.symm (H (t, CS z)).2) = _
    rw [hH]
    rfl
  · intro z v
    have h := (doubleSplitShearPath_endpoints (L z) (hbase z) (hvertical z)
      (hproj z) (hprojVertical z)).1 (RS z v)
    change (RT z).symm (doubleSplitShearPath (L z) 0 (RS z v)) = _
    rw [h]
    change (RT z).symm (RT z (ST.equiv z ((c z).symm ((RS z).symm (RS z v))))) = _
    rw [(RT z).symm_apply_apply, (RS z).symm_apply_apply]
  · intro z v
    have h := (doubleSplitShearPath_endpoints (L z) (hbase z) (hvertical z)
      (hproj z) (hprojVertical z)).2 (RS z v)
    change (RT z).symm (doubleSplitShearPath (L z) 1 (RS z v)) = _
    rw [h]
    rfl

end Composition

end AtiyahSinger

