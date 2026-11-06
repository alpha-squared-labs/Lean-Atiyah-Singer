/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.GlobalNormalCoordinates
public import AtiyahSinger.Geometry.TangentNormalBundle

/-!
# Ordered normal coordinates of a linear embedding

Public module ID: M1288.

Complementary coordinates for a linear inclusion induce the ordered quotient
and vertical splitting of its actual tangent normal bundle. The resulting
normalized tube is the whole ambient tangent space in those same coordinates.
These formulas retain the original normal quotient and the canonical vertical
and projection maps used by the tangent pushforward.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology tangentBundleFullChartedSpace
  tangentBundle_full_isManifold

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The native tangent coordinates of a model vector space, with its full model made explicit. -/
private def modelTangentCoordinates (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TangentBundle 𝓘(ℝ, E) E ≃ₘ⟮𝓘(ℝ, E × E), 𝓘(ℝ, E × E)⟯ E × E where
  __ := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).toEquiv
  contMDiff_toFun := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_tangentBundleModelSpaceHomeomorph
  contMDiff_invFun := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_tangentBundleModelSpaceHomeomorph_symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [FiniteDimensional ℝ E] in
/-- In native model tangent charts the coordinate map has identity derivative. -/
private theorem modelTangentCoordinates_mfderiv (z : TangentBundle 𝓘(ℝ, E) E) :
    mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) (modelTangentCoordinates E) z =
      ContinuousLinearMap.id ℝ (E × E) := by
  have heq : (modelTangentCoordinates E : TangentBundle 𝓘(ℝ, E) E → E × E) =
      extChartAt 𝓘(ℝ, E × E) z := by
    funext w
    change (w.proj, w.snd) = 𝓘(ℝ, E × E) (chartAt (E × E) z w)
    rw [show (chartAt (E × E) z : TangentBundle 𝓘(ℝ, E) E → E × E) =
      TotalSpace.toProd E E from tangentBundle_model_space_coe_chartAt z]
    rfl
  rw [heq, mfderiv_extChartAt_self]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The two actual normal atlases remain visible through the ordered splitting construction.
/-- A globally linear inclusion has the canonical ordered tangent-normal splitting and product
tube, in the same complementary coordinates as its original normal quotient. -/
theorem exists_linearEmbedding_tangentNormal_coordinates
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (c : F ≃L[ℝ] E × G) (hlinear : ∀ x, f x = c.symm (x, 0)) :
    letI := normalBundleFiberBundle f hf.isImmersion
    letI := normalBundleVectorBundle f hf.isImmersion
    letI := normalBundleContMDiffVectorBundle f hf.isImmersion
    ∃ e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ] G,
      (∀ (x : E) (w : F),
        e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ w) =
          (c w).2) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) ↦
          (z.proj, e z.proj z.snd)) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
        (fun z : E × G ↦ (⟨z.1, (e z.1).symm z.2⟩ :
          TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))) ∧
      ∃ S : TangentNormalSplitting f hf,
        ∃ T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf),
          ∀ (z : TangentBundle 𝓘(ℝ, E) E)
            (u v : NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj),
            T.totalMap _ _ ⟨z, (S.equiv z).symm (u, v)⟩ =
              (⟨c.symm (z.proj, e z.proj u), c.symm (z.snd, e z.proj v)⟩ :
                TangentBundle 𝓘(ℝ, F) F) := by
  classical
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let Tf := smoothTangentMap f
  let hTf := isImmersion_smoothTangentMap f hf
  let := normalBundleFiberBundle Tf hTf
  let := normalBundleVectorBundle Tf hTf
  let := normalBundleContMDiffVectorBundle Tf hTf
  let TM := TangentBundle 𝓘(ℝ, E) E
  let TN := TangentBundle 𝓘(ℝ, F) F
  let ν := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νT := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) Tf
  let V := NormalModel E F
  let VT := NormalModel (E × E) (F × F)
  let πM := smoothTangentBundleProjection E E
  let νP := (πM : TM → E) *ᵖ ν
  let Q (x : E) := (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
  let QT (z : TM) :=
    (LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) Tf z).toLinearMap).mkQ
  -- The original linear inclusion and its tangent map use exactly the same block coordinates.
  let L : E →L[ℝ] F := c.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E G)
  have hfderiv (x : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x = L := by
    have h : (f : E → F) = L := funext hlinear
    rw [h]
    exact L.hasFDerivAt.hasMFDerivAt.mfderiv
  let a := modelTangentCoordinates E
  let b := modelTangentCoordinates F
  let cT : (F × F) ≃L[ℝ] (E × E) × (G × G) :=
    (c.prodCongr c).trans
      (LinearEquiv.prodProdProdComm ℝ E G E G).toContinuousLinearEquiv
  have hTlinear (z : TM) : b (Tf z) = cT.symm (a z, 0) := by
    change (f z.proj, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj z.snd) = _
    rw [hfderiv, hlinear]
    rfl
  obtain ⟨e, he, hes, hei⟩ := exists_global_normal_coordinates f hf.isImmersion
    (Diffeomorph.refl 𝓘(ℝ, E) E ∞) (Diffeomorph.refl 𝓘(ℝ, F) F ∞) c hlinear
  have heQ (x : E) (w : F) : e x (Q x w) = (c w).2 := by
    have h := he x w
    change e x (Q x w) = (c (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) id (f x) w)).2 at h
    rw [mfderiv_id] at h
    exact h
  obtain ⟨eT, heT, heTs, heTi⟩ := exists_global_normal_coordinates Tf hTf a b cT hTlinear
  have heTQ (z : TM) (w : F × F) : eT z (QT z w) = ((c w.1).2, (c w.2).2) := by
    rw [heT, modelTangentCoordinates_mfderiv]
    rfl
  obtain ⟨T, hT⟩ := exists_global_normal_tube Tf hTf a b cT hTlinear eT heT heTs heTi
  let s (z : TM) : νT z ≃L[ℝ] ν z.proj × ν z.proj :=
    (eT z).trans ((e z.proj).symm.prodCongr (e z.proj).symm)
  have hsQ (z : TM) (w : F × F) : s z (QT z w) = (Q z.proj w.1, Q z.proj w.2) := by
    change ((e z.proj).symm (eT z (QT z w)).1,
      (e z.proj).symm (eT z (QT z w)).2) = _
    rw [heTQ]
    apply Prod.ext
    · exact (e z.proj).symm_apply_eq.mpr (heQ z.proj w.1).symm
    · exact (e z.proj).symm_apply_eq.mpr (heQ z.proj w.2).symm
  -- Smoothness is tested in the native pullback and double-bundle charts.
  have hback₁ : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, G × G))
      (𝓘(ℝ, E).prod 𝓘(ℝ, V)) ∞
      (fun z : TM × (G × G) ↦ (⟨z.1.proj, (e z.1.proj).symm z.2.1⟩ : TotalSpace V ν)) :=
    hei.comp ((πM.contMDiff.comp contMDiff_fst).prodMk
      ((ContinuousLinearMap.fst ℝ G G).contDiff.contMDiff.comp contMDiff_snd))
  have hback₂ : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, G × G))
      (𝓘(ℝ, E).prod 𝓘(ℝ, V)) ∞
      (fun z : TM × (G × G) ↦ (⟨z.1.proj, (e z.1.proj).symm z.2.2⟩ : TotalSpace V ν)) :=
    hei.comp ((πM.contMDiff.comp contMDiff_fst).prodMk
      ((ContinuousLinearMap.snd ℝ G G).contDiff.contMDiff.comp contMDiff_snd))
  have hback : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, G × G))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V)) ∞
      (fun z : TM × (G × G) ↦
        (⟨z.1, ((e z.1.proj).symm z.2.1, (e z.1.proj).symm z.2.2)⟩ :
          TotalSpace (V × V) (νP ×ᵇ νP))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_fst, ?_⟩
    exact ((Bundle.contMDiffAt_totalSpace.mp (hback₁ z)).2).prodMk_space
      (Bundle.contMDiffAt_totalSpace.mp (hback₂ z)).2
  have hdown₁ : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
      (𝓘(ℝ, E).prod 𝓘(ℝ, V)) ∞
      (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
        (⟨z.proj.proj, z.snd.1⟩ : TotalSpace V ν)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨πM.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj _), ?_⟩
    have h := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V)) ∞ id z from contMDiffAt_id)).2
    exact (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : V × V → V)).contDiffAt.comp_contMDiffAt h
  have hdown₂ : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
      (𝓘(ℝ, E).prod 𝓘(ℝ, V)) ∞
      (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
        (⟨z.proj.proj, z.snd.2⟩ : TotalSpace V ν)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨πM.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj _), ?_⟩
    have h := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V)) ∞ id z from contMDiffAt_id)).2
    exact (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : V × V → V)).contDiffAt.comp_contMDiffAt h
  have hfront : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, G × G)) ∞
      (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
        (z.proj, (e z.proj.proj z.snd.1, e z.proj.proj z.snd.2))) :=
    (contMDiff_proj _).prodMk ((contMDiff_snd.comp (hes.comp hdown₁)).prodMk_space
      (contMDiff_snd.comp (hes.comp hdown₂)))
  -- The canonical quotient projection and vertical inclusion fix the order of the two factors.
  have hprojection (z : TN) :
      mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F F) z =
        ContinuousLinearMap.fst ℝ F F := by
    have h := mfderiv_comp z
      (((ContinuousLinearMap.fst ℝ F F).contDiff :
        ContDiff ℝ ∞ (ContinuousLinearMap.fst ℝ F F)).contMDiff.mdifferentiable
          (by simp) (b z))
      (b.contMDiff.mdifferentiable (by simp) z)
    rw [modelTangentCoordinates_mfderiv] at h
    change mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F F) z =
      mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (ContinuousLinearMap.fst ℝ F F) (b z) at h
    rw [(ContinuousLinearMap.fst ℝ F F).hasFDerivAt.hasMFDerivAt.mfderiv] at h
    exact h
  have hvertical (z : TN) : tangentVerticalLift F F z =
      ContinuousLinearMap.inr ℝ F F := by
    let e₀ : F ≃L[ℝ] F :=
      (trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj).continuousLinearEquivAt
      ℝ z.proj (mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj)
    let γ (w : F) : TN := ⟨z.proj, (show F from z.snd) + e₀.symm w⟩
    have hγ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F × F) ∞ γ :=
      b.symm.contMDiff.comp (contMDiff_const.prodMk_space
        (contMDiff_const.add e₀.symm.contDiff.contMDiff))
    have h := mfderiv_comp 0 (b.contMDiff.mdifferentiable (by simp) (γ 0))
      (hγ.mdifferentiable (by simp) 0)
    rw [modelTangentCoordinates_mfderiv] at h
    change mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) (b ∘ γ) 0 =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) γ 0 at h
    have hd : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) (b ∘ γ) 0 =
        (ContinuousLinearMap.inr ℝ F F).comp e₀.symm.toContinuousLinearMap := by
      convert! ((hasFDerivAt_const z.proj (0 : F)).prodMk
        ((hasFDerivAt_const (show F from z.snd) (0 : F)).add
          e₀.symm.toContinuousLinearMap.hasFDerivAt)).hasMFDerivAt.mfderiv using 1
      ext w <;> simp
    rw [hd] at h
    change ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) γ 0).comp
      (NormedSpace.fromTangentSpace (0 : F)).symm.toContinuousLinearMap).comp
        e₀.toContinuousLinearMap = _
    rw [← h]
    ext w
    change (0, e₀.symm (e₀ w)) = (0, w)
    rw [e₀.symm_apply_apply]
  let seq := (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec
  let S : TangentNormalSplitting f hf :=
    { equiv := s
      contMDiff_toFun := hback.comp heTs
      contMDiff_invFun := heTi.comp hfront
      fst_equiv := by
        intro z w
        obtain ⟨v, rfl⟩ := (LinearMap.range
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) Tf z).toLinearMap).mkQ_surjective w
        have hp := seq.2.2.2.1 z v
        change tangentNormalProjection f hf z (QT z v) =
          Q z.proj (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F)
            (smoothTangentBundleProjection F F) (Tf z) v) at hp
        rw [hprojection] at hp
        exact (congrArg Prod.fst (hsQ z v)).trans hp.symm
      equiv_vertical := by
        intro z w
        obtain ⟨v, rfl⟩ := (LinearMap.range
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ_surjective w
        have hi := seq.2.2.1 z v
        change tangentNormalVerticalMap f hf z (Q z.proj v) =
          QT z (tangentVerticalLift F F (Tf z) v) at hi
        rw [hvertical] at hi
        change s z (tangentNormalVerticalMap f hf z (Q z.proj v)) = (0, Q z.proj v)
        rw [hi, hsQ]
        change (Q z.proj 0, Q z.proj v) = (0, Q z.proj v)
        rw [(Q z.proj).map_zero] }
  refine ⟨e, heQ, hes, hei, S, T, ?_⟩
  intro z u v
  rw [hT]
  change b.symm (cT.symm (a z, eT z ((s z).symm (u, v)))) = _
  have hs : eT z ((s z).symm (u, v)) = (e z.proj u, e z.proj v) := by
    exact (eT z).apply_symm_apply _
  rw [hs]
  rfl

end AtiyahSinger
