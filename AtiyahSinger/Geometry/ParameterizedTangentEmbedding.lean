/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactEuclideanEmbedding
public import AtiyahSinger.Geometry.TangentEmbedding

/-!
# Parameterized tangent embeddings

Public module ID: M1340.

Joint smoothness of a family induces joint smoothness of its vertical tangent
maps. For a compact Hausdorff source and a Hausdorff target, a real family
of smooth embeddings gives a proper time-preserving embedding of the
tangent cylinder. Properness is obtained by
restricting the tangent map of the proper graph embedding to zero parameter
velocities; no compactness of the tangent bundle is assumed.

These parameter constructions supplement the isotopy argument in SG III.13.
All tangent maps and product charts are the original mathlib constructions.
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

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
set_option backward.isDefEq.respectTransparency false in
/-- Joint smoothness passes to the actual derivatives in the manifold direction. -/
theorem contMDiff_parameterTangentMap
    (f : ℝ → M → N)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M ↦ f p.1 p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E)).tangent) (𝓘(ℝ, F)).tangent ∞
      (fun p : ℝ × TangentBundle 𝓘(ℝ, E) M ↦
        tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2) := by
  -- The vertical tangent is the full differential applied to zero time velocity.
  let j : ℝ × TangentBundle 𝓘(ℝ, E) M →
      TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (ℝ × M) :=
    fun p ↦ ⟨(p.1, p.2.proj), (0, p.2.snd)⟩
  have hj : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E)).tangent)
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)).tangent ∞ j :=
    contMDiff_equivTangentBundleProd_symm.comp
      (((contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ))).comp
        contMDiff_fst).prodMk contMDiff_snd)
  have hcomp := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hj
  convert hcomp using 1
  funext p
  simp only [j, Function.comp_def, tangentMap]
  rw [mfderiv_prod_eq_add_apply (hf.mdifferentiable (by simp) _), map_zero, zero_add]

set_option backward.isDefEq.respectTransparency false in
/-- A proper smooth family of embeddings is a smooth embedding of its parameter cylinder. -/
theorem isSmoothEmbedding_parameterMap
    (f : ℝ → M → N)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M ↦ f p.1 p.2))
    (hemb : ∀ t, IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (f t))
    (hproper : IsProperMap (fun p : ℝ × M ↦ (p.1, f p.1 p.2))) :
    IsSmoothEmbedding (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ (fun p : ℝ × M ↦ (p.1, f p.1 p.2)) := by
  -- Retaining the parameter gives injectivity, including its differential.
  let g : ℝ × M → ℝ × N := fun p ↦ (p.1, f p.1 p.2)
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ g := contMDiff_fst.prodMk hf
  have hinj : Function.Injective g := by
    rintro ⟨t, x⟩ ⟨s, y⟩ h
    have hts : t = s := congrArg Prod.fst h
    subst s
    exact Prod.ext rfl ((hemb t).isEmbedding.injective (congrArg Prod.snd h))
  have hder (p : ℝ × M) : Function.Injective
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) g p) := by
    apply (injective_iff_map_eq_zero (mfderiv _ _ g p)).mpr
    intro v hv
    have hformula : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) g p v =
        (v.1, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun t ↦ f t p.2) p.1 v.1 +
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2 v.2) := by
      rw [mfderiv_prodMk mdifferentiableAt_fst (hf.mdifferentiable (by simp) p)]
      rw [mfderiv_fst]
      change (v.1, mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F)
        (fun p : ℝ × M ↦ f p.1 p.2) p v) = _
      rw [mfderiv_prod_eq_add_apply (hf.mdifferentiable (by simp) p)]
    have htime : v.1 = 0 := by
      rw [hformula] at hv
      exact congrArg Prod.fst hv
    have hspace : v.2 = 0 := by
      apply (hemb p.1).isImmersion.mfderiv_injective (by simp) p.2
      rw [map_zero]
      have hsecond := congrArg Prod.snd hv
      rw [hformula, htime, map_zero, zero_add] at hsecond
      exact hsecond
    exact Prod.ext htime hspace
  -- Apply the finite-dimensional immersion criterion in the same product charts.
  let : ChartedSpace (ℝ × E) (ℝ × M) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ E) (ℝ × M))
  let : ChartedSpace (ℝ × F) (ℝ × N) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ F) (ℝ × N))
  let : IsManifold 𝓘(ℝ, ℝ × E) ∞ (ℝ × M) := by
    simpa only [modelWithCornersSelf_prod] using
      (inferInstance : IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (ℝ × M))
  let : IsManifold 𝓘(ℝ, ℝ × F) ∞ (ℝ × N) := by
    simpa only [modelWithCornersSelf_prod] using
      (inferInstance : IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ (ℝ × N))
  have himm : IsImmersion 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ g :=
    isImmersion_of_injective_mfderiv
      ⟨g, by simpa only [modelWithCornersSelf_prod] using hg⟩
      (by
        change ∀ p, Function.Injective (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g p)
        simpa only [modelWithCornersSelf_prod] using! hder)
  refine ⟨by simpa only [modelWithCornersSelf_prod] using himm, ?_⟩
  exact (IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    ⟨hproper.continuous, hinj, hproper.isClosedMap⟩).isEmbedding

set_option backward.isDefEq.respectTransparency false in
/-- The vertical tangent cylinder of a compact-source family of embeddings is proper. -/
theorem isProperMap_parameterTangentMap [CompactSpace M] [T2Space M] [T2Space N]
    (f : ℝ → M → N)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M ↦ f p.1 p.2))
    (hemb : ∀ t, IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (f t)) :
    IsProperMap (fun p : ℝ × TangentBundle 𝓘(ℝ, E) M ↦
      (p.1, tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2)) := by
  -- The graph is proper because its parameter projection has compact fibers M.
  let g : ℝ × M → ℝ × N := fun p ↦ (p.1, f p.1 p.2)
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ g := contMDiff_fst.prodMk hf
  have hgp : IsProperMap g := isProperMap_of_comp_of_t2 hg.continuous
    continuous_fst isProperMap_fst_of_compactSpace
  have hge := isSmoothEmbedding_parameterMap f hf hemb hgp
  -- Use the original product charts to apply properness of the full tangent map.
  let : ChartedSpace (ℝ × E) (ℝ × M) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ E) (ℝ × M))
  let : ChartedSpace (ℝ × F) (ℝ × N) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ F) (ℝ × N))
  let : IsManifold 𝓘(ℝ, ℝ × E) ∞ (ℝ × M) := by
    simpa only [modelWithCornersSelf_prod] using
      (inferInstance : IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (ℝ × M))
  let : IsManifold 𝓘(ℝ, ℝ × F) ∞ (ℝ × N) := by
    simpa only [modelWithCornersSelf_prod] using
      (inferInstance : IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ (ℝ × N))
  have hge' : IsSmoothEmbedding 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ g := by
    simpa only [modelWithCornersSelf_prod] using hge
  have hTg : IsProperMap
      (tangentMap (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) g) := by
    simpa only [modelWithCornersSelf_prod] using! isProperMap_tangentMap hge' hgp
  -- Zero time velocities form a closed subbundle of the full tangent bundle.
  let jM : ℝ × TangentBundle 𝓘(ℝ, E) M →
      TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (ℝ × M) :=
    fun p ↦ ⟨(p.1, p.2.proj), (0, p.2.snd)⟩
  let jN : ℝ × TangentBundle 𝓘(ℝ, F) N →
      TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (ℝ × N) :=
    fun p ↦ ⟨(p.1, p.2.proj), (0, p.2.snd)⟩
  let eM : TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (ℝ × M) ≃ₜ
      TangentBundle 𝓘(ℝ, ℝ) ℝ × TangentBundle 𝓘(ℝ, E) M :=
    { equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ 𝓘(ℝ, E) M with
      continuous_toFun := (contMDiff_equivTangentBundleProd (n := ∞)).continuous
      continuous_invFun := (contMDiff_equivTangentBundleProd_symm (n := ∞)).continuous }
  have hz : IsClosedEmbedding (fun t : ℝ ↦
      (⟨t, 0⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have hzero : IsClosedEmbedding (fun t : ℝ ↦ (t, (0 : ℝ))) := by
      exact ⟨isEmbedding_prodMkLeft 0, (isClosedMap_prodMk_right 0).isClosed_range⟩
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.isClosedEmbedding.comp hzero
  have hjMp : IsProperMap jM :=
    (eM.symm.isClosedEmbedding.comp (hz.prodMap IsClosedEmbedding.id)).isProperMap
  have hjNc : Continuous jN :=
    ((contMDiff_equivTangentBundleProd_symm (n := ∞)).comp
      (((contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ))).comp
        contMDiff_fst).prodMk contMDiff_snd)).continuous
  have hjNi : Function.Injective jN := by
    rintro ⟨t, ⟨y, v⟩⟩ ⟨s, ⟨z, w⟩⟩ h
    have hbase := congrArg TotalSpace.proj h
    have hts : t = s := congrArg Prod.fst hbase
    have hyz : y = z := congrArg Prod.snd hbase
    subst s
    subst z
    have hvw : v = w := congrArg Prod.snd (eq_of_heq (TotalSpace.mk.inj h).2)
    subst w
    rfl
  -- Differentiating the graph at zero time velocity is the actual vertical family.
  let A : ℝ × TangentBundle 𝓘(ℝ, E) M → ℝ × TangentBundle 𝓘(ℝ, F) N :=
    fun p ↦ (p.1, tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2)
  have hfactor : jN ∘ A =
      tangentMap (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) g ∘ jM := by
    funext p
    simp only [Function.comp_def, jM, jN, A, tangentMap, g]
    rw [mfderiv_prodMk mdifferentiableAt_fst (hf.mdifferentiable (by simp) _)]
    rw [mfderiv_fst]
    change (⟨(p.1, f p.1 p.2.proj), (0,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2.proj p.2.snd)⟩ :
      TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (ℝ × N)) =
      ⟨(p.1, f p.1 p.2.proj), (0, mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F)
        (fun p : ℝ × M ↦ f p.1 p.2) (p.1, p.2.proj) (0, p.2.snd))⟩
    rw [mfderiv_prod_eq_add_apply (hf.mdifferentiable (by simp) _), map_zero, zero_add]
  apply isProperMap_of_comp_of_inj
    (continuous_fst.prodMk (contMDiff_parameterTangentMap f hf).continuous) hjNc
    _ hjNi
  rw [hfactor]
  exact hTg.comp hjMp

set_option backward.isDefEq.respectTransparency false in
/-- A compact-source family induces a smooth embedding of the actual tangent cylinder. -/
theorem isSmoothEmbedding_parameterTangentMap [CompactSpace M] [T2Space M] [T2Space N]
    (f : ℝ → M → N)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M ↦ f p.1 p.2))
    (hemb : ∀ t, IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (f t)) :
    IsSmoothEmbedding (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E)).tangent)
      (𝓘(ℝ, ℝ).prod (𝓘(ℝ, F)).tangent) ∞
      (fun p : ℝ × TangentBundle 𝓘(ℝ, E) M ↦
        (p.1, tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2)) := by
  -- The full and native tangent product models use precisely the same bundle charts.
  let : ChartedSpace (E × E) (TangentBundle 𝓘(ℝ, E) M) :=
    inferInstanceAs (ChartedSpace (ModelProd E E) (TangentBundle 𝓘(ℝ, E) M))
  let : ChartedSpace (F × F) (TangentBundle 𝓘(ℝ, F) N) :=
    inferInstanceAs (ChartedSpace (ModelProd F F) (TangentBundle 𝓘(ℝ, F) N))
  let : IsManifold 𝓘(ℝ, E × E) ∞ (TangentBundle 𝓘(ℝ, E) M) := by
    simpa only [modelWithCornersSelf_prod] using
      (inferInstance : IsManifold (𝓘(ℝ, E)).tangent ∞ (TangentBundle 𝓘(ℝ, E) M))
  let : IsManifold 𝓘(ℝ, F × F) ∞ (TangentBundle 𝓘(ℝ, F) N) := by
    simpa only [modelWithCornersSelf_prod] using
      (inferInstance : IsManifold (𝓘(ℝ, F)).tangent ∞ (TangentBundle 𝓘(ℝ, F) N))
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, F × F) ∞
      (fun p : ℝ × TangentBundle 𝓘(ℝ, E) M ↦
        tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2) := by
    simpa only [modelWithCornersSelf_prod] using contMDiff_parameterTangentMap f hf
  have hAe (t : ℝ) : IsSmoothEmbedding 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) ∞
      (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) (f t)) := by
    simpa only [modelWithCornersSelf_prod] using isSmoothEmbedding_tangentMap (hemb t)
  have h := isSmoothEmbedding_parameterMap
    (fun t ↦ tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) (f t)) hA hAe
    (isProperMap_parameterTangentMap f hf hemb)
  simpa only [modelWithCornersSelf_prod] using h

end AtiyahSinger
