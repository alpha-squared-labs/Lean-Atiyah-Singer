/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OpenTubularTransport
public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.OpenComplexNormal
public import AtiyahSinger.Topology.TangentEmbeddingPushforward

/-!
# The same normal data in an open smooth square

Public module ID: M2232.

Actual ambient derivatives induce the real quotient comparisons. The same
comparisons transport the supplied tangent-normal splitting and its ordered
complexification, so their total-space maps agree before taking Thom classes.
This is the geometric input for open locality of the tangent pushforward.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff TensorProduct

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology complexifiedNormalPullbackTopology

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

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TP" => TangentBundle 𝓘(ℝ, G) P

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An open square transports one splitting and complexification through the same normal maps. -/
theorem exists_openSquare_tangentNormalData
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, G) 𝓘(ℝ, H) P Q ∞)
    (i : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
    (j : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, H) N Q ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsSmoothEmbedding 𝓘(ℝ, G) 𝓘(ℝ, H) ∞ g)
    (hi : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ i)
    (hj : IsLocalDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, H) ∞ j)
    (hcomm : ∀ x, j (f x) = g (i x)) (Sg : TangentNormalSplitting g hg) :
    let Ti := smoothTangentMap i
    let D := (Ti : TM → TP) *ᵖ (ComplexifiedNormalPullback g)
    letI : ∀ z : TM, AddCommGroup (D z) := fun z ↦ by
      change AddCommGroup (ComplexifiedNormalPullback g (Ti z)); infer_instance
    letI : ∀ z : TM, Module ℂ (D z) := fun z ↦ by
      change Module ℂ (ComplexifiedNormalPullback g (Ti z)); infer_instance
    ∃ (eT : ∀ z : TM,
        NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z ≃L[ℝ]
          NormalBundle 𝓘(ℝ, G × G) 𝓘(ℝ, H × H) (smoothTangentMap g) (Ti z))
      (S : TangentNormalSplitting f hf)
      (U : ComplexBundle.Iso (ComplexifiedNormalPullback f) D),
      (∀ (z : TM) (v : F × F),
        eT z ((LinearMap.range
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ v) =
          (LinearMap.range (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, H × H)
            (smoothTangentMap g) (Ti z)).toLinearMap).mkQ
              (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, H × H) (smoothTangentMap j)
                (smoothTangentMap f z) v)) ∧
      ∀ (z : TM) (v : ComplexifiedNormalPullback f z),
        eT z ((complexifiedNormalTotalHomeomorph f hf S ⟨z, v⟩).snd) =
          (complexifiedNormalTotalHomeomorph g hg Sg ⟨Ti z, U.linearEquiv z v⟩).snd := by
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
  let Ti := smoothTangentMap i
  let D := (Ti : TM → TP) *ᵖ (ComplexifiedNormalPullback g)
  let (z : TM) : AddCommGroup (D z) := by
    change AddCommGroup (ComplexifiedNormalPullback g (Ti z)); infer_instance
  let (z : TM) : Module ℂ (D z) := by
    change Module ℂ (ComplexifiedNormalPullback g (Ti z)); infer_instance
  -- Differentiate the given square before comparing either original normal quotient.
  have hTcomm (z : TM) : smoothTangentMap j (smoothTangentMap f z) =
      smoothTangentMap g (Ti z) := by
    have hl := tangentMap_comp_at z (j.contMDiff.mdifferentiable (by simp) (f z.proj))
      (f.contMDiff.mdifferentiable (by simp) z.proj)
    have hr := tangentMap_comp_at z (g.contMDiff.mdifferentiable (by simp) (i z.proj))
      (i.contMDiff.mdifferentiable (by simp) z.proj)
    rw [show (j : N → Q) ∘ f = (g : P → Q) ∘ i from funext hcomm] at hl
    exact hl.symm.trans hr
  obtain ⟨e, he, hes, heis⟩ := exists_normalPullback_equiv_of_localDiffeomorph
    f g i j hf.isImmersion hg.isImmersion hi hj hcomm
  obtain ⟨eT, heT, heTs, _⟩ := exists_normalPullback_equiv_of_localDiffeomorph
    (smoothTangentMap f) (smoothTangentMap g) Ti (smoothTangentMap j)
    (isImmersion_smoothTangentMap f hf) (isImmersion_smoothTangentMap g hg)
    (isLocalDiffeomorph_smoothTangentMap i hi) (isLocalDiffeomorph_smoothTangentMap j hj) hTcomm
  have hmaps := tangentNormalPullback_maps_commute f g i j hf hg hcomm
    (fun x ↦ (e x).toContinuousLinearMap) (fun z ↦ (eT z).toContinuousLinearMap) he heT
  obtain ⟨S, hS⟩ := exists_tangentNormalSplitting_of_pullback f g i hf hg
    e eT heis heTs hmaps.1 hmaps.2 Sg
  obtain ⟨U, hU⟩ := exists_complexifiedNormalPullback_iso f g i hf.isImmersion hg.isImmersion
    e hes heis
  refine ⟨eT, S, U, heT, ?_⟩
  rcases U with ⟨ue, hUs, hUi⟩
  intro z v
  -- Scalar extension applies this same real map to the two ordered coordinates.
  let rf := complexificationReIm (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj)
  let rg := complexificationReIm (NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, H) g (i z.proj))
  have hcoords (v : ComplexifiedNormalPullback f z) :
      rg (ue z v) = (e z.proj (rf v).1, e z.proj (rf v).2) := by
    rw [hU]
    induction v using TensorProduct.inductionOn with
    | tmul c v =>
      change complexificationReIm _
        (((e z.proj).toLinearEquiv.baseChange ℝ ℂ _ _) (c ⊗ₜ[ℝ] v)) = _
      rw [LinearEquiv.baseChange_tmul, (complexificationReIm_properties _).1]
      change _ = (e z.proj ((complexificationReIm _ (c ⊗ₜ[ℝ] v)).1),
        e z.proj ((complexificationReIm _ (c ⊗ₜ[ℝ] v)).2))
      rw [(complexificationReIm_properties _).1, map_smul, map_smul]
      rfl
    | add u v hu hv =>
      simp only [map_add, hu, hv, Prod.fst_add, Prod.snd_add]
      rfl
  change eT z ((S.equiv z).symm (rf v)) = (Sg.equiv (Ti z)).symm (rg (ue z v))
  apply (Sg.equiv (Ti z)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, hcoords]
  have h := hS z ((S.equiv z).symm (rf v))
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  apply Prod.ext
  · exact ((e z.proj).apply_symm_apply _).symm.trans
      (congrArg (e z.proj) (congrArg Prod.fst h).symm)
  · exact ((e z.proj).apply_symm_apply _).symm.trans
      (congrArg (e z.proj) (congrArg Prod.snd h).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An open source restriction has a whole tangent tube with the same complex-normal map. -/
theorem exists_tangentEmbeddingTubularMap_openSource
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, G) 𝓘(ℝ, F) P N ∞)
    (i : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsSmoothEmbedding 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ g)
    (hi : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ i)
    (hinj : Function.Injective i) (hcomm : ∀ x, f x = g (i x))
    (Sg : TangentNormalSplitting g hg)
    (Tg : TubularNeighborhood (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)) :
    let Ti := smoothTangentMap i
    let D := (Ti : TM → TP) *ᵖ (ComplexifiedNormalPullback g)
    letI : ∀ z : TM, AddCommGroup (D z) := fun z ↦ by
      change AddCommGroup (ComplexifiedNormalPullback g (Ti z)); infer_instance
    letI : ∀ z : TM, Module ℂ (D z) := fun z ↦ by
      change Module ℂ (ComplexifiedNormalPullback g (Ti z)); infer_instance
    ∃ (S : TangentNormalSplitting f hf)
      (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
      (U : ComplexBundle.Iso (ComplexifiedNormalPullback f) D),
      ∀ w : TotalSpace Unit (ComplexifiedNormalPullback f),
        tangentEmbeddingTubularMap f hf S T w =
          tangentEmbeddingTubularMap g hg Sg Tg ⟨Ti w.proj, U.linearEquiv w.proj w.snd⟩ := by
  classical
  let idN := ContMDiffMap.id (I := 𝓘(ℝ, F)) (M := N) (n := ∞)
  have hid : smoothTangentMap idN =
      ContMDiffMap.id (I := 𝓘(ℝ, F × F)) (M := TangentBundle 𝓘(ℝ, F) N) := by
    apply ContMDiffMap.ext
    intro z
    change tangentMap 𝓘(ℝ, F) 𝓘(ℝ, F) id z = z
    rw [tangentMap_id]
    rfl
  obtain ⟨eT, S, U, heT, hnormal⟩ := exists_openSquare_tangentNormalData f g i idN hf hg
    hi (Diffeomorph.refl 𝓘(ℝ, F) N ∞).isLocalDiffeomorph hcomm Sg
  have hTcomm (z : TM) : smoothTangentMap f z = smoothTangentMap g (smoothTangentMap i z) := by
    have hr := tangentMap_comp_at z (g.contMDiff.mdifferentiable (by simp) (i z.proj))
      (i.contMDiff.mdifferentiable (by simp) z.proj)
    rw [show (g : P → N) ∘ i = f from (funext hcomm).symm] at hr
    exact hr
  have he (z : TM) (v : F × F) :
      eT z ((LinearMap.range
        (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, G × G) 𝓘(ℝ, F × F)
          (smoothTangentMap g) (smoothTangentMap i z)).toLinearMap).mkQ v := by
    have h := heT z v
    rw [hid] at h
    have hd : mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F × F)
        (ContMDiffMap.id (I := 𝓘(ℝ, F × F))
          (M := TangentBundle 𝓘(ℝ, F) N) (n := ∞)) (smoothTangentMap f z) =
        ContinuousLinearMap.id ℝ (F × F) := by
      change mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F × F) id (smoothTangentMap f z) = _
      rw [mfderiv_id]
      rfl
    rw [hd] at h
    exact h
  have hinjT : Function.Injective (smoothTangentMap i) := by
    rintro ⟨x, v⟩ ⟨y, w⟩ heq
    have hxy : x = y := hinj (congrArg TotalSpace.proj heq)
    subst y
    have hvw := congrArg (fun z ↦ z.snd) heq
    have hd := (hi.isInvertible_mfderiv (by simp) x).injective hvw
    exact congrArg (TotalSpace.mk x) hd
  obtain ⟨T, hT⟩ := exists_tubularNeighborhood_openSource
    (smoothTangentMap f) (smoothTangentMap g) (smoothTangentMap i)
    (isImmersion_smoothTangentMap f hf) (isImmersion_smoothTangentMap g hg)
    (isLocalDiffeomorph_smoothTangentMap i hi) hinjT hTcomm eT he Tg
  refine ⟨S, T, U, ?_⟩
  intro w
  change T.totalMap _ _ ⟨w.proj, (complexifiedNormalTotalHomeomorph f hf S w).snd⟩ = _
  rw [hT]
  change Tg.totalMap _ _ ⟨smoothTangentMap i w.proj,
    eT w.proj (complexifiedNormalTotalHomeomorph f hf S w).snd⟩ = _
  rw [hnormal]
  rfl

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An ambient open chart transports the actual tube through the specified complex-normal map. -/
theorem exists_tangentEmbeddingTubularMap_openAmbient
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
    (j : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ g)
    (hj : IsLocalDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ j)
    (hinj : Function.Injective j) (hcomm : ∀ x, j (f x) = g x)
    (Sg : TangentNormalSplitting g hg)
    (Tf : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)) :
    ∃ (S : TangentNormalSplitting f hf)
      (T : TubularNeighborhood (smoothTangentMap g) (isImmersion_smoothTangentMap g hg))
      (U : ComplexBundle.Iso (ComplexifiedNormalPullback f) (ComplexifiedNormalPullback g)),
      ∀ w : TotalSpace Unit (ComplexifiedNormalPullback f),
        smoothTangentMap j (tangentEmbeddingTubularMap f hf S Tf w) =
          tangentEmbeddingTubularMap g hg Sg T (U.totalHomeomorph w) := by
  classical
  let := isFiniteRank_complexifiedNormalPullback g hg.isImmersion
  let idM := ContMDiffMap.id (I := 𝓘(ℝ, E)) (M := M) (n := ∞)
  have hid : smoothTangentMap idM = ContMDiffMap.id (I := 𝓘(ℝ, E × E)) (M := TM) := by
    apply ContMDiffMap.ext
    intro z
    change tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) id z = z
    rw [tangentMap_id]
    rfl
  have hdata := exists_openSquare_tangentNormalData f g idM j hf hg
    (Diffeomorph.refl 𝓘(ℝ, E) M ∞).isLocalDiffeomorph hj hcomm Sg
  dsimp only at hdata
  rw [hid] at hdata
  obtain ⟨eT, S, U₀, heT, hnormal⟩ := hdata
  let U : ComplexBundle.Iso (ComplexifiedNormalPullback f) (ComplexifiedNormalPullback g) :=
    U₀.trans (ComplexBundle.pullbackIdIso (E := ComplexifiedNormalPullback g))
  have hU (z : TM) (v : ComplexifiedNormalPullback f z) :
      U.linearEquiv z v = U₀.linearEquiv z v := by
    change (ComplexBundle.pullbackIdIso (E := ComplexifiedNormalPullback g)).linearEquiv z
      (U₀.linearEquiv z v) = _
    rw [ComplexBundle.pullbackIdIso_apply]
  have hTcomm (z : TM) : smoothTangentMap j (smoothTangentMap f z) = smoothTangentMap g z := by
    have hl := tangentMap_comp_at z (j.contMDiff.mdifferentiable (by simp) (f z.proj))
      (f.contMDiff.mdifferentiable (by simp) z.proj)
    rw [show (j : N → P) ∘ f = g from funext hcomm] at hl
    exact hl.symm
  have hinjT : Function.Injective (smoothTangentMap j) := by
    rintro ⟨x, v⟩ ⟨y, w⟩ heq
    have hxy : x = y := hinj (congrArg TotalSpace.proj heq)
    subst y
    have hvw := congrArg (fun z ↦ z.snd) heq
    have hd := (hj.isInvertible_mfderiv (by simp) x).injective hvw
    exact congrArg (TotalSpace.mk x) hd
  obtain ⟨T, hT⟩ := exists_tubularNeighborhood_openAmbient
    (smoothTangentMap f) (smoothTangentMap g) (smoothTangentMap j)
    (isImmersion_smoothTangentMap f hf) (isImmersion_smoothTangentMap g hg)
    (isLocalDiffeomorph_smoothTangentMap j hj) hinjT hTcomm eT heT Tf
  refine ⟨S, T, U, ?_⟩
  intro w
  change smoothTangentMap j (Tf.totalMap _ _ (complexifiedNormalTotalHomeomorph f hf S w)) =
    T.totalMap _ _ ⟨w.proj,
      (complexifiedNormalTotalHomeomorph g hg Sg ⟨w.proj, U.linearEquiv w.proj w.snd⟩).snd⟩
  rw [hT]
  have hn := hnormal w.proj w.snd
  have hmap := congrArg (fun v : ComplexifiedNormalPullback g w.proj ↦
    (show NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) (smoothTangentMap g) w.proj from
      (complexifiedNormalTotalHomeomorph g hg Sg ⟨w.proj, v⟩).snd)) (hU w.proj w.snd)
  have hn' := congrArg (eT w.proj).symm (hn.trans hmap.symm)
  rw [ContinuousLinearEquiv.symm_apply_apply] at hn'
  apply congrArg (smoothTangentMap j)
  apply congrArg (Tf.totalMap _ _)
  exact TotalSpace.ext rfl (heq_of_eq hn')

end AtiyahSinger
