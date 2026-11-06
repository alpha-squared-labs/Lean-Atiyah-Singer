/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParameterizedNormalBundle
public import AtiyahSinger.Geometry.TangentNormalPullback
public import AtiyahSinger.Geometry.ZeroVelocityNormalPullback

/-!
# The ordered tangent-normal splitting on a parameter slice

Public module ID: M1341.

Restrict the actual tangent-normal splitting of a parameter embedding through
the zero-time-velocity normal comparison. On a fixed time slice, its ordered
factors agree with the genuine canonical tangent-normal sequence of the slice
embedding. The equality of tangent slice inclusions and zero-velocity inclusions
is proved before any quotient or fiber transport is used.

This is the same-witness endpoint comparison in SG III.13 isotopy invariance.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] productFullChartedSpace product_full_isManifold
  tangentBundleFullChartedSpace tangentBundle_full_isManifold normalBundleTopology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tangentMap_parameterSlice (E M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (t : ℝ) :
    smoothTangentMap (smoothParameterSlice E M t) =
      (zeroVelocityInclusion E M).comp
        (smoothParameterSlice (E × E) (TangentBundle 𝓘(ℝ, E) M) t) := by
  apply ContMDiffMap.ext
  intro z
  have hi : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) (smoothParameterSlice E M t) z.proj =
      ContinuousLinearMap.inr ℝ ℝ E := by
    have h := mfderiv_prodMk (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, E))
      (f := fun _ : M ↦ t) (g := id) (x := z.proj)
      mdifferentiableAt_const mdifferentiableAt_id
    rw [mfderiv_const, mfderiv_id] at h
    simpa only [modelWithCornersSelf_prod] using! h
  change (⟨(t, z.proj), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E)
    (smoothParameterSlice E M t) z.proj z.snd⟩ : TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × M)) =
      ⟨(t, z.proj), (0, z.snd)⟩
  rw [hi]
  rfl

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (β : ContMDiffMap 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) (ℝ × M) (ℝ × N) ∞)
  (H : ContMDiffMap 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F))
    (ℝ × TangentBundle 𝓘(ℝ, E) M) (ℝ × TangentBundle 𝓘(ℝ, F) N) ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hβ : IsSmoothEmbedding 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ β)
  (hH : IsImmersion 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) ∞ H)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "TP" => TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × M)
local notation "νf" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νβ" => NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) β
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "νTβ" => NormalBundle 𝓘(ℝ, (ℝ × E) × (ℝ × E))
  𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap β)
local notation "νH" => NormalBundle 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) H
local notation "Vf" => NormalModel E F
local notation "Vβ" => NormalModel (ℝ × E) (ℝ × F)
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "VTβ" => NormalModel ((ℝ × E) × (ℝ × E)) ((ℝ × F) × (ℝ × F))
local notation "VH" => NormalModel (ℝ × (E × E)) (ℝ × (F × F))
local notation "jM" => zeroVelocityInclusion E M
local notation "jN" => zeroVelocityInclusion F N

set_option maxHeartbeats 800000 in
-- The two nested tangent bases and their actual quotient reindexing are compared together.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same cylinder comparisons induce a normalized tangent-normal splitting at a slice. -/
theorem exists_parameterSlice_tangentNormalSplitting
    (t : ℝ) (hβslice : ∀ x, β (t, x) = (t, f x))
    (hHslice : ∀ z, H (t, z) = (t, smoothTangentMap f z))
    (e : ∀ x, νf x ≃L[ℝ] νβ (t, x))
    (eH : ∀ z : TM, νTf z ≃L[ℝ] νH (t, z))
    (eZ : ∀ p : ℝ × TM, νH p ≃L[ℝ] νTβ (jM p))
    (he : ∀ (x : M) (v : F),
      e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) β (t, x)).toLinearMap).mkQ
          (0, v))
    (heH : ∀ (z : TM) (v : F × F),
      eH z ((LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F)
        (smoothTangentMap f) z).toLinearMap).mkQ v) =
          (LinearMap.range (mfderiv 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F))
            H (t, z)).toLinearMap).mkQ (0, v))
    (heZ : ∀ (p : ℝ × TM) (v : ℝ × (F × F)),
      eZ p ((LinearMap.range (mfderiv 𝓘(ℝ, ℝ × (E × E))
        𝓘(ℝ, ℝ × (F × F)) H p).toLinearMap).mkQ v) =
          (LinearMap.range (mfderiv 𝓘(ℝ, (ℝ × E) × (ℝ × E))
            𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap β) (jM p)).toLinearMap).mkQ
              (mfderiv 𝓘(ℝ, ℝ × (F × F)) 𝓘(ℝ, (ℝ × F) × (ℝ × F)) jN (H p) v))
    (heis :
      letI := normalBundleFiberBundle f hf.isImmersion
      letI := normalBundleVectorBundle f hf.isImmersion
      letI := normalBundleContMDiffVectorBundle f hf.isImmersion
      letI := normalBundleFiberBundle β hβ.isImmersion
      letI := normalBundleVectorBundle β hβ.isImmersion
      letI := normalBundleContMDiffVectorBundle β hβ.isImmersion
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vβ)) (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
        (fun z : TotalSpace Vβ ((smoothParameterSlice E M t : M → ℝ × M) *ᵖ νβ) ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace Vf νf)))
    (heHs :
      letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
      letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
      letI := normalBundleContMDiffVectorBundle
        (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
      letI := normalBundleFiberBundle H hH
      letI := normalBundleVectorBundle H hH
      letI := normalBundleContMDiffVectorBundle H hH
      ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf)) (𝓘(ℝ, E × E).prod 𝓘(ℝ, VH)) ∞
        (fun z : TotalSpace VTf νTf ↦ (⟨z.proj, eH z.proj z.snd⟩ :
          TotalSpace VH ((smoothParameterSlice (E × E) TM t : TM → ℝ × TM) *ᵖ νH))))
    (heZs :
      letI := normalBundleFiberBundle H hH
      letI := normalBundleVectorBundle H hH
      letI := normalBundleContMDiffVectorBundle H hH
      letI := normalBundleFiberBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      letI := normalBundleVectorBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      letI := normalBundleContMDiffVectorBundle
        (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
      ContMDiff (𝓘(ℝ, ℝ × (E × E)).prod 𝓘(ℝ, VH))
        (𝓘(ℝ, ℝ × (E × E)).prod 𝓘(ℝ, VTβ)) ∞
        (fun z : TotalSpace VH νH ↦ (⟨z.proj, eZ z.proj z.snd⟩ :
          TotalSpace VTβ ((jM : ℝ × TM → TP) *ᵖ νTβ))))
    (Sβ : TangentNormalSplitting β hβ) :
    ∃ S : TangentNormalSplitting f hf, ∀ (z : TM) (v : νTf z),
      Sβ.equiv (jM (t, z)) (eZ (t, z) (eH z v)) =
        (e z.proj (S.equiv z v).1, e z.proj (S.equiv z v).2) := by
  classical
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle β hβ.isImmersion
  let := normalBundleVectorBundle β hβ.isImmersion
  let := normalBundleContMDiffVectorBundle β hβ.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleFiberBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
  let := normalBundleVectorBundle (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap β) (isImmersion_smoothTangentMap β hβ)
  let := normalBundleFiberBundle H hH
  let := normalBundleVectorBundle H hH
  let := normalBundleContMDiffVectorBundle H hH
  let i := smoothParameterSlice E M t
  let j := smoothParameterSlice F N t
  let Ti := smoothTangentMap i
  have hTi (z : TM) : Ti z = jM (t, z) :=
    congrArg (fun k ↦ k z) (tangentMap_parameterSlice E M t)
  -- Equality transport only reindexes the original quotient fiber; it fixes representatives.
  let transport (a b : TP) (h : a = b) : νTβ a ≃L[ℝ] νTβ b := by
    subst b
    exact ContinuousLinearEquiv.refl ℝ (νTβ a)
  have htransport (a b : TP) (h : a = b) (v : νTβ a) : HEq (transport a b h v) v := by
    subst b
    rfl
  have htransport_mk (a b : TP) (h : a = b) (v : (ℝ × F) × (ℝ × F)) :
      transport a b h ((LinearMap.range (mfderiv 𝓘(ℝ, (ℝ × E) × (ℝ × E))
        𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap β) a).toLinearMap).mkQ v) =
      (LinearMap.range (mfderiv 𝓘(ℝ, (ℝ × E) × (ℝ × E))
        𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap β) b).toLinearMap).mkQ v := by
    subst b
    rfl
  let eT (z : TM) : νTf z ≃L[ℝ] νTβ (Ti z) :=
    ((eH z).trans (eZ (t, z))).trans (transport _ _ (hTi z).symm)
  have heT (z : TM) (v : νTf z) :
      (⟨Ti z, eT z v⟩ : TotalSpace VTβ νTβ) = ⟨jM (t, z), eZ (t, z) (eH z v)⟩ :=
    TotalSpace.ext (hTi z) (htransport _ _ (hTi z).symm _)
  have hJ (y : N) : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ × F) j y =
      ContinuousLinearMap.inr ℝ ℝ F := by
    have h := mfderiv_prodMk (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, F))
      (f := fun _ : N ↦ t) (g := id) (x := y)
      mdifferentiableAt_const mdifferentiableAt_id
    rw [mfderiv_const, mfderiv_id] at h
    simpa only [modelWithCornersSelf_prod] using! h
  have hTJ (z : TM) (v : F × F) :
      mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap j)
        (smoothTangentMap f z) v =
      mfderiv 𝓘(ℝ, ℝ × (F × F)) 𝓘(ℝ, (ℝ × F) × (ℝ × F)) jN
        (H (t, z)) (0, v) := by
    let s := smoothParameterSlice (F × F) TN t
    have hs : mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, ℝ × (F × F)) s (smoothTangentMap f z) =
        ContinuousLinearMap.inr ℝ ℝ (F × F) := by
      have h := mfderiv_prodMk (I := 𝓘(ℝ, F × F)) (I' := 𝓘(ℝ, ℝ))
        (I'' := 𝓘(ℝ, F × F)) (f := fun _ : TN ↦ t) (g := id)
        (x := smoothTangentMap f z) mdifferentiableAt_const mdifferentiableAt_id
      rw [mfderiv_const, mfderiv_id] at h
      simpa only [modelWithCornersSelf_prod] using! h
    have h := mfderiv_comp (smoothTangentMap f z)
      ((jN).contMDiff.mdifferentiable (by simp) (s (smoothTangentMap f z)))
      (s.contMDiff.mdifferentiable (by simp) (smoothTangentMap f z))
    have hfun : (jN : ℝ × TN → _) ∘ s = (smoothTangentMap j : TN → _) := by
      funext y
      exact congrArg (fun k ↦ k y) (tangentMap_parameterSlice F N t).symm
    rw [hfun, hs] at h
    rw [hHslice]
    exact congrArg (fun L : (F × F) →L[ℝ] ((ℝ × F) × (ℝ × F)) ↦ L v) h
  have heTmk (z : TM) (v : F × F) :
      eT z ((LinearMap.range (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F)
        (smoothTangentMap f) z).toLinearMap).mkQ v) =
      (LinearMap.range (mfderiv 𝓘(ℝ, (ℝ × E) × (ℝ × E))
        𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap β) (Ti z)).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, (ℝ × F) × (ℝ × F)) (smoothTangentMap j)
            (smoothTangentMap f z) v) := by
    change transport _ _ (hTi z).symm (eZ (t, z) (eH z _)) = _
    rw [heH, heZ, htransport_mk, hTJ]
  -- Smoothness is checked on actual lifted total spaces before reindexing by the equal base.
  have hL : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
      (𝓘(ℝ, ℝ × (E × E)).prod 𝓘(ℝ, VH)) ∞
      (fun z : TotalSpace VTf νTf ↦ (⟨(t, z.proj), eH z.proj z.snd⟩ : TotalSpace VH νH)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨(smoothParameterSlice (E × E) TM t).contMDiff.contMDiffAt.comp z
      (Bundle.contMDiffAt_proj νTf), (Bundle.contMDiffAt_totalSpace.mp (heHs z)).2⟩
  have hZ := heZs.comp hL
  have hLift : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
      (𝓘(ℝ, (ℝ × E) × (ℝ × E)).prod 𝓘(ℝ, VTβ)) ∞
      (fun z : TotalSpace VTf νTf ↦ (⟨jM (t, z.proj), eZ (t, z.proj)
        (eH z.proj z.snd)⟩ : TotalSpace VTβ νTβ)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨(jM).contMDiff.contMDiffAt.comp z
      ((smoothParameterSlice (E × E) TM t).contMDiff.contMDiffAt.comp z
        (Bundle.contMDiffAt_proj νTf)), (Bundle.contMDiffAt_totalSpace.mp (hZ z)).2⟩
  have hLift' : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
      (𝓘(ℝ, (ℝ × E) × (ℝ × E)).prod 𝓘(ℝ, VTβ)) ∞
      (fun z : TotalSpace VTf νTf ↦ (⟨Ti z.proj, eT z.proj z.snd⟩ : TotalSpace VTβ νTβ)) :=
    hLift.congr (fun z ↦ heT z.proj z.snd)
  have heTs : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTf))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTβ)) ∞
      (fun z : TotalSpace VTf νTf ↦ (⟨z.proj, eT z.proj z.snd⟩ :
        TotalSpace VTβ ((Ti : TM → TP) *ᵖ νTβ))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨Bundle.contMDiffAt_proj νTf, (Bundle.contMDiffAt_totalSpace.mp (hLift' z)).2⟩
  have heRep (x : M) (v : F) :
      e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
      (LinearMap.range (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) β (i x)).toLinearMap).mkQ
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ × F) j (f x) v) := by
    rw [hJ]
    exact he x v
  have hcanonical := tangentNormalPullback_maps_commute f β i j hf hβ
    (fun x ↦ (hβslice x).symm) (fun x ↦ (e x).toContinuousLinearMap)
    (fun z ↦ (eT z).toContinuousLinearMap) heRep heTmk
  obtain ⟨S, hS⟩ := exists_tangentNormalSplitting_of_pullback f β i hf hβ e eT heis heTs
    hcanonical.1 hcanonical.2 Sβ
  refine ⟨S, ?_⟩
  intro z v
  have hleft : Sβ.equiv (Ti z) (eT z v) =
      Sβ.equiv (jM (t, z)) (eZ (t, z) (eH z v)) := by
    have h := congrArg (fun q : TotalSpace VTβ νTβ ↦
      (⟨q.proj.proj, Sβ.equiv q.proj q.snd⟩ : TotalSpace (Vβ × Vβ) (νβ ×ᵇ νβ))) (heT z v)
    exact eq_of_heq (congr_arg_heq (fun q : TotalSpace (Vβ × Vβ) (νβ ×ᵇ νβ) ↦ q.snd) h)
  rw [← hleft, hS]
  apply Prod.ext
  · exact ((e z.proj).apply_symm_apply _).symm
  · exact ((e z.proj).apply_symm_apply _).symm

end AtiyahSinger
