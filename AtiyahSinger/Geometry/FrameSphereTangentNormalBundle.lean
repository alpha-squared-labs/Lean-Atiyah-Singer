/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleNormalDerivative
public import AtiyahSinger.Geometry.FrameSphereNormalBundle
public import AtiyahSinger.Geometry.FrameSphereTangentParametrization
public import AtiyahSinger.Geometry.TangentNormalSplittingCriterion

/-!
# The ordered normal derivative of the actual frame-sphere tangent chart

Public module ID: M1251.

The actual tangent parametrization, with a horizontal lift adapted to the
south section, has an invertible normal derivative. Its first component is
the original base normal derivative; on the second factor it is the original
vertical map. Exactness gives the required ordered splitting without removing
the lower-left term contributed by variation of the horizontal lift.

All maps, quotient normals, tangent models and radial curves are the specified
native ones. This is the normal comparison required by the frame-sphere tube;
the cotangent musical and pole comparisons are separate geometric comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Topology
open scoped ContDiff

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere
  normalBundleTopology verticalTangentTopology tangentBundleFullChartedSpace
  tangentBundle_full_isManifold

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxSynthPendingDepth 55 in
set_option maxHeartbeats 2800000 in
-- Both canonical normal components are checked on the same actual radial family.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tangent chart determines a normalized ordered splitting of its normal bundle. -/
theorem exists_frameSphere_tangentNormalSplitting
    (H : letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
      let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let I := 𝓘(ℝ, EB)
    let J := 𝓘(ℝ, EB × R)
    let H' : SmoothHorizontalLift (smoothAssociatedSphereProjection S) := H
    let a := frameSphereStereographic (EB := EB) r V
    let j : ContMDiffMap I J B Z ∞ :=
      ⟨fun x ↦ a.symm ⟨x, 0⟩,
        (frameSphereStereographic_spec (EB := EB) r V).2.2.2.2.2.comp
          (contMDiff_zeroSection ℝ V)⟩
    let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := EB) r V
    let F := (exists_frameSphere_tangentParametrization (EB := EB) r V H).choose
    let e := (exists_frameSphere_normalEquiv (EB := EB) r V).choose
    ∀ (_hH : ∀ x : B, H'.lift (j x) = mfderiv I J j x),
      (∀ z : TangentBundle I B, (F ⟨z, 0, 0⟩ : TangentBundle J Z) =
        smoothTangentMap j z) ∧
      ∃ K : TangentNormalSplitting j hj,
        ∀ (z : TangentBundle I B) (u w : V z.proj),
          (K.equiv z).symm (e z.proj u, e z.proj w) =
            (LinearMap.range (mfderiv 𝓘(ℝ, EB × EB) 𝓘(ℝ, (EB × R) × (EB × R))
              (smoothTangentMap j) z).toLinearMap).mkQ
                (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, (EB × R) × (EB × R))
                  (fun t : ℝ ↦ (F ⟨z, t • u, t • w⟩ : TangentBundle J Z)) 0
                  ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)) := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let IT := 𝓘(ℝ, EB × EB)
  let JT := 𝓘(ℝ, (EB × R) × (EB × R))
  let a := frameSphereStereographic (EB := EB) r V
  let j : ContMDiffMap I J B Z ∞ :=
    ⟨fun x ↦ a.symm ⟨x, 0⟩,
      (frameSphereStereographic_spec (EB := EB) r V).2.2.2.2.2.comp
        (contMDiff_zeroSection ℝ V)⟩
  let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := EB) r V
  let F := (exists_frameSphere_tangentParametrization (EB := EB) r V H).choose
  have hF := (exists_frameSphere_tangentParametrization (EB := EB) r V H).choose_spec
  let e := (exists_frameSphere_normalEquiv (EB := EB) r V).choose
  have he := (exists_frameSphere_normalEquiv (EB := EB) r V).choose_spec
  dsimp only
  intro hH
  let q : ContMDiffMap J I Z B ∞ := smoothAssociatedSphereProjection S
  let L : ∀ z : TotalSpace R V, V z.proj ≃L[ℝ]
      VerticalTangentFiber J I q (a.symm z) :=
    (exists_frameSphere_verticalDerivativeEquiv (EB := EB) r V).choose
  have hL (z : TotalSpace R V) (v : V z.proj) : (L z v).val =
      mfderiv 𝓘(ℝ, ℝ) J (fun t : ℝ ↦ a.symm ⟨z.proj, z.snd + t • v⟩) 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) :=
    (exists_frameSphere_verticalDerivativeEquiv (EB := EB) r V).choose_spec.1 z v
  have hformula (z : TangentBundle I B) (u w : V z.proj) :
      let horizontal : EB × R := H.lift (a.symm ⟨z.proj, u⟩) z.snd
      let vertical : EB × R := (L ⟨z.proj, u⟩ w).val
      (F ⟨z, u, w⟩ : TangentBundle J Z) = ⟨a.symm ⟨z.proj, u⟩, horizontal + vertical⟩ := by
    apply (hF z u w).trans
    exact Bundle.TotalSpace.ext rfl (heq_of_eq
      (congrArg (fun v : EB × R ↦
        (show EB × R from H.lift (a.symm ⟨z.proj, u⟩) z.snd) + v)
          (hL ⟨z.proj, u⟩ w).symm))
  have hzero (z : TangentBundle I B) :
      (F ⟨z, 0, 0⟩ : TangentBundle J Z) = smoothTangentMap j z := by
    rw [hformula]
    have hhorizontal := DFunLike.congr_fun (hH z.proj) z.snd
    change (H.lift (j z.proj) z.snd : EB × R) = mfderiv I J j z.proj z.snd at hhorizontal
    change _ = (⟨j z.proj, mfderiv I J j z.proj z.snd⟩ : TangentBundle J Z)
    apply Bundle.TotalSpace.ext
    · rfl
    · apply heq_of_eq
      change (H.lift (j z.proj) z.snd : EB × R) + (L ⟨z.proj, 0⟩ 0).val = _
      rw [map_zero, Submodule.coe_zero, add_zero]
      exact hhorizontal
  refine ⟨hzero, ?_⟩
  let prT : ContMDiffMap IT I (TangentBundle I B) B ∞ :=
    ⟨Bundle.TotalSpace.proj, (smoothTangentBundleProjection EB B).contMDiff⟩
  let Vt := (prT : TangentBundle I B → B) *ᵖ V
  let (z : TangentBundle I B) : NormedAddCommGroup (Vt z) := by
    change NormedAddCommGroup (V z.proj)
    infer_instance
  let (z : TangentBundle I B) : NormedSpace ℝ (Vt z) := by
    change NormedSpace ℝ (V z.proj)
    infer_instance
  let W := Vt ×ᵇ Vt
  let : FiberBundle (R × R) W := by
    change FiberBundle (R × R) (Vt ×ᵇ Vt)
    infer_instance
  let : VectorBundle ℝ (R × R) W := by
    change VectorBundle ℝ (R × R) (Vt ×ᵇ Vt)
    infer_instance
  let : ContMDiffVectorBundle ∞ (R × R) W IT := by
    change ContMDiffVectorBundle ∞ (R × R) (Vt ×ᵇ Vt) IT
    infer_instance
  let C := IT.prod 𝓘(ℝ, R × R)
  let fT := smoothTangentMap j
  let hfT := isImmersion_smoothTangentMap j hj
  let := normalBundleFiberBundle j hj.isImmersion
  let := normalBundleVectorBundle j hj.isImmersion
  let := normalBundleContMDiffVectorBundle j hj.isImmersion
  let := normalBundleFiberBundle fT hfT
  let := normalBundleVectorBundle fT hfT
  let := normalBundleContMDiffVectorBundle fT hfT
  let ν := NormalBundle I J j
  let νT := NormalBundle IT JT fT
  let N := NormalModel EB (EB × R)
  let NT := NormalModel (EB × EB) ((EB × R) × (EB × R))
  let νP := (prT : TangentBundle I B → B) *ᵖ ν
  let A : ContMDiffMap C JT (TotalSpace (R × R) W) (TangentBundle J Z) ∞ :=
    ⟨fun z ↦ (F z : TangentBundle J Z), by
      change ContMDiff (IT.prod 𝓘(ℝ, R × R)) JT ∞ _
      rw (occs := .pos [1]) [show IT = I.tangent from modelWithCornersSelf_prod]
      rw (occs := .pos [1]) [show JT = J.tangent from modelWithCornersSelf_prod]
      exact contMDiff_subtype_val.comp F.contMDiff_toFun⟩
  let D : ∀ z : TangentBundle I B, W z →L[ℝ] νT z :=
    (exists_bundle_normalDerivative W fT hfT A hzero).choose
  have hD := (exists_bundle_normalDerivative W fT hfT A hzero).choose_spec.1
  have hDsmooth := (exists_bundle_normalDerivative W fT hfT A hzero).choose_spec.2
  let p := tangentNormalProjection j hj
  let i := tangentNormalVerticalMap j hj
  have hcurve (z : TangentBundle I B) (v : W z) :
      ContMDiff 𝓘(ℝ, ℝ) JT ∞ (fun t : ℝ ↦ A ⟨z, t • v⟩) := by
    apply A.contMDiff.comp
    intro t
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_const, ?_⟩
    let b := trivializationAt (R × R) W z
    have hz : z ∈ b.baseSet := mem_baseSet_trivializationAt (R × R) W z
    have hlinear : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, R × R) ∞
        (fun t : ℝ ↦ t • (b ⟨z, v⟩).2) t := contMDiffAt_id.smul contMDiffAt_const
    apply hlinear.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro t
    change (b ⟨z, t • v⟩).2 = t • (b ⟨z, v⟩).2
    simp only [← b.continuousLinearMapAt_apply_of_mem ℝ hz, map_smul]
  -- The tangent projection of the actual curve is the original stereographic radial curve.
  have hfirst (z : TangentBundle I B) (u w : V z.proj) :
      p z (D z (u, w)) = e z.proj u := by
    let ρ : ℝ → TangentBundle J Z := fun t ↦ A ⟨z, t • (u, w)⟩
    let pr := smoothTangentBundleProjection (EB × R) Z
    have hρ0 : ρ 0 = fT z := by
      change (F ⟨z, (0 : ℝ) • u, (0 : ℝ) • w⟩ : TangentBundle J Z) = smoothTangentMap j z
      rw [zero_smul, zero_smul]
      exact hzero z
    have hproj : pr ∘ ρ = fun t : ℝ ↦ a.symm ⟨z.proj, t • u⟩ := by
      funext t
      exact congrArg (fun y : TangentBundle J Z ↦ y.proj) (hformula z (t • u) (t • w))
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := JT) (I'' := J) 0
      (pr.contMDiff.mdifferentiable (by simp) (ρ 0))
      ((hcurve z (u, w)).mdifferentiable (by simp) 0)
    rw [hρ0, hproj] at hchain
    let v : (EB × R) × (EB × R) := mfderiv 𝓘(ℝ, ℝ) JT ρ 0
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)
    have hp := (exists_tangentNormal_exactSequence j hj).choose_spec.choose_spec.2.2.2.1 z v
    have hd := DFunLike.congr_fun hchain
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)
    calc
      p z (D z (u, w)) =
          p z ((LinearMap.range (mfderiv IT JT fT z).toLinearMap).mkQ v) :=
        congrArg (p z) (hD z (u, w))
      _ = (LinearMap.range (mfderiv I J j z.proj).toLinearMap).mkQ
          (mfderiv JT J pr (fT z) v) := hp
      _ = (LinearMap.range (mfderiv I J j z.proj).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, ℝ) J (fun t : ℝ ↦ a.symm ⟨z.proj, t • u⟩) 0
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)) :=
        congrArg (LinearMap.range (mfderiv I J j z.proj).toLinearMap).mkQ hd.symm
      _ = e z.proj u := (he.1 z.proj u).symm
  -- A pure second-factor curve lies in one tangent fiber; adaptation fixes its base velocity.
  have hvertical (z : TangentBundle I B) (w : V z.proj) :
      D z (0, w) = i z (e z.proj w) := by
    let y := fT z
    let v : EB × R := (L ⟨z.proj, 0⟩ w).val
    let b := trivializationAt (EB × R) (TangentSpace J) y.proj
    have hy : y.proj ∈ b.baseSet :=
      mem_baseSet_trivializationAt (EB × R) (TangentSpace J) y.proj
    let e₀ := b.continuousLinearEquivAt ℝ y.proj hy
    let β : (EB × R) → TangentBundle J Z := fun u ↦ ⟨y.proj, y.snd + e₀.symm u⟩
    let l : ℝ →L[ℝ] (EB × R) := (ContinuousLinearMap.id ℝ ℝ).smulRight (e₀ v)
    have hβ : ContMDiff 𝓘(ℝ, EB × R) JT ∞ β := by
      intro u
      rw [show JT = J.prod 𝓘(ℝ, EB × R) from modelWithCornersSelf_prod]
      apply Bundle.contMDiffAt_totalSpace.mpr
      refine ⟨contMDiffAt_const, ?_⟩
      have hadd : ContMDiffAt 𝓘(ℝ, EB × R) 𝓘(ℝ, EB × R) ∞
          (fun v : EB × R ↦ e₀ y.snd + v) u := contMDiffAt_const.add contMDiffAt_id
      apply hadd.congr_of_eventuallyEq
      apply Filter.Eventually.of_forall
      intro u
      change (b ⟨y.proj, y.snd + e₀.symm u⟩).2 = e₀ y.snd + u
      rw [← b.continuousLinearMapAt_apply_of_mem ℝ hy]
      rw [← b.coe_continuousLinearEquivAt_eq hy]
      change e₀ (y.snd + e₀.symm u) = e₀ y.snd + u
      rw [map_add, e₀.apply_symm_apply]
    have hfun : (fun t : ℝ ↦ A ⟨z, t • (0, w)⟩) = β ∘ l := by
      funext t
      change (F ⟨z, t • (0 : V z.proj), t • w⟩ : TangentBundle J Z) = β (l t)
      rw [smul_zero, hformula]
      apply Bundle.TotalSpace.ext
      · rfl
      · apply heq_of_eq
        let horizontal : EB × R := H.lift (j z.proj) z.snd
        let tangent : EB × R := mfderiv I J j z.proj z.snd
        let vertical : EB × R := (L ⟨z.proj, 0⟩ (t • w)).val
        let affine : EB × R := e₀.symm (t • e₀ v)
        change horizontal + vertical = tangent + affine
        have hh := DFunLike.congr_fun (hH z.proj) z.snd
        change horizontal = tangent at hh
        apply congrArg₂ (fun (v w : EB × R) ↦ v + w) hh
        change (L ⟨z.proj, 0⟩ (t • w)).val = (e₀.symm (t • e₀ v) : EB × R)
        rw [map_smul, map_smul, e₀.symm_apply_apply]
        rfl
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, EB × R)) (I'' := JT) 0
      (hβ.mdifferentiable (by simp) (l 0))
      (l.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
    rw [← hfun, show l 0 = 0 from map_zero l,
      l.hasFDerivAt.hasMFDerivAt.mfderiv] at hchain
    have hder : mfderiv 𝓘(ℝ, ℝ) JT (fun t : ℝ ↦ A ⟨z, t • (0, w)⟩) 0
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) =
          tangentVerticalLift (EB × R) Z y v := by
      have hd := DFunLike.congr_fun hchain
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)
      change _ = (mfderiv 𝓘(ℝ, EB × R) JT β 0) (l (1 : ℝ)) at hd
      change _ = (mfderiv 𝓘(ℝ, EB × R) JT β 0) (e₀ v)
      exact hd.trans (congrArg (mfderiv 𝓘(ℝ, EB × R) JT β 0) (one_smul ℝ (e₀ v)))
    have heL : e z.proj w =
        (LinearMap.range (mfderiv I J j z.proj).toLinearMap).mkQ v := by
      have hd := hL ⟨z.proj, 0⟩ w
      have hc : (fun t : ℝ ↦ a.symm ⟨z.proj, (0 : V z.proj) + t • w⟩) =
          (fun t : ℝ ↦ a.symm ⟨z.proj, t • w⟩) := by
        funext t
        rw [zero_add]
      rw [hc] at hd
      exact (he.1 z.proj w).trans
        (congrArg (LinearMap.range (mfderiv I J j z.proj).toLinearMap).mkQ hd.symm)
    have hi := (exists_tangentNormal_exactSequence j hj).choose_spec.choose_spec.2.2.1 z v
    calc
      D z (0, w) = (LinearMap.range (mfderiv IT JT fT z).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, ℝ) JT (fun t : ℝ ↦ A ⟨z, t • (0, w)⟩) 0
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)) := hD z (0, w)
      _ = (LinearMap.range (mfderiv IT JT fT z).toLinearMap).mkQ
          (tangentVerticalLift (EB × R) Z y v) :=
        congrArg (LinearMap.range (mfderiv IT JT fT z).toLinearMap).mkQ hder
      _ = i z ((LinearMap.range (mfderiv I J j z.proj).toLinearMap).mkQ v) := hi.symm
      _ = i z (e z.proj w) := congrArg (i z) heL.symm
  -- Use the same original base-normal isomorphism on both factors, in its pulled native atlas.
  let assembly (z : TangentBundle I B) : (ν z.proj × ν z.proj) →L[ℝ] νT z :=
    (D z).comp (((e z.proj).symm.prodCongr (e z.proj).symm).toContinuousLinearMap)
  have hpair : ContMDiff (IT.prod 𝓘(ℝ, N × N)) C ∞
      (fun z : TotalSpace (N × N) (νP ×ᵇ νP) ↦
        (⟨z.proj, (e z.proj.proj).symm z.snd.1,
          (e z.proj.proj).symm z.snd.2⟩ : TotalSpace (R × R) W)) := by
    intro z
    have ht : ContMDiffAt (IT.prod 𝓘(ℝ, N × N)) IT ∞
        (fun w : TotalSpace (N × N) (νP ×ᵇ νP) ↦ w.proj) z :=
      Bundle.contMDiffAt_proj (νP ×ᵇ νP)
    have hb := prT.contMDiff.contMDiffAt.comp z ht
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (IT.prod 𝓘(ℝ, N × N))
        (IT.prod 𝓘(ℝ, N × N)) ∞ id z)).2
    have hfirst : ContMDiffAt (IT.prod 𝓘(ℝ, N × N)) (I.prod 𝓘(ℝ, N)) ∞
        (fun w : TotalSpace (N × N) (νP ×ᵇ νP) ↦
          (⟨w.proj.proj, w.snd.1⟩ : TotalSpace N ν)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, (ContinuousLinearMap.fst ℝ N N).contDiff.contMDiff.contMDiffAt.comp z hc⟩
    have hsecond : ContMDiffAt (IT.prod 𝓘(ℝ, N × N)) (I.prod 𝓘(ℝ, N)) ∞
        (fun w : TotalSpace (N × N) (νP ×ᵇ νP) ↦
          (⟨w.proj.proj, w.snd.2⟩ : TotalSpace N ν)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, (ContinuousLinearMap.snd ℝ N N).contDiff.contMDiff.contMDiffAt.comp z hc⟩
    have hu := he.2.2.contMDiffAt.comp z hfirst
    have hw := he.2.2.contMDiffAt.comp z hsecond
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨ht, (Bundle.contMDiffAt_totalSpace.mp hu).2.prodMk_space
      (Bundle.contMDiffAt_totalSpace.mp hw).2⟩
  have hassembly : ContMDiff (IT.prod 𝓘(ℝ, N × N)) (IT.prod 𝓘(ℝ, NT)) ∞
      (fun z : TotalSpace (N × N) (νP ×ᵇ νP) ↦
        (⟨z.proj, assembly z.proj z.snd⟩ : TotalSpace NT νT)) :=
    hDsmooth.comp hpair
  have hproject (z : TangentBundle I B) (v : ν z.proj × ν z.proj) :
      tangentNormalProjection j hj z (assembly z v) = v.1 := by
    change p z (D z ((e z.proj).symm v.1, (e z.proj).symm v.2)) = v.1
    exact (hfirst z ((e z.proj).symm v.1) ((e z.proj).symm v.2)).trans
      ((e z.proj).apply_symm_apply v.1)
  have hinclude (z : TangentBundle I B) (v : ν z.proj) :
      assembly z (0, v) = tangentNormalVerticalMap j hj z v := by
    change D z ((e z.proj).symm 0, (e z.proj).symm v) = i z v
    rw [map_zero]
    exact (hvertical z ((e z.proj).symm v)).trans
      (congrArg (i z) ((e z.proj).apply_symm_apply v))
  let result := exists_tangentNormalSplitting_of_assembly j hj assembly hassembly hproject hinclude
  let K : TangentNormalSplitting j hj := result.choose
  have hK : ∀ z v, (K.equiv z).symm v = assembly z v := result.choose_spec
  refine ⟨K, ?_⟩
  intro z u w
  apply (hK z (e z.proj u, e z.proj w)).trans
  change D z ((e z.proj).symm (e z.proj u), (e z.proj).symm (e z.proj w)) = _
  exact (congrArg (D z) (Prod.ext ((e z.proj).symm_apply_apply u)
    ((e z.proj).symm_apply_apply w))).trans (hD z (u, w))

end AtiyahSinger
