/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereVerticalCotangent
public import AtiyahSinger.Geometry.FrameSpherePoleNormalization
public import AtiyahSinger.Geometry.FrameSphereZeroSection
public import AtiyahSinger.Geometry.SectionNormalVertical

/-!
# The original vector bundle as the south-section normal

Public module ID: M1245.

Differentiate the original stereographic inverse in each bundle fiber at zero.
Its class in the original south-section quotient normal is a smooth bundle
isomorphism. Fiberwise invertibility is checked using an actual orthogonal
frame, the normalized pole chart derivative and the original sphere fiber
derivative equivalence. Smoothness follows by differentiating the same global
radial family, independently of the frames used in that verification.

The normalization is that of the original whole-vector-bundle chart. Its
factor two relative to the normalized pole chart is retained explicitly.
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
  normalBundleTopology verticalTangentTopology

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxSynthPendingDepth 45 in
set_option maxHeartbeats 2200000 in
-- The original normal, associated sphere, frame and pulled tangent atlases occur together.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The radial derivative of the original frame chart identifies the south-section normal. -/
theorem exists_frameSphere_normalEquiv :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let a := frameSphereStereographic (EB := EB) r V
    let j : ContMDiffMap 𝓘(ℝ, EB) 𝓘(ℝ, EB × R) B Z ∞ :=
      ⟨fun x ↦ a.symm ⟨x, 0⟩,
        (frameSphereStereographic_spec (EB := EB) r V).2.2.2.2.2.comp
          (contMDiff_zeroSection ℝ V)⟩
    let hj := (isSmoothEmbedding_frameSphere_zeroSection (EB := EB) r V).isImmersion
    letI := normalBundleFiberBundle j hj
    letI := normalBundleVectorBundle j hj
    letI := normalBundleContMDiffVectorBundle j hj
    let ν := NormalBundle 𝓘(ℝ, EB) 𝓘(ℝ, EB × R) j
    ∃ e : ∀ x, V x ≃L[ℝ] ν x,
      (∀ (x : B) (v : V x), e x v =
        (LinearMap.range (mfderiv 𝓘(ℝ, EB) 𝓘(ℝ, EB × R) j x).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EB × R) (fun t : ℝ ↦ a.symm ⟨x, t • v⟩) 0
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))) ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, R))
        (𝓘(ℝ, EB).prod 𝓘(ℝ, NormalModel EB (EB × R))) ∞
        (fun z : TotalSpace R V ↦
          (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (NormalModel EB (EB × R)) ν)) ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, NormalModel EB (EB × R)))
        (𝓘(ℝ, EB).prod 𝓘(ℝ, R)) ∞
        (fun z : TotalSpace (NormalModel EB (EB × R)) ν ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace R V)) := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let a := frameSphereStereographic (EB := EB) r V
  let c := frameSphereHomeomorph (EB := EB) r V
  have ha := frameSphereStereographic_spec (EB := EB) r V
  let j : ContMDiffMap I J B Z ∞ :=
    ⟨fun x ↦ a.symm ⟨x, 0⟩, ha.2.2.2.2.2.comp (contMDiff_zeroSection ℝ V)⟩
  let hj := (isSmoothEmbedding_frameSphere_zeroSection (EB := EB) r V).isImmersion
  let q := smoothAssociatedSphereProjection S
  let hq := associatedSphereProjection_isSubmersion S
  let := normalBundleFiberBundle j hj
  let := normalBundleVectorBundle j hj
  let := normalBundleContMDiffVectorBundle j hj
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let ν := NormalBundle I J j
  let K := VerticalTangentFiber J I q
  have hqj (x : B) : q (j x) = x := by
    have hc := (frameSphereHomeomorph_spec (EB := EB) r V).1
    have hbase (z : Z) : q z = (c z).val.1.proj := by
      induction z using Quotient.inductionOn with
      | h u =>
        change q (associatedBundleMk G P (OrthogonalSphere r) u.1 u.2) =
          (c (associatedBundleMk G P (OrthogonalSphere r) u.1 u.2)).val.1.proj
        rw [hc]
        rfl
    rw [hbase]
    change (c (a.symm ⟨x, 0⟩)).val.1.proj = x
    rw [ha.2.2.2.1]
  obtain ⟨n, hn, _, _, _⟩ := exists_section_normal_vertical_equiv q hq j hj hqj
  -- A frame is used only for pointwise invertibility, never as an asserted smooth choice.
  let frame (x : B) : R ≃ₗᵢ[ℝ] V x := by
    apply Classical.choice
    obtain ⟨⟨y, p⟩, hp⟩ := S.toIsPrincipalBundle.projection_properties.2.2 x
    change y = x at hp
    subst y
    exact ⟨p⟩
  let p (x : B) : P := ⟨x, frame x⟩
  let s := orthogonalSpherePole r false
  let b := orthogonalSphereNormalizedChart r false
  have hb := orthogonalSphereNormalizedChart_smooth r false
  have hb0 : b.symm (0 : R) = s :=
    (orthogonalSphereNormalizedChart_properties r false).2.2.1
  have hbt : (0 : R) ∈ b.target := by
    rw [(orthogonalSphereNormalizedChart_properties r false).2.1]
    trivial
  have hbd : b.MDifferentiable (𝓡 r) (𝓡 r) :=
    ⟨hb.1.mdifferentiableOn (by simp), (hb.2.mdifferentiable (by simp)).mdifferentiableOn⟩
  let db : R ≃L[ℝ] TangentSpace (𝓡 r) s := hbd.symm.mfderiv hbt
  let half : R ≃L[ℝ] R :=
    (LinearEquiv.smulOfNeZero ℝ R (1 / 2 : ℝ) (by norm_num)).toContinuousLinearEquiv
  have hpole (x : B) : associatedBundleMk G P (OrthogonalSphere r) (p x) s = j x := by
    have h := frameSphereStereographic_symm_two_smul (EB := EB) r V (p x) 0
    rw [map_zero, smul_zero, hb0] at h
    exact h.symm
  let L₀ (x : B) : V x ≃L[ℝ]
      K (associatedBundleMk G P (OrthogonalSphere r) (p x) s) :=
    ((frame x).symm.toContinuousLinearEquiv.trans half).trans
      (db.trans (associatedSphereFiberTangentEquiv S (p x) s))
  let L (x : B) : V x ≃L[ℝ] K (j x) := (hpole x) ▸ L₀ x
  have hLval (x : B) (v : V x) : (L x v).val = (L₀ x v).val := by
    -- Transport changes only the kernel index, so it preserves the ambient tangent vector.
    have hcast {y y' : Z} (h : y = y') (e : V x ≃L[ℝ] K y) :
        ((show V x ≃L[ℝ] K y' from h ▸ e) v).val = (e v).val := by
      subst y'
      rfl
    exact hcast (hpole x) (L₀ x)
  let ρ (z : TotalSpace R V) (t : ℝ) : Z := a.symm ⟨z.proj, t • z.snd⟩
  have hρ0 (z : TotalSpace R V) : ρ z 0 = j z.proj := by simp [ρ, j]
  have hρ : ContMDiff ((I.prod 𝓘(ℝ, R)).prod 𝓘(ℝ, ℝ)) J ∞
      (Function.uncurry ρ) := by
    apply ha.2.2.2.2.2.comp
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    have hbase : ContMDiffAt ((I.prod 𝓘(ℝ, R)).prod 𝓘(ℝ, ℝ)) I ∞
        (fun w : TotalSpace R V × ℝ ↦ w.1.proj) z :=
      (Bundle.contMDiffAt_proj V).comp z contMDiffAt_fst
    refine ⟨hbase, ?_⟩
    let t := trivializationAt R V z.1.proj
    have hv := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_fst : ContMDiffAt ((I.prod 𝓘(ℝ, R)).prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, R)) ∞ (fun w : TotalSpace R V × ℝ ↦ w.1) z)).2
    apply (contMDiffAt_snd.smul hv).congr_of_eventuallyEq
    filter_upwards [hbase.continuousAt (t.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt R V z.1.proj))] with w hw
    change (t ⟨w.1.proj, w.2 • w.1.snd⟩).2 = w.2 • (t w.1).2
    simp only [← t.continuousLinearMapAt_apply_of_mem ℝ hw, map_smul]
  have hradial (z : TotalSpace R V) :
      (mfderiv 𝓘(ℝ, ℝ) J (ρ z) 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : EB × R) =
          (L z.proj z.snd).val := by
    let i : OrthogonalSphere r → Z := associatedBundleMk G P (OrthogonalSphere r) (p z.proj)
    let u := half ((frame z.proj).symm z.snd)
    let l : ℝ →L[ℝ] R := (ContinuousLinearMap.id ℝ ℝ).smulRight u
    have hfun : ρ z = i ∘ b.symm ∘ l := by
      funext t
      have hc := frameSphereStereographic_symm_two_smul (EB := EB) r V (p z.proj) (l t)
      have hvec : (2 : ℝ) • (frame z.proj) (l t) = t • z.snd := by
        change (2 : ℝ) • (frame z.proj) (t • ((1 / 2 : ℝ) •
          (frame z.proj).symm z.snd)) = t • z.snd
        rw [map_smul, map_smul, (frame z.proj).apply_symm_apply, smul_smul, smul_smul]
        congr 1
        ring
      rw [hvec] at hc
      exact hc
    have hi := (smoothAssociatedSphereFiberInclusion S (p z.proj)).contMDiff
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 r) (I'' := J) 0
      ((hi.comp hb.2).mdifferentiable (by simp) (l 0))
      ((l.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp) 0)
    rw [show l 0 = 0 from map_zero l] at hchain
    have hchain₂ := mfderiv_comp (I := 𝓡 r) (I' := 𝓡 r) (I'' := J) (0 : R)
      (hi.mdifferentiable (by simp) _) (hb.2.mdifferentiable (by simp) _)
    have hl : mfderiv 𝓘(ℝ, ℝ) (𝓡 r) l 0 = l :=
      l.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [hchain₂, hl] at hchain
    have hd := DFunLike.congr_fun hchain ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)
    have hfder := congrArg (fun k : ℝ → Z ↦
      (mfderiv 𝓘(ℝ, ℝ) J k 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : EB × R))
        hfun
    have hunit : l ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = u := by
      change (1 : ℝ) • u = u
      exact one_smul ℝ u
    have he := (exists_associatedSphereFiberTangentEquiv S (p z.proj) s).choose_spec (db u)
    apply hfder.trans
    calc
      (mfderiv 𝓘(ℝ, ℝ) J ((i ∘ b.symm) ∘ l) 0
          ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : EB × R) =
        (mfderiv (𝓡 r) J i (b.symm 0) : R →L[ℝ] EB × R)
          (db (l ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1))) := hd
      _ = (mfderiv (𝓡 r) J i (b.symm 0) : R →L[ℝ] EB × R) (db u) :=
        congrArg (fun v : R ↦ (mfderiv (𝓡 r) J i (b.symm 0) : R →L[ℝ] EB × R) (db v))
          hunit
      _ = (mfderiv (𝓡 r) J i s : R →L[ℝ] EB × R) (db u) :=
        congrArg (fun y : OrthogonalSphere r ↦ (mfderiv (𝓡 r) J i y : R →L[ℝ] EB × R)
          (db u)) hb0
      _ = (L z.proj z.snd).val := he.symm.trans (hLval z.proj z.snd).symm
  have hL : ContMDiff (I.prod 𝓘(ℝ, R)) (I.prod 𝓘(ℝ, EB × R)) ∞
      (fun z : TotalSpace R V ↦ (⟨z.proj, (L z.proj z.snd).val⟩ :
        TotalSpace (EB × R) ((j : B → Z) *ᵖ (TangentSpace J)))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj V, ?_⟩
    have hd := ContMDiffAt.mfderiv_apply ρ (fun _ : TotalSpace R V ↦ (0 : ℝ)) id
      (fun _ : TotalSpace R V ↦ (1 : ℝ)) (hρ (z, 0)) contMDiffAt_const contMDiffAt_id
      contMDiffAt_const (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
    apply hd.congr_of_eventuallyEq
    let t := trivializationAt (EB × R) (TangentSpace J) (j z.proj)
    have hbase := j.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj V)
    filter_upwards [hbase.continuousAt (t.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt (EB × R) (TangentSpace J) (j z.proj)))] with w hw
    dsimp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, id_eq,
      ContinuousLinearMap.comp_apply]
    rw [TangentBundle.symmL_model_space]
    change (t ⟨j w.proj, (L w.proj w.snd).val⟩).2 =
      (trivializationAt (EB × R) (TangentSpace J) (ρ z 0)).continuousLinearMapAt ℝ (ρ w 0)
        (mfderiv 𝓘(ℝ, ℝ) J (ρ w) 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))
    rw [hradial, hρ0 z, hρ0 w]
    exact (t.continuousLinearMapAt_apply_of_mem ℝ hw _).symm
  let e (x : B) : V x ≃L[ℝ] ν x := (L x).trans (n x)
  have he (x : B) (v : V x) : e x v =
      (LinearMap.range (mfderiv I J j x).toLinearMap).mkQ (L x v).val := hn x (L x v)
  have he_smooth : ContMDiff (I.prod 𝓘(ℝ, R))
      (I.prod 𝓘(ℝ, NormalModel EB (EB × R))) ∞
      (fun z : TotalSpace R V ↦
        (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (NormalModel EB (EB × R)) ν)) := by
    apply ((smoothNormalQuotientMap j hj).contMDiff.comp hL).congr
    intro z
    exact congrArg (fun v ↦ (⟨z.proj, v⟩ : TotalSpace (NormalModel EB (EB × R)) ν))
      (he z.proj z.snd)
  refine ⟨e, ?_, he_smooth, ?_⟩
  · intro x v
    rw [he, ← hradial ⟨x, v⟩]
  · apply contMDiff_bundleMap_of_comp_surjective
      (fun x ↦ (e x).toContinuousLinearMap) (fun x ↦ (e x).symm.toContinuousLinearMap)
      he_smooth (fun x ↦ (e x).surjective)
    apply contMDiff_id.congr
    intro z
    change (⟨z.proj, (e z.proj).symm (e z.proj z.snd)⟩ : TotalSpace R V) = z
    rw [(e z.proj).symm_apply_apply]

end AtiyahSinger
