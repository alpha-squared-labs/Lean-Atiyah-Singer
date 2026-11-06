/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereNormalBundle
public import AtiyahSinger.Geometry.FrameSphereOpenDiffeomorph
public import AtiyahSinger.Geometry.TubularNeighborhood

/-!
# The original stereographic tube on the actual south normal bundle

The radial normal identification transports the original whole-bundle
stereographic inverse to the actual quotient normal bundle of the south
section. Differentiation of that same radial family verifies the required
normalization. The tube retains its original open image and each specified
vector, including rank zero and an empty base.
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
set_option maxHeartbeats 1800000 in
-- The whole original sphere chart is transported through its actual normal derivative.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole frame chart is a normalized tube after the actual radial normal identification. -/
theorem exists_frameSphere_tubularNeighborhood :
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
    ∃ e : ∀ x, V x ≃L[ℝ] NormalBundle 𝓘(ℝ, EB) 𝓘(ℝ, EB × R) j x,
      ∃ T : TubularNeighborhood j hj,
        ∀ (x : B) (v : V x), (T.diffeomorph ⟨x, e x v⟩ : Z) = a.symm ⟨x, v⟩ := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let a := frameSphereStereographic (EB := EB) r V
  have ha := frameSphereStereographic_spec (EB := EB) r V
  let j : ContMDiffMap I J B Z ∞ :=
    ⟨fun x ↦ a.symm ⟨x, 0⟩, ha.2.2.2.2.2.comp (contMDiff_zeroSection ℝ V)⟩
  let hj := (isSmoothEmbedding_frameSphere_zeroSection (EB := EB) r V).isImmersion
  let := normalBundleFiberBundle j hj
  let := normalBundleVectorBundle j hj
  let := normalBundleContMDiffVectorBundle j hj
  let N := NormalModel EB (EB × R)
  let ν := NormalBundle I J j
  obtain ⟨e, he, hforward, hinverse⟩ := exists_frameSphere_normalEquiv (EB := EB) r V
  let d : TotalSpace R V ≃ₘ⟮I.prod 𝓘(ℝ, R), I.prod 𝓘(ℝ, N)⟯ TotalSpace N ν :=
    { toFun := fun z ↦ ⟨z.proj, e z.proj z.snd⟩
      invFun := fun z ↦ ⟨z.proj, (e z.proj).symm z.snd⟩
      left_inv := by
        rintro ⟨x, v⟩
        change (⟨x, (e x).symm (e x v)⟩ : TotalSpace R V) = ⟨x, v⟩
        rw [(e x).symm_apply_apply]
      right_inv := by
        rintro ⟨x, v⟩
        change (⟨x, e x ((e x).symm v)⟩ : TotalSpace N ν) = ⟨x, v⟩
        rw [(e x).apply_symm_apply]
      contMDiff_toFun := hforward
      contMDiff_invFun := hinverse }
  let U : TopologicalSpace.Opens Z := ⟨a.source, a.open_source⟩
  let D : TotalSpace N ν ≃ₘ⟮I.prod 𝓘(ℝ, N), J⟯ U :=
    d.symm.trans (frameSphereStereographicDiffeomorph (EB := EB) r V)
  have hD (x : B) (v : ν x) : (D ⟨x, v⟩ : Z) = a.symm ⟨x, (e x).symm v⟩ := rfl
  let T : TubularNeighborhood j hj :=
    { target := U
      diffeomorph := D
      map_zero := by
        intro x
        rw [hD, map_zero]
        rfl
      normal_deriv := by
        intro x
        dsimp only
        intro v
        let t := trivializationAt N ν x
        let c := t.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt N ν x)
        let Avert : N →L[ℝ] V x :=
          (e x).symm.toContinuousLinearMap.comp c.symm.toContinuousLinearMap
        let f : N → Z := fun w ↦ a.symm ⟨x, Avert w⟩
        have hf : ContMDiff 𝓘(ℝ, N) J ∞ f := by
          apply ha.2.2.2.2.2.comp
          intro w
          let a₀ := trivializationAt R V x
          have hx : x ∈ a₀.baseSet := mem_baseSet_trivializationAt R V x
          apply (a₀.contMDiffAt_iff (a₀.mem_source.mpr hx)).mpr
          refine ⟨contMDiffAt_const, ?_⟩
          have hc : ContMDiffAt 𝓘(ℝ, N) 𝓘(ℝ, R) ∞
              ((a₀.continuousLinearMapAt ℝ x).comp Avert) w :=
            ((a₀.continuousLinearMapAt ℝ x).comp Avert).contDiff.contMDiff.contMDiffAt
          apply hc.congr_of_eventuallyEq
          exact Filter.Eventually.of_forall (fun w ↦
            (a₀.continuousLinearMapAt_apply_of_mem ℝ hx (Avert w)).symm)
        let l : ℝ →L[ℝ] N := (ContinuousLinearMap.id ℝ ℝ).smulRight v
        have hfun : (fun s : ℝ ↦ a.symm ⟨x, s • Avert v⟩) = f ∘ l := by
          funext s
          change a.symm ⟨x, s • Avert v⟩ = a.symm ⟨x, Avert (s • v)⟩
          rw [map_smul]
        have hc := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, N)) (I'' := J) 0
          (hf.mdifferentiable (by simp) (l 0))
          ((l.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp) 0)
        have hl : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, N) l 0 = l :=
          l.hasFDerivAt.hasMFDerivAt.mfderiv
        rw [show l 0 = 0 from map_zero l, hl] at hc
        have hv := DFunLike.congr_fun hc ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)
        have hder : (mfderiv 𝓘(ℝ, ℝ) J (fun s : ℝ ↦ a.symm ⟨x, s • Avert v⟩) 0
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : EB × R) =
              mfderiv 𝓘(ℝ, N) J f 0 ((NormedSpace.fromTangentSpace (0 : N)).symm v) := by
          have hh := congrArg (fun k : ℝ → Z ↦ (mfderiv 𝓘(ℝ, ℝ) J k 0
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : EB × R)) hfun
          apply hh.trans
          have hunit : l ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) =
              (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : N)).symm v := by
            change (1 : ℝ) • v = v
            exact one_smul ℝ v
          exact hv.trans (congrArg (fun w : N ↦
            (mfderiv 𝓘(ℝ, N) J f 0 : N →L[ℝ] EB × R) w) hunit)
        have hn := he x (Avert v)
        rw [hder] at hn
        have heA : e x (Avert v) = c.symm v := (e x).apply_symm_apply (c.symm v)
        rw [heA] at hn
        change (LinearMap.range (mfderiv I J j x).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, N) J (fun w ↦ (D ⟨x, c.symm w⟩ : Z)) 0
            ((NormedSpace.fromTangentSpace (0 : N)).symm v)) = c.symm v
        exact hn.symm }
  refine ⟨e, T, ?_⟩
  intro x v
  change (D ⟨x, e x v⟩ : Z) = a.symm ⟨x, v⟩
  rw [hD, (e x).symm_apply_apply]

end AtiyahSinger
