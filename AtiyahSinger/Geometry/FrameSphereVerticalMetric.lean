/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereVerticalDerivative
public import AtiyahSinger.Geometry.PositiveRieszComparison
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The positive vertical metric comparison in the original frame chart

Public module ID: M1256.

Pull the supplied ambient metric back along the actual affine vertical
stereographic derivative. Compare its Riesz map with the original fiber inner
product, keeping both native bundle topologies. The resulting smooth positive
fiber equivalence depends on the actual real chart coordinate.

The only left inverse chosen in the argument is pointwise and is used to bound
a metric unit ball. No smoothly chosen complement, horizontal lift, compact
base or uniform spectral bound is assumed.
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
  verticalTangentTopology

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxSynthPendingDepth 50 in
set_option maxHeartbeats 2200000 in
-- Compare the original fiber metric with the metric of the same actual affine derivative.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original chart has a smooth positive inverse-Riesz comparison on its vector fibers. -/
theorem exists_frameSphere_verticalRieszComparison
    (g : letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
      let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      ContMDiffRiemannianMetric 𝓘(ℝ, EB × R) ∞ (EB × R)
        (TangentSpace 𝓘(ℝ, EB × R) : Z → Type _)) :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let I := 𝓘(ℝ, EB)
    let J := 𝓘(ℝ, EB × R)
    let A := I.prod 𝓘(ℝ, R)
    let g' : ContMDiffRiemannianMetric J ∞ (EB × R) (TangentSpace J : Z → Type _) := g
    let a := frameSphereStereographic (EB := EB) r V
    let L := (exists_frameSphere_verticalDerivativeEquiv (EB := EB) r V).choose
    let pr : ContMDiffMap A I (TotalSpace R V) B ∞ :=
      ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj V⟩
    let W := (pr : TotalSpace R V → B) *ᵖ V
    ∃ C : ∀ z : TotalSpace R V, V z.proj ≃L[ℝ] V z.proj,
      (∀ (z : TotalSpace R V) (v w : V z.proj),
        g'.inner (a.symm z) (L z (C z v)).val (L z w).val = inner ℝ v w) ∧
      ContMDiff (A.prod 𝓘(ℝ, R)) (A.prod 𝓘(ℝ, R)) ∞
        (fun z : TotalSpace R W ↦ (⟨z.proj, C z.proj z.snd⟩ : TotalSpace R W)) ∧
      ContMDiff (A.prod 𝓘(ℝ, R)) (A.prod 𝓘(ℝ, R)) ∞
        (fun z : TotalSpace R W ↦ (⟨z.proj, (C z.proj).symm z.snd⟩ : TotalSpace R W)) ∧
      ∀ (z : TotalSpace R V) (v : V z.proj), v ≠ 0 → 0 < inner ℝ v (C z v) := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let A := I.prod 𝓘(ℝ, R)
  let a := frameSphereStereographic (EB := EB) r V
  let q := smoothAssociatedSphereProjection S
  let hq := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let K := VerticalTangentFiber J I q
  let VM := VerticalTangentModel (EB × R) EB
  let pr : ContMDiffMap A I (TotalSpace R V) B ∞ :=
    ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj V⟩
  let W := (pr : TotalSpace R V → B) *ᵖ V
  let (z : TotalSpace R V) : NormedAddCommGroup (W z) := by
    change NormedAddCommGroup (V z.proj)
    infer_instance
  let (z : TotalSpace R V) : InnerProductSpace ℝ (W z) := by
    change InnerProductSpace ℝ (V z.proj)
    infer_instance
  let aInv : ContMDiffMap A J (TotalSpace R V) Z ∞ :=
    ⟨a.symm, (frameSphereStereographic_spec (EB := EB) r V).2.2.2.2.2⟩
  let Y := (aInv : TotalSpace R V → Z) *ᵖ K
  let L : ∀ z : TotalSpace R V, W z ≃L[ℝ] K (a.symm z) :=
    (exists_frameSphere_verticalDerivativeEquiv (EB := EB) r V).choose
  have hL : ContMDiff (A.prod 𝓘(ℝ, R)) (A.prod 𝓘(ℝ, VM)) ∞
      (fun z : TotalSpace R W ↦ (⟨z.proj, L z.proj z.snd⟩ : TotalSpace VM Y)) :=
    (exists_frameSphere_verticalDerivativeEquiv (EB := EB) r V).choose_spec.2.1
  let k (z : TotalSpace R V) : W z →L[ℝ] (EB × R) :=
    (LinearMap.ker (mfderiv J I q (a.symm z)).toLinearMap).subtypeL.comp
      (L z).toContinuousLinearMap
  have hk (z : TotalSpace R V) : Injective (k z) := by
    intro v w hvw
    apply (L z).injective
    exact Subtype.ext hvw
  have hdrop : ContMDiff (A.prod 𝓘(ℝ, VM)) (J.prod 𝓘(ℝ, VM)) ∞
      (fun z : TotalSpace VM Y ↦ (⟨aInv z.proj, z.snd⟩ : TotalSpace VM K)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨aInv.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj Y), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (A.prod 𝓘(ℝ, VM))
        (A.prod 𝓘(ℝ, VM)) ∞ id z)).2
  have hktotal : ContMDiff (A.prod 𝓘(ℝ, R)) (J.prod 𝓘(ℝ, EB × R)) ∞
      (fun z : TotalSpace R W ↦
        (⟨a.symm z.proj, k z.proj z.snd⟩ : TangentBundle J Z)) :=
    (smoothVerticalTangentInclusion q hq).contMDiff.comp (hdrop.comp hL)
  have hforget : ContMDiff (A.prod 𝓘(ℝ, R)) (I.prod 𝓘(ℝ, R)) ∞
      (fun z : TotalSpace R W ↦ (⟨z.proj.proj, z.snd⟩ : TotalSpace R V)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨pr.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj W), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (A.prod 𝓘(ℝ, R)) (A.prod 𝓘(ℝ, R)) ∞ id z)).2
  let b₀ (z : TotalSpace R V) : W z →L[ℝ] W z →L[ℝ] ℝ := innerSL ℝ
  let b₁ (z : TotalSpace R V) : W z →L[ℝ] W z →L[ℝ] ℝ :=
    (g.inner (a.symm z)).bilinearComp (k z) (k z)
  -- Scalar evaluations in the original local frames detect the full bilinear metric matrix.
  have hsmooth (b : ∀ z : TotalSpace R V, W z →L[ℝ] W z →L[ℝ] ℝ)
      (heval : ∀ (z : TotalSpace R V) (u v : R),
        let t := trivializationAt R W z
        ContMDiffAt A 𝓘(ℝ, ℝ) ∞
          (fun y ↦ b y (t.symmL ℝ y u) (t.symmL ℝ y v)) z) :
      ContMDiff A (A.prod 𝓘(ℝ, R →L[ℝ] R →L[ℝ] ℝ)) ∞
        (fun z ↦ TotalSpace.mk' (R →L[ℝ] R →L[ℝ] ℝ) z (b z)) := by
    intro z
    let t := trivializationAt R W z
    let s := trivializationAt ℝ (Bundle.Trivial (TotalSpace R V) ℝ) z
    let tDual := t.continuousLinearMap (RingHom.id ℝ) s
    have hz : z ∈ t.baseSet := mem_baseSet_trivializationAt R W z
    let B (y : TotalSpace R V) : R →L[ℝ] R →L[ℝ] ℝ :=
      (b y).bilinearComp (t.symmL ℝ y) (t.symmL ℝ y)
    have hB : ContMDiffAt A 𝓘(ℝ, R →L[ℝ] R →L[ℝ] ℝ) ∞ B z := by
      rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
      apply contDiffWithinAt_clm_apply.mpr
      intro u
      apply contDiffWithinAt_clm_apply.mpr
      intro v
      have h := heval z u v
      rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at h
      exact h
    apply (contMDiffAt_hom_bundle (fun y : TotalSpace R V ↦ TotalSpace.mk'
      (R →L[ℝ] R →L[ℝ] ℝ) y (b y))).mpr
    refine ⟨contMDiffAt_id, hB.congr_of_eventuallyEq ?_⟩
    filter_upwards [t.open_baseSet.mem_nhds hz] with y hy
    ext u v
    change ((tDual.continuousLinearMapAt ℝ y) (b y (t.symmL ℝ y u))) v = _
    rw [tDual.continuousLinearMapAt_apply_of_mem ℝ ⟨hy, by simp [s]⟩]
    change (s.continuousLinearMapAt ℝ y) (b y (t.symmL ℝ y u) (t.symmL ℝ y v)) = _
    dsimp only [s, Bundle.Trivial.fiberBundle_trivializationAt']
    rw [Bundle.Trivial.continuousLinearMapAt_trivialization]
    rfl
  have hframe (z : TotalSpace R V) (u : R) :
      ContMDiffAt A (A.prod 𝓘(ℝ, R)) ∞
        (fun y ↦ (⟨y, (trivializationAt R W z).symmL ℝ y u⟩ : TotalSpace R W)) z := by
    let t := trivializationAt R W z
    have hz : z ∈ t.baseSet := mem_baseSet_trivializationAt R W z
    apply (t.contMDiffAt_iff (t.mem_source.mpr hz)).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply (contMDiffAt_const (c := u)).congr_of_eventuallyEq
    filter_upwards [t.open_baseSet.mem_nhds hz] with y hy
    rw [← t.continuousLinearMapAt_apply_of_mem ℝ hy]
    exact t.continuousLinearMapAt_symmL hy u
  have hb₀ : ContMDiff A (A.prod 𝓘(ℝ, R →L[ℝ] R →L[ℝ] ℝ)) ∞
      (fun z ↦ TotalSpace.mk' (R →L[ℝ] R →L[ℝ] ℝ) z (b₀ z)) := by
    apply hsmooth
    intro z u v
    exact (hforget.contMDiffAt.comp z (hframe z u)).inner_bundle
      (hforget.contMDiffAt.comp z (hframe z v))
  have hb₁ : ContMDiff A (A.prod 𝓘(ℝ, R →L[ℝ] R →L[ℝ] ℝ)) ∞
      (fun z ↦ TotalSpace.mk' (R →L[ℝ] R →L[ℝ] ℝ) z (b₁ z)) := by
    apply hsmooth
    intro z u v
    have h : ContMDiffAt A (J.prod 𝓘(ℝ, ℝ)) ∞
        (fun y ↦ (⟨a.symm y, b₁ y ((trivializationAt R W z).symmL ℝ y u)
          ((trivializationAt R W z).symmL ℝ y v)⟩ : TotalSpace ℝ (Bundle.Trivial Z ℝ))) z := by
      apply ContMDiffAt.clm_bundle_apply₂ (F₁ := EB × R) (F₂ := EB × R)
      · exact g.contMDiff.contMDiffAt.comp z aInv.contMDiff.contMDiffAt
      · exact hktotal.contMDiffAt.comp z (hframe z u)
      · exact hktotal.contMDiffAt.comp z (hframe z v)
    exact (Bundle.contMDiffAt_totalSpace.mp h).2
  have hb₀bounded (z : TotalSpace R V) :
      Bornology.IsVonNBounded ℝ {v : W z | b₀ z v v < 1} := by
    apply (NormedSpace.isVonNBounded_of_isBounded ℝ
      (Metric.isBounded_ball (x := (0 : W z)) (r := 1))).subset
    intro v hv
    change dist v 0 < (1 : ℝ)
    rw [dist_zero_right]
    have hsq : ‖v‖ ^ 2 < (1 : ℝ) := by
      change inner ℝ v v < 1 at hv
      simpa only [b₀, innerSL_apply_apply, real_inner_self_eq_norm_sq] using hv
    have hn := norm_nonneg v
    nlinarith
  -- A pointwise linear left inverse proves boundedness; it is never asserted to vary smoothly.
  have hb₁bounded (z : TotalSpace R V) :
      Bornology.IsVonNBounded ℝ {v : W z | b₁ z v v < 1} := by
    obtain ⟨l, hl⟩ := (k z).toLinearMap.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (hk z))
    let lC : (EB × R) →L[ℝ] W z := l.toContinuousLinearMap
    apply ((g.isVonNBounded (a.symm z)).image lC).subset
    intro v hv
    exact ⟨k z v, hv, DFunLike.congr_fun hl v⟩
  let g₀ : ContMDiffRiemannianMetric A ∞ R W :=
    { inner := b₀
      symm := fun _ _ _ ↦ real_inner_comm _ _
      pos := fun _ _ hv ↦ real_inner_self_pos.mpr hv
      isVonNBounded := hb₀bounded
      contMDiff := hb₀ }
  let g₁ : ContMDiffRiemannianMetric A ∞ R W :=
    { inner := b₁
      symm := fun z v w ↦ g.symm (a.symm z) (k z v) (k z w)
      pos := by
        intro z v hv
        exact g.pos (a.symm z) (k z v) (fun h ↦ hv ((hk z) (h.trans (map_zero (k z)).symm)))
      isVonNBounded := hb₁bounded
      contMDiff := hb₁ }
  exact exists_positiveRieszComparison A W g₀ g₁

end AtiyahSinger

