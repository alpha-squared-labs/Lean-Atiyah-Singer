/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereVerticalMetric
public import AtiyahSinger.Geometry.PositiveDoubleBundleHomotopy

/-!
# Proper removal of the actual frame-sphere cotangent correction

Public module ID: M1248.

Pull the original positive inverse-Riesz comparison to the native tangent
projection. Its reciprocal scaling and positive vertical correction have a
proper homotopy to the identity on that same doubled pullback bundle.
The corrected endomorphism is evaluated at the actual scaled first vector.
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
set_option maxHeartbeats 3000000 in
-- The original metric comparison is pulled through two native total-space bundle layers.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact scaled positive correction in the native tangent pullback is properly homotopic
to the identity, with its original metric comparison evaluated at the scaled real point. -/
theorem exists_frameSphere_positiveCoordinates_properHomotopy
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
    let C := (exists_frameSphere_verticalRieszComparison r V g).choose
    let pr : C(TangentBundle 𝓘(ℝ, EB) B, B) :=
      ⟨TotalSpace.proj, FiberBundle.continuous_proj EB (TangentSpace 𝓘(ℝ, EB))⟩
    let W := (pr : TangentBundle 𝓘(ℝ, EB) B → B) *ᵖ V
    ∃ e : TotalSpace (R × R) (W ×ᵇ W) ≃ₜ TotalSpace (R × R) (W ×ᵇ W),
      (∀ z, e z = ⟨z.proj, (2 : ℝ) • z.snd.1,
        (1 / 2 : ℝ) • C ⟨z.proj.proj, (2 : ℝ) • z.snd.1⟩ z.snd.2⟩) ∧
      ∃ H : ContinuousMap.Homotopy (ContinuousMap.id (TotalSpace (R × R) (W ×ᵇ W)))
          ⟨e, e.continuous⟩, IsProperMap H := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let C := (exists_frameSphere_verticalRieszComparison r V g).choose
  let pr : C(TangentBundle 𝓘(ℝ, EB) B, B) :=
    ⟨TotalSpace.proj, FiberBundle.continuous_proj EB (TangentSpace 𝓘(ℝ, EB))⟩
  let W := (pr : TangentBundle 𝓘(ℝ, EB) B → B) *ᵖ V
  let (z : TangentBundle 𝓘(ℝ, EB) B) : NormedAddCommGroup (W z) := by
    change NormedAddCommGroup (V z.proj)
    infer_instance
  let (z : TangentBundle 𝓘(ℝ, EB) B) : InnerProductSpace ℝ (W z) := by
    change InnerProductSpace ℝ (V z.proj)
    infer_instance
  let : FiberBundle R W := FiberBundle.pullback (F := R) (E := V) pr
  let : VectorBundle ℝ R W := VectorBundle.pullback ℝ (F := R) (E := V) pr
  let πW : C(TotalSpace R W, TangentBundle 𝓘(ℝ, EB) B) :=
    ⟨TotalSpace.proj, FiberBundle.continuous_proj R W⟩
  let πV : C(TotalSpace R V, B) := ⟨TotalSpace.proj, FiberBundle.continuous_proj R V⟩
  let W₁ := (πW : TotalSpace R W → TangentBundle 𝓘(ℝ, EB) B) *ᵖ W
  let V₁ := (πV : TotalSpace R V → B) *ᵖ V
  let A (z : TotalSpace R W) : W z.proj →L[ℝ] W z.proj :=
    (C ⟨z.proj.proj, z.snd⟩).toContinuousLinearMap
  -- Forget only the tangent vector; retain both original V vectors and their common base.
  have hdrop : Continuous (fun z : TotalSpace R W₁ ↦
      (⟨⟨z.proj.proj.proj, z.proj.snd⟩, z.snd⟩ : TotalSpace R V₁)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding R V πV).continuous_iff]
    exact ((Pullback.continuous_lift R V pr).comp
      (Pullback.continuous_proj R W πW)).prodMk
        ((Pullback.continuous_lift R V pr).comp (Pullback.continuous_lift R W πW))
  have hC : Continuous (fun z : TotalSpace R V₁ ↦
      (⟨z.proj, C z.proj z.snd⟩ : TotalSpace R V₁)) :=
    (exists_frameSphere_verticalRieszComparison r V g).choose_spec.2.1.continuous
  have hA : Continuous (fun z : TotalSpace R W₁ ↦
      (⟨z.proj, A z.proj z.snd⟩ : TotalSpace R W₁)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding R W πW).continuous_iff]
    apply (Pullback.continuous_proj R W πW).prodMk
    rw [(inducing_pullbackTotalSpaceEmbedding R V pr).continuous_iff]
    exact ((Pullback.continuous_proj R V pr).comp
      (Pullback.continuous_lift R W πW)).prodMk
        ((Pullback.continuous_lift R V πV).comp (hC.comp hdrop))
  have hpos (z : TotalSpace R W) (v : W z.proj) (hv : v ≠ 0) :
      0 < inner ℝ v (A z v) :=
    (exists_frameSphere_verticalRieszComparison r V g).choose_spec.2.2.2
      ⟨z.proj.proj, z.snd⟩ v hv
  -- Apply the proper whole-cylinder construction to this very pulled positive map.
  obtain ⟨e, he, H, hH, _⟩ :=
    exists_positiveDoubleBundle_scaledProperHomotopy W A hA hpos 2 (by norm_num)
  dsimp only
  refine ⟨e, ?_, H, hH⟩
  intro z
  apply (he z).trans
  apply TotalSpace.ext
  · rfl
  apply heq_of_eq
  apply Prod.ext
  · rfl
  · change (2 : ℝ)⁻¹ • C ⟨z.proj.proj, (2 : ℝ) • z.snd.1⟩ z.snd.2 =
      (1 / 2 : ℝ) • C ⟨z.proj.proj, (2 : ℝ) • z.snd.1⟩ z.snd.2
    rw [one_div]

end AtiyahSinger
