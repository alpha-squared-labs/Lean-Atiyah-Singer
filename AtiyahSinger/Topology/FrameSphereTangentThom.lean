/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereTangentTubularNeighborhood
public import AtiyahSinger.Topology.ComplexificationBundleMap
public import AtiyahSinger.Topology.TangentEmbeddingPushforward
public import AtiyahSinger.Topology.ThomNaturality

/-!
# The original frame-sphere normal Thom map in tangent coordinates

Public module ID: M1860.

Scalar extension of the same actual normal equivalence transports the original
normal Thom class to the original complexified vector bundle. The previously
normalized tangent tube then has exactly the original tangent parametrization
in ordered real/imaginary coordinates. No arbitrary real normal equivalence or
new Thom operator is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Topology ComplexBundle
open scoped ContDiff TensorProduct

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

variable [T2Space B] [SecondCountableTopology B]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ)
    (OrthogonalFrameBundle r V) (OrthogonalSphere r))]
  [SecondCountableTopology (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ)
    (OrthogonalFrameBundle r V) (OrthogonalSphere r))]

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology complexifiedNormalPullbackTopology
  ComplexBundle.t2Space_totalSpace ComplexBundle.locallyCompactSpace_totalSpace

set_option maxSynthPendingDepth 55 in
set_option maxHeartbeats 6000000 in
-- Every bundle map uses the same original normal quotient and native pullback topology.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual frame-sphere tangent pushforward is its original vector-bundle Thom map
followed by the same tangent parametrization in real/imaginary coordinates. -/
theorem exists_frameSphere_tangentThom_comparison
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
    letI : T2Space (TangentBundle I B) := (tangentBundle_topology EB B).1
    letI : LocallyCompactSpace (TangentBundle I B) :=
      ChartedSpace.locallyCompactSpace (EB × EB) (TangentBundle I B)
    letI : T2Space (TangentBundle J Z) := (tangentBundle_topology (EB × R) Z).1
    letI : LocallyCompactSpace (TangentBundle J Z) :=
      ChartedSpace.locallyCompactSpace ((EB × R) × (EB × R)) (TangentBundle J Z)
    let pr : ContMDiffMap I.tangent I (TangentBundle I B) B ∞ :=
      ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj (TangentSpace I)⟩
    let W := (pr : TangentBundle I B → B) *ᵖ V
    let C := fun z : TangentBundle I B ↦ ℂ ⊗[ℝ] W z
    letI := complexificationTopology R W
    letI : IsFiniteRank C := isFiniteRank_complexification R W
    letI : T2Space (TotalSpace Unit C) := t2Space_totalSpace C
    letI : LocallyCompactSpace (TotalSpace Unit C) := locallyCompactSpace_totalSpace C
    letI := isFiniteRank_complexifiedNormalPullback j hj.isImmersion
    let F := (exists_frameSphere_tangentParametrization (EB := EB) r V H).choose
    let eDouble := complexificationDoubleTotalHomeomorph R W
    let U : TopologicalSpace.Opens (TangentBundle J Z) :=
      ⟨Bundle.TotalSpace.proj ⁻¹' a.source,
        a.open_source.preimage (FiberBundle.continuous_proj (EB × R) (TangentSpace J))⟩
    let jF : C(TotalSpace Unit C, TangentBundle J Z) :=
      ⟨fun z ↦ (F (eDouble z) : TangentBundle J Z),
        continuous_subtype_val.comp (F.contMDiff.continuous.comp eDouble.continuous)⟩
    let hjF := U.isOpen.isOpenEmbedding_subtypeVal.comp
      (F.toHomeomorph.isOpenEmbedding.comp eDouble.isOpenEmbedding)
    (∀ x : B, H'.lift (j x) = mfderiv I J j x) →
    ∃ K : TangentNormalSplitting j hj,
      ∃ T : TubularNeighborhood (smoothTangentMap j) (isImmersion_smoothTangentMap j hj),
        ∀ (hC : ContinuousHermitianMetric C)
          (hN : ContinuousHermitianMetric (ComplexifiedNormalPullback j)),
          tangentEmbeddingPushforwardWith j hj K T hN =
            (compactSupportKZeroOpenPushforward jF hjF).comp hC.supportedThomHom := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let a := frameSphereStereographic (EB := EB) r V
  let j : ContMDiffMap I J B Z ∞ :=
    ⟨fun x ↦ a.symm ⟨x, 0⟩,
      (frameSphereStereographic_spec (EB := EB) r V).2.2.2.2.2.comp
        (contMDiff_zeroSection ℝ V)⟩
  let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := EB) r V
  let := normalBundleFiberBundle j hj.isImmersion
  let := normalBundleVectorBundle j hj.isImmersion
  let := normalBundleContMDiffVectorBundle j hj.isImmersion
  let ν := NormalBundle I J j
  let N := NormalModel EB (EB × R)
  let : T2Space (TangentBundle I B) := (tangentBundle_topology EB B).1
  let : LocallyCompactSpace (TangentBundle I B) :=
    ChartedSpace.locallyCompactSpace (EB × EB) (TangentBundle I B)
  let : T2Space (TangentBundle J Z) := (tangentBundle_topology (EB × R) Z).1
  let : LocallyCompactSpace (TangentBundle J Z) :=
    ChartedSpace.locallyCompactSpace ((EB × R) × (EB × R)) (TangentBundle J Z)
  let pr : ContMDiffMap I.tangent I (TangentBundle I B) B ∞ :=
    ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj (TangentSpace I)⟩
  let W := (pr : TangentBundle I B → B) *ᵖ V
  let Y := (pr : TangentBundle I B → B) *ᵖ ν
  let (z : TangentBundle I B) : AddCommGroup (Y z) := by
    change AddCommGroup (ν z.proj)
    infer_instance
  let (z : TangentBundle I B) : Module ℝ (Y z) := by
    change Module ℝ (ν z.proj)
    infer_instance
  let C := fun z : TangentBundle I B ↦ ℂ ⊗[ℝ] W z
  let CN := ComplexifiedNormalPullback j
  let := complexificationTopology R W
  let : IsFiniteRank C := isFiniteRank_complexification R W
  let : T2Space (TotalSpace Unit C) := t2Space_totalSpace C
  let : LocallyCompactSpace (TotalSpace Unit C) := locallyCompactSpace_totalSpace C
  let := isFiniteRank_complexifiedNormalPullback j hj.isImmersion
  let F := (exists_frameSphere_tangentParametrization (EB := EB) r V H).choose
  let eDouble := complexificationDoubleTotalHomeomorph R W
  let U : TopologicalSpace.Opens (TangentBundle J Z) :=
    ⟨Bundle.TotalSpace.proj ⁻¹' a.source,
      a.open_source.preimage (FiberBundle.continuous_proj (EB × R) (TangentSpace J))⟩
  let jF : C(TotalSpace Unit C, TangentBundle J Z) :=
    ⟨fun z ↦ (F (eDouble z) : TangentBundle J Z),
      continuous_subtype_val.comp (F.contMDiff.continuous.comp eDouble.continuous)⟩
  let hjF := U.isOpen.isOpenEmbedding_subtypeVal.comp
    (F.toHomeomorph.isOpenEmbedding.comp eDouble.isOpenEmbedding)
  dsimp only
  intro hH
  obtain ⟨K, T, hT⟩ := exists_frameSphere_tangentTubularNeighborhood (EB := EB) r V H hH
  let e : ∀ x : B, V x ≃L[ℝ] ν x :=
    (exists_frameSphere_normalEquiv (EB := EB) r V).choose
  have hef : ContMDiff (I.prod 𝓘(ℝ, R)) (I.prod 𝓘(ℝ, N)) ∞
      (fun z : TotalSpace R V ↦ (⟨z.proj, e z.proj z.snd⟩ : TotalSpace N ν)) :=
    (exists_frameSphere_normalEquiv (EB := EB) r V).choose_spec.2.1
  have hei : ContMDiff (I.prod 𝓘(ℝ, N)) (I.prod 𝓘(ℝ, R)) ∞
      (fun z : TotalSpace N ν ↦ (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace R V)) :=
    (exists_frameSphere_normalEquiv (EB := EB) r V).choose_spec.2.2
  -- Pull back the same actual normal equivalence and its inverse, then extend scalars.
  have hep : Continuous (fun z : TotalSpace R W ↦
      (⟨z.proj, e z.proj.proj z.snd⟩ : TotalSpace N Y)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding N ν (pr : TangentBundle I B → B)).continuous_iff]
    exact (Pullback.continuous_proj R V (pr : TangentBundle I B → B)).prodMk
      (hef.continuous.comp (Pullback.continuous_lift R V (pr : TangentBundle I B → B)))
  have hepi : Continuous (fun z : TotalSpace N Y ↦
      (⟨z.proj, (e z.proj.proj).symm z.snd⟩ : TotalSpace R W)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding R V (pr : TangentBundle I B → B)).continuous_iff]
    exact (Pullback.continuous_proj N ν (pr : TangentBundle I B → B)).prodMk
      (hei.continuous.comp (Pullback.continuous_lift N ν (pr : TangentBundle I B → B)))
  let eC : Iso C CN :=
    { linearEquiv := fun z ↦ (e z.proj).toLinearEquiv.baseChange ℝ ℂ
      continuous_total := continuous_complexification_map
        (V := R) (W := N) (E := W) (F := Y)
        (fun z : TangentBundle I B ↦ (e z.proj).toLinearMap) hep
      continuous_symm := by
        have hc : Continuous (fun z : TotalSpace Unit CN ↦
            (⟨z.proj, ((e z.proj.proj).symm.toLinearMap.baseChange ℂ) z.snd⟩ :
              TotalSpace Unit C)) :=
          continuous_complexification_map (V := N) (W := R) (E := Y) (F := W)
            (fun z : TangentBundle I B ↦ (e z.proj).symm.toLinearMap) hepi
        apply hc.congr
        intro z
        apply TotalSpace.ext rfl
        apply heq_of_eq
        change ((e z.proj.proj).symm.toLinearMap.baseChange ℂ) z.snd =
          ((e z.proj.proj).toLinearEquiv.baseChange ℝ ℂ).symm z.snd
        induction z.snd using TensorProduct.inductionOn with
        | tmul c v => rfl
        | add v w hv hw => simp only [map_add, hv, hw] }
  have hcoords (z : TangentBundle I B) (v : C z) :
      complexificationReIm (ν z.proj) (eC.linearEquiv z v) =
        (e z.proj (complexificationReIm (W z) v).1,
          e z.proj (complexificationReIm (W z) v).2) := by
    induction v using TensorProduct.inductionOn with
    | tmul c v =>
      change complexificationReIm (ν z.proj) (c ⊗ₜ[ℝ] e z.proj v) =
        (e z.proj (complexificationReIm (W z) (c ⊗ₜ[ℝ] v)).1,
          e z.proj (complexificationReIm (W z) (c ⊗ₜ[ℝ] v)).2)
      rw [(complexificationReIm_properties _).1, (complexificationReIm_properties _).1]
      simp only [map_smul]
    | add v w hv hw =>
      simp only [map_add, hv, hw, Prod.fst_add, Prod.snd_add]
      rfl
  -- The same ordered real/imaginary pair enters K inverse and the same actual tube T.
  have hmap : (tangentEmbeddingTubularMap j hj K T).comp
      ⟨eC.totalHomeomorph, eC.totalHomeomorph.continuous⟩ = jF := by
    apply ContinuousMap.ext
    intro z
    change (T.diffeomorph ⟨z.proj, (K.equiv z.proj).symm
      (complexificationReIm (ν z.proj.proj) (eC.linearEquiv z.proj z.snd))⟩ :
      TangentBundle J Z) = F (eDouble z)
    rw [hcoords]
    exact hT z.proj (complexificationReIm (W z.proj) z.snd).1
      (complexificationReIm (W z.proj) z.snd).2
  refine ⟨K, T, ?_⟩
  intro hC hN
  -- Naturality of the actual supported Thom operator uses this complex-linear isomorphism.
  have hThom := hC.supportedThomHom_iso hN eC
  have hpush := compactSupportKZeroOpenPushforward_comp
    eC.totalHomeomorph eC.totalHomeomorph.isOpenEmbedding
    (tangentEmbeddingTubularMap j hj K T) (isOpenEmbedding_tangentEmbeddingTubularMap j hj K T)
  have hraw : (tangentEmbeddingTubularMap j hj K T) ∘ eC.totalHomeomorph = jF :=
    congrArg (fun f : C(TotalSpace Unit C, TangentBundle J Z) ↦ (f : _ → _)) hmap
  simp only [hraw, compactSupportKZeroOpenPushforward_homeomorph] at hpush
  change (compactSupportKZeroOpenPushforward (tangentEmbeddingTubularMap j hj K T)
    (isOpenEmbedding_tangentEmbeddingTubularMap j hj K T)).comp hN.supportedThomHom = _
  rw [← hThom, ← AddMonoidHom.comp_assoc, ← hpush]

end AtiyahSinger
