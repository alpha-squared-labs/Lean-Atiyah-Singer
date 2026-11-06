/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FrameSpherePoleThom
public import AtiyahSinger.Geometry.FrameSphereCotangentPoleComparison
public import AtiyahSinger.Geometry.FrameSpherePositiveCoordinates
public import AtiyahSinger.Topology.FrameSphereTangentThom
public import AtiyahSinger.Topology.TangentComplexificationMusical

/-!
# The original frame-sphere pole class and its tangent embedding pushforward

Public module ID: M0641.

Compare the actual associated south-pole class with the normal Thom-to-tube
map. The metric flat base change retains the original complexified vector;
the cotangent pole has the verified reciprocal scales and positive correction.
Its proper homotopy removes this same correction before normal Thom naturality.
No equality of analytic indices enters this class comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Function Manifold Topology
open scoped ContDiff TensorProduct

variable {n : ℕ} (r : ℕ)
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold (𝓡 n) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V (𝓡 n)]
  [IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere
  verticalTangentTopology

local notation "BModel" => EuclideanSpace ℝ (Fin n)
local notation "RModel" => EuclideanSpace ℝ (Fin r)
local notation "GO" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle GO P (OrthogonalSphere r)


attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  ComplexBundle.t2Space_totalSpace ComplexBundle.locallyCompactSpace_totalSpace
  tangentBundleFullChartedSpace tangentBundle_full_isManifold
  complexifiedNormalPullbackTopology continuousSMul_orthogonalSphereCotangent
  compactSpace_orthogonalGroup

variable [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ)
    (OrthogonalFrameBundle r V) (OrthogonalSphere r))]
  [SecondCountableTopology (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ)
    (OrthogonalFrameBundle r V) (OrthogonalSphere r))]

set_option maxSynthPendingDepth 55 in
set_option maxHeartbeats 20000000 in
-- The full type retains the original associated quotient, two pullbacks and the normal tube.

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same south-pole twisted class is exactly the original tangent normal pushforward
transported by the compatible metric musical map. -/
theorem exists_frameSpherePole_tangentPushforward_comparison
    (H : letI := continuousSMul_orthogonalFrame r V (𝓡 n)
      let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (g : SmoothTangentMetric (n := n) (M := B))
    (h : letI := continuousSMul_orthogonalFrame r V (𝓡 n)
      let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      ContMDiffRiemannianMetric 𝓘(ℝ, BModel × RModel) ∞ (BModel × RModel)
        (TangentSpace 𝓘(ℝ, BModel × RModel) : Z → Type _)) :
    letI := continuousSMul_orthogonalFrame r V (𝓡 n)
    let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let I := 𝓡 n
    let J := 𝓘(ℝ, BModel × RModel)
    let q := smoothAssociatedSphereProjection S
    let H' : SmoothHorizontalLift q := H
    let h' : ContMDiffRiemannianMetric J ∞ (BModel × RModel) (TangentSpace J : Z → Type _) := h
    let d := (exists_tangentMusical_diffeomorph h').choose
    let eCot := associatedSphereCotangentHomeomorph S H'
    let a := frameSphereStereographic (EB := BModel) r V
    let j : ContMDiffMap I J B Z ∞ :=
      ⟨fun x ↦ a.symm ⟨x, 0⟩,
        (frameSphereStereographic_spec (EB := BModel) r V).2.2.2.2.2.comp
          (contMDiff_zeroSection ℝ V)⟩
    let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := BModel) r V
    letI : T2Space (TangentBundle I B) := (tangentBundle_topology BModel B).1
    letI : LocallyCompactSpace (TangentBundle I B) :=
      ChartedSpace.locallyCompactSpace (BModel × BModel) (TangentBundle I B)
    letI : T2Space (TangentBundle J Z) := (tangentBundle_topology (BModel × RModel) Z).1
    letI : LocallyCompactSpace (TangentBundle J Z) :=
      ChartedSpace.locallyCompactSpace ((BModel × RModel) × (BModel × RModel)) (TangentBundle J Z)
    let hQ := isPrincipalBundle_pullback (G := GO)
      (projection := orthogonalFrameProjection r V) (cotangentProjection (n := n) (M := B))
    letI := associatedBundle_t2Space
      (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) hQ
    letI := associatedBundle_locallyCompactSpace
      (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) hQ
    letI := eCot.t2Space
    letI := eCot.symm.isOpenEmbedding.locallyCompactSpace
    letI := isFiniteRank_complexifiedNormalPullback j hj.isImmersion
    (∀ (x : Z) (v : TangentSpace I (q x)),
      h'.inner x (H'.lift x v) = (g.inner (q x) v).comp (mfderiv J I q x)) →
    (∀ x : B, H'.lift (j x) = mfderiv I J j x) →
    ∃ K : TangentNormalSplitting j hj,
      ∃ T : TubularNeighborhood (smoothTangentMap j) (isImmersion_smoothTangentMap j hj),
        ∀ (hN : ContinuousHermitianMetric (ComplexifiedNormalPullback j))
          (u : CompactSupportKZero (TangentBundle I B)),
          compactSupportKZeroHomeomorph eCot
            (associatedSupportTwistedProduct (G := GO)
              (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r))
              (cotangentProjection (n := n) (M := B))
              (compactSupportKZeroHomeomorph g.flatHomeomorph u)
              (orthogonalSphereMusicalKMap r (orthogonalSpherePolePushforward r false 1))) =
            compactSupportKZeroHomeomorph d.toHomeomorph
              (tangentEmbeddingPushforwardWith j hj K T hN u) := by
  classical
  let := continuousSMul_orthogonalFrame r V (𝓡 n)
  let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓡 n
  let J := 𝓘(ℝ, BModel × RModel)
  let q := smoothAssociatedSphereProjection S
  let d := (exists_tangentMusical_diffeomorph h).choose
  let eCot := associatedSphereCotangentHomeomorph S H
  let a := frameSphereStereographic (EB := BModel) r V
  let j : ContMDiffMap I J B Z ∞ :=
    ⟨fun x ↦ a.symm ⟨x, 0⟩,
      (frameSphereStereographic_spec (EB := BModel) r V).2.2.2.2.2.comp
        (contMDiff_zeroSection ℝ V)⟩
  let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := BModel) r V
  let TM := TangentBundle I B
  let TZ := TangentBundle J Z
  let X := CotangentTotalSpace (n := n) (M := B)
  let f := cotangentProjection (n := n) (M := B)
  let : T2Space TM := (tangentBundle_topology BModel B).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (BModel × BModel) TM
  let : T2Space TZ := (tangentBundle_topology (BModel × RModel) Z).1
  let : LocallyCompactSpace TZ :=
    ChartedSpace.locallyCompactSpace ((BModel × RModel) × (BModel × RModel)) TZ
  let hQ := isPrincipalBundle_pullback (G := GO)
    (projection := orthogonalFrameProjection r V) (cotangentProjection (n := n) (M := B))
  let := associatedBundle_t2Space
    (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) hQ
  let := associatedBundle_locallyCompactSpace
    (Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) hQ
  let := eCot.t2Space
  let := eCot.symm.isOpenEmbedding.locallyCompactSpace
  let := isFiniteRank_complexifiedNormalPullback j hj.isImmersion
  dsimp only
  intro hcompat hH
  obtain ⟨K, T, hnormal⟩ :=
    exists_frameSphere_tangentThom_comparison (EB := BModel) r V H hH
  obtain ⟨c, hc, HC, hHC⟩ :=
    exists_frameSphere_positiveCoordinates_properHomotopy (EB := BModel) r V h
  -- The source scalar extension and its cotangent pullback are the original bundles.
  let CB := fun b : B ↦ ℂ ⊗[ℝ] V b
  let := complexificationTopology RModel V
  let := isFiniteRank_complexification RModel V
  let : IsContinuousRiemannianBundle RModel V := by
    obtain ⟨k, hk, hinner⟩ :=
      IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := ∞) (F := RModel) (E := V)
    exact ⟨k, hk.continuous, hinner⟩
  let hB := complexificationHermitianMetric (R := RModel) (E := V)
  let p : C(TM, B) := ⟨TotalSpace.proj, FiberBundle.continuous_proj BModel (TangentSpace I)⟩
  let WT := (p : TM → B) *ᵖ V
  let CT := fun z : TM ↦ ℂ ⊗[ℝ] WT z
  let CX := (f : X → B) *ᵖ CB
  let := isFiniteRank_pullback (E := CB) f
  let := complexificationTopology RModel WT
  let := isFiniteRank_complexification RModel WT
  let : ParacompactSpace TM := (tangentBundle_topology BModel B).2.2
  let hT : ContinuousHermitianMetric CT := (nonempty_continuousHermitianMetric CT).some
  obtain ⟨qM, hqM, hqMv, hqMThom⟩ := exists_tangentComplexification_musical_thomMap RModel V g
  obtain ⟨e, he, eF, heF, jP, hjP, hjPv, hclass⟩ :=
    exists_frameSpherePole_thom_openMap (n := n) (r := r) V H false
  let F := (exists_frameSphere_tangentParametrization r V H).choose
  let eDouble := complexificationDoubleTotalHomeomorph RModel WT
  let D := TotalSpace (RModel × RModel) (WT ×ᵇ WT)
  let : T2Space D := eDouble.t2Space
  let : LocallyCompactSpace D := eDouble.symm.isOpenEmbedding.locallyCompactSpace
  let cMap : C(D, D) := ⟨c, c.continuous⟩
  let eMap : C(TotalSpace Unit CT, D) := ⟨eDouble, eDouble.continuous⟩
  let U : TopologicalSpace.Opens TZ :=
    ⟨TotalSpace.proj ⁻¹' a.source,
      a.open_source.preimage (FiberBundle.continuous_proj (BModel × RModel) (TangentSpace J))⟩
  let k : C(TotalSpace (RModel × RModel) (WT ×ᵇ WT), TZ) :=
    ⟨fun z ↦ (F z : TZ), continuous_subtype_val.comp F.contMDiff.continuous⟩
  have hk : IsOpenEmbedding k := U.isOpen.isOpenEmbedding_subtypeVal.comp
    F.toHomeomorph.isOpenEmbedding
  let jF : C(TotalSpace Unit CT, TZ) := k.comp ⟨eDouble, eDouble.continuous⟩
  have hjF : IsOpenEmbedding jF := hk.comp eDouble.isOpenEmbedding
  let dMap : C(TZ, _) := ⟨d, d.contMDiff.continuous⟩
  -- The actual pole map agrees on every original frame representative, with both scales intact.
  have hmaps : jP.comp qM = (dMap.comp k).comp
      (cMap.comp eMap) := by
    apply ContinuousMap.ext
    rintro ⟨⟨b, ξ⟩, v⟩
    obtain ⟨p₀, hp₀⟩ := S.toIsPrincipalBundle.projection_properties.2.2 b
    rcases p₀ with ⟨b₀, frame⟩
    change b₀ = b at hp₀
    subst b₀
    let p₀ : P := ⟨b, frame⟩
    let uv := complexificationReIm (V b) v
    let z : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2
      (fun i ↦ (frame.symm uv.1 i : ℂ) + Complex.I * (frame.symm uv.2 i : ℂ))
    have hre : frame (WithLp.toLp 2 (fun i ↦ (z i).re)) = uv.1 := by
      have hz : WithLp.toLp 2 (fun i ↦ (z i).re) = frame.symm uv.1 := by
        ext i
        simp [z]
      rw [hz, frame.apply_symm_apply]
    have him : frame (WithLp.toLp 2 (fun i ↦ (z i).im)) = uv.2 := by
      have hz : WithLp.toLp 2 (fun i ↦ (z i).im) = frame.symm uv.2 := by
        ext i
        simp [z]
      rw [hz, frame.apply_symm_apply]
    let Q := PrincipalBundlePullback f (orthogonalFrameProjection r V)
    let pQ : Q := ⟨(⟨b, g.inner b ξ⟩, p₀), rfl⟩
    let zA := associatedBundleMk GO Q (EuclideanSpace ℂ (Fin r)) pQ z
    have hebase : e (associatedBundleMk GO P (EuclideanSpace ℂ (Fin r)) p₀ z) =
        (⟨b, v⟩ : TotalSpace Unit CB) := by
      rw [he]
      change (⟨b, (complexificationReIm (V b)).symm
        (frame (WithLp.toLp 2 (fun i ↦ (z i).re)),
          frame (WithLp.toLp 2 (fun i ↦ (z i).im)))⟩ : TotalSpace Unit CB) = ⟨b, v⟩
      rw [hre, him]
      exact congrArg (fun w ↦ (⟨b, w⟩ : TotalSpace Unit CB))
        ((complexificationReIm (V b)).symm_apply_apply v)
    have hepair : eF zA = qM (⟨⟨b, ξ⟩, v⟩ : TotalSpace Unit CT) := by
      apply (pullbackTotalSpaceEmbedding_isClosedEmbedding CB f).injective
      rw [heF, hqMv]
      change (⟨b, g.inner b ξ⟩, e (associatedBundleMk GO P (EuclideanSpace ℂ (Fin r)) p₀ z)) =
        ((⟨b, g.inner b ξ⟩ : X), (⟨b, v⟩ : TotalSpace Unit CB))
      rw [hebase]
    have hpole := hjPv pQ z
    rw [hepair] at hpole
    apply hpole.trans
    have hcoordinate := frameSphere_cotangentPole_eq_musical_tangentParametrization r V H g h
      hcompat p₀ ξ z
    apply hcoordinate.trans
    let target (u w : V b) : D :=
      ⟨⟨b, ξ⟩, (2 : ℝ) • u,
        (1 / 2 : ℝ) • (exists_frameSphere_verticalRieszComparison r V h).choose
          ⟨b, (2 : ℝ) • u⟩ w⟩
    have hframe : target (frame (WithLp.toLp 2 (fun i ↦ (z i).re)))
        (frame (WithLp.toLp 2 (fun i ↦ (z i).im))) = target uv.1 uv.2 :=
      congrArg₂ target hre him
    have hcor : c (eDouble (⟨⟨b, ξ⟩, v⟩ : TotalSpace Unit CT)) = target uv.1 uv.2 :=
      hc (eDouble (⟨⟨b, ξ⟩, v⟩ : TotalSpace Unit CT))
    exact congrArg (fun w : D ↦ d (k w)) (hframe.trans hcor.symm)
  -- Proper homotopy removes the same positive correction on the whole doubled bundle.
  have hcK : compactSupportKZeroHomeomorph c = AddMonoidHom.id _ := by
    have h := compactSupportKZeroPullback_eq_of_proper_homotopy isProperMap_id
      c.isProperMap HC hHC
    rw [compactSupportKZeroPullback_id] at h
    change AddMonoidHom.id _ = compactSupportKZeroHomeomorph c.symm at h
    have hc := compactSupportKZeroHomeomorph_symm c
    rw [← h, AddMonoidHom.id_comp] at hc
    exact hc
  have hpush : (compactSupportKZeroOpenPushforward jP hjP).comp
      (compactSupportKZeroOpenPushforward qM hqM) =
      (compactSupportKZeroHomeomorph d.toHomeomorph).comp
        (compactSupportKZeroOpenPushforward jF hjF) := by
    have hraw : (jP : _ → _) ∘ qM = d.toHomeomorph ∘ k ∘ c ∘ eDouble :=
      congrArg (fun z : C(TotalSpace Unit CT, _) ↦ (z : _ → _)) hmaps
    calc
      _ = compactSupportKZeroOpenPushforward (jP ∘ qM) (hjP.comp hqM) :=
        (compactSupportKZeroOpenPushforward_comp qM hqM jP hjP).symm
      _ = compactSupportKZeroOpenPushforward (d.toHomeomorph ∘ k ∘ c ∘ eDouble)
          (d.toHomeomorph.isOpenEmbedding.comp
            (hk.comp (c.isOpenEmbedding.comp eDouble.isOpenEmbedding))) := by
        simp only [hraw]
      _ = (compactSupportKZeroOpenPushforward d.toHomeomorph d.toHomeomorph.isOpenEmbedding).comp
          ((compactSupportKZeroOpenPushforward k hk).comp
            ((compactSupportKZeroOpenPushforward c c.isOpenEmbedding).comp
              (compactSupportKZeroOpenPushforward eDouble eDouble.isOpenEmbedding))) := by
        rw [compactSupportKZeroOpenPushforward_comp (k ∘ c ∘ eDouble)
          (hk.comp (c.isOpenEmbedding.comp eDouble.isOpenEmbedding))
          d.toHomeomorph d.toHomeomorph.isOpenEmbedding,
          compactSupportKZeroOpenPushforward_comp (c ∘ eDouble)
            (c.isOpenEmbedding.comp eDouble.isOpenEmbedding) k hk,
          compactSupportKZeroOpenPushforward_comp eDouble eDouble.isOpenEmbedding
            c c.isOpenEmbedding]
      _ = _ := by
        rw [compactSupportKZeroOpenPushforward_homeomorph d.toHomeomorph,
          compactSupportKZeroOpenPushforward_homeomorph c, hcK, AddMonoidHom.id_comp,
          ← compactSupportKZeroOpenPushforward_comp eDouble eDouble.isOpenEmbedding k hk]
        rfl
  refine ⟨K, T, ?_⟩
  intro hN u
  have hmus := DFunLike.congr_fun (hqMThom hB hT) u
  change compactSupportKZeroOpenPushforward qM hqM (hT.supportedThomHom u) =
    (hB.pullback f).supportedThomHom (compactSupportKZeroHomeomorph g.flatHomeomorph u) at hmus
  have hnormalu := DFunLike.congr_fun (hnormal hT hN) u
  change tangentEmbeddingPushforwardWith j hj K T hN u =
    compactSupportKZeroOpenPushforward jF hjF (hT.supportedThomHom u) at hnormalu
  rw [hclass, ← hmus, ← AddMonoidHom.comp_apply, hpush,
    AddMonoidHom.comp_apply, ← hnormalu]

end AtiyahSinger
