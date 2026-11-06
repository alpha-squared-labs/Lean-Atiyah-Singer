/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SphereCotangentPoleClass
public import AtiyahSinger.Topology.AssociatedSphereCotangentKZero
public import AtiyahSinger.Topology.AssociatedTwistedProductOpen
public import AtiyahSinger.Topology.OrthogonalFrameThomCoefficient

/-!
# The actual associated pole class as an open image of the normal Thom class

Public module ID: M0642.

The original frame complexification and its supported coefficient comparison,
followed by equivariant pole extension, give an explicit open map from the
pulled complexified bundle into the actual cotangent space of its frame sphere.
The specified horizontal lift, original quotient representatives and normalized
inverse-dual pole chart all remain visible in the formula.

This is the geometric class comparison preceding SG III.13 Property 2. The
remaining comparison with a normalized tangent tube is separate: the theorem
does not identify an arbitrary horizontal lift with the south section derivative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct Matrix.Norms.Elementwise

private theorem homeomorph_openPushforward_pullback
    {A B C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    [LocallyCompactSpace A] [T2Space A] [LocallyCompactSpace B] [T2Space B]
    [LocallyCompactSpace C] [T2Space C] [LocallyCompactSpace D] [T2Space D]
    (e : A ≃ₜ B) (f : C(A, C)) (hf : Topology.IsOpenEmbedding f) (g : C ≃ₜ D)
    (b : CompactSupportKZero B) :
    compactSupportKZeroHomeomorph g
        (compactSupportKZeroOpenPushforward f hf
          (compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap b)) =
      compactSupportKZeroOpenPushforward (g ∘ f ∘ e.symm)
        (g.isOpenEmbedding.comp (hf.comp e.symm.isOpenEmbedding)) b := by
  change compactSupportKZeroHomeomorph g
    (compactSupportKZeroOpenPushforward f hf (compactSupportKZeroHomeomorph e.symm b)) = _
  rw [← compactSupportKZeroOpenPushforward_homeomorph g,
    ← compactSupportKZeroOpenPushforward_homeomorph e.symm,
    ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp,
    ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp]
  rfl

variable {n r : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin r)) V]

local notation "RModel" => EuclideanSpace ℝ (Fin r)
local notation "W" => EuclideanSpace ℂ (Fin r)
local notation "GO" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))


attribute [local instance] orthogonalFrameTopology exteriorAlgebraNormedAddCommGroup
  exteriorAlgebraNormedSpace exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology isFiniteRank_associatedEquivariant isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace
  t2Space_cotangent locallyCompactSpace_cotangent continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent compactSpace_orthogonalGroup

variable [CompactSpace B] [T2Space B]

set_option maxSynthPendingDepth 45 in
set_option synthInstance.maxHeartbeats 100000 in
-- The source has nested original principal pullback and complexification instances.
set_option maxHeartbeats 6000000 in
-- Retain the three native associated, complexified pullback and cotangent bundle realizations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The source, associated open map and target use the same actual quotient witnesses.
/-- The original sphere pole class is the actual supported Thom class extended by the
specified frame, inverse-dual pole chart and supplied horizontal lift. -/
theorem exists_frameSpherePole_thom_openMap
    (H : letI := continuousSMul_orthogonalFrame r V I
      let S := smoothOrthogonalFrameAtlas r V I
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) (atInfinity : Bool) :
    letI := continuousSMul_orthogonalFrame r V I
    let S := smoothOrthogonalFrameAtlas r V I
    let hP := S.toIsPrincipalBundle
    letI := hP
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let C := fun b : B ↦ ℂ ⊗[ℝ] V b
    letI := complexificationTopology RModel V
    letI := ComplexBundle.isFiniteRank_complexification RModel V
    letI : IsContinuousRiemannianBundle RModel V := by
      obtain ⟨g, hg, hinner⟩ :=
        IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := ∞) (F := RModel) (E := V)
      exact ⟨g, hg.continuous, hinner⟩
    let h := complexificationHermitianMetric (R := RModel) (E := V)
    letI (b : B) : NormedAddCommGroup (C b) := (h.toCore b).toNormedAddCommGroup
    letI (b : B) : InnerProductSpace ℂ (C b) := InnerProductSpace.ofCore (h.toCore b).toCore
    let X := CotangentTotalSpace (n := n) (M := B)
    let f := cotangentProjection (n := n) (M := B)
    let projection := orthogonalFrameProjection r V
    let Q := PrincipalBundlePullback f projection
    let Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
    let Z := AssociatedBundle GO P W
    letI := associatedBundle_t2Space (Y := W) hP
    letI := associatedBundle_locallyCompactSpace (Y := W) hP
    let hQ := isPrincipalBundle_pullback (G := GO) (projection := projection) f
    letI := associatedBundle_t2Space (Y := W) hQ
    letI := associatedBundle_locallyCompactSpace (Y := W) hQ
    letI := associatedBundle_t2Space (Y := Y) hQ
    letI := associatedBundle_locallyCompactSpace (Y := Y) hQ
    let eCot := associatedSphereCotangentHomeomorph S H
    letI := eCot.t2Space
    letI := eCot.symm.isOpenEmbedding.locallyCompactSpace
    ∃ e : Z ≃ₜ TotalSpace Unit C,
      (∀ (p : P) (z : W),
        e (associatedBundleMk GO P W p z) =
          ⟨p.1, (complexificationReIm (V p.1)).symm
            (p.2 (WithLp.toLp 2 (fun i ↦ (z i).re)),
              p.2 (WithLp.toLp 2 (fun i ↦ (z i).im)))⟩) ∧
      ∃ eF : AssociatedBundle GO Q W ≃ₜ TotalSpace Unit ((f : X → B) *ᵖ C),
        (∀ z, pullbackTotalSpaceEmbedding (F := Unit) (E := C) f (eF z) =
          ((associatedBundlePullbackProdMap (G := GO) (Y := W) f z).1,
            e (associatedBundlePullbackProdMap (G := GO) (Y := W) f z).2)) ∧
        ∃ (j : C(TotalSpace Unit ((f : X → B) *ᵖ C),
            TotalSpace (((EuclideanSpace ℝ (Fin n)) × RModel) →L[ℝ] ℝ)
              (fun z : AssociatedBundle GO P (OrthogonalSphere r) ↦
                TangentSpace 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) × RModel) z →L[ℝ] ℝ)))
            (hj : Topology.IsOpenEmbedding j),
          (∀ (p : Q) (z : W), j (eF (associatedBundleMk GO Q W p z)) =
            eCot (associatedBundleMk GO Q Y p
              (orthogonalSphereCotangentChart r atInfinity z))) ∧
          ∀ a : CompactSupportKZero X,
            compactSupportKZeroHomeomorph eCot
              (associatedSupportTwistedProduct (G := GO) (Y := Y) f a
                (orthogonalSphereMusicalKMap r (orthogonalSpherePolePushforward r atInfinity 1))) =
              compactSupportKZeroOpenPushforward j hj ((h.pullback f).supportedThomHom a) := by
  classical
  let := continuousSMul_orthogonalFrame r V I
  let S := smoothOrthogonalFrameAtlas r V I
  let hP := S.toIsPrincipalBundle
  let := hP
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let C := fun b : B ↦ ℂ ⊗[ℝ] V b
  let := complexificationTopology RModel V
  let := ComplexBundle.isFiniteRank_complexification RModel V
  let : IsContinuousRiemannianBundle RModel V := by
    obtain ⟨g, hg, hinner⟩ :=
      IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := ∞) (F := RModel) (E := V)
    exact ⟨g, hg.continuous, hinner⟩
  let h := complexificationHermitianMetric (R := RModel) (E := V)
  let (b : B) : NormedAddCommGroup (C b) := (h.toCore b).toNormedAddCommGroup
  let (b : B) : InnerProductSpace ℂ (C b) := InnerProductSpace.ofCore (h.toCore b).toCore
  let X := CotangentTotalSpace (n := n) (M := B)
  let f := cotangentProjection (n := n) (M := B)
  let projection := orthogonalFrameProjection r V
  let Q := PrincipalBundlePullback f projection
  let Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
  let := associatedBundle_t2Space (Y := W) hP
  let := associatedBundle_locallyCompactSpace (Y := W) hP
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let hQ := isPrincipalBundle_pullback (G := GO) (projection := projection) f
  let := associatedBundle_t2Space (Y := W) hQ
  let := associatedBundle_locallyCompactSpace (Y := W) hQ
  let := associatedBundle_t2Space (Y := Y) hQ
  let := associatedBundle_locallyCompactSpace (Y := Y) hQ
  let eCot := associatedSphereCotangentHomeomorph S H
  let := eCot.t2Space
  let := eCot.symm.isOpenEmbedding.locallyCompactSpace
  -- The existing frame comparison specifies both real/imaginary coordinates and the paired map.
  obtain ⟨e, he, eF, heF, hThom⟩ :=
    exists_orthogonalFrame_supportedThom_homeomorph (n := n) (r := r) V f
  let pole := orthogonalSphereCotangentChart r atInfinity
  let hpole := orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity
  let epole := orthogonalSphereCotangentChart_equivariant r atInfinity
  let jA := associatedBundleMap («P» := Q) pole epole
  have hjA : Topology.IsOpenEmbedding jA := isOpenEmbedding_associatedBundleMap pole epole hpole
  let j : C(TotalSpace Unit ((f : X → B) *ᵖ C), _) :=
    ⟨fun z ↦ eCot (jA (eF.symm z)),
      eCot.continuous.comp (jA.continuous.comp eF.symm.continuous)⟩
  have hj : Topology.IsOpenEmbedding j :=
    eCot.isOpenEmbedding.comp (hjA.comp eF.symm.isOpenEmbedding)
  refine ⟨e, he, eF, heF, j, hj, ?_, ?_⟩
  · intro p z
    change eCot (jA (eF.symm (eF (associatedBundleMk GO Q W p z)))) = _
    rw [eF.symm_apply_apply]
    rfl
  · intro a
    -- Extend the actual pole class first; proper/open base change keeps the full paired map.
    rw [orthogonalSphereMusicalKMap_polePushforward,
      associatedSupportTwistedProduct_openPushforward, hThom]
    -- Abstract functoriality is applied to these exact maps without unfolding their constructions.
    exact homeomorph_openPushforward_pullback eF jA hjA eCot
      ((h.pullback f).supportedThomHom a)

end AtiyahSinger
