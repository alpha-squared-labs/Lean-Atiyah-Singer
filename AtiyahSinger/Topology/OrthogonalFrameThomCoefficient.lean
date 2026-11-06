/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedThomCoefficient
public import AtiyahSinger.Topology.OrthogonalFrameThomClass

/-!
# The original orthogonal frame Thom class with supported coefficients

Public module ID: M1980.

The specified frame complexification homeomorphism and its original
associated Bott class identify the actual supported Thom map over every
LCH pullback base. The coefficient may have noncompact base, but its
support is compact. The complete paired-map identity retains the actual
frame coordinates and the canonical complexification metric.

This supplies the normal coefficient comparison used in SG III.13.
The sphere open extension and its stereographic scaling remain separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct Matrix.Norms.Elementwise

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

variable [CompactSpace B] [T2Space B]

include n r V in
set_option maxSynthPendingDepth 40 in
set_option synthInstance.maxHeartbeats 100000 in
-- Resolve the original frame metric and the same right tensor-coefficient instances.
set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Use precisely the original frame metric, complexification and principal quotient instances.
/-- The original associated exterior Bott product is the pulled-back supported Thom operator. -/
theorem exists_orthogonalFrame_supportedThom_homeomorph
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] (f : C(X, B)) :
    letI := continuousSMul_orthogonalFrame r V I
    let hP := (smoothOrthogonalFrameAtlas r V I).toIsPrincipalBundle
    letI := hP
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
    let Z := AssociatedBundle GO P W
    let projection := orthogonalFrameProjection r V
    letI := associatedBundle_t2Space (Y := W) hP
    letI := associatedBundle_locallyCompactSpace (Y := W) hP
    letI := associatedBundle_t2Space (Y := W)
      (isPrincipalBundle_pullback (G := GO) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace (Y := W)
      (isPrincipalBundle_pullback (G := GO) (projection := projection) f)
    ∃ e : Z ≃ₜ TotalSpace Unit C,
      (∀ (p : P) (z : W),
        e (associatedBundleMk GO P W p z) =
          ⟨p.1, (complexificationReIm (V p.1)).symm
            (p.2 (WithLp.toLp 2 (fun i ↦ (z i).re)),
              p.2 (WithLp.toLp 2 (fun i ↦ (z i).im)))⟩) ∧
      ∃ eF : AssociatedBundle GO (PrincipalBundlePullback f projection) W ≃ₜ
          TotalSpace Unit ((f : X → B) *ᵖ C),
        (∀ z, pullbackTotalSpaceEmbedding (F := Unit) (E := C) f (eF z) =
          ((associatedBundlePullbackProdMap (G := GO) (Y := W) f z).1,
            e (associatedBundlePullbackProdMap (G := GO) (Y := W) f z).2)) ∧
        ∀ a : CompactSupportKZero X,
          associatedSupportTwistedProduct (G := GO) (Y := W) f a
            (equivariantExteriorBottClass (orthogonalComplexification_unitary r)) =
            compactSupportKZeroPullback ⟨eF, eF.continuous⟩ eF.isProperMap
              ((h.pullback f).supportedThomHom a) := by
  classical
  let := continuousSMul_orthogonalFrame r V I
  let hP := (smoothOrthogonalFrameAtlas r V I).toIsPrincipalBundle
  let := hP
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
  let Z := AssociatedBundle GO P W
  let projection := orthogonalFrameProjection r V
  let := associatedBundle_t2Space (Y := W) hP
  let := associatedBundle_locallyCompactSpace (Y := W) hP
  let := associatedBundle_t2Space (Y := W)
    (isPrincipalBundle_pullback (G := GO) (projection := projection) f)
  let := associatedBundle_locallyCompactSpace (Y := W)
    (isPrincipalBundle_pullback (G := GO) (projection := projection) f)
  obtain ⟨e, he, hclass⟩ := exists_orthogonalFrame_thomClass_homeomorph (n := n) (r := r) V
  have heBase (z : Z) : (e z).proj = associatedBundleProjection (F := W) hP z := by
    induction z using Quotient.inductionOn with
    | h w => exact congrArg (fun z : TotalSpace Unit C ↦ z.proj) (he w.1 w.2)
  let oneB := (compactSupportKZeroCompactEquiv B).symm
    (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1))
  -- The compact-base unit evaluates the same supported operator to its original exterior class.
  have hunit : h.supportedThomHom oneB = exteriorThomClass C h.continuous_pairing := by
    change supportedThomHom C h.continuous_pairing oneB = _
    rw [supportedThomHom_compact, AddMonoidHom.comp_apply]
    change exteriorThomHom C h.continuous_pairing
      ((compactSupportKZeroCompactEquiv B) ((compactSupportKZeroCompactEquiv B).symm
        (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1)))) = _
    rw [AddEquiv.apply_symm_apply]
    exact complexKZeroCompactSupportAction_one
      (⟨π Unit C, continuous_proj⟩ : C(TotalSpace Unit C, B)) _
  have hv : associatedSupportKZero hP
      (equivariantExteriorBottClass (orthogonalComplexification_unitary r)) =
        compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap
          (h.supportedThomHom oneB) := by
    rw [hunit]
    exact hclass
  -- Apply the full paired-map result to this exact frame homeomorphism and exterior class.
  obtain ⟨eF, heF, hproduct⟩ := exists_associatedSupportTwistedProduct_thomHomeomorph h e heBase
    (equivariantExteriorBottClass (orthogonalComplexification_unitary r)) hv f
  exact ⟨e, he, eF, heF, hproduct⟩

end AtiyahSinger

