/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorSupportedReturnBound
public import AtiyahSinger.Analysis.AtlasMetricL2Comparison

/-!
# Global L² return from a supported whole-fiber family

Public module ID: M0150.

A section supported where the given base cutoff equals one is reconstructed
from its whole-fiber family. The supplied native isomorphism and metric pairing
transfer the atlas H⁰ return estimate to the global L² inclusion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (F : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
  [T2Space B]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))

local notation "D" => AssociatedEquivariantFiber (E := F.Fiber) S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- Normalize the original whole-fiber norms and the same global metric section.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Original whole-fiber norms bound the actual global L² section on its given base support. -/
theorem exists_associatedSphereTensorLocalizedFiber_global_return_bound
    (b : B) {c : OpenPartialHomeomorph B X}
    (input : BundleChartCutoff (r := a) E c) (hc : c ∈ atlas X B)
    (hinput : c.symm '' tsupport input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ c.symm '' tsupport input.cutoff, χ x = 1)
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν] :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
    ∀ (_G₀ : AtlasBundlePresentation AT) (l : ContinuousHermitianMetric T)
      (_hl : AT.IsSmoothHermitianMetric l) (N : SmoothFiniteComplexBundle (n := n + r) Z)
      (kGlobal : SmoothHermitianMetric (n := n + r) (r := N.rank) N.Fiber)
      (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
      letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
      ∀ (e : Iso T N.Fiber)
        (he : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N.Fiber)
          e.toHom.linearMap)
        (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) AT
          e.symm.toHom.linearMap),
        (∀ (z : Z) (v w : T z), kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
          (l.toCore z).inner v w) →
        let sectionEquiv :=
          (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
            (nativeSmoothSectionLinearEquiv N.Fiber)
        let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
        ∃ C : ℝ, 0 ≤ C ∧ ∀ w : AT.smoothSections,
          (∀ z, w.val z ≠ 0 → πS z ∈ c.symm '' {x | input.cutoff x = 1}) →
          ∃ u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber,
            (∀ (z : Xp) (i : Fin a), u z i = nativeSmoothSectionLinearEquiv F.Fiber
              ((input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
                associatedSphereTensorLocalFiberCoordinates S E A b input.frame
                  input.frame_mem_atlas i
                  (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                  (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)))) ∧
            (∀ (s : ℝ) (i : Fin a),
              MemLp (fun z ↦ L.smoothToSobolev s (u z i)) 2 (volume : Measure Xp)) ∧
            ∃ hu : ∀ i : Fin a,
                MemLp (fun z ↦ k.smoothToL2 ν (u z i)) 2 (volume : Measure Xp),
              ‖inclusion w‖ ≤
                C * ∑ i : Fin a, ‖(hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
  dsimp only
  intro G₀ l hl N kGlobal η hη
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  intro e he hi hpair
  let sectionEquiv :=
    (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
      (nativeSmoothSectionLinearEquiv N.Fiber)
  let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
  -- The local coordinates and the global metric bridge use the very same original section.
  have hlocalData := exists_associatedSphereTensorLocalizedFiber_return_bound (a := a)
    S E F σ hσ b input hc hinput χ hχ hχsupport hχone L k ν G₀
  let C : ℝ := hlocalData.choose
  have hC := hlocalData.choose_spec.1
  have hlocal := hlocalData.choose_spec.2
  have hglobalData :=
    AT.exists_sobolevZero_l2_comparison G₀ l hl N kGlobal η e he hi hpair
  let Cglobal : ℝ := hglobalData.choose_spec.choose
  have hCglobal := hglobalData.choose_spec.choose_spec.2.1
  have hglobal := hglobalData.choose_spec.choose_spec.2.2
  refine ⟨Cglobal * C, mul_nonneg hCglobal.le hC, ?_⟩
  intro w hw
  let u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber :=
    (hlocal w hw).choose
  have hu := (hlocal w hw).choose_spec.1
  have hs := (hlocal w hw).choose_spec.2.1
  have hm := (hlocal w hw).choose_spec.2.2.choose
  have hb := (hlocal w hw).choose_spec.2.2.choose_spec
  refine ⟨u, hu, hs, hm, ?_⟩
  apply (hglobal w).2.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hCglobal.le

end AtiyahSinger
