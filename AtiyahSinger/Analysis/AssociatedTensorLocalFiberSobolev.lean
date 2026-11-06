/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorLocalizedFiber
public import AtiyahSinger.Analysis.EquivariantAtlasOperator
public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.SmoothSectionSobolevFamily

import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Actual compact whole-fiber families in native Sobolev and metric L² spaces

Public module ID: M0179.

The original base cutoff and normalized principal representative give the same
whole-sphere sections as the existing localized-family construction. Retyping
these values into the native sphere bundle preserves all original frame
coordinates. Joint smoothness then gives continuity in each prescribed native
Sobolev norm, while the unchanged compact base support gives L² membership.
The specified native sphere metric has the same property by its actual
Sobolev-zero identification. No sphere cutoff or tensor decomposition is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

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

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1400000 in
-- Normalize the original whole-fiber cutoff and localized Sobolev L² representatives.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual compact whole-fiber input belongs to every native fiber Sobolev L² family. -/
theorem exists_associatedSphereTensorLocalizedFiber_sobolev
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
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hA).smoothSections,
      ∃ u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber,
        (∀ (z : Xp) (i : Fin a), u z i = nativeSmoothSectionLinearEquiv F.Fiber
          ((input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
            associatedSphereTensorLocalFiberCoordinates S E A b input.frame
              input.frame_mem_atlas i
              (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
              (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)))) ∧
        (∀ z ∉ (EuclideanSpace.equiv (Fin n) ℝ) '' tsupport input.cutoff, ∀ i, u z i = 0) ∧
        (∀ (s : ℝ) (i : Fin a),
          Continuous (fun z ↦ L.smoothToSobolev s (u z i)) ∧
            MemLp (fun z ↦ L.smoothToSobolev s (u z i)) 2 (volume : Measure Xp)) ∧
        ∀ i : Fin a, MemLp (fun z ↦ k.smoothToL2 ν (u z i)) 2 (volume : Measure Xp) := by
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
  dsimp only
  intro w
  obtain ⟨v, hvalue, hsmooth, hsupport, _⟩ :=
    exists_associatedSphereTensorLocalizedFiberFamily (a := a)
      S E A σ hA b input hc hinput χ hχ hχsupport hχone w
  let eF := nativeSmoothSectionLinearEquiv (n := r) (r := F.rank) F.Fiber
  let u (z : Xp) (i : Fin a) := eF (v z i)
  have hzero (z : Xp)
      (hz : z ∉ (EuclideanSpace.equiv (Fin n) ℝ) '' tsupport input.cutoff) (i : Fin a) :
      u z i = 0 := by
    change eF (v z i) = 0
    rw [hsupport z hz i, map_zero]
  -- Native frame coordinates are recovered by the exact inverse finite-coordinate equivalence.
  have hnative (i : Fin a) (j : Fin L.size) :
      ContMDiffOn ((𝓘(ℝ, Xp)).prod (𝓡 r)) 𝓘(ℝ, EuclideanSpace ℂ (Fin F.rank)) ∞
        (fun p : Xp × Y ↦ (L.frame j ⟨p.2, (u p.1 i).val p.2⟩).2)
        (Set.univ ×ˢ (L.frame j).baseSet) := by
    let e := EuclideanSpace.equiv (Fin F.rank) ℂ
    have h := hsmooth i ⟨L.frame j, L.frame_mem_atlas j⟩
    have hc := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn h
    apply hc.congr
    intro p hp
    change e.symm (e (L.frame j ⟨p.2, (v p.1 i).val p.2⟩).2) = _
    exact e.symm_apply_apply _
  have hcont (s : ℝ) (i : Fin a) : Continuous (fun z ↦ L.smoothToSobolev s (u z i)) :=
    SmoothBundlePresentation.continuous_sobolev_family 𝓘(ℝ, Xp) L
      (fun z ↦ u z i) (hnative i) s
  let K := (EuclideanSpace.equiv (Fin n) ℝ) '' tsupport input.cutoff
  have hK : IsCompact K := input.compact_support.image (EuclideanSpace.equiv (Fin n) ℝ).continuous
  have hcompact (s : ℝ) (i : Fin a) :
      HasCompactSupport (fun z ↦ L.smoothToSobolev s (u z i)) := by
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ hK.isClosed
    intro z hz
    by_contra hn
    apply hz
    change L.smoothToSobolev s (u z i) = 0
    rw [hzero z hn i, map_zero]
  refine ⟨u, fun z i ↦ congrArg eF (hvalue z i), hzero,
    fun s i ↦ ⟨hcont s i, (hcont s i).memLp_of_hasCompactSupport (hcompact s i)⟩, ?_⟩
  intro i
  -- The same sphere metric identifies Sobolev zero with its actual integral L² completion.
  let e := k.sobolevZeroEquivL2 (μ := ν) L
  have hmetric : (fun z ↦ k.smoothToL2 ν (u z i)) =
      fun z ↦ e (L.smoothToSobolev 0 (u z i)) := by
    funext z
    exact (k.sobolevZeroEquivL2_smooth L (u z i)).symm
  rw [hmetric]
  exact (e.continuous.comp (hcont 0 i)).memLp_of_hasCompactSupport
    ((hcompact 0 i).comp_left (g := e) (map_zero e))

end AtiyahSinger
