/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSmoothBundleDescent
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Topology.AssociatedInvariantMetric

/-!
# Smoothness of the specified metric on the associated sphere bundle

Public module ID: M1077.

The given invariant sphere metric descends smoothly in the original
associated bundle atlas. In a principal chart, both inverse frame vectors
use the same normalized principal representative. Their pairing is exactly
the original sphere Gram entry composed with the original sphere coordinate.
The metric, action, quotient fibers and manifold model remain unchanged.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {E : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (E y)]
  [∀ y, Module ℂ (E y)] [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (A : SmoothComplexBundleAtlas (n := r) E)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) E)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified invariant smooth sphere metric is smooth in the original associated atlas. -/
theorem isSmoothHermitianMetric_associatedEquivariantMetric
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (h : ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (hInvariant : ∀ (g : G) (y : OrthogonalSphere r) (u v : E y),
      (h.toCore (g • y)).inner (σ.linearMap g y u) (σ.linearMap g y v) =
        (h.toCore y).inner u v) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereSmoothBundleAtlas S A σ hσ).IsSmoothHermitianMetric
      (associatedEquivariantMetric S.toIsPrincipalBundle σ h hInvariant) := by
  classical
  let := associatedSphereChartedSpace S
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let t (b : B) := associatedSphereTrivialization S b
  have hbase (b : B) : (t b).baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have hchart (i : B × A.Index) :
      (AD.chart i).baseSet = (t i.1).source ∩
        (t i.1) ⁻¹' (Set.univ ×ˢ (A.chart i.2).baseSet) :=
    (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization i.1) (S.equivariant i.1) (A.chart i.2) (A.linear i.2)).choose_spec.1
  have hcoord (b : B) : ContMDiffOn (𝓡 (n + r)) ((𝓡 n).prod (𝓡 r)) ∞
      (t b) (t b).source :=
    ((exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b).1.comp
      d.symm.contMDiff.contMDiffOn (fun _ hz ↦ hz)
  intro i a b
  have hsource (z : Z) (hz : z ∈ (AD.chart i).baseSet) : z ∈ (t i.1).source :=
    ((hchart i) ▸ hz).1
  have hsphere (z : Z) (hz : z ∈ (AD.chart i).baseSet) :
      (t i.1 z).2 ∈ (A.chart i.2).baseSet := ((hchart i) ▸ hz).2.2
  have hy : ContMDiffOn (𝓡 (n + r)) (𝓡 r) ∞
      (fun z : Z ↦ (t i.1 z).2) (AD.chart i).baseSet :=
    contMDiff_snd.comp_contMDiffOn ((hcoord i.1).mono hsource)
  have hs := (hh i.2 a b).comp hy hsphere
  apply hs.congr
  intro z hz
  have hz' := hsphere z hz
  have hx : (t i.1 z).1 ∈ (S.trivialization i.1).baseSet :=
    hbase i.1 ▸ (t i.1).mem_target.mp ((t i.1).map_source (hsource z hz))
  let p := (S.trivialization i.1).toOpenPartialHomeomorph.symm ((t i.1 z).1, 1)
  have hp : projection p = (t i.1 z).1 :=
    (S.trivialization i.1).proj_symm_apply' hx
  have hrep : associatedBundleMk G P (OrthogonalSphere r) p (t i.1 z).2 = z :=
    ((exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization i.1) (S.equivariant i.1)).choose_spec.2.2 _ _ hx).symm.trans
        ((t i.1).left_inv (hsource z hz))
  -- The exact associated inverse frame is represented in the normalized principal section.
  have hinverse (v : Fin (A.rank i.2) → ℂ) :
      (AD.frameLinearEquiv i z hz).symm v =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p (t i.1 z).2 hrep
          ((A.frameLinearEquiv i.2 (t i.1 z).2 hz').symm v) := by
    apply (AD.frameLinearEquiv i z hz).injective
    rw [LinearEquiv.apply_symm_apply]
    symm
    have heval := (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization i.1) (S.equivariant i.1) (A.chart i.2) (A.linear i.2)).choose_spec.2.2
        p (t i.1 z).2 z hrep ((A.frameLinearEquiv i.2 (t i.1 z).2 hz').symm v)
          (hp.symm ▸ hx)
    change (AD.frameLinearEquiv i z hz) _ = _ at heval
    rw [heval]
    dsimp only [p]
    rw [(S.trivialization i.1).apply_symm_apply' hx, σ.one_map]
    exact (A.frameLinearEquiv i.2 (t i.1 z).2 hz').apply_symm_apply v
  -- Its Gram entry is the same sphere Gram entry, composed with the smooth local sphere map.
  have hzAD : z ∈ ((associatedSphereSmoothBundleAtlas S A σ hσ).chart i).baseSet := hz
  simp only [Function.comp_apply, dite_eq_left hz', dite_eq_left hzAD]
  change (associatedEquivariantMetricCore S.toIsPrincipalBundle σ h z).inner
      ((AD.frameLinearEquiv i z hz).symm (Pi.single a 1))
      ((AD.frameLinearEquiv i z hz).symm (Pi.single b 1)) =
    (h.toCore (t i.1 z).2).inner
      ((A.frameLinearEquiv i.2 (t i.1 z).2 hz').symm (Pi.single a 1))
      ((A.frameLinearEquiv i.2 (t i.1 z).2 hz').symm (Pi.single b 1))
  rw [hinverse, hinverse]
  exact associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ h hInvariant
    p (t i.1 z).2 hrep _ _

end AtiyahSinger
