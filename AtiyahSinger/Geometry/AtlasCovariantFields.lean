/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasComplexConnection
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Covariant derivatives along smooth tangent fields in a prescribed atlas

Public module ID: M1093.

The given atlas connection sends a smooth section and a smooth tangent field to
another smooth section of the same original bundle. Iterating this operation
with all old-slot corrections gives the usual full covariant tensor derivative
on smooth fields. No fixed bundle rank, fiber norm, or compactness is required.
These are the intrinsic operations underlying SG III.2 (2.1).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "H" => EuclideanSpace ℝ (Fin n)
local notation "MI" => 𝓘(ℝ, H)
local notation "TM" => TangentSpace MI (M := M)
local notation "𝓧" => ContMDiffSection MI H ∞ TM

variable {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {A : SmoothComplexBundleAtlas (n := n) E}

namespace AtlasComplexConnection

set_option backward.isDefEq.respectTransparency false in
/-- The original connection evaluated on a smooth tangent field is a smooth atlas section. -/
theorem isSmoothSection_covariantDerivative (cov : AtlasComplexConnection A)
    (u : A.smoothSections) (X : 𝓧) :
    A.IsSmoothSection (fun x ↦ cov.covariantDerivative u x (X x)) := by
  intro i x hx
  let c := chartAt H x
  have hc : c ∈ atlas H M := chart_mem_atlas H x
  have hxc : x ∈ c.source := mem_chart_source H x
  let t : Trivialization H (π H TM) := (tangentBundleCore MI M).localTriv ⟨c, hc⟩
  let : MemTrivializationAtlas t := ⟨⟨⟨c, hc⟩, rfl⟩⟩
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let e := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  let f : H → V := atlasSectionInChart A c i u.val
  let Xc : M → H := fun y ↦ (t ⟨y, X y⟩).2
  -- The section and tangent field are smooth in these exact original coordinates.
  have hchart : ContMDiffAt MI MI ∞ c x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hxc
  have hsymm : ContMDiffAt MI MI ∞ c.symm (c x) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
      (c.map_source hxc)
  have hcoord : ContMDiffAt MI 𝓘(ℝ, V) ∞
      (fun y ↦ e.symm (A.chart i ⟨y, u.val y⟩).2) x :=
    (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.contMDiffAt.comp x
      ((u.property i).contMDiffAt ((A.chart i).open_baseSet.mem_nhds hx))
  have hf : ContDiffAt ℝ ∞ f (c x) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact hcoord.comp_of_eq hsymm (c.left_inv hxc)
  have hXc : ContMDiffAt MI MI ∞ Xc x :=
    (t.contMDiffAt_section_iff hxc).mp X.contMDiff.contMDiffAt
  have hdomain : c.target ∩ c.symm ⁻¹' (A.chart i).baseSet ∈ nhds (c x) := by
    apply Filter.inter_mem (c.open_target.mem_nhds (c.map_source hxc))
    apply hsymm.continuousAt.preimage_mem_nhds
    rw [c.left_inv hxc]
    exact (A.chart i).open_baseSet.mem_nhds hx
  have hΓ : ContDiffAt ℝ ∞ (cov.connectionForm c i) (c x) :=
    (cov.smooth_connectionForm c hc i).contDiffAt hdomain
  -- Both the differentiated section and the connection correction are smooth.
  have hdu := ((hf.fderiv_right (by simp)).contMDiffAt.comp x hchart).clm_apply hXc
  let R := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have hΓX := (hΓ.contMDiffAt.comp x hchart).clm_apply hXc
  have hconnection := (R.contMDiff.contMDiffAt.comp x hΓX).clm_apply
    (hf.contMDiffAt.comp x hchart)
  have hformula : ContMDiffAt MI 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
      (fun y ↦ e (fderiv ℝ f (c y) (Xc y) +
        cov.connectionForm c i (c y) (Xc y) (f (c y)))) x :=
    (e.toContinuousLinearMap.restrictScalars ℝ).contMDiff.contMDiffAt.comp x
      (hdu.add hconnection)
  apply ContMDiffAt.contMDiffWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hxc, (A.chart i).open_baseSet.mem_nhds hx]
    with y hyc hyi
  -- The same tangent trivialization is the actual derivative of the chosen base chart.
  have hderiv : mfderiv MI MI c y = t.continuousLinearMapAt ℝ y := by
    rw [(tangentBundleCore MI M).localTriv_continuousLinearMapAt
      (show y ∈ t.baseSet from hyc)]
    rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas hc hyc)]
    rfl
  have hvector : mfderiv MI MI c y (X y) = Xc y := by
    rw [hderiv]
    exact t.continuousLinearMapAt_apply_of_mem ℝ hyc (X y)
  rw [cov.covariantDerivative_eq u c hc i y ⟨hyc, hyi⟩ (X y)]
  change A.frameLinearEquiv i y hyi
    ((A.frameLinearEquiv i y hyi).symm
      (e (fderiv ℝ f (c y) (mfderiv MI MI c y (X y)) +
        cov.connectionForm c i (c y) (mfderiv MI MI c y (X y)) (f (c y))))) = _
  rw [LinearEquiv.apply_symm_apply, hvector]

/-- The supplied connection differentiates an original smooth section along a smooth field. -/
def directionalDerivative (cov : AtlasComplexConnection A)
    (u : A.smoothSections) (X : 𝓧) : A.smoothSections :=
  ⟨fun x ↦ cov.covariantDerivative u x (X x),
    cov.isSmoothSection_covariantDerivative u X⟩

end AtlasComplexConnection

/-- The supplied smooth tangent connection differentiates one smooth tangent field along another. -/
def smoothTangentCovariantDerivative
    (covT : CovariantDerivative MI H TM) (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (X Y : 𝓧) : 𝓧 where
  toFun := fun x ↦ covT Y x (X x)
  contMDiff_toFun := by
    have hY := hcovT.contMDiff.contMDiff (by simpa using Y.contMDiff.contMDiffOn)
    exact (contMDiffOn_univ.mp hY).clm_bundle_apply X.contMDiff

namespace AtlasComplexConnection

/-- The full covariant derivative evaluated on smooth fields, with every old-slot correction.
The value remains a smooth section of the original varying-rank atlas. -/
def iteratedDirectionalDerivative (cov : AtlasComplexConnection A)
    (covT : CovariantDerivative MI H TM) (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (u : A.smoothSections) : (k : ℕ) → (Fin k → 𝓧) → A.smoothSections
  | 0, _ => u
  | k + 1, X =>
    cov.directionalDerivative (cov.iteratedDirectionalDerivative covT hcovT u k (Fin.tail X))
        (X 0) -
      ∑ a : Fin k, cov.iteratedDirectionalDerivative covT hcovT u k
        (Function.update (Fin.tail X) a
          (smoothTangentCovariantDerivative covT hcovT (X 0) (X a.succ)))

end AtlasComplexConnection

end AtiyahSinger
