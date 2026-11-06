/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParacompactSmoothSelection
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Smooth varying radii inside a bundle neighborhood

Public module ID: M1117.

An open neighborhood of the entire zero section in a continuous Riemannian
vector bundle contains a disk bundle with positive smooth varying radius.
Only the finite-dimensional base manifold is assumed Hausdorff and paracompact;
there is no compactness assumption and no uniform radius assertion.

The proof uses boundedness of the original frame in the continuous metric and
a smooth selection from the convex intervals of admissible positive radii.
This is the standard varying-radius step in noncompact tubular constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology
open scoped ContDiff Manifold

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B] [T2Space B] [ParacompactSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContinuousRiemannianBundle F V]

/-- A neighborhood of the whole zero section contains a positive smooth varying-radius disk. -/
theorem exists_contMDiff_radius_subset {U : Set (TotalSpace F V)} (hU : IsOpen U)
    (hzero : ∀ x : B, (⟨x, 0⟩ : TotalSpace F V) ∈ U) :
    ∃ ε : ContMDiffMap 𝓘(ℝ, EB) 𝓘(ℝ) B ℝ ∞,
      (∀ x, 0 < ε x) ∧ ∀ (x : B) (v : V x), ‖v‖ < ε x → (⟨x, v⟩ : TotalSpace F V) ∈ U := by
  let t (x : B) : Set ℝ := {r | 0 < r ∧ ∀ v : V x, ‖v‖ < r →
    (⟨x, v⟩ : TotalSpace F V) ∈ U}
  have ht (x : B) : Convex ℝ (t x) := by
    apply Set.OrdConnected.convex
    constructor
    intro a ha b hb r hr
    exact ⟨ha.1.trans_le hr.1, fun v hv ↦ hb.2 v (hv.trans_le hr.2)⟩
  have hlocal (x : B) : ∃ r : ℝ, ∀ᶠ y in 𝓝 x, r ∈ t y := by
    let e := trivializationAt F V x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
    -- One original frame supplies a uniform small coordinate ball on a base neighborhood.
    have hi : ContinuousAt (fun p : B × F ↦
        (⟨p.1, e.symm p.1 p.2⟩ : TotalSpace F V)) (x, 0) :=
      e.continuousOn_symm.continuousAt
        ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)
    have hz : e.symm x (0 : F) = 0 := by
      rw [← e.symmL_apply (R := ℝ) hx, map_zero]
    have hpre : (fun p : B × F ↦ (⟨p.1, e.symm p.1 p.2⟩ : TotalSpace F V)) ⁻¹' U ∈
        𝓝 (x, (0 : F)) := hi (by simpa only [hz] using hU.mem_nhds (hzero x))
    obtain ⟨W, hW, A, hA, hWA⟩ := mem_nhds_prod_iff.mp hpre
    obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.mp hA
    obtain ⟨C, hC, hbound⟩ := eventually_norm_trivializationAt_lt F V x
    refine ⟨r / C, ?_⟩
    filter_upwards [hW, e.open_baseSet.mem_nhds hx, hbound] with y hy hye hyC
    refine ⟨div_pos hr hC, fun v hv ↦ ?_⟩
    have hnorm : ‖e.continuousLinearMapAt ℝ y v‖ < r := by
      calc
        ‖e.continuousLinearMapAt ℝ y v‖ ≤ ‖e.continuousLinearMapAt ℝ y‖ * ‖v‖ :=
          (e.continuousLinearMapAt ℝ y).le_opNorm v
        _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right hyC.le (norm_nonneg v)
        _ < r := by simpa only [mul_comm] using (lt_div_iff₀ hC).mp hv
    have hAcoord : e.continuousLinearMapAt ℝ y v ∈ A :=
      hrA (by simpa only [Metric.mem_ball, dist_zero_right] using hnorm)
    have hmem := hWA (show (y, e.continuousLinearMapAt ℝ y v) ∈ W ×ˢ A from ⟨hy, hAcoord⟩)
    have hinv : e.symm y (e.continuousLinearMapAt ℝ y v) = v := by
      rw [← e.symmL_apply (R := ℝ) hye, e.symmL_continuousLinearMapAt (R := ℝ) hye]
    simpa only [mem_preimage, hinv] using hmem
  obtain ⟨ε, hε⟩ := exists_contMDiffMap_mem_convex_of_paracompact (EB := EB) t ht hlocal
  exact ⟨ε, fun x ↦ (hε x).1, fun x v hv ↦ (hε x).2 v hv⟩

end AtiyahSinger
