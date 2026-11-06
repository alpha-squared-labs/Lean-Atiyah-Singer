/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame

/-!
# Local frame detection of smooth sections

Public module ID: M1098.

Smoothness in one original covering frame at each point implies smoothness
in every chart of the same atlas. The transition columns reconstruct the
actual coordinate function. The local frame may vary with the point, and
ranks on unrelated components need not agree.

This local criterion permits the normalized principal-chart extension to
be checked before returning to all charts of the prescribed tensor atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] (A : SmoothComplexBundleAtlas (n := n) E)

/-- A section is smooth if one original covering frame detects smoothness at each point. -/
theorem isSmoothSection_of_locally (u : ∀ x : M, E x)
    (h : ∀ x : M, ∃ i : A.Index, x ∈ (A.chart i).baseSet ∧
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun y ↦ (A.chart i ⟨y, u y⟩).2) x) : A.IsSmoothSection u := by
  classical
  intro j x hx
  obtain ⟨i, hix, hs⟩ := h x
  -- Original transition columns express all target coordinates as a finite smooth sum.
  have hsum : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
      (fun y ↦ ∑ k : Fin (A.rank i), (A.chart i ⟨y, u y⟩).2 k •
        (A.chart j ((A.chart i).toPartialEquiv.symm (y, Pi.single k 1))).2) x := by
    apply contMDiffAt_finsetSum
    intro k _
    have hcoeff := contMDiffAt_pi_space.mp hs k
    have hcolumn := (A.contMDiffOn_coordChange i j k).contMDiffAt
      (((A.chart i).open_baseSet.inter (A.chart j).open_baseSet).mem_nhds ⟨hix, hx⟩)
    have hmul : ContDiff ℝ ∞ (fun z : ℂ × (Fin (A.rank j) → ℂ) ↦ z.1 • z.2) :=
      contDiff_smul
    exact hmul.contMDiff.contMDiffAt.comp x (hcoeff.prodMk_space hcolumn)
  apply (hsum.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(A.chart i).open_baseSet.mem_nhds hix,
    (A.chart j).open_baseSet.mem_nhds hx] with y hyi hyj
  let ei := A.frameLinearEquiv i y hyi
  let ej := A.frameLinearEquiv j y hyj
  have hcol (k : Fin (A.rank i)) :
      (A.chart j ⟨y, ei.symm (Pi.single k 1)⟩).2 =
        (A.chart j ((A.chart i).toPartialEquiv.symm (y, Pi.single k 1))).2 := by
    apply congrArg (fun z : TotalSpace Unit E ↦ (A.chart j z).2)
    exact TotalSpace.mk_cast (F := Unit) (E := E)
      ((A.chart i).proj_symm_apply' hyi)
      ((A.chart i).toOpenPartialHomeomorph.symm (y, Pi.single k 1)).2
  have hu := congrArg (fun v : Fin (A.rank i) → ℂ ↦ ej (ei.symm v))
    ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr (ei (u y)))
  simp only [map_sum, map_smul, LinearEquiv.symm_apply_apply, Pi.basisFun_repr] at hu
  change ej (u y) = _
  have hsum' : (∑ k, ei (u y) k • ej (ei.symm (Pi.single k 1))) = ej (u y) := by
    simpa only [Pi.basisFun_apply] using hu
  exact hsum'.symm.trans (Finset.sum_congr rfl (fun k _ ↦ congrArg (_ • ·) (hcol k)))

end AtiyahSinger.SmoothComplexBundleAtlas
