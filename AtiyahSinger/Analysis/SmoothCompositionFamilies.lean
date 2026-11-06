/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Derivative continuity for smooth composition families

Public module ID: M0965.

Evaluation of every Schwartz derivative is jointly continuous in the function
and the point. The parameterized chain rule then preserves joint continuity of
all finite derivatives. These criteria use the original Schwartz topology and
allow an arbitrary topological parameter space. They are used for geometric
changes of variables in the topology of smooth sections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold Set Topology
open scoped BoundedContinuousFunction ContDiff Manifold SchwartzMap

/-- Evaluating any finite derivative is jointly continuous on Schwartz space times its domain. -/
theorem continuous_iteratedFDeriv_schwartz
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) :
    Continuous (fun p : SchwartzMap X F × X ↦ iteratedFDeriv ℝ k p.1 p.2) := by
  -- The k-th derivative is a bounded continuous function controlled by one Schwartz seminorm.
  let D (f : SchwartzMap X F) : X →ᵇ (X [×k]→L[ℝ] F) :=
    BoundedContinuousFunction.ofNormedAddCommGroup (iteratedFDeriv ℝ k f)
      (f.smooth ⊤ |>.continuous_iteratedFDeriv (by simp))
      (SchwartzMap.seminorm ℝ 0 k f) (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f k)
  let T : SchwartzMap X F →L[ℝ] X →ᵇ (X [×k]→L[ℝ] F) :=
    SchwartzMap.mkCLMtoNormedSpace D
      (fun f g ↦ by
        apply BoundedContinuousFunction.ext
        intro x
        exact iteratedFDeriv_add_apply (f.smooth k |>.contDiffAt)
          (g.smooth k |>.contDiffAt))
      (fun c f ↦ by
        apply BoundedContinuousFunction.ext
        intro x
        exact iteratedFDeriv_const_smul_apply (f.smooth k |>.contDiffAt))
      ⟨{(0, k)}, 1, zero_le_one, fun f ↦ by
        rw [Finset.sup_singleton, one_mul]
        apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
        exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f k⟩
  -- Bounded-continuous evaluation varies continuously in both its arguments.
  exact continuous_eval.comp ((T.continuous.comp continuous_fst).prodMk continuous_snd)

/-- The parameterized chain rule preserves joint continuity of every finite derivative. -/
theorem continuousOn_iteratedFDeriv_comp_family
    {Z X Y F : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Z → Y → F) (g : Z → X → Y) (s : Set (Z × X))
    (hf : ∀ p ∈ s, ContDiffAt ℝ ∞ (f p.1) (g p.1 p.2))
    (hg : ∀ p ∈ s, ContDiffAt ℝ ∞ (g p.1) p.2)
    (hdf : ∀ k : ℕ, ContinuousOn (fun p ↦ iteratedFDeriv ℝ k (f p.1) (g p.1 p.2)) s)
    (hdg : ∀ k : ℕ, ContinuousOn (fun p ↦ iteratedFDeriv ℝ k (g p.1) p.2) s)
    (k : ℕ) :
    ContinuousOn (fun p ↦ iteratedFDeriv ℝ k ((f p.1) ∘ (g p.1)) p.2) s := by
  -- Each term in the finite chain rule is a continuous multilinear composition of jets.
  have hsum : ContinuousOn (fun p : Z × X ↦
      (ftaylorSeries ℝ (f p.1) (g p.1 p.2)).taylorComp
        (ftaylorSeries ℝ (g p.1) p.2) k) s := by
    apply continuousOn_finsetSum
    intro c _
    let B := c.compAlongOrderedFinpartitionL ℝ X Y F
    change ContinuousOn (fun p : Z × X ↦
      B (iteratedFDeriv ℝ c.length (f p.1) (g p.1 p.2))
        (fun i ↦ iteratedFDeriv ℝ (c.partSize i) (g p.1) p.2)) s
    exact B.continuous_uncurry_of_multilinear.comp_continuousOn
      ((hdf c.length).prodMk (continuousOn_pi.mpr (fun i ↦ hdg (c.partSize i))))
  apply hsum.congr
  intro p hp
  exact iteratedFDeriv_comp (hf p hp) (hg p hp) (by simp)

universe u

/-- Differentiating only the vector-space variable preserves joint manifold smoothness. -/
theorem contMDiffOn_iteratedFDeriv_parameter
    {V HG Y : Type*} {X F : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace HG] (I : ModelWithCorners ℝ V HG)
    [TopologicalSpace Y] [ChartedSpace HG Y] [IsManifold I ∞ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Y × X → F} {s : Set (Y × X)} (hs : IsOpen s)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, F) ∞ f s) (k : ℕ) :
    ContMDiffOn (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, X [×k]→L[ℝ] F) ∞
      (fun p ↦ iteratedFDeriv ℝ k (fun x ↦ f (p.1, x)) p.2) s := by
  have hpartial {A : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
      {g : Y × X → A}
      (hg : ContMDiffOn (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, A) ∞ g s) :
      ContMDiffOn (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, X →L[ℝ] A) ∞
        (fun p ↦ fderiv ℝ (fun x ↦ g (p.1, x)) p.2) s := by
    intro p hp
    have hlocal := (hg p hp).contMDiffAt (hs.mem_nhds hp)
    have hcomp : ContMDiffAt ((I.prod 𝓘(ℝ, X)).prod 𝓘(ℝ, X)) 𝓘(ℝ, A) ∞
        (fun q : (Y × X) × X ↦ g (q.1.1, q.2)) (p, p.2) :=
      hlocal.comp_of_eq (contMDiffAt_fst.fst.prodMk contMDiffAt_snd) rfl
    have hd := hcomp.mfderiv (m := ∞) (fun q : Y × X ↦ fun x : X ↦ g (q.1, x))
      (fun q : Y × X ↦ q.2) contMDiffAt_snd (by simp)
    have heq : inTangentCoordinates 𝓘(ℝ, X) 𝓘(ℝ, A)
        (fun q : Y × X ↦ q.2) (fun q ↦ g (q.1, q.2))
        (fun q ↦ mfderiv 𝓘(ℝ, X) 𝓘(ℝ, A) (fun x ↦ g (q.1, x)) q.2) p =
        (fun q : Y × X ↦ fderiv ℝ (fun x ↦ g (q.1, x)) q.2) := by
      funext q
      simp only [mfderiv_eq_fderiv]
      unfold inTangentCoordinates
      erw [inCoordinates_tangent_bundle_core_model_space]
      rfl
    rw [heq] at hd
    exact hd.contMDiffWithinAt
  -- Iterate the partial derivative, retaining the original manifold parameter throughout.
  induction k with
  | zero =>
    exact (((continuousMultilinearCurryFin0 ℝ X F).symm :
      F →L[ℝ] X [×0]→L[ℝ] F).contMDiff).comp_contMDiffOn hf
  | succ k ih =>
    have hd := hpartial ih
    let hL := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) F).symm
    rw [show (fun p : Y × X ↦
        iteratedFDeriv ℝ (k + 1) (fun x ↦ f (p.1, x)) p.2) =
        fun p ↦ hL (fderiv ℝ (fun x ↦
          iteratedFDeriv ℝ k (fun y ↦ f (p.1, y)) x) p.2) from by
      funext p
      exact congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ)
        (f := fun x ↦ f (p.1, x))) p.2]
    convert (hL : (X →L[ℝ] X [×k]→L[ℝ] F) →L[ℝ]
      X [×(k + 1)]→L[ℝ] F).contMDiff.comp_contMDiffOn hd using 1
    rfl

end AtiyahSinger
