/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.VerticalTangentBundle
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# The vertical cotangent sequence of a smooth submersion

Public module ID: M1512.

The vertical cotangent fiber is the real continuous dual of the actual kernel
of the differential. Restriction of covectors to this kernel has kernel exactly
the range of the original cotangent pullback. Thus the quotient appearing in
SG III.13, p.251, is the vertical cotangent space, not the vertical tangent
space without an additional metric identification.

All maps below retain the original tangent and subspace topologies. The native
Hom-bundle construction gives the dual bundle when the selected vertical atlas
is installed. Exactness is the standard finite-dimensional dual exact sequence,
applied to the actual derivative in submersion normal-form charts. It is a
project supplement to the notation in SG, not a separately numbered SG lemma.
The fiberwise exactness proof is given below; global atlas and splitting results are separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

section Fibers

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

/-- The vertical cotangent fiber is the continuous dual of the original vertical tangent fiber. -/
abbrev VerticalCotangentFiber (f : M → N) (x : M) : Type _ :=
  VerticalTangentFiber 𝓘(ℝ, E) 𝓘(ℝ, F) f x →L[ℝ] ℝ

/-- Cotangent pullback at a point is precomposition with the actual manifold derivative. -/
def submersionCotangentPullback (f : M → N) (x : M) :
    (TangentSpace 𝓘(ℝ, F) (f x) →L[ℝ] ℝ) →ₗ[ℝ]
      (TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) :=
  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).lcomp ℝ

/-- Restriction to the actual kernel of the derivative, with its original subspace topology. -/
def verticalCotangentRestriction (f : M → N) (x : M) :
    (TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) →ₗ[ℝ] VerticalCotangentFiber (E := E) (F := F) f x :=
  (LinearMap.ker (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).subtypeL.lcomp ℝ

end Fibers

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- The original cotangent pullback and vertical restriction form the short exact sequence. -/
theorem submersion_cotangent_exact
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : Manifold.IsSubmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (x : M) :
    Function.Injective (submersionCotangentPullback (E := E) (F := F) f x) ∧
      Function.Surjective (verticalCotangentRestriction (E := E) (F := F) f x) ∧
        LinearMap.range (submersionCotangentPullback (E := E) (F := F) f x) =
          LinearMap.ker (verticalCotangentRestriction (E := E) (F := F) f x) := by
  /- Stage 1: differentiate a submersion normal form at x. The original
  derivative is conjugate by invertible chart derivatives to the first
  projection, hence is surjective. The proof derives this consequence
  directly from the supplied normal-form equation.
  Stage 2: precomposition with that surjective derivative is injective.
  A covector in its range vanishes on the actual derivative kernel. Conversely,
  a covector vanishing there factors uniquely through the derivative quotient,
  giving a covector on the original target tangent space.
  Stage 3: extend a linear functional on the kernel to the whole tangent
  space using any finite-dimensional linear complement at this one point.
  All these linear maps are continuous for the original finite-dimensional
  topologies, so restriction is surjective on continuous duals as stated.
  This identifies T*M / range(df*) with (ker df)* by the first isomorphism
  theorem. No metric identifies this dual with ker df in this statement;
  no global complement, compactness or separation of M or N is required. -/
  classical
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let L : E →L[ℝ] F := mfderiv I J f x
  -- Differentiate the supplied normal form, rather than assuming derivative surjectivity.
  have hsurj : Function.Surjective L := by
    let h := hf.isSubmersionAt x
    have hdomAtlas : h.domChart ∈ IsManifold.maximalAtlas I 1 M :=
      IsManifold.maximalAtlas_subset_of_le (by simp) h.domChart_mem_maximalAtlas
    have hcodAtlas : h.codChart ∈ IsManifold.maximalAtlas J 1 N :=
      IsManifold.maximalAtlas_subset_of_le (by simp) h.codChart_mem_maximalAtlas
    have hdom : h.domChart.MDifferentiable I I :=
      ⟨fun y hy ↦ (mdifferentiableAt_of_mem_maximalAtlas hdomAtlas hy).mdifferentiableWithinAt,
        fun y hy ↦
          (mdifferentiableAt_symm_of_mem_maximalAtlas hdomAtlas hy).mdifferentiableWithinAt⟩
    have hcod : h.codChart.MDifferentiable J J :=
      ⟨fun y hy ↦ (mdifferentiableAt_of_mem_maximalAtlas hcodAtlas hy).mdifferentiableWithinAt,
        fun y hy ↦
          (mdifferentiableAt_symm_of_mem_maximalAtlas hcodAtlas hy).mdifferentiableWithinAt⟩
    let P : E →L[ℝ] F :=
      (ContinuousLinearMap.fst ℝ F h.complement).comp h.equiv.toContinuousLinearMap
    have hnormal : (h.codChart ∘ f ∘ h.domChart.symm) =ᶠ[𝓝 (h.domChart x)] P := by
      filter_upwards [h.domChart.open_target.mem_nhds
        (h.domChart.map_source h.mem_domChart_source)] with y hy
      exact h.writtenInCharts (by simpa [OpenPartialHomeomorph.extend_target] using hy)
    have hderiv : mfderiv I J (h.codChart ∘ f ∘ h.domChart.symm) (h.domChart x) = P := by
      rw [hnormal.mfderiv_eq, mfderiv_eq_fderiv]
      exact P.fderiv
    have hreturn : h.domChart.symm (h.domChart x) = x :=
      h.domChart.left_inv h.mem_domChart_source
    have hfirst := mfderiv_comp (h.domChart x)
      (f.contMDiff.mdifferentiable (by simp) (h.domChart.symm (h.domChart x)))
      (hdom.mdifferentiableAt_symm (h.domChart.map_source h.mem_domChart_source))
    have hsecond := mfderiv_comp (h.domChart x)
      (hcod.mdifferentiableAt (h.source_subset_preimage_source
        (h.domChart.map_target (h.domChart.map_source h.mem_domChart_source))))
      ((f.contMDiff.mdifferentiable (by simp)
        (h.domChart.symm (h.domChart x))).comp (h.domChart x)
        (hdom.mdifferentiableAt_symm (h.domChart.map_source h.mem_domChart_source)))
    rw [hderiv, hfirst] at hsecond
    simp only [Function.comp_apply] at hsecond
    -- The normal projection is onto, and the target chart derivative is injective.
    intro w
    let v := h.equiv.symm ((mfderiv J J h.codChart (f x)) w, 0)
    refine ⟨(mfderiv I I h.domChart.symm (h.domChart x)) v, ?_⟩
    apply hcod.mfderiv_injective h.mem_codChart_source
    have hv := congrArg (fun T : E →L[ℝ] F ↦ T v) hsecond
    have hPv : P v = (mfderiv J J h.codChart (f x)) w := by
      change (h.equiv (h.equiv.symm _)).1 = _
      rw [h.equiv.apply_symm_apply]
    change P v = (mfderiv J J h.codChart (f (h.domChart.symm (h.domChart x))))
      ((mfderiv I J f (h.domChart.symm (h.domChart x)))
        ((mfderiv I I h.domChart.symm (h.domChart x)) v)) at hv
    rw [hreturn] at hv
    exact hv.symm.trans hPv
  -- Work in the original tangent models; no topology or bundle map is replaced.
  change Function.Injective (L.lcomp ℝ) ∧
    Function.Surjective ((LinearMap.ker L.toLinearMap).subtypeL.lcomp ℝ) ∧
      LinearMap.range (L.lcomp ℝ) =
        LinearMap.ker ((LinearMap.ker L.toLinearMap).subtypeL.lcomp ℝ)
  -- Pullback along this surjective derivative is injective on the original continuous dual.
  refine ⟨?_, ?_, ?_⟩
  · intro α β hαβ
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := hsurj w
    exact congrArg (fun γ : E →L[ℝ] ℝ ↦ γ v) hαβ
  · -- Extend a linear functional from the kernel; finite dimension ensures continuity.
    intro α
    obtain ⟨β, hβ⟩ := α.toLinearMap.exists_extend
    refine ⟨β.toContinuousLinearMap, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun γ ↦ γ v) hβ
  · -- A functional annihilating the kernel factors through a right inverse of the derivative.
    obtain ⟨s, hs⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
    apply le_antisymm
    · rintro ξ ⟨α, rfl⟩
      apply ContinuousLinearMap.ext
      intro v
      change α (L v.val) = 0
      rw [show L v.val = 0 from v.property, map_zero]
    · intro ξ hξ
      refine ⟨ξ.comp s, ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      have hker : L (v - s (L v)) = 0 := by
        rw [map_sub]
        have hv := congrArg (fun T : F →L[ℝ] F ↦ T (L v)) hs
        exact sub_eq_zero.mpr hv.symm
      have hzero : ξ (v - s (L v)) = 0 :=
        congrArg (fun γ : LinearMap.ker L.toLinearMap →L[ℝ] ℝ ↦
          γ ⟨v - s (L v), hker⟩) hξ
      change ξ (s (L v)) = ξ v
      exact (sub_eq_zero.mp (by simpa only [map_sub] using hzero)).symm

end AtiyahSinger
