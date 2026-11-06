/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactEuclideanEmbedding
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The inverse-function criterion in full charts with finite-dimensional source

Public module ID: M1235.

A smooth map from a finite-dimensional full-model manifold whose actual
differential is invertible at every point is a local diffeomorphism. The smooth
inverse-function theorem is applied in the original maximal charts, and its
inverse is smooth on the whole open target. This supplies actual local inverse
charts, not only an injective differential or a topological local homeomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option maxHeartbeats 800000 in
-- Retain the actual manifold charts and restrict to their common inverse-function domain.
set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ F] in
/-- Invertible differentials in full charts with finite-dimensional source give local
diffeomorphisms. -/
theorem isLocalDiffeomorph_of_isInvertible_mfderiv
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : ∀ x : M, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  intro x
  let φ := chartAt E x
  let ψ := chartAt F (f x)
  let a := φ x
  let g : E → F := ψ ∘ f ∘ φ.symm
  let Ω : Set E := φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source)
  have hΩ : IsOpen Ω :=
    φ.isOpen_inter_preimage_symm (ψ.open_source.preimage f.contMDiff.continuous)
  have haΩ : a ∈ Ω := by simp [Ω, a, φ, ψ]
  have hg : ContDiffOn ℝ ∞ g Ω := by
    apply ContMDiffOn.contDiffOn
    apply (contMDiffOn_chart (I := 𝓘(ℝ, F)) (x := f x)).comp
    · exact f.contMDiff.comp_contMDiffOn
        ((contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).mono (fun y hy ↦ hy.1))
    · intro y hy
      exact hy.2
  have hga : ContDiffAt ℝ ∞ g a := hg.contDiffAt (hΩ.mem_nhds haΩ)
  have heq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x = fderiv ℝ g a := by
    have hd := (f.contMDiff x).mdifferentiableAt (by simp)
    simp only [mfderiv, hd, ↓reduceIte, writtenInExtChartAt, mfld_simps,
      fderivWithin_univ]
    rfl
  have hbij : Function.Bijective (fderiv ℝ g a) := by
    rw [← heq]
    exact (hf x).bijective
  let e : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ g a).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt g (e : E →L[ℝ] F) a := by
    exact (hga.differentiableAt (by simp)).hasFDerivAt
  -- Restrict the inverse-function chart so every derivative on its source is invertible.
  let U : Set E := Ω ∩ {u | (fderiv ℝ g u).IsInvertible}
  have hU : IsOpen U :=
    (hg.continuousOn_fderiv_of_isOpen hΩ (by simp)).isOpen_inter_preimage hΩ
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let H₀ := hga.toOpenPartialHomeomorph g hd (by simp)
  let H := H₀.restr U
  have hHU : H.source ⊆ U := by
    intro y hy
    exact hU.interior_eq ▸ hy.2
  have haH : a ∈ H.source := by
    refine ⟨hga.mem_toOpenPartialHomeomorph_source hd (by simp), ?_⟩
    rw [hU.interior_eq]
    exact ⟨haΩ, ⟨e, hd.fderiv.symm⟩⟩
  have hHcd : ContDiffOn ℝ ∞ H H.source := hg.mono (fun y hy ↦ (hHU hy).1)
  have hHinv : ContDiffOn ℝ ∞ H.symm H.target := by
    intro y hy
    have hp := hHU (H.map_target hy)
    have hgp : ContDiffAt ℝ ∞ g (H.symm y) := hg.contDiffAt (hΩ.mem_nhds hp.1)
    obtain ⟨d, hd'⟩ := hp.2
    have hder : HasFDerivAt H (d : E →L[ℝ] F) (H.symm y) := by
      change HasFDerivAt g _ _
      rw [hd']
      exact (hgp.differentiableAt (by simp)).hasFDerivAt
    exact (H.contDiffAt_symm hy hder hgp).contDiffWithinAt
  let A : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := φ.toPartialEquiv
      open_source := φ.open_source
      open_target := φ.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let B : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ :=
    { toPartialEquiv := H.toPartialEquiv
      open_source := H.open_source
      open_target := H.open_target
      contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.mpr hHcd
      contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.mpr hHinv }
  let C : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) N F ∞ :=
    { toPartialEquiv := ψ.toPartialEquiv
      open_source := ψ.open_source
      open_target := ψ.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let D := (A.trans B).trans C.symm
  have hxD : x ∈ D.source := by
    refine ⟨⟨mem_chart_source E x, haH⟩, ?_⟩
    change g (φ x) ∈ ψ.target
    have hx : φ.symm (φ x) = x := φ.left_inv (mem_chart_source E x)
    change ψ (f (φ.symm (φ x))) ∈ ψ.target
    rw [hx]
    exact ψ.map_source (mem_chart_source F (f x))
  have hD (y : M) (hy : y ∈ D.source) : f y = D y := by
    change f y = ψ.symm (g (φ y))
    have hφ : φ.symm (φ y) = y := φ.left_inv hy.1.1
    have hψ : f y ∈ ψ.source := by
      have h := (hHU hy.1.2).1.2
      change f (φ.symm (φ y)) ∈ ψ.source at h
      rwa [hφ] at h
    change f y = ψ.symm (ψ (f (φ.symm (φ y))))
    rw [hφ, ψ.left_inv hψ]
  -- Keep f itself as the forward map, with the inverse from these same original charts.
  let Df : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞ :=
    { toFun := f
      invFun := D.toPartialEquiv.symm
      source := D.source
      target := D.target
      map_source' := fun y hy ↦ (hD y hy).symm ▸ D.toPartialEquiv.map_source hy
      map_target' := fun _ hy ↦ D.toPartialEquiv.map_target hy
      left_inv' := fun y hy ↦ (congrArg D.toPartialEquiv.symm (hD y hy)).trans
        (D.toPartialEquiv.left_inv hy)
      right_inv' := fun y hy ↦ (hD _ (D.toPartialEquiv.map_target hy)).trans
        (D.toPartialEquiv.right_inv hy)
      open_source := D.open_source
      open_target := D.open_target
      contMDiffOn_toFun := f.contMDiff.contMDiffOn
      contMDiffOn_invFun := D.contMDiffOn_invFun }
  exact Df.isLocalDiffeomorphAt _ _ _ hxD

end AtiyahSinger
