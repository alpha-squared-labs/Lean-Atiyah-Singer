/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Inverse function foundations for smooth local additions

Public module ID: M1299.

The inverse function theorem for boundaryless real manifolds with a complete
source model turns normalized local subtraction maps into local additions
and tubular coordinates. The local inverse comes from conjugating the
normed-space inverse function theorem by the original charts.

Smoothness is assumed on an open neighborhood. The germ definition of
`ContMDiffAt` at infinite order, at just one point, does not assert smoothness
on a fixed neighborhood. Boundaryless models include the product and tangent-
bundle models and need not be definitionally identical to the normed model.
No compactness, properness, Hausdorffness or countability is needed here.

Source: the usual chart proof of the smooth inverse function theorem; compare
HU XVIII.2, printed p.265. The normed-space theorem is supplied by mathlib.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold Set Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The smooth inverse function theorem in the original boundaryless manifold models.
The partial diffeomorphism agrees with the original map everywhere, and its source lies in the
specified open neighborhood. The complete source model includes every finite-dimensional case. -/
theorem exists_partialDiffeomorph_of_isInvertible_mfderiv {f : M → N} {s : Set M} {x : M}
    (hf : ContMDiffOn I J ∞ f s) (hs : IsOpen s) (hx : x ∈ s)
    (hd : (mfderiv I J f x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph I J M N ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ s ∧ (Φ : M → N) = f := by
  classical
  -- Pass to the original charts, retaining the open set where all compositions are valid.
  let φ : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I x
      open_source := isOpen_extChartAt_source (I := I) x
      open_target := isOpen_extChartAt_target x
      continuousOn_toFun := continuousOn_extChartAt x
      continuousOn_invFun := continuousOn_extChartAt_symm x }
  let ψ : OpenPartialHomeomorph N F :=
    { toPartialEquiv := extChartAt J (f x)
      open_source := isOpen_extChartAt_source (I := J) (f x)
      open_target := isOpen_extChartAt_target (f x)
      continuousOn_toFun := continuousOn_extChartAt (f x)
      continuousOn_invFun := continuousOn_extChartAt_symm (f x) }
  have hψsmooth : ContMDiffOn J 𝓘(ℝ, F) ∞ ψ ψ.source := by
    change ContMDiffOn J 𝓘(ℝ, F) ∞ (extChartAt J (f x)) (extChartAt J (f x)).source
    simpa only [extChartAt_source] using (contMDiffOn_extChartAt (I := J) (x := f x))
  let a : E := φ x
  let g : E → F := ψ ∘ f ∘ φ.symm
  let Ω : Set E := φ.target ∩ φ.symm ⁻¹' (s ∩ f ⁻¹' ψ.source)
  have hΩ : IsOpen Ω :=
    φ.isOpen_inter_preimage_symm
      (hf.continuousOn.isOpen_inter_preimage hs ψ.open_source)
  have haΩ : a ∈ Ω := by
    simp [Ω, a, φ, ψ, hx]
  have hg : ContDiffOn ℝ ∞ g Ω := by
    apply ContMDiffOn.contDiffOn
    apply hψsmooth.comp
    · exact hf.comp
        ((contMDiffOn_extChartAt_symm (I := I) x).mono (fun y hy ↦ hy.1))
        (fun y hy ↦ hy.2.1)
    · intro y hy
      exact hy.2.2
  have hga : ContDiffAt ℝ ∞ g a := hg.contDiffAt (hΩ.mem_nhds haΩ)
  have hdiff : MDifferentiableAt I J f x :=
    (hf.contMDiffAt (hs.mem_nhds hx)).mdifferentiableAt (by simp)
  have hderiv : mfderiv I J f x = fderiv ℝ g a := by
    simpa only [I.range_eq_univ, fderivWithin_univ] using! hdiff.mfderiv_abuse
  have hginv : (fderiv ℝ g a).IsInvertible := hderiv ▸ hd
  obtain ⟨L, hL⟩ := hginv
  have hgderiv : HasFDerivAt g (L : E →L[ℝ] F) a := by
    rw [hL]
    exact (hga.differentiableAt (by simp)).hasFDerivAt
  -- Restrict to the open locus of invertible derivatives, so the whole inverse is smooth.
  let Ω' : Set E := Ω ∩ {z | (fderiv ℝ g z).IsInvertible}
  have hΩ' : IsOpen Ω' :=
    (hg.continuousOn_fderiv_of_isOpen hΩ (by simp)).isOpen_inter_preimage hΩ
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have haΩ' : a ∈ Ω' := ⟨haΩ, ⟨L, hL⟩⟩
  let H₀ : OpenPartialHomeomorph E F :=
    hga.toOpenPartialHomeomorph g hgderiv (by simp)
  let H : OpenPartialHomeomorph E F := H₀.restr Ω'
  have hHsource : H.source ⊆ Ω' := fun z hz ↦ hΩ'.interior_eq ▸ hz.2
  have haH : a ∈ H.source := by
    refine ⟨hga.mem_toOpenPartialHomeomorph_source hgderiv (by simp), ?_⟩
    simpa only [hΩ'.interior_eq] using haΩ'
  have hHinv : ContDiffOn ℝ ∞ H.symm H.target := by
    intro y hy
    have hp := hHsource (H.map_target hy)
    have hgp : ContDiffAt ℝ ∞ g (H.symm y) := hg.contDiffAt (hΩ.mem_nhds hp.1)
    obtain ⟨D, hD⟩ := hp.2
    have hd' : HasFDerivAt H (D : E →L[ℝ] F) (H.symm y) := by
      change HasFDerivAt g _ _
      rw [hD]
      exact (hgp.differentiableAt (by simp)).hasFDerivAt
    exact (H.contDiffAt_symm hy hd' hgp).contDiffWithinAt
  -- Conjugate the same inverse by the charts; its forward map agrees with the original f.
  let K : OpenPartialHomeomorph M N := φ.trans (H.trans ψ.symm)
  have hxK : x ∈ K.source := by
    refine ⟨mem_extChartAt_source (I := I) x, haH, ?_⟩
    change g a ∈ ψ.target
    simp [g, a, φ, ψ]
  have hKs : K.source ⊆ s := by
    intro y hy
    have hΩy := (hHsource hy.2.1).1
    have hy' : φ.symm (φ y) ∈ s := hΩy.2.1
    simpa only [φ.left_inv hy.1] using hy'
  have hKf : EqOn f K K.source := by
    intro y hy
    have hfy : f y ∈ ψ.source := by
      have hy' : f (φ.symm (φ y)) ∈ ψ.source := (hHsource hy.2.1).1.2.2
      simpa only [φ.left_inv hy.1] using hy'
    change f y = ψ.symm (ψ (f (φ.symm (φ y))))
    rw [φ.left_inv hy.1, ψ.left_inv hfy]
  have hKinv : ContMDiffOn J I ∞ K.symm K.target := by
    apply (contMDiffOn_extChartAt_symm (I := I) x).comp
    · apply (contMDiffOn_iff_contDiffOn.mpr hHinv).comp
        (hψsmooth.mono (fun y hy ↦ hy.1.1))
      intro y hy
      exact hy.1.2
    · intro y hy
      exact hy.2
  let Φ : PartialDiffeomorph I J M N ∞ :=
    { toFun := f
      invFun := K.symm
      source := K.source
      target := K.target
      map_source' := fun y hy ↦ hKf hy ▸ K.map_source hy
      map_target' := fun y hy ↦ K.map_target hy
      left_inv' := fun y hy ↦ by rw [hKf hy]; exact K.left_inv hy
      right_inv' := fun y hy ↦ by rw [hKf (K.map_target hy)]; exact K.right_inv hy
      open_source := K.open_source
      open_target := K.open_target
      contMDiffOn_toFun := hf.mono hKs
      contMDiffOn_invFun := hKinv }
  exact ⟨Φ, hxK, hKs, rfl⟩

end AtiyahSinger
