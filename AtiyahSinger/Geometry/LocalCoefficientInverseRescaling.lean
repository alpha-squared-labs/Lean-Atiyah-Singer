/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.LocalCoefficientRescalingContinuity
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Inverse rescaling for a local continuous coefficient factorization

Public module ID: M1291.

An open partial homeomorphism locally factors as smooth normalized geometry
after a continuous coefficient shear. Above a specified zero vector in its
source, its inverse rescaling is jointly continuous at scale zero. Removing
the shear gives a local homeomorphism; the triangular derivative of the
smooth factor makes its local inverse smooth. The specified inverse and
coefficient family are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter Set Topology
open scoped ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- The specified inverse has jointly continuous rescaling at scale zero above the
given source zero vector. -/
theorem continuousAt_rescaleAlongFibers_symm_of_coefficient
    (A : E × F → G ≃L[ℝ] G) (S : Set (E × F)) (hS : IsOpen S)
    (hA : ContinuousOn (fun p : (E × F) × G ↦ A p.1 p.2) (S ×ˢ univ))
    (hAi : ContinuousOn (fun p : (E × F) × G ↦ (A p.1).symm p.2) (S ×ˢ univ))
    (hzero : ∀ y : E, (y, (0 : F)) ∈ S → A (y, 0) = ContinuousLinearEquiv.refl ℝ G)
    (e : OpenPartialHomeomorph (E × (F × G)) (E × (F × G)))
    (g : E × (F × G) → E × (F × G)) {U : Set (E × (F × G))}
    (hg : ContDiffOn ℝ ∞ g U) (hU : IsOpen U)
    (hgzero : ∀ y : E, (y, (0 : F × G)) ∈ U → g (y, 0) = (y, 0))
    (x : E) (v : F) (w : G) (hxS : (x, (0 : F)) ∈ S)
    (hxU : (x, (0 : F × G)) ∈ U) (hxe : (x, (0 : F × G)) ∈ e.source)
    (hezero : e (x, 0) = (x, 0))
    (hlocal : (e : E × (F × G) → E × (F × G)) =ᶠ[𝓝 (x, (0 : F × G))]
      g ∘ continuousCoefficientShear A S hS hA hAi)
    (hnormal : (fderiv ℝ (fun z ↦ (g z).2) (x, 0)).comp
      (ContinuousLinearMap.inr ℝ E (F × G)) = ContinuousLinearMap.id ℝ (F × G)) :
    ContinuousAt (rescaleAlongFibers e.symm) (0, x, v, w) := by
  classical
  let C := continuousCoefficientShear A S hS hA hAi
  let D := C.symm.trans e
  let z : E × (F × G) := (x, 0)
  have hxC : z ∈ C.target := hxS
  have hCzero : C.symm z = z := by simp [C, continuousCoefficientShear, z]
  have hxD : z ∈ D.source := by
    refine ⟨hxC, ?_⟩
    change C.symm z ∈ e.source
    rw [hCzero]
    exact hxe
  have hDzero : D z = z := by
    change e (C.symm z) = z
    rw [hCzero]
    exact hezero
  have hxDt : z ∈ D.target := hDzero ▸ D.map_source hxD
  have hDizero : D.symm z = z :=
    (congrArg D.symm hDzero.symm).trans (D.left_inv hxD)
  -- Removing the specified shear gives the smooth factor on a genuine open neighborhood.
  have hDg : (D : E × (F × G) → E × (F × G)) =ᶠ[𝓝 z] g := by
    have hnear := (C.continuousAt_symm hxC).eventually
      (show ∀ᶠ q in 𝓝 (C.symm z), e q = g (C q) from by
        rw [hCzero]
        exact hlocal)
    filter_upwards [hnear, C.open_target.mem_nhds hxC] with q hq hqt
    change e (C.symm q) = g q
    rw [hq, C.right_inv hqt]
  have hnear : ∀ᶠ q in 𝓝 z, D q = g q ∧ q ∈ D.source ∧ q ∈ U := by
    filter_upwards [hDg, D.open_source.mem_nhds hxD, hU.mem_nhds hxU] with q hq hqD hqU
    exact ⟨hq, hqD, hqU⟩
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hnear
  have hWU : W ⊆ U := fun q hq ↦ (hWsub hq).2.2
  have hWD : W ⊆ D.source := fun q hq ↦ (hWsub hq).2.1
  have hDeq : EqOn D g W := fun q hq ↦ (hWsub hq).1
  have hDs : ContDiffOn ℝ ∞ D W := (hg.mono hWU).congr hDeq
  have hga : ContDiffAt ℝ ∞ g z := hg.contDiffAt (hU.mem_nhds hxU)
  let L := fderiv ℝ g z
  have hLg : HasFDerivAt g L z := (hga.differentiableAt (by simp)).hasFDerivAt
  -- Fixed zero vectors and the normalized normal block give a triangular invertible derivative.
  have hbase : (fun y : E ↦ g (y, (0 : F × G))) =ᶠ[𝓝 x]
      (fun y : E ↦ (y, (0 : F × G))) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt
      (hU.mem_nhds hxU)] with y hy
    exact hgzero y hy
  have hLbase (a : E) : L (a, 0) = (a, 0) := by
    have h := (hLg.comp x (hasFDerivAt_prodMk_left x (0 : F × G))).congr_of_eventuallyEq
      hbase.symm
    exact DFunLike.congr_fun (h.unique (hasFDerivAt_prodMk_left x (0 : F × G))) a
  have hLnormal (b : F × G) : (L (0, b)).2 = b := by
    rw [hLg.snd.fderiv] at hnormal
    exact DFunLike.congr_fun hnormal b
  have hLsnd (q : E × (F × G)) : (L q).2 = q.2 := by
    have hq : q = (q.1, 0) + (0, q.2) := by simp
    calc
      (L q).2 = (L (q.1, 0)).2 + (L (0, q.2)).2 := by
        conv_lhs => rw [hq, map_add]
        rfl
      _ = q.2 := by rw [hLbase, hLnormal]; simp
  have hinj : Function.Injective L := by
    have hker (q : E × (F × G)) (hq : L q = 0) : q = 0 := by
      have hb : q.2 = 0 := by simpa only [hLsnd, Prod.snd_zero] using congrArg Prod.snd hq
      have hq' : q = (q.1, 0) := Prod.ext rfl hb
      rw [hq', hLbase] at hq
      exact hq'.trans hq
    intro q r hqr
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hqr, sub_self]
  let l : (E × (F × G)) ≃L[ℝ] (E × (F × G)) :=
    (LinearEquiv.ofBijective L.toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hLD : HasFDerivAt D (l : _ →L[ℝ] _) z := hLg.congr_of_eventuallyEq hDg
  -- The inverse is smooth on the image of the open locus of invertible derivatives.
  let W' := W ∩ {q | (fderiv ℝ D q).IsInvertible}
  have hW' : IsOpen W' :=
    (hDs.continuousOn_fderiv_of_isOpen hW (by simp)).isOpen_inter_preimage hW
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hxW' : z ∈ W' := ⟨hxW, l, hLD.fderiv.symm⟩
  let V := (D.target ∩ D.symm ⁻¹' W') ∩ W
  have hV : IsOpen V := (D.isOpen_inter_preimage_symm hW').inter hW
  have hxV : z ∈ V := by
    refine ⟨⟨hxDt, ?_⟩, hxW⟩
    change D.symm z ∈ W'
    rw [hDizero]
    exact hxW'
  have hDi : ContDiffOn ℝ ∞ D.symm V := by
    intro q hq
    have hpoint := hq.1.2
    obtain ⟨k, hk⟩ := hpoint.2
    have hDq := hDs.contDiffAt (hW.mem_nhds hpoint.1)
    have hDq' : HasFDerivAt D (k : _ →L[ℝ] _) (D.symm q) := by
      rw [hk]
      exact (hDq.differentiableAt (by simp)).hasFDerivAt
    exact (D.contDiffAt_symm hq.1.1 hDq' hDq).contDiffWithinAt
  have hDiz (y : E) (hy : (y, (0 : F × G)) ∈ V) : D.symm (y, 0) = (y, 0) := by
    have hfixed : D (y, 0) = (y, 0) := (hDeq hy.2).trans (hgzero y (hWU hy.2))
    exact (congrArg D.symm hfixed.symm).trans (D.left_inv (hWD hy.2))
  have hLDi : HasFDerivAt D.symm (l.symm : _ →L[ℝ] _) z := by
    apply D.hasFDerivAt_symm hxDt
    simpa only [hDizero] using hLD
  have hDinormal : (fderiv ℝ (fun q ↦ (D.symm q).2) z).comp
      (ContinuousLinearMap.inr ℝ E (F × G)) = ContinuousLinearMap.id ℝ (F × G) := by
    rw [hLDi.snd.fderiv]
    apply ContinuousLinearMap.ext
    intro b
    have h := hLsnd (l.symm (0, b))
    change (l (l.symm (0, b))).2 = (l.symm (0, b)).2 at h
    rw [l.apply_symm_apply] at h
    exact h.symm
  -- The inverse factorization uses the same coefficient inverse and this actual local inverse.
  have hzeroi (y : E) (hy : (y, (0 : F)) ∈ S) :
      (A (y, 0)).symm = ContinuousLinearEquiv.refl ℝ G := by rw [hzero y hy]; rfl
  have hcont := (continuousAt_rescaleAlongFibers_coefficient_comp
    (fun q ↦ (A q).symm) S hS hAi hA hzeroi D.symm hDi hV hDiz
    x v w hxS hxV hDinormal).2
  have hinverse : (e.symm : E × (F × G) → E × (F × G)) =ᶠ[𝓝 z]
      (C.symm ∘ D.symm) := by
    filter_upwards [D.open_target.mem_nhds hxDt] with q hq
    change e.symm q = C.symm (C (e.symm q))
    exact (C.left_inv hq.2).symm
  exact hcont.congr_of_eventuallyEq
    (eventuallyEq_rescaleAlongFibers_zero e.symm (C.symm ∘ D.symm) x (v, w) hinverse)

end AtiyahSinger
