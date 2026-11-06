/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Geometry.ManifoldModelChange

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Cotangent transport under a specified linear change of manifold model

Public module ID: M1153.

Postcomposing every original chart with `e : E ≃L[ℝ] F` changes the coordinates
of a tangent vector by `e`. A covector therefore changes by precomposition
with `e.symm`. The base point and its topology remain unchanged. Both total
spaces carry their native dual tangent-bundle topologies, for their respective
atlases; neither topology is defined by transport through the claimed map.

This is the coordinate covariance used in SG III.1 and III.3. It supplies the
precise model comparison needed to apply the existing Euclidean analytic index
to the full product model of the associated sphere bundle in SG III.13.
No finite dimension, separation, compactness or orientation is needed here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (e : E ≃L[ℝ] F) (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

/-- Change the original covector coordinates by the inverse of the specified model map. -/
def cotangentLinearModelMap :
    letI := linearModelChartedSpace e M
    TotalSpace (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) →
      TotalSpace (F →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ) := by
  letI := linearModelChartedSpace e M
  exact fun z ↦ ⟨z.proj, z.snd.comp e.symm.toContinuousLinearMap⟩

variable [hM : IsManifold 𝓘(ℝ, E) ∞ M]

include hM in
/-- The specified inverse-dual formula respects the two native cotangent bundle topologies. -/
theorem isHomeomorph_cotangentLinearModelMap :
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    IsHomeomorph (cotangentLinearModelMap e M) := by
  classical
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let d := linearModelDiffeomorph e M
  let source := TotalSpace (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
  let target := TotalSpace (F →L[ℝ] ℝ) (fun x : M ↦ TangentSpace J x →L[ℝ] ℝ)
  -- The two model atlases retain exactly the certified derivatives e and e.symm.
  have hderiv (x : M) : mfderiv J I d.symm x = e.symm.toContinuousLinearMap :=
    (contMDiff_mfderiv_linearModelId e M).2.2 x
  have hderiv' (x : M) : mfderiv I J d x = e.toContinuousLinearMap :=
    (contMDiff_mfderiv_linearModelId e M).2.1 x
  have hforward : Continuous (cotangentLinearModelMap e M) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let tE := trivializationAt E (TangentSpace I : M → Type _) z₀.proj
    have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
      (fun z : source ↦ z) (x₀ := z₀)).mp continuousAt_id
    have hξ : ContinuousAt (fun z : source ↦ z.snd.comp (tE.symmL ℝ z.proj)) z₀ := by
      have h := hsource.2
      change ContinuousAt (fun z : source ↦
        ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj).comp
          (z.snd.comp (tE.symmL ℝ z.proj))) z₀ at h
      simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_comp] using h
    have hd := ((d.symm.contMDiffAt (x := z₀.proj)).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt.comp
      (f := fun z : source ↦ z.proj) hsource.1
    apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
    refine ⟨hsource.1, ?_⟩
    apply (hξ.clm_comp hd).congr_of_eventuallyEq
    filter_upwards [hsource.1.preimage_mem_nhds
      (tE.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ z₀.proj))]
      with z hz
    apply ContinuousLinearMap.ext
    intro v
    have hscalar :
        (trivializationAt ℝ (fun _ : M ↦ ℝ) z₀.proj).continuousLinearMapAt ℝ z.proj =
          ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    simp only [cotangentLinearModelMap, Function.comp_apply, inTangentCoordinates,
      ContinuousLinearMap.inCoordinates, Function.id_def,
      ContinuousLinearMap.comp_apply, hscalar, ContinuousLinearMap.id_apply]
    change z.snd (e.symm ((trivializationAt F (TangentSpace J : M → Type _)
        z₀.proj).symmL ℝ z.proj v)) =
      z.snd (tE.symmL ℝ z.proj (tE.continuousLinearMapAt ℝ z.proj
        ((mfderiv J I d.symm z.proj)
          ((trivializationAt F (TangentSpace J : M → Type _)
            z₀.proj).symmL ℝ z.proj v))))
    erw [tE.symmL_continuousLinearMapAt (R := ℝ) hz, hderiv]
    rfl
  -- The reverse formula uses precomposition with e in the other original native topology.
  let inverseMap (z : target) : source := ⟨z.proj, z.snd.comp e.toContinuousLinearMap⟩
  have hbackward : Continuous inverseMap := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let tF := trivializationAt F (TangentSpace J : M → Type _) z₀.proj
    have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
      (fun z : target ↦ z) (x₀ := z₀)).mp continuousAt_id
    have hξ : ContinuousAt (fun z : target ↦ z.snd.comp (tF.symmL ℝ z.proj)) z₀ := by
      have h := hsource.2
      change ContinuousAt (fun z : target ↦
        ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj).comp
          (z.snd.comp (tF.symmL ℝ z.proj))) z₀ at h
      simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_comp] using h
    have hd := ((d.contMDiffAt (x := z₀.proj)).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt.comp
      (f := fun z : target ↦ z.proj) hsource.1
    apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
    refine ⟨hsource.1, ?_⟩
    apply (hξ.clm_comp hd).congr_of_eventuallyEq
    filter_upwards [hsource.1.preimage_mem_nhds
      (tF.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ z₀.proj))]
      with z hz
    apply ContinuousLinearMap.ext
    intro v
    have hscalar :
        (trivializationAt ℝ (fun _ : M ↦ ℝ) z₀.proj).continuousLinearMapAt ℝ z.proj =
          ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    simp only [inverseMap, Function.comp_apply, inTangentCoordinates,
      ContinuousLinearMap.inCoordinates, Function.id_def,
      ContinuousLinearMap.comp_apply, hscalar, ContinuousLinearMap.id_apply]
    change z.snd (e ((trivializationAt E (TangentSpace I : M → Type _)
        z₀.proj).symmL ℝ z.proj v)) =
      z.snd (tF.symmL ℝ z.proj (tF.continuousLinearMapAt ℝ z.proj
        ((mfderiv I J d z.proj)
          ((trivializationAt E (TangentSpace I : M → Type _)
            z₀.proj).symmL ℝ z.proj v))))
    erw [tF.symmL_continuousLinearMapAt (R := ℝ) hz, hderiv']
    rfl
  -- The same two precomposition maps cancel fiberwise, keeping the base point fixed.
  let h : source ≃ₜ target :=
    { toFun := cotangentLinearModelMap e M
      invFun := inverseMap
      left_inv := by
        rintro ⟨x, ξ⟩
        dsimp only [inverseMap, cotangentLinearModelMap]
        congr 1
        apply ContinuousLinearMap.ext
        intro v
        exact congrArg ξ (e.symm_apply_apply v)
      right_inv := by
        rintro ⟨x, ξ⟩
        dsimp only [inverseMap, cotangentLinearModelMap]
        congr 1
        apply ContinuousLinearMap.ext
        intro v
        exact congrArg ξ (e.apply_symm_apply v)
      continuous_toFun := hforward
      continuous_invFun := hbackward }
  exact h.isHomeomorph

/-- The homeomorphism of native cotangent bundles with the exact inverse-dual formula. -/
def cotangentLinearModelHomeomorph :
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    TotalSpace (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) ≃ₜ
      TotalSpace (F →L[ℝ] ℝ) (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ) := by
  letI := linearModelChartedSpace e M
  letI := isManifold_linearModelChartedSpace e M
  exact (isHomeomorph_cotangentLinearModelMap e M).homeomorph
    (cotangentLinearModelMap e M)

end AtiyahSinger
