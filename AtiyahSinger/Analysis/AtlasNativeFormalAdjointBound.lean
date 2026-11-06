/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleIsoSobolev
public import AtiyahSinger.Analysis.NativeAtlasSobolev
public import AtiyahSinger.Analysis.SobolevFormalAdjointBound
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Formal-adjoint estimates in the specified native models (M2318)

The given smooth bundle isomorphisms and native presentations transport an
atlas Sobolev estimate before applying the original Hermitian pairing. The
result bounds the actual reverse map in these same native models, with a
constant independent of both maps and their error parameter. This supplies
one common transport for the horizontal and vertical cutoff errors; no new
localization or separately regularized reverse operator is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 30 in
/-- The original atlas bound transfers to its actual formal adjoint in the given native models. -/
theorem exists_atlas_native_formalAdjoint_bound
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (Li : AtlasBundlePresentation A) (Lo : AtlasBundlePresentation B)
    (N₀ N₁ : SmoothFiniteComplexBundle (n := n) M)
    (h : SmoothHermitianMetric (n := n) (r := N₀.rank) N₀.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := N₁.rank) N₁.Fiber)
    (Di : SmoothBundlePresentation (n := n) (r := N₀.rank) N₀.Fiber)
    (Do : SmoothBundlePresentation (n := n) (r := N₁.rank) N₁.Fiber) (s t : ℝ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
    let B₀ := nativeSmoothComplexBundleAtlas (n := n) (r := N₀.rank) N₀.Fiber
    let B₁ := nativeSmoothComplexBundleAtlas (n := n) (r := N₁.rank) N₁.Fiber
    ∀ (e : Iso E N₀.Fiber) (f : Iso F N₁.Fiber)
      (he : IsSmoothAtlasBundleMap A B₀ e.toHom.linearMap)
      (hei : IsSmoothAtlasBundleMap B₀ A e.symm.toHom.linearMap)
      (hf : IsSmoothAtlasBundleMap B B₁ f.toHom.linearMap)
      (hfi : IsSmoothAtlasBundleMap B₁ B f.symm.toHom.linearMap),
      let S₀ := (atlasSmoothSectionEquiv A B₀ e he hei).trans
        (nativeSmoothSectionLinearEquiv (n := n) (r := N₀.rank) N₀.Fiber)
      let S₁ := (atlasSmoothSectionEquiv B B₁ f hf hfi).trans
        (nativeSmoothSectionLinearEquiv (n := n) (r := N₁.rank) N₁.Fiber)
      ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ →
        ∀ (T : A.smoothSections →ₗ[ℂ] B.smoothSections)
          (S : B.smoothSections →ₗ[ℂ] A.smoothSections),
          (∀ u v, k.sectionPairing μ (S₁ (T u)) (S₁ v) =
            h.sectionPairing μ (S₀ u) (S₀ (S v))) →
          (∀ u, ‖Lo.smoothToSobolev t (T u)‖ ≤ δ * ‖Li.smoothToSobolev s u‖) →
          ∀ v, ‖Di.smoothToSobolev (-s) (S₀ (S v))‖ ≤
            C * δ * ‖Do.smoothToSobolev (-t) (S₁ v)‖ := by
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  intro B₀ B₁ e f he hei hf hfi S₀ S₁
  -- Both norm comparisons use the prescribed fiber maps and native presentations.
  obtain ⟨Ci, hCi, hi⟩ := exists_atlasSmoothSectionEquiv_sobolev_comparison
    A B₀ e he hei Li Di.toAtlasBundlePresentation s
  obtain ⟨Co, hCo, ho⟩ := exists_atlasSmoothSectionEquiv_sobolev_comparison
    B B₁ f hf hfi Lo Do.toAtlasBundlePresentation t
  have hin (u : A.smoothSections) :
      ‖Li.smoothToSobolev s u‖ ≤ Ci * ‖Di.smoothToSobolev s (S₀ u)‖ := by
    have hn := (Di.nativeAtlasSobolevEquiv s).norm_map (Di.smoothToSobolev s (S₀ u))
    rw [Di.nativeAtlasSobolevEquiv_smoothToSobolev] at hn
    change ‖Di.toAtlasBundlePresentation.smoothToSobolev s
      ((nativeSmoothSectionLinearEquiv N₀.Fiber).symm
        ((nativeSmoothSectionLinearEquiv N₀.Fiber)
          (atlasSmoothSectionEquiv A B₀ e he hei u)))‖ = _ at hn
    rw [LinearEquiv.symm_apply_apply] at hn
    exact (hi u).2.trans_eq (congrArg (Ci * ·) hn)
  have hout (v : B.smoothSections) :
      ‖Do.smoothToSobolev t (S₁ v)‖ ≤ Co * ‖Lo.smoothToSobolev t v‖ := by
    have hn := (Do.nativeAtlasSobolevEquiv t).norm_map (Do.smoothToSobolev t (S₁ v))
    rw [Do.nativeAtlasSobolevEquiv_smoothToSobolev] at hn
    change ‖Do.toAtlasBundlePresentation.smoothToSobolev t
      ((nativeSmoothSectionLinearEquiv N₁.Fiber).symm
        ((nativeSmoothSectionLinearEquiv N₁.Fiber)
          (atlasSmoothSectionEquiv B B₁ f hf hfi v)))‖ = _ at hn
    rw [LinearEquiv.symm_apply_apply] at hn
    exact hn.symm.trans_le (ho v).1
  obtain ⟨Cd, hCd, hdual⟩ := exists_sobolev_formalAdjoint_bound μ h k Di Do s t
  refine ⟨Cd * Co * Ci, by positivity, ?_⟩
  intro δ hδ T S hpair hbound
  let Tn := S₁.toLinearMap.comp (T.comp S₀.symm.toLinearMap)
  let Sn := S₀.toLinearMap.comp (S.comp S₁.symm.toLinearMap)
  have hpairNative (u : smoothSections (n := n) (r := N₀.rank) N₀.Fiber)
      (v : smoothSections (n := n) (r := N₁.rank) N₁.Fiber) :
      k.sectionPairing μ (Tn u) v = h.sectionPairing μ u (Sn v) := by
    have h := hpair (S₀.symm u) (S₁.symm v)
    rw [S₀.apply_symm_apply, S₁.apply_symm_apply] at h
    exact h
  have hboundNative (u : smoothSections (n := n) (r := N₀.rank) N₀.Fiber) :
      ‖Do.smoothToSobolev t (Tn u)‖ ≤ (Co * Ci * δ) * ‖Di.smoothToSobolev s u‖ := by
    have hiu := hin (S₀.symm u)
    rw [S₀.apply_symm_apply] at hiu
    calc
      _ ≤ Co * ‖Lo.smoothToSobolev t (T (S₀.symm u))‖ := hout _
      _ ≤ Co * (δ * ‖Li.smoothToSobolev s (S₀.symm u)‖) := by gcongr; exact hbound _
      _ ≤ Co * (δ * (Ci * ‖Di.smoothToSobolev s u‖)) := by gcongr
      _ = _ := by ring
  intro v
  have hfinal := hdual (Co * Ci * δ) (by positivity) Tn Sn hpairNative hboundNative (S₁ v)
  have hSn : Sn (S₁ v) = S₀ (S v) := by
    change S₀ (S (S₁.symm (S₁ v))) = _
    rw [S₁.symm_apply_apply]
  rw [hSn] at hfinal
  convert hfinal using 1
  ring

end AtiyahSinger
