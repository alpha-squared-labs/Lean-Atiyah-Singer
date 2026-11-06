/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ProductSchwartzSlice
public import AtiyahSinger.Analysis.SchwartzEuclideanParameter

/-!
# Schwartz outputs of the actual factorwise lift

Public module ID: M0873.

A compact joint Schwartz input gives a joint smooth family of exact slices
with one common compact support. The original compact-symbol quantization
preserves that joint smoothness. Multiplication by the supplied second-factor
cutoff gives compact product support, hence an actual Schwartz output for the
same lifted Fourier integral. No separated-input restriction is imposed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- The original lifted quantization has an actual Schwartz output on compact joint inputs. -/
theorem exists_schwartz_quantize_liftedProductSymbol_of_hasCompactSupport
    {n m r q : ℕ} (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ)
    (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
    (hw : HasCompactSupport w) :
    ∃ v : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q)),
      (∀ z, quantize (liftedProductSymbol a χ) w z = v z) ∧
      tsupport v ⊆ EuclideanSpace.finAddEquivProd.symm ''
        (tsupport a ×ˢ tsupport χ) := by
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let U := EuclideanSpace ℂ (Fin r)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  have hg (y : Y) : (fun x : X ↦ (x, y)).HasTemperateGrowth := by
    convert (ContinuousLinearMap.inl ℝ X Y).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const ((0 : X), y)) using 1
    funext x
    simp
  let F (y : Y) : 𝓢(X, U) :=
    SchwartzMap.compCLM ℂ (hg y) ⟨1, 1, fun x ↦ by
      simpa only [one_mul, pow_one] using
        (norm_fst_le (x, y)).trans (le_add_of_nonneg_left zero_le_one)⟩
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm w)
  have hFvalue (y : Y) (x : X) : F y x = w (e.symm (x, y)) := rfl
  -- Every exact slice has the same compact first-coordinate support.
  let K := (fun z : Z ↦ (e z).1) '' tsupport w
  have hK : IsCompact K := hw.image (continuous_fst.comp e.continuous)
  have hFsupport (y : Y) : tsupport (F y) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    refine ⟨e.symm (x, y), subset_tsupport w hx, ?_⟩
    simp only [e.apply_symm_apply]
  have hF : ContDiff ℝ ∞ (fun p : Y × X ↦ F p.1 p.2) :=
    (w.smooth ⊤).comp (e.symm.contDiff.comp (contDiff_snd.prodMk contDiff_fst))
  let T := quantizeSchwartz 1 a ha haK
  have hT : ContDiff ℝ ∞ (fun p : Y × X ↦ T (F p.1) p.2) :=
    contDiff_schwartzOperator_euclidean_of_common_compact_support F hF K hK hFsupport T
  let g (z : Z) : EuclideanSpace ℂ (Fin q) :=
    (χ (e z).2 : ℂ) • T (F (e z).2) (e z).1
  have hgsmooth : ContDiff ℝ ∞ g := by
    have hcoefficient : ContDiff ℝ ∞ (fun z : Z ↦ (χ (e z).2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_snd.comp e.contDiff))
    -- Keep the original slice and output maps fixed while swapping the two coordinates.
    have houtput : ContDiff ℝ ∞ (fun z : Z ↦ T (F (e z).2) (e z).1) :=
      ContDiff.comp (g := fun p : Y × X ↦ T (F p.1) p.2)
        (f := fun z : Z ↦ ((e z).2, (e z).1)) hT
        ((contDiff_snd.comp e.contDiff).prodMk (contDiff_fst.comp e.contDiff))
    exact hcoefficient.smul houtput
  -- The original compact symbol and supplied cutoff control the actual output support.
  have hTzero (u : 𝓢(X, U)) (x : X) (hx : x ∉ tsupport a) : T u x = 0 := by
    rw [quantizeSchwartz_apply]
    have ha0 := image_eq_zero_of_notMem_tsupport hx
    simp only [quantize, ha0, Pi.zero_apply, zero_apply, smul_zero, integral_zero]
  have hproduct : IsCompact (e.symm '' (tsupport a ×ˢ tsupport χ)) :=
    (haK.prod hχK).image e.symm.continuous
  have hsupport : tsupport g ⊆ e.symm '' (tsupport a ×ˢ tsupport χ) := by
    apply closure_minimal ?_ hproduct.isClosed
    intro z hz
    refine ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩
    · by_contra h
      exact hz (by simp only [g, hTzero _ _ h, smul_zero])
    · by_contra h
      exact hz (by simp only [g, image_eq_zero_of_notMem_tsupport h,
        Complex.ofReal_zero, zero_smul])
  let v := HasCompactSupport.toSchwartzMap
    (show HasCompactSupport g from
      hproduct.of_isClosed_subset (isClosed_tsupport _) hsupport) hgsmooth
  refine ⟨v, ?_, hsupport⟩
  intro z
  have h := quantize_liftedProductSymbol_eq_slice a ha haK χ w (e z).2 (F (e z).2)
    (hFvalue (e z).2) (e z).1
  change quantize (liftedProductSymbol a χ) w (e.symm (e z)) = _ at h
  rw [e.symm_apply_apply] at h
  simpa only [v, HasCompactSupport.toSchwartzMap_toFun, g, T, quantizeSchwartz_apply] using h

end AtiyahSinger
