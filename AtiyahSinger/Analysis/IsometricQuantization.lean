/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.BesselSymbol
public import AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Orthogonal coordinate changes for the actual Fourier quantizer

Public module ID: M0764.

Orthogonal changes of Euclidean coordinates preserve symbol order, the exact
SG Fourier quantization formula, and every Bessel Sobolev norm. These formulas
transport product cutoffs between the two coordinate orders without changing
their geometric norm or their totalized integral convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

variable {n m r q : ℕ}

/-- Orthogonal coordinate transport preserves the full symbol order. -/
theorem isSymbol_comp_linearIsometry
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (d : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol Set.univ d a) :
    IsSymbol Set.univ d (fun x ξ ↦ a (e x) (e ξ)) := by
  have hdim : m = n := by simpa using e.toLinearEquiv.finrank_eq
  subst m
  have hs : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
  refine ⟨(hs.comp ((e.contDiff.comp contDiff_fst).prodMk
    (e.contDiff.comp contDiff_snd))).contDiffOn, ?_⟩
  intro K hKU hK i j
  exact exists_bound_symbol_comp_linear_frequency Set.univ isOpen_univ d a ha
    Set.univ isOpen_univ e e.contDiff.contDiffOn (fun _ _ ↦ Set.mem_univ _)
    (fun _ ↦ e.toContinuousLinearEquiv.toContinuousLinearMap) contDiffOn_const
    (fun _ _ ↦ ⟨e.toContinuousLinearEquiv, rfl⟩) K hK hKU i j

/-- The actual SG quantizer commutes with a fixed orthogonal coordinate change. -/
theorem quantize_comp_linearIsometry
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (a : SymbolFunction n r q)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin m)) :
    quantize (fun y ξ ↦ a (e y) (e ξ))
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv u) x =
      quantize a u (e x) := by
  have hdim : m = n := by simpa using e.toLinearEquiv.finrank_eq
  let v := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv u
  have hf (ξ : EuclideanSpace ℝ (Fin m)) : fourierSG v ξ = fourierSG u (e ξ) := by
    simp only [fourierSG, SchwartzMap.fourier_coe]
    change FourierTransform.fourier ((u : _ → _) ∘ e) ((2 * Real.pi)⁻¹ • ξ) = _
    rw [Real.fourier_comp_linearIsometry, e.map_smul]
  -- Orthogonality preserves both the Fourier phase and the original volume measure.
  change quantize (fun y ξ ↦ a (e y) (e ξ)) v x = quantize a u (e x)
  simp only [quantize, hf, hdim]
  congr 1
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [e.inner_map_map]

/-- Every real Bessel Sobolev norm is unchanged by orthogonal coordinate transport. -/
theorem norm_schwartzSobolevCoordinate_comp_linearIsometry
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (s : ℝ) (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    ‖schwartzSobolevCoordinate s
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv u)‖ =
      ‖schwartzSobolevCoordinate s u‖ := by
  let v := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv u
  have hb : (fun x ξ ↦ besselSymbol n r (2 * s) (e x) (e ξ)) =
      besselSymbol m r (2 * s) := by
    funext x ξ
    simp only [besselSymbol, ← e.map_smul, e.norm_map]
  have hquant (x : EuclideanSpace ℝ (Fin m)) :
      quantize (besselSymbol m r (2 * s)) v x =
        quantize (besselSymbol n r (2 * s)) u (e x) := by
    rw [← hb]
    exact quantize_comp_linearIsometry e _ u x
  -- The Bessel pairing uses the same quantizer and the same measure-preserving substitution.
  have hsq : ((‖schwartzSobolevCoordinate s v‖ ^ 2 : ℝ) : ℂ) =
      ((‖schwartzSobolevCoordinate s u‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_schwartzSobolevCoordinate_sq_eq_integral,
      norm_schwartzSobolevCoordinate_sq_eq_integral]
    simp only [hquant]
    change (∫ x, inner ℂ (u (e x)) (quantize (besselSymbol n r (2 * s)) u (e x))) = _
    exact e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
      (fun z : EuclideanSpace ℝ (Fin n) ↦ inner ℂ (u z)
        (quantize (besselSymbol n r (2 * s)) u z))
  have hreal : ‖schwartzSobolevCoordinate s v‖ ^ 2 =
      ‖schwartzSobolevCoordinate s u‖ ^ 2 := Complex.ofReal_injective hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hreal


/-- Orthogonal changes of the two coefficient bases commute with the actual quantizer. -/
theorem quantize_conjugate_linearIsometry {r' q' : ℕ}
    (e : EuclideanSpace ℂ (Fin r') ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r))
    (f : EuclideanSpace ℂ (Fin q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q'))
    (a : SymbolFunction n r q)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (fun y ξ ↦ f.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((a y ξ).comp e.toContinuousLinearEquiv.toContinuousLinearMap))
      (SchwartzMap.postcompCLM e.symm.toContinuousLinearEquiv.toContinuousLinearMap u) x =
        f (quantize a u x) := by
  let v := SchwartzMap.postcompCLM e.symm.toContinuousLinearEquiv.toContinuousLinearMap u
  have hf (ξ : EuclideanSpace ℝ (Fin n)) : fourierSG v ξ = e.symm (fourierSG u ξ) := by
    simp only [fourierSG, SchwartzMap.fourier_coe, Real.fourier_eq']
    change (∫ y, Complex.exp _ • e.symm (u y)) = e.symm (∫ y, Complex.exp _ • u y)
    simp_rw [← e.symm.map_smul]
    exact e.symm.toLinearIsometry.integral_comp_comm _
  -- Isometric coefficient maps preserve the totalized Bochner integral as well.
  change quantize (fun y ξ ↦ f.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((a y ξ).comp e.toContinuousLinearEquiv.toContinuousLinearMap)) v x = _
  simp only [quantize, ContinuousLinearMap.comp_apply, hf,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    e.apply_symm_apply]
  simp_rw [← f.map_smul]
  have hint := f.toLinearIsometry.integral_comp_comm (μ := volume)
    (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • a x ξ (fourierSG u ξ))
  refine (congrArg (fun z : EuclideanSpace ℂ (Fin q') ↦
    (((2 * Real.pi) ^ n)⁻¹ : ℝ) • z) hint).trans ?_
  exact (f.toLinearEquiv.map_smul_of_tower (((2 * Real.pi) ^ n)⁻¹) _).symm

/-- Orthogonal coefficient transport preserves every real Bessel Sobolev norm. -/
theorem norm_schwartzSobolevCoordinate_postcomp_linearIsometry
    (e : EuclideanSpace ℂ (Fin r) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q))
    (s : ℝ) (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    ‖schwartzSobolevCoordinate s
      (SchwartzMap.postcompCLM e.toContinuousLinearEquiv.toContinuousLinearMap u)‖ =
      ‖schwartzSobolevCoordinate s u‖ := by
  let v := SchwartzMap.postcompCLM e.toContinuousLinearEquiv.toContinuousLinearMap u
  have hb : (fun x ξ ↦ e.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((besselSymbol n r (2 * s) x ξ).comp
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap)) =
      besselSymbol n q (2 * s) := by
    funext x ξ
    apply ContinuousLinearMap.ext
    intro z
    simp only [besselSymbol, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
    exact (e.toLinearEquiv.map_smul_of_tower _ (e.symm z)).trans
      (congrArg (_ • ·) (e.apply_symm_apply z))
  have hquant (x : EuclideanSpace ℝ (Fin n)) :
      quantize (besselSymbol n q (2 * s)) v x =
        e (quantize (besselSymbol n r (2 * s)) u x) := by
    rw [← hb]
    exact quantize_conjugate_linearIsometry e.symm e _ u x
  -- The Bessel pairing is preserved by these same coefficient isometries.
  have hsq : ((‖schwartzSobolevCoordinate s v‖ ^ 2 : ℝ) : ℂ) =
      ((‖schwartzSobolevCoordinate s u‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_schwartzSobolevCoordinate_sq_eq_integral,
      norm_schwartzSobolevCoordinate_sq_eq_integral]
    simp only [hquant]
    apply integral_congr_ae
    filter_upwards [] with x
    change inner ℂ (e (u x)) (e (quantize (besselSymbol n r (2 * s)) u x)) = _
    exact e.inner_map_map _ _
  have hreal : ‖schwartzSobolevCoordinate s v‖ ^ 2 =
      ‖schwartzSobolevCoordinate s u‖ ^ 2 := Complex.ofReal_injective hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hreal

end AtiyahSinger
