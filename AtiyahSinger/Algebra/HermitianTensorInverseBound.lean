/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# A quantitative inverse bound for the original Hermitian tensor matrix

Public module ID: M0034.

An inverse bound for either original factor controls the inverse of its full
Hermitian graded tensor matrix. The proof keeps the Hilbert tensor norms and
the existing maximum norm on the two summands. The factor two accounts for
that maximum norm; no alternative product norm or equal-rank hypothesis is
introduced. This supplies the quantitative step needed for full-symbol
ellipticity after the actual finite cutoff factors have been identified.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]

-- Implementation lemma: tensoring a specified bounded left inverse preserves its bound.
private theorem norm_le_mul_norm_tensor_map_of_leftInverse {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (a : X →L[ℂ] Y) (b : Y →L[ℂ] X) (hab : b.comp a = ContinuousLinearMap.id ℂ X)
    (C : ℝ) (hb : ‖b‖ ≤ C) :
    (∀ u : X ⊗[ℂ] Z, ‖u‖ ≤ C * ‖TensorProduct.map a.toLinearMap LinearMap.id u‖) ∧
    (∀ u : Z ⊗[ℂ] X, ‖u‖ ≤ C * ‖TensorProduct.map LinearMap.id a.toLinearMap u‖) := by
  constructor
  · intro u
    have hinv : b.rTensor Z (a.rTensor Z u) = u := by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.rTensor_comp,
        hab, ContinuousLinearMap.rTensor_id, ContinuousLinearMap.id_apply]
    calc
      ‖u‖ = ‖b.rTensor Z (a.rTensor Z u)‖ := congrArg norm hinv.symm
      _ ≤ ‖b.rTensor Z‖ * ‖a.rTensor Z u‖ := (b.rTensor Z).le_opNorm _
      _ ≤ C * ‖a.rTensor Z u‖ := mul_le_mul_of_nonneg_right
        ((ContinuousLinearMap.norm_rTensor_le Z b).trans hb) (norm_nonneg _)
      _ = C * ‖TensorProduct.map a.toLinearMap LinearMap.id u‖ := rfl
  · intro u
    have hinv : b.lTensor Z (a.lTensor Z u) = u := by
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.lTensor_comp,
        hab, ContinuousLinearMap.lTensor_id, ContinuousLinearMap.id_apply]
    calc
      ‖u‖ = ‖b.lTensor Z (a.lTensor Z u)‖ := congrArg norm hinv.symm
      _ ≤ ‖b.lTensor Z‖ * ‖a.lTensor Z u‖ := (b.lTensor Z).le_opNorm _
      _ ≤ C * ‖a.lTensor Z u‖ := mul_le_mul_of_nonneg_right
        ((ContinuousLinearMap.norm_lTensor_le Z b).trans hb) (norm_nonneg _)
      _ = C * ‖TensorProduct.map LinearMap.id a.toLinearMap u‖ := by
        rw [ContinuousLinearMap.lTensor_apply]
        rfl

/-- Either factor's inverse bound controls the same full Hermitian tensor matrix. -/
theorem reciprocalTensorSymbol_isInvertible_of_inverse_bound
    (p : E₀ →L[ℂ] E₁) (q : F₀ →L[ℂ] F₁) (C : ℝ) (hC : 0 ≤ C)
    (h : (p.IsInvertible ∧ ‖p.inverse‖ ≤ C) ∨ (q.IsInvertible ∧ ‖q.inverse‖ ≤ C)) :
    let T := (reciprocalTensorSymbol p.toLinearMap p.toLinearMap.adjoint
      q.toLinearMap q.toLinearMap.adjoint).toContinuousLinearMap
    T.IsInvertible ∧ ‖T.inverse‖ ≤ 2 * C := by
  classical
  let := FiniteDimensional.complete ℂ E₀
  let := FiniteDimensional.complete ℂ E₁
  let := FiniteDimensional.complete ℂ F₀
  let := FiniteDimensional.complete ℂ F₁
  let D₀ := TensorProduct.map p.toLinearMap (LinearMap.id : Module.End ℂ F₀)
  let D₁ := TensorProduct.map p.toLinearMap.adjoint (LinearMap.id : Module.End ℂ F₁)
  let Q₀ := TensorProduct.map (LinearMap.id : Module.End ℂ E₀) q.toLinearMap
  let Q₁ := TensorProduct.map (LinearMap.id : Module.End ℂ E₁) q.toLinearMap.adjoint
  let T := (reciprocalTensorSymbol p.toLinearMap p.toLinearMap.adjoint
    q.toLinearMap q.toLinearMap.adjoint).toContinuousLinearMap
  -- The off-diagonal inner products cancel for these same two adjoint pairs.
  have henergy (u : (E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) :
      ‖(T u).1‖ ^ 2 + ‖(T u).2‖ ^ 2 =
        ‖D₀ u.1‖ ^ 2 + ‖Q₀ u.1‖ ^ 2 + ‖D₁ u.2‖ ^ 2 + ‖Q₁ u.2‖ ^ 2 := by
    have hcross : inner ℂ (D₀ u.1) (Q₁ u.2) = inner ℂ (Q₀ u.1) (D₁ u.2) := by
      rw [← LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_right]
      congr 1
      change (D₀.adjoint.comp Q₁) u.2 = (Q₀.adjoint.comp D₁) u.2
      simp only [D₀, D₁, Q₀, Q₁, TensorProduct.adjoint_map, LinearMap.adjoint_id,
        ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]
    change ‖D₀ u.1 - Q₁ u.2‖ ^ 2 + ‖Q₀ u.1 + D₁ u.2‖ ^ 2 = _
    rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), hcross]
    ring
  have hparts (u : (E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) :
      ‖D₀ u.1‖ ≤ ‖(T u).1‖ + ‖(T u).2‖ ∧
      ‖Q₀ u.1‖ ≤ ‖(T u).1‖ + ‖(T u).2‖ ∧
      ‖D₁ u.2‖ ≤ ‖(T u).1‖ + ‖(T u).2‖ ∧
      ‖Q₁ u.2‖ ≤ ‖(T u).1‖ + ‖(T u).2‖ := by
    have he := henergy u
    have hn₀ := norm_nonneg (T u).1
    have hn₁ := norm_nonneg (T u).2
    have hd₀ := norm_nonneg (D₀ u.1)
    have hq₀ := norm_nonneg (Q₀ u.1)
    have hd₁ := norm_nonneg (D₁ u.2)
    have hq₁ := norm_nonneg (Q₁ u.2)
    have hs₀ := sq_nonneg ‖D₀ u.1‖
    have hs₁ := sq_nonneg ‖Q₀ u.1‖
    have hs₂ := sq_nonneg ‖D₁ u.2‖
    have hs₃ := sq_nonneg ‖Q₁ u.2‖
    have hprod : 0 ≤ ‖(T u).1‖ * ‖(T u).2‖ := mul_nonneg hn₀ hn₁
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  -- Either original inverse controls both its forward and its adjoint tensor blocks.
  have hlower (u : (E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) : ‖u‖ ≤ (2 * C) * ‖T u‖ := by
    have hsum : C * (‖(T u).1‖ + ‖(T u).2‖) ≤ (2 * C) * ‖T u‖ := by
      have h₀ := norm_fst_le (T u)
      have h₁ := norm_snd_le (T u)
      nlinarith
    rw [Prod.norm_def]
    apply max_le
    · rcases h with ⟨hp, hpC⟩ | ⟨hq, hqC⟩
      · have hbound : ‖u.1‖ ≤ C * ‖D₀ u.1‖ :=
          (norm_le_mul_norm_tensor_map_of_leftInverse (Z := F₀) p p.inverse
            hp.inverse_comp_self C hpC).1 u.1
        have hpart : ‖D₀ u.1‖ ≤ ‖(T u).1‖ + ‖(T u).2‖ := (hparts u).1
        exact hbound.trans ((mul_le_mul_of_nonneg_left hpart hC).trans hsum)
      · have hbound : ‖u.1‖ ≤ C * ‖Q₀ u.1‖ :=
          (norm_le_mul_norm_tensor_map_of_leftInverse (Z := E₀) q q.inverse
            hq.inverse_comp_self C hqC).2 u.1
        have hpart : ‖Q₀ u.1‖ ≤ ‖(T u).1‖ + ‖(T u).2‖ := (hparts u).2.1
        exact hbound.trans ((mul_le_mul_of_nonneg_left hpart hC).trans hsum)
    · rcases h with ⟨hp, hpC⟩ | ⟨hq, hqC⟩
      · have hinv : p.inverse.adjoint.comp p.adjoint = ContinuousLinearMap.id ℂ E₁ := by
          rw [← ContinuousLinearMap.adjoint_comp, hp.self_comp_inverse,
            ContinuousLinearMap.adjoint_id]
        have hnorm : ‖p.inverse.adjoint‖ ≤ C := by
          simpa only [ContinuousLinearMap.adjoint.norm_map] using hpC
        have hbound : ‖u.2‖ ≤ C * ‖D₁ u.2‖ := by
          simpa only [D₁, ContinuousLinearMap.adjoint_toLinearMap] using
            (norm_le_mul_norm_tensor_map_of_leftInverse (Z := F₁) p.adjoint
              p.inverse.adjoint hinv C hnorm).1 u.2
        exact hbound.trans ((mul_le_mul_of_nonneg_left (hparts u).2.2.1 hC).trans hsum)
      · have hinv : q.inverse.adjoint.comp q.adjoint = ContinuousLinearMap.id ℂ F₁ := by
          rw [← ContinuousLinearMap.adjoint_comp, hq.self_comp_inverse,
            ContinuousLinearMap.adjoint_id]
        have hnorm : ‖q.inverse.adjoint‖ ≤ C := by
          simpa only [ContinuousLinearMap.adjoint.norm_map] using hqC
        have hbound : ‖u.2‖ ≤ C * ‖Q₁ u.2‖ := by
          simpa only [Q₁, ContinuousLinearMap.adjoint_toLinearMap] using
            (norm_le_mul_norm_tensor_map_of_leftInverse (Z := E₁) q.adjoint
              q.inverse.adjoint hinv C hnorm).2 u.2
        exact hbound.trans ((mul_le_mul_of_nonneg_left (hparts u).2.2.2 hC).trans hsum)
  have hbij : Function.Bijective T := by
    have hfactor : Function.Bijective p ∨ Function.Bijective q :=
      h.imp (fun hp ↦ hp.1.bijective) (fun hq ↦ hq.1.bijective)
    simpa only [T, LinearMap.coe_toContinuousLinearMap', weightedGradedTensorSymbol,
      Complex.ofReal_one, one_smul] using weightedGradedTensorSymbol_bijective
        p.toLinearMap q.toLinearMap 1 1
        (hfactor.imp (fun hp ↦ ⟨one_ne_zero, hp⟩) (fun hq ↦ ⟨one_ne_zero, hq⟩))
  have hT : T.IsInvertible :=
    ⟨(LinearEquiv.ofBijective T.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩
  refine ⟨hT, ?_⟩
  apply T.inverse.opNorm_le_bound (by positivity)
  intro u
  simpa only [hT.self_apply_inverse] using hlower (T.inverse u)

end AtiyahSinger
