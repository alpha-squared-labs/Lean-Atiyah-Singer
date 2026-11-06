/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedGraphApproximation
public import AtiyahSinger.Analysis.HilbertTensorCompletion

/-!
# Strong approximation on completed Hilbert tensors

Public module ID: M0731.

Uniformly contractive strong approximations in the two factors induce a strong
approximation on the specified Hilbert tensor completion. This is the continuity
step used to regularize simultaneous unbounded factor graphs.
-/

@[expose] public noncomputable section

namespace TensorProduct

open Filter UniformSpace
open scoped TensorProduct Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The completed tensor of two strong contraction approximations converges strongly. -/
theorem tendsto_completion_mapL_of_contractions
    (f : ℕ → E →L[ℂ] E) (g : ℕ → F →L[ℂ] F)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hfx : ∀ x : E, Tendsto (fun n ↦ f n x) atTop (𝓝 x))
    (hgy : ∀ y : F, Tendsto (fun n ↦ g n y) atTop (𝓝 y))
    (u : Completion (E ⊗[ℂ] F)) :
    Tendsto (fun n ↦ (mapL (f n) (g n)).completion u) atTop (𝓝 u) := by
  let L (n : ℕ) := (mapL (f n) (g n)).completion
  have hnorm (n : ℕ) (u : Completion (E ⊗[ℂ] F)) : ‖L n u‖ ≤ ‖u‖ := by
    induction u using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih u =>
      change ‖(mapL (f n) (g n)).completion (u : Completion (E ⊗[ℂ] F))‖ ≤ _
      rw [ContinuousLinearMap.completion_apply_coe, Completion.norm_coe, Completion.norm_coe]
      calc
        ‖mapL (f n) (g n) u‖ ≤ ‖mapL (f n) (g n)‖ * ‖u‖ :=
          (mapL (f n) (g n)).le_opNorm u
        _ ≤ (‖f n‖ * ‖g n‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (norm_mapL_le _ _) (norm_nonneg _)
        _ ≤ (1 * 1) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hf n) (hg n) (norm_nonneg _) zero_le_one)
            (norm_nonneg _)
        _ = ‖u‖ := by ring
  have hclosed : IsClosed {u : Completion (E ⊗[ℂ] F) |
      Tendsto (fun n ↦ L n u) atTop (𝓝 u)} := by
    apply Equicontinuous.isClosed_setOfPred_tendsto _ continuous_id
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ 1
    intro n
    apply (L n).lipschitzWith_of_opNorm_le
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simpa only [one_mul] using hnorm n u
  -- On finite tensors use continuity of tensoring; uniform contraction passes to completion.
  refine Completion.induction_on (p := fun u ↦ Tendsto (fun n ↦ L n u) atTop (𝓝 u))
    u hclosed ?_
  intro u
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    have hc : Continuous (fun z : E × F ↦
        ((z.1 ⊗ₜ[ℂ] z.2 : E ⊗[ℂ] F) : Completion (E ⊗[ℂ] F))) := by fun_prop
    simpa only [L, ContinuousLinearMap.completion_apply_coe, mapL_tmul, Function.comp_def] using
      hc.continuousAt.tendsto.comp ((hfx x).prodMk_nhds (hgy y))
  | add u v hu hv =>
    simpa only [Completion.coe_add, _root_.map_add] using hu.add hv

end TensorProduct
