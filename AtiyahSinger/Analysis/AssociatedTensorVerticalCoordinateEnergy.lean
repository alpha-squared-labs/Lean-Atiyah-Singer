/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ProductFiberH1Energy
public import AtiyahSinger.Analysis.SmoothSectionFamilyL2Coordinates

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual vertical chart energy controlled by native whole-fiber H¹

Public module ID: M0195.

The supplied joint Schwartz coordinates agree with the original finite tensor
rows of the given native fiber localization. Exact row-slice energy and the
original Sobolev norm then bound every right-coordinate derivative by the same
whole-fiber H¹ family. The coordinate concatenation, native presentation and
Fourier normalization are retained. No estimate or replacement family is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff Topology SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1000000 in

/-- Native whole-fiber H¹ controls the original right-coordinate Schwartz energy. -/
theorem vertical_energy_le_family_sobolev {m a : ℕ}
    (L : SmoothBundlePresentation (n := n) (r := r) E)
    (u : (Fin m → ℝ) → Fin a → smoothSections (n := n) (r := r) E)
    (hu : ∀ i : Fin a,
      MemLp (fun x ↦ L.smoothToSobolev 1 (u x i)) 2 (volume : Measure (Fin m → ℝ)))
    (j : Fin L.size)
    (v : 𝓢(EuclideanSpace ℝ (Fin (m + n)), EuclideanSpace ℂ (Fin (a * r))))
    (hcoords : ∀ i x y l, L.localize j (u x i) y l =
      v (EuclideanSpace.finAddEquivProd.symm
        ((EuclideanSpace.equiv (Fin m) ℝ).symm x, y)) (finProdFinEquiv (i, l))) :
    ‖v.toLp 2‖ ^ 2 + ∑ l : Fin n,
        ‖(LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd m l) (1 : ℝ))
          v).toLp 2‖ ^ 2 ≤
      (1 + (2 * Real.pi) ^ 2) * ∑ i : Fin a,
        ‖(hu i).toLp (fun x ↦ L.smoothToSobolev 1 (u x i))‖ ^ 2 := by
  classical
  let X := EuclideanSpace ℝ (Fin m)
  let Xp := Fin m → ℝ
  let ex := EuclideanSpace.equiv (Fin m) ℝ
  let f (i : Fin a) (x : X) := L.localize j (u (ex x) i)
  have hf (i : Fin a) (x : X) (y : EuclideanSpace ℝ (Fin n)) (l : Fin r) :
      f i x y l = v (EuclideanSpace.finAddEquivProd.symm (x, y))
        (finProdFinEquiv (i, l)) := by
    change L.localize j (u (ex x) i) y l = _
    have h := hcoords i (ex x) y l
    change L.localize j (u (ex x) i) y l =
      v (EuclideanSpace.finAddEquivProd.symm (ex.symm (ex x), y))
        (finProdFinEquiv (i, l)) at h
    rw [ex.symm_apply_apply] at h
    exact h
  have henergy := norm_vertical_energy_eq_sum_integral_fiber v f hf
  -- The actual native H¹ norm is the sum over its original localized Bessel norms.
  have hpoint (i : Fin a) (x : X) :
      ‖schwartzSobolevCoordinate 1 (f i x)‖ ^ 2 ≤ ‖L.smoothToSobolev 1 (u (ex x) i)‖ ^ 2 := by
    rw [L.norm_smoothToSobolev_sq]
    exact Finset.single_le_sum (fun k _ ↦ sq_nonneg
      ‖schwartzSobolevCoordinate 1 (L.localize k (u (ex x) i))‖) (Finset.mem_univ j)
  have hex : MeasurePreserving ex := PiLp.volume_preserving_ofLp (Fin m)
  have hex' : MeasurePreserving ex.toHomeomorph.toMeasurableEquiv
      (volume : Measure X) (volume : Measure Xp) := hex
  have hfamily (i : Fin a) :
      ‖(hu i).toLp (fun x ↦ L.smoothToSobolev 1 (u x i))‖ ^ 2 =
        ∫ x : Xp, ‖L.smoothToSobolev 1 (u x i)‖ ^ 2 := by
    let : InnerProductSpace ℝ (L.SobolevSpace 1) :=
      InnerProductSpace.rclikeToReal ℂ (L.SobolevSpace 1)
    let g := (hu i).toLp (fun x ↦ L.smoothToSobolev 1 (u x i))
    calc
      ‖g‖ ^ 2 = inner ℝ g g := (real_inner_self_eq_norm_sq _).symm
      _ = ∫ x : Xp, ‖g x‖ ^ 2 := by
        simp only [L2.inner_def, real_inner_self_eq_norm_sq]
        rfl
      _ = _ := integral_congr_ae (by
        filter_upwards [(hu i).coeFn_toLp] with x hx
        exact congrArg (fun w ↦ ‖w‖ ^ 2) hx)
  have hrow (i : Fin a) : (∫ x : X, ‖schwartzSobolevCoordinate 1 (f i x)‖ ^ 2) ≤
      ‖(hu i).toLp (fun x ↦ L.smoothToSobolev 1 (u x i))‖ ^ 2 := by
    have hi := (hu i).integrable_norm_pow (by norm_num)
    calc
      _ ≤ ∫ x : X, ‖L.smoothToSobolev 1 (u (ex x) i)‖ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
          (hex.integrable_comp_of_integrable hi) (Filter.Eventually.of_forall (hpoint i))
      _ = ∫ x : Xp, ‖L.smoothToSobolev 1 (u x i)‖ ^ 2 :=
        hex'.integral_comp' (fun x ↦ ‖L.smoothToSobolev 1 (u x i)‖ ^ 2)
      _ = _ := (hfamily i).symm
  have hweighted := henergy.trans_le (Finset.sum_le_sum (fun i _ ↦ hrow i))
  -- Convert the original period-one Fourier energy to the unweighted derivative energy.
  have hscalar (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      x + y ≤ (1 + (2 * Real.pi) ^ 2) * (x + (2 * Real.pi)⁻¹ ^ 2 * y) := by
    have hc : (2 * Real.pi) ^ 2 * ((2 * Real.pi)⁻¹ ^ 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero), one_pow]
    have hnonneg := add_nonneg (mul_nonneg (sq_nonneg (2 * Real.pi)) hx)
      (mul_nonneg (sq_nonneg ((2 * Real.pi)⁻¹)) hy)
    nlinarith [congrArg (fun z : ℝ ↦ z * y) hc]
  exact (hscalar _ _ (sq_nonneg _) (Finset.sum_nonneg (fun l _ ↦ sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hweighted (by positivity))

end SmoothBundlePresentation

end AtiyahSinger
