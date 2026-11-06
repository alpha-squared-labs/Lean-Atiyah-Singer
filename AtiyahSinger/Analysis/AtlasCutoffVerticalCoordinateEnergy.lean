/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ProductFiberH1Energy
public import AtiyahSinger.Analysis.SmoothSectionFamilyL2Coordinates
public import AtiyahSinger.Analysis.NativeAtlasSobolev
public import AtiyahSinger.Analysis.AtlasSobolevLocalization

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Arbitrary original cutoff energy controlled by native whole-fiber H¹

Public module ID: M0237.

The supplied joint Schwartz coordinates agree with the original finite tensor
rows of an arbitrary given atlas cutoff. Exact row-slice energy and the
original Sobolev norm then bound every right-coordinate derivative by the same
whole-fiber H¹ family. The coordinate concatenation, native presentation and
Fourier normalization are retained. No estimate or replacement family is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
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

/-- Any fixed atlas cutoff retains vertical row energy control by the native family norm. -/
theorem exists_atlasCutoff_vertical_energy_le_family_sobolev {m a : ℕ}
    (L : SmoothBundlePresentation (n := n) (r := r) E)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ D : AtlasChartCutoff (nativeSmoothComplexBundleAtlas (n := n) (r := r) E) c,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (u : (Fin m → ℝ) → Fin a → smoothSections (n := n) (r := r) E)
          (hu : ∀ i : Fin a,
            MemLp (fun x ↦ L.smoothToSobolev 1 (u x i)) 2
              (volume : Measure (Fin m → ℝ)))
          (v : 𝓢(EuclideanSpace ℝ (Fin (m + n)), EuclideanSpace ℂ (Fin (a * r)))),
          (∀ i x y l, D.localize hc
            ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm (u x i)) y l =
              v (EuclideanSpace.finAddEquivProd.symm
                ((EuclideanSpace.equiv (Fin m) ℝ).symm x, y)) (finProdFinEquiv (i, l))) →
          ‖v.toLp 2‖ ^ 2 + ∑ l : Fin n,
              ‖(LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd m l) (1 : ℝ))
                v).toLp 2‖ ^ 2 ≤
            C * ∑ i : Fin a,
              ‖(hu i).toLp (fun x ↦ L.smoothToSobolev 1 (u x i))‖ ^ 2 := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro D
  let e := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
  -- The exact original cutoff is bounded in the unchanged native Hilbert completion.
  obtain ⟨B, hB, hbound⟩ := D.exists_norm_localize_sobolev_le hc
    L.toAtlasBundlePresentation 1
  have hpoint (w : smoothSections (n := n) (r := r) E) :
      ‖schwartzSobolevCoordinate 1 (D.localize hc (e.symm w))‖ ^ 2 ≤
        B ^ 2 * ‖L.smoothToSobolev 1 w‖ ^ 2 := by
    have hb := hbound (e.symm w)
    rw [← L.nativeAtlasSobolevEquiv_smoothToSobolev 1 w,
      (L.nativeAtlasSobolevEquiv 1).norm_map] at hb
    exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq (mul_pow _ _ 2)
  refine ⟨(1 + (2 * Real.pi) ^ 2) * B ^ 2, by positivity, ?_⟩
  intro u hu v hcoords
  let X := EuclideanSpace ℝ (Fin m)
  let Xp := Fin m → ℝ
  let ex := EuclideanSpace.equiv (Fin m) ℝ
  let f (i : Fin a) (x : X) := D.localize hc (e.symm (u (ex x) i))
  have hf (i : Fin a) (x : X) (y : EuclideanSpace ℝ (Fin n)) (l : Fin r) :
      f i x y l = v (EuclideanSpace.finAddEquivProd.symm (x, y))
        (finProdFinEquiv (i, l)) := by
    have h := hcoords i (ex x) y l
    change f i x y l =
      v (EuclideanSpace.finAddEquivProd.symm (ex.symm (ex x), y))
        (finProdFinEquiv (i, l)) at h
    rw [ex.symm_apply_apply] at h
    exact h
  have henergy := norm_vertical_energy_eq_sum_integral_fiber v f hf
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
  -- Integrate the actual rows; no membership in a preferred finite presentation is needed.
  have hrow (i : Fin a) : (∫ x : X, ‖schwartzSobolevCoordinate 1 (f i x)‖ ^ 2) ≤
      B ^ 2 * ‖(hu i).toLp (fun x ↦ L.smoothToSobolev 1 (u x i))‖ ^ 2 := by
    have hi := (hu i).integrable_norm_pow (by norm_num)
    calc
      _ ≤ ∫ x : X, B ^ 2 * ‖L.smoothToSobolev 1 (u (ex x) i)‖ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
          ((hex.integrable_comp_of_integrable hi).const_mul (B ^ 2))
          (Filter.Eventually.of_forall (fun x ↦ hpoint (u (ex x) i)))
      _ = B ^ 2 * ∫ x : Xp, ‖L.smoothToSobolev 1 (u x i)‖ ^ 2 := by
        rw [integral_const_mul]
        exact congrArg (fun z : ℝ ↦ B ^ 2 * z)
          (hex'.integral_comp' (fun x ↦ ‖L.smoothToSobolev 1 (u x i)‖ ^ 2))
      _ = _ := congrArg (fun z : ℝ ↦ B ^ 2 * z) (hfamily i).symm
  have hweighted := henergy.trans_le (Finset.sum_le_sum (fun i _ ↦ hrow i))
  rw [← Finset.mul_sum] at hweighted
  -- Retain the period-one Fourier normalization when removing the derivative weights.
  have hscalar (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      x + y ≤ (1 + (2 * Real.pi) ^ 2) * (x + (2 * Real.pi)⁻¹ ^ 2 * y) := by
    have hc : (2 * Real.pi) ^ 2 * ((2 * Real.pi)⁻¹ ^ 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero), one_pow]
    have hnonneg := add_nonneg (mul_nonneg (sq_nonneg (2 * Real.pi)) hx)
      (mul_nonneg (sq_nonneg ((2 * Real.pi)⁻¹)) hy)
    nlinarith [congrArg (fun z : ℝ ↦ z * y) hc]
  have hresult := (hscalar _ _ (sq_nonneg _)
    (Finset.sum_nonneg (fun l _ ↦ sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hweighted (by positivity))
  exact hresult.trans_eq (mul_assoc _ _ _).symm

end SmoothBundlePresentation

end AtiyahSinger
