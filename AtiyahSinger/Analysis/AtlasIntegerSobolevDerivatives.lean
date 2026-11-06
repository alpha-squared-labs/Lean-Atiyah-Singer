/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSobolev
public import AtiyahSinger.Analysis.IntegerSobolevDerivatives
public import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Integer derivative integrals for the original atlas Sobolev norm

Public module ID: M0253.

The actual cutoff localizations have compact support and are Schwartz functions.
Their full Fréchet derivative operator norms characterize the original integer Fourier
norm, with one pair of positive constants for the finite varying-rank atlas.
This is the local analytic part of SG III.2, Proposition 2.14; no covariant
derivative or geometric norm comparison is assumed here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.AtlasBundlePresentation

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {A : SmoothComplexBundleAtlas (n := n) E}

/-- The original Fourier norm is equivalent to the full Fréchet derivative norms of its own cutoffs.
The constants are uniform over sections and over the finite family of local ranks. -/
theorem exists_norm_smoothToSobolev_sq_derivatives_comparison
    (L : AtlasBundlePresentation A) (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : A.smoothSections,
      c * (∑ a : Fin L.size, ∑ j : Fin (k + 1),
        ∫ z : EuclideanSpace ℝ (Fin n),
          ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z‖ ^ 2) ≤
        ‖L.smoothToSobolev (k : ℝ) u‖ ^ 2 ∧
      ‖L.smoothToSobolev (k : ℝ) u‖ ^ 2 ≤
        C * (∑ a : Fin L.size, ∑ j : Fin (k + 1),
          ∫ z : EuclideanSpace ℝ (Fin n),
            ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z‖ ^ 2) := by
  classical
  have hFourier :
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : A.smoothSections,
        c * (∑ a : Fin L.size, ∑ j : Fin (k + 1), ∑ p : Fin j.val → Fin n,
          ∫ z : EuclideanSpace ℝ (Fin n),
            ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z
              (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ))‖ ^ 2) ≤
          ‖L.smoothToSobolev (k : ℝ) u‖ ^ 2 ∧
        ‖L.smoothToSobolev (k : ℝ) u‖ ^ 2 ≤
          C * (∑ a : Fin L.size, ∑ j : Fin (k + 1), ∑ p : Fin j.val → Fin n,
            ∫ z : EuclideanSpace ℝ (Fin n),
              ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z
                (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ))‖ ^ 2) := by
    classical
    let Q (a : Fin L.size) (u : A.smoothSections) : ℝ :=
      ∑ j : Fin (k + 1), ∑ p : Fin j.val → Fin n,
        ∫ z : EuclideanSpace ℝ (Fin n),
          ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z
            (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ))‖ ^ 2
    have hQ (a : Fin L.size) (u : A.smoothSections) : 0 ≤ Q a u :=
      Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦
        integral_nonneg (fun _ ↦ sq_nonneg _)))
    -- Plancherel and the original Fourier convention apply at each actual local rank.
    have hlocal (a : Fin L.size) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ u : A.smoothSections,
          c * Q a u ≤ ‖schwartzSobolevCoordinate (k : ℝ) (L.localize a u)‖ ^ 2 ∧
          ‖schwartzSobolevCoordinate (k : ℝ) (L.localize a u)‖ ^ 2 ≤ C * Q a u := by
      obtain ⟨c, C, hc, hC, h⟩ :=
        exists_schwartzSobolevCoordinate_sq_derivatives_comparison n
          (A.rank (L.frameIndex a)) k
      have hnorm (v : 𝓢(EuclideanSpace ℝ (Fin n),
          EuclideanSpace ℂ (Fin (A.rank (L.frameIndex a))))) :
          ‖v.toLp 2‖ ^ 2 = ∫ z, ‖v z‖ ^ 2 := by
        rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
        norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
        rw [← Real.sqrt_eq_rpow]
        exact Real.sq_sqrt (integral_nonneg (fun z ↦ sq_nonneg ‖v z‖))
      refine ⟨c, C, hc, hC, fun u ↦ ?_⟩
      have hfun : ⇑(L.localize a u) = L.localizedFunction a u := rfl
      simpa only [hnorm, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
        hfun, Q] using h (L.localize a u)
    choose c C hc hC hlocal using hlocal
    -- A product of positive lower constants also handles an empty presentation.
    let c₀ : ℝ := ∏ a : Fin L.size, min 1 (c a)
    let C₀ : ℝ := 1 + ∑ a : Fin L.size, C a
    have hc₀ : 0 < c₀ := Finset.prod_pos (fun a _ ↦ lt_min zero_lt_one (hc a))
    have hC₀ : 0 < C₀ := by
      dsimp [C₀]
      exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun a _ ↦ (hC a).le))
    have hc_le (a : Fin L.size) : c₀ ≤ c a := by
      apply le_trans _ (min_le_right 1 (c a))
      have h := Finset.prod_le_prod_of_subset_of_le_one₀
        (Finset.subset_univ {a})
        (fun b _ ↦ (lt_min zero_lt_one (hc b)).le)
        (fun b _ _ ↦ min_le_left 1 (c b))
      simpa only [Finset.prod_singleton, c₀] using h
    have hC_le (a : Fin L.size) : C a ≤ C₀ := by
      have h := Finset.single_le_sum (fun b _ ↦ (hC b).le) (Finset.mem_univ a)
      dsimp [C₀]
      linarith
    refine ⟨c₀, C₀, hc₀, hC₀, fun u ↦ ?_⟩
    -- The finite Hilbert square sum is exactly the specified completion norm.
    rw [L.norm_smoothToSobolev_sq]
    change c₀ * (∑ a, Q a u) ≤ _ ∧ _ ≤ C₀ * (∑ a, Q a u)
    constructor
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a _ ↦
        (mul_le_mul_of_nonneg_right (hc_le a) (hQ a u)).trans (hlocal a u).1)
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a _ ↦ (hlocal a u).2.trans
        (mul_le_mul_of_nonneg_right (hC_le a) (hQ a u)))
  -- Finite ordered coordinate evaluations determine each multilinear derivative.
  have hjet (r j : ℕ) : ∃ d D : ℝ, 0 < d ∧ 0 < D ∧
      ∀ F : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℂ (Fin r)),
        d * ‖F‖ ^ 2 ≤ ∑ p : Fin j → Fin n,
          ‖F (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ))‖ ^ 2 ∧
        (∑ p : Fin j → Fin n,
          ‖F (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ))‖ ^ 2) ≤ D * ‖F‖ ^ 2 := by
    let V := ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℂ (Fin r))
    let W := PiLp 2 (fun _ : Fin j → Fin n ↦ EuclideanSpace ℂ (Fin r))
    let T : V →ₗ[ℝ] W := {
      toFun := fun F ↦ WithLp.toLp 2
        (fun p ↦ F (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ)))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    have hT : Function.Injective T := by
      intro F G hFG
      apply ContinuousMultilinearMap.toMultilinearMap_injective
      apply Module.Basis.ext_multilinear
        (fun _ : Fin j ↦ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
      intro p
      have h := congrArg (fun t : W ↦ t p) hFG
      change F (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ)) =
        G (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ)) at h
      simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
        ContinuousMultilinearMap.coe_coe] using h
    let : FiniteDimensional ℝ V := Module.Finite.of_injective T hT
    let Tc : V →L[ℝ] W := T.toContinuousLinearMap
    obtain ⟨B, hB, hb⟩ := T.injective_iff_antilipschitz.mp hT
    let d : ℝ := (B : ℝ)⁻¹ ^ 2
    let D : ℝ := (max ‖Tc‖ 1) ^ 2
    have hBpos : 0 < (B : ℝ) := hB
    have hDpos : 0 < max ‖Tc‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine ⟨d, D, sq_pos_of_pos (inv_pos.mpr hBpos), sq_pos_of_pos hDpos, ?_⟩
    intro F
    have hnorm : ‖T F‖ ^ 2 = ∑ p : Fin j → Fin n,
        ‖F (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ))‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 _ (T F)
    have hlo : ‖F‖ ≤ (B : ℝ) * ‖T F‖ := by
      simpa only [map_zero, dist_zero_right] using hb.le_mul_dist F 0
    have hlo' : (B : ℝ)⁻¹ * ‖F‖ ≤ ‖T F‖ := by
      exact (inv_mul_le_iff₀ hBpos).mpr hlo
    have hup : ‖T F‖ ≤ max ‖Tc‖ 1 * ‖F‖ :=
      (Tc.le_opNorm F).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg F))
    rw [← hnorm]
    constructor
    · dsimp only [d]
      simpa only [mul_pow] using
        pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hBpos.le) (norm_nonneg F)) hlo' 2
    · dsimp only [D]
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (T F)) hup 2
  obtain ⟨c, C, hc, hC, hFourier⟩ := hFourier
  let I := Fin L.size × Fin (k + 1)
  choose d D hd hD hjet using
    (fun t : I ↦ hjet (A.rank (L.frameIndex t.1)) t.2.val)
  let d₀ : ℝ := ∏ t : I, min 1 (d t)
  let D₀ : ℝ := 1 + ∑ t : I, D t
  have hd₀ : 0 < d₀ := Finset.prod_pos (fun t _ ↦ lt_min zero_lt_one (hd t))
  have hD₀ : 0 < D₀ := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun t _ ↦ (hD t).le))
  have hd_le (t : I) : d₀ ≤ d t := by
    apply le_trans _ (min_le_right 1 (d t))
    have h := Finset.prod_le_prod_of_subset_of_le_one₀
      (Finset.subset_univ {t})
      (fun s _ ↦ (lt_min zero_lt_one (hd s)).le)
      (fun s _ _ ↦ min_le_left 1 (d s))
    simpa only [Finset.prod_singleton, d₀] using h
  have hD_le (t : I) : D t ≤ D₀ := by
    have h := Finset.single_le_sum (fun s _ ↦ (hD s).le) (Finset.mem_univ t)
    dsimp [D₀]
    linarith
  let Q (u : A.smoothSections) : ℝ :=
    ∑ a : Fin L.size, ∑ j : Fin (k + 1),
      ∫ z : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z‖ ^ 2
  let R (u : A.smoothSections) : ℝ :=
    ∑ a : Fin L.size, ∑ j : Fin (k + 1), ∑ p : Fin j.val → Fin n,
      ∫ z : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z
          (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ))‖ ^ 2
  -- The original compact support controls all derivative integrals, including order zero.
  have hop_int (u : A.smoothSections) (a : Fin L.size) (j : Fin (k + 1)) :
      Integrable (fun z : EuclideanSpace ℝ (Fin n) ↦
        ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z‖ ^ 2) := by
    have hf := L.localizedFunction_properties a u
    have hc := hf.1.continuous_iteratedFDeriv (show (j.val : WithTop ℕ∞) ≤ ∞ by simp)
    have hs := (hf.2.2.iteratedFDeriv (𝕜 := ℝ) j.val).norm
    simpa only [Pi.mul_def, pow_two] using
      (hc.norm.mul hc.norm).integrable_of_hasCompactSupport (μ := volume) hs.mul_right
  have hcoord_int (u : A.smoothSections) (a : Fin L.size) (j : Fin (k + 1))
      (p : Fin j.val → Fin n) :
      Integrable (fun z : EuclideanSpace ℝ (Fin n) ↦
        ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z
          (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ))‖ ^ 2) := by
    have hi := ((LineDeriv.iteratedLineDerivOp
      (fun b ↦ EuclideanSpace.single (p b) (1 : ℝ)) (L.localize a u)).memLp 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
      |>.integrable_norm_pow (show (2 : ℕ) ≠ 0 by decide)
    have hfun : ⇑(L.localize a u) = L.localizedFunction a u := rfl
    simpa only [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, hfun] using hi
  have hcompare (u : A.smoothSections) : d₀ * Q u ≤ R u ∧ R u ≤ D₀ * Q u := by
    dsimp only [Q, R]
    constructor
    · simp_rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro j _
      rw [← integral_finsetSum _ (fun p _ ↦ hcoord_int u a j p), ← integral_const_mul]
      apply integral_mono ((hop_int u a j).const_mul d₀)
        (integrable_finsetSum _ (fun p _ ↦ hcoord_int u a j p))
      intro z
      exact (mul_le_mul_of_nonneg_right (hd_le (a, j)) (sq_nonneg _)).trans
        (hjet (a, j) (iteratedFDeriv ℝ j.val (L.localizedFunction a u) z)).1
    · simp_rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro j _
      rw [← integral_finsetSum _ (fun p _ ↦ hcoord_int u a j p), ← integral_const_mul]
      apply integral_mono (integrable_finsetSum _ (fun p _ ↦ hcoord_int u a j p))
        ((hop_int u a j).const_mul D₀)
      intro z
      exact (hjet (a, j) (iteratedFDeriv ℝ j.val (L.localizedFunction a u) z)).2.trans
        (mul_le_mul_of_nonneg_right (hD_le (a, j)) (sq_nonneg _))
  refine ⟨c * d₀, C * D₀, mul_pos hc hd₀, mul_pos hC hD₀, fun u ↦ ?_⟩
  change (c * d₀) * Q u ≤ _ ∧ _ ≤ (C * D₀) * Q u
  constructor
  · calc
      (c * d₀) * Q u = c * (d₀ * Q u) := mul_assoc _ _ _
      _ ≤ c * R u := mul_le_mul_of_nonneg_left (hcompare u).1 hc.le
      _ ≤ _ := (hFourier u).1
  · calc
      _ ≤ C * R u := (hFourier u).2
      _ ≤ C * (D₀ * Q u) := mul_le_mul_of_nonneg_left (hcompare u).2 hC.le
      _ = (C * D₀) * Q u := (mul_assoc _ _ _).symm

end AtiyahSinger.AtlasBundlePresentation
