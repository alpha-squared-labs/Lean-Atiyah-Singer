/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Symbol
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.LinearAlgebra.Quotient.Defs

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The symbol filtration and principal symbol quotient

Public module ID: M1027.

D05 and local prerequisites for A02/A03. SG III.3.13 defines the principal symbol
as a class in the complex module quotient S^m / S^(m-1).
Composition below is pointwise composition of symbol matrices, descended to the
quotient. Its comparison with composition of quantized operators requires SG 3.5
and 3.10 and is not asserted here. No full polyhomogeneous expansion is required.

Symbols are total functions with estimates only over the open set U. Values outside
U have no effect on the quotient, since a symbol vanishing over U has every order.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff Topology

-- The quotient sits over a submodule of functions valued in continuous linear maps.
set_option maxSynthPendingDepth 10

/-- The ambient matrix-valued functions in a Euclidean bundle chart. -/
abbrev SymbolFunction (n r q : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
    (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))

variable {n r q k : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} {m l : ℝ}

/-- The zero symbol has every real order. -/
theorem isSymbol_zero (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℝ) :
    IsSymbol U m (0 : SymbolFunction n r q) := by
  /- All mixed derivatives of zero vanish, including the zeroth derivative.
  Its joint smoothness is immediate and the constant C = 0 gives every estimate. -/
  constructor
  · exact contDiffOn_const
  · intro K hK hcompact i j
    refine ⟨0, le_rfl, ?_⟩
    intro x hx ξ
    simp [symbolDerivative]

/-- The fixed-order symbol class is closed under addition on an open domain. -/
theorem IsSymbol.add (hU : IsOpen U) {a b : SymbolFunction n r q}
    (ha : IsSymbol U m a) (hb : IsSymbol U m b) : IsSymbol U m (a + b) := by
  /- Stage 1: openness turns joint smoothness on U into local smoothness at each point.
  Differentiate the sum there; this matters because symbolDerivative uses total derivatives.
  Stage 2: the triangle inequality bounds each derivative by the sum of its two constants. -/
  have hparametric {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
      (f : P → Q → R) (x : P) (y : Q)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (j : ℕ) :
      ContDiffAt ℝ ∞ (fun p : P × Q ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, y) := by
    -- Parameter differentiation remains smooth; each step differentiates and uncurries once.
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Q R).symm : _ →L[ℝ] Q [×0]→L[ℝ] R)
    | succ j ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun p : P × Q ↦ fun z : Q ↦ iteratedFDeriv ℝ j (f p.1) z))
          ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun p : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, y) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ Q) R).symm :
          _ →L[ℝ] Q [×(j + 1)]→L[ℝ] R)
  have hfg (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ (Function.uncurry a) (x, ξ) ∧
        ContDiffAt ℝ ∞ (Function.uncurry b) (x, ξ) :=
    ⟨ha.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ ξ⟩),
      hb.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ ξ⟩)⟩
  -- Differentiate first in frequency and then in the spatial variable on the same open domain.
  have hder (i j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) :
      symbolDerivative (a + b) i j x ξ =
        symbolDerivative a i j x ξ + symbolDerivative b i j x ξ := by
    have hnear : (fun y ↦ iteratedFDeriv ℝ j ((a + b) y) ξ) =ᶠ[𝓝 x]
        (fun y ↦ iteratedFDeriv ℝ j (a y) ξ + iteratedFDeriv ℝ j (b y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_add_apply
        (((hfg y hy ξ).1.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
        (((hfg y hy ξ).2.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hf := (hparametric a x ξ (hfg x hx ξ).1 j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    have hg := (hparametric b x ξ (hfg x hx ξ).2 j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hnear.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_add_apply (hf.of_le (by simp)) (hg.of_le (by simp)))
  refine ⟨ha.1.add hb.1, ?_⟩
  intro K hK hcompact i j
  obtain ⟨C, hC, haC⟩ := ha.2 K hK hcompact i j
  obtain ⟨D, hD, hbD⟩ := hb.2 K hK hcompact i j
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro x hx ξ
  rw [hder i j x (hK hx) ξ, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (haC x hx ξ) (hbD x hx ξ))

/-- Complex scalar multiplication preserves real smoothness and the symbol order. -/
theorem IsSymbol.smul (hU : IsOpen U) (c : ℂ) {a : SymbolFunction n r q}
    (ha : IsSymbol U m a) : IsSymbol U m (c • a) := by
  /- Multiplication by c is a continuous real-linear map of the matrix space.
  Commute it with all mixed derivatives on the open domain and multiply each
  nonnegative seminorm bound by the nonnegative number norm(c). -/
  have hparametric {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
      (f : P → Q → R) (x : P) (y : Q)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (j : ℕ) :
      ContDiffAt ℝ ∞ (fun p : P × Q ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, y) := by
    -- Parameter differentiation remains smooth; each step differentiates and uncurries once.
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Q R).symm : _ →L[ℝ] Q [×0]→L[ℝ] R)
    | succ j ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun p : P × Q ↦ fun z : Q ↦ iteratedFDeriv ℝ j (f p.1) z))
          ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun p : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, y) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ Q) R).symm :
          _ →L[ℝ] Q [×(j + 1)]→L[ℝ] R)
  have hf (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ (Function.uncurry a) (x, ξ) :=
    ha.1.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ ξ⟩)
  -- The complex scalar is constant, and hence acts real-linearly through both derivatives.
  have hder (i j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) :
      symbolDerivative (c • a) i j x ξ = c • symbolDerivative a i j x ξ := by
    have hnear : (fun y ↦ iteratedFDeriv ℝ j ((c • a) y) ξ) =ᶠ[𝓝 x]
        (fun y ↦ c • iteratedFDeriv ℝ j (a y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_const_smul_apply (a := c)
        (((hf y hy ξ).comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hparam := (hparametric a x ξ (hf x hx ξ) j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    exact ((hnear.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_const_smul_apply (a := c) (hparam.of_le (by simp)))
  refine ⟨ha.1.const_smul c, ?_⟩
  intro K hK hcompact i j
  obtain ⟨C, hC, haC⟩ := ha.2 K hK hcompact i j
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, ?_⟩
  intro x hx ξ
  rw [hder i j x (hK hx) ξ, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (haC x hx ξ) (norm_nonneg c)

/-- Increasing the allowed order weakens the estimates. -/
theorem IsSymbol.mono {a : SymbolFunction n r q} (ha : IsSymbol U m a)
    (hml : m ≤ l) : IsSymbol U l a := by
  /- The weight 1 + norm(ξ) is at least one. Monotonicity of its real powers
  compares exponents m-j and l-j for every derivative order j; keep the same constants
  and the unchanged joint smoothness condition. No openness is needed for this step. -/
  refine ⟨ha.1, ?_⟩
  intro K hK hcompact i j
  obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact i j
  refine ⟨C, hC, ?_⟩
  intro x hx ξ
  -- The unchanged constant still works because every frequency weight has base at least one.
  exact (hbound x hx ξ).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (norm_nonneg ξ))
      (sub_le_sub_right hml j)) hC)

/-- The standard complex vector space S^m_(1,0)(U; Hom(ℂ^r, ℂ^q)). -/
def symbolSpace (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (r q : ℕ) : Submodule ℂ (SymbolFunction n r q) where
  carrier := {a | IsSymbol U m a}
  zero_mem' := isSymbol_zero U m
  add_mem' := fun ha hb ↦ ha.add hU hb
  smul_mem' := fun c _ ha ↦ ha.smul hU c

/-- The symbol spaces form the usual increasing real-order filtration. -/
theorem symbolSpace_mono (hU : IsOpen U) (hml : m ≤ l) :
    symbolSpace U hU m r q ≤ symbolSpace U hU l r q := by
  /- Unpack membership as the symbol estimates. The preceding order comparison
  sends every symbol of order m to one of order l without changing its actual function. -/
  intro a ha
  -- Inclusion changes only the allowed growth order, retaining the same total symbol function.
  exact IsSymbol.mono ha hml

/-- Symbols of one lower order, as a submodule of the given order-m symbol space. -/
def lowerOrderSymbols (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (r q : ℕ) : Submodule ℂ (symbolSpace U hU m r q) :=
  (symbolSpace U hU (m - 1) r q).comap (symbolSpace U hU m r q).subtype

/-- SG Definition 3.13: the actual quotient S^m / S^(m-1). -/
abbrev PrincipalSymbolSpace (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (r q : ℕ) : Type :=
  (symbolSpace U hU m r q) ⧸ lowerOrderSymbols U hU m r q

/-- The canonical complex-linear projection from symbols to principal symbol classes. -/
def principalSymbolClass (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (r q : ℕ) :
    symbolSpace U hU m r q →ₗ[ℂ] PrincipalSymbolSpace U hU m r q :=
  (lowerOrderSymbols U hU m r q).mkQ

/-- Equality of principal classes means precisely one-order decay of their difference. -/
theorem principalSymbolClass_eq_iff (hU : IsOpen U)
    (a b : symbolSpace U hU m r q) :
    principalSymbolClass U hU m r q a = principalSymbolClass U hU m r q b ↔
      IsSymbol U (m - 1) (a.val - b.val) := by
  /- Apply the module quotient equality criterion: the difference lies in the denominator.
  Unfold the comap along the subtype map; its membership is exactly the stated
  lower-order symbol estimate for the difference of the two actual matrix functions. -/
  -- Equality in this exact quotient is membership of the actual difference in its denominator.
  exact Submodule.Quotient.eq (lowerOrderSymbols U hU m r q)

/-- The kernel of the principal class projection consists exactly of lower-order symbols. -/
theorem principalSymbolClass_eq_zero_iff (hU : IsOpen U)
    (a : symbolSpace U hU m r q) :
    principalSymbolClass U hU m r q a = 0 ↔ IsSymbol U (m - 1) a.val := by
  /- The kernel of a quotient projection is its denominator submodule.
  Here the denominator is the comap of S^(m-1), so membership tests the original
  symbol function and imposes no additional ellipticity or homogeneity requirement. -/
  -- The denominator is the comap of the original lower-order class along the subtype map.
  exact Submodule.Quotient.mk_eq_zero (p := lowerOrderSymbols U hU m r q)

/-- Every local principal class has an actual symbol representative. -/
theorem principalSymbolClass_surjective (hU : IsOpen U) (m : ℝ) :
    Function.Surjective (principalSymbolClass U hU m r q) := by
  /- Use the surjectivity of the canonical module quotient map.
  This chooses an arbitrary S^m representative, not a homogeneous representative:
  general S^m symbols need not have a homogeneous leading term. -/
  -- Quotient representatives are genuine order-m symbols, with no homogeneity assumption.
  exact (lowerOrderSymbols U hU m r q).mkQ_surjective

/-- A smooth symbol function with uniformly bounded frequency support has every order. -/
theorem isSmoothingSymbol_of_frequency_support (hU : IsOpen U)
    (a : SymbolFunction n r q) (R : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ Set.univ))
    (hsupp : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → a x ξ = 0) : IsSmoothingSymbol U a := by
  /- Stage 1: outside a slightly larger closed frequency ball, the function and all
  derivatives vanish locally. Openness of U justifies the derivatives used here.
  Stage 2: on each compact K times that ball, every derivative is bounded by continuity.
  Every real power of 1 + norm(ξ) has a positive minimum on the ball, so absorb
  its reciprocal into the derivative bound to obtain any prescribed symbol order. -/
  have hparametric {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
      (f : P → Q → R) (x : P) (y : Q)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (j : ℕ) :
      ContDiffAt ℝ ∞ (fun p : P × Q ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, y) := by
    -- Parameter differentiation remains smooth; each step differentiates and uncurries once.
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Q R).symm : _ →L[ℝ] Q [×0]→L[ℝ] R)
    | succ j ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun p : P × Q ↦ fun z : Q ↦ iteratedFDeriv ℝ j (f p.1) z))
          ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun p : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, y) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ Q) R).symm :
          _ →L[ℝ] Q [×(j + 1)]→L[ℝ] R)
  intro order
  refine ⟨hsmooth, ?_⟩
  intro K hK hcompact i j
  let B : ℝ := max R 0 + 1
  -- Off a larger frequency ball the symbol is locally zero in both variables.
  have hderzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : B < ‖ξ‖) :
      symbolDerivative a i j x ξ = 0 := by
    have hR : R < ‖ξ‖ := by
      dsimp [B] at hξ
      linarith [le_max_left R 0]
    have hinner (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
        iteratedFDeriv ℝ j (a y) ξ = 0 := by
      have hnear : a y =ᶠ[𝓝 ξ] 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hR] with ζ hζ
        exact hsupp y hy ζ (le_of_lt hζ)
      simpa only [iteratedFDeriv_zero, Pi.zero_apply] using
        (hnear.iteratedFDeriv ℝ j).eq_of_nhds
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hinner y hy
    simpa only [symbolDerivative, iteratedFDeriv_zero, Pi.zero_apply] using
      (hnear.iteratedFDeriv ℝ i).eq_of_nhds
  -- On the compact product, joint smoothness controls the actual weighted mixed derivative.
  have hcont : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        ‖symbolDerivative a i j p.1 p.2‖ / (1 + ‖p.2‖) ^ (order - (j : ℝ)))
      (K ×ˢ Metric.closedBall 0 B) := by
    intro p hp
    have hfp : ContDiffAt ℝ ∞ (Function.uncurry a) p :=
      hsmooth.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hK hp.1, Set.mem_univ p.2⟩)
    have hξ := hparametric a p.1 p.2 hfp j
    have hswap : ContDiffAt ℝ ∞
        (Function.uncurry (fun ξ x ↦ iteratedFDeriv ℝ j (a x) ξ)) (p.2, p.1) :=
      hξ.comp (p.2, p.1) (contDiffAt_snd.prodMk contDiffAt_fst)
    have hx := hparametric _ p.2 p.1 hswap i
    have hnorm := ((hx.comp p (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt.norm)
    have hbase : Continuous
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦ (1 : ℝ) + ‖p.2‖) :=
      continuous_const.add continuous_snd.norm
    have hweight : ContinuousAt
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          (1 + ‖p.2‖) ^ (order - (j : ℝ))) p :=
      hbase.continuousAt.rpow_const (Or.inl (ne_of_gt (by positivity)))
    exact (hnorm.div hweight (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))
      |>.continuousWithinAt
  have hprod := hcompact.prod (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) B)
  obtain ⟨C, hC⟩ := (hprod.image_of_continuousOn hcont).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx ξ
  by_cases hξ : ‖ξ‖ ≤ B
  · have hmem : ξ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) B := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hξ
    have hbound := hC ⟨(x, ξ), ⟨hx, hmem⟩, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mp
      (hbound.trans (le_max_left C 0))
  · rw [hderzero x (hK hx) ξ (lt_of_not_ge hξ), norm_zero]
    exact mul_nonneg (le_max_right C 0) (Real.rpow_nonneg (by positivity) _)

/-- Changing a representative only at bounded frequencies does not change its class. -/
theorem principalSymbolClass_eq_of_eq_high_frequency (hU : IsOpen U)
    (a b : symbolSpace U hU m r q) (R : ℝ)
    (hab : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → a.val x ξ = b.val x ξ) :
    principalSymbolClass U hU m r q a = principalSymbolClass U hU m r q b := by
  /- The difference is jointly smooth over U and vanishes at all sufficiently large
  frequencies. The preceding compact-frequency argument makes it smoothing,
  hence in particular of order m-1, which is precisely equality in the quotient. -/
  -- The same difference is smooth and has uniformly bounded frequency support over U.
  apply (principalSymbolClass_eq_iff hU a b).mpr
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry (a.val - b.val)) (U ×ˢ Set.univ) :=
    a.property.1.sub b.property.1
  have hsupport : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → (a.val - b.val) x ξ = 0 := by
    intro x hx ξ hξ
    exact sub_eq_zero.mpr (hab x hx ξ hξ)
  exact isSmoothingSymbol_of_frequency_support hU (a.val - b.val) R hsmooth hsupport (m - 1)

/-- Pointwise composition, with the same order of factors as operator composition. -/
def symbolComp (b : SymbolFunction n q k) (a : SymbolFunction n r q) :
    SymbolFunction n r k := fun x ξ ↦ (b x ξ).comp (a x ξ)

/-- Pointwise composition adds symbol orders for rectangular matrix symbols. -/
theorem IsSymbol.symbolComp (hU : IsOpen U) {a : SymbolFunction n r q}
    {b : SymbolFunction n q k} (hb : IsSymbol U l b) (ha : IsSymbol U m a) :
    IsSymbol U (l + m) (symbolComp b a) := by
  /- Stage 1: composition of matrices is a continuous bilinear operation, so the
  composition is jointly real smooth. Apply the mixed Leibniz rule on the open domain.
  Stage 2: split the j frequency derivatives between the factors. Each summand has
  weight (1+norm(ξ))^(l-j₁+m-j₂), where j₁+j₂=j. The finitely many constants
  and combinatorial factors are absorbed into a single constant for each compact K. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  -- Mixed derivatives are controlled by frequency induction and spatial Leibniz bounds.
  let mixed {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  -- Parameter differentiation retains smooth dependence on both original variables.
  have parametric {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (x ξ : P)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ)) (j : ℕ) :
      ContDiffAt ℝ ∞ (fun p : P × P ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, ξ) := by
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ P V).symm : _ →L[ℝ] P [×0]→L[ℝ] V)
    | succ j ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun p : P × P ↦ fun z : P ↦ iteratedFDeriv ℝ j (f p.1) z))
          ((x, ξ), ξ) := ih.comp ((x, ξ), ξ) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun p : P × P ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, ξ) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ P) V).symm :
          _ →L[ℝ] P [×(j + 1)]→L[ℝ] V)
  -- Currying is an isometry, so differentiating once in frequency lowers the order exactly once.
  have mixed_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have mixed_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i : ℕ) (x ξ : P) :
      ‖mixed f i 0 x ξ‖ = ‖iteratedFDeriv ℝ i (fun y ↦ f y ξ) x‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ 0 (f y) ξ) =
        (continuousMultilinearCurryFin0 ℝ P V).symm ∘ (fun y ↦ f y ξ) := by
      rfl
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have smooth_frequency_derivative {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {U : Set P} (hU : IsOpen U) (f : P → P → V)
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Set.univ)) :
      ContDiffOn ℝ ∞ (fun p : P × P ↦ fderiv ℝ (f p.1) p.2) (U ×ˢ Set.univ) := by
    intro p hp
    have hf' := hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds hp)
    have h : ContDiffAt ℝ ∞
        (Function.uncurry (fun z : P × P ↦ fun η : P ↦ f z.1 η)) (p, p.2) :=
      hf'.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact (h.fderiv contDiffAt_snd (by simp)).contDiffWithinAt
  have mixed_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {U : Set P} (hU : IsOpen U) (f g : P → P → V)
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Set.univ))
      (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ Set.univ))
      (i j : ℕ) (x ξ : P) (hx : x ∈ U) :
      mixed (fun y η ↦ f y η + g y η) i j x ξ =
        mixed f i j x ξ + mixed g i j x ξ := by
    have hlocal (y η : P) (hy : y ∈ U) :
        ContDiffAt ℝ ∞ (Function.uncurry f) (y, η) ∧
          ContDiffAt ℝ ∞ (Function.uncurry g) (y, η) :=
      ⟨hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, Set.mem_univ η⟩),
        hg.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, Set.mem_univ η⟩)⟩
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ f y η + g y η) ξ) =ᶠ[𝓝 x]
        (fun y ↦ iteratedFDeriv ℝ j (f y) ξ + iteratedFDeriv ℝ j (g y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_add_apply
        (((hlocal y ξ hy).1.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
        (((hlocal y ξ hy).2.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hf' := (parametric f x ξ (hlocal x ξ hx).1 j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    have hg' := (parametric g x ξ (hlocal x ξ hx).2 j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    exact ((heq.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_add_apply (hf'.of_le (by simp)) (hg'.of_le (by simp)))
  -- Induct on frequency order for arbitrary bilinear targets, including derivative spaces.
  have mixed_bilinear_estimate (j : ℕ) {U K : Set P} (hU : IsOpen U) (hKU : K ⊆ U) :
      ∀ {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
        (B : V →L[ℝ] W →L[ℝ] Z) (f : P → P → V) (g : P → P → W) (l m : ℝ),
        ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Set.univ) →
        ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ Set.univ) →
        (∀ i k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixed f i k x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (l - (k : ℝ))) →
        (∀ i k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixed g i k x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (k : ℝ))) →
        ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixed (fun y η ↦ B (f y η) (g y η)) i j x ξ‖ ≤
            C * (1 + ‖ξ‖) ^ (l + m - (j : ℝ)) := by
    induction j with
    | zero =>
      -- With no frequency derivatives, the usual spatial Leibniz bound suffices.
      intro V W Z _ _ _ _ _ _ B f g l m hf hg hfb hgb i
      choose Cf hCf hfb using fun k ↦ hfb k 0
      choose Cg hCg hgb using fun k ↦ hgb k 0
      refine ⟨‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * Cf k * Cg (i - k),
        mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun k _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf k)) (hCg (i - k)))), ?_⟩
      intro x hx ξ
      rw [mixed_zero]
      have hf' : ContDiffOn ℝ ∞ (fun y ↦ f y ξ) U :=
        hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy ↦ ⟨hy, Set.mem_univ ξ⟩)
      have hg' : ContDiffOn ℝ ∞ (fun y ↦ g y ξ) U :=
        hg.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy ↦ ⟨hy, Set.mem_univ ξ⟩)
      have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf' hg' hU.uniqueDiffOn
        (hKU hx) (n := i) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ hU (hKU hx)] at h
      apply h.trans
      simp only [Nat.cast_zero, sub_zero]
      calc
        ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
            ‖iteratedFDeriv ℝ k (fun y ↦ f y ξ) x‖ *
            ‖iteratedFDeriv ℝ (i - k) (fun y ↦ g y ξ) x‖ ≤
            ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
              (Cf k * (1 + ‖ξ‖) ^ l) * (Cg (i - k) * (1 + ‖ξ‖) ^ m) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply Finset.sum_le_sum
          intro k hk
          have hfk := hfb k x hx ξ
          have hgk := hgb (i - k) x hx ξ
          simp only [mixed_zero, Nat.cast_zero, sub_zero] at hfk hgk
          gcongr
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hCf k)
            (Real.rpow_nonneg (by positivity) _))
        _ = _ := by
          rw [Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖)]
          rw [mul_assoc]
          congr 1
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    | succ j ih =>
      -- Differentiate either factor in frequency and apply the induction hypothesis twice.
      intro V W Z _ _ _ _ _ _ B f g l m hf hg hfb hgb i
      let df : P → P → P →L[ℝ] V := fun x ξ ↦ fderiv ℝ (f x) ξ
      let dg : P → P → P →L[ℝ] W := fun x ξ ↦ fderiv ℝ (g x) ξ
      have hdf := smooth_frequency_derivative hU f hf
      have hdg := smooth_frequency_derivative hU g hg
      have hdfb : ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixed df a b x ξ‖ ≤ C * (1 + ‖ξ‖) ^ ((l - 1) - (b : ℝ)) := by
        intro a b
        obtain ⟨C, hC, hbound⟩ := hfb a (b + 1)
        refine ⟨C, hC, ?_⟩
        intro x hx ξ
        have h := hbound x hx ξ
        rw [← mixed_shift] at h
        have hexp : l - ((b + 1 : ℕ) : ℝ) = l - 1 - (b : ℝ) := by
          push_cast
          ring
        rw [hexp] at h
        exact h
      have hdgb : ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixed dg a b x ξ‖ ≤ C * (1 + ‖ξ‖) ^ ((m - 1) - (b : ℝ)) := by
        intro a b
        obtain ⟨C, hC, hbound⟩ := hgb a (b + 1)
        refine ⟨C, hC, ?_⟩
        intro x hx ξ
        have h := hbound x hx ξ
        rw [← mixed_shift] at h
        have hexp : m - ((b + 1 : ℕ) : ℝ) = m - 1 - (b : ℝ) := by
          push_cast
          ring
        rw [hexp] at h
        exact h
      let p : P → P → P →L[ℝ] Z := fun x ξ ↦ B.precompR P (f x ξ) (dg x ξ)
      let q : P → P → P →L[ℝ] Z := fun x ξ ↦ B.precompL P (df x ξ) (g x ξ)
      obtain ⟨C, hC, hp⟩ := ih (B.precompR P) f dg l (m - 1) hf hdg hfb hdgb i
      obtain ⟨D, hD, hq⟩ := ih (B.precompL P) df g (l - 1) m hdf hg hdfb hgb i
      refine ⟨C + D, add_nonneg hC hD, ?_⟩
      intro x hx ξ
      have hps : ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ Set.univ) :=
        (B.precompR P).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hf hdg
      have hqs : ContDiffOn ℝ ∞ (Function.uncurry q) (U ×ˢ Set.univ) :=
        (B.precompL P).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hdf hg
      have heq : (fun y ↦ iteratedFDeriv ℝ j
          (fun η ↦ fderiv ℝ (fun η ↦ B (f y η) (g y η)) η) ξ) =ᶠ[𝓝 x]
          (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ p y η + q y η) ξ) := by
        filter_upwards [hU.mem_nhds (hKU hx)] with y hy
        congr 1
        funext η
        have hf' := (hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, Set.mem_univ η⟩)).comp η
          (contDiffAt_const.prodMk contDiffAt_id)
        have hg' := (hg.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, Set.mem_univ η⟩)).comp η
          (contDiffAt_const.prodMk contDiffAt_id)
        exact B.fderiv_of_bilinear (hf'.differentiableAt (by simp))
          (hg'.differentiableAt (by simp))
      rw [← mixed_shift]
      change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
      rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
      change ‖mixed (fun y η ↦ p y η + q y η) i j x ξ‖ ≤ _
      rw [mixed_add hU p q hps hqs i j x ξ (hKU hx)]
      have h := (norm_add_le _ _).trans (add_le_add (hp x hx ξ) (hq x hx ξ))
      have he₁ : l + (m - 1) - (j : ℝ) = l + m - ((j + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      have he₂ : (l - 1) + m - (j : ℝ) = l + m - ((j + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [he₁, he₂, ← add_mul] at h
      exact h
  -- Apply the general real bilinear estimate to the actual complex matrix composition.
  let B := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin r))
    (EuclideanSpace ℂ (Fin q)) (EuclideanSpace ℂ (Fin k))).bilinearRestrictScalars ℝ
  refine ⟨B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hb.1 ha.1, ?_⟩
  intro K hKU hK i j
  exact mixed_bilinear_estimate j hU hKU B b a l m hb.1 ha.1
    (hb.2 K hKU hK) (ha.2 K hKU hK) i

/-- The actual pointwise composition packaged with its symbol estimates. -/
def symbolSpaceComp (hU : IsOpen U) (b : symbolSpace U hU l q k)
    (a : symbolSpace U hU m r q) : symbolSpace U hU (l + m) r k :=
  ⟨symbolComp b.val a.val, b.property.symbolComp hU a.property⟩

/-- Changing either factor by one lower order changes the product by one lower order. -/
theorem principalSymbolClass_comp_congr (hU : IsOpen U)
    (b b' : symbolSpace U hU l q k) (a a' : symbolSpace U hU m r q)
    (hb : principalSymbolClass U hU l q k b = principalSymbolClass U hU l q k b')
    (ha : principalSymbolClass U hU m r q a = principalSymbolClass U hU m r q a') :
    principalSymbolClass U hU (l + m) r k (symbolSpaceComp hU b a) =
      principalSymbolClass U hU (l + m) r k (symbolSpaceComp hU b' a') := by
  /- Expand ba-b'a' as (b-b')a + b'(a-a'). Equality of the input classes makes
  the two differences have orders l-1 and m-1. Pointwise composition puts both
  summands in order l+m-1. Their sum therefore vanishes in the target quotient.
  This is filtered matrix algebra; no quantization composition formula is used. -/
  -- Quotient equality supplies the two actual one-order-lower differences.
  have hb' := (principalSymbolClass_eq_iff hU b b').mp hb
  have ha' := (principalSymbolClass_eq_iff hU a a').mp ha
  have hleft : IsSymbol U (l + m - 1) (symbolComp (b.val - b'.val) a.val) := by
    convert hb'.symbolComp hU a.property using 1
    ring
  have hright : IsSymbol U (l + m - 1) (symbolComp b'.val (a.val - a'.val)) := by
    convert b'.property.symbolComp hU ha' using 1
    ring
  -- The noncommutative difference expansion keeps the order of the two maps.
  apply (principalSymbolClass_eq_iff hU _ _).mpr
  change IsSymbol U (l + m - 1) (symbolComp b.val a.val - symbolComp b'.val a'.val)
  have hexpand : symbolComp b.val a.val - symbolComp b'.val a'.val =
      symbolComp (b.val - b'.val) a.val + symbolComp b'.val (a.val - a'.val) := by
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    simp only [symbolComp, Pi.sub_apply, Pi.add_apply, sub_apply,
      add_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hexpand]
  exact hleft.add hU hright

/-- Pointwise matrix composition descended to the actual principal symbol quotients. -/
def principalSymbolComp (hU : IsOpen U) :
    PrincipalSymbolSpace U hU l q k → PrincipalSymbolSpace U hU m r q →
      PrincipalSymbolSpace U hU (l + m) r k :=
  Quotient.lift₂
    (fun b a ↦ principalSymbolClass U hU (l + m) r k (symbolSpaceComp hU b a))
    (fun b a b' a' hb ha ↦ principalSymbolClass_comp_congr hU b b' a a'
      (Quotient.sound hb) (Quotient.sound ha))

/-- The quotient product acts on representatives by actual matrix composition. -/
theorem principalSymbolComp_class (hU : IsOpen U)
    (b : symbolSpace U hU l q k) (a : symbolSpace U hU m r q) :
    principalSymbolComp hU (principalSymbolClass U hU l q k b)
        (principalSymbolClass U hU m r q a) =
      principalSymbolClass U hU (l + m) r k (symbolSpaceComp hU b a) := by
  /- Evaluate the two quotient lifts on their canonical representatives.
  The descent proof affects only well-definedness; the representative of the result
  is exactly the pointwise product b(x,ξ) composed with a(x,ξ). -/
  -- Both quotient lifts evaluate on these exact original representatives.
  rfl

/-- Addition in the left factor is respected by the graded symbol product. -/
theorem principalSymbolComp_add_left (hU : IsOpen U)
    (b c : PrincipalSymbolSpace U hU l q k) (a : PrincipalSymbolSpace U hU m r q) :
    principalSymbolComp hU (b + c) a =
      principalSymbolComp hU b a + principalSymbolComp hU c a := by
  /- Lift all three classes to representatives using quotient surjectivity.
  The class projection preserves sums, and pointwise composition distributes over
  addition in the left matrix factor. Project that identity to the target quotient. -/
  -- Use actual order-l and order-m representatives of the three quotient classes.
  obtain ⟨b, rfl⟩ := principalSymbolClass_surjective (r := q) (q := k) hU l b
  obtain ⟨c, rfl⟩ := principalSymbolClass_surjective (r := q) (q := k) hU l c
  obtain ⟨a, rfl⟩ := principalSymbolClass_surjective (r := r) (q := q) hU m a
  rw [← map_add, principalSymbolComp_class, principalSymbolComp_class,
    principalSymbolComp_class, ← map_add]
  -- Distribute the output map before projecting back to the same quotient.
  rfl

/-- Addition in the right factor is respected by the graded symbol product. -/
theorem principalSymbolComp_add_right (hU : IsOpen U)
    (b : PrincipalSymbolSpace U hU l q k) (a c : PrincipalSymbolSpace U hU m r q) :
    principalSymbolComp hU b (a + c) =
      principalSymbolComp hU b a + principalSymbolComp hU b c := by
  /- Choose symbol representatives for the three quotient classes.
  A continuous linear matrix map sends the sum of the two right-hand outputs to
  the sum of their images. The linear quotient projection preserves this identity. -/
  -- Quotient surjectivity reduces the claim to the original symbol functions.
  obtain ⟨b, rfl⟩ := principalSymbolClass_surjective (r := q) (q := k) hU l b
  obtain ⟨a, rfl⟩ := principalSymbolClass_surjective (r := r) (q := q) hU m a
  obtain ⟨c, rfl⟩ := principalSymbolClass_surjective (r := r) (q := q) hU m c
  rw [← map_add, principalSymbolComp_class, principalSymbolComp_class,
    principalSymbolComp_class, ← map_add]
  -- Additivity of the same output map distributes over the two input images.
  congr 1
  apply Subtype.ext
  funext x ξ
  apply ContinuousLinearMap.ext
  intro v
  simp [symbolSpaceComp, symbolComp]

/-- Complex scalar multiplication in the left factor passes through composition. -/
theorem principalSymbolComp_smul_left (hU : IsOpen U) (c : ℂ)
    (b : PrincipalSymbolSpace U hU l q k) (a : PrincipalSymbolSpace U hU m r q) :
    principalSymbolComp hU (c • b) a = c • principalSymbolComp hU b a := by
  /- Choose representatives and use the pointwise identity (c b) composed with a
  equals c times (b composed with a). The principal class projection is complex-linear,
  so the same identity holds independently of the chosen representatives. -/
  -- Choose representatives without choosing any new leading homogeneous data.
  obtain ⟨b, rfl⟩ := principalSymbolClass_surjective (r := q) (q := k) hU l b
  obtain ⟨a, rfl⟩ := principalSymbolClass_surjective (r := r) (q := q) hU m a
  rw [← map_smul, principalSymbolComp_class, principalSymbolComp_class, ← map_smul]
  -- Scaling the output map scales its actual composite by the same complex scalar.
  rfl

/-- Complex scalar multiplication in the right factor passes through composition. -/
theorem principalSymbolComp_smul_right (hU : IsOpen U) (c : ℂ)
    (b : PrincipalSymbolSpace U hU l q k) (a : PrincipalSymbolSpace U hU m r q) :
    principalSymbolComp hU b (c • a) = c • principalSymbolComp hU b a := by
  /- On representatives, complex linearity of b gives b(c a(v)) = c b(a(v)).
  Project the equality of symbol functions to the target quotient. The scalar is
  not conjugated: this operation is matrix composition, not a Hermitian adjoint. -/
  -- Descend the complex-linear identity from actual order-l and order-m symbols.
  obtain ⟨b, rfl⟩ := principalSymbolClass_surjective (r := q) (q := k) hU l b
  obtain ⟨a, rfl⟩ := principalSymbolClass_surjective (r := r) (q := q) hU m a
  rw [← map_smul, principalSymbolComp_class, principalSymbolComp_class, ← map_smul]
  -- Complex linearity of the output map introduces no scalar conjugation.
  congr 1
  apply Subtype.ext
  funext x ξ
  apply ContinuousLinearMap.ext
  intro v
  simp [symbolSpaceComp, symbolComp]

set_option maxHeartbeats 800000 in

/-- Local homogeneous leading data admit a smooth cutoff symbol representative. -/
theorem exists_symbol_of_homogeneous_on (hU : IsOpen U) (m : ℝ)
    (a₀ : SymbolFunction n r q)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry a₀) (U ×ˢ {ξ | ξ ≠ 0}))
    (hhom : IsHomogeneousSymbol U m a₀) :
    ∃ a : symbolSpace U hU m r q, ∀ x ∈ U, ∀ ξ, 1 ≤ ‖ξ‖ → a.val x ξ = a₀ x ξ := by
  /- Stage 1: multiply a₀ away from zero by a smooth radial cutoff, zero on a
  neighborhood of zero and one for norm(ξ) ≥ 1, and set the result to zero near zero.
  Stage 2: homogeneity controls frequency derivatives by their values on the unit
  sphere; smoothness bounds those values over each compact K in U. The cutoff region
  is compact in frequency, so its derivatives satisfy every required estimate.
  If n = 0 there are no nonzero frequencies; the zero symbol meets the specification. -/
  classical
  -- Fix the radial cutoff before modifying the homogeneous symbol.
  let highFrequencyCutoff (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
    1 - (⟨1 / 2, 1, by norm_num, by norm_num⟩ :
      ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) ξ
  have contDiff_highFrequencyCutoff : ContDiff ℝ ∞ (highFrequencyCutoff n) := by
    -- The chosen bump is globally smooth, so its complement is smooth at zero as well.
    exact contDiff_const.sub (ContDiffBump.contDiff _)
  have highFrequencyCutoff_eq_zero (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ ≤ 1 / 2) :
      highFrequencyCutoff n ξ = 0 := by
    -- The bump equals one on the fixed inner closed ball.
    let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
      ⟨1 / 2, 1, by norm_num, by norm_num⟩
    change 1 - φ ξ = 0
    rw [φ.one_of_mem_closedBall (by simpa [φ] using hξ)]
    exact sub_self 1
  have highFrequencyCutoff_eq_one (ξ : EuclideanSpace ℝ (Fin n)) (hξ : 1 ≤ ‖ξ‖) :
      highFrequencyCutoff n ξ = 1 := by
    -- The outer open ball is the bump support, including the claimed boundary convention.
    let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
      ⟨1 / 2, 1, by norm_num, by norm_num⟩
    change 1 - φ ξ = 1
    rw [φ.zero_of_le_dist (by simpa [φ] using hξ)]
    exact sub_zero 1
  let frequencyCutoffSymbol (a : SymbolFunction n r q) : SymbolFunction n r q :=
    fun x ξ ↦ (highFrequencyCutoff n ξ : ℂ) • a x ξ
  have frequencyCutoffSymbol_eq_of_one_le_norm (a : SymbolFunction n r q)
      (x ξ : EuclideanSpace ℝ (Fin n)) (hξ : 1 ≤ ‖ξ‖) :
      frequencyCutoffSymbol a x ξ = a x ξ := by
    -- Use the same specified cutoff, without any assumption on the original data.
    simp only [frequencyCutoffSymbol, highFrequencyCutoff_eq_one ξ hξ, Complex.ofReal_one,
      one_smul]
  have frequencyCutoffSymbol_eq_zero_of_norm_le (a : SymbolFunction n r q)
      (x ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ ≤ 1 / 2) :
      frequencyCutoffSymbol a x ξ = 0 := by
    -- Multiplication by the zero cutoff suppresses even arbitrary original values.
    simp only [frequencyCutoffSymbol, highFrequencyCutoff_eq_zero ξ hξ, Complex.ofReal_zero,
      zero_smul]
  have isSymbol_frequencyCutoffSymbol (U : Set (EuclideanSpace ℝ (Fin n)))
      (hU : IsOpen U) (m : ℝ) (a : SymbolFunction n r q)
      (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ {ξ | ξ ≠ 0}))
      (hhom : IsHomogeneousSymbol U m a) : IsSymbol U m (frequencyCutoffSymbol a) := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let b := frequencyCutoffSymbol a
    -- Smoothness is patched from the zero neighborhood and the punctured-frequency formula.
    have hcut : ContDiff ℝ ∞ (fun p : V × V ↦ (highFrequencyCutoff n p.2 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_highFrequencyCutoff.comp contDiff_snd)
    have hsm : ContDiffOn ℝ ∞ (Function.uncurry b) (U ×ˢ Set.univ) := by
      intro p hp
      by_cases hξ : p.2 = 0
      · have heq : Function.uncurry b =ᶠ[𝓝 p] (fun _ ↦ 0) := by
          have hsmall : ‖p.2‖ < (1 / 2 : ℝ) := by simp [hξ]
          filter_upwards [continuous_snd.norm.continuousAt.eventually (gt_mem_nhds hsmall)]
            with z hz
          exact frequencyCutoffSymbol_eq_zero_of_norm_le a z.1 z.2 hz.le
        exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
      · have ha := hsmooth.contDiffAt
          ((hU.prod (isOpen_ne : IsOpen {ξ : V | ξ ≠ 0})).mem_nhds ⟨hp.1, hξ⟩)
        exact (hcut.contDiffAt.smul ha).contDiffWithinAt
    refine ⟨hsm, ?_⟩
    -- Full derivatives commute with invertible linear dilations, including totalized derivatives.
    have deriv_comp_smul {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] (t : ℝ) (ht : t ≠ 0) (f : V → W) (j : ℕ) (ξ : V) :
        iteratedFDeriv ℝ j (fun ζ ↦ f (t • ζ)) ξ =
          t ^ j • iteratedFDeriv ℝ j f (t • ξ) := by
      let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
      have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := ξ) (Set.mem_univ _) j
      simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
      change iteratedFDeriv ℝ j (f ∘ e) ξ = _
      rw [h]
      ext v
      change (iteratedFDeriv ℝ j f (t • ξ)) (fun i ↦ t • v i) = _
      rw [ContinuousMultilinearMap.map_smul_univ]
      simp
    have deriv_smul {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] (t : ℝ) (ht : t ≠ 0) (f : V → W) (j : ℕ) (ξ : V) :
        iteratedFDeriv ℝ j (fun ζ ↦ t • f ζ) ξ = t • iteratedFDeriv ℝ j f ξ := by
      let e : W ≃L[ℝ] W := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
      have h := e.iteratedFDeriv_comp_left (f := f) (x := ξ) (i := j)
      change iteratedFDeriv ℝ j (e ∘ f) ξ = _
      rw [h]
      rfl
    -- Differentiate homogeneity first in frequency and then on the original open base domain.
    have hscale (i j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
        (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) (t : ℝ) (ht : 0 < t) :
        symbolDerivative a i j x (t • ξ) = t ^ (m - (j : ℝ)) • symbolDerivative a i j x ξ := by
      have hfreq (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
          iteratedFDeriv ℝ j (a y) (t • ξ) =
            t ^ (m - (j : ℝ)) • iteratedFDeriv ℝ j (a y) ξ := by
        have heq : (fun ζ ↦ a y (t • ζ)) =ᶠ[𝓝 ξ] (fun ζ ↦ (t ^ m) • a y ζ) := by
          filter_upwards [(isOpen_ne : IsOpen {ζ : EuclideanSpace ℝ (Fin n) | ζ ≠ 0}).mem_nhds hξ]
            with ζ hζ
          exact hhom y hy ζ hζ t ht
        have hd := (heq.iteratedFDeriv ℝ j).eq_of_nhds
        rw [deriv_comp_smul t ht.ne', deriv_smul (t ^ m) (Real.rpow_pos_of_pos ht m).ne'] at hd
        calc
          _ = (t ^ j)⁻¹ • (t ^ j • iteratedFDeriv ℝ j (a y) (t • ξ)) := by
            rw [inv_smul_smul₀ (pow_ne_zero _ ht.ne')]
          _ = ((t ^ j)⁻¹ * t ^ m) • iteratedFDeriv ℝ j (a y) ξ := by rw [hd, smul_smul]
          _ = _ := by
            rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
            congr 2
            ring
      have heq : (fun y ↦ iteratedFDeriv ℝ j (a y) (t • ξ)) =ᶠ[𝓝 x]
          (fun y ↦ t ^ (m - (j : ℝ)) • iteratedFDeriv ℝ j (a y) ξ) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact hfreq y hy
      have hd := (heq.iteratedFDeriv ℝ i).eq_of_nhds
      rw [deriv_smul _ (Real.rpow_pos_of_pos ht _).ne'] at hd
      exact hd
    have hparametric {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
        [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
        (f : P → Q → R) (x : P) (y : Q)
        (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (j : ℕ) :
        ContDiffAt ℝ ∞ (fun p : P × Q ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, y) := by
      -- Parameter differentiation remains smooth; each step differentiates and uncurries once.
      induction j with
      | zero =>
        exact hf.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ Q R).symm : _ →L[ℝ] Q [×0]→L[ℝ] R)
      | succ j ih =>
        have h : ContDiffAt ℝ ∞
            (Function.uncurry (fun p : P × Q ↦ fun z : Q ↦ iteratedFDeriv ℝ j (f p.1) z))
            ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
        have hd : ContDiffAt ℝ ∞
            (fun p : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, y) :=
          h.fderiv contDiffAt_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ Q) R).symm :
            _ →L[ℝ] Q [×(j + 1)]→L[ℝ] R)
    have hmixed (f : SymbolFunction n r q) (p : V × V)
        (hf : ContDiffAt ℝ ∞ (Function.uncurry f) p) (i j : ℕ) :
        ContDiffAt ℝ ∞ (fun z : V × V ↦ symbolDerivative f i j z.1 z.2) p := by
      have hξ := hparametric f p.1 p.2 hf j
      have hswap : ContDiffAt ℝ ∞
          (Function.uncurry (fun ξ x ↦ iteratedFDeriv ℝ j (f x) ξ)) (p.2, p.1) :=
        hξ.comp (p.2, p.1) (contDiffAt_snd.prodMk contDiffAt_fst)
      exact (hparametric _ p.2 p.1 hswap i).comp p
        (contDiffAt_snd.prodMk contDiffAt_fst)
    -- Comparing homogeneous and inhomogeneous weights must also cover negative symbol orders.
    have hweight (k t : ℝ) (ht : 1 ≤ t) :
        t ^ k ≤ (2 : ℝ) ^ |k| * (1 + t) ^ k := by
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      by_cases hk : 0 ≤ k
      · have htwo : (1 : ℝ) ≤ 2 ^ |k| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
        calc
          t ^ k ≤ (1 + t) ^ k := Real.rpow_le_rpow htpos.le (by linarith) hk
          _ ≤ 2 ^ |k| * (1 + t) ^ k := le_mul_of_one_le_left (by positivity) htwo
      · have hk' : k ≤ 0 := (lt_of_not_ge hk).le
        have hcomp : (2 * t) ^ k ≤ (1 + t) ^ k :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hk'
        calc
          t ^ k = 2 ^ |k| * (2 * t) ^ k := by
            rw [Real.mul_rpow (by norm_num) htpos.le, abs_of_nonpos hk', ← mul_assoc,
              ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero, one_mul]
          _ ≤ 2 ^ |k| * (1 + t) ^ k := mul_le_mul_of_nonneg_left hcomp (by positivity)
    intro K hKU hK i j
    let k := m - (j : ℝ)
    -- Compactness controls the smooth cutoff on the full low-frequency ball.
    have hlowcont : ContinuousOn
        (fun p : V × V ↦ ‖symbolDerivative b i j p.1 p.2‖ / (1 + ‖p.2‖) ^ k)
        (K ×ˢ Metric.closedBall 0 2) := by
      intro p hp
      have hf := hsm.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hKU hp.1, Set.mem_univ _⟩)
      have hnorm := (hmixed b p hf i j).continuousAt.norm
      have hbase : Continuous (fun p : V × V ↦ (1 : ℝ) + ‖p.2‖) :=
        continuous_const.add continuous_snd.norm
      have hw : ContinuousAt (fun p : V × V ↦ (1 + ‖p.2‖) ^ k) p :=
        hbase.continuousAt.rpow_const
          (Or.inl (ne_of_gt (by positivity)))
      exact (hnorm.div hw (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))).continuousWithinAt
    obtain ⟨C₀, hC₀⟩ := ((hK.prod (isCompact_closedBall (0 : V) 2)).image_of_continuousOn
      hlowcont).bddAbove
    -- On the unit sphere all mixed derivatives of the original data are uniformly bounded.
    have hsphere : ContinuousOn (fun p : V × V ↦ ‖symbolDerivative a i j p.1 p.2‖)
        (K ×ˢ Metric.sphere 0 1) := by
      intro p hp
      have hnorm : ‖p.2‖ = 1 := by simpa using hp.2
      have hne : p.2 ≠ 0 := by intro hz; simp [hz] at hnorm
      have hf := hsmooth.contDiffAt
        ((hU.prod (isOpen_ne : IsOpen {ξ : V | ξ ≠ 0})).mem_nhds ⟨hKU hp.1, hne⟩)
      exact (hmixed a p hf i j).continuousAt.norm.continuousWithinAt
    obtain ⟨C₁, hC₁⟩ := ((hK.prod (isCompact_sphere (0 : V) 1)).image_of_continuousOn
      hsphere).bddAbove
    let D := max C₁ 0
    refine ⟨max C₀ 0 + D * 2 ^ |k|, by dsimp only [D]; positivity, ?_⟩
    intro x hx ξ
    by_cases hlow : ‖ξ‖ ≤ 2
    · have hmem : ξ ∈ Metric.closedBall (0 : V) 2 := by simpa using hlow
      have hbound := hC₀ ⟨(x, ξ), ⟨hx, hmem⟩, rfl⟩
      have hC : C₀ ≤ max C₀ 0 + D * 2 ^ |k| := by
        have hnonneg : 0 ≤ D * 2 ^ |k| := by dsimp only [D]; positivity
        linarith [le_max_left C₀ 0]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mp (hbound.trans hC)
    · have hlarge : 2 < ‖ξ‖ := lt_of_not_ge hlow
      have hξpos : 0 < ‖ξ‖ := lt_trans (by norm_num) hlarge
      let η := ‖ξ‖⁻¹ • ξ
      have hηnorm : ‖η‖ = 1 := by
        simp only [η, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
        exact inv_mul_cancel₀ hξpos.ne'
      have hηne : η ≠ 0 := by intro hz; simp [hz] at hηnorm
      have hreconstruct : ‖ξ‖ • η = ξ := smul_inv_smul₀ hξpos.ne' ξ
      -- Away from the cutoff transition, equality on a neighborhood identifies full derivatives.
      have hder : symbolDerivative b i j x ξ = symbolDerivative a i j x ξ := by
        have heq (y : V) : b y =ᶠ[𝓝 ξ] a y := by
          filter_upwards [continuous_norm.continuousAt.eventually
            (lt_mem_nhds (show (1 : ℝ) < ‖ξ‖ by linarith))] with ζ hζ
          exact frequencyCutoffSymbol_eq_of_one_le_norm a y ζ hζ.le
        have hfunctions : (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) =
            (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) :=
          funext (fun y ↦ ((heq y).iteratedFDeriv ℝ j).eq_of_nhds)
        unfold symbolDerivative
        rw [hfunctions]
      have hbound : ‖symbolDerivative a i j x η‖ ≤ D := by
        apply (hC₁ ⟨(x, η), ⟨hx, ?_⟩, rfl⟩).trans (le_max_left C₁ 0)
        simpa using hηnorm
      have hnorm : ‖symbolDerivative b i j x ξ‖ =
          ‖ξ‖ ^ k * ‖symbolDerivative a i j x η‖ := by
        rw [hder]
        conv_lhs => rw [← hreconstruct, hscale i j x (hKU hx) η hηne ‖ξ‖ hξpos]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hξpos _)]
      calc
        _ = ‖ξ‖ ^ k * ‖symbolDerivative a i j x η‖ := hnorm
        _ ≤ ‖ξ‖ ^ k * D := mul_le_mul_of_nonneg_left hbound (by positivity)
        _ ≤ (2 ^ |k| * (1 + ‖ξ‖) ^ k) * D :=
          mul_le_mul_of_nonneg_right (hweight k ‖ξ‖ (by linarith)) (le_max_right C₁ 0)
        _ ≤ (max C₀ 0 + D * 2 ^ |k|) * (1 + ‖ξ‖) ^ k := by
          have hnonneg : 0 ≤ max C₀ 0 * (1 + ‖ξ‖) ^ k := by positivity
          nlinarith
  -- Retain this actual regularized function as the existential symbol witness.
  refine ⟨⟨frequencyCutoffSymbol a₀, isSymbol_frequencyCutoffSymbol U hU m a₀ hsmooth hhom⟩, ?_⟩
  intro x hx ξ hξ
  exact frequencyCutoffSymbol_eq_of_one_le_norm a₀ x ξ hξ

/-- A homogeneous leading representative of a principal class is unique away from zero. -/
theorem homogeneous_eq_of_principalSymbolClass_eq (hU : IsOpen U)
    (a b : symbolSpace U hU m r q) (a₀ b₀ : SymbolFunction n r q)
    (ha₀ : IsHomogeneousSymbol U m a₀) (hb₀ : IsHomogeneousSymbol U m b₀)
    (R : ℝ) (hR : 0 < R)
    (ha : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → a.val x ξ = a₀ x ξ)
    (hb : ∀ x ∈ U, ∀ ξ, R ≤ ‖ξ‖ → b.val x ξ = b₀ x ξ)
    (hab : principalSymbolClass U hU m r q a = principalSymbolClass U hU m r q b) :
    ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → a₀ x ξ = b₀ x ξ := by
  /- Fix x and a nonzero ξ. Equality in the quotient bounds a-b at x by order m-1.
  At tξ for t sufficiently large, the high-frequency agreements and homogeneity give
  t^m times (a₀(x,ξ)-b₀(x,ξ)). Divide the estimate by t^m and let t tend to infinity;
  the resulting bound tends to zero for every real m. Thus the difference vanishes.
  The assertion deliberately excludes ξ=0, where homogeneous data were never prescribed. -/
  intro x hx ξ hξ
  -- The actual quotient gives its zeroth estimate at the same base point.
  have hdiff := (principalSymbolClass_eq_iff hU a b).mp hab
  obtain ⟨C, hC, hbound⟩ := hdiff.2 {x} (by simpa) (isCompact_singleton) 0 0
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hscaled : ∀ᶠ t : ℝ in Filter.atTop,
      ‖a₀ x ξ - b₀ x ξ‖ ≤ C * (t⁻¹ + ‖ξ‖) ^ (m - 1) * t⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop (R / ‖ξ‖)] with t ht
    have htpos : 0 < t := lt_of_lt_of_le (div_pos hR hnorm) ht
    have hfreq : R ≤ ‖t • ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact (div_le_iff₀ hnorm).mp ht
    have h := hbound x (Set.mem_singleton x) (t • ξ)
    simp only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero,
      Pi.sub_apply] at h
    rw [ha x hx _ hfreq, hb x hx _ hfreq, ha₀ x hx ξ hξ t htpos,
      hb₀ x hx ξ hξ t htpos, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos htpos m)] at h
    have hbase : 0 < t⁻¹ + ‖ξ‖ := by positivity
    have hfactor : 1 + ‖t • ξ‖ = t * (t⁻¹ + ‖ξ‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      field_simp
    rw [hfactor, Real.mul_rpow htpos.le hbase.le,
      Real.rpow_sub htpos, Real.rpow_one] at h
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos htpos m)).mp
    calc
      t ^ m * ‖a₀ x ξ - b₀ x ξ‖ ≤
          C * (t ^ m / t * (t⁻¹ + ‖ξ‖) ^ (m - 1)) := h
      _ = t ^ m * (C * (t⁻¹ + ‖ξ‖) ^ (m - 1) * t⁻¹) := by ring
  -- After dividing by the homogeneous degree, the one-order gain tends to zero.
  have hinv : Filter.Tendsto (fun t : ℝ ↦ t⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hweight : Filter.Tendsto (fun t : ℝ ↦ (t⁻¹ + ‖ξ‖) ^ (m - 1))
      Filter.atTop (nhds (‖ξ‖ ^ (m - 1))) := by
    simpa only [zero_add] using
      (hinv.add_const ‖ξ‖).rpow_const (Or.inl (by simpa using (ne_of_gt hnorm)))
  have hlimit : Filter.Tendsto
      (fun t : ℝ ↦ C * (t⁻¹ + ‖ξ‖) ^ (m - 1) * t⁻¹) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (hweight.const_mul C).mul hinv
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (ge_of_tendsto hlimit hscaled))

end AtiyahSinger
