/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentChartNormBounds
public import AtiyahSinger.Analysis.TensorCutoffGlobalSymbol
public import AtiyahSinger.Analysis.UniformSymbolRegularization

/-!
# Homogeneity at infinity of the actual finite-atlas cutoff

Public module ID: M0618.

The high-frequency angular cutoff vanishes unless its retained factor already
lies beyond the fixed regularization radius. Thus the exact finite-atlas
coefficient, with all original signed weights, is degree one at infinity.
The radius controls both endpoints of a positive rescaling and works for
every original patch pair simultaneously.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

private def productCutoffAngular (ε r s : ℝ) : ℝ :=
  if r = 0 then 0 else 1 - productCutoffProfile (ε * s / r)

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  {E₀ E₁ : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]

set_option maxHeartbeats 800000 in
-- One compact-frequency bound controls every original finite patch pair.
private theorem exists_productCutoffWeight_tail_of_eq
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a b : GlobalSymbolFunction (n := n) E₀ E₁) (R₀ : ℝ) (hR₀pos : 0 < R₀)
    (hrecover : ∀ x ξ, R₀ ≤ g.length x ξ → a x ξ = b x ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (i : Fin A.size) (j : Fin B.size) (x : M) (y : N)
      (ξ₁ : CotangentFiber (n := n) x) (ξ₂ : CotangentFiber (n := m) y),
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
      let r := ‖covectorInChart (A.patch i).chart x ξ₁‖
      let s := ‖covectorInChart (B.patch j).chart y ξ₂‖
      (A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s =
          (A.patch i).weight x * (B.patch j).weight y * productCutoffAngular ε r s ∧
      (((A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s : ℝ) : ℂ) •
          a x ξ₁ =
        (((A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s : ℝ) : ℂ) •
          b x ξ₁ := by
  classical
  obtain ⟨C, hC, hA⟩ := A.exists_covectorInChart_norm_bounds g
  obtain ⟨D, hD, hB⟩ := B.exists_covectorInChart_norm_bounds k
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  let L := (C + D) * (2 / ε)
  let J := 1 + 2 * C * D / ε
  let R := max L (J * R₀) + 1
  have hJpos : 0 < J := by dsimp [J]; positivity
  have hLR : L < R := lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one
  have hJR : J * R₀ < R := lt_add_of_le_of_pos (le_max_right _ _) zero_lt_one
  have hRpos : 0 < R := (mul_pos hJpos hR₀pos).trans hJR
  let angular := productCutoffAngular ε
  have hpone (u : ℝ) (hu : 2 ≤ u) : productCutoffProfile u = 1 := by
    let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    change 1 - φ u = 1
    rw [φ.zero_of_le_dist (by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith : 0 ≤ u), φ] using hu),
      sub_zero]
  -- Above this common radius, a nonzero angular term forces recovery of the first symbol.
  have hhigh (i : Fin A.size) (j : Fin B.size) (x : M) (y : N)
      (ξ₁ : CotangentFiber (n := n) x) (ξ₂ : CotangentFiber (n := m) y)
      (hξ : R ≤ g.length x ξ₁ + k.length y ξ₂) :
      let r := ‖covectorInChart (A.patch i).chart x ξ₁‖
      let s := ‖covectorInChart (B.patch j).chart y ξ₂‖
      (A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s =
          (A.patch i).weight x * (B.patch j).weight y * angular r s ∧
      (((A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s : ℝ) : ℂ) •
          a x ξ₁ =
        (((A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s : ℝ) : ℂ) •
          b x ξ₁ := by
    dsimp only
    by_cases hi : (A.patch i).weight x = 0
    · simp [hi]
    by_cases hj : (B.patch j).weight y = 0
    · simp [hj]
    let r := ‖covectorInChart (A.patch i).chart x ξ₁‖
    let s := ‖covectorInChart (B.patch j).chart y ξ₂‖
    have hr : 0 ≤ r := norm_nonneg _
    have hs : 0 ≤ s := norm_nonneg _
    have hg := hA i x hi ξ₁
    have hk := hB j y hj ξ₂
    change g.length x ξ₁ ≤ C * r ∧ r ≤ C * g.length x ξ₁ at hg
    change k.length y ξ₂ ≤ D * s ∧ s ≤ D * k.length y ξ₂ at hk
    let ρ := Real.sqrt (r ^ 2 + s ^ 2)
    have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
    have hρsq : ρ ^ 2 = r ^ 2 + s ^ 2 := Real.sq_sqrt (by positivity)
    have hrρ : r ≤ ρ := by nlinarith [sq_nonneg s]
    have hsρ : s ≤ ρ := by nlinarith [sq_nonneg r]
    have hrad : 2 ≤ ε * ρ := by
      by_contra h
      have hρlt : ρ < 2 / ε := (lt_div_iff₀ hε).mpr (by nlinarith)
      have hbound : g.length x ξ₁ + k.length y ξ₂ ≤ (C + D) * ρ := by nlinarith
      have hlt : (C + D) * ρ < L := mul_lt_mul_of_pos_left hρlt (add_pos hCpos hDpos)
      linarith
    have htail : productFrequencyCutoff ε r s = angular r s := by
      rw [productFrequencyCutoff, hpone _ hrad]
      by_cases hz : r = 0
      · simp [angular, productCutoffAngular, hz]
      · simp [angular, productCutoffAngular, hz]
    refine ⟨by rw [htail], ?_⟩
    change (((A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s : ℝ) : ℂ) •
        a x ξ₁ =
      (((A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s : ℝ) : ℂ) •
        b x ξ₁
    rw [htail]
    by_cases hzero : angular r s = 0
    · simp [hzero]
    have hrne : r ≠ 0 := by intro hz; exact hzero (by simp [angular, productCutoffAngular, hz])
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrne)
    have hcone : ε * s < 2 * r := by
      by_contra h
      have hratio : 2 ≤ ε * s / r := (le_div_iff₀ hrpos).mpr (le_of_not_gt h)
      exact hzero (by simp [angular, productCutoffAngular, hrne, hpone _ hratio])
    have hsbound : s ≤ 2 * C * g.length x ξ₁ / ε := by
      apply (le_div_iff₀ hε).mpr
      nlinarith [hg.2]
    have hsum : g.length x ξ₁ + k.length y ξ₂ ≤ J * g.length x ξ₁ := by
      calc
        g.length x ξ₁ + k.length y ξ₂ ≤ g.length x ξ₁ + D * s := by linarith [hk.1]
        _ ≤ g.length x ξ₁ + D * (2 * C * g.length x ξ₁ / ε) := by gcongr
        _ = J * g.length x ξ₁ := by dsimp [J]; ring
    have hlength : R₀ ≤ g.length x ξ₁ := by
      by_contra h
      have hlt : J * g.length x ξ₁ < J * R₀ := mul_lt_mul_of_pos_left (lt_of_not_ge h) hJpos
      linarith
    rw [hrecover x ξ₁ hlength]
  exact ⟨R, hRpos, hhigh⟩

set_option maxHeartbeats 800000 in
-- One compact-frequency bound controls every original finite patch pair.
private theorem exists_productCutoffWeight_regularizedSymbol_tail
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a : GlobalSymbolFunction (n := n) E₀ E₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (i : Fin A.size) (j : Fin B.size) (x : M) (y : N)
      (ξ₁ : CotangentFiber (n := n) x) (ξ₂ : CotangentFiber (n := m) y),
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
      let r := ‖covectorInChart (A.patch i).chart x ξ₁‖
      let s := ‖covectorInChart (B.patch j).chart y ξ₂‖
      (A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s =
          (A.patch i).weight x * (B.patch j).weight y * productCutoffAngular ε r s ∧
      (((A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s : ℝ) : ℂ) •
          A.regularizedSymbolFunction a x ξ₁ =
        (((A.patch i).weight x * (B.patch j).weight y * productFrequencyCutoff ε r s : ℝ) : ℂ) •
          a x ξ₁ := by
  obtain ⟨R₀, hR₀, hrecover⟩ := A.exists_regularizedSymbolFunction_eq_of_length_ge g
  exact exists_productCutoffWeight_tail_of_eq A B g k (A.regularizedSymbolFunction a) a
    R₀ (zero_lt_one.trans_le hR₀) (hrecover a) ε hε

set_option maxHeartbeats 800000 in
-- One radius keeps the surviving factor outside its original regularization region.
/-- The exact canonical first-factor cutoff coefficient is degree one at infinity. -/
theorem QuantizationPresentation.exists_productCutoffWeight_regularizedSymbol_homogeneous
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a : GlobalSymbolFunction (n := n) E₀ E₁)
    (ha : IsHomogeneousGlobalSymbol E₀ E₁ 1 a) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (y : N)
      (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) (t : ℝ), 0 < t →
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
      let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
      let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
      R ≤ g.length x (t • ξ₁) + k.length y (t • ξ₂) →
        ((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y (t • ξ) : ℝ) : ℂ) •
            A.regularizedSymbolFunction a x (t • ξ₁) =
          (t : ℂ) •
            (((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
              A.regularizedSymbolFunction a x ξ₁) := by
  classical
  obtain ⟨R, hRpos, hhigh⟩ :=
    exists_productCutoffWeight_regularizedSymbol_tail A B g k a ε hε
  have hangular (r s t : ℝ) (ht : 0 < t) :
      productCutoffAngular ε (t * r) (t * s) = productCutoffAngular ε r s := by
    by_cases hr : r = 0
    · simp [productCutoffAngular, hr]
    · simp only [productCutoffAngular, ite_eq_right hr, ite_eq_right (mul_ne_zero ht.ne' hr)]
      congr 2
      field_simp
  refine ⟨R, hRpos, ?_⟩
  intro x y ξ t ht
  dsimp only
  intro hξ htξ
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  have hcoord (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :
      covectorInChart c x (t • ξ₁) = t • covectorInChart c x ξ₁ := by ext l; rfl
  have hcoord' (c : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))) :
      covectorInChart c y (t • ξ₂) = t • covectorInChart c y ξ₂ := by ext l; rfl
  -- Each patch pair uses the same angular coefficient at the two radii.
  simp only [Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hleftData := hhigh i j x y (t • ξ₁) (t • ξ₂) htξ
  have hrightData := hhigh i j x y ξ₁ ξ₂ hξ
  have hleft := hleftData.2.trans
    (congrArg (fun c : ℝ ↦ (c : ℂ) • a x (t • ξ₁)) hleftData.1)
  have hright := hrightData.2.trans
    (congrArg (fun c : ℝ ↦ (c : ℂ) • a x ξ₁) hrightData.1)
  have hsplit₁ : ((t • ξ).comp e.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        t • ξ₁ := by ext v; rfl
  have hsplit₂ : ((t • ξ).comp e.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        t • ξ₂ := by ext v; rfl
  change (((A.patch i).productCutoffWeight (B.patch j) ε x y (t • ξ) : ℝ) : ℂ) •
      A.regularizedSymbolFunction a x (t • ξ₁) =
        (t : ℂ) • (((A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
          A.regularizedSymbolFunction a x ξ₁
  dsimp only [QuantizationPatch.productCutoffWeight]
  rw [hsplit₁, hsplit₂, hleft, hright]
  rw [hcoord, hcoord', norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hangular _ _ t ht]
  by_cases hzero : ξ₁ = 0
  · have hcoord0 : covectorInChart (A.patch i).chart x ξ₁ = 0 := by
      rw [hzero]
      ext l
      rfl
    simp [hcoord0, productCutoffAngular]
  · rw [ha x ξ₁ hzero t ht, Real.rpow_one, smul_comm]


/-- On a common exterior, the exact cutoff coefficient removes all dependence
on the original symbol's low-frequency regularization. -/
theorem QuantizationPresentation.exists_productCutoffWeight_regularizedSymbol_eq
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a : GlobalSymbolFunction (n := n) E₀ E₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (y : N)
      (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ),
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
      let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
      let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
        ((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
            A.regularizedSymbolFunction a x ξ₁ =
          ((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) • a x ξ₁ := by
  classical
  obtain ⟨R, hR, hhigh⟩ := exists_productCutoffWeight_regularizedSymbol_tail A B g k a ε hε
  refine ⟨R, hR, ?_⟩
  intro x y ξ
  dsimp only
  intro hξ
  simp only [Complex.ofReal_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (hhigh i j x y _ _ hξ).2

/-- Canonical product cutoffs preserve equality of two original symbols at infinity. -/
theorem QuantizationPresentation.exists_productCutoffWeight_smul_eq_of_eventually_eq
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a b : GlobalSymbolFunction (n := n) E₀ E₁) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (heq : ∀ x ξ, R₀ ≤ g.length x ξ → a x ξ = b x ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (y : N)
      (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ),
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
      let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
      let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
        ((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
            a x ξ₁ =
          ((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) • b x ξ₁ := by
  classical
  obtain ⟨R, hR, hhigh⟩ := exists_productCutoffWeight_tail_of_eq A B g k a b R₀ hR₀ heq ε hε
  refine ⟨R, hR, ?_⟩
  intro x y ξ
  dsimp only
  intro hξ
  simp only [Complex.ofReal_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (hhigh i j x y _ _ hξ).2

/-- Homogeneous full-symbol tails give homogeneous canonical cutoffs at infinity. -/
theorem QuantizationPresentation.exists_productCutoffWeight_homogeneous_of_tail
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a b : GlobalSymbolFunction (n := n) E₀ E₁)
    (hb : IsHomogeneousGlobalSymbol E₀ E₁ 1 b)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (htail : ∀ x ξ, R₀ ≤ g.length x ξ → a x ξ = b x ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (y : N)
      (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) (t : ℝ), 0 < t →
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
      let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
      let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
      R ≤ g.length x (t • ξ₁) + k.length y (t • ξ₂) →
        ((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y (t • ξ) : ℝ) : ℂ) •
            a x (t • ξ₁) =
          (t : ℂ) •
            (((∑ i, ∑ j, (A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
              a x ξ₁) := by
  classical
  obtain ⟨R, hRpos, hhigh⟩ :=
    exists_productCutoffWeight_tail_of_eq A B g k a b R₀ hR₀ htail ε hε
  have hangular (r s t : ℝ) (ht : 0 < t) :
      productCutoffAngular ε (t * r) (t * s) = productCutoffAngular ε r s := by
    by_cases hr : r = 0
    · simp [productCutoffAngular, hr]
    · simp only [productCutoffAngular, ite_eq_right hr, ite_eq_right (mul_ne_zero ht.ne' hr)]
      congr 2
      field_simp
  refine ⟨R, hRpos, ?_⟩
  intro x y ξ t ht
  dsimp only
  intro hξ htξ
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  have hcoord (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :
      covectorInChart c x (t • ξ₁) = t • covectorInChart c x ξ₁ := by ext l; rfl
  have hcoord' (c : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))) :
      covectorInChart c y (t • ξ₂) = t • covectorInChart c y ξ₂ := by ext l; rfl
  -- Each patch pair uses the same angular coefficient at the two radii.
  simp only [Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hleftData := hhigh i j x y (t • ξ₁) (t • ξ₂) htξ
  have hrightData := hhigh i j x y ξ₁ ξ₂ hξ
  have hleft := hleftData.2.trans
    (congrArg (fun c : ℝ ↦ (c : ℂ) • b x (t • ξ₁)) hleftData.1)
  have hright := hrightData.2.trans
    (congrArg (fun c : ℝ ↦ (c : ℂ) • b x ξ₁) hrightData.1)
  have hsplit₁ : ((t • ξ).comp e.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        t • ξ₁ := by ext v; rfl
  have hsplit₂ : ((t • ξ).comp e.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        t • ξ₂ := by ext v; rfl
  change (((A.patch i).productCutoffWeight (B.patch j) ε x y (t • ξ) : ℝ) : ℂ) •
      a x (t • ξ₁) =
        (t : ℂ) • (((A.patch i).productCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
          a x ξ₁
  dsimp only [QuantizationPatch.productCutoffWeight]
  rw [hsplit₁, hsplit₂, hleft, hright]
  rw [hcoord, hcoord', norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hangular _ _ t ht]
  by_cases hzero : ξ₁ = 0
  · have hcoord0 : covectorInChart (A.patch i).chart x ξ₁ = 0 := by
      rw [hzero]
      ext l
      rfl
    simp [hcoord0, productCutoffAngular]
  · rw [hb x ξ₁ hzero t ht, Real.rpow_one, smul_comm]

end AtiyahSinger
