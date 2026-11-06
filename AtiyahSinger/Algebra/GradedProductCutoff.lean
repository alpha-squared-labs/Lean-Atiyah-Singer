/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol
public import AtiyahSinger.Analysis.ProductSymbolCutoff
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Topology.UnitInterval

/-!
# Hermitian graded tensor symbols and the product-frequency homotopy

Public module ID: M0031.

The finite-dimensional graded matrix in SG III.13.5, (13.12), uses the actual
Hermitian adjoints of the two original maps. Its even and odd spaces are the
same four tensor factors used by `reciprocalTensorSymbol`. Real weights scale
each original map and its adjoint together. If either weighted factor is
invertible, the entire graded matrix is invertible, without an equal-rank
assumption on the other factor.

The reciprocal-pair scalar-square theorem does not apply to arbitrary
adjoints. Here the positive operator squares on the two even summands give
injectivity of the original forward matrix. Either invertible factor equates
the total even and odd dimensions, so finite dimensionality gives surjectivity.
The linear equivalence below retains the original forward matrix exactly.

The scalar homotopy uses the existing product-frequency cutoff from SG p.250.
For `0 < epsilon <= 1`, the weight of the larger frequency is exactly one
throughout the homotopy. This permits one common compact control for two
eventually invertible factor symbols. It is not an assertion that a spatially
compactly supported local symbol is elliptic outside its spatial support.

The algebraic invertibility argument and the scalar cutoff properties fill
the exercise on SG p.250; they are project supplements, not newly numbered
lemmas of the book. Applications to bundles also require continuity and compact-support
hypotheses for the original factor symbols.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct unitInterval

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]

/-- SG's actual Hermitian graded matrix with the same real weight on each adjoint pair. -/
def weightedGradedTensorSymbol (d : E₀ →ₗ[ℂ] E₁) (e : F₀ →ₗ[ℂ] F₁)
    (α β : ℝ) :
    ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) →ₗ[ℂ]
      ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) :=
  reciprocalTensorSymbol ((α : ℂ) • d) ((α : ℂ) • d.adjoint)
    ((β : ℂ) • e) ((β : ℂ) • e.adjoint)

/-- One nonzero weighted invertible factor makes the original Hermitian graded matrix bijective. -/
theorem weightedGradedTensorSymbol_bijective
    (d : E₀ →ₗ[ℂ] E₁) (e : F₀ →ₗ[ℂ] F₁) (α β : ℝ)
    (h : (α ≠ 0 ∧ Function.Bijective d) ∨ (β ≠ 0 ∧ Function.Bijective e)) :
    Function.Bijective (weightedGradedTensorSymbol d e α β) := by
  /- First identify the adjoints of the real-weighted maps. Bijectivity
  of either weighted factor also gives bijectivity of its adjoint.
  Expand the formal reverse-after-forward composite on the two even
  tensor summands: the mixed terms cancel and each diagonal is a sum
  of operators of the form T* T. Pairing a kernel vector with these
  identities gives sums of squared norms. The invertible factor and
  its adjoint force both components of that vector to vanish.
  Finally, either invertible factor equates its own source and target
  dimensions. The tensor dimension formulas then equate the total even
  and odd dimensions, so injectivity gives surjectivity of the original
  matrix. The other factor may have unequal source and target ranks. -/
  -- Real weights retain the specified adjoint pairs.
  let D : E₀ →ₗ[ℂ] E₁ := (α : ℂ) • d
  let E : F₀ →ₗ[ℂ] F₁ := (β : ℂ) • e
  have hadjD : D.adjoint = (α : ℂ) • d.adjoint := by
    change LinearMap.adjoint ((α : ℂ) • d) = _
    rw [map_smulₛₗ]
    congr 1
    exact Complex.conj_ofReal α
  have hadjE : E.adjoint = (β : ℂ) • e.adjoint := by
    change LinearMap.adjoint ((β : ℂ) • e) = _
    rw [map_smulₛₗ]
    congr 1
    exact Complex.conj_ofReal β
  have hweighted : Function.Bijective D ∨ Function.Bijective E := by
    rcases h with ⟨hα, hd⟩ | ⟨hβ, he⟩
    · left
      exact (LinearEquiv.smulOfNeZero ℂ E₁ (α : ℂ) (by exact_mod_cast hα)).bijective.comp hd
    · right
      exact (LinearEquiv.smulOfNeZero ℂ F₁ (β : ℂ) (by exact_mod_cast hβ)).bijective.comp he
  -- Bijectivity of a finite-dimensional map also gives bijectivity of its actual adjoint.
  have hadjointD (hT : Function.Bijective D) : Function.Bijective D.adjoint := by
    have hdim := (LinearEquiv.ofBijective D hT).finrank_eq
    have hinj : Function.Injective D.adjoint := by
      rw [← LinearMap.ker_eq_bot, ← D.orthogonal_range,
        LinearMap.range_eq_top.mpr hT.2, Submodule.top_orthogonal_eq_bot]
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mp hinj⟩
  have hadjointE (hT : Function.Bijective E) : Function.Bijective E.adjoint := by
    have hdim := (LinearEquiv.ofBijective E hT).finrank_eq
    have hinj : Function.Injective E.adjoint := by
      rw [← LinearMap.ker_eq_bot, ← E.orthogonal_range,
        LinearMap.range_eq_top.mpr hT.2, Submodule.top_orthogonal_eq_bot]
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mp hinj⟩
  -- Expand the reverse composite before using positivity on each original tensor summand.
  let D₀ := TensorProduct.map D (LinearMap.id : F₀ →ₗ[ℂ] F₀)
  let D₁ := TensorProduct.map D.adjoint (LinearMap.id : F₁ →ₗ[ℂ] F₁)
  let e₀ := TensorProduct.map (LinearMap.id : E₀ →ₗ[ℂ] E₀) E
  let e₁ := TensorProduct.map (LinearMap.id : E₁ →ₗ[ℂ] E₁) E.adjoint
  let T := reciprocalTensorSymbol D D.adjoint E E.adjoint
  let S := reciprocalTensorSymbolReverse D D.adjoint E E.adjoint
  have hcomp : S.comp T =
      ((D₀.adjoint.comp D₀ + e₀.adjoint.comp e₀).comp (LinearMap.fst ℂ _ _)).prod
        ((D₁.adjoint.comp D₁ + e₁.adjoint.comp e₁).comp (LinearMap.snd ℂ _ _)) := by
    dsimp only [S, T, D₀, D₁, e₀, e₁]
    simp only [TensorProduct.adjoint_map, LinearMap.adjoint_id, LinearMap.adjoint_adjoint]
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
      intro x y <;> apply Prod.ext <;>
      simp [reciprocalTensorSymbol, reciprocalTensorSymbolReverse, add_comm]
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro z hz
      change T z = 0 at hz
      have hc : S (T z) = 0 := by rw [hz, map_zero]
      change (S.comp T) z = 0 at hc
      rw [hcomp] at hc
      have hc₀ := congrArg Prod.fst hc
      have hc₁ := congrArg Prod.snd hc
      change D₀.adjoint (D₀ z.1) + e₀.adjoint (e₀ z.1) = 0 at hc₀
      change D₁.adjoint (D₁ z.2) + e₁.adjoint (e₁ z.2) = 0 at hc₁
      -- Each diagonal is a sum of two squared norms, so no cancellation can hide a kernel.
      have hi₀ := congrArg (fun y ↦ (inner ℂ z.1 y).re) hc₀
      have hi₁ := congrArg (fun y ↦ (inner ℂ z.2 y).re) hc₁
      simp only [inner_add_right, LinearMap.adjoint_inner_right, inner_zero_right,
        Complex.add_re, Complex.zero_re] at hi₀ hi₁
      rw [show (inner ℂ (D₀ z.1) (D₀ z.1)).re = ‖D₀ z.1‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (D₀ z.1),
        show (inner ℂ (e₀ z.1) (e₀ z.1)).re = ‖e₀ z.1‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (e₀ z.1)] at hi₀
      rw [show (inner ℂ (D₁ z.2) (D₁ z.2)).re = ‖D₁ z.2‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (D₁ z.2),
        show (inner ℂ (e₁ z.2) (e₁ z.2)).re = ‖e₁ z.2‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (e₁ z.2)] at hi₁
      have hz₀ : D₀ z.1 = 0 ∧ e₀ z.1 = 0 := by
        constructor
        · apply norm_eq_zero.mp
          nlinarith only [hi₀, sq_nonneg ‖e₀ z.1‖, norm_nonneg (D₀ z.1)]
        · apply norm_eq_zero.mp
          nlinarith only [hi₀, sq_nonneg ‖D₀ z.1‖, norm_nonneg (e₀ z.1)]
      have hz₁ : D₁ z.2 = 0 ∧ e₁ z.2 = 0 := by
        constructor
        · apply norm_eq_zero.mp
          nlinarith only [hi₁, sq_nonneg ‖e₁ z.2‖, norm_nonneg (D₁ z.2)]
        · apply norm_eq_zero.mp
          nlinarith only [hi₁, sq_nonneg ‖D₁ z.2‖, norm_nonneg (e₁ z.2)]
      change z = 0
      apply Prod.ext
      · rcases hweighted with hD | hE
        · exact (TensorProduct.map_bijective hD Function.bijective_id).1
            (hz₀.1.trans (map_zero D₀).symm)
        · exact (TensorProduct.map_bijective Function.bijective_id hE).1
            (hz₀.2.trans (map_zero e₀).symm)
      · rcases hweighted with hD | hE
        · exact (TensorProduct.map_bijective (hadjointD hD) Function.bijective_id).1
            (hz₁.1.trans (map_zero D₁).symm)
        · exact (TensorProduct.map_bijective Function.bijective_id (hadjointE hE)).1
            (hz₁.2.trans (map_zero e₁).symm)
    · exact bot_le
  -- Either invertible factor equates the total even and odd dimensions.
  have hdim : Module.finrank ℂ ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) =
      Module.finrank ℂ ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) := by
    simp only [Module.finrank_prod, Module.finrank_tensorProduct]
    rcases hweighted with hD | hE
    · rw [(LinearEquiv.ofBijective D hD).finrank_eq]
    · rw [(LinearEquiv.ofBijective E hE).finrank_eq]
      omega
  have hbij : Function.Bijective T :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  simpa only [T, hadjD, hadjE, weightedGradedTensorSymbol, D, E] using hbij

/-- The equivalence whose forward action is exactly the specified Hermitian graded matrix. -/
def weightedGradedTensorSymbolEquiv
    (d : E₀ →ₗ[ℂ] E₁) (e : F₀ →ₗ[ℂ] F₁) (α β : ℝ)
    (h : (α ≠ 0 ∧ Function.Bijective d) ∨ (β ≠ 0 ∧ Function.Bijective e)) :
    ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) ≃ₗ[ℂ]
      ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) :=
  LinearEquiv.ofBijective (weightedGradedTensorSymbol d e α β)
    (weightedGradedTensorSymbol_bijective d e α β h)

/-- Linear interpolation from the unchanged factor to its original SG frequency cutoff. -/
def productCutoffHomotopyWeight (ε : ℝ) (t : unitInterval) (r s : ℝ) : ℝ :=
  1 - (t : ℝ) + (t : ℝ) * productFrequencyCutoff ε r s

/-- The actual SG interpolation has its endpoints, bounded weights, and unchanged larger factor. -/
theorem productCutoffHomotopyWeight_properties
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    (∀ r s : ℝ, productCutoffHomotopyWeight ε 0 r s = 1 ∧
      productCutoffHomotopyWeight ε 1 r s = productFrequencyCutoff ε r s) ∧
    (∀ (t : unitInterval) (r s : ℝ),
      productCutoffHomotopyWeight ε t r s ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ (t : unitInterval) (r s : ℝ), 0 ≤ r → 0 ≤ s → s ≤ r →
      productCutoffHomotopyWeight ε t r s = 1) ∧
    Continuous (fun z : unitInterval × (ℝ × ℝ) ↦
      productCutoffHomotopyWeight ε z.1 z.2.1 z.2.2) := by
  /- Stage 1: substitute the two actual unit-interval endpoints into the
  affine formula. The fixed bump and its complement take values in [0,1].
  Both branches of productFrequencyCutoff are complements of products of
  numbers in that interval, including its stipulated axis branch. The
  interpolation is a convex combination of one and this same cutoff
  value, so every intermediate weight remains in [0,1].
  Stage 2: when 0<r and 0<=s<=r, epsilon*s/r lies in [0,1]. The ratio
  profile vanishes and the exact cutoff is one, regardless of its radial
  profile. When r=0, these inequalities force s=0; the radial profile
  vanishes and the axis branch again gives one. Hence the full homotopy
  weight of the larger frequency is one. Interchanging r and s supplies
  the other factor. The chosen epsilon<=1 bound is sufficient; no assertion
  for every positive epsilon is made, since both cutoffs can vanish when
  epsilon>=2 and the two equal frequencies are sufficiently large.
  Stage 3: off the first frequency axis, continuity follows by ordinary
  composition, with the nonzero denominator r. Near the joint origin the
  radial profile vanishes, so the whole original cutoff is identically
  one; continuity does not require continuity of s/r at that origin.
  Near r=0 and s nonzero, the magnitude of epsilon*s/r is at least
  two for sufficiently small nonzero r. The chosen bump complement then
  equals one, on both sides of the axis. Thus the off-axis formula equals
  the specified axis value 1-phi(epsilon*sqrt(r^2+s^2)) on a neighborhood.
  This proves continuity on the full real plane, including negative radii
  admitted by the auxiliary definition. The radii used by symbols are norms.
  Finally take the displayed affine combination with the continuous
  unit-interval coordinate. This retains the same cutoff at the endpoint
  and gives joint continuity of this actual family. -/
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hprofile (x : ℝ) : productCutoffProfile x = 1 - bump x := rfl
  have hpcont : Continuous productCutoffProfile := continuous_const.sub bump.continuous
  have hpbound (x : ℝ) : productCutoffProfile x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hprofile]
    exact ⟨sub_nonneg.mpr bump.le_one, sub_le_self _ bump.nonneg⟩
  have hpzero (x : ℝ) (hx : |x| ≤ 1) : productCutoffProfile x = 0 := by
    rw [hprofile, bump.one_of_mem_closedBall]
    · simp
    · simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
  have hpone (x : ℝ) (hx : 2 ≤ |x|) : productCutoffProfile x = 1 := by
    rw [hprofile, bump.zero_of_le_dist]
    · simp
    · simpa only [Real.dist_eq, sub_zero] using hx
  -- Bounds retain the stipulated axis branch on the whole real plane.
  have hbound (r s : ℝ) : productFrequencyCutoff ε r s ∈ Set.Icc (0 : ℝ) 1 := by
    have ha := hpbound (ε * Real.sqrt (r ^ 2 + s ^ 2))
    have hb : (if r = 0 then 1 else productCutoffProfile (ε * s / r)) ∈
        Set.Icc (0 : ℝ) 1 := by
      split_ifs
      · exact ⟨zero_le_one, le_refl _⟩
      · exact hpbound _
    dsimp [productFrequencyCutoff]
    constructor
    · have hm := mul_le_mul ha.2 hb.2 hb.1 (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
    · have hm := mul_nonneg ha.1 hb.1
      linarith
  -- The larger nonnegative frequency always retains the original factor.
  have hlarger (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r) :
      productFrequencyCutoff ε r s = 1 := by
    by_cases hz : r = 0
    · have hsz : s = 0 := le_antisymm (hz ▸ hsr) hs
      subst r
      subst s
      simp [productFrequencyCutoff, hpzero 0 (by norm_num)]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
      have hn : 0 ≤ ε * s / r := div_nonneg (mul_nonneg hε.le hs) hr
      have hl : ε * s / r ≤ 1 := (div_le_one hrpos).mpr (by nlinarith)
      rw [productFrequencyCutoff, ite_eq_right hz, hpzero (ε * s / r) (by rwa [abs_of_nonneg hn])]
      simp
  -- Use local formulas off the axis, at the origin, and on the punctured axis.
  have hradial : Continuous (fun z : ℝ × ℝ ↦ ε * Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) := by
    fun_prop
  have hcutoff : Continuous (fun z : ℝ × ℝ ↦ productFrequencyCutoff ε z.1 z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hr : z.1 = 0
    · by_cases hs : z.2 = 0
      · have hevent : ∀ᶠ w : ℝ × ℝ in nhds z,
            ε * Real.sqrt (w.1 ^ 2 + w.2 ^ 2) < 1 :=
          hradial.continuousAt.eventually (gt_mem_nhds (by simp [hr, hs]))
        apply (continuous_const (y := (1 : ℝ))).continuousAt.congr_of_eventuallyEq
        filter_upwards [hevent] with w hw
        have hn : 0 ≤ ε * Real.sqrt (w.1 ^ 2 + w.2 ^ 2) :=
          mul_nonneg hε.le (Real.sqrt_nonneg _)
        rw [productFrequencyCutoff, hpzero _ (by rw [abs_of_nonneg hn]; exact hw.le)]
        simp
      · have hl : Continuous (fun w : ℝ × ℝ ↦ 2 * |w.1|) := by fun_prop
        have hu : Continuous (fun w : ℝ × ℝ ↦ |ε * w.2|) := by fun_prop
        have hevent : ∀ᶠ w : ℝ × ℝ in nhds z, 2 * |w.1| < |ε * w.2| :=
          hl.continuousAt.eventually_lt hu.continuousAt (by
            simpa only [hr, abs_zero, mul_zero] using abs_pos.mpr (mul_ne_zero hε.ne' hs))
        have hc : Continuous (fun w : ℝ × ℝ ↦
            1 - productCutoffProfile (ε * Real.sqrt (w.1 ^ 2 + w.2 ^ 2))) :=
          continuous_const.sub (hpcont.comp hradial)
        apply hc.continuousAt.congr_of_eventuallyEq
        filter_upwards [hevent] with w hw
        by_cases hwzero : w.1 = 0
        · simp [productFrequencyCutoff, hwzero]
        · have hratio : 2 ≤ |ε * w.2 / w.1| := by
            rw [abs_div]
            exact (le_div_iff₀ (abs_pos.mpr hwzero)).mpr hw.le
          simp [productFrequencyCutoff, hwzero, hpone _ hratio]
    · have hne : ∀ᶠ w : ℝ × ℝ in nhds z, w.1 ≠ 0 :=
        continuous_fst.continuousAt.eventually (isOpen_ne.mem_nhds hr)
      have hratio : ContinuousAt (fun w : ℝ × ℝ ↦ ε * w.2 / w.1) z := by fun_prop
      have hc : ContinuousAt (fun w : ℝ × ℝ ↦
          1 - productCutoffProfile (ε * Real.sqrt (w.1 ^ 2 + w.2 ^ 2)) *
            productCutoffProfile (ε * w.2 / w.1)) z :=
        continuousAt_const.sub ((hpcont.continuousAt.comp hradial.continuousAt).mul
          (hpcont.continuousAt.comp hratio))
      apply hc.congr_of_eventuallyEq
      filter_upwards [hne] with w hw
      simp only [productFrequencyCutoff, ite_eq_right hw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s
    simp [productCutoffHomotopyWeight]
  · intro t r s
    have ht : (0 : ℝ) ≤ t := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hc := hbound r s
    have hm := mul_nonneg ht hc.1
    have hu := mul_le_mul_of_nonneg_left hc.2 ht
    dsimp [productCutoffHomotopyWeight]
    constructor <;> linarith
  · intro t r s hr hs hsr
    rw [productCutoffHomotopyWeight, hlarger r s hr hs hsr]
    ring
  · exact (continuous_const.sub continuous_fst.subtype_val).add
      (continuous_fst.subtype_val.mul (hcutoff.comp continuous_snd))

end AtiyahSinger
