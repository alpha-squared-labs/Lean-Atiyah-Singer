/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothSectionTopology
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Multiplication of smooth bundle sections by smooth functions

Public module ID: M0982.

D01/D04: actual pointwise scalar multiplication and its continuous action on the
C-infinity test topology. Fixed compact cutoff presentations give derivative
bounds of the same order. This is the ordinary module action of smooth functions,
not a new regularity assumption in a carrier. Sources: SG III.2.2 and 2.14;
Taylor I.1 (the usual topology of smooth tests).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

variable (f : M → ℂ)
  (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ f)

include hf in
/-- Pointwise multiplication by a real-smooth complex scalar preserves smooth sections. -/
theorem isSmoothSection_mul (u : smoothSections (n := n) (r := r) E) :
    IsSmoothSection (n := n) (r := r) E (fun x ↦ f x • u.val x) := by
  /- In each complex-linear frame the coordinate formula is f times the smooth
  coordinate vector of u. Scalar multiplication is a real-smooth bilinear map,
  so its composition is smooth on the frame base. No compactness is needed. -/
  intro e he
  let := he
  -- In the original input frame, the scalar multiplies the same section coordinates.
  have hsmul : ContDiff ℝ ∞ (fun z : ℂ × EuclideanSpace ℂ (Fin r) ↦ z.1 • z.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.smul contDiff_snd).restrict_scalars ℝ
  apply (hsmul.contMDiff.comp_contMDiffOn
    (hf.contMDiffOn.prodMk_space (u.property e he))).congr
  intro x hx
  exact (e.linear ℂ hx).2 (f x) (u.val x)

/-- The genuine complex-linear multiplication operator on smooth sections. -/
def smoothSectionMul : smoothSections (n := n) (r := r) E →ₗ[ℂ]
    smoothSections (n := n) (r := r) E where
  toFun u := ⟨fun x ↦ f x • u.val x, isSmoothSection_mul E f hf u⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    exact smul_add (f x) (u.val x) (v.val x)
  map_smul' c u := by
    apply Subtype.ext
    funext x
    exact smul_comm (f x) c (u.val x)

/-- The packaged multiplication retains the original fiberwise formula. -/
theorem smoothSectionMul_apply (u : smoothSections (n := n) (r := r) E) (x : M) :
    (smoothSectionMul (n := n) (r := r) E f hf u).val x = f x • u.val x := by
  /- Unfold the linear map's underlying section. Its smoothness certificate
  changes neither the base point nor the scalar multiplying the actual fiber. -/
  rfl

/-- Multiplication by the constant one function is the identity section map. -/
theorem smoothSectionMul_one
    (h1 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ (fun _ : M ↦ (1 : ℂ))) :
    smoothSectionMul (n := n) (r := r) E (fun _ ↦ 1) h1 = LinearMap.id := by
  /- Evaluate both linear maps on a section and then at every base point.
  The scalar identity one_smul gives the same section; proof fields are irrelevant. -/
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  exact one_smul ℂ (u.val x)

/-- Composition of two multiplication operators multiplies their scalar functions. -/
theorem smoothSectionMul_comp (g : M → ℂ)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ g)
    (hfg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ (f * g)) :
    (smoothSectionMul (n := n) (r := r) E f hf).comp (smoothSectionMul (n := n) (r := r) E g hg) =
      smoothSectionMul (n := n) (r := r) E (f * g) hfg := by
  /- Evaluate on each fiber and use associativity of scalar multiplication.
  The order is f after g. The right map uses the pointwise product and an
  explicit smoothness certificate, with no new section-space structure. -/
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  exact (mul_smul (f x) (g x) (u.val x)).symm

/-- Nonvanishing smooth scalar multiplication is a bijection on actual smooth sections. -/
theorem smoothSectionMul_bijective (hzero : ∀ x, f x ≠ 0) :
    Function.Bijective (smoothSectionMul (n := n) (r := r) E f hf) := by
  /- The reciprocal function is smooth because f is nowhere zero. Its actual
  pointwise multiplication is an inverse in both directions by the preceding
  composition identity. This needs no uniform lower bound on a noncompact base. -/
  -- Nonvanishing gives a smooth reciprocal without any global lower bound.
  have hinv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ (f x)⁻¹) := by
    intro x
    exact ((contDiffAt_inv ℝ (hzero x)).contMDiffAt).comp x (hf x)
  let T := smoothSectionMul (n := n) (r := r) E (fun x ↦ (f x)⁻¹) hinv
  have hleft : Function.LeftInverse T (smoothSectionMul (n := n) (r := r) E f hf) := by
    intro u
    apply Subtype.ext
    funext x
    change (f x)⁻¹ • (f x • u.val x) = u.val x
    rw [smul_smul, inv_mul_cancel₀ (hzero x), one_smul]
  have hright : Function.RightInverse T (smoothSectionMul (n := n) (r := r) E f hf) := by
    intro u
    apply Subtype.ext
    funext x
    change f x • ((f x)⁻¹ • u.val x) = u.val x
    rw [smul_smul, mul_inv_cancel₀ (hzero x), one_smul]
  exact ⟨hleft.injective, hright.surjective⟩

variable {E} (A : SmoothBundlePresentation (n := n) (r := r) E)
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hM hT2 hSC hE

/-- Each derivative seminorm is bounded at the same order under fixed smooth multiplication. -/
theorem exists_smoothSectionMul_seminorm_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : A.SmoothSectionSpace,
      A.smoothSectionSeminorm k (A.smoothSectionEquiv.symm
        (smoothSectionMul (n := n) (r := r) E f hf (A.smoothSectionEquiv u))) ≤
          C * A.smoothSectionSeminorm k u := by
  /- Localized multiplication is f times the already localized section.
  The Leibniz rule through order k uses only derivatives of that section through k.
  Derivatives of f in each chart are bounded on the fixed compact cutoff support.
  A finite maximum gives C, independent of u; empty presentations are harmless. -/
  classical
  let K (j : Fin A.size) := (A.chart j) '' tsupport (A.cutoff j)
  let F (j : Fin A.size) (z : EuclideanSpace ℝ (Fin n)) := f ((A.chart j).symm z)
  have hK (j : Fin A.size) : IsCompact (K j) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  have htarget (j : Fin A.size) : K j ⊆ (A.chart j).target := by
    rintro z ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (A.support_subset j hx).1
  -- The scalar is smooth on the original coordinate target, which contains the compact support.
  have hF (j : Fin A.size) : ContDiffOn ℝ ∞ (F j) (A.chart j).target := by
    intro z hz
    have hc := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) (A.chart_mem_atlas j)) hz
    exact ((hf.contMDiffAt).comp z hc).contDiffAt.contDiffWithinAt
  have hbounds (j : Fin A.size) (i : Fin (k + 1)) :
      ∃ B : ℝ, ∀ x ∈ K j,
        ‖iteratedFDerivWithin ℝ i.val (F j) (A.chart j).target x‖ ≤ B :=
    (hK j).exists_bound_of_continuousOn
      (((hF j).continuousOn_iteratedFDerivWithin (by simp)
        (A.chart j).open_target.uniqueDiffOn).mono (htarget j))
  choose B hB using hbounds
  let D (j : Fin A.size) : ℝ := 1 + ∑ i : Fin (k + 1), max 0 (B j i)
  have hDpos (j : Fin A.size) : 0 < D j := by
    dsimp [D]
    positivity
  have hDbound (j : Fin A.size) (i : ℕ) (hi : i ≤ k)
      (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K j) :
      ‖iteratedFDerivWithin ℝ i (F j) (A.chart j).target x‖ ≤ D j := by
    let i' : Fin (k + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
    have hterm : max 0 (B j i') ≤ ∑ l : Fin (k + 1), max 0 (B j l) :=
      Finset.single_le_sum (fun l _ ↦ le_max_left 0 (B j l)) (Finset.mem_univ i')
    exact (hB j i' x hx).trans ((le_max_right _ _).trans (hterm.trans (by dsimp [D]; linarith)))
  let C : ℝ := 1 + ∑ j : Fin A.size, (2 : ℝ) ^ k * D j
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro u
  let u₀ := A.smoothSectionEquiv u
  let v := smoothSectionMul (n := n) (r := r) E f hf u₀
  have hlocal (j : Fin A.size) : A.localizedFunction j v =
      fun z ↦ F j z • A.localizedFunction j u₀ z := by
    let := A.frame_mem_atlas j
    funext z
    by_cases hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j)
    · have hframe := (A.support_subset j hcut).2
      have hsmul : (A.frame j ⟨(A.chart j).symm z,
          f ((A.chart j).symm z) • u₀.val ((A.chart j).symm z)⟩).2 =
            f ((A.chart j).symm z) •
              (A.frame j ⟨(A.chart j).symm z, u₀.val ((A.chart j).symm z)⟩).2 :=
        ((A.frame j).linearEquivAt ℂ _ hframe).map_smul _ _
      by_cases hz : z ∈ (A.chart j).target
      · simp only [SmoothBundlePresentation.localizedFunction, ite_eq_left hz,
          sectionInChart]
        change (A.cutoff j ((A.chart j).symm z) : ℂ) •
          (A.frame j ⟨(A.chart j).symm z,
            f ((A.chart j).symm z) • u₀.val ((A.chart j).symm z)⟩).2 = _
        rw [hsmul, smul_comm]
      · simp [SmoothBundlePresentation.localizedFunction, hz]
    · simp [SmoothBundlePresentation.localizedFunction, image_eq_zero_of_notMem_tsupport hcut]
  have hnorm (j : Fin A.size) (i : ℕ) (hi : i ≤ k)
      (x : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ i (A.localizedFunction j u₀) x‖ ≤ A.smoothSectionSeminorm k u := by
    exact le_csSup (A.bddAbove_ckNorm_values k (A.smoothToCk k u₀)) ⟨j, i, hi, x, rfl⟩
  -- Leibniz estimates only use derivatives through the requested order and the same support.
  have hderiv (j : Fin A.size) (i : ℕ) (hi : i ≤ k)
      (x : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ i (A.localizedFunction j v) x‖ ≤ C * A.smoothSectionSeminorm k u := by
    by_cases hx : x ∈ K j
    · have hxt := htarget j hx
      have hproduct := norm_iteratedFDerivWithin_smul_le (hF j)
        (A.contDiff_localizedFunction j u₀).contDiffOn (A.chart j).open_target.uniqueDiffOn
        hxt (n := i) (by simp)
      rw [iteratedFDerivWithin_of_isOpen i (A.chart j).open_target hxt, ← hlocal] at hproduct
      have hterms :
          (∑ q ∈ Finset.range (i + 1), (i.choose q : ℝ) *
            ‖iteratedFDerivWithin ℝ q (F j) (A.chart j).target x‖ *
            ‖iteratedFDerivWithin ℝ (i - q) (A.localizedFunction j u₀)
              (A.chart j).target x‖) ≤
          (2 : ℝ) ^ i * D j * A.smoothSectionSeminorm k u := by
        calc
          _ ≤ ∑ q ∈ Finset.range (i + 1),
              (i.choose q : ℝ) * D j * A.smoothSectionSeminorm k u := by
            apply Finset.sum_le_sum
            intro q hq
            have hqi : q ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
            rw [iteratedFDerivWithin_of_isOpen (i - q) (A.chart j).open_target hxt]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (hDbound j q (hqi.trans hi) x hx) (by positivity))
              (hnorm j (i - q) ((Nat.sub_le i q).trans hi) x) (norm_nonneg _)
              (by positivity)
          _ = (2 : ℝ) ^ i * D j * A.smoothSectionSeminorm k u := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            congr 2
            exact_mod_cast Nat.sum_range_choose i
      have hconst : (2 : ℝ) ^ i * D j ≤ C := by
        have hpower : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi
        have hterm : (2 : ℝ) ^ k * D j ≤ ∑ l : Fin A.size, (2 : ℝ) ^ k * D l :=
          Finset.single_le_sum (fun l _ ↦ mul_nonneg (by positivity) (hDpos l).le)
            (Finset.mem_univ j)
        exact (mul_le_mul_of_nonneg_right hpower (hDpos j).le).trans
          (hterm.trans (by dsimp [C]; linarith))
      exact hproduct.trans (hterms.trans
        (mul_le_mul_of_nonneg_right hconst (apply_nonneg _ _)))
    · -- Off the common cutoff image every derivative of the localized output vanishes.
      have hnot : x ∉ tsupport (iteratedFDeriv ℝ i (A.localizedFunction j v)) := by
        intro hmem
        exact hx (A.tsupport_localizedFunction_subset j v (tsupport_iteratedFDeriv_subset i hmem))
      rw [image_eq_zero_of_notMem_tsupport hnot, norm_zero]
      exact mul_nonneg hC.le (apply_nonneg _ _)
  change A.ckNorm k (A.smoothToCk k v) ≤ C * A.smoothSectionSeminorm k u
  by_cases hsize : A.size = 0
  · have : IsEmpty (Fin A.size) := Fin.isEmpty_iff.mpr hsize
    simp only [SmoothBundlePresentation.ckNorm, IsEmpty.exists_iff, Set.ofPred_false,
      Real.sSup_empty]
    exact mul_nonneg hC.le (apply_nonneg _ _)
  · let j₀ : Fin A.size := ⟨0, Nat.pos_of_ne_zero hsize⟩
    refine csSup_le ?_ ?_
    · exact ⟨‖iteratedFDeriv ℝ 0 (A.localizedFunction j₀ v) 0‖,
        j₀, 0, Nat.zero_le k, 0, rfl⟩
    · rintro a ⟨j, i, hi, x, rfl⟩
      exact hderiv j i hi x

/-- Multiplication is continuous in the full smooth topology of the test space. -/
theorem continuous_smoothSectionMul :
    Continuous (fun u : A.SmoothSectionSpace ↦ A.smoothSectionEquiv.symm
      (smoothSectionMul (n := n) (r := r) E f hf (A.smoothSectionEquiv u))) := by
  /- Apply the preceding estimate to every output seminorm, using the explicit
  seminorm-family topology. The same-order bounds imply continuity of the linear
  map, without replacing smooth convergence by pointwise convergence. -/
  let T : A.SmoothSectionSpace →ₗ[ℂ] A.SmoothSectionSpace :=
    A.smoothSectionEquiv.symm.toLinearMap.comp
      ((smoothSectionMul (n := n) (r := r) E f hf).comp A.smoothSectionEquiv.toLinearMap)
  have hp := A.withSeminorms_smoothSectionTopology
  -- The previously proved same-order bounds use the original smooth-test topology on both sides.
  apply hp.continuous_of_isBounded hp T
  intro k
  obtain ⟨C, hC, hbound⟩ := exists_smoothSectionMul_seminorm_bound f hf A k
  refine ⟨{k}, ⟨C, hC.le⟩, ?_⟩
  intro u
  rw [Finset.sup_singleton]
  exact hbound u

/-- The same pointwise multiplier packaged as a continuous map on actual smooth tests. -/
def SmoothBundlePresentation.smoothMul : A.SmoothSectionSpace →L[ℂ] A.SmoothSectionSpace where
  toLinearMap := A.smoothSectionEquiv.symm.toLinearMap.comp
    ((smoothSectionMul (n := n) (r := r) E f hf).comp A.smoothSectionEquiv.toLinearMap)
  cont := continuous_smoothSectionMul f hf A

/-- Evaluation after test multiplication is evaluation of the multiplied section. -/
theorem SmoothBundlePresentation.smoothMul_apply (u : A.SmoothSectionSpace) (x : M) :
    (A.smoothSectionEquiv (A.smoothMul f hf u)).val x =
      f x • (A.smoothSectionEquiv u).val x := by
  /- Forget the presentation tag on both sides and apply smoothSectionMul_apply.
  The continuous packaging retains exactly the same fiberwise multiplication. -/
  rfl

end AtiyahSinger
