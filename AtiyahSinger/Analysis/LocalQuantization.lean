/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Amplitude
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Localization near the diagonal

Public module ID: M0788.

SG Corollary 3.7, using the concrete reduction in Theorem 3.5.
The cutoff is an actual mathlib smooth bump evaluated at x-y. A spatially compact
symbol p yields a compactly supported amplitude χ(x,y)p(x,ξ), an exact reduced
symbol, and an ε-local quantization. Its difference from p is in S^(-∞).
The difference of the two quantizations improves arbitrary real Sobolev orders.

Although χp has compact (x,y) support, (χ-1)p generally does not. The smoothing
claim is therefore obtained by comparing the full expansions, not by applying
the compact-amplitude theorem to (χ-1)p. Global bundle gluing remains separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

variable {n r q : ℕ}

/-- A standard smooth cutoff, one for dist(x,y) ≤ ε/2 and zero for dist(x,y) ≥ ε. -/
def diagonalCutoff (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ :=
  fun z ↦ (⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩ :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (z.1 - z.2)

/-- The diagonal cutoff is jointly smooth even at x=y. -/
theorem contDiff_diagonalCutoff (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (diagonalCutoff n ε hε) := by
  /- The chosen ContDiffBump is smooth on the whole Euclidean space. Compose it
  with the continuous linear difference map (x,y)↦x-y. This also handles the diagonal;
  no differentiability assertion about the unsquared distance at zero is needed. -/
  -- The spatial difference is smooth, including on the diagonal.
  exact (ContDiffBump.contDiff _).comp (contDiff_fst.sub contDiff_snd)

/-- The cutoff is identically one on a fixed neighborhood of the diagonal. -/
theorem diagonalCutoff_eq_one (ε : ℝ) (hε : 0 < ε)
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : dist x y ≤ ε / 2) :
    diagonalCutoff n ε hε (x, y) = 1 := by
  /- The vector x-y lies in the inner closed ball of the bump, because its norm
  equals dist(x,y). Apply ContDiffBump.one_of_mem_closedBall with inner radius ε/2;
  positivity of ε ensures a nonempty open neighborhood on which this remains one. -/
  -- The inner closed ball is evaluated on the actual spatial difference.
  apply ContDiffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hxy

/-- The cutoff vanishes at and beyond the prescribed distance. -/
theorem diagonalCutoff_eq_zero (ε : ℝ) (hε : 0 < ε)
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : ε ≤ dist x y) :
    diagonalCutoff n ε hε (x, y) = 0 := by
  /- The distance of x-y from zero is at least the outer radius ε.
  Apply the bump's zero_of_le_dist property. In particular the assertion includes
  the boundary of the outer ball, which is needed for the closed support bound. -/
  -- The outer-radius inequality includes its boundary.
  apply ContDiffBump.zero_of_le_dist
  simpa only [dist_zero_right, dist_eq_norm, sub_zero] using hxy

/-- Multiply a left symbol by a cutoff in the two spatial variables. -/
def localizedAmplitude
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r q) : AmplitudeFunction n r q :=
  fun x y ξ ↦ χ (x, y) • p x ξ

/-- A smooth spatial cutoff preserves the amplitude order. -/
theorem isAmplitude_localizedAmplitude (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) : IsAmplitude m (localizedAmplitude χ p) := by
  /- Joint smoothness follows by pullback and scalar multiplication. On a compact
  spatial-pair set, all derivatives of χ are bounded, and the x projection is compact.
  Apply Leibniz to the mixed derivatives. All frequency derivatives fall on p,
  so the estimate loses precisely one order per frequency derivative and none in x or y. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
  -- Derivatives in one variable retain joint smoothness in the other variable.
  have parametric {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
      ContDiff ℝ ∞ (fun z : P × P ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
    induction k with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ P V).symm : _ →L[ℝ] P [×0]→L[ℝ] V)
    | succ k ih =>
      have h : ContDiff ℝ ∞
          (Function.uncurry (fun z : P × P ↦ fun η : P ↦ iteratedFDeriv ℝ k (f z.1) η)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : P × P ↦ fderiv ℝ (iteratedFDeriv ℝ k (f z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ P) V).symm :
          _ →L[ℝ] P [×(k + 1)]→L[ℝ] V)
  refine ⟨(hχ.comp contDiff_fst).smul
    (hps.comp (contDiff_fst.fst.prodMk contDiff_snd)), ?_⟩
  intro K hK i j k
  let B := ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin j ↦ P) (P [×k]→L[ℝ] H)
  let dχ (x y : P) := iteratedFDeriv ℝ j (fun z ↦ χ (x, z)) y
  let dp (x ξ : P) := iteratedFDeriv ℝ k (p x) ξ
  have hdχ : ContDiff ℝ ∞ (Function.uncurry dχ) :=
    parametric (fun x y ↦ χ (x, y)) hχ j
  have hdp : ContDiff ℝ ∞ (Function.uncurry dp) := parametric p hps k
  -- Bound every spatial derivative of the cutoff on the same original compact pair set.
  have hbounded (l : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K →
      ‖iteratedFDeriv ℝ l (fun z ↦ dχ z y) x‖ ≤ C := by
    have hsmooth : ContDiff ℝ ∞ (fun z : P × P ↦
        iteratedFDeriv ℝ l (fun x ↦ dχ x z.2) z.1) :=
      (parametric (fun y x ↦ dχ x y)
        (hdχ.comp (contDiff_snd.prodMk contDiff_fst)) l).comp
          (contDiff_snd.prodMk contDiff_fst)
    obtain ⟨C, hC⟩ := (hK.image hsmooth.continuous.norm).bddAbove
    exact ⟨max C 0, le_max_right _ _, fun x y hxy ↦
      (hC ⟨(x, y), hxy, rfl⟩).trans (le_max_left _ _)⟩
  choose C hC hc using hbounded
  choose D hD hd using fun l ↦
    hp.2 (Prod.fst '' K) (Set.subset_univ _) (hK.image continuous_fst) l k
  refine ⟨∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * C l * D (i - l),
    Finset.sum_nonneg (fun l _ ↦ mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hC l)) (hD (i - l))), ?_⟩
  intro x y hxy ξ
  -- Frequency derivatives hit only p; input-position derivatives hit only the cutoff.
  have hfreq (z w : P) :
      iteratedFDeriv ℝ k (localizedAmplitude χ p z w) ξ = χ (z, w) • dp z ξ := by
    exact iteratedFDeriv_const_smul_apply'
      ((hps.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  have hderivative : amplitudeDerivative (localizedAmplitude χ p) i j k x y ξ =
      iteratedFDeriv ℝ i (fun z ↦ B (dχ z y) (dp z ξ)) x := by
    unfold amplitudeDerivative
    simp only [hfreq]
    congr 1
    funext z
    have hχz : ContDiffAt ℝ j (fun w ↦ χ (z, w)) y :=
      (hχ.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp)
    rw [iteratedFDeriv_smul_const_apply hχz]
    rfl
  rw [hderivative]
  have hχx : ContDiff ℝ ∞ (fun z ↦ dχ z y) :=
    hdχ.comp (contDiff_id.prodMk contDiff_const)
  have hpx : ContDiff ℝ ∞ (fun z ↦ dp z ξ) :=
    hdp.comp (contDiff_id.prodMk contDiff_const)
  have hle := B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hχx hpx x (n := i) (by simp)
    ContinuousMultilinearMap.norm_smulRightL_le
  apply hle.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l hl
  have hpBound := hd (i - l) x ⟨(x, y), hxy, rfl⟩ ξ
  change ‖iteratedFDeriv ℝ (i - l) (fun z ↦ dp z ξ) x‖ ≤ _ at hpBound
  calc
    (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun z ↦ dχ z y) x‖ *
        ‖iteratedFDeriv ℝ (i - l) (fun z ↦ dp z ξ) x‖ ≤
        (i.choose l : ℝ) * C l * (D (i - l) * (1 + ‖ξ‖) ^ (m - (k : ℝ))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hc l x y hxy) (Nat.cast_nonneg _)) hpBound
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC l))
    _ = _ := by ring

-- Compactness of the spatial band does not require positivity of ε.
set_option linter.unusedVariables false in
/-- Compact x support and a bounded diagonal band give uniform compact (x,y) support. -/
theorem hasCompactSupport_localizedAmplitude (p : SymbolFunction n r q)
    (hp : HasCompactSupport p)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hfar : ∀ x y, ε ≤ dist x y → χ (x, y) = 0) :
    HasCompactSupport (Function.uncurry (localizedAmplitude χ p)) := by
  /- Nonzero values require x in tsupport(p) and dist(x,y)<ε. The closed set
  where x belongs to that compact set and dist(x,y)≤ε is bounded in the finite-dimensional
  product space, hence compact. It contains the closure of the amplitude's spatial support.
  The support is uniform in ξ because hp concerns x↦p(x,·), not each fixed frequency. -/
  -- Parametrize the closed diagonal band by a compact base point and a bounded difference.
  let L (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (z.1, z.1 - z.2)
  have hL : Continuous L := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  have hK : IsCompact (L '' (tsupport p ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε)) :=
    (hp.prod (isCompact_closedBall _ _)).image hL
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ hK.isClosed
  intro z hz
  have hzp : z.1 ∈ tsupport p := by
    by_contra hzout
    have hpzero : p z.1 = 0 := image_eq_zero_of_notMem_tsupport hzout
    apply hz
    funext ξ
    simp [Function.uncurry, localizedAmplitude, hpzero]
  have hdist : dist z.1 z.2 ≤ ε := by
    by_contra hdist
    have hχzero := hfar z.1 z.2 (le_of_lt (lt_of_not_ge hdist))
    change χ z = 0 at hχzero
    apply hz
    funext ξ
    simp [Function.uncurry, localizedAmplitude, hχzero]
  refine ⟨(z.1, z.1 - z.2), ⟨hzp, ?_⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hdist
  · simp [L]

/-- If the cutoff is one near the diagonal, only the zeroth expansion coefficient survives. -/
theorem amplitudeExpansionTerm_localizedAmplitude
    (p : SymbolFunction n r q)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hnear : ∀ x y, dist x y ≤ δ → χ (x, y) = 1) (j : ℕ) :
    amplitudeExpansionTerm (localizedAmplitude χ p) j = if j = 0 then p else 0 := by
  /- For j=0 the diagonal value is p because χ(x,x)=1. For j>0, with x and η fixed,
  the function y↦χ(x,y)p(x,η) is constant on an open neighborhood of y=x. Thus its
  j-th y derivative there is zero for every η, and all subsequent η derivatives vanish.
  This only uses the cutoff's local constancy; no symbol estimates on p are needed. -/
  classical
  by_cases hj : j = 0
  · -- Zeroth derivatives evaluate the diagonal, where the cutoff is one.
    simp only [hj, amplitudeExpansionTerm_zero]
    funext x ξ
    simp [localizedAmplitude, hnear x x (by simpa using hδ.le)]
  · -- Every positive input-position derivative vanishes on the constant diagonal germ.
    simp only [ite_eq_right hj]
    funext x ξ
    have hyderiv (η : EuclideanSpace ℝ (Fin n)) :
        iteratedFDeriv ℝ j (fun y ↦ localizedAmplitude χ p x y η) x = 0 := by
      have hlocal : (fun y ↦ localizedAmplitude χ p x y η) =ᶠ[nhds x]
          (fun _ ↦ p x η) := by
        filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
        have hxy : dist x y ≤ δ := by
          simpa only [dist_comm] using (Metric.mem_ball.mp hy).le
        simp [localizedAmplitude, hnear x y hxy]
      have heq := (hlocal.iteratedFDeriv ℝ j).eq_of_nhds
      simpa only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply] using heq
    -- This zero family is differentiated in frequency only after the input derivative.
    simp [amplitudeExpansionTerm, hyderiv, iteratedFDeriv_const_of_ne hj]

-- The output-support argument uses only the distance band.
set_option linter.unusedVariables false in
/-- Cutting the amplitude to the diagonal band restricts the actual output support. -/
theorem tsupport_amplitudeApply_localizedAmplitude
    (p : SymbolFunction n r q)
    (χ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hfar : ∀ x y, ε ≤ dist x y → χ (x, y) = 0)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    tsupport (amplitudeApply (localizedAmplitude χ p) u) ⊆
      Metric.cthickening ε (tsupport u) := by
  /- Outside the closed ε-thickening, every y in the support of u has dist(x,y)>ε,
  so the cutoff vanishes. At all other y, u(y)=0. The integrand is therefore zero
  for every frequency, and the output vanishes. Since the thickening is closed,
  it also contains the closure of the output support. No integral interchange is used. -/
  -- A point outside the closed thickening cannot interact with any nonzero input value.
  apply closure_minimal ?_ Metric.isClosed_cthickening
  intro x hx
  by_contra hxout
  have hzero (ξ y : EuclideanSpace ℝ (Fin n)) :
      Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
        localizedAmplitude χ p x y ξ (u y) = 0 := by
    by_cases hy : y ∈ tsupport u
    · have hdist : ε ≤ dist x y := by
        by_contra hdist
        exact hxout (Metric.mem_cthickening_of_dist_le x y ε (tsupport u) hy
          (le_of_lt (lt_of_not_ge hdist)))
      simp [localizedAmplitude, hfar x y hdist]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  apply hx
  simp [amplitudeApply, hzero]

/-- The actual reduced symbol for SG's ε-local replacement of a spatially compact symbol. -/
def localizedSymbol (p : SymbolFunction n r q) (ε : ℝ) (hε : 0 < ε) :
    SymbolFunction n r q :=
  amplitudeSymbol (localizedAmplitude (diagonalCutoff n ε hε) p)

/-- The ε-local replacement has the same allowed order as the original symbol. -/
theorem isSymbol_localizedSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p) (ε : ℝ) (hε : 0 < ε) :
    IsSymbol Set.univ m (localizedSymbol p ε hε) := by
  /- The explicit diagonal cutoff is smooth and zero outside the ε band. Together
  with the uniform compact x support of p this makes χp a compactly supported
  amplitude of order m. Apply the exact symbol reduction theorem to this amplitude. -/
  exact isSymbol_amplitudeSymbol m _
    (isAmplitude_localizedAmplitude m p hp _ (contDiff_diagonalCutoff ε hε))
    (hasCompactSupport_localizedAmplitude p hsupp _ ε hε (diagonalCutoff_eq_zero ε hε))

/-- The replacement retains uniform compact support in the output variable. -/
theorem hasCompactSupport_localizedSymbol (p : SymbolFunction n r q)
    (hsupp : HasCompactSupport p) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (localizedSymbol p ε hε) := by
  /- The cutoff amplitude has compact spatial support, using hsupp and the distance band.
  Its reduced symbol has compact x support by the first-projection support argument.
  These support arguments use the actual integral formula and need no symbol estimates. -/
  -- Use the same actual diagonal cutoff and its already controlled compact spatial support.
  exact hasCompactSupport_amplitudeSymbol _
    (hasCompactSupport_localizedAmplitude p hsupp (diagonalCutoff n ε hε) ε hε
      (diagonalCutoff_eq_zero ε hε))

/-- SG Corollary 3.7: localization changes the symbol only by a smoothing symbol. -/
theorem isSmoothingSymbol_localizedSymbol_sub (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p) (ε : ℝ) (hε : 0 < ε) :
    IsSmoothingSymbol Set.univ (localizedSymbol p ε hε - p) := by
  /- The full amplitude expansion of χp has zeroth term p and all positive-degree
  terms zero, because χ=1 near the diagonal. For every N≥1 the remainder estimate
  therefore puts the difference in S^(m-N); these orders tend to negative infinity.
  Do not apply the compact-amplitude theorem to (χ-1)p: that difference need not
  have compact y support. Comparison of the expansion coefficients avoids this gap. -/
  have hexp := hasSymbolExpansion_amplitudeSymbol m _
    (isAmplitude_localizedAmplitude m p hp _ (contDiff_diagonalCutoff ε hε))
    (hasCompactSupport_localizedAmplitude p hsupp _ ε hε (diagonalCutoff_eq_zero ε hε))
  have hterms (j : ℕ) :
      amplitudeExpansionTerm (localizedAmplitude (diagonalCutoff n ε hε) p) j =
        if j = 0 then p else 0 :=
    amplitudeExpansionTerm_localizedAmplitude p _ (ε / 2) (by positivity)
      (diagonalCutoff_eq_one ε hε) j
  intro l
  obtain ⟨N, hN⟩ := exists_nat_gt (m - l)
  have h := hexp (N + 1)
  have hsum : (∑ j ∈ Finset.range (N + 1),
      amplitudeExpansionTerm (localizedAmplitude (diagonalCutoff n ε hε) p) j) = p := by
    simp_rw [hterms]
    simp
  rw [hsum] at h
  exact h.mono (by push_cast; linarith)

/-- SG (3.7): the replacement is ε-local on the actual Schwartz inputs. -/
theorem tsupport_quantize_localizedSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p) (ε : ℝ) (hε : 0 < ε)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    tsupport (quantize (localizedSymbol p ε hε) u) ⊆
      Metric.cthickening ε (tsupport u) := by
  /- The exact amplitude-to-symbol identity identifies this quantization with the
  integral for χp. The cutoff vanishes whenever dist(x,y)≥ε, so the preceding
  support lemma places the output inside the closed ε-thickening of the input support.
  Schwartz inputs include smooth compactly supported inputs, as used in SG (3.7). -/
  have hreduce := quantize_amplitudeSymbol m (localizedAmplitude (diagonalCutoff n ε hε) p)
    (isAmplitude_localizedAmplitude m p hp _ (contDiff_diagonalCutoff ε hε))
    (hasCompactSupport_localizedAmplitude p hsupp _ ε hε (diagonalCutoff_eq_zero ε hε)) u
  change tsupport (quantize (amplitudeSymbol _) u) ⊆ _
  rw [hreduce]
  exact tsupport_amplitudeApply_localizedAmplitude p _ ε hε
    (diagonalCutoff_eq_zero ε hε) u

/-- The difference of the two actual quantizations improves arbitrary real Sobolev orders. -/
theorem exists_sobolev_extension_localizedSymbol_sub (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hsupp : HasCompactSupport p) (ε : ℝ) (hε : 0 < ε)
    (s t : ℝ) :
    ∃ T : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          besselRealization n q t (T (schwartzSobolevCoordinate s u)) φ =
            ∫ x, φ x • (quantize (localizedSymbol p ε hε) u x - quantize p u x) := by
  /- The difference symbol is smoothing and has compact x support, the latter inside
  the union of the two compact supports. Use its order s-t estimate in the existing
  quantization extension theorem. On Schwartz inputs both frequency integrals are
  integrable, so quantization of the difference is exactly the difference of quantizations.
  This gives SG's all-order equivalence, with the actual Sobolev realization specified. -/
  have hlocalized : IsSymbol Set.univ m (localizedSymbol p ε hε) :=
    isSymbol_localizedSymbol m p hp hsupp ε hε
  have hdiff : IsSymbol Set.univ (s - t) (localizedSymbol p ε hε - p) :=
    isSmoothingSymbol_localizedSymbol_sub m p hp hsupp ε hε (s - t)
  have hcompact : HasCompactSupport (localizedSymbol p ε hε - p) :=
    (hasCompactSupport_localizedSymbol p hsupp ε hε).sub hsupp
  -- Each fixed spatial symbol is a temperate multiplier of the Schwartz Fourier transform.
  have hInt (b : SymbolFunction n r q) (hb : IsSymbol Set.univ m b)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (x : EuclideanSpace ℝ (Fin n)) :
      Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        b x ξ (fourierSG u ξ)) := by
    let X := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let F := EuclideanSpace ℂ (Fin q)
    have hg : (b x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry b) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using hb.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := hb.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈m - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have h := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
        apply h.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase : (fun ξ : X ↦
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : X ≃L[ℝ] X :=
      (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).flip (hphase.smul hg) w).integrable
  -- The smoothing difference has the exact order needed for this pair of Sobolev spaces.
  obtain ⟨T, hT⟩ := exists_quantize_sobolev_extension (s - t) s
    (localizedSymbol p ε hε - p) hdiff (tsupport (localizedSymbol p ε hε - p)) hcompact
    (fun x hx ξ ↦ congrFun (image_eq_zero_of_notMem_tsupport hx) ξ)
  have horder : s - (s - t) = t := by ring
  simp only [horder] at hT
  refine ⟨T, ?_⟩
  intro u φ
  rw [hT]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  -- Subtraction commutes with the original frequency integrals by the two L¹ checks.
  simp only [quantize, Pi.sub_apply, sub_apply, smul_sub]
  rw [integral_sub (hInt _ hlocalized u x) (hInt p hp u x), smul_sub]

end AtiyahSinger
