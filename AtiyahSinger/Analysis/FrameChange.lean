/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange

/-!
# Changes of bundle frames for local pseudodifferential operators

Public module ID: M0639.

The bundle-trivialization step in SG III.3.15 and 3.18, pp.186-187.
Apply the actual amplitude reduction of III.3.5 to A(x) p(x,ξ) B(y).
For changes from old to new frames, the input factor is the inverse transition:
the operator is A P B⁻¹ and its principal class is represented by A p B⁻¹.

Frame matrices need only be smooth on an open overlap. Compact cutoffs inside it
give genuine continuous Schwartz multipliers. Two-sided operator support removes
the cutoff dependence. No global growth, Hermitian or unitarity assumption is used.
The full left symbol need not equal the pointwise transformed principal symbol.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

variable {n r q k l : ℕ}

/-- A scalar cutoff times an actual matrix function. -/
def cutoffMatrix (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) :
    EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
  fun x ↦ χ x • A x

/-- Local smoothness suffices for a matrix cut off strictly inside its open domain. -/
theorem contDiff_cutoffMatrix (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hA : ContDiffOn ℝ ∞ A U) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (cutoffMatrix χ A) := by
  /- On U use the product rule for the real scalar action on complex matrices.
  Outside tsupport χ the product is identically zero on a neighborhood. These
  open neighborhoods cover the whole space since the closed support lies in U.
  No regularity of the total extension of A outside U is used. -/
  classical
  -- Use the local product on U and the identically zero germ off the cutoff support.
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hA.contDiffAt (hU.mem_nhds hx))
  · have hxχ : x ∉ tsupport χ := fun h ↦ hx (hχU h)
    have hzero : ContDiffAt ℝ ∞
        (fun _ : EuclideanSpace ℝ (Fin n) ↦
          (0 : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) x :=
      contDiffAt_const
    apply hzero.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
    simp [cutoffMatrix, hy]

/-- Compact support of the scalar cutoff controls the matrix support without regularity. -/
theorem hasCompactSupport_cutoffMatrix (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hcχ : HasCompactSupport χ) : HasCompactSupport (cutoffMatrix χ A) := by
  /- The matrix is zero wherever χ is zero, so its closed support is contained
  in tsupport χ. A closed subset of this compact support is compact. Neither
  smoothness nor invertibility of the matrix is needed for this raw support fact. -/
  -- Multiplication by the zero cutoff kills the matrix independently of its extension.
  exact hcχ.smul_right

/-- A compact smooth matrix function specifies a unique continuous Schwartz multiplier. -/
theorem existsUnique_matrixMultiplierCLM
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A) :
    ∃! T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      ∀ u x, T u x = A x (u x) := by
  /- Stage 1: all derivatives of A are bounded on its compact support and zero
  off it. Thus A has temperate growth. Apply the continuous bilinear evaluation
  of a complex-linear map to a vector in the Schwartz multiplier construction.
  Stage 2: the pointwise formula determines every output and gives uniqueness.
  This includes rectangular matrices and zero fiber ranks. -/
  -- Compact support supplies temperate growth of the actual matrix coefficient.
  let T := SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin q)))
    (hcA.hasTemperateGrowth hA)
  refine ⟨T, fun _ _ ↦ rfl, ?_⟩
  -- Equality at every point identifies both the Schwartz outputs and the continuous map.
  intro S hS
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  exact hS u x

/-- Actual matrix multiplication on Schwartz space, fixed by its pointwise specification. -/
def matrixMultiplierCLM
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) :=
  (existsUnique_matrixMultiplierCLM A hA hcA).exists.choose

/-- The named multiplier has the specified matrix action at every point. -/
theorem matrixMultiplierCLM_apply
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) : matrixMultiplierCLM A hA hcA u x = A x (u x) := by
  /- Use the specification of the chosen unique continuous map. The formula
  identifies the operator with multiplication of actual function values; it is
  independent of the proofs supplied for smoothness and compact support. -/
  exact (existsUnique_matrixMultiplierCLM A hA hcA).exists.choose_spec u x

/-- Matrix multiplication cannot enlarge the closed support of its input. -/
theorem tsupport_matrixMultiplierCLM_subset
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    tsupport (matrixMultiplierCLM A hA hcA u) ⊆ tsupport u := by
  /- Where u is zero, linearity of A makes the product zero. Take closures of
  this inclusion of nonzero loci, using the actual multiplier formula. Invertibility
  would give equality on its domain, but is not required for this inclusion. -/
  -- Compare the nonzero loci before passing to their closures.
  apply closure_mono
  intro x hx
  change matrixMultiplierCLM A hA hcA u x ≠ 0 at hx
  change u x ≠ 0
  intro hzero
  apply hx
  rw [matrixMultiplierCLM_apply, hzero, map_zero]

/-- The amplitude for output multiplication by A and input multiplication by B. -/
def matrixAmplitude
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : SymbolFunction n r q) : AmplitudeFunction n k l :=
  fun x y ξ ↦ (A x).comp ((p x ξ).comp (B y))

/-- The diagonal matrix product representing the transformed leading symbol. -/
def matrixSymbol
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : SymbolFunction n r q) : SymbolFunction n k l :=
  fun x ξ ↦ (A x).comp ((p x ξ).comp (B x))

/-- Smooth spatial matrix factors preserve the amplitude order. -/
theorem isAmplitude_matrixAmplitude (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    IsAmplitude m (matrixAmplitude A B p) := by
  /- Apply the mixed product rule, preserving the order A,p,B. On each compact
  pair set all spatial derivatives of A and B are bounded. Frequency derivatives
  hit only p, lowering its order by their number. Compact support is not needed
  until the amplitude is used to define its reduced quantized operator. -/
  let V := EuclideanSpace ℝ (Fin n)
  -- Smooth spatial coefficients are zero-order symbols on each compact spatial set.
  have coefficientSymbol {s t : ℕ}
      (C : V → EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))
      (hC : ContDiff ℝ ∞ C) : IsSymbol Set.univ 0 (fun x _ ↦ C x) := by
    refine ⟨(hC.comp contDiff_fst).contDiffOn, ?_⟩
    intro K _ hcompact i j
    cases j with
    | zero =>
      have hcont : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ i C x‖) K := by
        intro x hx
        exact ((hC.contDiffAt).continuousAt_iteratedFDeriv
          (by simp)).norm.continuousWithinAt
      obtain ⟨D, hD⟩ := (hcompact.image_of_continuousOn hcont).bddAbove
      refine ⟨max D 0, le_max_right _ _, ?_⟩
      intro x hx ξ
      have heq : (fun y ↦ iteratedFDeriv ℝ 0 (fun _ : V ↦ C y) ξ) =
          (continuousMultilinearCurryFin0 ℝ V
            (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))).symm ∘ C := rfl
      change ‖iteratedFDeriv ℝ i
        (fun y ↦ iteratedFDeriv ℝ 0 (fun _ : V ↦ C y) ξ) x‖ ≤ _
      rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      simp only [Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
      exact (hD ⟨x, hx, rfl⟩).trans (le_max_left D 0)
    | succ j =>
      refine ⟨0, le_rfl, ?_⟩
      intro x hx ξ
      have hz : (fun y : V ↦ iteratedFDeriv ℝ (j + 1) (fun _ : V ↦ C y) ξ) = 0 := by
        funext y
        exact congrFun (iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j) (C y)) ξ
      change ‖iteratedFDeriv ℝ i
        (fun y ↦ iteratedFDeriv ℝ (j + 1) (fun _ : V ↦ C y) ξ) x‖ ≤ _
      rw [hz, iteratedFDeriv_zero]
      simp
  -- The left factor has order m; the separated input matrix has order zero.
  have hAp := (coefficientSymbol A hA).symbolComp isOpen_univ hp
  have h := isAmplitude_leftRightAmplitude (0 + m) 0 (symbolComp (fun x _ ↦ A x) p)
    (fun y _ ↦ B y) hAp (coefficientSymbol B hB)
  change IsAmplitude (0 + m + 0)
    (fun x y ξ ↦ ((A x).comp (p x ξ)).comp (B y)) at h
  change IsAmplitude m (fun x y ξ ↦ (A x).comp ((p x ξ).comp (B y)))
  simpa only [zero_add, add_zero, ContinuousLinearMap.comp_assoc] using h

/-- Compact matrix supports provide both compact spatial supports of the amplitude. -/
theorem hasCompactSupport_matrixAmplitude
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : SymbolFunction n r q) (hcA : HasCompactSupport A) (hcB : HasCompactSupport B) :
    HasCompactSupport (Function.uncurry (matrixAmplitude A B p)) := by
  /- The amplitude is zero if x is outside the support of A or y outside that
  of B, uniformly over frequency. Take the product of the two compact closed
  supports; no support or symbol estimate on p is used. -/
  -- Each nonzero amplitude requires both of the original spatial matrix factors.
  apply (hcA.prod hcB).of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ ((isClosed_tsupport A).prod (isClosed_tsupport B))
  intro z hz
  constructor
  · by_contra hAz
    apply hz
    funext ξ
    simp [Function.uncurry, matrixAmplitude, image_eq_zero_of_notMem_tsupport hAz]
  · by_contra hBz
    apply hz
    funext ξ
    simp [Function.uncurry, matrixAmplitude, image_eq_zero_of_notMem_tsupport hBz]

/-- Exact amplitude reduction realizes matrix multiplication on both sides of quantization. -/
theorem quantize_matrixAmplitude (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin k)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (amplitudeSymbol (matrixAmplitude A B p)) u x =
      A x (quantize p (matrixMultiplierCLM B hB hcB u) x) := by
  /- Stage 1: apply the exact compact-amplitude reduction theorem. In its inner
  y integral substitute the pointwise multiplier formula, and factor A(x),p(x,ξ)
  outside the integrable Fourier integral. Stage 2: the remaining expression is
  the original quantization of Bu, followed by A(x). Use the existing SG Fourier
  normalization, including its single inverse factor (2π)^(-n). -/
  -- First reduce this exact compact matrix amplitude, retaining both original multipliers.
  have hreduce := quantize_amplitudeSymbol m (matrixAmplitude A B p)
    (isAmplitude_matrixAmplitude m p hp A B hA hB)
    (hasCompactSupport_matrixAmplitude A B p hcA hcB) u
  rw [congrFun hreduce x]
  let V := EuclideanSpace ℝ (Fin n)
  let w := matrixMultiplierCLM B hB hcB u
  have hw (y : V) : w y = B y (u y) := matrixMultiplierCLM_apply B hB hcB u y
  have hfourier (ξ : V) :
      fourierSG w ξ = ∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • w y := by
    unfold fourierSG
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with y
    congr 2
    rw [inner_smul_right]
    push_cast
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have hintegrable (ξ : V) : MeasureTheory.Integrable
      (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • w y) := by
    have hcont : Continuous
        (fun y ↦ Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • w y) := by
      fun_prop
    apply w.integrable.norm.mono' hcont.aestronglyMeasurable
    filter_upwards [] with y
    simp [norm_smul, Complex.norm_exp, Complex.mul_re]
  -- At fixed frequency the input matrix is absorbed in the same Schwartz function w.
  have hinner (ξ : V) :
      (∫ y, Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) •
        matrixAmplitude A B p x y ξ (u y)) =
      A x (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ (fourierSG w ξ)) := by
    let L := (A x).comp (p x ξ)
    have hL : A x (p x ξ (fourierSG w ξ)) =
        ∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • L (w y) := by
      rw [hfourier]
      change L (∫ y, Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) • w y) = _
      rw [← L.integral_comp_comm (hintegrable ξ)]
      simp only [map_smul]
    rw [map_smul, hL, ← MeasureTheory.integral_smul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with y
    have hphase : Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) =
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
          Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) := by
      rw [← Complex.exp_add, inner_sub_left]
      congr 1
      push_cast
      ring
    simp only [matrixAmplitude, ContinuousLinearMap.comp_apply, hphase, mul_smul, hw, L]
  -- The remaining frequency integral is integrable before passing through A(x).
  have hInt (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (x : EuclideanSpace ℝ (Fin n)) :
      MeasureTheory.Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        p x ξ (fourierSG u ξ)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let F := EuclideanSpace ℂ (Fin q)
    -- At each fixed spatial point, the symbol is a temperate frequency multiplier.
    have hg : (p x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry p) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := hp.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈m - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have h := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
        apply h.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase : (fun ξ : V ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    -- The Fourier convention differs by an invertible real dilation, preserving Schwartz space.
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).flip (hphase.smul hg) w).integrable
  change ((2 * Real.pi) ^ n)⁻¹ • (∫ ξ, _) = A x (quantize p w x)
  simp_rw [hinner]
  rw [(A x).integral_comp_comm (hInt p hp w x)]
  exact (A x).map_smul_of_tower ((2 * Real.pi) ^ n)⁻¹ _ |>.symm

/-- Locally smooth matrix factors preserve symbol order on an open overlap. -/
theorem isSymbol_matrixSymbol (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol U m p)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    IsSymbol U m (matrixSymbol A B p) := by
  /- Joint smoothness follows by continuous bilinear composition. On each compact
  subset of U, every derivative of both matrices is bounded. Apply Leibniz to
  the spatial derivatives; all frequency derivatives fall on p. Openness ensures
  that the total derivatives used in the symbol estimates are the local ones. -/
  let V := EuclideanSpace ℝ (Fin n)
  -- A smooth spatial coefficient has order zero, including all mixed derivatives.
  have coefficientSymbol {s t : ℕ}
      (C : V → EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))
      (hC : ContDiffOn ℝ ∞ C U) : IsSymbol U 0 (fun x _ ↦ C x) := by
    refine ⟨hC.comp contDiffOn_fst (fun _ hx ↦ hx.1), ?_⟩
    intro K hK hcompact i j
    cases j with
    | zero =>
      have hcont : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ i C x‖) K := by
        intro x hx
        exact ((hC.contDiffAt (hU.mem_nhds (hK hx))).continuousAt_iteratedFDeriv
          (by simp)).norm.continuousWithinAt
      obtain ⟨D, hD⟩ := (hcompact.image_of_continuousOn hcont).bddAbove
      refine ⟨max D 0, le_max_right _ _, ?_⟩
      intro x hx ξ
      have heq : (fun y ↦ iteratedFDeriv ℝ 0 (fun _ : V ↦ C y) ξ) =
          (continuousMultilinearCurryFin0 ℝ V
            (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))).symm ∘ C := rfl
      change ‖iteratedFDeriv ℝ i
        (fun y ↦ iteratedFDeriv ℝ 0 (fun _ : V ↦ C y) ξ) x‖ ≤ _
      rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      simp only [Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
      exact (hD ⟨x, hx, rfl⟩).trans (le_max_left D 0)
    | succ j =>
      refine ⟨0, le_rfl, ?_⟩
      intro x hx ξ
      have hz : (fun y : V ↦ iteratedFDeriv ℝ (j + 1) (fun _ : V ↦ C y) ξ) = 0 := by
        funext y
        exact congrFun (iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j) (C y)) ξ
      change ‖iteratedFDeriv ℝ i
        (fun y ↦ iteratedFDeriv ℝ (j + 1) (fun _ : V ↦ C y) ξ) x‖ ≤ _
      rw [hz, iteratedFDeriv_zero]
      simp
  -- Compose in the original order A, p, B; the two zero orders leave m unchanged.
  have hApB := (coefficientSymbol A hA).symbolComp hU
    (hp.symbolComp hU (coefficientSymbol B hB))
  change IsSymbol U (0 + (m + 0)) (fun x ξ ↦ (A x).comp ((p x ξ).comp (B x))) at hApB
  change IsSymbol U m (fun x ξ ↦ (A x).comp ((p x ξ).comp (B x)))
  simpa only [zero_add, add_zero] using hApB

/-- The reduced amplitude and its diagonal matrix symbol agree to one lower order. -/
theorem isSymbol_amplitudeSymbol_matrixAmplitude_sub (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hA : ContDiff ℝ ∞ A) (hcA : HasCompactSupport A)
    (hB : ContDiff ℝ ∞ B) (hcB : HasCompactSupport B) :
    IsSymbol Set.univ (m - 1)
      (amplitudeSymbol (matrixAmplitude A B p) - matrixSymbol A B p) := by
  /- Verify the compact-amplitude hypotheses and take N=1 in its full expansion.
  The zeroth coefficient is the amplitude on y=x, exactly A(x)p(x,ξ)B(x).
  Positive-degree terms contain frequency derivatives of p and spatial derivatives
  of B. They are lower order, not identically zero for variable input frames. -/
  have h := hasSymbolExpansion_amplitudeSymbol m (matrixAmplitude A B p)
    (isAmplitude_matrixAmplitude m p hp A B hA hB)
    (hasCompactSupport_matrixAmplitude A B p hcA hcB) 1
  simp only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero] at h
  exact h

section

variable (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
  (A : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℂ (Fin q) ≃L[ℂ] EuclideanSpace ℂ (Fin q))
  (B : EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℂ (Fin r) ≃L[ℂ] EuclideanSpace ℂ (Fin r))

/-- Change from old to new output and input frames at the symbol level. -/
def frameSymbol (p : SymbolFunction n r q) : SymbolFunction n r q :=
  matrixSymbol (fun x ↦ (A x).toContinuousLinearMap) (fun x ↦ (B x).symm.toContinuousLinearMap) p

variable (hA : ContDiffOn ℝ ∞ (fun x ↦ (A x).toContinuousLinearMap) U)
  (hB : ContDiffOn ℝ ∞ (fun x ↦ (B x).symm.toContinuousLinearMap) U)

include hU hA hB in
/-- The frame transformation preserves all real symbol orders, locally on the overlap. -/
theorem isSymbol_frameSymbol (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol U m p) :
    IsSymbol U m (frameSymbol A B p) := by
  /- Apply the matrix-symbol estimate to the forward output and inverse input
  transitions. Their derivatives are bounded on each compact subset of U. No
  uniform bounds on the entire open overlap or unitary frame assumption are required. -/
  exact isSymbol_matrixSymbol U hU m p hp _ _ hA hB

/-- Successive frame changes have the expected transition cocycle on symbols. -/
theorem frameSymbol_trans
    (A' : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) ≃L[ℂ] EuclideanSpace ℂ (Fin q))
    (B' : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) ≃L[ℂ] EuclideanSpace ℂ (Fin r))
    (p : SymbolFunction n r q) :
    frameSymbol A' B' (frameSymbol A B p) =
      frameSymbol (fun x ↦ (A x).trans (A' x)) (fun x ↦ (B x).trans (B' x)) p := by
  /- Evaluate at x,ξ. The left side is A' A p B⁻¹ B'⁻¹. Associativity of
  continuous linear-map composition and the reversed order of inverse products
  identify it with the composite transition formula. Smoothness is unnecessary. -/
  -- The inverse input transitions compose in reverse order, as in the actual frame change.
  funext x ξ
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- Reversing both transitions recovers the original symbol exactly. -/
theorem frameSymbol_symm (p : SymbolFunction n r q) :
    frameSymbol (fun x ↦ (A x).symm) (fun x ↦ (B x).symm) (frameSymbol A B p) = p := by
  /- At each x,ξ cancel the adjacent inverse output transitions and the adjacent
  inverse input transitions. This is an exact matrix identity, not a quotient
  equality, and it imposes no smoothness or symbol-order condition. -/
  -- Cancel in the two original fibers before identifying the whole symbol function.
  funext x ξ
  apply ContinuousLinearMap.ext
  intro v
  simp [frameSymbol, matrixSymbol]

variable (χ : EuclideanSpace ℝ (Fin n) → ℝ)
  (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)

/-- A concrete full left symbol for the cut-off frame conjugation. -/
def frameChangeSymbol (p : SymbolFunction n r q) : SymbolFunction n r q :=
  amplitudeSymbol (matrixAmplitude (cutoffMatrix χ (fun x ↦ (A x).toContinuousLinearMap))
    (cutoffMatrix χ (fun x ↦ (B x).symm.toContinuousLinearMap)) p)

/-- The actual Schwartz operator χ A P χ B⁻¹ using one admissible overlap cutoff. -/
def frameChangeOperator
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)) :=
  (matrixMultiplierCLM (cutoffMatrix χ (fun x ↦ (A x).toContinuousLinearMap))
    (contDiff_cutoffMatrix U hU _ hA χ hχ hχU)
    (hasCompactSupport_cutoffMatrix χ _ hcχ)).comp
      (P.comp (matrixMultiplierCLM (cutoffMatrix χ (fun x ↦ (B x).symm.toContinuousLinearMap))
        (contDiff_cutoffMatrix U hU _ hB χ hχ hχU)
        (hasCompactSupport_cutoffMatrix χ _ hcχ)))

include U hU hA hB hχ hcχ hχU in
/-- The full cut-off frame symbol has the original order on all of Euclidean space. -/
theorem isSymbol_frameChangeSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) : IsSymbol Set.univ m (frameChangeSymbol A B χ p) := by
  /- Both cut-off matrix functions are globally smooth and compactly supported.
  The matrix-amplitude lemmas supply its order and uniform compact spatial support.
  Apply SG 3.5 to the explicit amplitudeSymbol, without any global frame growth bound. -/
  exact isSymbol_amplitudeSymbol m _
    (isAmplitude_matrixAmplitude m p hp _ _
      (contDiff_cutoffMatrix U hU _ hA χ hχ hχU)
      (contDiff_cutoffMatrix U hU _ hB χ hχ hχU))
    (hasCompactSupport_matrixAmplitude _ _ p
      (hasCompactSupport_cutoffMatrix χ _ hcχ)
      (hasCompactSupport_cutoffMatrix χ _ hcχ))

include U hU hA hB hχ hcχ hχU in
/-- The same explicit symbol has the full compact-amplitude asymptotic expansion. -/
theorem hasSymbolExpansion_frameChangeSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) :
    HasSymbolExpansion Set.univ (fun j ↦ m - (j : ℝ)) (frameChangeSymbol A B χ p)
      (amplitudeExpansionTerm
        (matrixAmplitude (cutoffMatrix χ (fun x ↦ (A x).toContinuousLinearMap))
          (cutoffMatrix χ (fun x ↦ (B x).symm.toContinuousLinearMap)) p)) := by
  /- Apply the full expansion of the compact matrix amplitude. Its j-th term
  differentiates the input matrix χB⁻¹ in y and p in ξ before setting y=x,
  with the existing (-i)^j/j! convention. The statement controls each finite
  remainder, including N=0, and does not assert convergence of the formal series. -/
  exact hasSymbolExpansion_amplitudeSymbol m _
    (isAmplitude_matrixAmplitude m p hp _ _
      (contDiff_cutoffMatrix U hU _ hA χ hχ hχU)
      (contDiff_cutoffMatrix U hU _ hB χ hχ hχU))
    (hasCompactSupport_matrixAmplitude _ _ p
      (hasCompactSupport_cutoffMatrix χ _ hcχ)
      (hasCompactSupport_cutoffMatrix χ _ hcχ))

variable (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
  𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))

/-- The explicit symbol gives the exact cut-off frame action on every Schwartz input. -/
theorem quantize_frameChangeSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hP : ∀ u x, P u x = quantize p u x)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (frameChangeSymbol A B χ p) u x =
      frameChangeOperator U hU A B hA hB χ hχ hcχ hχU P u x := by
  /- Apply the exact matrix-amplitude formula to the two cut-off transitions.
  The input multiplier produces a legitimate Schwartz input, on which hP
  identifies P with quantize p. The output multiplier gives the remaining
  factor χA. The identity retains all lower-order and smoothing contributions. -/
  -- Both cut-off transitions use the same overlap and original cutoff.
  have h := quantize_matrixAmplitude m p hp
    (cutoffMatrix χ (fun x ↦ (A x).toContinuousLinearMap))
    (cutoffMatrix χ (fun x ↦ (B x).symm.toContinuousLinearMap))
    (contDiff_cutoffMatrix U hU _ hA χ hχ hχU)
    (hasCompactSupport_cutoffMatrix χ _ hcχ)
    (contDiff_cutoffMatrix U hU _ hB χ hχ hχU)
    (hasCompactSupport_cutoffMatrix χ _ hcχ) u x
  change quantize (amplitudeSymbol _) u x = _
  rw [h]
  -- The given quantization identity applies to the actual matrix-multiplied input.
  rw [← hP]
  exact (matrixMultiplierCLM_apply _ _ _ _ x).symm

/-- Frame conjugation preserves both support conditions in the same set. -/
theorem hasOperatorSupport_frameChangeOperator (K : Set (EuclideanSpace ℝ (Fin n)))
    (hPK : HasOperatorSupport K P) :
    HasOperatorSupport K (frameChangeOperator U hU A B hA hB χ hχ hcχ hχU P) := by
  /- Matrix multiplication cannot enlarge closed support. Thus the output
  support lies in the support of P applied to the input multiplier, hence in K.
  If the input support misses K, so does its multiplied input and P kills it.
  No closedness, compactness, or cutoff-equals-one condition on K is required. -/
  let Tin := matrixMultiplierCLM (cutoffMatrix χ (fun x ↦ (B x).symm.toContinuousLinearMap))
    (contDiff_cutoffMatrix U hU _ hB χ hχ hχU)
    (hasCompactSupport_cutoffMatrix χ _ hcχ)
  let Tout := matrixMultiplierCLM (cutoffMatrix χ (fun x ↦ (A x).toContinuousLinearMap))
    (contDiff_cutoffMatrix U hU _ hA χ hχ hχU)
    (hasCompactSupport_cutoffMatrix χ _ hcχ)
  -- Output multiplication preserves the output support already controlled by P.
  refine ⟨fun u ↦ ?_, ?_⟩
  · exact (tsupport_matrixMultiplierCLM_subset _ _ _ (P (Tin u))).trans (hPK.1 (Tin u))
  -- Input multiplication preserves disjointness from K, so the same P annihilates it.
  · intro u hu
    have hinput : Disjoint (tsupport (Tin u)) K :=
      hu.mono_left (tsupport_matrixMultiplierCLM_subset _ _ _ u)
    change Tout (P (Tin u)) = 0
    rw [hPK.2 _ hinput, map_zero]

/-- Cutoffs equal to one near operator support produce the same frame action. -/
theorem frameChangeOperator_eq (K : Set (EuclideanSpace ℝ (Fin n)))
    (hPK : HasOperatorSupport K P) (hone : K ⊆ interior {x | χ x = 1})
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρone : K ⊆ interior {x | ρ x = 1}) :
    frameChangeOperator U hU A B hA hB χ hχ hcχ hχU P =
      frameChangeOperator U hU A B hA hB ρ hρ hcρ hρU P := by
  /- Stage 1: the difference of the input multipliers vanishes on a neighborhood
  of K, so its closed support misses K and P kills it. Stage 2: P's output has
  support in K; either output cutoff is one there. Pointwise equality proves
  equality of the continuous operators, including their smoothing terms. -/
  let Tχ := matrixMultiplierCLM (cutoffMatrix χ (fun x ↦ (B x).symm.toContinuousLinearMap))
    (contDiff_cutoffMatrix U hU _ hB χ hχ hχU)
    (hasCompactSupport_cutoffMatrix χ _ hcχ)
  let Tρ := matrixMultiplierCLM (cutoffMatrix ρ (fun x ↦ (B x).symm.toContinuousLinearMap))
    (contDiff_cutoffMatrix U hU _ hB ρ hρ hρU)
    (hasCompactSupport_cutoffMatrix ρ _ hcρ)
  -- The input difference is zero on a neighborhood of every point of K.
  have hinput (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
      P (Tχ u) = P (Tρ u) := by
    have hdisjoint : Disjoint (tsupport (Tχ u - Tρ u)) K := by
      apply Set.disjoint_left.mpr
      intro x hx hxK
      have hnear : (fun y ↦ (Tχ u - Tρ u) y) =ᶠ[nhds x] 0 := by
        filter_upwards [isOpen_interior.mem_nhds (hone hxK),
          isOpen_interior.mem_nhds (hρone hxK)] with y hyχ hyρ
        have hyχ' : y ∈ {x | χ x = 1} := interior_subset hyχ
        have hyρ' : y ∈ {x | ρ x = 1} := interior_subset hyρ
        change χ y = 1 at hyχ'
        change ρ y = 1 at hyρ'
        simp [Tχ, Tρ, matrixMultiplierCLM_apply, cutoffMatrix, hyχ', hyρ']
      exact (notMem_tsupport_iff_eventuallyEq.mpr hnear) hx
    have hzero := hPK.2 (Tχ u - Tρ u) hdisjoint
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  -- The common output is supported in K, where each remaining cutoff equals one.
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  change matrixMultiplierCLM _ _ _ (P (Tχ u)) x =
    matrixMultiplierCLM _ _ _ (P (Tρ u)) x
  rw [matrixMultiplierCLM_apply, matrixMultiplierCLM_apply, hinput u]
  by_cases hx : x ∈ K
  · have hχx : x ∈ {x | χ x = 1} := interior_subset (hone hx)
    have hρx : x ∈ {x | ρ x = 1} := interior_subset (hρone hx)
    change χ x = 1 at hχx
    change ρ x = 1 at hρx
    simp [cutoffMatrix, hχx, hρx]
  · have hz : P (Tρ u) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hPK.1 (Tρ u) h))
    simp [hz]

include hU hA hB hχ hcχ hχU in
/-- The full frame symbol agrees with A p B⁻¹ to one lower order on the overlap. -/
theorem isSymbol_frameChangeSymbol_sub (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K)
    (hPK : HasOperatorSupport K P) (hone : K ⊆ interior {x | χ x = 1}) :
    IsSymbol U (m - 1) (frameChangeSymbol A B χ p - frameSymbol A B p) := by
  /- Stage 1: the N=1 amplitude expansion gives the diagonal term χ² A p B⁻¹.
  Stage 2: recover tsupport p ⊆ K from the exact quantization and output support.
  On K the cutoff is one; off K the entire p(x,·) is zero. Thus the diagonal
  term equals A p B⁻¹ everywhere, even for the arbitrary total frame extensions.
  Restrict the remainder estimate to U. Compactness of K is not needed here. -/
  have hrem := isSymbol_amplitudeSymbol_matrixAmplitude_sub m p hp
    (cutoffMatrix χ (fun x ↦ (A x).toContinuousLinearMap))
    (cutoffMatrix χ (fun x ↦ (B x).symm.toContinuousLinearMap))
    (contDiff_cutoffMatrix U hU _ hA χ hχ hχU)
    (hasCompactSupport_cutoffMatrix χ _ hcχ)
    (contDiff_cutoffMatrix U hU _ hB χ hχ hχU)
    (hasCompactSupport_cutoffMatrix χ _ hcχ)
  -- Output support recovers support of the same symbol used in the quantization identity.
  have hpK := tsupport_symbol_subset_of_hasOperatorSupport m p hp P hP K hK hPK
  have hdiag : matrixSymbol
      (cutoffMatrix χ (fun x ↦ (A x).toContinuousLinearMap))
      (cutoffMatrix χ (fun x ↦ (B x).symm.toContinuousLinearMap)) p =
        frameSymbol A B p := by
    funext x ξ
    by_cases hx : x ∈ K
    · have hxχ : x ∈ {x | χ x = 1} := interior_subset (hone hx)
      change χ x = 1 at hxχ
      simp [matrixSymbol, cutoffMatrix, frameSymbol, hxχ]
    · have hpx : p x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hpK h))
      simp [matrixSymbol, cutoffMatrix, frameSymbol, hpx]
  rw [hdiag] at hrem
  exact hrem.restrict (Set.subset_univ U)

/-- Equality in the actual principal-symbol quotient under a change of bundle frames. -/
theorem principalSymbolClass_frameChange (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hP : ∀ u x, P u x = quantize p u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K)
    (hPK : HasOperatorSupport K P) (hone : K ⊆ interior {x | χ x = 1}) :
    principalSymbolClass U hU m r q
        ⟨frameChangeSymbol A B χ p,
          (isSymbol_frameChangeSymbol U hU A B hA hB χ hχ hcχ hχU m p hp).restrict
            (Set.subset_univ U)⟩ =
      principalSymbolClass U hU m r q
        ⟨frameSymbol A B p,
          isSymbol_frameSymbol U hU A B hA hB m p (hp.restrict (Set.subset_univ U))⟩ := by
  /- The preceding difference estimate is exactly membership in S^(m-1).
  Apply the established quotient equality criterion. This compares actual
  principal classes; it does not identify full left symbols with their diagonal
  matrix products or require a homogeneous leading representative. -/
  apply (principalSymbolClass_eq_iff hU _ _).mpr
  exact isSymbol_frameChangeSymbol_sub U hU A B hA hB χ hχ hcχ hχU P
    m p hp hP K hK hPK hone

end

end AtiyahSinger
