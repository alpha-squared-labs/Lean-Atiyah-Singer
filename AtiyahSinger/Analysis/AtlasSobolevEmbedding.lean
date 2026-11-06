/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasCkSections

/-!
# Sobolev embedding into actual finite-order sections

Public module ID: M0306.

A01: under the strict inequality s > n/2+k, Sobolev vectors have unique actual
C^k representatives in the original locally finite-rank bundle. The bounded map
is fixed on dense original smooth sections, and its distribution formula records
that it represents the same vector in each specified localization.

Sources: Spin Geometry III.2.5 and III.2.15(1). The use of local finite ranks and
the finite supremum norm is the chartwise version of the usual bundle argument.
No ellipticity, spin structure, Hermitian metric or uniform positive rank is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  {A : SmoothComplexBundleAtlas (n := n) E}

include hM hT2 hSC

namespace AtlasBundlePresentation

variable (L : AtlasBundlePresentation A)

/-- Sobolev embedding extends the original smooth inclusion uniquely when s > n/2+k. -/
theorem existsUnique_sobolevToCk (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    ∃! T : L.SobolevSpace s →L[ℂ] L.CkSectionSpace k,
      ∀ u : A.smoothSections,
        T (L.smoothToSobolev s u) = L.smoothToCk k u := by
  /- Stage 1: apply Euclidean Sobolev embedding to each actual Schwartz localization
  with its chart rank. The strict exponent controls the suprema of all real
  derivatives through k. Each local H^s norm is bounded by the finite Hilbert
  sum norm, so the actual smooth inclusion is bounded in the induced C^k norm.
  Stage 2: use injectivity and density of smoothToSobolev to extend this same
  inclusion into the complete space of actual C^k sections. Density proves
  uniqueness among bounded extensions with the displayed smooth-input formula. -/
  classical
  -- First obtain the Euclidean estimate separately in every specified local rank.
  choose C hC hlocal using fun j : Fin L.size ↦
    sobolev_embedding n (A.rank (L.frameIndex j)) k s hs
  have hschwartz (j : Fin L.size)
      (v : 𝓢(EuclideanSpace ℝ (Fin n),
        EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j))))) :
      ∀ i : ℕ, i ≤ k → ∀ x,
        ‖iteratedFDeriv ℝ i v x‖ ≤ C j * ‖schwartzSobolevCoordinate s v‖ := by
    obtain ⟨f, hf, htest, hbound⟩ := hlocal j (schwartzSobolevCoordinate s v)
    -- Equality of the actual distributions identifies the continuous representative.
    have hsame : (v : EuclideanSpace ℝ (Fin n) → _) = f := by
      apply MeasureTheory.Measure.eq_of_ae_eq (μ := volume) ?_ v.continuous hf.continuous
      apply ae_eq_of_integral_contDiff_smul_eq v.continuous.locallyIntegrable
        hf.continuous.locallyIntegrable
      intro g hg hcompact
      have hcompact' : HasCompactSupport (Complex.ofRealCLM ∘ g) :=
        hcompact.comp_left rfl
      have hsmooth : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) :=
        Complex.ofRealCLM.contDiff.comp hg
      let φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := hcompact'.toSchwartzMap hsmooth
      have hφ := htest φ
      rw [besselRealization_schwartzSobolevCoordinate] at hφ
      simpa [φ] using hφ
    simpa only [← hsame] using hbound
  -- A finite sum provides a common bound, also when the presentation is empty.
  let C₀ : ℝ := ∑ j, C j
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun j _ ↦ hC j)
  have hbound (u : A.smoothSections) :
      ‖L.smoothToCk k u‖ ≤ C₀ * ‖L.smoothToSobolev s u‖ := by
    change ‖L.ckDerivativeCoordinates k (L.smoothToCk k u)‖ ≤ _
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC₀ (norm_nonneg _))).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC₀ (norm_nonneg _))).mpr
    intro i
    apply (BoundedContinuousFunction.norm_le (mul_nonneg hC₀ (norm_nonneg _))).mpr
    intro x
    change ‖iteratedFDeriv ℝ i.val (L.localizedCkFunction k j (L.smoothToCk k u)) x‖ ≤ _
    have hsame : L.localizedCkFunction k j (L.smoothToCk k u) = L.localize j u := rfl
    rw [hsame]
    have hcomponent : ‖schwartzSobolevCoordinate s (L.localize j u)‖ ≤
        ‖L.smoothToSobolev s u‖ :=
      PiLp.norm_apply_le (L.sobolevCoordinates s u) j
    have hconstant : C j ≤ C₀ :=
      Finset.single_le_sum (fun a _ ↦ hC a) (Finset.mem_univ j)
    calc
      ‖iteratedFDeriv ℝ i.val (L.localize j u) x‖ ≤
          C j * ‖schwartzSobolevCoordinate s (L.localize j u)‖ :=
        hschwartz j (L.localize j u) i.val (by omega) x
      _ ≤ C j * ‖L.smoothToSobolev s u‖ :=
        mul_le_mul_of_nonneg_left hcomponent (hC j)
      _ ≤ C₀ * ‖L.smoothToSobolev s u‖ :=
        mul_le_mul_of_nonneg_right hconstant (norm_nonneg _)
  -- Extend this same original smooth inclusion into the complete actual section space.
  let T : L.SobolevSpace s →L[ℂ] L.CkSectionSpace k :=
    (L.smoothToCk k).extendOfNorm (L.smoothToSobolev s)
  have hT (u : A.smoothSections) :
      T (L.smoothToSobolev s u) = L.smoothToCk k u :=
    LinearMap.extendOfNorm_eq (L.denseRange_smoothToSobolev s) ⟨C₀, hbound⟩ u
  refine ⟨T, hT, ?_⟩
  -- Density fixes the bounded extension without changing any fiber value.
  intro S hS
  apply DFunLike.coe_injective
  apply (L.denseRange_smoothToSobolev s).equalizer S.continuous T.continuous
  funext u
  exact (hS u).trans (hT u).symm

/-- The canonical bounded map to actual C^k representatives. -/
def sobolevToCk (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    L.SobolevSpace s →L[ℂ] L.CkSectionSpace k :=
  Classical.choose (L.existsUnique_sobolevToCk k s hs).exists

/-- The Sobolev representative of a smooth section has the same original values. -/
theorem sobolevToCk_smoothToSobolev (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s)
    (u : A.smoothSections) :
    L.sobolevToCk k s hs (L.smoothToSobolev s u) = L.smoothToCk k u := by
  /- Apply the defining dense-subspace specification of the chosen map. -/
  exact (Classical.choose_spec (L.existsUnique_sobolevToCk k s hs).exists) u

/-- The C^k output represents the actual localized Sobolev distribution. -/
theorem localDistribution_sobolevToCk (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s)
    (j : Fin L.size) (u : L.SobolevSpace s)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    L.localDistribution s j u φ =
      ∫ x, φ x • L.localizedCkFunction k j (L.sobolevToCk k s hs u) x := by
  /- Stage 1: approximate u by original smooth sections in the concrete H^s space.
  The bounded extension gives convergence in C^k, hence uniform convergence of
  the localized functions, all supported in the same compact cutoff image.
  Stage 2: pass to the limit in the test integrals by dominated convergence.
  Bessel distribution realization is continuous and gives the same limit on
  the left. On each approximating smooth section the identity is already the
  actual localization formula, fixing the resulting representative uniquely. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))
  -- The original zeroth jet is a bounded continuous coordinate of the actual section.
  let J : L.CkSectionSpace k →L[ℂ] L.CkCoordinates k :=
    { toLinearMap := L.ckDerivativeCoordinatesLinearMap k
      cont := by
        have hJ : Isometry (L.ckDerivativeCoordinates k) := by
          intro v w
          rfl
        exact hJ.continuous }
  let P : L.CkSectionSpace k →L[ℂ]
      (BoundedContinuousFunction X (ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ X) V)) :=
    (ContinuousLinearMap.proj ⟨0, Nat.zero_lt_succ k⟩).comp
      ((ContinuousLinearMap.proj j).comp J)
  let evaluateZero : ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ X) V →L[ℝ] V :=
    (continuousMultilinearCurryFin0 ℝ X V).toContinuousLinearEquiv.toContinuousLinearMap
  let F : L.CkSectionSpace k →L[ℝ] (BoundedContinuousFunction X V) :=
    (evaluateZero.compLeftContinuousBounded X).comp (P.restrictScalars ℝ)
  have hF (v : L.CkSectionSpace k) (x : X) :
      F v x = L.localizedCkFunction k j v x := by
    change (continuousMultilinearCurryFin0 ℝ X V)
      (iteratedFDeriv ℝ 0 (L.localizedCkFunction k j v) x) = _
    simp only [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
  -- Schwartz L1 decay turns this uniform coordinate control into continuity of each test integral.
  have htest : Continuous (fun v : L.CkSectionSpace k ↦ ∫ x : X, φ x • F v x) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply continuousAt_of_dominated
      (bound := fun x : X ↦ ‖φ x‖ * (‖F‖ * (‖v‖ + 1)))
    · exact Filter.Eventually.of_forall fun w ↦
        (φ.continuous.smul (F w).continuous).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds v zero_lt_one] with w hw
      have hnorm : ‖w‖ ≤ ‖v‖ + 1 := by
        calc
          ‖w‖ = ‖(w - v) + v‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - v‖ + ‖v‖ := norm_add_le _ _
          _ ≤ ‖v‖ + 1 := by
            rw [← dist_eq_norm]
            linarith [Metric.mem_ball.mp hw]
      apply Filter.Eventually.of_forall
      intro x
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((F w).norm_coe_le_norm x).trans
        ((F.le_opNorm w).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))
    · exact φ.integrable.norm.mul_const _
    · apply Filter.Eventually.of_forall
      intro x
      exact (((BoundedContinuousFunction.evalCLM ℝ x).continuous.comp F.continuous).const_smul
        (φ x)).continuousAt
  have htest' : Continuous (fun v : L.CkSectionSpace k ↦
      ∫ x, φ x • L.localizedCkFunction k j v x) := by
    simpa only [hF] using htest
  -- The same original Bessel realization is continuous on the completed Hilbert coordinates.
  let T : L.SobolevCoordinates →L[ℂ] V :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) _ φ).comp
      ((besselRealization n (A.rank (L.frameIndex j)) s).comp (PiLp.proj 2 _ j))
  have hleft : Continuous (fun w : L.SobolevSpace s ↦ L.localDistribution s j w φ) :=
    T.continuous.comp continuous_subtype_val
  refine (L.denseRange_smoothToSobolev s).induction_on u
    (isClosed_eq hleft (htest'.comp (L.sobolevToCk k s hs).continuous)) ?_
  -- The dense smooth formula identifies the two continuous extensions.
  intro v
  rw [L.localDistribution_smoothToSobolev, L.sobolevToCk_smoothToSobolev]
  rfl

/-- Sobolev embedding into the actual finite-order section space is injective. -/
theorem sobolevToCk_injective (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    Function.Injective (L.sobolevToCk k s hs) := by
  /- Equal output sections give equal test integrals in every selected chart.
  The distribution formula gives equality of all source Bessel distributions.
  Injectivity of each Bessel realization recovers the complete coordinate tuple,
  and hence the original Sobolev vectors. -/
  intro u v huv
  apply Subtype.ext
  apply (WithLp.ext_iff 2).mpr
  funext j
  -- Equality of the actual output sections gives equality of the same localized distributions.
  apply besselRealization_injective n (A.rank (L.frameIndex j)) s
  apply DFunLike.ext
  intro φ
  change L.localDistribution s j u φ = L.localDistribution s j v φ
  rw [L.localDistribution_sobolevToCk k s hs,
    L.localDistribution_sobolevToCk k s hs, huv]

end AtlasBundlePresentation

end AtiyahSinger
