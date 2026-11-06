/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSobolev
public import AtiyahSinger.Geometry.AtlasBundlePresentation

/-!
# Sobolev completions for locally finite-rank smooth bundle atlases

Public module ID: M0304.

D04: the original atlas sections are localized using a finite partition and
sent to their actual Bessel coordinates. Each coordinate has its own finite
fiber dimension. The closed range completion in this finite Hilbert sum is
therefore an actual Sobolev space for every real order, including negative
orders. No fiber metric, norm or global constant rank is assumed on E.

The Fourier integral below uses mathlib's exp(-2 pi i x.xi) convention.
The square sum of local norms is equivalent to SG's finite sum, not equal
to that sum. Sources: Spin Geometry III.2, Definition 2.3, (2.17) and Proposition 2.14.
Change of presentation and the integer covariant-derivative model are A01
comparison theorems; they are not fields of this completion definition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap FourierTransform

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  {A : SmoothComplexBundleAtlas (n := n) E}

namespace AtlasBundlePresentation

variable (L : AtlasBundlePresentation A)

/-- The finite Hilbert sum with the finite rank of each selected atlas chart. -/
abbrev SobolevCoordinates : Type :=
  PiLp 2 (fun j : Fin L.size ↦
    Lp (EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))

/-- The original section mapped to its cutoff Bessel coordinates at real order s. -/
def sobolevCoordinates (s : ℝ) : A.smoothSections →ₗ[ℂ] L.SobolevCoordinates :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    (LinearMap.pi fun j ↦
      (schwartzSobolevCoordinateLinearMap n (A.rank (L.frameIndex j)) s).comp
        (L.localizeLinearMap j))

/-- The completion in the specified norm, realized as a closed Hilbert subspace. -/
abbrev SobolevSpace (s : ℝ) : Type :=
  (L.sobolevCoordinates s).range.topologicalClosure

/-- The original smooth section included into its Sobolev completion. -/
def smoothToSobolev (s : ℝ) : A.smoothSections →ₗ[ℂ] L.SobolevSpace s :=
  (Submodule.inclusion (L.sobolevCoordinates s).range.le_topologicalClosure).comp
    (L.sobolevCoordinates s).rangeRestrict

include hM hT2 hSC

/-- The Sobolev norm separates the original smooth sections at every real order. -/
theorem smoothToSobolev_injective (s : ℝ) :
    Function.Injective (L.smoothToSobolev s) := by
  /- Stage 1: equality in the completion is equality of the actual Bessel
  coordinates. Apply the inverse Bessel realization at every local rank.
  Its Schwartz identity gives equality of the localized distributions,
  hence of the smooth localized functions themselves.
  Stage 2: on the cutoff support the selected original bundle chart is
  fiberwise invertible. Recover equality of the cutoff sections in E x.
  Sum these identities using the partition of unity at x to recover the
  original section value. This includes zero-rank charts and an empty base. -/
  classical
  intro u v huv
  -- Recover the original localized Schwartz functions from the actual Hilbert coordinates.
  have hlocal (j : Fin L.size) : L.localize j u = L.localize j v := by
    have hcoord := congrArg (fun w : L.SobolevSpace s ↦ w.val j) huv
    change schwartzSobolevCoordinate s (L.localize j u) =
      schwartzSobolevCoordinate s (L.localize j v) at hcoord
    have hdist := congrArg (besselRealization n (A.rank (L.frameIndex j)) s) hcoord
    rw [besselRealization_schwartzSobolevCoordinate,
      besselRealization_schwartzSobolevCoordinate] at hdist
    apply (SchwartzMap.injective_toLp 2 volume)
    apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
    change ((L.localize j u).toLp 2 volume :
        𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j))))) =
      ((L.localize j v).toLp 2 volume :
        𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))))
    simpa only [Lp.toTemperedDistribution_toLp_eq] using hdist
  apply Subtype.ext
  funext x
  -- Use the original, possibly varying-rank frame only on its prescribed base set.
  have hcut (j : Fin L.size) :
      (L.cutoff j x : ℂ) • u.val x = (L.cutoff j x : ℂ) • v.val x := by
    by_cases hx : x ∈ tsupport (L.cutoff j)
    · have hsource := (L.support_subset j hx).1
      have hframe := (L.support_subset j hx).2
      have hpointu :
          (⟨(L.chart j).symm (L.chart j x),
            u.val ((L.chart j).symm (L.chart j x))⟩ : TotalSpace Unit E) = ⟨x, u.val x⟩ :=
        congrArg (fun y ↦ (⟨y, u.val y⟩ : TotalSpace Unit E)) ((L.chart j).left_inv hsource)
      have hpointv :
          (⟨(L.chart j).symm (L.chart j x),
            v.val ((L.chart j).symm (L.chart j x))⟩ : TotalSpace Unit E) = ⟨x, v.val x⟩ :=
        congrArg (fun y ↦ (⟨y, v.val y⟩ : TotalSpace Unit E)) ((L.chart j).left_inv hsource)
      have hcoords := congrArg (fun f ↦ f (L.chart j x)) (hlocal j)
      change L.localizedFunction j u (L.chart j x) =
        L.localizedFunction j v (L.chart j x) at hcoords
      simp only [localizedFunction, ite_eq_left ((L.chart j).map_source hsource),
        atlasSectionInChart, hpointu, hpointv, (L.chart j).left_inv hsource] at hcoords
      -- The supplied linear frame is bijective on this original fiber.
      have hfiber :
          (A.chart (L.frameIndex j) ⟨x, (L.cutoff j x : ℂ) • u.val x⟩).2 =
            (A.chart (L.frameIndex j) ⟨x, (L.cutoff j x : ℂ) • v.val x⟩).2 := by
        rw [(A.linear (L.frameIndex j) x hframe).map_smul,
          (A.linear (L.frameIndex j) x hframe).map_smul]
        apply (EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ).symm.injective
        simpa only [map_smul] using hcoords
      have htotal := (A.chart (L.frameIndex j)).toPartialEquiv.injOn
        ((A.chart (L.frameIndex j)).mem_source.mpr hframe)
        ((A.chart (L.frameIndex j)).mem_source.mpr hframe)
        (Prod.ext (by simp [hframe]) hfiber)
      exact eq_of_heq (congr_arg_heq (fun z : TotalSpace Unit E ↦ z.2) htotal)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  -- The given finite partition reconstructs exactly the same original fiber values.
  have hsum : ∑ j, (L.cutoff j x : ℂ) = 1 := by exact_mod_cast L.sum_cutoff x
  calc
    u.val x = (∑ j, (L.cutoff j x : ℂ)) • u.val x := by rw [hsum, one_smul]
    _ = ∑ j, (L.cutoff j x : ℂ) • u.val x := Finset.sum_smul
    _ = ∑ j, (L.cutoff j x : ℂ) • v.val x := Finset.sum_congr rfl (fun j _ ↦ hcut j)
    _ = (∑ j, (L.cutoff j x : ℂ)) • v.val x := Finset.sum_smul.symm
    _ = v.val x := by rw [hsum, one_smul]

/-- Smooth sections have dense image in the concrete Hilbert completion. -/
theorem denseRange_smoothToSobolev (s : ℝ) : DenseRange (L.smoothToSobolev s) := by
  /- The ambient range of the linear Bessel-coordinate map is dense in
  its topological closure by definition. Its factorization into that
  closed subspace has the same image, with the inherited topology. -/
  have hdense : DenseRange
      (Set.inclusion (L.sobolevCoordinates s).range.le_topologicalClosure) :=
    (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  exact hdense.comp (L.sobolevCoordinates s).surjective_rangeRestrict.denseRange
    (continuous_inclusion _)

/-- The specified Hilbert norm is the square sum of actual local Bessel norms. -/
theorem norm_smoothToSobolev_sq (s : ℝ) (u : A.smoothSections) :
    ‖L.smoothToSobolev s u‖ ^ 2 =
      ∑ j, ‖schwartzSobolevCoordinate s (L.localize j u)‖ ^ 2 := by
  /- The completion inherits the norm of its ambient PiLp 2 space.
  The squared norm of a finite Hilbert sum is the sum of the squared
  coordinate norms, even when the coordinates have different dimensions.
  Each coordinate is exactly the displayed localized Bessel function. -/
  exact PiLp.norm_sq_eq_of_L2 _ (L.sobolevCoordinates s u)

/-- The Fourier-integral formula for the actual real-order Sobolev norm.
Mathlib uses exp(-2 pi i x.xi); SG uses the unitary exp(-i x.xi) normalization. -/
theorem norm_smoothToSobolev_sq_fourier (s : ℝ) (u : A.smoothSections) :
    ‖L.smoothToSobolev s u‖ ^ 2 =
      ∑ j, ∫ ξ : EuclideanSpace ℝ (Fin n),
        (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 (L.localize j u) ξ‖ ^ 2 := by
  /- Stage 1: use the preceding square-sum identity. For each chart,
  Plancherel converts the L² norm of the inverse Fourier transform of
  the weighted transform into the L² norm of that weighted transform.
  Stage 2: the real positive multiplier is (1+|xi|²)^(s/2). Squaring
  its norm gives (1+|xi|²)^s. Schwartz decay ensures integrability for
  every real s. Sum the equalities over the finite presentation.
  No (2 pi)^(-n) factor occurs for mathlib's normalized convention. -/
  rw [L.norm_smoothToSobolev_sq]
  apply Finset.sum_congr rfl
  intro j _
  let w : EuclideanSpace ℝ (Fin n) → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)
  have hw : w.HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)
  let v := SchwartzMap.fourierMultiplierCLM
    (EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))) w (L.localize j u)
  -- Plancherel applies to the original weighted Schwartz function, with no rescaling.
  change ‖v.toLp 2 volume‖ ^ 2 = _
  rw [← SchwartzMap.norm_fourier_toL2_eq v]
  have hnorm : ‖(𝓕 v).toLp 2 volume‖ ^ 2 = ∫ ξ, ‖𝓕 v ξ‖ ^ 2 := by
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact integral_nonneg (fun ξ ↦ sq_nonneg ‖𝓕 v ξ‖)
  rw [hnorm]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  change ‖𝓕 v ξ‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 (L.localize j u) ξ‖ ^ 2
  -- Fourier inversion leaves exactly the positive real multiplier on this frequency.
  have hfourier : 𝓕 v ξ = w ξ • 𝓕 (L.localize j u) ξ := by
    simp only [v, SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
      SchwartzMap.smulLeftCLM_apply_apply hw]
  rw [hfourier, norm_smul, mul_pow]
  have hweight : ‖w ξ‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    ring
  rw [hweight]

/-- The localized distribution represented by a vector at real Sobolev order. -/
def localDistribution (s : ℝ) (j : Fin L.size) (u : L.SobolevSpace s) :
    𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))) :=
  besselRealization n (A.rank (L.frameIndex j)) s (u.val j)

/-- Bessel realization recovers the original localized section on smooth inputs. -/
theorem localDistribution_smoothToSobolev (s : ℝ) (j : Fin L.size)
    (u : A.smoothSections) :
    L.localDistribution s j (L.smoothToSobolev s u) =
      (L.localize j u : 𝓢'(_, _)) := by
  /- The coordinate is J^s of the actual localized Schwartz function.
  Apply the existing Bessel realization identity at this chart's finite
  rank to cancel J^s with J^(-s), including at negative and zero orders. -/
  exact besselRealization_schwartzSobolevCoordinate s (L.localize j u)

/-- Completion preserves the fixed compact support of every localized distribution. -/
theorem isSupportedIn_localDistribution (s : ℝ) (j : Fin L.size)
    (u : L.SobolevSpace s) :
    IsSupportedIn (L.localDistribution s j u)
      ((L.chart j) '' tsupport (L.cutoff j)) := by
  /- Stage 1: approximate the completed vector by the dense image of
  actual smooth sections. Each localization has support in the same
  compact coordinate image of the specified cutoff support.
  Stage 2: coordinate projection, Bessel realization and evaluation
  against a fixed Schwartz function are continuous. If that function
  has compact support disjoint from the fixed support bound, every
  approximating distribution evaluates to zero. Pass to the limit. -/
  have hK : IsCompact ((L.chart j) '' tsupport (L.cutoff j)) :=
    (L.compact_support j).image_of_continuousOn
      ((L.chart j).continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
  -- Compact tests characterize this same closed support bound.
  apply (isSupportedIn_iff_compact_tests _ _ hK.isClosed).mpr
  intro φ _ hdisjoint
  -- The fixed-test evaluation is continuous in the original closed Hilbert subspace.
  let T : L.SobolevCoordinates →L[ℂ] EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j))) :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) _ φ).comp
      ((besselRealization n (A.rank (L.frameIndex j)) s).comp (PiLp.proj 2 _ j))
  have heval : Continuous (fun w : L.SobolevSpace s ↦ L.localDistribution s j w φ) :=
    T.continuous.comp continuous_subtype_val
  refine (L.denseRange_smoothToSobolev s).induction_on u
    (isClosed_eq heval continuous_const)
    ?_
  intro v
  rw [L.localDistribution_smoothToSobolev]
  -- Every smooth localization has precisely the same prescribed support bound.
  change (∫ x, φ x • L.localizedFunction j v x) = 0
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro x
  change φ x • L.localizedFunction j v x = 0
  by_cases hx : x ∈ tsupport φ
  · have hnot : x ∉ tsupport (L.localizedFunction j v) := fun hlocal ↦
      Set.disjoint_left.mp hdisjoint hx ((L.localizedFunction_properties j v).2.1 hlocal)
    rw [image_eq_zero_of_notMem_tsupport hnot, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end AtlasBundlePresentation

end AtiyahSinger
