/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianAdditiveResolvent
public import AtiyahSinger.Analysis.ConnectionLaplacianSobolevCommutant

/-!
# Continuous even-Sobolev realizations of the original additive resolvent

Public module ID: M0399.

The same additive resolvent has a norm-continuous realization on every even
nonnegative Sobolev level. The common norm bound is integrable against the
fractional weight, so uniformly bounded continuous remainder families can be
integrated after this actual resolvent.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

/-- The original additive resolvent acts continuously with its uniform even-Sobolev bound. -/
theorem exists_connectionLaplacianResolvent_sobolev_family
    (A : SmoothBundlePresentation (n := n) (r := r) E) (k : ℕ) :
    ∃ G : ℝ → (A.SobolevSpace (2 * (k : ℝ)) →L[ℂ] A.SobolevSpace (2 * (k : ℝ))),
      ContinuousOn G (Set.Ioi 0) ∧ ∃ C : ℝ, 0 ≤ C ∧
        (∀ t : ℝ, 0 < t → ‖G t‖ ≤ C / (1 + t)) ∧
        ∀ t : ℝ, 0 < t → ∃ U : smoothSections (n := n) (r := r) E →ₗ[ℂ]
            smoothSections (n := n) (r := r) E,
          (∀ u : smoothSections (n := n) (r := r) E,
            h.smoothToL2 μ (U u) =
              connectionLaplacianResolvent μ g h cov hcov hcomplex t (h.smoothToL2 μ u)) ∧
          ∀ u : smoothSections (n := n) (r := r) E,
            G t (A.smoothToSobolev (2 * (k : ℝ)) u) =
              A.smoothToSobolev (2 * (k : ℝ)) (U u) := by
  classical
  let H := h.L2SectionSpace μ
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  let S := Subalgebra.centralizer ℂ ({B} : Set (H →L[ℂ] H))
  let F := connectionLaplacianResolvent μ g h cov hcov hcomplex
  -- Commutation is algebraic even where the total ring inverse is zero.
  have hcommute (t : ℝ) : Commute (F t) B := by
    let D : H →L[ℂ] H := 1 + t • B
    have hDB : Commute D B := by
      change (1 + t • B) * B = B * (1 + t • B)
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    have hIB : Commute (Ring.inverse D) B := by
      by_cases hD : IsUnit D
      · obtain ⟨d, hd⟩ := hD
        rw [← hd, Ring.inverse_unit]
        exact (show Commute (d : H →L[ℂ] H) B from hd.symm ▸ hDB).units_inv_left
      · rw [Ring.inverse_non_unit D hD]
        exact Commute.zero_left B
    change (B * Ring.inverse D) * B = B * (B * Ring.inverse D)
    rw [mul_assoc, hIB.eq, ← mul_assoc]
  let T (t : ℝ) : S := ⟨F t, by
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    intro Q hQ
    obtain rfl := Set.mem_singleton_iff.mp hQ
    exact (hcommute t).eq.symm⟩
  -- Positivity makes 1+tB a unit on the entire positive parameter half-line.
  have hB : 0 ≤ B := (connectionLaplacianInverse_properties μ g h cov hcov hcomplex).1
  have hself : IsSelfAdjoint B := .of_nonneg hB
  have hunit (t : ℝ) (ht : 0 < t) : IsUnit (1 + t • B) := by
    have hden : cfc (fun x : ℝ ↦ 1 + t * x) B = 1 + t • B := by
      rw [cfc_const_add (1 : ℝ) (fun x : ℝ ↦ t * x) B
        (continuousOn_const.mul continuousOn_id) hself,
        cfc_const_mul_id t B hself, map_one]
    rw [← hden]
    apply (isUnit_cfc_iff (fun x : ℝ ↦ 1 + t * x) B
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) hself).mpr
    intro x hx
    exact (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg ht.le (spectrum_nonneg_of_nonneg hB hx))).ne'
  have hF : ContinuousOn F (Set.Ioi 0) := by
    intro t ht
    obtain ⟨d, hd⟩ := hunit t ht
    have hi : ContinuousAt Ring.inverse (1 + t • B) :=
      hd ▸ NormedRing.inverse_continuousAt d
    have hdct : ContinuousAt (fun s : ℝ ↦ (1 : H →L[ℂ] H) + s • B) t :=
      continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    have hict : ContinuousAt (fun s : ℝ ↦ Ring.inverse (1 + s • B)) t :=
      hi.comp (f := fun s : ℝ ↦ 1 + s • B) hdct
    exact (continuousAt_const.mul hict).continuousWithinAt
  have hT : ContinuousOn T (Set.Ioi 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuousOn_iff_continuous_domRestrict.mp hF).subtype_mk _
  obtain ⟨R, hR⟩ := exists_connectionLaplacian_commutant_sobolev_action
    μ g h cov hcov hcomplex A k
  let G := fun t : ℝ ↦ R (T t)
  refine ⟨G, R.continuous.comp_continuousOn hT, ‖R‖, norm_nonneg _, ?_, ?_⟩
  · intro t ht
    calc
      ‖G t‖ ≤ ‖R‖ * ‖T t‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (1 + t)⁻¹ := mul_le_mul_of_nonneg_left
        (connectionLaplacianResolvent_properties μ g h cov hcov hcomplex t ht).2.1
        (norm_nonneg _)
      _ = ‖R‖ / (1 + t) := (div_eq_mul_inv _ _).symm
  · intro t _
    exact hR (T t)

end AtiyahSinger
