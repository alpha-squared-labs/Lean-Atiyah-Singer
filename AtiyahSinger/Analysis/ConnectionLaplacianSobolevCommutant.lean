/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianResolventSobolev

/-!
# Continuous Sobolev action of the bounded spectral commutant

Public module ID: M0400.

The same bounded operators commuting with the original inverse act on every
nonnegative even Sobolev level. This action is a continuous linear map of the
bounded operator, so continuous resolvent families have continuous Sobolev
realizations as well. Density and the original smooth L2 graph fix all maps.
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

set_option maxHeartbeats 1000000 in
-- The extended limit accommodates the original bounded commutant on each even Sobolev completion.
/-- The original bounded commutant acts continuously on each even Sobolev completion. -/
theorem exists_connectionLaplacian_commutant_sobolev_action
    (A : SmoothBundlePresentation (n := n) (r := r) E) (k : ℕ) :
    let S := Subalgebra.centralizer ℂ
      {connectionLaplacianInverse μ g h cov hcov hcomplex}
    ∃ R : S →L[ℂ]
        (A.SobolevSpace (2 * (k : ℝ)) →L[ℂ] A.SobolevSpace (2 * (k : ℝ))),
      ∀ T : S, ∃ U : smoothSections (n := n) (r := r) E →ₗ[ℂ]
          smoothSections (n := n) (r := r) E,
        (∀ u : smoothSections (n := n) (r := r) E,
          h.smoothToL2 μ (U u) = (T : h.L2SectionSpace μ →L[ℂ] h.L2SectionSpace μ)
            (h.smoothToL2 μ u)) ∧
        ∀ u : smoothSections (n := n) (r := r) E,
          R T (A.smoothToSobolev (2 * (k : ℝ)) u) =
            A.smoothToSobolev (2 * (k : ℝ)) (U u) := by
  classical
  let H := h.L2SectionSpace μ
  let B := connectionLaplacianInverse μ g h cov hcov hcomplex
  let S := Subalgebra.centralizer ℂ ({B} : Set (H →L[ℂ] H))
  let s : ℝ := 2 * (k : ℝ)
  let f := h.smoothToL2 μ
  have hcommute (T : S) : Commute (T : H →L[ℂ] H) B := by
    change (T : H →L[ℂ] H) * B = B * (T : H →L[ℂ] H)
    exact (((Subalgebra.mem_centralizer_iff ℂ).mp T.property) B (Set.mem_singleton B)).symm
  obtain ⟨C, hC, hbound⟩ :=
    exists_connectionLaplacian_commutant_sobolev_bound μ g h cov hcov hcomplex A k
  choose U hU using fun T : S ↦ (hbound (T : H →L[ℂ] H) (hcommute T)).exists
  -- Extend each actual smooth action, keeping the same common operator-norm constant.
  let F (T : S) := (A.smoothToSobolev s).comp (U T)
  let R₀ (T : S) : A.SobolevSpace s →L[ℂ] A.SobolevSpace s :=
    (F T).extendOfNorm (A.smoothToSobolev s)
  have hR₀ (T : S) (u : smoothSections (n := n) (r := r) E) :
      R₀ T (A.smoothToSobolev s u) = A.smoothToSobolev s (U T u) :=
    LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev s)
      ⟨C * ‖(T : H →L[ℂ] H)‖, (hU T).2⟩ u
  have hnorm (T : S) : ‖R₀ T‖ ≤ C * ‖T‖ :=
    (F T).opNorm_extendOfNorm_le (A.denseRange_smoothToSobolev s)
      (mul_nonneg hC (norm_nonneg _)) (hU T).2
  -- Linearity follows on the original sections from the injective metric L2 embedding.
  have hadd (T V : S) (u : smoothSections (n := n) (r := r) E) :
      U (T + V) u = U T u + U V u := by
    apply h.smoothToL2_injective μ
    rw [(hU (T + V)).1 u, map_add, (hU T).1 u, (hU V).1 u]
    rfl
  have hsmul (c : ℂ) (T : S) (u : smoothSections (n := n) (r := r) E) :
      U (c • T) u = c • U T u := by
    apply h.smoothToL2_injective μ
    rw [(hU (c • T)).1 u, map_smul, (hU T).1 u]
    rfl
  let Rlin : S →ₗ[ℂ] (A.SobolevSpace s →L[ℂ] A.SobolevSpace s) := {
    toFun := R₀
    map_add' := by
      intro T V
      apply ContinuousLinearMap.ext
      intro z
      change R₀ (T + V) z = R₀ T z + R₀ V z
      refine (A.denseRange_smoothToSobolev s).induction_on z
        (isClosed_eq (R₀ (T + V)).continuous ((R₀ T).continuous.add (R₀ V).continuous)) ?_
      intro u
      rw [hR₀, hR₀, hR₀, hadd, map_add]
    map_smul' := by
      intro c T
      apply ContinuousLinearMap.ext
      intro z
      change R₀ (c • T) z = c • R₀ T z
      refine (A.denseRange_smoothToSobolev s).induction_on z
        (isClosed_eq (R₀ (c • T)).continuous ((R₀ T).continuous.const_smul c)) ?_
      intro u
      rw [hR₀, hR₀, hsmul, map_smul] }
  let R : S →L[ℂ] (A.SobolevSpace s →L[ℂ] A.SobolevSpace s) :=
    Rlin.mkContinuous C hnorm
  refine ⟨R, ?_⟩
  intro T
  exact ⟨U T, (hU T).1, hR₀ T⟩

end AtiyahSinger
