/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DistributionSections

/-!
# Finite-order distributions and their Sobolev representatives

Public module ID: M0444.

D04/A01/A06: every continuous distribution on the compact base has some finite
order, hence a representative in a sufficiently negative Sobolev completion.
A prescribed Sobolev order is characterized by its opposite-order test bound.
These are consequences of the actual smooth topology, Sobolev embedding and perfect
bilinear duality, not fields assumed in the definition of a distribution.

Taylor I.1 pp.10--12 supplies the test-space topology; SG III.2.15 supplies the
embedding and duality. The bundle reconstruction is an explicit project deduction.
No uniform negative order for all distributions or noncompact version is claimed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable (A : SmoothBundlePresentation (n := n) (r := r) E)

variable [MeasurableSpace M] (μ : Measure M)

/-- Each distribution has one finite derivative bound; its order may depend on the distribution. -/
theorem exists_bound_distributionSection (D : A.DistributionSection μ) :
    ∃ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ α : A.dualPresentation.SmoothSectionSpace,
      ‖D α‖ ≤ C * A.dualPresentation.smoothSectionSeminorm k α := by
  /- Apply the normed-target continuity criterion to D on the actual smooth
  dual-test space. Finitely many seminorm bounds reduce to one largest derivative
  order. This uses compact-base tests, not the noncompact LF topology. -/
  -- The functional already carries continuity for the actual dual-test topology.
  exact (A.dualPresentation.continuous_linearMap_iff_exists_bound D.toLinearMap).mp
    D.continuous

variable [BorelSpace M] [hC : CompactSpace M]
  [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hE hC hμ

set_option maxHeartbeats 800000 in
-- The reflexivity construction elaborates the original two nested dual completion spaces.
/-- A prescribed Sobolev representative exists exactly when its dual Sobolev test bound holds. -/
theorem existsUnique_sobolev_representative_iff (s : ℝ) (D : A.DistributionSection μ) :
    (∃! u : A.SobolevSpace s, A.sobolevToDistribution μ s u = D) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ α : A.dualPresentation.SmoothSectionSpace,
        ‖D α‖ ≤ C * ‖A.dualTestToSobolev (-s) α‖ := by
  /- Forward: boundedness of the flipped perfect pairing gives the test estimate.
  Reverse: the estimate extends D uniquely from dense smooth dual tests to a
  bounded functional on the opposite-order completion. The dual of the existing
  duality equivalence, together with reflexivity of the primal Hilbert space,
  represents that functional by u. The defining test identities give equality
  with D; injectivity of sobolevToDistribution proves uniqueness. -/
  classical
  let e := A.sobolevEvaluationDuality μ s
  constructor
  · rintro ⟨u, hu, _⟩
    let L := e.toContinuousLinearMap.flip u
    refine ⟨‖L‖ + 1, by positivity, ?_⟩
    intro α
    rw [← hu]
    change ‖L (A.dualTestToSobolev (-s) α)‖ ≤ _
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))
  · rintro ⟨C, hC, hbound⟩
    -- Extend the actual test functional to the opposite-order completion.
    have hdense : DenseRange (A.dualTestToSobolev (-s)) := by
      apply Dense.mono (s₁ := Set.range (A.dualSmoothToSobolev (-s))) ?_
        (A.denseRange_dualSmoothToSobolev (-s))
      rintro y ⟨α, rfl⟩
      refine ⟨A.dualPresentation.smoothSectionEquiv.symm (dualSectionsEquiv E α), ?_⟩
      simp only [A.dualTestToSobolev_apply,
          LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    let L : A.DualSobolevSpace (-s) →L[ℂ] ℂ :=
      D.toLinearMap.extendOfNorm (A.dualTestToSobolev (-s)).toLinearMap
    have hL (α : A.dualPresentation.SmoothSectionSpace) :
        L (A.dualTestToSobolev (-s) α) = D α :=
      LinearMap.extendOfNorm_eq hdense ⟨C, hbound⟩ α
    -- Hilbert reflexivity represents the dual of e by a primal vector.
    -- Two conjugations cancel; the final representation is the original bilinear pairing.
    let R := InnerProductSpace.toDual ℂ (A.SobolevSpace s)
    let g : A.SobolevSpace s →L[ℂ] ℂ :=
      { toFun v := star (L (e.symm (R v)))
        map_add' := by intros; simp
        map_smul' := by
          intro c v
          rw [map_smulₛₗ R, map_smul, map_smul]
          simp
        cont := continuous_star.comp (L.continuous.comp (e.symm.continuous.comp R.continuous)) }
    let u := R.symm g
    have hrepresent (α : A.DualSobolevSpace (-s)) : e α u = L α := by
      obtain ⟨v, hv⟩ := R.surjective (e α)
      have hu : inner ℂ u v = star (L α) := by
        calc
          inner ℂ u v = g v := InnerProductSpace.toDual_symm_apply
          _ = star (L (e.symm (R v))) := rfl
          _ = star (L α) := by rw [hv, e.symm_apply_apply]
      rw [← hv]
      change inner ℂ v u = L α
      exact (inner_conj_symm v u).symm.trans (by rw [hu]; simp)
    have hu : A.sobolevToDistribution μ s u = D := by
      apply ContinuousLinearMap.ext
      intro α
      change e (A.dualTestToSobolev (-s) α) u = D α
      rw [hrepresent, hL]
    refine ⟨u, hu, ?_⟩
    intro v hv
    exact A.sobolevToDistribution_injective μ s (hv.trans hu.symm)

/-- A derivative bound of order k yields H^(-t) whenever t is strictly greater than n/2+k. -/
theorem existsUnique_sobolev_representative_of_bound
    (D : A.DistributionSection μ) (k : ℕ) (C : ℝ) (hCpos : 0 < C)
    (hD : ∀ α : A.dualPresentation.SmoothSectionSpace,
      ‖D α‖ ≤ C * A.dualPresentation.smoothSectionSeminorm k α)
    (t : ℝ) (ht : (n : ℝ) / 2 + k < t) :
    ∃! u : A.SobolevSpace (-t), A.sobolevToDistribution μ (-t) u = D := by
  /- Apply the strict Sobolev-to-C^k estimate on the actual dual presentation.
  Its common-model Sobolev norm agrees with the independent dual norm through
  dualSobolevEquiv. The assumed derivative bound becomes an H^t test bound.
  Use the preceding characterization at order -t, transporting -(-t)=t.
  The strict inequality is essential to this embedding argument. -/
  obtain ⟨K, hK, hSobolev⟩ := A.dualPresentation.exists_sobolev_ck_bound k t ht
  apply (A.existsUnique_sobolev_representative_iff μ (-t) D).mpr
  refine ⟨C * (K + 1), mul_pos hCpos (by positivity), ?_⟩
  intro α
  have hnorm : ‖A.dualPresentation.smoothToSobolev t
      (A.dualPresentation.smoothSectionEquiv α)‖ = ‖A.dualTestToSobolev t α‖ := by
    exact ((A.dualSobolevEquiv t).symm.norm_map _).symm
  have hestimate := hSobolev (A.dualPresentation.smoothSectionEquiv α)
  change A.dualPresentation.smoothSectionSeminorm k α ≤
    K * ‖A.dualPresentation.smoothToSobolev t
      (A.dualPresentation.smoothSectionEquiv α)‖ at hestimate
  rw [hnorm] at hestimate
  rw [neg_neg]
  calc
    ‖D α‖ ≤ C * A.dualPresentation.smoothSectionSeminorm k α := hD α
    _ ≤ C * (K * ‖A.dualTestToSobolev t α‖) :=
      mul_le_mul_of_nonneg_left hestimate hCpos.le
    _ ≤ C * (K + 1) * ‖A.dualTestToSobolev t α‖ := by
      nlinarith [norm_nonneg (A.dualTestToSobolev t α)]

/-- Every distribution on the compact base belongs to some nonpositive integer Sobolev order. -/
theorem exists_sobolev_representative (D : A.DistributionSection μ) :
    ∃ k : ℕ, ∃ u : A.SobolevSpace (-(k : ℝ)),
      A.sobolevToDistribution μ (-(k : ℝ)) u = D := by
  /- First obtain a finite derivative order l and a bound for this D. Choose
  an integer k strictly larger than n/2+l and apply the previous theorem.
  The integer and norm bound may depend on D. This is a consequence of continuity,
  not a preselected Sobolev order imposed on the distribution carrier. -/
  obtain ⟨l, C, hC, hbound⟩ := A.exists_bound_distributionSection μ D
  obtain ⟨k, hk⟩ := exists_nat_gt ((n : ℝ) / 2 + l)
  obtain ⟨u, hu, _⟩ := A.existsUnique_sobolev_representative_of_bound μ D l C hC hbound k hk
  exact ⟨k, u, hu⟩

variable (B : SmoothBundlePresentation (n := n) (r := r) E)


set_option linter.unusedSectionVars false in
/-- There is a unique linear change of distribution presentation preserving actual tests. -/
theorem existsUnique_distributionEquiv :
    ∃! T : A.DistributionSection μ ≃ₗ[ℂ] B.DistributionSection μ,
      ∀ (D : A.DistributionSection μ) (α : B.dualPresentation.SmoothSectionSpace),
        T D α = D (A.dualPresentation.smoothSectionEquiv.symm
          (B.dualPresentation.smoothSectionEquiv α)) := by
  /- Both test spaces consist of the same actual smooth covectors. Their smooth
  topologies agree by presentation independence. Precompose each functional with
  the identity of tests; it remains continuous. Reverse this identity to obtain
  the inverse map. Evaluation on every test gives uniqueness of the linear equivalence. -/
  -- The actual identity of covectors is continuous in both presentation topologies.
  let toA : B.dualPresentation.SmoothSectionSpace →L[ℂ]
      A.dualPresentation.SmoothSectionSpace :=
    { toLinearMap := A.dualPresentation.smoothSectionEquiv.symm.toLinearMap.comp
        B.dualPresentation.smoothSectionEquiv.toLinearMap
      cont := by
        change @Continuous _ _ B.dualPresentation.smoothSectionTopology
          A.dualPresentation.smoothSectionTopology id
        rw [A.dualPresentation.smoothSectionTopology_eq B.dualPresentation]
        exact continuous_id }
  let toB : A.dualPresentation.SmoothSectionSpace →L[ℂ]
      B.dualPresentation.SmoothSectionSpace :=
    { toLinearMap := B.dualPresentation.smoothSectionEquiv.symm.toLinearMap.comp
        A.dualPresentation.smoothSectionEquiv.toLinearMap
      cont := by
        change @Continuous _ _ A.dualPresentation.smoothSectionTopology
          B.dualPresentation.smoothSectionTopology id
        rw [B.dualPresentation.smoothSectionTopology_eq A.dualPresentation]
        exact continuous_id }
  -- Precomposition gives inverse linear maps on the original continuous functionals.
  let T : A.DistributionSection μ ≃ₗ[ℂ] B.DistributionSection μ :=
    { toFun D := D.comp toA
      invFun D := D.comp toB
      left_inv := by
        intro D
        ext α
        rfl
      right_inv := by
        intro D
        ext α
        rfl
      map_add' := by
        intro D G
        ext α
        rfl
      map_smul' := by
        intro c D
        ext α
        rfl }
  refine ⟨T, ?_, ?_⟩
  · intro D α
    rfl
  · -- Any competing equivalence has the same value on every actual smooth covector.
    intro S hS
    apply LinearEquiv.ext
    intro D
    apply ContinuousLinearMap.ext
    intro α
    exact hS D α

/-- The actual identity of test covectors induces the canonical distribution identification. -/
def distributionEquiv : A.DistributionSection μ ≃ₗ[ℂ] B.DistributionSection μ :=
  Classical.choose (A.existsUnique_distributionEquiv μ B).exists

/-- The canonical distribution comparison evaluates on the same underlying covector. -/
theorem distributionEquiv_apply (D : A.DistributionSection μ)
    (α : B.dualPresentation.SmoothSectionSpace) :
    A.distributionEquiv μ B D α = D (A.dualPresentation.smoothSectionEquiv.symm
      (B.dualPresentation.smoothSectionEquiv α)) := by
  /- Use the defining specification of the chosen unique equivalence. The
  formula changes only the test-space presentation, keeping the density fixed. -/
  exact Classical.choose_spec (A.existsUnique_distributionEquiv μ B).exists D α

/-- The canonical Sobolev and distribution presentation comparisons agree. -/
theorem distributionEquiv_sobolevToDistribution (s : ℝ) (u : A.SobolevSpace s) :
    A.distributionEquiv μ B (A.sobolevToDistribution μ s u) =
      B.sobolevToDistribution μ s (A.sobolevEquiv B s u) := by
  /- Fix a smooth dual test. Both expressions are continuous functionals of u
  at order s. On the dense smooth image, the actual same-point integral and the
  smooth-input specification of sobolevEquiv identify them. Extend by density,
  then use extensionality over all tests. No arbitrary Hilbert isomorphism is used. -/
  apply ContinuousLinearMap.ext
  intro α
  rw [A.distributionEquiv_apply]
  let β := A.dualPresentation.smoothSectionEquiv.symm
    (B.dualPresentation.smoothSectionEquiv α)
  have hmap := (A.denseRange_smoothToSobolev s).equalizer
    (A.sobolevEvaluationDuality μ s (A.dualTestToSobolev (-s) β)).continuous
    ((B.sobolevEvaluationDuality μ s (B.dualTestToSobolev (-s) α)).continuous.comp
      (A.sobolevEquiv B s).continuous) (by
      funext v
      change A.sobolevToDistribution μ s (A.smoothToSobolev s v) β =
        B.sobolevToDistribution μ s (A.sobolevEquiv B s (A.smoothToSobolev s v)) α
      rw [A.sobolevEquiv_smoothToSobolev, A.sobolevToDistribution_smoothToSobolev,
        B.sobolevToDistribution_smoothToSobolev, A.smoothToDistribution_apply,
        B.smoothToDistribution_apply]
      simp only [β, LinearEquiv.apply_symm_apply])
  exact congrFun hmap u

end SmoothBundlePresentation

end AtiyahSinger
