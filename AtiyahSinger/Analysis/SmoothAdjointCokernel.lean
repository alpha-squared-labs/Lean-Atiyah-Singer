/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricFormalAdjoint
public import AtiyahSinger.Analysis.PseudodifferentialIndex
public import AtiyahSinger.Geometry.HermitianMetricDual

/-!
# Smooth adjoint representatives of an elliptic cokernel

Public module ID: M0960.

The smooth-kernel parametrix supplies a representative of every cokernel functional
by an actual smooth covector. The given Hermitian adjunction then identifies the
natural quotient map from its smooth kernel. This lower-level Fredholm alternative
is shared by differential adjoints with installed or explicitly supplied metrics;
it does not import their later Sobolev transpose or adjoint consumers.
Sources: SG III.5.2–5.3; the metric-independent functional reconstruction is a
project deduction from the established smooth-kernel and Sobolev duality theorems.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set SmoothBundlePresentation
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

omit hF

set_option maxHeartbeats 4000000 in
-- Compare the same dual bundle across all real Sobolev orders and smooth embeddings.
/-- A functional bounded in every real Sobolev order has a smooth covector representative. -/
private theorem exists_smoothDualSection_of_sobolev_functionals
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (L : ∀ s : ℝ, StrongDual ℂ (A.SobolevSpace s))
    (hL : ∀ (s : ℝ) (u : smoothSections (n := n) (r := r) E),
      L s (A.smoothToSobolev s u) = L 0 (A.smoothToSobolev 0 u)) :
    ∃ α : smoothDualSections (n := n) (r := r) E,
      ∀ u, smoothDualSectionPairing E μ α u = L 0 (A.smoothToSobolev 0 u) := by
  -- Opposite-order duality produces compatible Sobolev representatives of one functional.
  -- Opposite-order evaluation is compatible with the original dual inclusion.
  have pairing_inclusion (s t : ℝ) (hst : s ≤ t) (α : A.dualPresentation.SobolevSpace (-s))
      (u : smoothSections (n := n) (r := r) E) :
      A.sobolevEvaluationDuality μ t ((A.dualSobolevEquiv (-t)).symm
        (A.dualPresentation.sobolevInclusion (-s) (-t) (neg_le_neg hst) α))
          (A.smoothToSobolev t u) =
        A.sobolevEvaluationDuality μ s ((A.dualSobolevEquiv (-s)).symm α)
          (A.smoothToSobolev s u) := by
    refine (A.dualPresentation.denseRange_smoothToSobolev (-s)).induction_on α ?_ ?_
    · exact isClosed_eq
        (((A.sobolevEvaluationDuality μ t).continuous.comp
          ((A.dualSobolevEquiv (-t)).symm.continuous.comp
            (A.dualPresentation.sobolevInclusion (-s) (-t)
              (neg_le_neg hst)).continuous)).clm_apply
            continuous_const)
        (((A.sobolevEvaluationDuality μ s).continuous.comp
          (A.dualSobolevEquiv (-s)).symm.continuous).clm_apply continuous_const)
    · intro β
      obtain ⟨γ, rfl⟩ := (dualSectionsEquiv E).surjective β
      rw [A.dualPresentation.sobolevInclusion_smoothToSobolev,
        ← A.dualSobolevEquiv_smooth (-t), ← A.dualSobolevEquiv_smooth (-s)]
      simp only [LinearIsometryEquiv.symm_apply_apply]
      exact (A.sobolevEvaluationPairing_smooth μ t γ u).trans
        (A.sobolevEvaluationPairing_smooth μ s γ u).symm
  -- Recover a common smooth row before comparing its higher-order realizations.
  have smooth_row (L : ∀ s : ℝ, StrongDual ℂ (A.SobolevSpace s))
      (hL : ∀ (s : ℝ) (u : smoothSections (n := n) (r := r) E),
        L s (A.smoothToSobolev s u) = L 0 (A.smoothToSobolev 0 u)) :
      ∃ α : smoothDualSections (n := n) (r := r) E,
        ∀ s : ℝ, A.dualSmoothToSobolev (-s) α = (A.sobolevEvaluationDuality μ s).symm (L s) := by
    classical
    let row (s : ℝ) : A.dualPresentation.SobolevSpace (-s) :=
      A.dualSobolevEquiv (-s) ((A.sobolevEvaluationDuality μ s).symm (L s))
    have hrow (s : ℝ) (u : A.SobolevSpace s) :
        A.sobolevEvaluationDuality μ s ((A.dualSobolevEquiv (-s)).symm (row s)) u = L s u := by
      simp only [row, LinearIsometryEquiv.symm_apply_apply,
        ContinuousLinearEquiv.apply_symm_apply]
    -- Pairing against the same dense smooth inputs identifies the lowered high-order rows.
    have hcompatible (s t : ℝ) (hst : s ≤ t) :
        A.dualPresentation.sobolevInclusion (-s) (-t) (neg_le_neg hst) (row s) = row t := by
      apply (A.dualSobolevEquiv (-t)).symm.injective
      apply (A.sobolevEvaluationDuality μ t).injective
      apply ContinuousLinearMap.ext
      intro v
      refine (A.denseRange_smoothToSobolev t).induction_on v ?_ ?_
      · exact isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
      · intro u
        rw [pairing_inclusion s t hst (row s) u, hrow, hrow]
        exact (hL s u).trans (hL t u).symm
    -- All higher global lifts of one fixed vector give all local Sobolev orders.
    have hregular : A.dualPresentation.IsSmoothOn (-0) (row 0) Set.univ := by
      apply (A.dualPresentation.isSmoothOn_iff_forall_memSobolevOn
        (-0) (row 0) Set.univ isOpen_univ).mpr
      intro t
      let q : ℝ := max t 0
      have hq : -q ≤ 0 := by dsimp [q]; linarith [le_max_right t 0]
      have hmem : A.dualPresentation.MemSobolevOn (-0) (row 0) (-(-q)) Set.univ := by
        rw [← hcompatible (-q) 0 hq]
        intro j
        rw [A.dualPresentation.localDistribution_sobolevInclusion]
        exact A.dualPresentation.memSobolevOn_self (-(-q)) (row (-q)) Set.univ j
      exact A.dualPresentation.memSobolevOn_of_le (-0) (-(-q)) t (row 0) Set.univ
        hmem (by dsimp [q]; linarith [le_max_left t 0])
    obtain ⟨β, hβ, _⟩ :=
      (A.dualPresentation.isSmoothOn_univ_iff_exists_smooth_lift (-0) (row 0)).mp hregular
    let α : smoothDualSections (n := n) (r := r) E := (dualSectionsEquiv E).symm β
    have hαzero : A.dualSmoothToSobolev (-0) α =
        (A.sobolevEvaluationDuality μ 0).symm (L 0) := by
      apply (A.dualSobolevEquiv (-0)).injective
      rw [A.dualSobolevEquiv_smooth, LinearEquiv.apply_symm_apply]
      exact hβ
    -- The common smooth representative has the required embedding at every original order.
    refine ⟨α, ?_⟩
    intro s
    apply (A.sobolevEvaluationDuality μ s).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    apply ContinuousLinearMap.ext
    intro v
    refine (A.denseRange_smoothToSobolev s).induction_on v ?_ ?_
    · exact isClosed_eq (ContinuousLinearMap.continuous _) (L s).continuous
    · intro u
      change A.sobolevEvaluationPairing μ s (A.dualSmoothToSobolev (-s) α)
        (A.smoothToSobolev s u) = _
      rw [A.sobolevEvaluationPairing_smooth]
      have hzero := A.sobolevEvaluationPairing_smooth μ 0 α u
      unfold sobolevEvaluationPairing at hzero
      rw [hαzero, ContinuousLinearEquiv.apply_symm_apply] at hzero
      exact hzero.symm.trans (hL s u).symm
  obtain ⟨α, hα⟩ := smooth_row L hL
  refine ⟨α, ?_⟩
  intro u
  have hpair := A.sobolevEvaluationPairing_smooth μ 0 α u
  unfold sobolevEvaluationPairing at hpair
  rw [hα, ContinuousLinearEquiv.apply_symm_apply] at hpair
  exact hpair.symm

include hF

namespace PseudodifferentialOperator

/-- The given smooth adjoint kernel represents the original smooth cokernel naturally. -/
theorem bijective_adjointKer_to_coker_of_isParametrix
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap)
    (R : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E)
    (hR : IsMetricFormalAdjoint h k μ P.toLinearMap R) :
    Function.Bijective (P.toLinearMap.range.mkQ.comp R.ker.subtype) := by
  /- A cokernel functional extends to the finite-dimensional Hausdorff Sobolev quotient.
  The right smoothing residual makes it bounded at every order, hence smooth duality
  represents it by a smooth adjoint zero. Positivity both separates quotient classes
  and proves injectivity of the specified kernel inclusion followed by projection. -/
  classical
  let C := smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range
  let f : R.ker →ₗ[ℂ] C := P.toLinearMap.range.mkQ.comp R.ker.subtype
  have horth (w : R.ker) (u : smoothSections (n := n) (r := r) E) :
      k.sectionPairing μ (P.toLinearMap u) w.val = 0 := by
    rw [hR u w.val, show R w.val = 0 from w.property]
    unfold SmoothHermitianMetric.sectionPairing
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact InnerProductSpace.Core.inner_zero_right _
  -- A range vector in the smooth adjoint kernel has vanishing squared norm.
  have hfinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro w hw
    obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero P.toLinearMap.range).mp hw
    have hz := horth w u
    rw [hu] at hz
    exact Subtype.ext ((k.sectionPairing_self_eq_zero_iff μ w.val).mp hz)
  -- Every functional on the smooth quotient is represented by a smooth covector.
  have hrepresent (φ : Module.Dual ℂ C) :
      ∃ w : R.ker, ∀ v, k.sectionPairing μ w.val v = φ (P.toLinearMap.range.mkQ v) := by
    let H := B.SobolevSpace (0 - m)
    let S : Submodule ℂ H := (P.sobolevExtension A B 0).range
    let D := H ⧸ S
    have hFred := P.isFredholm_sobolevExtension_of_isParametrix Q A B hQ 0
    let : IsClosed (S : Set H) := hFred.isClosed_range
    let : FiniteDimensional ℂ D := hFred.finite_coker
    let e := P.sobolevCokerEquiv A B Q hQ 0
    let ψ : Module.Dual ℂ D := φ.comp e.symm.toLinearMap
    let proj : H →L[ℂ] D := ⟨S.mkQ, S.continuous_mkQ⟩
    let L₀ : StrongDual ℂ H := ψ.toContinuousLinearMap.comp proj
    have hL₀ (v : smoothSections (n := n) (r := q) F) :
        L₀ (B.smoothToSobolev (0 - m) v) = φ (P.toLinearMap.range.mkQ v) := by
      change φ (e.symm (S.mkQ (B.smoothToSobolev (0 - m) v))) = _
      rw [← P.sobolevCokerMap_mkQ A B 0]
      exact congrArg φ (e.symm_apply_apply _)
    obtain ⟨K, hK⟩ := hQ.2
    let L (s : ℝ) : StrongDual ℂ (B.SobolevSpace s) :=
      -(L₀.comp (K.sobolevExtension μ B B s (0 - m)))
    have hL (s : ℝ) (v : smoothSections (n := n) (r := q) F) :
        L s (B.smoothToSobolev s v) = φ (P.toLinearMap.range.mkQ v) := by
      change -L₀ (K.sobolevExtension μ B B s (0 - m) (B.smoothToSobolev s v)) = _
      rw [K.sobolevExtension_smoothToSobolev, hL₀, hK]
      change -φ (P.toLinearMap.range.mkQ (P.toLinearMap (Q.toLinearMap v) - v)) = _
      have hzero : P.toLinearMap.range.mkQ (P.toLinearMap (Q.toLinearMap v)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨Q.toLinearMap v, rfl⟩
      rw [map_sub, hzero, zero_sub, map_neg, neg_neg]
    obtain ⟨α, hα⟩ := exists_smoothDualSection_of_sobolev_functionals (μ := μ) B L
      (fun s v ↦ (hL s v).trans (hL 0 v).symm)
    let w := k.dualSectionsEquiv.symm α
    have hw (v : smoothSections (n := n) (r := q) F) :
        k.sectionPairing μ w v = φ (P.toLinearMap.range.mkQ v) := by
      rw [← k.dualSectionPairing_dualSectionsEquiv μ w v,
        show k.dualSectionsEquiv w = α from k.dualSectionsEquiv.apply_symm_apply α,
        hα, hL]
    -- Annihilation of the original smooth range forces the actual adjoint equation.
    have hRw : R w = 0 := by
      apply (h.sectionPairing_self_eq_zero_iff μ (R w)).mp
      rw [← hR (R w) w, ← k.sectionPairing_conj_symm μ (P.toLinearMap (R w)) w, hw]
      have hzero : P.toLinearMap.range.mkQ (P.toLinearMap (R w)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨R w, rfl⟩
      rw [hzero, map_zero, map_zero]
    exact ⟨⟨w, hRw⟩, hw⟩
  -- Any functional annihilating the projected adjoint kernel is zero, so that image is all C.
  have hsurj : Function.Surjective f := by
    intro z
    have hz : z ∈ f.range := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff f.range z).mp
      intro φ hφ
      obtain ⟨w, hw⟩ := hrepresent φ
      have hvanish : φ (f w) = 0 :=
        (Submodule.mem_dualAnnihilator φ).mp hφ (f w) ⟨w, rfl⟩
      have hwzero : w.val = 0 := by
        apply (k.sectionPairing_self_eq_zero_iff μ w.val).mp
        exact (hw w.val).trans hvanish
      obtain ⟨v, rfl⟩ := P.toLinearMap.range.mkQ_surjective z
      rw [← hw, hwzero]
      unfold SmoothHermitianMetric.sectionPairing
      apply integral_eq_zero_of_ae
      filter_upwards [] with x
      let : InnerProductSpace.Core ℂ (F x) := k.toCore x
      exact InnerProductSpace.Core.inner_zero_left _
    exact hz
  exact ⟨hfinj, hsurj⟩

end PseudodifferentialOperator

end AtiyahSinger
