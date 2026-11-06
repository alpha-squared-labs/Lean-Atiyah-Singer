/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactTestFormalAdjoint
public import AtiyahSinger.Analysis.GlobalFormalAdjoint
public import AtiyahSinger.Analysis.HermitianMetricFormalAdjoint
public import AtiyahSinger.Analysis.HermitianMetricSymbol

import AtiyahSinger.Analysis.DifferentialParametrix
import AtiyahSinger.Analysis.SmoothAdjointCokernel

/-!
# Differential formal adjoints for explicit metrics

Public module ID: M0721.

D02/A07: the closed-manifold integral adjoint of a differential operator, keeping
its actual section map and principal symbol. Sources: SG III.5 (5.1)–(5.3),
pp.194–195. Metric-change and natural-quotient formulas are project deductions.
The convention D_j=-i∂_j gives no extra sign in the principal adjoint formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

namespace DifferentialOperator

variable {d : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F d)

/-- The integral identity determines a unique differential operator of the same order bound. -/
theorem existsUnique_metricFormalAdjoint :
    ∃! Q : DifferentialOperator (n := n) (r := q) (q := r) F E d,
      IsMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap := by
  -- On a compact base all original smooth sections are supported in univ.
  obtain ⟨Q, hQ, huniq⟩ := P.existsUnique_compactTestMetricFormalAdjoint (μ := μ) h k
  refine ⟨Q, ?_, ?_⟩
  · intro u v
    exact hQ Set.univ Set.univ isCompact_univ isCompact_univ
      ⟨u, fun x hx ↦ (hx (Set.mem_univ x)).elim⟩
      ⟨v, fun x hx ↦ (hx (Set.mem_univ x)).elim⟩
  · intro R hR
    apply huniq R
    intro K L _ _ u v
    exact hR u.val v.val

/-- The actual differential adjoint selected from the unique integral characterization. -/
def metricFormalAdjoint : DifferentialOperator (n := n) (r := q) (q := r) F E d :=
  Classical.choose (P.existsUnique_metricFormalAdjoint (μ := μ) h k).exists

/-- The chosen differential operator satisfies the explicit-metric integral identity. -/
theorem isMetricFormalAdjoint_metricFormalAdjoint :
    IsMetricFormalAdjoint h k μ P.toLinearMap
      (P.metricFormalAdjoint (μ := μ) h k).toLinearMap := by
  -- Read the pairing property of the chosen differential-operator witness.
  exact (P.existsUnique_metricFormalAdjoint (μ := μ) h k).exists.choose_spec

/-- The integral characterization identifies any candidate differential adjoint. -/
theorem metricFormalAdjoint_eq
    (Q : DifferentialOperator (n := n) (r := q) (q := r) F E d)
    (hQ : IsMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap) :
    P.metricFormalAdjoint (μ := μ) h k = Q := by
  -- Both candidates satisfy the same unique integral characterization.
  exact (P.existsUnique_metricFormalAdjoint (μ := μ) h k).unique
    (P.isMetricFormalAdjoint_metricFormalAdjoint h k) hQ

/-- Double differential adjunction recovers the original operator. -/
theorem metricFormalAdjoint_metricFormalAdjoint :
    (P.metricFormalAdjoint (μ := μ) h k).metricFormalAdjoint (μ := μ) k h = P := by
  -- Hermitian symmetry reverses the same-metric integral relation.
  exact (P.metricFormalAdjoint (μ := μ) h k).metricFormalAdjoint_eq k h P
    (P.isMetricFormalAdjoint_metricFormalAdjoint h k).symm

/-- Changing both metrics conjugates the differential adjoint section map exactly. -/
theorem metricFormalAdjoint_change (h' : SmoothHermitianMetric (n := n) (r := r) E)
    (k' : SmoothHermitianMetric (n := n) (r := q) F) :
    (P.metricFormalAdjoint (μ := μ) h' k').toLinearMap =
      (h'.changeSections h).toLinearMap.comp
        ((P.metricFormalAdjoint (μ := μ) h k).toLinearMap.comp
          (k.changeSections k').toLinearMap) := by
  -- The general change formula acts on precisely the old adjoint's section map.
  exact (P.isMetricFormalAdjoint_metricFormalAdjoint h' k').unique
    ((P.isMetricFormalAdjoint_metricFormalAdjoint h k).change h' k')

/-- The differential principal symbol is the explicit fiber adjoint. -/
theorem principalSymbol_metricFormalAdjoint_pairing
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
    (u : E x) (v : F x) :
    k.pairing x (P.principalSymbol x ξ u) v =
      h.pairing x u ((P.metricFormalAdjoint (μ := μ) h k).principalSymbol x ξ v) := by
  -- Restrict the original closed-base adjunction to compact tests, then detect its top order.
  apply IsCompactTestMetricFormalAdjoint.principalSymbol_pairing h k (μ := μ)
    (P := P) (Q := P.metricFormalAdjoint (μ := μ) h k) ?_ x ξ u v
  intro K L _ _ s t
  exact P.isMetricFormalAdjoint_metricFormalAdjoint h k s.val t.val

/-- Differential ellipticity is preserved in both directions. -/
theorem isElliptic_metricFormalAdjoint_iff :
    (P.metricFormalAdjoint (μ := μ) h k).IsElliptic ↔ P.IsElliptic := by
  -- On the original finite-dimensional fibers, the symbol pairing identifies the actual adjoint.
  have hbij (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      Function.Bijective ((P.metricFormalAdjoint (μ := μ) h k).principalSymbol x ξ) ↔
        Function.Bijective (P.principalSymbol x ξ) := by
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let A : E x →L[ℂ] F x := (P.principalSymbol x ξ).toContinuousLinearMap
    let B : F x →L[ℂ] E x :=
      ((P.metricFormalAdjoint (μ := μ) h k).principalSymbol x ξ).toContinuousLinearMap
    have hB : h.adjoint k x A = B := h.adjoint_eq k x A B
      (P.principalSymbol_metricFormalAdjoint_pairing h k x ξ)
    have hh := h.bijective_adjoint_iff k x A
    rw [hB] at hh
    exact hh
  -- Ellipticity imposes the same bijectivity test at every nonzero real covector.
  constructor
  · intro hP x ξ hξ
    exact (hbij x ξ).mp (hP x ξ hξ)
  · intro hP x ξ hξ
    exact (hbij x ξ).mpr (hP x ξ hξ)

/-- A smooth adjoint zero is exactly a vector orthogonal to every smooth output. -/
theorem metricFormalAdjoint_apply_eq_zero_iff (v : smoothSections (n := n) (r := q) F) :
    (P.metricFormalAdjoint (μ := μ) h k).toLinearMap v = 0 ↔
      ∀ u, k.sectionPairing μ (P.toLinearMap u) v = 0 := by
  constructor
  · intro hz u
    rw [P.isMetricFormalAdjoint_metricFormalAdjoint h k u v, hz]
    unfold SmoothHermitianMetric.sectionPairing
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact InnerProductSpace.Core.inner_zero_right _
  · -- Test orthogonality with the actual smooth adjoint image and use positivity.
    intro hz
    apply (h.sectionPairing_self_eq_zero_iff μ _).mp
    rw [← P.isMetricFormalAdjoint_metricFormalAdjoint h k]
    exact hz _

/-- For an elliptic differential operator the actual adjoint-kernel quotient map is bijective. -/
theorem bijective_ker_metricFormalAdjoint_to_coker (hP : P.IsElliptic) :
    Function.Bijective (P.toLinearMap.range.mkQ.comp
      (P.metricFormalAdjoint (μ := μ) h k).toLinearMap.ker.subtype) := by
  -- The original elliptic differential map has a two-sided smooth-kernel parametrix.
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  -- Recover smooth cokernel representatives using the specified metrics and density.
  exact (P.toPseudodifferentialOperator μ).bijective_adjointKer_to_coker_of_isParametrix
    h k A B Q hQ (P.metricFormalAdjoint (μ := μ) h k).toLinearMap
    (P.isMetricFormalAdjoint_metricFormalAdjoint h k)

/-- The natural smooth quotient equivalence for the specified metrics and density. -/
def kerMetricFormalAdjointEquivCoker (hP : P.IsElliptic) :
    (P.metricFormalAdjoint (μ := μ) h k).toLinearMap.ker ≃ₗ[ℂ]
      (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) :=
  LinearEquiv.ofBijective
    (P.toLinearMap.range.mkQ.comp
      (P.metricFormalAdjoint (μ := μ) h k).toLinearMap.ker.subtype)
    (P.bijective_ker_metricFormalAdjoint_to_coker h k hP)

/-- The natural equivalence uses the original smooth quotient class. -/
theorem kerMetricFormalAdjointEquivCoker_apply (hP : P.IsElliptic)
    (v : (P.metricFormalAdjoint (μ := μ) h k).toLinearMap.ker) :
    P.kerMetricFormalAdjointEquivCoker h k hP v = P.toLinearMap.range.mkQ v.val := by
  -- The chosen equivalence retains its forward map: inclusion followed by this quotient.
  rfl

/-- The analytic index has the two smooth kernel formula for any explicit metrics. -/
theorem analyticIndex_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint (hP : P.IsElliptic) :
    P.analyticIndex hP = (Module.finrank ℂ P.toLinearMap.ker : ℤ) -
      Module.finrank ℂ (P.metricFormalAdjoint (μ := μ) h k).toLinearMap.ker := by
  -- Substitute the dimension of the actual metric adjoint kernel via the quotient equivalence.
  rw [P.analyticIndex_eq_finrank_sub hP,
    ← (P.kerMetricFormalAdjointEquivCoker (μ := μ) h k hP).finrank_eq]

end DifferentialOperator

end AtiyahSinger
