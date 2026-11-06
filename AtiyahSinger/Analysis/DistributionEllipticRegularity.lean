/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DistributionSectionRegularity
public import AtiyahSinger.Analysis.PseudodifferentialDistributions
public import AtiyahSinger.Analysis.PseudodifferentialLocalRegularity

/-!
# Elliptic regularity for distribution sections

Public module ID: M0440.

A02/A04/A06: transfer the original local Sobolev mapping, pseudolocality and
left-parametrix regularity to the genuine continuous distribution carrier.
Full-symbol ellipticity gives exact singular-support preservation. The final
interfaces retain the original differential operator and its Sobolev extensions.
Sources: SG III.3.17(ii), III.4.6--4.7, III.5.2(i); Taylor III.1.4--1.5.
The base is compact; no noncompact LF or properly supported operator model is claimed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory SmoothBundlePresentation
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

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

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- A global order-m PDO maps local H^t distributions to local H^(t-m) distributions. -/
theorem memSobolevOn_distributionExtension (D : A.DistributionSection μ) (t : ℝ)
    (U : Set M) (hU : IsOpen U) (hD : DistributionSection.MemSobolevOn A μ D t U) :
    DistributionSection.MemSobolevOn B μ (P.distributionExtension A B D) (t - m) U := by
  /- Keep one original negative-order representative throughout the mapping
  theorem and the passage back to the actual distribution extension. -/
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu] at hD ⊢
  have hin := (DistributionSection.memSobolevOn_sobolevToDistribution_iff
    A μ (-(k : ℝ)) u t U).mp hD
  rw [P.distributionExtension_sobolevToDistribution]
  apply (DistributionSection.memSobolevOn_sobolevToDistribution_iff
    B μ (-(k : ℝ) - m) _ (t - m) U).mpr
  exact P.memSobolevOn_sobolevExtension A B (-(k : ℝ)) t u U hU hin

/-- Global PDOs are pseudolocal on all distribution sections of the compact base. -/
theorem isSmoothOn_distributionExtension (D : A.DistributionSection μ)
    (U : Set M) (hU : IsOpen U) (hD : DistributionSection.IsSmoothOn A μ D U) :
    DistributionSection.IsSmoothOn B μ (P.distributionExtension A B D) U := by
  /- The input supplies all local orders for this same distribution. Raising
  the requested input order by m gives every desired output order. -/
  apply (DistributionSection.isSmoothOn_iff_forall_memSobolevOn B μ _ U hU).mpr
  intro t
  have hin := (DistributionSection.isSmoothOn_iff_forall_memSobolevOn
    A μ D U hU).mp hD (t + m)
  have hout := P.memSobolevOn_distributionExtension A B D (t + m) U hU hin
  simpa only [add_sub_cancel_right] using hout

/-- The distribution extension creates no new singularities. -/
theorem singularSupport_distributionExtension_subset (D : A.DistributionSection μ) :
    DistributionSection.singularSupport B μ (P.distributionExtension A B D) ⊆
      DistributionSection.singularSupport A μ D := by
  /- Preserve each original smooth neighborhood and then negate its existence.
  This proves the inclusion without a symbol inverse or a new representative. -/
  intro x hx
  change ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ DistributionSection.IsSmoothOn A μ D U
  rintro ⟨U, hU, hxU, hD⟩
  exact hx ⟨U, hU, hxU, P.isSmoothOn_distributionExtension A B D U hU hD⟩

/-- An actual smooth-kernel operator sends every distribution to a globally smooth section. -/
theorem isSmoothOn_distributionExtension_of_isSmoothingOperator
    (hP : IsSmoothingOperator μ P.toLinearMap) (D : A.DistributionSection μ) :
    DistributionSection.IsSmoothOn B μ (P.distributionExtension A B D) Set.univ := by
  /- Represent D in one Sobolev order. The actual kernel supplied by hP has
  bounded extensions to every target order, agreeing with P's original extension
  on smooth inputs and hence by density. Its output has a smooth representative.
  Sobolev/distribution compatibility transfers this smoothness to the new action. -/
  obtain ⟨K, hK⟩ := hP
  obtain ⟨l, u, hu⟩ := A.exists_sobolev_representative μ D
  let s : ℝ := -(l : ℝ)
  -- Identify the original bounded action with the same kernel extension.
  have hT : P.sobolevExtension A B s = K.sobolevExtension μ A B s (s - m) := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer
      (P.sobolevExtension A B s).continuous
      (K.sobolevExtension μ A B s (s - m)).continuous
    funext v
    simp only [Function.comp_apply, P.sobolevExtension_smoothToSobolev,
      K.sobolevExtension_smoothToSobolev, hK]
  obtain ⟨v, hv, _⟩ := K.existsUnique_sobolevSmoothOutput μ A B s u
  -- The single smooth output represents the given distributional image.
  rw [← hu, P.distributionExtension_sobolevToDistribution]
  apply (DistributionSection.isSmoothOn_sobolevToDistribution_iff B μ (s - m) _
    Set.univ).mpr
  rw [hT, hv (s - m)]
  exact B.isSmoothOn_smoothToSobolev (s - m) v Set.univ isOpen_univ

/-- Only a left smooth-kernel error is needed to recover local regularity of a distribution. -/
theorem memSobolevOn_distribution_of_isSmoothingOperator
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (D : A.DistributionSection μ) (t : ℝ) (U : Set M) (hU : IsOpen U)
    (hPD : DistributionSection.MemSobolevOn B μ (P.distributionExtension A B D) t U) :
    DistributionSection.MemSobolevOn A μ D (t + m) U := by
  /- Transport through one actual Sobolev representative and its image under P.
  The left-residual theorem applies to those same vectors, and the representative
  criterion returns the local statement for the original distribution. -/
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu] at hPD ⊢
  rw [P.distributionExtension_sobolevToDistribution] at hPD
  have hPu := (DistributionSection.memSobolevOn_sobolevToDistribution_iff
    B μ (-(k : ℝ) - m) _ t U).mp hPD
  apply (DistributionSection.memSobolevOn_sobolevToDistribution_iff
    A μ (-(k : ℝ)) u (t + m) U).mpr
  exact P.memSobolevOn_of_isSmoothingOperator A B Q hQ (-(k : ℝ)) t u U hU hPu

/-- Full-symbol ellipticity gains m local derivatives for every distribution input. -/
theorem memSobolevOn_distribution_of_isElliptic (hP : P.IsElliptic)
    (D : A.DistributionSection μ) (t : ℝ) (U : Set M) (hU : IsOpen U)
    (hPD : DistributionSection.MemSobolevOn B μ (P.distributionExtension A B D) t U) :
    DistributionSection.MemSobolevOn A μ D (t + m) U := by
  /- Use the existing full-symbol elliptic parametrix and keep its left
  smooth-kernel error. The preceding distribution lifting theorem applies to D.
  Ellipticity is global; only the information about PD is localized to U.
  This compact bundle statement uses the order gain of Taylor III.1.5. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  exact P.memSobolevOn_distribution_of_isSmoothingOperator A B Q hQ.1 D t U hU hPD

/-- An elliptic PDO is locally hypoelliptic on the whole continuous distribution carrier. -/
theorem isSmoothOn_distribution_of_isElliptic (hP : P.IsElliptic)
    (D : A.DistributionSection μ) (U : Set M) (hU : IsOpen U)
    (hPD : DistributionSection.IsSmoothOn B μ (P.distributionExtension A B D) U) :
    DistributionSection.IsSmoothOn A μ D U := by
  /- For each desired input order l, smoothness of PD supplies order l-m.
  Apply local elliptic regularity to obtain (l-m)+m=l. The all-order criterion
  yields local smoothness. There is no boundary condition or spectral assumption. -/
  apply (DistributionSection.isSmoothOn_iff_forall_memSobolevOn A μ D U hU).mpr
  intro l
  have hout := (DistributionSection.isSmoothOn_iff_forall_memSobolevOn
    B μ (P.distributionExtension A B D) U hU).mp hPD (l - m)
  simpa only [sub_add_cancel] using
    P.memSobolevOn_distribution_of_isElliptic A B hP D (l - m) U hU hout

/-- A globally elliptic PDO preserves singular support exactly on all distributions. -/
theorem singularSupport_distributionExtension_eq_of_isElliptic (hP : P.IsElliptic)
    (D : A.DistributionSection μ) :
    DistributionSection.singularSupport B μ (P.distributionExtension A B D) =
      DistributionSection.singularSupport A μ D := by
  /- One inclusion is pseudolocality of P. For the other, take any smooth
  neighborhood for PD and use local elliptic regularity there. Thus D and PD
  have the same smooth neighborhoods. Global ellipticity permits equality on M;
  ellipticity only on U would instead give an equality restricted to U. -/
  apply Set.Subset.antisymm (P.singularSupport_distributionExtension_subset A B D)
  intro x hx
  change ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    DistributionSection.IsSmoothOn B μ (P.distributionExtension A B D) U
  rintro ⟨U, hU, hxU, hPD⟩
  exact hx ⟨U, hU, hxU, P.isSmoothOn_distribution_of_isElliptic A B hP D U hU hPD⟩

end PseudodifferentialOperator

namespace DifferentialOperator

omit hμ

variable {k : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F k)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The original differential operator acts on distributions through its exact PDO inclusion. -/
def distributionExtension : A.DistributionSection μ →ₗ[ℂ] B.DistributionSection μ :=
  (P.toPseudodifferentialOperator μ).distributionExtension A B

/-- The differential distribution action agrees with its original Sobolev extension. -/
theorem distributionExtension_sobolevToDistribution (s : ℝ) (u : A.SobolevSpace s) :
    P.distributionExtension μ A B (A.sobolevToDistribution μ s u) =
      B.sobolevToDistribution μ (s - k) (P.sobolevExtension A B s u) := by
  /- Apply the PDO compatibility theorem to the exact differential inclusion.
  Its Sobolev extension is the original differential extension by the existing
  comparison theorem. The natural order k is coerced to the same real order. -/
  change (P.toPseudodifferentialOperator μ).distributionExtension A B
    (A.sobolevToDistribution μ s u) = _
  rw [PseudodifferentialOperator.distributionExtension_sobolevToDistribution,
    P.sobolevExtension_toPseudodifferentialOperator μ A B s]

/-- Local elliptic regularity for the distribution extension of the original differential map. -/
theorem memSobolevOn_distribution_of_isElliptic (hP : P.IsElliptic)
    (D : A.DistributionSection μ) (t : ℝ) (U : Set M) (hU : IsOpen U)
    (hPD : DistributionSection.MemSobolevOn B μ (P.distributionExtension μ A B D) t U) :
    DistributionSection.MemSobolevOn A μ D (t + k) U := by
  /- Choose a negative-order representative of D and identify the output by
  the differential compatibility theorem. Apply the original differential local
  Sobolev theorem and return to distributions. This includes k=0, and requires
  neither self-adjointness nor the strong ellipticity condition of scalar PDE estimates. -/
  obtain ⟨j, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu] at hPD ⊢
  rw [P.distributionExtension_sobolevToDistribution] at hPD
  have hPu := (DistributionSection.memSobolevOn_sobolevToDistribution_iff
    B μ (-(j : ℝ) - k) _ t U).mp hPD
  apply (DistributionSection.memSobolevOn_sobolevToDistribution_iff
    A μ (-(j : ℝ)) u (t + k) U).mpr
  exact P.memSobolevOn_of_isElliptic (μ := μ) A B hP (-(j : ℝ)) t u U hU hPu

/-- SG III.5.2(i) transported from all Sobolev realizations to all closed-base distributions. -/
theorem isSmoothOn_distribution_of_isElliptic (hP : P.IsElliptic)
    (D : A.DistributionSection μ) (U : Set M) (hU : IsOpen U)
    (hPD : DistributionSection.IsSmoothOn B μ (P.distributionExtension μ A B D) U) :
    DistributionSection.IsSmoothOn A μ D U := by
  /- Use local smoothness of PD at each Sobolev order and the preceding
  differential lifting theorem to obtain every local order for D. The all-order
  criterion concludes. SG states the Sobolev-input version; the extension to this
  carrier uses the separately established compact-base representation theorem. -/
  apply (DistributionSection.isSmoothOn_iff_forall_memSobolevOn A μ D U hU).mpr
  intro l
  have hout := (DistributionSection.isSmoothOn_iff_forall_memSobolevOn
    B μ (P.distributionExtension μ A B D) U hU).mp hPD (l - k)
  simpa only [sub_add_cancel] using
    P.memSobolevOn_distribution_of_isElliptic μ A B hP D (l - k) U hU hout

end DifferentialOperator

end AtiyahSinger
