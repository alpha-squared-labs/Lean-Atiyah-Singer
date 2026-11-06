/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DistributionSobolev
public import AtiyahSinger.Analysis.SobolevLocalComparison

/-!
# Local regularity of distribution sections on a compact base

Public module ID: M0442.

D04/A01/A06: standard local Sobolev membership, smoothness and singular support on
actual continuous distributions. Their formulas use existing localized Sobolev
representatives. Faithfulness and order-decreasing comparison show independence
of the representative; existence of such a representative is established separately
in DistributionSobolev, not assumed in the distribution carrier.
Sources: SG III.2.2, III.2.11--2.15; Taylor I.5 and III.1.4--1.5.
The representative-independent local predicates retain the original section and density.
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

variable [BorelSpace M] [hC : CompactSpace M]
  [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hE hC hμ

namespace DistributionSection

/-- Standard local Sobolev membership, computed in any actual Sobolev realization. -/
def MemSobolevOn (D : A.DistributionSection μ) (t : ℝ) (U : Set M) : Prop :=
  ∃ s : ℝ, ∃ u : A.SobolevSpace s,
    A.sobolevToDistribution μ s u = D ∧ A.MemSobolevOn s u t U

/-- Local smoothness of the same distribution, using its actual localized Sobolev realization. -/
def IsSmoothOn (D : A.DistributionSection μ) (U : Set M) : Prop :=
  ∃ s : ℝ, ∃ u : A.SobolevSpace s,
    A.sobolevToDistribution μ s u = D ∧ A.IsSmoothOn s u U

/-- The usual singular support: points without a smooth open neighborhood. -/
def singularSupport (D : A.DistributionSection μ) : Set M :=
  {x | ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ IsSmoothOn A μ D U}

/-- Local Sobolev membership agrees with the original predicate at every representative order. -/
theorem memSobolevOn_sobolevToDistribution_iff (s : ℝ) (u : A.SobolevSpace s)
    (t : ℝ) (U : Set M) :
    MemSobolevOn A μ (A.sobolevToDistribution μ s u) t U ↔ A.MemSobolevOn s u t U := by
  /- Reverse: use s and u as the witnesses. Forward: lower the witness and u
  to the minimum of their ambient orders. The natural inclusions preserve their
  distributions, so injectivity at this common order identifies the two vectors.
  Inclusion invariance of local regularity gives the stated condition for u.
  Thus the existential formula describes a standard property of D, not a choice. -/
  constructor
  · rintro ⟨l, v, hv, hlocal⟩
    -- Faithfulness identifies the two specified inclusions in a common lower order.
    have heq : A.sobolevInclusion l (min l s) (min_le_left l s) v =
        A.sobolevInclusion s (min l s) (min_le_right l s) u := by
      apply A.sobolevToDistribution_injective μ (min l s)
      simpa only [A.sobolevToDistribution_sobolevInclusion] using hv
    have hlow := (A.memSobolevOn_sobolevInclusion_iff l (min l s) t
      (min_le_left l s) v U).mpr hlocal
    rw [heq] at hlow
    exact (A.memSobolevOn_sobolevInclusion_iff s (min l s) t
      (min_le_right l s) u U).mp hlow
  · intro hu
    exact ⟨s, u, rfl, hu⟩

/-- Local smoothness agrees with the original predicate in every Sobolev realization. -/
theorem isSmoothOn_sobolevToDistribution_iff (s : ℝ) (u : A.SobolevSpace s) (U : Set M) :
    IsSmoothOn A μ (A.sobolevToDistribution μ s u) U ↔ A.IsSmoothOn s u U := by
  /- Use s,u in one direction. In the other, compare the two witnesses in a
  common lower completion by the faithful distribution embedding. The original
  local smoothness predicate is unchanged by these natural inclusions. -/
  constructor
  · rintro ⟨l, v, hv, hlocal⟩
    have heq : A.sobolevInclusion l (min l s) (min_le_left l s) v =
        A.sobolevInclusion s (min l s) (min_le_right l s) u := by
      apply A.sobolevToDistribution_injective μ (min l s)
      simpa only [A.sobolevToDistribution_sobolevInclusion] using hv
    have hlow := (A.isSmoothOn_sobolevInclusion_iff l (min l s)
      (min_le_left l s) v U).mpr hlocal
    rw [heq] at hlow
    exact (A.isSmoothOn_sobolevInclusion_iff s (min l s)
      (min_le_right l s) u U).mp hlow
  · intro hu
    exact ⟨s, u, rfl, hu⟩

/-- Passing from a Sobolev vector to its distribution preserves its actual singular support. -/
theorem singularSupport_sobolevToDistribution (s : ℝ) (u : A.SobolevSpace s) :
    singularSupport A μ (A.sobolevToDistribution μ s u) = A.singularSupport s u := by
  /- The preceding equivalence holds on every open neighborhood of each base
  point. Substitute it in the negated neighborhood definitions and use set
  extensionality. The equality is in M, not in an ambient coordinate space. -/
  ext x
  change (¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      IsSmoothOn A μ (A.sobolevToDistribution μ s u) U) ↔
    ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ A.IsSmoothOn s u U
  simp only [isSmoothOn_sobolevToDistribution_iff]

/-- Local Sobolev regularity restricts to smaller subsets. -/
theorem memSobolevOn_mono (D : A.DistributionSection μ) (t : ℝ) (U V : Set M)
    (hD : MemSobolevOn A μ D t U) (hVU : V ⊆ U) : MemSobolevOn A μ D t V := by
  /- Retain the actual Sobolev witness of hD and restrict its local predicate
  by the original subset theorem. The same witness still represents D, so no
  extension across the boundary of V or change of ambient order is required. -/
  obtain ⟨s, u, hu, hlocal⟩ := hD
  exact ⟨s, u, hu, SmoothBundlePresentation.memSobolevOn_mono A s t u U V hlocal hVU⟩

/-- Lowering the desired local Sobolev order preserves membership of the distribution. -/
theorem memSobolevOn_of_le (D : A.DistributionSection μ) (t l : ℝ) (U : Set M)
    (hD : MemSobolevOn A μ D t U) (hlt : l ≤ t) : MemSobolevOn A μ D l U := by
  /- Keep one witness representing D and apply the original local order
  inclusion to it. Only the target regularity decreases; its global ambient
  realization and the represented continuous functional remain unchanged. -/
  obtain ⟨s, u, hu, hlocal⟩ := hD
  exact ⟨s, u, hu, SmoothBundlePresentation.memSobolevOn_of_le A s t l u U hlocal hlt⟩

/-- Smoothness on an open set is equivalent to membership in all local real Sobolev orders. -/
theorem isSmoothOn_iff_forall_memSobolevOn (D : A.DistributionSection μ)
    (U : Set M) (hU : IsOpen U) :
    IsSmoothOn A μ D U ↔ ∀ t : ℝ, MemSobolevOn A μ D t U := by
  /- Choose one negative-order representative of D. Both preceding comparison
  theorems apply at that same order, for every t. The all-order criterion for
  the original Sobolev section proves the equivalence. This avoids exchanging
  existential representatives and universal orders without a compatibility argument. -/
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu, isSmoothOn_sobolevToDistribution_iff]
  simp only [memSobolevOn_sobolevToDistribution_iff]
  exact A.isSmoothOn_iff_forall_memSobolevOn (-(k : ℝ)) u U hU

/-- On the compact whole base, local H^t is equivalent to a unique global H^t representative. -/
theorem memSobolevOn_univ_iff (D : A.DistributionSection μ) (t : ℝ) :
    MemSobolevOn A μ D t Set.univ ↔
      ∃! u : A.SobolevSpace t, A.sobolevToDistribution μ t u = D := by
  /- First place D in an ambient order at most t, lowering an existing
  representative if necessary. Use the original whole-base local-to-global
  recovery, including membership in the defining completion closure. Compatibility
  of inclusion gives the desired distribution. Faithfulness gives uniqueness.
  Conversely a global H^t representative is locally H^t on the whole base. -/
  constructor
  · rintro ⟨s, u, hu, hlocal⟩
    -- Lower the same representative before recovering the desired order.
    let l : ℝ := min s t
    let v : A.SobolevSpace l := A.sobolevInclusion s l (min_le_left s t) u
    have hv : A.sobolevToDistribution μ l v = D := by
      exact (A.sobolevToDistribution_sobolevInclusion μ s l (min_le_left s t) u).trans hu
    have hvlocal : A.MemSobolevOn l v t Set.univ :=
      (A.memSobolevOn_sobolevInclusion_iff s l t (min_le_left s t) u Set.univ).mpr hlocal
    obtain ⟨w, hw, _⟩ :=
      (A.memSobolevOn_univ_iff_exists_sobolev_lift l t (min_le_right s t) v).mp hvlocal
    have hwd : A.sobolevToDistribution μ t w = D := by
      rw [← A.sobolevToDistribution_sobolevInclusion μ t l (min_le_right s t) w, hw, hv]
    exact ⟨w, hwd, fun z hz ↦ A.sobolevToDistribution_injective μ t (hz.trans hwd.symm)⟩
  · rintro ⟨u, hu, _⟩
    exact ⟨t, u, hu, A.memSobolevOn_self t u Set.univ⟩

/-- Whole-base smoothness recovers a unique actual smooth section. -/
theorem isSmoothOn_univ_iff_exists_smooth (D : A.DistributionSection μ) :
    IsSmoothOn A μ D Set.univ ↔
      ∃! u : smoothSections (n := n) (r := r) E, A.smoothToDistribution μ u = D := by
  /- Choose a Sobolev representative and apply the original smooth global
  recovery theorem to it. The smooth Sobolev embedding and distribution embedding
  commute. Their injectivity makes the smooth representative unique. The converse
  follows by localizing the same actual smooth section in the chosen presentation. -/
  constructor
  · rintro ⟨s, u, hu, hlocal⟩
    obtain ⟨v, hv, _⟩ := (A.isSmoothOn_univ_iff_exists_smooth_lift s u).mp hlocal
    have hvd : A.smoothToDistribution μ v = D := by
      rw [← A.sobolevToDistribution_smoothToSobolev μ s v, hv, hu]
    refine ⟨v, hvd, ?_⟩
    intro z hz
    -- Faithfulness at the original ambient order identifies the actual smooth sections.
    apply A.smoothToSobolev_injective s
    apply A.sobolevToDistribution_injective μ s
    simpa only [A.sobolevToDistribution_smoothToSobolev] using hz.trans hvd.symm
  · rintro ⟨v, hv, _⟩
    refine ⟨0, A.smoothToSobolev 0 v, ?_, ?_⟩
    · exact (A.sobolevToDistribution_smoothToSobolev μ 0 v).trans hv
    · exact A.isSmoothOn_smoothToSobolev 0 v Set.univ isOpen_univ

/-- The singular support of a distribution section is closed. -/
theorem isClosed_singularSupport (D : A.DistributionSection μ) :
    IsClosed (singularSupport A μ D) := by
  /- The complement is the union of all open neighborhoods on which D is
  smooth, hence is open. Equivalently choose any Sobolev representative and use
  the singular-support comparison and the original closedness result. -/
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu, singularSupport_sobolevToDistribution]
  exact A.isClosed_singularSupport (-(k : ℝ)) u

/-- On an open set, smoothness is exactly disjointness from singular support. -/
theorem isSmoothOn_iff_disjoint_singularSupport (D : A.DistributionSection μ)
    (U : Set M) (hU : IsOpen U) :
    IsSmoothOn A μ D U ↔ Disjoint U (singularSupport A μ D) := by
  /- Choose one representative of D, transfer both the smoothness and
  singular-support expressions to it, and use the original open-set criterion.
  Its gluing argument supplies a local smooth representative, not a global extension. -/
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu, isSmoothOn_sobolevToDistribution_iff, singularSupport_sobolevToDistribution]
  exact A.isSmoothOn_iff_disjoint_singularSupport (-(k : ℝ)) u U hU

variable (B : SmoothBundlePresentation (n := n) (r := r) E)

/-- Canonical presentation comparison preserves local Sobolev regularity on open subsets. -/
theorem memSobolevOn_distributionEquiv_iff (D : A.DistributionSection μ)
    (t : ℝ) (U : Set M) (hU : IsOpen U) :
    MemSobolevOn B μ (A.distributionEquiv μ B D) t U ↔ MemSobolevOn A μ D t U := by
  /- Choose a Sobolev representative in A. The canonical distribution
  comparison sends it to the existing Sobolev comparison in B. Apply both
  representative criteria and the original local change-of-presentation theorem;
  the latter supplies the coordinate and frame bounds at the target order t. -/
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu, A.distributionEquiv_sobolevToDistribution,
    memSobolevOn_sobolevToDistribution_iff, memSobolevOn_sobolevToDistribution_iff]
  exact A.memSobolevOn_sobolevEquiv_iff B (-(k : ℝ)) t u U hU

/-- Local smoothness is independent of the finite presentation used for the same tests. -/
theorem isSmoothOn_distributionEquiv_iff (D : A.DistributionSection μ)
    (U : Set M) (hU : IsOpen U) :
    IsSmoothOn B μ (A.distributionEquiv μ B D) U ↔ IsSmoothOn A μ D U := by
  /- Choose one actual Sobolev representative and use presentation invariance
  of its local smoothness. The canonical comparison retains the underlying
  covector tests and the same positive density at that representative order. -/
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu, A.distributionEquiv_sobolevToDistribution,
    isSmoothOn_sobolevToDistribution_iff, isSmoothOn_sobolevToDistribution_iff]
  exact A.isSmoothOn_sobolevEquiv_iff B (-(k : ℝ)) u U hU

/-- Canonical presentation comparison preserves the singular support in the original base. -/
theorem singularSupport_distributionEquiv (D : A.DistributionSection μ) :
    singularSupport B μ (A.distributionEquiv μ B D) = singularSupport A μ D := by
  /- Apply presentation invariance of local smoothness to every open
  neighborhood. The neighborhood predicates, and therefore their negations,
  agree pointwise on M. No coordinate image outside a chart source is used. -/
  obtain ⟨k, u, hu⟩ := A.exists_sobolev_representative μ D
  rw [← hu, A.distributionEquiv_sobolevToDistribution,
    singularSupport_sobolevToDistribution, singularSupport_sobolevToDistribution]
  exact A.singularSupport_sobolevEquiv B (-(k : ℝ)) u

end DistributionSection

end SmoothBundlePresentation

end AtiyahSinger
