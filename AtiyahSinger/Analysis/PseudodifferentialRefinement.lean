/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import AtiyahSinger.Analysis.PseudodifferentialCutoff

/-!
# Finite refinement of an actual pseudodifferential piece

Public module ID: M0898.

Refine a compactly supported piece into any open cover of its original input
and output supports. The new pieces keep its chart, frames and actual Fourier
operator, absorb a finite partition and nested input cutoffs, and have the exact
original sum of leading symbols. The discarded off-diagonal terms form a genuine
smooth-kernel operator for the same density. This is the standard partition
argument used to transport an actual PDO through moving coordinate charts.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

variable {E F}

namespace PseudodifferentialPiece

variable [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- A finite open refinement preserves the actual piece modulo smoothing and its exact symbol. -/
theorem exists_refinement {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    {ι : Type*} (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff) ⊆
      ⋃ i, U i) :
    ∃ (N : ℕ) (a : Fin N → ι) (R : Fin N → PseudodifferentialPiece E F m),
      IsSmoothingOperator μ (L.toLinearMap - ∑ j, (R j).toLinearMap) ∧
      (∑ j, (R j).globalSymbol) = L.globalSymbol ∧
      ∀ j, (R j).chart.symm ''
        (tsupport (R j).output.cutoff ∪ tsupport (R j).input.cutoff) ⊆ U (a j) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let K := L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)
  let D := L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
  have hD : IsOpen D :=
    (L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet
  have htarget : tsupport L.output.cutoff ∪ tsupport L.input.cutoff ⊆ L.chart.target := by
    rintro z (hz | hz)
    · exact (L.output.support_subset hz).1
    · exact (L.input.support_subset hz).1
  have hK : IsCompact K :=
    (L.output.compact_support.union L.input.compact_support).image_of_continuousOn
      (L.chart.continuousOn_symm.mono htarget)
  have hKD : K ⊆ D := by
    rintro x ⟨z, hz | hz, rfl⟩
    · exact ⟨⟨L.chart.map_target (L.output.support_subset hz).1,
        L.output_support_in_input_frame hz⟩, (L.output.support_subset hz).2⟩
    · exact ⟨⟨L.chart.map_target (L.input.support_subset hz).1,
        (L.input.support_subset hz).2⟩, L.input_support_in_output_frame hz⟩
  -- Refine the compact original support by relatively compact members of the prescribed cover.
  choose a ha using fun x : K ↦ Set.mem_iUnion.mp (hcover x.property)
  have hshrink (x : K) : ∃ V : Set M, IsOpen V ∧ (x : M) ∈ V ∧
      closure V ⊆ U (a x) ∩ D ∧ IsCompact (closure V) := by
    obtain ⟨V, hV, hxV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := (x : M))) ((hU (a x)).inter hD)
      (Set.singleton_subset_iff.mpr ⟨ha x, hKD x.property⟩)
    exact ⟨V, hV, hxV (Set.mem_singleton _), hVU, hVc⟩
  choose V hV hxV hVU hVc using hshrink
  have hcov : K ⊆ ⋃ x : K, V x := fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV hcov
  let index : Fin s.card ≃ s := s.equivFin.symm
  let W (j : Fin s.card) := V (index j)
  have hWcov : K ⊆ ⋃ j, W j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [W] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hK.isClosed W
    (fun j ↦ hV (index j)) hWcov
  have hcρ (j : Fin s.card) : HasCompactSupport (ρ j) :=
    (hVc (index j)).of_isClosed_subset (isClosed_tsupport _)
      (fun x hx ↦ subset_closure (hρ j hx))
  have hsρ (j : Fin s.card) : tsupport (ρ j) ⊆ U (a (index j)) ∩ D :=
    fun x hx ↦ hVU (index j) (subset_closure (hρ j hx))
  have hcut (j : Fin s.card) : ∃ β : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ β ∧
      tsupport β ⊆ U (a (index j)) ∩ D ∧ ∀ x ∈ tsupport (ρ j), β x = 1 := by
    obtain ⟨O, hO, hρO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure
      (hcρ j) ((hU (a (index j))).inter hD) (hsρ j)
    obtain ⟨β, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := I) (n := ⊤) (isClosed_tsupport (ρ j))
      (hρO.trans hO.subset_interior_closure)
    have hb : tsupport β ⊆ closure O := by
      apply closure_minimal ?_ hOc.isClosed
      intro x hx
      by_contra hn
      exact hx (hzero x hn)
    refine ⟨β, β.contMDiff, hb.trans hOU, ?_⟩
    intro x hx
    exact (interior_subset (s := {x | β x = 1}))
      (subset_interior_iff_mem_nhdsSet.mpr hone hx)
  choose β hβ hsβ hβone using hcut
  let R (j : Fin s.card) := L.cutoff (ρ j) (β j) (ρ j).contMDiff (hβ j)
  have hprod (j : Fin s.card) (x : M) : ρ j x * β j x = ρ j x := by
    by_cases hx : ρ j x = 0
    · simp [hx]
    · rw [hβone j x (subset_tsupport _ hx), mul_one]
  -- Local continuity of the inverse chart transports each new cutoff support correctly.
  have hsupport (C : BundleChartCutoff (r := r) E L.chart) (ψ : M → ℝ)
      (hψ : ContMDiff I 𝓘(ℝ) ∞ ψ) :
      L.chart.symm '' tsupport (C.mulSmooth L.chart_mem_atlas ψ hψ).cutoff ⊆ tsupport ψ := by
    rintro x ⟨z, hz, rfl⟩
    by_contra hn
    have hzC : z ∈ tsupport C.cutoff := tsupport_mul_subset_left hz
    have ht := (C.support_subset hzC).1
    have heq := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
      (L.chart.continuousAt_symm ht)
    have heq' : (C.mulSmooth L.chart_mem_atlas ψ hψ).cutoff =ᶠ[𝓝 z] 0 := by
      filter_upwards [heq] with y hy
      change C.cutoff y * ψ (L.chart.symm y) = 0
      rw [show ψ (L.chart.symm y) = 0 from hy, mul_zero]
    exact (notMem_tsupport_iff_eventuallyEq.mpr heq') hz
  -- The leading symbol retains exactly the finite partition, since every input plateau is one.
  have hsymbol (j : Fin s.card) (x : M) (ξ) :
      (R j).globalSymbolFunction x ξ = (ρ j x : ℂ) • L.globalSymbolFunction x ξ := by
    by_cases hx : x ∈ D
    · dsimp only [D] at hx
      simp only [R, PseudodifferentialPiece.cutoff, BundleChartCutoff.mulSmooth,
        globalSymbolFunction, ite_eq_left hx, L.chart.left_inv hx.1.1]
      rw [smul_smul]
      congr 1
      calc
        _ = ((ρ j x * β j x : ℝ) : ℂ) *
            ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) := by
          push_cast
          ring
        _ = _ := by rw [hprod]
    · dsimp only [D] at hx
      simp [R, PseudodifferentialPiece.cutoff, BundleChartCutoff.mulSmooth,
        globalSymbolFunction, hx]
  have hsymbolsum : (∑ j, (R j).globalSymbol) = L.globalSymbol := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change (∑ j, (R j).globalSymbolFunction) = L.globalSymbolFunction
    funext x ξ
    simp only [Finset.sum_apply, hsymbol]
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      have hsum : ∑ j, ρ j x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hsum, Complex.ofReal_one, one_smul]
    · have hz : L.globalSymbolFunction x ξ = 0 :=
        L.globalSymbolFunction_eq_zero x
          (fun h ↦ hx ((Set.image_mono (Set.inter_subset_left.trans Set.subset_union_left)) h)) ξ
      simp [hz]
  -- Keep the complete actual map: the discarded input tails have separated scalar supports.
  let X (j : Fin s.card) := smoothSectionMul (n := n) (r := r) E (fun x ↦ (β j x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp (hβ j))
  let Y (j : Fin s.card) := smoothSectionMul (n := n) (r := q) F (fun x ↦ (ρ j x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp (ρ j).contMDiff)
  let T (j : Fin s.card) := (Y j).comp (L.toLinearMap.comp (LinearMap.id - X j))
  have hT (j : Fin s.card) : IsSmoothingOperator μ (T j) := by
    have hminus : smoothSectionMul (n := n) (r := r) E (fun x ↦ ((1 - β j x : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub (hβ j))) =
        LinearMap.id - X j := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      change ((1 - β j x : ℝ) : ℂ) • u.val x = u.val x - (β j x : ℂ) • u.val x
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    have ht := L.isSmoothingOperator_cutoff_of_mul_eq_zero (μ := μ)
      (ρ j) (fun x ↦ 1 - β j x) (ρ j).contMDiff (contMDiff_const.sub (hβ j))
      (fun x ↦ by nlinarith [hprod j x])
    rwa [hminus] at ht
  have horiginal : (∑ j, (Y j).comp L.toLinearMap) = L.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
    change ∑ j, (ρ j x : ℂ) • (L.toLinearMap u).val x = (L.toLinearMap u).val x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      have hsum : ∑ j, ρ j x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hsum, Complex.ofReal_one, one_smul]
    · have hz := L.toLinearMap_eq_zero u x
        (fun h ↦ hx ((Set.image_mono Set.subset_union_left) h))
      simp [hz]
  have herror : (∑ j, T j) = L.toLinearMap - ∑ j, (R j).toLinearMap := by
    simp only [T, LinearMap.comp_sub, LinearMap.comp_id, Finset.sum_sub_distrib, horiginal]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact (L.toLinearMap_cutoff (ρ j) (β j) (ρ j).contMDiff (hβ j)).symm
  refine ⟨s.card, fun j ↦ a (index j), R, ?_, hsymbolsum, ?_⟩
  · obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
    obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
    apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ _ A B).mpr
    intro t
    rw [← herror]
    exact (pseudodifferentialSpace E F μ t).sum_mem
      (fun j _ ↦ (hT j).isPseudodifferentialOperator t _)
  · intro j x hx
    rcases hx with ⟨z, hz | hz, rfl⟩
    · -- The same argument applies to the output bundle, whose rank may differ.
      have hzC : z ∈ tsupport L.output.cutoff := tsupport_mul_subset_left hz
      by_contra hn
      have hp : L.chart.symm z ∉ tsupport (ρ j) := fun h ↦ hn ((hsρ j h).1)
      have heq := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
        (L.chart.continuousAt_symm (L.output.support_subset hzC).1)
      have heq' : (R j).output.cutoff =ᶠ[𝓝 z] 0 := by
        filter_upwards [heq] with y hy
        change L.output.cutoff y * ρ j (L.chart.symm y) = 0
        rw [show ρ j (L.chart.symm y) = 0 from hy, mul_zero]
      exact (notMem_tsupport_iff_eventuallyEq.mpr heq') hz
    · exact (hsβ j (hsupport L.input (β j) (hβ j) ⟨z, hz, rfl⟩)).1

end PseudodifferentialPiece

end AtiyahSinger
