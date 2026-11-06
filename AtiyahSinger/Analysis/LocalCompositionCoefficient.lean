/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LocalComposition
public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.SymbolLocality

/-!
# Composition coefficients on an arbitrary open coordinate domain

Public module ID: M0785.

The finite composition coefficients depend only on the original local symbol
germs. Extending those germs near each compact window reduces their estimates
to the established whole-space coefficient theorem, without a global bound on
the original coordinate coefficients.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff Topology

/-- The degree-j composition coefficient has the expected order on every open domain. -/
theorem isSymbol_compositionExpansionTerm_on {n r s t : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol U l p) (hq : IsSymbol U m q) (j : ℕ) :
    IsSymbol U (l + m - (j : ℝ)) (compositionExpansionTerm p q j) := by
  classical
  apply IsSymbol.of_locally hU
  intro x hx
  -- Both extensions retain all frequency values on the same spatial neighborhood.
  obtain ⟨V, hV, hxV, hVUc, hVc⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_singleton (x := x)) hU
      (Set.singleton_subset_iff.mpr hx)
  obtain ⟨W, hW, hVW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hVc hU hVUc
  obtain ⟨χ, hχ, _, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hVW
  have hcχ : HasCompactSupport χ := by
    simpa only [HasCompactSupport, tsupport, hχsupp] using hWc
  have hχU : tsupport χ ⊆ U := by
    simpa only [tsupport, hχsupp] using hWU
  let p' := zeroExtendedSymbol U χ p
  let q' := zeroExtendedSymbol U χ q
  have hp' := isSymbol_zeroExtendedSymbol U hU l χ hχ hcχ hχU p hp
  have hq' := isSymbol_zeroExtendedSymbol U hU m χ hχ hcχ hχU q hq
  have hVU : V ⊆ U := Set.Subset.trans subset_closure hVUc
  have hVsub {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ V) :
      p' y = p y ∧ q' y = q y ∧ y ∈ U := by
    have hχy : χ y = 1 := (hχone y).mp (subset_closure hy)
    have hpval : p' y = p y := by
      funext ξ
      simp only [p', zeroExtendedSymbol_apply_of_mem U χ p y ξ (hVU hy),
        hχy, Complex.ofReal_one, one_smul]
    have hqval : q' y = q y := by
      funext ξ
      simp only [q', zeroExtendedSymbol_apply_of_mem U χ q y ξ (hVU hy),
        hχy, Complex.ofReal_one, one_smul]
    exact ⟨hpval, hqval, hVU hy⟩
  have hterm (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V)
      (ξ : EuclideanSpace ℝ (Fin n)) :
      compositionExpansionTerm p' q' j y ξ = compositionExpansionTerm p q j y ξ := by
    have hqnear : (fun z ↦ q' z ξ) =ᶠ[nhds y] (fun z ↦ q z ξ) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact congrFun (hVsub hz).2.1 ξ
    simp only [compositionExpansionTerm, (hVsub hy).1,
      (hqnear.iteratedFDeriv ℝ j).eq_of_nhds]
  have hglobal := isSymbol_compositionExpansionTerm l m p' q' hp' hq' j
  refine ⟨V, hV, hxV (Set.mem_singleton x), hVU, ?_, ?_⟩
  · -- Smoothness is transported through equality on the open product neighborhood.
    apply (hglobal.1.mono (Set.prod_mono (Set.subset_univ _) le_rfl)).congr
    intro z hz
    exact (hterm z.1 hz.1 z.2).symm
  · intro K hKV hK i k
    obtain ⟨C, hC, hbound⟩ := hglobal.2 K (Set.subset_univ _) hK i k
    refine ⟨C, hC, ?_⟩
    intro y hy ξ
    have hnear : (fun z ↦ iteratedFDeriv ℝ k (compositionExpansionTerm p' q' j z) ξ)
        =ᶠ[nhds y] (fun z ↦ iteratedFDeriv ℝ k (compositionExpansionTerm p q j z) ξ) := by
      filter_upwards [hV.mem_nhds (hKV hy)] with z hz
      have hzall : compositionExpansionTerm p' q' j z =
          compositionExpansionTerm p q j z := funext (hterm z hz)
      rw [hzall]
    have hder : symbolDerivative (compositionExpansionTerm p' q' j) i k y ξ =
        symbolDerivative (compositionExpansionTerm p q j) i k y ξ :=
      (hnear.iteratedFDeriv ℝ i).eq_of_nhds
    rw [← hder]
    exact hbound y hy ξ

end AtiyahSinger
