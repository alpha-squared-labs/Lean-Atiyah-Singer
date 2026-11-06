/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPrincipalSymbol

/-!
# Compact full symbols for actual PDO pieces

Public module ID: M0363.

A compact spatial plateau equal to one on the original output cutoff support
replaces a piece by one with a compact uncut full symbol. Its actual global section
map and transported globalSymbol representative remain unchanged. This supplies
compact symbols for the product-frequency construction with the original action.
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

/-- Every piece admits a compact uncut full symbol with the same section action
and exactly the same transported globalSymbol representative. -/
theorem PseudodifferentialPiece.exists_compactSymbol {d : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F d) :
    ∃ K : PseudodifferentialPiece (n := n) (r := r) (q := q) E F d,
      HasCompactSupport K.symbol ∧ K.toLinearMap = L.toLinearMap ∧
        K.globalSymbol = L.globalSymbol := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  obtain ⟨O, hO, hKO, _, hcO⟩ := exists_open_between_and_isCompact_closure
    L.output.compact_support isOpen_univ (Set.subset_univ _)
  obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO (isClosed_tsupport L.output.cutoff) hKO
  have hχK : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    rw [show tsupport χ = closure O from congrArg closure hsχ]
    exact hcO
  have hone (x : X) (hx : x ∈ tsupport L.output.cutoff) : χ x = 1 := (honeχ x).mp hx
  let a := zeroExtendedSymbol Set.univ χ L.symbol
  have ha : IsSymbol Set.univ d a :=
    isSymbol_zeroExtendedSymbol Set.univ isOpen_univ d χ hχ hχK
      (Set.subset_univ _) L.symbol L.isSymbol
  have haK : HasCompactSupport a := hasCompactSupport_zeroExtendedSymbol _ χ L.symbol hχK
  let K : PseudodifferentialPiece (n := n) (r := r) (q := q) E F d :=
    { L with
      symbol := a
      isSymbol := ha
      operator := quantizeSchwartz d a ha haK
      operator_apply := quantizeSchwartz_apply d a ha haK }
  have hquant (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      quantize a u x = (χ x : ℂ) • quantize L.symbol u x := by
    simp only [a, zeroExtendedSymbol, Set.mem_univ, ↓reduceIte, quantize, smul_apply]
    simp_rw [smul_comm (Complex.exp _) (χ x : ℂ)]
    rw [integral_smul, smul_comm]
  refine ⟨K, haK, ?_, ?_⟩
  · apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change K.output.extendedFunction (K.operator (K.input.localize K.chart_mem_atlas u)) x =
      L.output.extendedFunction (L.operator (L.input.localize L.chart_mem_atlas u)) x
    by_cases hx : x ∈ L.chart.source
    · simp only [K, BundleChartCutoff.extendedFunction, ite_eq_left hx,
        quantizeSchwartz_apply, hquant, map_smul]
      by_cases ho : L.output.cutoff (L.chart x) = 0
      · simp [ho]
      rw [hone _ (subset_tsupport _ ho), Complex.ofReal_one, one_smul, L.operator_apply]
    · simp only [K, BundleChartCutoff.extendedFunction, ite_eq_right hx]
  · -- The plateau also cancels in the transported representative before the principal quotient.
    apply Subtype.ext
    funext x ξ
    change K.globalSymbolFunction x ξ = L.globalSymbolFunction x ξ
    simp only [K, PseudodifferentialPiece.globalSymbolFunction]
    split_ifs
    · by_cases ho : L.output.cutoff (L.chart x) = 0
      · simp [ho]
      simp only [a, zeroExtendedSymbol, Set.mem_univ, ↓reduceIte,
        hone _ (subset_tsupport _ ho), Complex.ofReal_one, one_smul]
    · rfl

end AtiyahSinger
