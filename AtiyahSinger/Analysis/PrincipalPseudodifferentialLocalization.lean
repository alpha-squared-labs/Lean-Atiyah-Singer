/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SubordinatePseudodifferentialRepresentative
public import AtiyahSinger.Geometry.SmoothOrthogonalPrincipalBundle

import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A fixed native representative localized in the original principal atlas

Public module ID: M0870.

The data retain the actual finite family, its original principal chart centers,
the input plateaus, and the exact base PDO given by summing that family. Every
original PDO admits such data with the same principal class. Later horizontal
and vertical comparisons can therefore refer to one specified representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 15 in
/-- Fixed implementation data for a representative localized in the specified principal atlas. -/
structure PrincipalPseudodifferentialLocalization (m : ℝ) where
  /-- The finite number of native pieces, allowing the empty family. -/
  size : ℕ
  /-- The original principal chart selected for each piece. -/
  center : Fin size → B
  /-- The specified native PDO pieces, with unchanged base bundle models. -/
  piece : Fin size → PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m
  /-- The actual global base PDO that will be lifted. -/
  baseOperator : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m
  /-- Its section action is exactly the sum of these specified pieces. -/
  baseOperator_eq : baseOperator.toLinearMap = ∑ j, (piece j).toLinearMap
  /-- Both original supports of each piece lie in its selected principal chart. -/
  piece_support : ∀ j, (piece j).chart.symm ''
    (tsupport (piece j).output.cutoff ∪ tsupport (piece j).input.cutoff) ⊆
      (S.trivialization (center j)).baseSet
  /-- The base-only input plateau for each principal chart. -/
  inputCutoff : Fin size → B → ℝ
  /-- Every base plateau is smooth in the original base manifold. -/
  smooth_inputCutoff : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (inputCutoff j)
  /-- Its closed support lies inside the selected original principal chart. -/
  inputCutoff_support : ∀ j,
    tsupport (inputCutoff j) ⊆ (S.trivialization (center j)).baseSet
  /-- It is one on the entire original input support of the same piece. -/
  inputCutoff_eq_one : ∀ j, ∀ x ∈ (piece j).chart.symm '' tsupport (piece j).input.cutoff,
    inputCutoff j x = 1

set_option maxSynthPendingDepth 15 in
/-- Every base PDO has a representative in the original principal charts with the same class. -/
theorem PseudodifferentialOperator.exists_principalLocalization {m : ℝ}
    (R : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m) :
    ∃ C : PrincipalPseudodifferentialLocalization S E E' μ m,
      C.baseOperator.principalSymbol = R.principalSymbol := by
  classical
  obtain ⟨N, b, L, Q, hL, hQ, hsymbol⟩ := R.exists_subordinate_representative
    (fun b ↦ (S.trivialization b).baseSet)
    (fun b ↦ (S.trivialization b).open_baseSet) (fun x ↦ ⟨x, S.mem_baseSet x⟩)
  -- The original compact input supports admit base plateaus inside their principal charts.
  have hcutoff (j : Fin N) : ∃ χ : B → ℝ,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ tsupport χ ⊆ (S.trivialization (b j)).baseSet ∧
      ∀ x ∈ (L j).chart.symm '' tsupport (L j).input.cutoff, χ x = 1 := by
    let K := (L j).chart.symm '' tsupport (L j).input.cutoff
    have hK : IsCompact K := (L j).input.compact_support.image_of_continuousOn
      ((L j).chart.continuousOn_symm.mono (fun x hx ↦ ((L j).input.support_subset hx).1))
    have hKU : K ⊆ (S.trivialization (b j)).baseSet := by
      rintro x ⟨y, hy, rfl⟩
      exact hL j ⟨y, Or.inr hy, rfl⟩
    obtain ⟨W, hW, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure
      hK (S.trivialization (b j)).open_baseSet hKU
    obtain ⟨χ, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓡 n) (n := ⊤) hK.isClosed (hKW.trans hW.subset_interior_closure)
    have hs : tsupport χ ⊆ closure W := by
      apply closure_minimal ?_ hWc.isClosed
      intro x hx
      by_contra hn
      exact hx (hzero x hn)
    refine ⟨χ, χ.contMDiff, hs.trans hWU, ?_⟩
    intro x hx
    exact hone.self_of_nhdsSet x hx
  choose χ hχ hsχ honeχ using hcutoff
  -- Keep Q and every localization witness together; no remainder is lifted.
  exact ⟨{
    size := N
    center := b
    piece := L
    baseOperator := Q
    baseOperator_eq := hQ
    piece_support := hL
    inputCutoff := χ
    smooth_inputCutoff := hχ
    inputCutoff_support := hsχ
    inputCutoff_eq_one := honeχ }, hsymbol⟩

end AtiyahSinger
