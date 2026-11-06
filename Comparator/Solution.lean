/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Statements

/-!
# Atiyah--Singer comparator solution

The seven proofs apply the accepted production endpoints without adding
hypotheses. Their independently written propositions are in Statements.
This module never imports Challenge.
-/

@[expose] public noncomputable section

universe u v w a b

namespace AtiyahSinger.ComparatorTargets

open ComparatorStatements

/-- Compare the full t01 atlas endpoint. -/
theorem t01_atlas : T01Atlas.{u, v, w, a, b} := by
  exact AtlasPseudodifferentialOperator.index_eq_cotangentTopologicalIndex_fullSymbol

/-- Compare the full t01 native endpoint. -/
theorem t01_native : T01Native.{u, v, w} := by
  exact PseudodifferentialOperator.index_eq_cotangentTopologicalIndex_fullSymbol

/-- Compare the full t02 atlas endpoint. -/
theorem t02_atlas : T02Atlas.{a, b} := by
  exact AtlasPseudodifferentialOperator.index_eq_tangent_characteristic_number_fullSymbol

/-- Compare the full t02 native endpoint. -/
theorem t02_native : T02Native := by
  exact PseudodifferentialOperator.index_eq_tangent_characteristic_number_fullSymbol

/-- Compare the full t03 atlas endpoint. -/
theorem t03_atlas : T03Atlas.{a, b} := by
  exact AtlasPseudodifferentialOperator.index_eq_base_characteristic_number_fullSymbol

/-- Compare the full t03 native endpoint. -/
theorem t03_native : T03Native := by
  exact PseudodifferentialOperator.index_eq_base_characteristic_number_fullSymbol

/-- Compare the full t04 endpoint. -/
theorem t04 : T04.{a} := by
  exact EvenDimensionalSpinInput.twistedDiracPlus_index

end AtiyahSinger.ComparatorTargets
