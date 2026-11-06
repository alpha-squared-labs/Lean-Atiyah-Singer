/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Statements

/-!
# Atiyah--Singer comparator challenge

This isolated challenge intentionally admits only the seven comparison targets.
It is not imported by Solution or by the production mathematical library.
The comparator requires legal, fully checked proofs on the solution side.
-/

@[expose] public noncomputable section

universe u v w a b

namespace AtiyahSinger.ComparatorTargets

open ComparatorStatements

/-- Compare the full t01 atlas endpoint. -/
theorem t01_atlas : T01Atlas.{u, v, w, a, b} := by
  sorry

/-- Compare the full t01 native endpoint. -/
theorem t01_native : T01Native.{u, v, w} := by
  sorry

/-- Compare the full t02 atlas endpoint. -/
theorem t02_atlas : T02Atlas.{a, b} := by
  sorry

/-- Compare the full t02 native endpoint. -/
theorem t02_native : T02Native := by
  sorry

/-- Compare the full t03 atlas endpoint. -/
theorem t03_atlas : T03Atlas.{a, b} := by
  sorry

/-- Compare the full t03 native endpoint. -/
theorem t03_native : T03Native := by
  sorry

/-- Compare the full t04 endpoint. -/
theorem t04 : T04.{a} := by
  sorry

end AtiyahSinger.ComparatorTargets
