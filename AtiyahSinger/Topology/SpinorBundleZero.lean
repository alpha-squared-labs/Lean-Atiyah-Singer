/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinZero
public import AtiyahSinger.Algebra.SpinorWeights
public import AtiyahSinger.Topology.AssociatedVectorCoordinates
public import AtiyahSinger.Topology.SpinorBundle

/-!
# The original associated half-spin fibers in dimension zero

Public module ID: M2176.

The empty exterior monomial is positive and spans the original even spinor
space; the odd space is zero. The original associated-coordinate equivalence
transfers these dimensions to the actual half-spin quotient fibers over any
specified principal bundle for the native zero-dimensional spin group.

Source: Lawson--Michelsohn, Spin Geometry, I.5, the exterior model and its
parity decomposition. This is the zero-dimensional endpoint of that model,
with the native generated-group convention made explicit in SpinZero.
The existing full-spin dimension theorem already covers dimension zero.

The even associated fiber is retained as its original quotient, not replaced
by a trivial line. No new spin structure, canonical global trivialization,
or stable two-sheeted rank-zero lift is asserted. The dimensions of these
original quotient fibers are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

variable {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)

/-- In dimension zero the original positive half-spin fiber is a line and the negative is zero. -/
theorem finrank_halfSpinorBundle_zero (i : ZMod 2) (b : B) :
    Module.finrank ℂ (HalfSpinorBundle 0 hP i b) = if i = 0 then 1 else 0 := by
  /- Stage 1: choose a point of the supplied original principal fiber over b.
  The existing associatedVectorFiberMkLinearEquiv uses that same point to
  identify the original parity model with the original associated quotient
  fiber; its forward map is exactly s -> [p,s]. It preserves complex dimension.
  Stage 2: complexSpinorParityBasis indexes the original parity model by
  subsets of Fin 0 having cardinality congruent to i modulo two. The only
  subset is empty, of even cardinality. Thus the basis has one element for
  i=0 and no elements for i=1, giving exactly the displayed conditional.
  The associated bundle and its operations remain unchanged; no continuity
  of the chosen principal point or global line trivialization is assumed. -/
  classical
  -- First transfer dimension through the original fiber coordinates and parity basis.
  rw [(associatedVectorFiberLinearEquiv hP (complexSpinParityContRepresentation 0 i) b).finrank_eq,
    Module.finrank_eq_card_basis (complexSpinorParityBasis 0 i)]
  -- The empty subset is the unique even index; there are no indices of odd parity.
  by_cases hi : i = 0
  · subst i
    let : Unique {s : Finset (Fin 0) // (s.card : ZMod 2) = 0} :=
      { default := ⟨∅, by simp⟩
        uniq := fun s ↦ Subtype.ext (Subsingleton.elim _ _) }
    simp
  · let : IsEmpty {s : Finset (Fin 0) // (s.card : ZMod 2) = i} := ⟨by
      intro s
      have hs : s.val = ∅ := Subsingleton.elim _ _
      exact hi (by simpa [hs] using s.property.symm)⟩
    simp [hi]

end AtiyahSinger
