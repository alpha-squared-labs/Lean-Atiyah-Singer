/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSupportedCohomologyThom

/-!
# Comparing the triple boundary with the joint relative boundary

Public module ID: M2102.

For A contained in L contained in B union A, restriction gives a morphism
from the original cochain triple to the joint relative cochain sequence.
Naturality of its connecting homomorphism retains the actual union comparison
and the actual inclusion of B into B union A. This is the comparison used
for suspension through upper and lower half-axis complements.

Source: naturality of the long exact sequence of a triple, Hatcher,
Algebraic Topology, Sections 2.1 and 3.2. No openness is needed for this
identity; openness is used separately when the union comparison is inverted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction intertwines the actual triple and joint-support connecting homomorphisms. -/
theorem relativeUnionSingularCohomologyBoundary_triple (R : Type) [CommRing R]
    {X : Type u} [TopologicalSpace X] (A B L : Set X)
    (hAL : A ⊆ L) (hLU : L ⊆ B ∪ A) (k : ℕ) :
    (shortExact_relativeSingularCochainTripleSequence R L (B ∪ A) hLU).δ
        k (k + 1) rfl ≫ relativeUnionCohomologyComparison R B A (k + 1) =
      relativeSingularCohomologyPullback R
        (⟨fun z ↦ ⟨z.val, Or.inl z.property⟩,
          continuous_subtype_val.subtype_mk _⟩ : C(B, ↥(B ∪ A)))
        (A := (Subtype.val : B → X) ⁻¹' A)
        (B := (Subtype.val : ↥(B ∪ A) → X) ⁻¹' L)
        (fun _ hz ↦ hAL hz) k ≫
          (shortExact_relativeUnionSingularCochainSequence R A B).δ k (k + 1) rfl := by
  /- Construct the map on the original chain quotients first. Its left
  square consists of actual inclusions of pairs. Its right square is
  verified after the epimorphic ordinary chain projection. Dualize this
  same short-complex map and apply connecting-homomorphism naturality. -/
  let U := B ∪ A
  let i : C(B, U) := ⟨fun z ↦ ⟨z.val, Or.inl z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  let S := relativeUnionSingularChainSequence R A B
  let T := relativeSingularTripleSequence R L U hLU
  let f := relativeSingularChainsMap R (ContinuousMap.id X) (fun _ hx ↦ hAL hx)
  let Q := relativeUnionSingularChainsToRelative R B A
  have hS : relativeSingularChainsProjection R A ≫ S.g =
      relativeUnionSingularChainsProjection R B A := by
    exact cokernel.π_desc _ _ _
  have hQ : relativeUnionSingularChainsProjection R B A ≫ Q =
      relativeSingularChainsProjection R U := cokernel.π_desc _ _ _
  have hT : relativeSingularChainsProjection R A ≫ (f ≫ T.g) =
      relativeSingularChainsProjection R U := by
    change relativeSingularChainsProjection R A ≫
      (relativeSingularChainsMap R (ContinuousMap.id X) (fun _ hx ↦ hAL hx) ≫
        relativeSingularChainsMap R (ContinuousMap.id X) (fun _ hx ↦ hLU hx)) = _
    rw [← relativeSingularChainsMap_comp]
    simp [relativeSingularChainsMap, relativeSingularChainsProjection,
      singularSubspaceChains, cokernel.map]
    rfl
  let φ : S ⟶ T :=
    { τ₁ := relativeSingularChainsMap R i
        (A := (Subtype.val : B → X) ⁻¹' A)
        (B := (Subtype.val : U → X) ⁻¹' L) (fun _ hz ↦ hAL hz)
      τ₂ := f
      τ₃ := Q
      comm₁₂ := by
        change relativeSingularChainsMap R i (fun _ hz ↦ hAL hz) ≫
            relativeSingularChainsMap R (ContinuousMap.subtypeVal U) (fun _ hx ↦ hx) =
          relativeSingularChainsMap R (ContinuousMap.subtypeVal B) (fun _ hx ↦ hx) ≫ f
        dsimp only [f]
        rw [← relativeSingularChainsMap_comp, ← relativeSingularChainsMap_comp]
        rfl
      comm₂₃ := by
        apply (cancel_epi (relativeSingularChainsProjection R A)).mp
        rw [hT, ← Category.assoc, hS, hQ] }
  exact HomologySequence.δ_naturality
    ((singularCochainDualFunctor R).mapShortComplex.map (ShortComplex.opMap φ))
    (shortExact_relativeSingularCochainTripleSequence R L U hLU)
    (shortExact_relativeUnionSingularCochainSequence R A B) k (k + 1) rfl

end AtiyahSinger
