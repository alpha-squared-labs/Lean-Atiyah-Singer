/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.PositiveStepCupEvaluation

/-!
# Naturality of the positive step boundary class

Public module ID: M1998.

Pulling back a real-valued coordinate pulls back its original step coboundary.
The proof uses the actual morphism between the two pair cochain sequences.
This identifies the first-coordinate class in the base and in its product
with the fiber, without introducing a separate orientation witness.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The positive step coboundary pulls back along the same continuous coordinate map. -/
theorem positiveStepBoundaryClass_natural (R : Type) [CommRing R]
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, ℝ)) (g : C(Y, X)) :
    relativeSingularCohomologyPullback R g
        (A := {y : Y | (f.comp g) y ≠ 0}) (B := {x : X | f x ≠ 0})
        (fun _ h ↦ h) 1 (positiveStepBoundaryClass R f) =
      positiveStepBoundaryClass R (f.comp g) := by
  let A : Set X := {x | f x ≠ 0}
  let B : Set Y := {y | (f.comp g) y ≠ 0}
  let gB : C(B, A) := ⟨fun y ↦ ⟨g y.val, y.property⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let hg : Set.MapsTo g B A := fun _ h ↦ h
  let D := singularCochainDualFunctor R
  let G := (singularChainsFunctor R).map (TopCat.ofHom g)
  let GB := (singularChainsFunctor R).map (TopCat.ofHom gB)
  let S := singularSubspaceCochainsSequence R A
  let T := singularSubspaceCochainsSequence R B
  -- The same ordinary and relative chain maps commute with both pair inclusions.
  let φ : S ⟶ T :=
    { τ₁ := D.map (relativeSingularChainsMap R g hg).op
      τ₂ := D.map G.op
      τ₃ := D.map GB.op
      comm₁₂ := by
        change D.map (relativeSingularChainsMap R g hg).op ≫
            D.map (relativeSingularChainsProjection R B).op =
          D.map (relativeSingularChainsProjection R A).op ≫ D.map G.op
        rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp]
        congr 1
        apply congrArg Quiver.Hom.op
        simp [relativeSingularChainsMap, relativeSingularChainsProjection, G]
      comm₂₃ := by
        change D.map G.op ≫ D.map (singularSubspaceChains R B).op =
          D.map (singularSubspaceChains R A).op ≫ D.map GB.op
        rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp]
        congr 1
        apply congrArg Quiver.Hom.op
        simp only [G, GB, singularSubspaceChains, ← Functor.map_comp]
        rfl }
  let tx : C(A, ℝ) := ⟨fun x ↦ f x.val, f.continuous.comp continuous_subtype_val⟩
  let ty : C(B, ℝ) := ⟨fun y ↦ (f.comp g) y.val,
    (f.comp g).continuous.comp continuous_subtype_val⟩
  let sx := positiveStepLocallyConstant R tx (fun x ↦ x.property)
  let sy := positiveStepLocallyConstant R ty (fun y ↦ y.property)
  have hstep : singularCohomologyPullback R gB 0
      (locallyConstantSingularCohomologyClass R A sx) =
      locallyConstantSingularCohomologyClass R B sy := by
    rw [locallyConstantSingularCohomologyClass_natural]
    apply congrArg (locallyConstantSingularCohomologyClass R B)
    ext y
    change sx (gB y) = sy y
    rw [positiveStepLocallyConstant_apply, positiveStepLocallyConstant_apply]
    rfl
  have hδ := congrArg (fun h ↦ h (locallyConstantSingularCohomologyClass R A sx))
    (HomologySequence.δ_naturality φ (shortExact_singularSubspaceCochains R A)
      (shortExact_singularSubspaceCochains R B) 0 1 rfl)
  exact hδ.trans (congrArg
    (fun z ↦ (shortExact_singularSubspaceCochains R B).δ 0 1 rfl z) hstep)

end AtiyahSinger
