/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyLerayHirschReindex

/-!
# Transport of a Leray--Hirsch comparison over the same base

Public module ID: M2135.

The original comparison commutes with a specified total-space map over a
fixed base whenever that map preserves the specified cohomology classes.
Only their classes must agree; the cocycle representatives may be chosen
independently. This is used for the projective puncture and local models.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A specified map over the same base transports the actual finite comparison on homology. -/
theorem homologyMap_singularCohomologyLerayHirschMap_comp_pullback
    (R : Type) [CommRing R] {X Y Y' : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y']
    {ι : Type u} [Fintype ι]
    (π : C(Y, X)) (π' : C(Y', X)) (f : C(Y', Y)) (hπ : π.comp f = π')
    (d : ι → ℕ) (c : ∀ i, singularCocycles R Y (d i))
    (c' : ∀ i, singularCocycles R Y' (d i))
    (hc : ∀ i, singularCohomologyPullback R f (d i) (singularCocycleClass R Y (d i) (c i)) =
      singularCocycleClass R Y' (d i) (c' i)) (n : ℕ) :
    homologyMap (singularCohomologyLerayHirschMap R π d c) n ≫
        singularCohomologyPullback R f n =
      homologyMap (singularCohomologyLerayHirschMap R π' d c') n := by
  let C (i : ι) : CochainComplex (ModuleCat.{u} R) ℕ :=
    (singularCochains R X).extend (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))
  let c₀ (i : ι) := singularCocyclePullback R f (d i) (c i)
  -- On the unchanged base the naturality map on the source product is its identity.
  have hbase : (singularCochainsFunctor R).map
      (TopCat.ofHom (ContinuousMap.id X)).op = 𝟙 (singularCochains R X) :=
    (singularCochainsFunctor R).map_id _
  have hprod : cochainFamilyProductMap R id (fun i : ι ↦
      extendMap ((singularCochainsFunctor R).map (TopCat.ofHom (ContinuousMap.id X)).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) (d i))) = 𝟙 (cochainFamilyProduct R C) := by
    rw [hbase]
    simp only [extendMap_id]
    ext q a
    rfl
  have hn := singularCohomologyLerayHirschMap_natural R π π' f (ContinuousMap.id X)
    (by simpa using hπ) d c
  rw [hprod, Category.id_comp] at hn
  have hhom := congrArg (fun g ↦ homologyMap g n) hn
  rw [homologyMap_comp] at hhom
  -- Replace pulled-back cocycles only after identifying their original cohomology classes.
  have hclasses (i : ι) : singularCocycleClass R Y' (d i) (c₀ i) =
      singularCocycleClass R Y' (d i) (c' i) :=
    (singularCocycleClass_pullback R f (d i) (c i)).trans (hc i)
  exact hhom.symm.trans
    (homologyMap_singularCohomologyLerayHirschMap_congr R π' d c₀ c' hclasses n)

end AtiyahSinger
