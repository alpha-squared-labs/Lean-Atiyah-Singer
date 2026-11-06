/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The two summands in relative cohomological Mayer–Vietoris

Public module ID: M2066.

The native relative sequence is obtained by dualizing the actual
diagonal-and-difference chain sequence. This module identifies its middle
object with the two original relative cochain complexes. The comparison
retains the two specified inclusions and the difference sign; passing to
cohomology therefore gives the actual restriction maps used in gluing.

These are the additive-category adapters for the standard singular
Mayer–Vietoris argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The canonical dual-biproduct comparison for the original relative cochain sequence. -/
def relativeSingularCochainMayerVietorisMiddleIso (A B : Set X) :
    (relativeSingularCochainMayerVietorisSequence R A B).X₂ ≅
      relativeSingularCochains R A ⊞ relativeSingularCochains R B :=
  (singularCochainDualFunctor R).mapIso
      (biprod.opIso (relativeSingularChains R A) (relativeSingularChains R B)) ≪≫
    (singularCochainDualFunctor R).mapBiprod
      (op (relativeSingularChains R A)) (op (relativeSingularChains R B))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The first middle projection is dual to the original first chain inclusion. -/
theorem relativeSingularCochainMayerVietorisMiddleIso_hom_fst (A B : Set X) :
    (relativeSingularCochainMayerVietorisMiddleIso R A B).hom ≫ biprod.fst =
      (singularCochainDualFunctor R).map
        (biprod.inl : relativeSingularChains R A ⟶
          relativeSingularChains R A ⊞ relativeSingularChains R B).op := by
  dsimp only [relativeSingularCochainMayerVietorisMiddleIso]
  rw [Iso.trans_hom, Category.assoc, Functor.mapBiprod_hom,
    biprod.lift_fst]
  change (singularCochainDualFunctor R).map _ ≫
    (singularCochainDualFunctor R).map _ = _
  rw [← Functor.map_comp, biprod.opIso_hom_fst]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The second middle projection is dual to the original second chain inclusion. -/
theorem relativeSingularCochainMayerVietorisMiddleIso_hom_snd (A B : Set X) :
    (relativeSingularCochainMayerVietorisMiddleIso R A B).hom ≫ biprod.snd =
      (singularCochainDualFunctor R).map
        (biprod.inr : relativeSingularChains R B ⟶
          relativeSingularChains R A ⊞ relativeSingularChains R B).op := by
  dsimp only [relativeSingularCochainMayerVietorisMiddleIso]
  rw [Iso.trans_hom, Category.assoc, Functor.mapBiprod_hom,
    biprod.lift_snd]
  change (singularCochainDualFunctor R).map _ ≫
    (singularCochainDualFunctor R).map _ = _
  rw [← Functor.map_comp, biprod.opIso_hom_snd]

/-- The middle cohomology comparison uses the two original relative cohomology modules. -/
def relativeSingularCohomologyMayerVietorisMiddleIso (A B : Set X) (p : ℕ) :
    (relativeSingularCochainMayerVietorisSequence R A B).X₂.homology p ≅
      relativeSingularCohomology R A p ⊞ relativeSingularCohomology R B p :=
  (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p).mapIso
      (relativeSingularCochainMayerVietorisMiddleIso R A B) ≪≫
    (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p).mapBiprod
      (relativeSingularCochains R A) (relativeSingularCochains R B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native middle-to-last cochain map becomes the sum of the actual restrictions. -/
theorem relativeSingularCochainMayerVietorisMiddleIso_hom_sum (A B : Set X) :
    (relativeSingularCochainMayerVietorisMiddleIso R A B).hom ≫
      biprod.desc
        ((singularCochainDualFunctor R).map
          ((relativeSingularChainsFunctor R X).map (homOfLE Set.inter_subset_left)).op)
        ((singularCochainDualFunctor R).map
          ((relativeSingularChainsFunctor R X).map (homOfLE Set.inter_subset_right)).op) =
      (relativeSingularCochainMayerVietorisSequence R A B).g := by
  -- Resolve the sum through its projections before dualizing the diagonal map.
  rw [biprod.desc_eq, Preadditive.comp_add,
    ← Category.assoc, ← Category.assoc,
    relativeSingularCochainMayerVietorisMiddleIso_hom_fst,
    relativeSingularCochainMayerVietorisMiddleIso_hom_snd,
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add]
  congr 1
  apply Quiver.Hom.unop_inj
  simp [relativeSingularMayerVietorisShortComplex, biprod.lift_eq]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- After the specified union comparison, the first map is the difference of restrictions. -/
theorem relativeSingularCochainMayerVietorisMiddleIso_comparison_difference (A B : Set X) :
    (singularCochainDualFunctor R).map (relativeUnionSingularChainsToRelative R A B).op ≫
      (relativeSingularCochainMayerVietorisSequence R A B).f ≫
      (relativeSingularCochainMayerVietorisMiddleIso R A B).hom =
    biprod.lift
      ((singularCochainDualFunctor R).map
        ((relativeSingularChainsFunctor R X).map (homOfLE Set.subset_union_left)).op)
      (-((singularCochainDualFunctor R).map
        ((relativeSingularChainsFunctor R X).map (homOfLE Set.subset_union_right)).op)) := by
  let S := relativeSingularMayerVietorisShortComplex R A B
  let D := singularCochainDualFunctor R
  let q := relativeUnionSingularChainsToRelative R A B
  have hleft : (biprod.inl : relativeSingularChains R A ⟶ S.X₂) ≫ S.g ≫ q =
      (relativeSingularChainsFunctor R X).map (homOfLE Set.subset_union_left) := by
    apply (cancel_epi (relativeSingularChainsProjection R A)).mp
    simp [S, q, relativeSingularMayerVietorisShortComplex,
      relativeUnionSingularChainsToRelative, relativeSingularChainsFunctor,
      relativeSingularChainsMap, relativeSingularChainsProjection]
  have hright : (biprod.inr : relativeSingularChains R B ⟶ S.X₂) ≫ S.g ≫ q =
      -(relativeSingularChainsFunctor R X).map (homOfLE Set.subset_union_right) := by
    apply (cancel_epi (relativeSingularChainsProjection R B)).mp
    simp [S, q, relativeSingularMayerVietorisShortComplex,
      relativeUnionSingularChainsToRelative, relativeSingularChainsFunctor,
      relativeSingularChainsMap, relativeSingularChainsProjection]
  -- Dualize the two quotient identities separately, retaining the original minus sign.
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc,
      relativeSingularCochainMayerVietorisMiddleIso_hom_fst, biprod.lift_fst]
    change D.map q.op ≫ D.map S.g.op ≫ D.map biprod.inl.op = _
    rw [← D.map_comp, ← D.map_comp]
    have h := congrArg (fun f ↦ D.map f.op) hleft
    simpa only [op_comp, Category.assoc] using h
  · rw [Category.assoc, Category.assoc,
      relativeSingularCochainMayerVietorisMiddleIso_hom_snd, biprod.lift_snd]
    change D.map q.op ≫ D.map S.g.op ≫ D.map biprod.inr.op = _
    rw [← D.map_comp, ← D.map_comp]
    have h := congrArg (fun f ↦ D.map f.op) hright
    simpa only [op_comp, Category.assoc, op_neg, D.map_neg] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In cohomology the middle-to-last map is the sum of the original relative restrictions. -/
theorem relativeSingularCohomologyMayerVietorisMiddleIso_hom_sum (A B : Set X) (p : ℕ) :
    (relativeSingularCohomologyMayerVietorisMiddleIso R A B p).hom ≫
      biprod.desc
        (relativeSingularCohomologyRestriction R (A ∩ B) A Set.inter_subset_left p)
        (relativeSingularCohomologyRestriction R (A ∩ B) B Set.inter_subset_right p) =
      homologyMap (relativeSingularCochainMayerVietorisSequence R A B).g p := by
  let H := homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p
  dsimp only [relativeSingularCohomologyMayerVietorisMiddleIso]
  rw [Iso.trans_hom]
  change (H.map (relativeSingularCochainMayerVietorisMiddleIso R A B).hom ≫
    (H.mapBiprod (relativeSingularCochains R A) (relativeSingularCochains R B)).hom) ≫
    biprod.desc (H.map _) (H.map _) = H.map _
  rw [Category.assoc, biprod.mapBiprod_hom_desc, ← H.map_comp]
  exact congrArg H.map (relativeSingularCochainMayerVietorisMiddleIso_hom_sum R A B)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In cohomology the union comparison identifies the first map with the actual difference. -/
theorem relativeSingularCohomologyMayerVietorisMiddleIso_comparison_difference
    (A B : Set X) (p : ℕ) :
    relativeUnionCohomologyComparison R A B p ≫
      homologyMap (relativeSingularCochainMayerVietorisSequence R A B).f p ≫
      (relativeSingularCohomologyMayerVietorisMiddleIso R A B p).hom =
    biprod.lift
      (relativeSingularCohomologyRestriction R A (A ∪ B) Set.subset_union_left p)
      (-(relativeSingularCohomologyRestriction R B (A ∪ B) Set.subset_union_right p)) := by
  let H := homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p
  change H.map _ ≫ H.map _ ≫
    (H.map (relativeSingularCochainMayerVietorisMiddleIso R A B).hom ≫
      (H.mapBiprod (relativeSingularCochains R A) (relativeSingularCochains R B)).hom) =
    biprod.lift (H.map _) (-(H.map _))
  have h := congrArg (fun f ↦ H.map f ≫
    (H.mapBiprod (relativeSingularCochains R A) (relativeSingularCochains R B)).hom)
      (relativeSingularCochainMayerVietorisMiddleIso_comparison_difference R A B)
  simpa only [H.map_comp, Category.assoc, biprod.map_lift_mapBiprod, H.map_neg,
    Functor.op_map] using h

end AtiyahSinger
