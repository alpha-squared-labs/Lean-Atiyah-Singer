/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularHomology
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Naturality of the original degree-zero augmentation

Public module ID: M2142.

The ordinary augmentation sums the coefficients of a finite zero-cycle.
A continuous map sends each point generator to its image with that same
coefficient, so it preserves augmentation. This comparison uses mathlib's
specified augmentation and the original singular homology functor.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every continuous map preserves the augmentation of the original ordinary zero-homology. -/
theorem singularHomologyMap_augmentation (R : Type) [CommRing R]
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    singularHomologyMap R f 0 ≫ (TopCat.of Y).singularHomology₀ε (singularCoefficient R) =
      (TopCat.of X).singularHomology₀ε (singularCoefficient R) := by
  let C := singularChains R X
  let F := (singularChainsFunctor R).map (TopCat.ofHom f)
  let SX := TopCat.toSSet.obj (TopCat.of X)
  let SY := TopCat.toSSet.obj (TopCat.of Y)
  let : IsIso (C.iCycles 0) := ChainComplex.isIso_iCycles₀ C
  -- Every zero-chain is a cycle; their original quotient map is surjective on homology.
  apply (cancel_epi (C.homologyπ 0)).mp
  apply (cancel_epi (inv (C.iCycles 0))).mp
  apply Sigma.hom_ext
  intro σ
  have hlift : SX.ιChainComplex (R := singularCoefficient R) σ ≫ inv (C.iCycles 0) =
      C.liftCycles (SX.ιChainComplex (R := singularCoefficient R) σ) 0
        (by simp) (by simp) := by
    apply (cancel_mono (C.iCycles 0)).mp
    simp
  change SX.ιChainComplex (R := singularCoefficient R) σ ≫ inv (C.iCycles 0) ≫
    C.homologyπ 0 ≫ HomologicalComplex.homologyMap F 0 ≫
      SY.homology₀ε (singularCoefficient R) =
        SX.ιChainComplex (R := singularCoefficient R) σ ≫ inv (C.iCycles 0) ≫
          C.homologyπ 0 ≫ SX.homology₀ε (singularCoefficient R)
  simp only [← Category.assoc, hlift]
  simp only [Category.assoc]
  -- The homology map carries this very point generator to its image point generator.
  erw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, SSet.ι_chainComplexMap_f]
  exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε SY
    (singularCoefficient R) ((TopCat.toSSet.map (TopCat.ofHom f)).app (op ⦋0⦌) σ)).trans
    (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε SX (singularCoefficient R) σ).symm

end AtiyahSinger
