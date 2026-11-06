/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectivePuncture
public import AtiyahSinger.Topology.ProjectiveTautologicalSubspace

/-!
# The actual projective puncture over an arbitrary parameter space

Public module ID: M2020.

Removing the same projective point from every fiber of a product retracts
onto the product with its orthogonal projective hyperplane. The homotopy
retains the parameter, and the inverse is the actual projective subspace
inclusion. Pulling back the restricted tautological Chern root along that
same inverse gives the original lower-dimensional tautological root.

This supplies the geometric comparison for the lower Leray--Hirsch summands;
it does not assume or replace the projective cohomology computation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open CategoryTheory
open scoped ContinuousMap

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] (X : Type u) [TopologicalSpace X] (e : V) (he : e ≠ 0)

/-- The original deleted-point deformation preserves an arbitrary product parameter. -/
def puncturedProdHomotopyEquiv :
    {z : X × HermitianProjectiveSpace V InnerProductSpace.toCore // z.2 ≠ ofVector e he} ≃ₕ
      X × HermitianProjectiveSpace (Submodule.span ℂ {e})ᗮ InnerProductSpace.toCore := by
  let Q := HermitianProjectiveSpace V InnerProductSpace.toCore
  let A : Set (X × Q) := {z | z.2 ≠ ofVector e he}
  -- The first retyping retains the literal same pair and only locates its puncture certificate.
  let d : A ≃ₜ X × {P : Q // P ≠ ofVector e he} :=
    { toFun := fun z ↦ (z.val.1, ⟨z.val.2, z.property⟩)
      invFun := fun z ↦ ⟨(z.1, z.2.val), z.2.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      continuous_invFun :=
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _ }
  exact d.toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl X).prodCongr (puncturedHomotopyEquiv e he))

/-- The inverse keeps the original base projection and is the actual projective inclusion.
This grouped certificate records the two squares used by the lower-summand comparison. -/
theorem puncturedProdHomotopyEquiv_symm_properties :
    let K := (Submodule.span ℂ {e})ᗮ
    let A : Set (X × HermitianProjectiveSpace V InnerProductSpace.toCore) :=
      {z | z.2 ≠ ofVector e he}
    let s := (puncturedProdHomotopyEquiv X e he).invFun
    (ContinuousMap.subtypeVal A).comp s =
        (ContinuousMap.id X).prodMap (linearImageMap K.subtypeL Subtype.val_injective) ∧
      (ContinuousMap.fst.comp (ContinuousMap.subtypeVal A)).comp s = ContinuousMap.fst := by
  constructor <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same inverse pulls the restricted tautological class back to its actual lower root. -/
theorem tautologicalChernRoot_pullback_puncturedProdHomotopyEquiv_symm :
    let A : Set (X × HermitianProjectiveSpace V InnerProductSpace.toCore) :=
      {z | z.2 ≠ ofVector e he}
    let s := (puncturedProdHomotopyEquiv X e he).invFun
    singularCohomologyPullback ℤ s 2
        (singularCohomologyPullback ℤ (ContinuousMap.snd.comp (ContinuousMap.subtypeVal A)) 2
          (tautologicalChernRoot V)) =
      singularCohomologyPullback ℤ ContinuousMap.snd 2
        (tautologicalChernRoot (Submodule.span ℂ {e})ᗮ) := by
  let K := (Submodule.span ℂ {e})ᗮ
  let A : Set (X × HermitianProjectiveSpace V InnerProductSpace.toCore) :=
    {z | z.2 ≠ ofVector e he}
  let s := (puncturedProdHomotopyEquiv X e he).invFun
  let i := linearImageMap K.subtypeL Subtype.val_injective
  have hsquare : (ContinuousMap.snd.comp (ContinuousMap.subtypeVal A)).comp s =
      i.comp ContinuousMap.snd := by
    apply ContinuousMap.ext
    intro z
    exact congrArg Prod.snd
      (congrArg (fun f ↦ f z) (puncturedProdHomotopyEquiv_symm_properties X e he).1)
  have hcomp {Y Z W : Type u} [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
      (f : C(Y, Z)) (g : C(Z, W)) (a : singularCohomology ℤ W 2) :
      singularCohomologyPullback ℤ f 2 (singularCohomologyPullback ℤ g 2 a) =
        singularCohomologyPullback ℤ (g.comp f) 2 a :=
    congrArg (fun F ↦ F a)
      ((singularCohomologyFunctor ℤ 2).map_comp (TopCat.ofHom g).op (TopCat.ofHom f).op).symm
  -- The geometric square uses the same inclusion that identifies the actual tautological lines.
  calc
    _ = singularCohomologyPullback ℤ
        ((ContinuousMap.snd.comp (ContinuousMap.subtypeVal A)).comp s) 2
          (tautologicalChernRoot V) :=
      hcomp s (ContinuousMap.snd.comp (ContinuousMap.subtypeVal A)) _
    _ = singularCohomologyPullback ℤ (i.comp ContinuousMap.snd) 2
        (tautologicalChernRoot V) := by rw [hsquare]
    _ = singularCohomologyPullback ℤ ContinuousMap.snd 2
        (singularCohomologyPullback ℤ i 2 (tautologicalChernRoot V)) :=
      (hcomp ContinuousMap.snd i _).symm
    _ = singularCohomologyPullback ℤ ContinuousMap.snd 2 (tautologicalChernRoot K) :=
      congrArg (singularCohomologyPullback ℤ ContinuousMap.snd 2)
        (tautologicalChernRoot_pullback_subspace K)

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
