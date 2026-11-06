/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexOrientationClass
public import AtiyahSinger.Topology.ComplexCoordinatePiCup
public import AtiyahSinger.Topology.LocalCohomologyGeneratorChange
public import AtiyahSinger.Topology.RelativeCohomologyFiniteCup

/-!
# The local class of the complex coordinate sections

Public module ID: M1705.

The ordered product of the original complex orientation classes, pulled back
by the conjugate linear coordinates of an orthonormal basis, is supported at
the origin. These are exactly the coordinates of the projected tautological
sections in the affine projective chart. The empty family retains the original
degree-zero unit.

Source: the local coordinate-section argument for projective Chern powers in
Milnor--Stasheff, Characteristic Classes, Sections 9 and 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

variable {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The nonzero coordinate sets cover exactly the complement of the origin. -/
theorem iUnion_complexCoordinateNonzero (m : ℕ) (b : OrthonormalBasis (Fin m) ℂ W) :
    (⋃ i, {v : W | inner ℂ v (b i) ≠ 0}) = {v : W | v ≠ 0} := by
  classical
  ext v
  constructor
  · intro hv hzero
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact hi (by rw [hzero, inner_zero_left])
  · intro hv
    by_contra h
    have hcoords (i : Fin m) : inner ℂ (b i) v = 0 := by
      have hi : inner ℂ v (b i) = 0 := by
        by_contra hi
        exact h (Set.mem_iUnion.mpr ⟨i, hi⟩)
      rw [← inner_conj_symm, hi, map_zero]
    apply hv
    rw [← b.sum_repr' v]
    simp only [hcoords, zero_smul, Finset.sum_const_zero]

/-- The ordered coordinate cup class with its actual point support and tautological sign. -/
def complexCoordinateCup (m : ℕ) (b : OrthonormalBasis (Fin m) ℂ W) :
    relativeSingularCohomology ℤ {v : W | v ≠ 0} (2 * m) := by
  let U (i : Fin m) : Set W := {v | inner ℂ v (b i) ≠ 0}
  let hU (i : Fin m) : IsOpen (U i) :=
    isOpen_ne_fun (continuous_id.inner continuous_const) continuous_const
  let g (i : Fin m) : C(W, ULift.{u} ℂ) :=
    ⟨fun v ↦ ULift.up (inner ℂ v (b i)),
      continuous_uliftUp.comp (continuous_id.inner continuous_const)⟩
  let a (i : Fin m) : relativeSingularCohomology ℤ (U i) 2 :=
    relativeSingularCohomologyPullback ℤ (g i)
      (A := U i) (B := {z | z ≠ 0})
      (fun _ hv hz ↦ hv (congrArg ULift.down hz)) 2 complexOrientationClass.{u}
  exact (eqToIso (congrArg (fun A ↦ relativeSingularCohomology ℤ A (2 * m))
    (iUnion_complexCoordinateNonzero m b))).hom
      (relativeSingularCohomologyFiniteCup ℤ m U hU a)

private def complexCoordinateHomeomorph (m : ℕ) (b : OrthonormalBasis (Fin m) ℂ W) :
    W ≃ₜ (Fin m → ULift.{u} ℂ) where
  toFun v i := ULift.up (inner ℂ v (b i))
  invFun z := b.repr.symm ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin m)).symm
    (fun i ↦ star (z i).down))
  left_inv v := by
    apply b.repr.injective
    ext i
    rw [LinearIsometryEquiv.apply_symm_apply, b.repr_apply_apply]
    change star (inner ℂ v (b i)) = inner ℂ (b i) v
    exact inner_conj_symm (b i) v
  right_inv z := by
    funext i
    apply ULift.ext
    change inner ℂ
      (b.repr.symm ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin m)).symm
        (fun j ↦ star (z j).down))) (b i) = (z i).down
    rw [← inner_conj_symm, ← b.repr_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
    exact star_star _
  continuous_toFun := continuous_pi fun _ ↦
    continuous_uliftUp.comp (continuous_id.inner continuous_const)
  continuous_invFun := b.repr.symm.continuous.comp
    ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin m)).symm.continuous.comp
      (continuous_pi fun i ↦ (continuous_uliftDown.comp (continuous_apply i)).star))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original conjugate-coordinate cup freely generates integral local cohomology. -/
theorem complexCoordinateCup_is_generator (m : ℕ) (b : OrthonormalBasis (Fin m) ℂ W) :
    Function.Bijective (fun a : ℤ ↦ a • complexCoordinateCup m b) := by
  let Z := Fin m → ULift.{u} ℂ
  let f : C(W, Z) :=
    ⟨complexCoordinateHomeomorph m b, (complexCoordinateHomeomorph m b).continuous⟩
  let g : C(Z, W) :=
    ⟨(complexCoordinateHomeomorph m b).symm, (complexCoordinateHomeomorph m b).symm.continuous⟩
  let U (i : Fin m) : Set W := {v | inner ℂ v (b i) ≠ 0}
  let V (i : Fin m) : Set Z := {z | z i ≠ 0}
  let hU (i : Fin m) : IsOpen (U i) :=
    isOpen_ne_fun (continuous_id.inner continuous_const) continuous_const
  let hV (i : Fin m) : IsOpen (V i) :=
    isOpen_ne_fun (continuous_apply i) continuous_const
  let a (i : Fin m) : relativeSingularCohomology ℤ (V i) 2 :=
    relativeSingularCohomologyPullback ℤ
      (⟨fun z : Z ↦ z i, continuous_apply i⟩ : C(Z, ULift.{u} ℂ))
      (A := V i) (B := {z | z ≠ 0}) (fun _ hz ↦ hz) 2 complexOrientationClass.{u}
  let d (i : Fin m) : relativeSingularCohomology ℤ (U i) 2 :=
    relativeSingularCohomologyPullback ℤ
      (⟨fun v : W ↦ ULift.up (inner ℂ v (b i)),
        continuous_uliftUp.comp (continuous_id.inner continuous_const)⟩ : C(W, ULift.{u} ℂ))
      (A := U i) (B := {z | z ≠ 0})
      (fun _ hv hz ↦ hv (congrArg ULift.down hz)) 2 complexOrientationClass.{u}
  have hfi (i : Fin m) : Set.MapsTo f (U i) (V i) :=
    fun _ hv hz ↦ hv (congrArg ULift.down hz)
  have hf : Set.MapsTo f (⋃ i, U i) (⋃ i, V i) := by
    intro v hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨i, hfi i hi⟩
  have hg : Set.MapsTo g (⋃ i, V i) (⋃ i, U i) := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    intro hzero
    apply hi
    have hfg : f (g z) = z := (complexCoordinateHomeomorph m b).apply_symm_apply z
    rw [← hfg]
    change ULift.up (inner ℂ (g z) (b i)) = 0
    rw [hzero]
    rfl
  have hgf : g.comp f = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    exact (complexCoordinateHomeomorph m b).symm_apply_apply
  have hfg : f.comp g = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    exact (complexCoordinateHomeomorph m b).apply_symm_apply
  let J := relativeSingularCohomologyPullback ℤ f hf (2 * m)
  have : IsIso J :=
    isIso_relativeSingularCohomologyPullback_of_inverse ℤ f g hf hg hgf hfg (2 * m)
  -- The same conjugate coordinates are the actual homeomorphism components.
  have hd (i : Fin m) : relativeSingularCohomologyPullback ℤ f (hfi i) 2 (a i) = d i := by
    dsimp only [a, d]
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    rfl
  have hnat : J (relativeSingularCohomologyFiniteCup ℤ m V hV a) =
      relativeSingularCohomologyFiniteCup ℤ m U hU d := by
    have h := relativeSingularCohomologyPullback_finiteCup ℤ f m U V hU hV hfi a
    simpa only [hd] using h
  let K := eqToIso (congrArg (fun S ↦ relativeSingularCohomology ℤ S (2 * m))
    (iUnion_complexCoordinateNonzero m b))
  have hgen : Function.Bijective (fun r : ℤ ↦ r •
      relativeSingularCohomologyFiniteCup ℤ m V hV a) := by
    have h := relativeSingularCohomologyFiniteCup_pi_is_generator ℤ m
      complexOrientationClass.{u} (by
        convert complexOrientationClass_is_generator.{u} using 1
        funext r
        exact int_smul_eq_zsmul
          (relativeSingularCohomology ℤ {z : ULift.{u} ℂ | z ≠ 0} 2).isModule
          r complexOrientationClass.{u})
    convert h using 1
    funext r
    exact (int_smul_eq_zsmul (relativeSingularCohomology ℤ (⋃ i, V i) (2 * m)).isModule
      r (relativeSingularCohomologyFiniteCup ℤ m V hV a)).symm
  have hcomp := (ConcreteCategory.bijective_of_isIso K.hom).comp
    ((ConcreteCategory.bijective_of_isIso J).comp hgen)
  -- The final support equality is precisely the one used in complexCoordinateCup.
  have heq : (fun r : ℤ ↦ K.hom (J
      (r • relativeSingularCohomologyFiniteCup ℤ m V hV a))) =
        (fun r : ℤ ↦ r • complexCoordinateCup m b) := by
    funext r
    rw [map_zsmul, map_zsmul, hnat]
    rfl
  exact (congrArg Function.Bijective heq).mp hcomp

/-- The same coordinate class remains a local generator over every commutative ring. -/
theorem complexCoordinateCup_changeCoefficients_is_generator (R : Type) [CommRing R]
    (m : ℕ) (b : OrthonormalBasis (Fin m) ℂ W) :
    Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyChangeCoefficients R {v : W | v ≠ 0} (2 * m)
        (complexCoordinateCup m b)) := by
  let : FiniteDimensional ℂ W := Module.Finite.of_basis b.toBasis
  have hdim : Module.finrank ℝ W = 2 * m := by
    rw [finrank_real_of_complex, b.repr.toLinearEquiv.finrank_eq,
      finrank_euclideanSpace_fin]
  exact relativeSingularCohomologyChangeCoefficients_is_generator R
    (Module.finBasisOfFinrankEq ℝ W hdim) (complexCoordinateCup m b)
    (complexCoordinateCup_is_generator m b)

end AtiyahSinger
