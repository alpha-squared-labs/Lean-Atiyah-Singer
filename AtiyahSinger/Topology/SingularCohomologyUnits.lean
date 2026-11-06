/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyCup

/-!
# Pointwise units in degree-zero singular cohomology

Public module ID: M2139.

A degree-zero class that freely generates cohomology at every point acts
invertibly by cup product in every degree. The inverse is constructed on
the original zero-cocycles, whose values agree along every singular edge.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- In degree zero the original cohomology is canonically the module of actual cocycles. -/
def singularCohomologyZeroEquiv :
    singularCohomology R X 0 ≃ₗ[R] singularCocycles R X 0 :=
  ((singularCochains R X).isoHomologyπ₀.symm ≪≫
    ((singularCochains R X).sc 0).moduleCatCyclesIso).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse of the canonical degree-zero identification is the original cocycle class map. -/
theorem singularCohomologyZeroEquiv_symm_apply (a : singularCocycles R X 0) :
    (singularCohomologyZeroEquiv R X).symm a = singularCocycleClass R X 0 a := by
  exact congrArg (fun f ↦ f a)
    (((singularCochains R X).sc 0).moduleCatCyclesIso_inv_π)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original constant-one class freely generates degree-zero cohomology of a point. -/
theorem singularCohomologyOne_point_generator :
    Function.Bijective (fun r : R ↦ r • singularCohomologyOne R PUnit.{u + 1}) := by
  let P := PUnit.{u + 1}
  let e := singularCohomologyZeroEquiv R P
  let τ := ((TopCat.of P).toSSetObjEquiv (op ⦋0⦌)).symm
    (ContinuousMap.const _ PUnit.unit)
  have hclass (a : singularCocycles R P 0) : e (singularCocycleClass R P 0 a) = a := by
    rw [← singularCohomologyZeroEquiv_symm_apply]
    exact e.apply_symm_apply a
  have heval (r : R) :
      (singularCochainEquiv R P 0 (e (r • singularCohomologyOne R P)).val τ).down = r := by
    rw [map_smul, singularCohomologyOne, hclass]
    change (singularCochainEquiv R P 0 (r • singularCochainOne R P) τ).down = r
    rw [map_smul]
    change (r • singularCochainEquiv R P 0 (singularCochainOne R P) τ).down = r
    simp only [singularCochainOne, LinearEquiv.apply_symm_apply]
    change r * 1 = r
    exact mul_one r
  constructor
  · intro r s hrs
    have h := congrArg (fun a ↦ (singularCochainEquiv R P 0 (e a).val τ).down) hrs
    exact (heval r).symm.trans (h.trans (heval s))
  · intro a
    let r := (singularCochainEquiv R P 0 (e a).val τ).down
    refine ⟨r, ?_⟩
    apply e.injective
    apply Subtype.ext
    apply (singularCochainEquiv R P 0).injective
    funext σ
    have hστ : σ = τ := by
      apply ULift.ext
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      exact Subsingleton.elim _ _
    subst σ
    rw [map_smul, singularCohomologyOne, hclass]
    change singularCochainEquiv R P 0 (r • singularCochainOne R P) τ = _
    rw [map_smul]
    change r • singularCochainEquiv R P 0 (singularCochainOne R P) τ = _
    simp only [singularCochainOne, LinearEquiv.apply_symm_apply]
    apply ULift.ext
    change r * 1 = r
    exact mul_one r

/-- A degree-zero class generating cohomology at every point acts invertibly by right cup
product on the original singular cohomology in every degree. -/
theorem singularCohomologyCup_bijective_of_pointwise_generator
    (c : singularCohomology R X 0)
    (h : ∀ x : X, Function.Bijective (fun r : R ↦ r •
      singularCohomologyPullback R (ContinuousMap.const PUnit.{u + 1} x) 0 c)) :
    ∀ p, Function.Bijective (fun a : singularCohomology R X p ↦
      singularCohomologyCup R X p 0 a c) := by
  classical
  let A := TopCat.toSSet.obj (TopCat.of X)
  let e := singularCohomologyZeroEquiv R X
  let α := e c
  have hclass (Z : Type u) [TopologicalSpace Z] (a : singularCocycles R Z 0) :
      singularCohomologyZeroEquiv R Z (singularCocycleClass R Z 0 a) = a := by
    rw [← singularCohomologyZeroEquiv_symm_apply]
    exact (singularCohomologyZeroEquiv R Z).apply_symm_apply a
  -- The natural inclusion of H⁰ into actual zero-cochains identifies point evaluations.
  let J (Z : Type u) [TopologicalSpace Z] :
      singularCohomology R Z 0 ⟶ (singularCochains R Z).X 0 :=
    (singularCochains R Z).isoHomologyπ₀.inv ≫ (singularCochains R Z).iCycles 0
  have hJ (Z : Type u) [TopologicalSpace Z] (a : singularCohomology R Z 0) :
      J Z a = (singularCohomologyZeroEquiv R Z a).val :=
    (congrArg (fun f ↦ f ((singularCochains R Z).isoHomologyπ₀.inv a))
      ((singularCochains R Z).sc 0).moduleCatCyclesIso_hom_i).symm
  have hJmap {Z W : Type u} [TopologicalSpace Z] [TopologicalSpace W] (f : C(Z, W)) :
      singularCohomologyPullback R f 0 ≫ J Z =
        J W ≫ ((singularCochainsFunctor R).map (TopCat.ofHom f).op).f 0 := by
    change homologyMap ((singularCochainsFunctor R).map (TopCat.ofHom f).op) 0 ≫
        (singularCochains R Z).isoHomologyπ₀.inv ≫ (singularCochains R Z).iCycles 0 =
      ((singularCochains R W).isoHomologyπ₀.inv ≫ (singularCochains R W).iCycles 0) ≫
        ((singularCochainsFunctor R).map (TopCat.ofHom f).op).f 0
    rw [CochainComplex.isoHomologyπ₀_inv_naturality_assoc, cyclesMap_i]
    simp only [Category.assoc]
  have hunit (σ : A.obj (op ⦋0⦌)) :
      IsUnit (singularCochainEquiv R X 0 α.val σ).down := by
    let τ := ((TopCat.of PUnit.{u + 1}).toSSetObjEquiv (op ⦋0⦌)).symm
      (ContinuousMap.const _ PUnit.unit)
    let x : X := ((TopCat.of X).toSSetObjEquiv (op ⦋0⦌) σ)
      (Convexity.StdSimplex.single 0)
    let f := ContinuousMap.const PUnit.{u + 1} x
    let g := TopCat.toSSet.map (TopCat.ofHom f)
    have hg : g.app (op ⦋0⦌) τ = σ := by
      apply ULift.ext
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      change x = σ.down.hom z
      have hz : (ULift.up (Convexity.StdSimplex.single 0) :
          ULift.{u} (Convexity.StdSimplex ℝ (Fin 1))) = z := Subsingleton.elim _ _
      exact congrArg σ.down.hom hz
    let F := (singularCochainsFunctor R).map (TopCat.ofHom f).op
    have heval (b : (singularCochains R X).X 0) :
        singularCochainEquiv R PUnit.{u + 1} 0 (F.f 0 b) τ =
          singularCochainEquiv R X 0 b σ := by
      change (show (singularChains R X).X 0 ⟶ singularCoefficient R from b)
        (((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).ιChainComplex τ ≫
          (SSet.chainComplexMap g (singularCoefficient R)).f 0) (ULift.up 1)) = _
      rw [SSet.ι_chainComplexMap_f, hg]
      rfl
    obtain ⟨r, hr⟩ := (h x).surjective (singularCohomologyOne R PUnit.{u + 1})
    have hscalar := congrArg (fun a ↦
      singularCochainEquiv R PUnit.{u + 1} 0 (J PUnit.{u + 1} a) τ) hr
    have hnat := congrArg (fun t ↦ t c) (hJmap f)
    change J PUnit.{u + 1} (singularCohomologyPullback R f 0 c) = F.f 0 (J X c) at hnat
    rw [map_smul, hnat, map_smul] at hscalar
    change r • singularCochainEquiv R PUnit.{u + 1} 0 (F.f 0 (J X c)) τ = _ at hscalar
    rw [heval, hJ, hJ, singularCohomologyOne, hclass] at hscalar
    change r • singularCochainEquiv R X 0 α.val σ =
      singularCochainEquiv R PUnit.{u + 1} 0 (singularCochainOne R PUnit.{u + 1}) τ at hscalar
    rw [singularCochainOne, LinearEquiv.apply_symm_apply] at hscalar
    exact IsUnit.of_mul_eq_one_right r (congrArg ULift.down hscalar)
  -- Closed zero-cochains take equal values at the two endpoints of each singular edge.
  have hdiff (φ : (singularCochains R X).X 0) (σ : A.obj (op ⦋1⦌)) :
      singularCochainEquiv R X 1 ((singularCochains R X).d 0 1 φ) σ =
        singularCochainEquiv R X 0 φ (A.δ 0 σ) -
          singularCochainEquiv R X 0 φ (A.δ 1 σ) := by
    have hsum : singularCochainEquiv R X 1 ((singularCochains R X).d 0 1 φ) σ =
        ∑ i : Fin 2, (-1 : R) ^ i.val • singularCochainEquiv R X 0 φ (A.δ i σ) := by
      change (show (A.chainComplex (singularCoefficient R)).X 0 ⟶
          singularCoefficient R from φ)
        ((A.ιChainComplex σ ≫ (A.chainComplex (singularCoefficient R)).d 1 0)
          (ULift.up 1)) = _
      rw [SSet.ιChainComplex_d]
      simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
        LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
      apply Finset.sum_congr rfl
      intro i _
      change ((-1 : ℤ) ^ i.val) • singularCochainEquiv R X 0 φ (A.δ i σ) = _
      rw [← Int.cast_smul_eq_zsmul R]
      simp
    simpa [Fin.sum_univ_two, sub_eq_add_neg] using hsum
  let units (σ : A.obj (op ⦋0⦌)) : Rˣ := (hunit σ).unit
  have hu (σ : A.obj (op ⦋0⦌)) : (units σ : R) =
      (singularCochainEquiv R X 0 α.val σ).down := (hunit σ).unit_spec
  let ψ : (singularCochains R X).X 0 :=
    (singularCochainEquiv R X 0).symm fun σ ↦ ULift.up (↑((units σ)⁻¹) : R)
  have hψ (σ : A.obj (op ⦋0⦌)) : singularCochainEquiv R X 0 ψ σ =
      ULift.up (↑((units σ)⁻¹) : R) :=
    congrFun ((singularCochainEquiv R X 0).apply_symm_apply _) σ
  have hclosed : ((singularCochains R X).sc 0).g ψ = 0 := by
    change (singularCochains R X).d 0 ((ComplexShape.up ℕ).next 0) ψ = 0
    rw [CochainComplex.next]
    apply (singularCochainEquiv R X 1).injective
    funext σ
    change singularCochainEquiv R X 1 ((singularCochains R X).d 0 1 ψ) σ = 0
    rw [hdiff, hψ, hψ]
    have hα : (singularCochains R X).d 0 1 α.val = 0 := by
      have hα := α.property
      change (singularCochains R X).d 0 ((ComplexShape.up ℕ).next 0) α.val = 0 at hα
      rw [CochainComplex.next] at hα
      exact hα
    have hedge : singularCochainEquiv R X 0 α.val (A.δ 0 σ) =
        singularCochainEquiv R X 0 α.val (A.δ 1 σ) := by
      have hd := hdiff α.val σ
      rw [hα, map_zero] at hd
      exact sub_eq_zero.mp hd.symm
    have heq : units (A.δ 0 σ) = units (A.δ 1 σ) := by
      apply Units.ext
      rw [hu, hu, hedge]
    rw [heq, sub_self]
  let β : singularCocycles R X 0 := ⟨ψ, hclosed⟩
  let b := singularCocycleClass R X 0 β
  have hc : singularCocycleClass R X 0 α = c := by
    rw [← singularCohomologyZeroEquiv_symm_apply]
    exact e.symm_apply_apply c
  have hfront : singularCupFrontFace 0 0 = 𝟙 ⦋0⦌ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    rfl
  have hback : singularCupBackFace 0 0 = 𝟙 ⦋0⦌ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    apply Fin.ext
    change 0 + i.val = i.val
    exact Nat.zero_add i.val
  -- Multiplication of each unit by its reciprocal proves the inverse identity
  -- on actual zero-cocycles, hence on the already defined cohomology classes.
  have hinv : singularCohomologyCup R X 0 0 c b = singularCohomologyOne R X := by
    rw [← hc, singularCohomologyCup_cocycleClass]
    apply congrArg (singularCocycleClass R X 0)
    apply Subtype.ext
    apply (singularCochainEquiv R X 0).injective
    funext σ
    change singularCochainEquiv R X 0 (singularCochainCup R X 0 0 α.val ψ) σ = _
    change singularCochainEquiv R X 0 ((singularCochainEquiv R X 0).symm _) σ = _
    rw [LinearEquiv.apply_symm_apply, hfront, hback, op_id, CategoryTheory.Functor.map_id]
    change singularCochainEquiv R X 0 α.val σ * singularCochainEquiv R X 0 ψ σ =
      singularCochainEquiv R X 0 (singularCochainOne R X) σ
    rw [hψ]
    rw [singularCochainOne, LinearEquiv.apply_symm_apply]
    apply ULift.ext
    change (singularCochainEquiv R X 0 α.val σ).down * ↑((units σ)⁻¹) = 1
    rw [← hu]
    exact Units.mul_inv (units σ)
  have hinv' : singularCohomologyCup R X 0 0 b c = singularCohomologyOne R X := by
    have hcomm := singularCohomologyCup_comm R X 0 0 b c
    change singularCohomologyCup R X 0 0 b c =
      (-1 : R) ^ 0 • singularCohomologyCup R X 0 0 c b at hcomm
    rw [pow_zero, one_smul] at hcomm
    exact hcomm.trans hinv
  -- Associativity and the original unit law give both inverse cup maps in every degree.
  intro p
  have hassoc (a : singularCohomology R X p) (d f : singularCohomology R X 0) :
      singularCohomologyCup R X p 0 (singularCohomologyCup R X p 0 a d) f =
        singularCohomologyCup R X p 0 a (singularCohomologyCup R X 0 0 d f) := by
    have hA := singularCohomologyCup_assoc R X p 0 0 a d f
    rw [eqToIso_refl, Iso.refl_hom, ModuleCat.id_apply] at hA
    simp only [Nat.add_zero] at hA
    exact hA
  have hleft (a : singularCohomology R X p) :
      singularCohomologyCup R X p 0 (singularCohomologyCup R X p 0 a c) b = a := by
    rw [hassoc, hinv, singularCohomologyCup_one]
  have hright (a : singularCohomology R X p) :
      singularCohomologyCup R X p 0 (singularCohomologyCup R X p 0 a b) c = a := by
    rw [hassoc, hinv', singularCohomologyCup_one]
  refine ⟨?_, fun a ↦ ⟨singularCohomologyCup R X p 0 a b, hright a⟩⟩
  intro a a' ha
  have heq := congrArg (fun z : singularCohomology R X p ↦
    singularCohomologyCup R X p 0 z b) ha
  exact (hleft a).symm.trans (heq.trans (hleft a'))

end AtiyahSinger
