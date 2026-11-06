/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SimplexLocalHomology
public import AtiyahSinger.Topology.RelativeCohomologySequence
public import AtiyahSinger.Topology.SingularCohomologyUnits
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant functions as actual singular zero-cocycles

Public module ID: M1949.

A locally constant coefficient function gives a cocycle in the original
singular cochain complex. Its class is natural under continuous maps.
This supplies the positive-half-line step class used in local suspension
normalization, while retaining the original cochain and cup conventions.

Source: the standard description of singular H⁰, Hatcher, Algebraic Topology,
Section 3.1. Local constancy is sufficient here; no assertion that every
zero-cocycle is locally constant on an arbitrary space is made.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A locally constant coefficient function evaluated on the original zero-simplices. -/
def locallyConstantSingularCocycle (f : LocallyConstant X R) : singularCocycles R X 0 := by
  let A := TopCat.toSSet.obj (TopCat.of X)
  let φ : (singularCochains R X).X 0 := (singularCochainEquiv R X 0).symm
    (fun σ ↦ ULift.up (f (σ.down.hom (ULift.up (Convexity.StdSimplex.single 0)))))
  refine ⟨φ, ?_⟩
  -- Along a singular edge the function is constant, so the two endpoint values cancel.
  change (singularCochains R X).d 0 ((ComplexShape.up ℕ).next 0) φ = 0
  rw [CochainComplex.next]
  apply (singularCochainEquiv R X 1).injective
  funext σ
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
  refine hsum.trans ?_
  have heq : singularCochainEquiv R X 0 φ (A.δ 0 σ) =
      singularCochainEquiv R X 0 φ (A.δ 1 σ) := by
    let : PathConnectedSpace (ULift.{u} (Convexity.StdSimplex ℝ (Fin 2))) :=
      Homeomorph.ulift.symm.pathConnectedSpace
    simp only [φ, LinearEquiv.apply_symm_apply]
    apply congrArg ULift.up
    have hσ : Continuous (fun z : ULift.{u} (Convexity.StdSimplex ℝ (Fin 2)) ↦
        σ.down.hom z) := σ.down.hom.continuous
    exact IsLocallyConstant.apply_eq_of_preconnectedSpace
      (f.isLocallyConstant.comp_continuous hσ) _ _
  calc
    _ = singularCochainEquiv R X 0 φ (A.δ 0 σ) -
        singularCochainEquiv R X 0 φ (A.δ 1 σ) := by
      simp [Fin.sum_univ_two, sub_eq_add_neg]
    _ = 0 := sub_eq_zero.mpr heq
    _ = _ := rfl

/-- The original singular cohomology class of a locally constant function. -/
def locallyConstantSingularCohomologyClass (f : LocallyConstant X R) :
    singularCohomology R X 0 :=
  singularCocycleClass R X 0 (locallyConstantSingularCocycle R X f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullback of a locally constant coefficient class is composition with the same map. -/
theorem locallyConstantSingularCohomologyClass_natural {Y : Type u} [TopologicalSpace Y]
    (f : C(Y, X)) (a : LocallyConstant X R) :
    singularCohomologyPullback R f 0 (locallyConstantSingularCohomologyClass R X a) =
      locallyConstantSingularCohomologyClass R Y (a.comap f) := by
  let F := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  apply homologyMap_cycleClass R (singularCochains R X) (singularCochains R Y) F 0
  apply (singularCochainEquiv R Y 0).injective
  funext σ
  change (show (singularChains R X).X 0 ⟶ singularCoefficient R from
      (locallyConstantSingularCocycle R X a).val)
    (((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex σ ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (singularCoefficient R)).f 0) (ULift.up 1)) = _
  rw [SSet.ι_chainComplexMap_f]
  change singularCochainEquiv R X 0
      ((singularCochainEquiv R X 0).symm _)
      ((TopCat.toSSet.map (TopCat.ofHom f)).app (op ⦋0⦌) σ) =
    singularCochainEquiv R Y 0 ((singularCochainEquiv R Y 0).symm _) σ
  simp only [LinearEquiv.apply_symm_apply]
  rfl

/-- A constant coefficient gives that scalar times the original unit class. -/
theorem locallyConstantSingularCohomologyClass_const (a : R) :
    locallyConstantSingularCohomologyClass R X (LocallyConstant.const X a) =
      a • singularCohomologyOne R X := by
  change singularCocycleClass R X 0 _ = a • singularCocycleClass R X 0 _
  rw [← map_smul]
  apply congrArg (singularCocycleClass R X 0)
  apply Subtype.ext
  apply (singularCochainEquiv R X 0).injective
  funext σ
  change singularCochainEquiv R X 0 ((singularCochainEquiv R X 0).symm _) σ =
    a • singularCochainEquiv R X 0 ((singularCochainEquiv R X 0).symm _) σ
  simp only [LinearEquiv.apply_symm_apply]
  apply ULift.ext
  exact (mul_one a).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A locally constant function vanishing on the subspace defines its relative H⁰ class. -/
def relativeLocallyConstantSingularCohomologyClass (A : Set X)
    (f : LocallyConstant X R) (hf : ∀ x ∈ A, f x = 0) :
    relativeSingularCohomology R A 0 := by
  have hvanish : singularCohomologyPullback R (ContinuousMap.subtypeVal A) 0
      (locallyConstantSingularCohomologyClass R X f) = 0 := by
    rw [locallyConstantSingularCohomologyClass_natural]
    have hzero : f.comap (ContinuousMap.subtypeVal A) = LocallyConstant.const A 0 := by
      ext x
      exact hf x.val x.property
    rw [hzero, locallyConstantSingularCohomologyClass_const, zero_smul]
  have hexists : ∃ a : relativeSingularCohomology R A 0,
      relativeSingularCohomologyToOrdinary R A 0 a =
        locallyConstantSingularCohomologyClass R X f :=
    (ShortComplex.moduleCat_exact_iff _).mp
      ((shortExact_singularSubspaceCochains R A).homology_exact₂ 0) _ hvanish
  exact hexists.choose

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Forgetting the relative condition recovers the same original zero-cohomology class. -/
theorem relativeLocallyConstantSingularCohomologyClass_toOrdinary (A : Set X)
    (f : LocallyConstant X R) (hf : ∀ x ∈ A, f x = 0) :
    relativeSingularCohomologyToOrdinary R A 0
        (relativeLocallyConstantSingularCohomologyClass R X A f hf) =
      locallyConstantSingularCohomologyClass R X f := by
  unfold relativeLocallyConstantSingularCohomologyClass
  dsimp only
  exact @Classical.choose_spec (relativeSingularCohomology R A 0)
    (fun a ↦ relativeSingularCohomologyToOrdinary R A 0 a =
      locallyConstantSingularCohomologyClass R X f) _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A locally constant relative class pulls back to the same function on the source pair. -/
theorem relativeLocallyConstantSingularCohomologyClass_natural
    {Y : Type u} [TopologicalSpace Y] (g : C(Y, X)) (A : Set X) (B : Set Y)
    (hg : Set.MapsTo g B A) (f : LocallyConstant X R) (hf : ∀ x ∈ A, f x = 0) :
    relativeSingularCohomologyPullback R g hg 0
        (relativeLocallyConstantSingularCohomologyClass R X A f hf) =
      relativeLocallyConstantSingularCohomologyClass R Y B (f.comap g)
        (fun x hx ↦ hf (g x) (hg hx)) := by
  -- The relative-to-ordinary map is injective at the initial degree.
  let S := singularSubspaceCochainsSequence R B
  have := (shortExact_singularSubspaceCochains R B).mono_f
  have hmono : Mono (homologyMap S.f 0) :=
    mono_homologyMap_of_mono_of_not_rel _ _ (by simp)
  apply (ModuleCat.mono_iff_injective (homologyMap S.f 0)).mp hmono
  change relativeSingularCohomologyToOrdinary R B 0
      (relativeSingularCohomologyPullback R g hg 0 _) =
    relativeSingularCohomologyToOrdinary R B 0 _
  have hnat := congrArg (fun h ↦ h
    (relativeLocallyConstantSingularCohomologyClass R X A f hf))
      (relativeSingularCohomologyPullback_toOrdinary R g hg 0)
  change relativeSingularCohomologyToOrdinary R B 0
      (relativeSingularCohomologyPullback R g hg 0 _) =
    singularCohomologyPullback R g 0 (relativeSingularCohomologyToOrdinary R A 0 _) at hnat
  rw [hnat, relativeLocallyConstantSingularCohomologyClass_toOrdinary,
    relativeLocallyConstantSingularCohomologyClass_toOrdinary,
    locallyConstantSingularCohomologyClass_natural]

end AtiyahSinger
