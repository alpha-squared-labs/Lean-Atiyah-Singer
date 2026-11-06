/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCapProduct
public import AtiyahSinger.Topology.RelativeSingularCohomologyVanishing
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Evaluation of the original dual cohomology on homology

Public module ID: M2146.

The Kronecker pairing evaluates an actual algebraic cocycle on an actual cycle,
then descends both original boundary quotients. Over a field this identifies dual
cohomology with the linear dual of homology. The construction retains the native
chain complex and the canonical categorical homology comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The Kronecker pairing of an actual dual cocycle with an actual homology class. -/
def singularCochainHomologyEvaluation (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    ((singularCochainDualFunctor R).obj (op C)).homology n →ₗ[R]
      C.homology n →ₗ[R] singularCoefficient R := by
  let S := C.sc n
  let D := (singularCochainDualFunctor R).obj (op C)
  let T := D.sc n
  let evaluation : T.moduleCatLeftHomologyData.K →ₗ[R]
      S.moduleCatLeftHomologyData.K →ₗ[R] singularCoefficient R :=
    { toFun := fun φ ↦
        { toFun := fun c ↦ (show C.X n ⟶ singularCoefficient R from φ.val) c.val
          map_add' := by intros; exact map_add _ _ _
          map_smul' := by intros; exact map_smul _ _ _ }
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  have hleft : T.moduleCatToCycles.range ≤ evaluation.ker := by
    rintro φ ⟨ψ, hψ⟩
    apply LinearMap.ext
    intro c
    have hval := congrArg Subtype.val hψ
    change C.d n ((ComplexShape.down ℕ).next n) ≫ ψ = φ.val at hval
    change (show C.X n ⟶ singularCoefficient R from φ.val) c.val = 0
    rw [← hval, ModuleCat.comp_apply]
    have hc : C.d n ((ComplexShape.down ℕ).next n) c.val = 0 := c.property
    rw [hc, map_zero]
  have hright : S.moduleCatToCycles.range ≤ evaluation.flip.ker := by
    rintro c ⟨b, hb⟩
    apply LinearMap.ext
    intro φ
    have hval := congrArg Subtype.val hb
    change C.d ((ComplexShape.down ℕ).prev n) n b = c.val at hval
    have hφ : C.d ((ComplexShape.down ℕ).prev n) n ≫ φ.val = 0 := φ.property
    change (show C.X n ⟶ singularCoefficient R from φ.val) c.val = 0
    rw [← hval]
    exact congrArg (fun f ↦ f b) hφ
  let descended := evaluation.liftQ₂ T.moduleCatToCycles.range S.moduleCatToCycles.range
    hleft hright
  exact (descended.compl₂ S.moduleCatHomologyIso.hom.hom).comp
    T.moduleCatHomologyIso.hom.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation on the canonical cycle representatives is literal cochain evaluation. -/
theorem singularCochainHomologyEvaluation_cycleClass
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (φ : (((singularCochainDualFunctor R).obj (op C)).sc n).moduleCatLeftHomologyData.K)
    (c : (C.sc n).moduleCatLeftHomologyData.K) :
    singularCochainHomologyEvaluation R C n
      ((((singularCochainDualFunctor R).obj (op C)).sc n).moduleCatHomologyIso.inv
        ((((singularCochainDualFunctor R).obj (op C)).sc n).moduleCatToCycles.range.mkQ φ))
      ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ c)) =
        (show C.X n ⟶ singularCoefficient R from φ.val) c.val := by
  let S := C.sc n
  let D := (singularCochainDualFunctor R).obj (op C)
  let T := D.sc n
  let evaluation : T.moduleCatLeftHomologyData.K →ₗ[R]
      S.moduleCatLeftHomologyData.K →ₗ[R] singularCoefficient R :=
    { toFun := fun φ ↦
        { toFun := fun c ↦ (show C.X n ⟶ singularCoefficient R from φ.val) c.val
          map_add' := by intros; exact map_add _ _ _
          map_smul' := by intros; exact map_smul _ _ _ }
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  have hleft : T.moduleCatToCycles.range ≤ evaluation.ker := by
    rintro φ ⟨ψ, hψ⟩
    apply LinearMap.ext
    intro c
    have hval := congrArg Subtype.val hψ
    change C.d n ((ComplexShape.down ℕ).next n) ≫ ψ = φ.val at hval
    change (show C.X n ⟶ singularCoefficient R from φ.val) c.val = 0
    rw [← hval, ModuleCat.comp_apply]
    have hc : C.d n ((ComplexShape.down ℕ).next n) c.val = 0 := c.property
    rw [hc, map_zero]
  have hright : S.moduleCatToCycles.range ≤ evaluation.flip.ker := by
    rintro c ⟨b, hb⟩
    apply LinearMap.ext
    intro φ
    have hval := congrArg Subtype.val hb
    change C.d ((ComplexShape.down ℕ).prev n) n b = c.val at hval
    have hφ : C.d ((ComplexShape.down ℕ).prev n) n ≫ φ.val = 0 := φ.property
    change (show C.X n ⟶ singularCoefficient R from φ.val) c.val = 0
    rw [← hval]
    exact congrArg (fun f ↦ f b) hφ
  let descended := evaluation.liftQ₂ T.moduleCatToCycles.range S.moduleCatToCycles.range
    hleft hright
  let I := T.moduleCatHomologyIso
  let J := S.moduleCatHomologyIso
  have hI : I.hom (I.inv (T.moduleCatToCycles.range.mkQ φ)) =
      T.moduleCatToCycles.range.mkQ φ :=
    congrArg (fun f ↦ f (T.moduleCatToCycles.range.mkQ φ)) I.inv_hom_id
  have hJ : J.hom (J.inv (S.moduleCatToCycles.range.mkQ c)) =
      S.moduleCatToCycles.range.mkQ c :=
    congrArg (fun f ↦ f (S.moduleCatToCycles.range.mkQ c)) J.inv_hom_id
  change descended (I.hom (I.inv _)) (J.hom (J.inv _)) = _
  exact congrArg₂ (fun a b ↦ descended a b) hI hJ

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Over a field, Kronecker evaluation identifies actual dual cohomology with dual homology. -/
theorem singularCochainHomologyEvaluation_bijective (K : Type) [Field K]
    (C : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) :
    Function.Bijective (singularCochainHomologyEvaluation K C n) := by
  let S := C.sc n
  let D := (singularCochainDualFunctor K).obj (op C)
  let T := D.sc n
  have hrep {shape : ComplexShape ℕ} (A : HomologicalComplex (ModuleCat.{u} K) shape)
      (i : ℕ) (a : A.homology i) :
      ∃ z : (A.sc i).moduleCatLeftHomologyData.K,
        (A.sc i).moduleCatHomologyIso.inv ((A.sc i).moduleCatToCycles.range.mkQ z) = a := by
    obtain ⟨z, hz⟩ := (A.sc i).moduleCatToCycles.range.mkQ_surjective
      ((A.sc i).moduleCatHomologyIso.hom a)
    refine ⟨z, ?_⟩
    rw [hz]
    exact congrArg (fun f ↦ f a) (A.sc i).moduleCatHomologyIso.hom_inv_id
  constructor
  · -- A cocycle evaluating to zero on homology vanishes on every cycle.
    have hzero (a : D.homology n) (ha : singularCochainHomologyEvaluation K C n a = 0) :
        a = 0 := by
      obtain ⟨φ, rfl⟩ := hrep D n a
      let d := (C.d n ((ComplexShape.down ℕ).next n)).hom
      have hker : d.ker ≤ (show C.X n ⟶ singularCoefficient K from φ.val).hom.ker := by
        intro z hz
        let c : S.moduleCatLeftHomologyData.K := ⟨z, hz⟩
        have hvalue := congrArg
          (fun f ↦ f (S.moduleCatHomologyIso.inv (S.moduleCatToCycles.range.mkQ c))) ha
        have heval := singularCochainHomologyEvaluation_cycleClass K C n φ c
        exact heval.symm.trans hvalue
      -- Extend the induced functional on the boundary image to obtain a cochain primitive.
      let f : d.range →ₗ[K] singularCoefficient K :=
        (d.ker.liftQ (show C.X n ⟶ singularCoefficient K from φ.val).hom hker).comp
          d.quotKerEquivRange.symm.toLinearMap
      obtain ⟨g, hg⟩ := f.exists_extend
      have hprimitive : C.d n ((ComplexShape.down ℕ).next n) ≫ ModuleCat.ofHom g = φ.val := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        have hvalue := LinearMap.congr_fun hg (d.rangeRestrict z)
        change g (d z) = (show C.X n ⟶ singularCoefficient K from φ.val) z
        calc
          g (d z) = f (d.rangeRestrict z) := hvalue
          _ = (show C.X n ⟶ singularCoefficient K from φ.val) z := congrArg
            (d.ker.liftQ (show C.X n ⟶ singularCoefficient K from φ.val).hom hker)
            (d.quotKerEquivRange_symm_apply_image z (by exact ⟨z, rfl⟩))
      have hboundary : φ ∈ T.moduleCatToCycles.range :=
        ⟨ModuleCat.ofHom g, Subtype.ext hprimitive⟩
      change T.moduleCatHomologyIso.inv (T.moduleCatToCycles.range.mkQ φ) = 0
      have hb0 : T.moduleCatToCycles.range.mkQ φ = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hboundary
      exact (congrArg T.moduleCatHomologyIso.inv hb0).trans (map_zero _)
    intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hab, sub_self]
  · -- Pull a homology functional back to cycles and extend it to all chains.
    intro f
    let l : S.moduleCatLeftHomologyData.K →ₗ[K] singularCoefficient K :=
      (f.comp S.moduleCatHomologyIso.inv.hom).comp S.moduleCatToCycles.range.mkQ
    obtain ⟨g, hg⟩ := l.exists_extend
    have hclosed : C.d ((ComplexShape.down ℕ).prev n) n ≫ ModuleCat.ofHom g = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro b
      have hvalue := LinearMap.congr_fun hg (S.moduleCatToCycles b)
      have hb : S.moduleCatToCycles.range.mkQ (S.moduleCatToCycles b) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩
      change g (C.d ((ComplexShape.down ℕ).prev n) n b) = 0
      refine hvalue.trans ?_
      change f (S.moduleCatHomologyIso.inv
        (S.moduleCatToCycles.range.mkQ (S.moduleCatToCycles b))) = 0
      rw [hb, map_zero, map_zero]
    let φ : T.moduleCatLeftHomologyData.K := ⟨ModuleCat.ofHom g, hclosed⟩
    refine ⟨T.moduleCatHomologyIso.inv (T.moduleCatToCycles.range.mkQ φ), ?_⟩
    apply LinearMap.ext
    intro a
    obtain ⟨c, rfl⟩ := hrep C n a
    rw [singularCochainHomologyEvaluation_cycleClass]
    exact LinearMap.congr_fun hg c

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Augmenting the actual top-degree relative cap is exactly the Kronecker evaluation. -/
theorem relativeSingularCapProduct_augmentation
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (a : relativeSingularCohomology R A n) (z : relativeSingularHomology R A n) :
    (TopCat.of X).singularHomology₀ε (singularCoefficient R)
        (relativeSingularCapProduct R A n 0 a z) =
      singularCochainHomologyEvaluation R (relativeSingularChains R A) n a z := by
  let C := singularChains R X
  let S := TopCat.toSSet.obj (TopCat.of X)
  let ε := (TopCat.of X).singularHomology₀ε (singularCoefficient R)
  let : IsIso (C.iCycles 0) := ChainComplex.isIso_iCycles₀ C
  let E : C.X 0 ⟶ singularCoefficient R := inv (C.iCycles 0) ≫ C.homologyπ 0 ≫ ε
  have hgen (σ : S.obj (op ⦋0⦌)) : S.ιChainComplex (R := singularCoefficient R) σ ≫ E =
      𝟙 (singularCoefficient R) := by
    have hlift : S.ιChainComplex (R := singularCoefficient R) σ ≫ inv (C.iCycles 0) =
        C.liftCycles (S.ιChainComplex (R := singularCoefficient R) σ) 0
          (by simp) (by simp) := by
      apply (cancel_mono (C.iCycles 0)).mp
      simp
    change (S.ιChainComplex (R := singularCoefficient R) σ ≫ inv (C.iCycles 0)) ≫
      C.homologyπ 0 ≫ ε = _
    rw [hlift]
    exact S.liftCycles_ιChainComplex_homologyπ_homology₀ε (singularCoefficient R) σ
  have hcap (φ : (singularCochains R X).X n) :
      ModuleCat.ofHom (singularCochainCap R X n 0 φ) ≫ E = φ := by
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have hr : r = r.down • (ULift.up (1 : R) : ULift.{u} R) := by
      apply ULift.ext
      simp
    have hone : E (singularCochainCap R X n 0 φ
        (S.ιChainComplex (R := singularCoefficient R) σ (ULift.up 1))) =
          (show C.X n ⟶ singularCoefficient R from φ)
            (S.ιChainComplex (R := singularCoefficient R) σ (ULift.up 1)) := by
      rw [singularCochainCap_simplex, map_smul]
      have hε := congrArg (fun f ↦ f (ULift.up (1 : R)))
        (hgen (S.map (singularCupBackFace n 0).op σ))
      change E (S.ιChainComplex (R := singularCoefficient R)
        (S.map (singularCupBackFace n 0).op σ) (ULift.up 1)) = ULift.up 1 at hε
      rw [hε]
      have hfront : singularCupFrontFace n 0 = 𝟙 ⦋n⦌ := by
        ext i
        rfl
      have hfrontValue : S.map (singularCupFrontFace n 0).op σ = σ := by
        rw [hfront]
        exact congrArg (fun f ↦ f σ) (S.map_id (op ⦋n⦌))
      calc
        _ = singularCochainEquiv R X n φ (S.map (singularCupFrontFace n 0).op σ) := by
          apply ULift.ext
          simp
          rfl
        _ = singularCochainEquiv R X n φ σ :=
          congrArg (singularCochainEquiv R X n φ) hfrontValue
    change E (singularCochainCap R X n 0 φ
      (S.ιChainComplex (R := singularCoefficient R) σ r)) =
        (show C.X n ⟶ singularCoefficient R from φ)
          (S.ιChainComplex (R := singularCoefficient R) σ r)
    rw [hr, map_smul, map_smul, map_smul, hone, map_smul]
  have hclass : ModuleCat.ofHom (singularCycleClass R X 0) ≫ ε =
      (C.sc 0).moduleCatLeftHomologyData.i ≫ E := by
    change (C.sc 0).moduleCatLeftHomologyData.π ≫ (C.sc 0).moduleCatHomologyIso.inv ≫ ε = _
    rw [← ShortComplex.moduleCatCyclesIso_inv_π_assoc]
    change (C.sc 0).moduleCatCyclesIso.inv ≫ C.homologyπ 0 ≫ ε =
      (C.sc 0).moduleCatLeftHomologyData.i ≫ inv (C.iCycles 0) ≫ C.homologyπ 0 ≫ ε
    have hi : (C.sc 0).moduleCatLeftHomologyData.i ≫ inv (C.iCycles 0) =
        (C.sc 0).moduleCatCyclesIso.inv := by
      apply (cancel_mono (C.iCycles 0)).mp
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact (C.sc 0).moduleCatCyclesIso_inv_iCycles.symm
    exact congrArg (fun f ↦ f ≫ C.homologyπ 0 ≫ ε) hi.symm
  have hrelative (φ : (relativeSingularCochains R A).X n)
      (c : (relativeSingularChains R A).X n) :
      E (relativeSingularCochainCap R A n 0 φ c) =
        (show (relativeSingularChains R A).X n ⟶ singularCoefficient R from φ) c := by
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((relativeSingularChainsProjection R A).f n)).mp inferInstance c
    exact (congrArg E (relativeSingularCochainCap_projection R A n 0 φ b)).trans
      (congrArg (fun f ↦ f b) (hcap (relativeSingularCochainEquiv R A n φ).val))
  have hrep {shape : ComplexShape ℕ} (B : HomologicalComplex (ModuleCat.{u} R) shape)
      (i : ℕ) (b : B.homology i) :
      ∃ c : (B.sc i).moduleCatLeftHomologyData.K,
        (B.sc i).moduleCatHomologyIso.inv ((B.sc i).moduleCatToCycles.range.mkQ c) = b := by
    obtain ⟨c, hc⟩ := (B.sc i).moduleCatToCycles.range.mkQ_surjective
      ((B.sc i).moduleCatHomologyIso.hom b)
    refine ⟨c, ?_⟩
    rw [hc]
    exact congrArg (fun f ↦ f b) (B.sc i).moduleCatHomologyIso.hom_inv_id
  -- Descend the chain identity through the same cycle classes on both sides.
  obtain ⟨φ, rfl⟩ := hrep (relativeSingularCochains R A) n a
  obtain ⟨c, rfl⟩ := hrep (relativeSingularChains R A) n z
  change ε (relativeSingularCapProduct R A n 0 (relativeSingularCocycleClass R A n φ)
    (relativeSingularCycleClass R A n c)) = _
  refine (congrArg ε (relativeSingularCapProduct_cycleClass R A n 0 φ c)).trans ?_
  refine ((congrArg (fun f ↦ f (relativeSingularCycleCap R A n 0 φ c)) hclass).trans
    (hrelative φ.val c.val)).trans ?_
  exact (singularCochainHomologyEvaluation_cycleClass R (relativeSingularChains R A) n φ c).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A chosen basis of one-dimensional relative homology normalizes the actual top cap map.
The basis is explicit input; no comparison with an integral orientation is assumed here. -/
theorem relativeSingularCapProduct_generator_bijective (K : Type) [Field K]
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (A : Set X) (n : ℕ)
    (e : K ≃ₗ[K] relativeSingularHomology K A n) :
    Function.Bijective (fun a : relativeSingularCohomology K A n ↦
      relativeSingularCapProduct K A n 0 a (e 1)) := by
  let ε : singularHomology K X 0 ⟶ singularCoefficient K :=
    (TopCat.of X).singularHomology₀ε (singularCoefficient K)
  have hε : Function.Bijective ε := (ConcreteCategory.isIso_iff_bijective ε).mp inferInstance
  have hdual := singularCochainHomologyEvaluation_bijective K (relativeSingularChains K A) n
  constructor
  · intro a b hab
    apply hdual.injective
    apply LinearMap.ext
    intro z
    -- Every relative class is a scalar multiple of this same specified generator.
    have hz : z = e.symm z • e 1 := by
      calc
        z = e (e.symm z) := (e.apply_symm_apply z).symm
        _ = e (e.symm z • (1 : K)) := by rw [smul_eq_mul, mul_one]
        _ = e.symm z • e 1 := e.map_smul _ _
    have hvalue : singularCochainHomologyEvaluation K (relativeSingularChains K A) n a (e 1) =
        singularCochainHomologyEvaluation K (relativeSingularChains K A) n b (e 1) :=
      (relativeSingularCapProduct_augmentation K A n a (e 1)).symm.trans
        ((congrArg ε hab).trans (relativeSingularCapProduct_augmentation K A n b (e 1)))
    rw [hz, map_smul, map_smul, hvalue]
  · intro z
    -- Prescribe the augmentation on the generator and extend it by its basis coordinate.
    let l : relativeSingularHomology K A n →ₗ[K] singularCoefficient K :=
      e.symm.toLinearMap.smulRight (ε z)
    obtain ⟨a, ha⟩ := hdual.surjective l
    refine ⟨a, hε.injective ?_⟩
    have hvalue := LinearMap.congr_fun ha (e 1)
    have hl : l (e 1) = ε z := by simp [l]
    exact (relativeSingularCapProduct_augmentation K A n a (e 1)).trans (hvalue.trans hl)

end AtiyahSinger
