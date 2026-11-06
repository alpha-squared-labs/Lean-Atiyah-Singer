/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCupCochainMap
public import AtiyahSinger.Topology.SingularCechCochains

/-!
# Right cup on the original small cochains

Public module ID: M2158.

Restriction to small ordinary cochains is degreewise surjective. Right cup with
a fixed global relative cocycle, followed by restriction to small relative
cochains, vanishes on its kernel: every front face of a small simplex is still
small. It therefore descends as an actual cochain map. This construction uses
the original right-cup Leibniz theorem and requires no cochain-natural extension
of arbitrary small cochains.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- Ordinary small cochains are the actual algebraic dual of the small chain complex. -/
abbrev smallSingularCochains (𝒰 : Set (Set X)) : CochainComplex (ModuleCat.{u} R) ℕ :=
  (singularCochainDualFunctor R).obj (op (smallSingularChains R 𝒰))

/-- The original restriction of ordinary cochains to the same small simplex generators. -/
def smallSingularCochainsRestriction (𝒰 : Set (Set X)) :
    singularCochains R X ⟶ smallSingularCochains R 𝒰 :=
  (singularCochainDualFunctor R).map (smallSingularChainsInclusion R 𝒰).op

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to small cochains is surjective in every degree. -/
theorem epi_smallSingularCochainsRestriction_f (𝒰 : Set (Set X)) (q : ℕ) :
    Epi ((smallSingularCochainsRestriction R 𝒰).f q) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro c
  let s := (isSplitMono_smallSingularChainsInclusion R 𝒰 q).exists_splitMono.some
  refine ⟨s.retraction ≫ (show (smallSingularChains R 𝒰).X q ⟶
    singularCoefficient.{u} R from c), ?_⟩
  change (smallSingularChainsInclusion R 𝒰).f q ≫ s.retraction ≫ c = c
  rw [← Category.assoc, s.id, Category.id_comp]

/-- The ordinary-to-small restriction is an epimorphism of the actual cochain complexes. -/
theorem epi_smallSingularCochainsRestriction (𝒰 : Set (Set X)) :
    Epi (smallSingularCochainsRestriction R 𝒰) :=
  HomologicalComplex.epi_of_epi_f _ (epi_smallSingularCochainsRestriction_f R 𝒰)

/-- The original restriction to small cochains preserves cohomology for an open cover. -/
theorem isIso_homologyMap_smallSingularCochainsRestriction (𝒰 : Set (Set X))
    (hOpen : ∀ V ∈ 𝒰, IsOpen V) (hCover : ⋃₀ 𝒰 = Set.univ) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallSingularCochainsRestriction R 𝒰) q) :=
  isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R
    (smallSingularChainsInclusion R 𝒰)
    (homotopyEquivalences_smallSingularChainsInclusion R 𝒰 hOpen hCover) q

set_option backward.isDefEq.respectTransparency false in
private theorem smallRestriction_action_eq_zero (𝒰 : Set (Set X)) (A : Set X)
    (p r : ℕ) (a : (singularCochains R X).X p) (b : (relativeSingularCochains R A).X r)
    (ha : (smallSingularCochainsRestriction R 𝒰).f p a = 0) :
    (smallRelativeSingularCochainsRestriction R 𝒰 A).f (p + r)
      (relativeSingularCochainAction R A p r a b) = 0 := by
  apply simplicialRelativeCochain_ext R (smallSingularSubspaceSet 𝒰 A) (p + r)
  intro σ
  let S := TopCat.toSSet.obj (TopCat.of X)
  let P := smallSingularSet 𝒰
  let c := relativeSingularCochainAction R A p r a b
  have hp : cokernel.π (smallSingularSubspaceChains R 𝒰 A) ≫
      smallRelativeSingularChainsInclusion R 𝒰 A =
      smallSingularChainsInclusion R 𝒰 ≫ relativeSingularChainsProjection R A := by
    simp [smallRelativeSingularChainsInclusion, relativeSingularChainsProjection, cokernel.map]
  have hgen := congrArg (fun F ↦ F.f (p + r)
    (P.toSSet.ιChainComplex (R := singularCoefficient.{u} R) σ (ULift.up 1))) hp
  change _ = ((P.toSSet.ιChainComplex (R := singularCoefficient.{u} R) σ ≫
    (SSet.chainComplexMap P.ι (singularCoefficient.{u} R)).f (p + r)) ≫
      (relativeSingularChainsProjection R A).f (p + r)) (ULift.up 1) at hgen
  rw [SSet.ι_chainComplexMap_f] at hgen
  change (show (relativeSingularChains R A).X (p + r) ⟶ singularCoefficient.{u} R from c)
    ((smallRelativeSingularChainsInclusion R 𝒰 A).f (p + r) _) = 0
  erw [hgen]
  -- The quotient pullback of the actual relative action is its ordinary cup formula.
  have hact : (relativeSingularChainsProjection R A).f (p + r) ≫ c =
      singularCochainCup R X p r a (relativeSingularCochainEquiv R A r b).val := by
    exact congrArg Subtype.val ((relativeSingularCochainEquiv R A (p + r)).apply_symm_apply
      ⟨singularCochainCup R X p r a (relativeSingularCochainEquiv R A r b).val,
        singularCochainCup_mem_relative R A p r a b⟩)
  change ((relativeSingularChainsProjection R A).f (p + r) ≫ c)
    (S.ιChainComplex (R := singularCoefficient.{u} R) σ.val (ULift.up 1)) = 0
  rw [hact]
  change singularCochainEquiv R X (p + r)
    ((singularCochainEquiv R X (p + r)).symm _) σ.val = 0
  rw [LinearEquiv.apply_symm_apply]
  -- The front face remains in the same cover member, so the first factor vanishes.
  let τ := P.toSSet.map (singularCupFrontFace p r).op σ
  have hfront := congrArg (fun z ↦
    (show (smallSingularChains R 𝒰).X p ⟶ singularCoefficient.{u} R from z)
      (P.toSSet.ιChainComplex (R := singularCoefficient.{u} R) τ (ULift.up 1))) ha
  change ((P.toSSet.ιChainComplex (R := singularCoefficient.{u} R) τ ≫
    (SSet.chainComplexMap P.ι (singularCoefficient.{u} R)).f p) ≫ a) (ULift.up 1) = 0 at hfront
  rw [SSet.ι_chainComplexMap_f] at hfront
  change singularCochainEquiv R X p a
    (S.map (singularCupFrontFace p r).op σ.val) = 0 at hfront
  rw [hfront, zero_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Right cup with a fixed original cocycle descends to an actual map on small cochains. -/
@[no_expose]
def smallSingularCochainCupMap (𝒰 : Set (Set X)) (A : Set X) (r : ℕ)
    (U : relativeSingularCocycles R A r) :
    (smallSingularCochains R 𝒰).extend (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶
      smallRelativeSingularCochains R 𝒰 A := by
  let C := singularCochains R X
  let S := smallSingularCochains R 𝒰
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let s := HomologicalComplex.extendMap (smallSingularCochainsRestriction R 𝒰) e
  have hs : Epi s := by
    apply HomologicalComplex.epi_of_epi_f
    intro n
    by_cases hn : r ≤ n
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
      dsimp only [s]
      rw [HomologicalComplex.extendMap_f _ e (i := p) (i' := p + r) rfl]
      have := epi_smallSingularCochainsRestriction_f R 𝒰 p
      infer_instance
    · exact (S.isZero_extend_X e n (by
        intro p hp
        change p + r = n at hp
        omega)).epi _
  let g := relativeSingularCochainCupMap R A r U ≫
    smallRelativeSingularCochainsRestriction R 𝒰 A
  have hker : kernel.ι s ≫ g = 0 := by
    ext n x
    by_cases hn : r ≤ n
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
      let α := (C.extendXIso e (i := p) (i' := p + r) rfl).hom ((kernel.ι s).f (p + r) x)
      have he := congrArg (fun F ↦ F.f (p + r) x) (kernel.condition s)
      change s.f (p + r) ((kernel.ι s).f (p + r) x) = 0 at he
      have hα : (smallSingularCochainsRestriction R 𝒰).f p α = 0 := by
        have h := congrArg ((S.extendXIso e (i := p) (i' := p + r) rfl).hom) he
        dsimp only [s] at h
        rw [HomologicalComplex.extendMap_f _ e (i := p) (i' := p + r) rfl] at h
        change (S.extendXIso e (i := p) (i' := p + r) rfl).hom
          ((S.extendXIso e (i := p) (i' := p + r) rfl).inv
            ((smallSingularCochainsRestriction R 𝒰).f p α)) =
          (S.extendXIso e (i := p) (i' := p + r) rfl).hom 0 at h
        simpa only [Iso.inv_hom_id_apply, map_zero] using h
      change (smallRelativeSingularCochainsRestriction R 𝒰 A).f (p + r)
        ((relativeSingularCochainCupMap R A r U).f (p + r)
          ((kernel.ι s).f (p + r) x)) = 0
      rw [relativeSingularCochainCupMap_f]
      exact smallRestriction_action_eq_zero R 𝒰 A p r α U.val hα
    · have hzero : (relativeSingularCochainCupMap R A r U).f n = 0 :=
        (C.isZero_extend_X e n (by
          intro p hp
          change p + r = n at hp
          omega)).eq_of_src _ _
      change (smallRelativeSingularCochainsRestriction R 𝒰 A).f n
        ((relativeSingularCochainCupMap R A r U).f n ((kernel.ι s).f n x)) = 0
      rw [hzero]
      exact map_zero _
  exact Abelian.epiDesc s g hker

set_option backward.isDefEq.respectTransparency false in
/-- The small right-cup map is the factor of the original right-cup map under restriction. -/
theorem smallSingularCochainsRestriction_cupMap (𝒰 : Set (Set X)) (A : Set X) (r : ℕ)
    (U : relativeSingularCocycles R A r) :
    HomologicalComplex.extendMap (smallSingularCochainsRestriction R 𝒰)
      (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ smallSingularCochainCupMap R 𝒰 A r U =
      relativeSingularCochainCupMap R A r U ≫
        smallRelativeSingularCochainsRestriction R 𝒰 A := by
  simp only [smallSingularCochainCupMap, Abelian.comp_epiDesc]

private theorem isIso_dualCokernelProjection_of_notNonempty {S T : SSet.{u}} (i : S ⟶ T)
    (hS : ¬ S.Nonempty) :
    IsIso ((singularCochainDualFunctor R).map
      (cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))).op) := by
  let : S.HasDimensionLT 0 := (S.notNonempty_iff_hasDimensionLT_zero).mp hS
  have hz := S.isZero_chainComplex (singularCoefficient.{u} R)
  have hi : SSet.chainComplexMap i (singularCoefficient.{u} R) = 0 := hz.eq_of_src _ _
  have : IsIso (cokernel.π (SSet.chainComplexMap i (singularCoefficient.{u} R))) :=
    CokernelCofork.IsColimit.isIso_π (CokernelCofork.ofπ _ (cokernel.condition _))
      (cokernelIsCokernel _) hi
  infer_instance

/-- The canonical map from relative-empty small cochains to ordinary small cochains. -/
def smallRelativeSingularCochainsToOrdinaryEmpty (𝒰 : Set (Set X)) :
    smallRelativeSingularCochains R 𝒰 (∅ : Set X) ⟶ smallSingularCochains R 𝒰 :=
  (singularCochainDualFunctor R).map
    (cokernel.π (smallSingularSubspaceChains R 𝒰 (∅ : Set X))).op

/-- The empty relative condition changes none of the actual small cochains. -/
theorem isIso_smallRelativeSingularCochainsToOrdinaryEmpty (𝒰 : Set (Set X)) :
    IsIso (smallRelativeSingularCochainsToOrdinaryEmpty R 𝒰) := by
  apply isIso_dualCokernelProjection_of_notNonempty R
    (smallSingularSubspaceSet 𝒰 (∅ : Set X))
  rintro ⟨v⟩
  let f := (TopCat.of (∅ : Set X)).toSSetObjEquiv (op ⦋0⦌) v.val
  exact (f (Classical.arbitrary _)).property

/-- The canonical comparison of relative-empty and ordinary small cochain complexes. -/
def smallRelativeSingularCochainsEmptyIso (𝒰 : Set (Set X)) :
    smallRelativeSingularCochains R 𝒰 (∅ : Set X) ≅ smallSingularCochains R 𝒰 := by
  have := isIso_smallRelativeSingularCochainsToOrdinaryEmpty R 𝒰
  exact asIso (smallRelativeSingularCochainsToOrdinaryEmpty R 𝒰)

/-- The canonical map from relative-empty to ordinary original cochains is invertible. -/
theorem isIso_relativeSingularCochainsToOrdinary_empty (X : Type u) [TopologicalSpace X] :
    IsIso ((singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R (∅ : Set X)).op) := by
  apply isIso_dualCokernelProjection_of_notNonempty R
    (TopCat.toSSet.map (TopCat.ofHom
      (⟨Subtype.val, continuous_subtype_val⟩ : C((∅ : Set X), X))))
  rintro ⟨v⟩
  let f := (TopCat.of (∅ : Set X)).toSSetObjEquiv (op ⦋0⦌) v
  exact (f (Classical.arbitrary _)).property

set_option backward.isDefEq.respectTransparency false in
/-- The original and small empty-relative identifications commute with restriction. -/
theorem smallRelativeSingularCochainsRestriction_emptyIso (𝒰 : Set (Set X)) :
    smallRelativeSingularCochainsRestriction R 𝒰 (∅ : Set X) ≫
      (smallRelativeSingularCochainsEmptyIso R 𝒰).hom =
      (singularCochainDualFunctor R).map
        (relativeSingularChainsProjection R (∅ : Set X)).op ≫
          smallSingularCochainsRestriction R 𝒰 := by
  let D := singularCochainDualFunctor R
  change D.map (smallRelativeSingularChainsInclusion R 𝒰 (∅ : Set X)).op ≫
      D.map (cokernel.π (smallSingularSubspaceChains R 𝒰 (∅ : Set X))).op =
    D.map (relativeSingularChainsProjection R (∅ : Set X)).op ≫
      D.map (smallSingularChainsInclusion R 𝒰).op
  rw [← D.map_comp, ← D.map_comp, ← op_comp, ← op_comp]
  congr 1
  apply congrArg Quiver.Hom.op
  simp [smallRelativeSingularChainsInclusion, relativeSingularChainsProjection, cokernel.map]

/-- The original-to-small comparison with empty relative condition is an epimorphism. -/
theorem epi_smallRelativeSingularCochainsRestriction_empty (𝒰 : Set (Set X)) :
    Epi (smallRelativeSingularCochainsRestriction R 𝒰 (∅ : Set X)) := by
  have := isIso_relativeSingularCochainsToOrdinary_empty R X
  have := epi_smallSingularCochainsRestriction R 𝒰
  apply (epi_comp_iff_of_isIso _ (smallRelativeSingularCochainsEmptyIso R 𝒰).hom).mp
  rw [smallRelativeSingularCochainsRestriction_emptyIso]
  infer_instance

/-- The same small right-cup map with the relative-empty source used by the Čech family. -/
def smallRelativeSingularCochainCupMap (𝒰 : Set (Set X)) (A : Set X) (r : ℕ)
    (U : relativeSingularCocycles R A r) :
    (smallRelativeSingularCochains R 𝒰 (∅ : Set X)).extend
      (ComplexShape.embeddingUp'Add (1 : ℕ) r) ⟶ smallRelativeSingularCochains R 𝒰 A :=
  HomologicalComplex.extendMap (smallRelativeSingularCochainsEmptyIso R 𝒰).hom
    (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫ smallSingularCochainCupMap R 𝒰 A r U

set_option backward.isDefEq.respectTransparency false in
/-- The Čech-source version of small right cup restricts the original map through the
canonical empty-relative identification, on the same cover and relative subset. -/
theorem smallRelativeSingularCochainsRestriction_cupMap
    (𝒰 : Set (Set X)) (A : Set X) (r : ℕ) (U : relativeSingularCocycles R A r) :
    HomologicalComplex.extendMap (smallRelativeSingularCochainsRestriction R 𝒰 (∅ : Set X))
      (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
        smallRelativeSingularCochainCupMap R 𝒰 A r U =
      HomologicalComplex.extendMap ((singularCochainDualFunctor R).map
        (relativeSingularChainsProjection R (∅ : Set X)).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
          relativeSingularCochainCupMap R A r U ≫
            smallRelativeSingularCochainsRestriction R 𝒰 A := by
  rw [smallRelativeSingularCochainCupMap, ← Category.assoc, ← HomologicalComplex.extendMap_comp,
    smallRelativeSingularCochainsRestriction_emptyIso, HomologicalComplex.extendMap_comp,
    Category.assoc, smallSingularCochainsRestriction_cupMap]

end AtiyahSinger
