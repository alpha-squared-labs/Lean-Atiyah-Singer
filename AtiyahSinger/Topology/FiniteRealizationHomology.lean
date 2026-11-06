/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularHomology
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Finite realization sources for singular homology

Public module ID: M1855.

Every original singular homology class comes from the realization of a finite
subcomplex of the original singular simplicial set. The continuous map is
exactly the realization of the inclusion followed by the original adjunction
counit. The chain representative lifts to the finite subcomplex, and the
adjunction unit then gives a singular cycle on its realized space.

The triangle identity returns that cycle to the original chain exactly.
No simplicial-to-singular homology equivalence is required. This is the usual
finite-support and realization argument for singular homology, expressed in
the native simplicial chains, realization and singular-chain models.
Compactness and Hausdorffness of finite realizations are separate topological
results; no separation hypothesis on the original base is used here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum Simplicial

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every singular homology class lifts from a finite realization by the original counit map. -/
theorem exists_finiteRealization_singularHomology_preimage
    (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
    (n : ℕ) (c : singularHomology R X n) :
    ∃ (A : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) (_ : SSet.Finite A)
      (d : singularHomology R |(A : SSet)| n),
      singularHomologyMap R
        (((sSetTopAdj.homEquiv (A : SSet) (TopCat.of X)).symm A.ι).hom) n d = c := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  let C := singularChains R X
  let M : ModuleCat.{u} R := singularCoefficient R
  -- A finite sum of simplex generators lifts to the finite union of their subcomplexes.
  have hfinite (z : C.X n) :
      ∃ A : S.Subcomplex, SSet.Finite A ∧
        z ∈ ((SSet.chainComplexMap A.ι M).f n).hom.range := by
    let e : C.X n ≅ ModuleCat.of R (⨁ _σ : S.obj (op ⦋n⦌), M) :=
      ModuleCat.coprodIsoDirectSum (fun _σ : S.obj (op ⦋n⦌) ↦ M)
    have hall (d : ⨁ _σ : S.obj (op ⦋n⦌), M) :
        ∃ A : S.Subcomplex, SSet.Finite A ∧
          e.inv d ∈ ((SSet.chainComplexMap A.ι M).f n).hom.range := by
      induction d using DirectSum.induction_on with
      | zero =>
        refine ⟨⊥, SSet.finite_of_hasDimensionLT _ 0 (fun j hj ↦ ?_), ?_⟩
        · exact (Nat.not_lt_zero j hj).elim
        · rw [map_zero]
          exact Submodule.zero_mem _
      | of σ a =>
        let A := SSet.Subcomplex.ofSimplex σ
        let τ : A.obj (op ⦋n⦌) := ⟨σ, SSet.Subcomplex.mem_ofSimplex_obj σ⟩
        refine ⟨A, inferInstance, (A : SSet).ιChainComplex (R := M) τ a, ?_⟩
        have hgen : e.inv (DirectSum.of (fun _σ : S.obj (op ⦋n⦌) ↦ M) σ a) =
            S.ιChainComplex (R := M) σ a :=
          congrArg (fun f ↦ f a)
            (ModuleCat.lof_coprodIsoDirectSum_inv (fun _σ : S.obj (op ⦋n⦌) ↦ M) σ)
        rw [hgen]
        change ((A : SSet).ιChainComplex τ ≫ (SSet.chainComplexMap A.ι M).f n) a = _
        exact congrArg (fun f ↦ f a)
          (SSet.ι_chainComplexMap_f (X := (A : SSet)) (Y := S) (f := A.ι) (R := M) τ)
      | add a b ha hb =>
        obtain ⟨A, hA, x, hx⟩ := ha
        obtain ⟨B, hB, y, hy⟩ := hb
        let U : Bool → S.Subcomplex := fun t ↦ if t then A else B
        let W : S.Subcomplex := ⨆ t, U t
        have hW : SSet.Finite W := (SSet.finite_iSup_iff U).mpr (by
          intro t
          cases t
          · exact hB
          · exact hA)
        have hmono (A B : S.Subcomplex) (hAB : A ≤ B) :
            ((SSet.chainComplexMap A.ι M).f n).hom.range ≤
              ((SSet.chainComplexMap B.ι M).f n).hom.range := by
          let i := SSet.chainComplexMap (SSet.Subcomplex.homOfLE hAB) M
          have hi : i ≫ SSet.chainComplexMap B.ι M = SSet.chainComplexMap A.ι M := by
            simp only [i, SSet.chainComplexMap, ← Functor.map_comp,
              SSet.Subcomplex.homOfLE_ι]
          rintro v ⟨w, rfl⟩
          exact ⟨i.f n w, congrArg (fun f ↦ f.f n w) hi⟩
        refine ⟨W, hW, ?_⟩
        rw [map_add]
        exact Submodule.add_mem _
          (hmono A W (le_iSup U true) ⟨x, hx⟩)
          (hmono B W (le_iSup U false) ⟨y, hy⟩)
    obtain ⟨A, hA, hz⟩ := hall (e.hom z)
    have he : e.inv (e.hom z) = z := congrArg (fun f ↦ f z) e.hom_inv_id
    exact ⟨A, hA, he ▸ hz⟩
  -- Lift the original cycle, and use degreewise injectivity to retain its cycle condition.
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance c
  obtain ⟨A, hA, b, hb⟩ := hfinite (C.iCycles n z)
  let D := (A : SSet).chainComplex M
  let i : D ⟶ C := SSet.chainComplexMap A.ι M
  let j := (ComplexShape.down ℕ).next n
  have hinj : Function.Injective (i.f j) :=
    (ModuleCat.mono_iff_injective _).mp
      (inferInstanceAs (Mono ((SSet.chainComplexMap A.pair.hom M).f j)))
  have hcycle : D.d n j b = 0 := by
    apply hinj
    rw [map_zero]
    have hcomm := congrArg (fun f ↦ f b) (i.comm n j)
    have hzero := congrArg (fun f ↦ f z) (C.iCycles_d n j)
    exact hcomm.symm.trans ((congrArg (fun a ↦ C.d n j a) hb).trans hzero)
  let w : D.cycles n := (D.sc n).moduleCatCyclesIso.inv ⟨b, hcycle⟩
  have hw : D.iCycles n w = b :=
    congrArg (fun f ↦ f ⟨b, hcycle⟩) (D.sc n).moduleCatCyclesIso_inv_iCycles
  have hwz : HomologicalComplex.cyclesMap i n w = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    exact (congrArg (fun f ↦ f w) (HomologicalComplex.cyclesMap_i i n)).trans
      ((congrArg (fun a ↦ i.f n a) hw).trans hb)
  -- The unit gives singular chains on the finite realization. Its counit map returns them.
  let f : |(A : SSet)| ⟶ TopCat.of X :=
    (sSetTopAdj.homEquiv (A : SSet) (TopCat.of X)).symm A.ι
  let η := sSetTopAdj.unit.app (A : SSet)
  have hunit : η ≫ TopCat.toSSet.map f = A.ι :=
    (sSetTopAdj.homEquiv (A : SSet) (TopCat.of X)).apply_symm_apply A.ι
  let a : D ⟶ singularChains R |(A : SSet)| := SSet.chainComplexMap η M
  let g : singularChains R |(A : SSet)| ⟶ C := (singularChainsFunctor R).map f
  have hag : a ≫ g = i := by
    change ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj M).map η ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj M).map (TopCat.toSSet.map f) = _
    rw [← Functor.map_comp, hunit]
  -- Functoriality carries this same lifted cycle to the originally requested homology class.
  refine ⟨A, hA, HomologicalComplex.homologyMap a n (D.homologyπ n w), ?_⟩
  change (HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap g n)
    (D.homologyπ n w) = c
  rw [← HomologicalComplex.homologyMap_comp, hag]
  exact (congrArg (fun f ↦ f w) (HomologicalComplex.homologyπ_naturality i n)).trans
    ((congrArg (fun a ↦ C.homologyπ n a) hwz).trans hz)

end AtiyahSinger
