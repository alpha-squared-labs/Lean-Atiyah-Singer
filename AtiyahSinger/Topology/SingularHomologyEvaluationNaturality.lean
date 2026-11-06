/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularHomologyEvaluation

/-!
# Naturality of the original Kronecker evaluation

Public module ID: M2147.

The actual chain map and its actual cochain dual give the same evaluation.
The proof computes both maps on the canonical quotient classes and therefore
retains all categorical homology comparisons, coefficients and signs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pulling a cohomology class back and pushing a homology class forward give the same pairing. -/
theorem singularCochainHomologyEvaluation_naturality (R : Type) [CommRing R]
    (C D : ChainComplex (ModuleCat.{u} R) ℕ) (F : C ⟶ D) (n : ℕ)
    (a : ((singularCochainDualFunctor R).obj (op D)).homology n) (z : C.homology n) :
    singularCochainHomologyEvaluation R D n a (HomologicalComplex.homologyMap F n z) =
      singularCochainHomologyEvaluation R C n
        (HomologicalComplex.homologyMap ((singularCochainDualFunctor R).map F.op) n a) z := by
  have hrep {shape : ComplexShape ℕ} (A : HomologicalComplex (ModuleCat.{u} R) shape)
      (i : ℕ) (x : A.homology i) :
      ∃ c : (A.sc i).moduleCatLeftHomologyData.K,
        (A.sc i).moduleCatHomologyIso.inv ((A.sc i).moduleCatToCycles.range.mkQ c) = x := by
    obtain ⟨c, hc⟩ := (A.sc i).moduleCatToCycles.range.mkQ_surjective
      ((A.sc i).moduleCatHomologyIso.hom x)
    refine ⟨c, ?_⟩
    rw [hc]
    exact congrArg (fun f ↦ f x) (A.sc i).moduleCatHomologyIso.hom_inv_id
  -- The canonical homology comparisons preserve the specified cycle representatives.
  have hclass {shape : ComplexShape ℕ}
      (C D : HomologicalComplex (ModuleCat.{u} R) shape) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K)
      (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
      HomologicalComplex.homologyMap F n
          ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) shape n).map F
    let G := ShortComplex.leftHomologyMapData S
      (C.sc n).moduleCatLeftHomologyData (D.sc n).moduleCatLeftHomologyData
    have hcycles : G.φK a = b := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f a) G.commi).trans h
    have hquot := congrArg (fun f ↦ f a) G.commπ
    change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
      (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
    rw [hcycles] at hquot
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F n = _ at hmap
    rw [hmap]
    change (D.sc n).moduleCatHomologyIso.inv
      (G.φH ((C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)))) = _
    have hcancel : (C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
          (C.sc n).moduleCatToCycles.range.mkQ a :=
      congrArg (fun f ↦ f ((C.sc n).moduleCatToCycles.range.mkQ a))
        (C.sc n).moduleCatHomologyIso.inv_hom_id
    rw [hcancel, hquot]
  have hcycles {shape : ComplexShape ℕ}
      (C D : HomologicalComplex (ModuleCat.{u} R) shape) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
  let C' := (singularCochainDualFunctor R).obj (op C)
  let D' := (singularCochainDualFunctor R).obj (op D)
  let F' := (singularCochainDualFunctor R).map F.op
  obtain ⟨φ, rfl⟩ := hrep D' n a
  obtain ⟨c, rfl⟩ := hrep C n z
  obtain ⟨d, hd⟩ := hcycles C D F n c
  obtain ⟨ψ, hψ⟩ := hcycles D' C' F' n φ
  rw [hclass C D F n c d hd.symm, hclass D' C' F' n φ ψ hψ.symm,
    singularCochainHomologyEvaluation_cycleClass, singularCochainHomologyEvaluation_cycleClass]
  -- On chains, the dual map is literally precomposition by this same F.
  rw [hd, hψ]
  rfl

end AtiyahSinger
