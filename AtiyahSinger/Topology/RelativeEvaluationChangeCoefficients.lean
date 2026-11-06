/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomologyChangeCoefficients
public import AtiyahSinger.Topology.SingularHomologyChangeCoefficients
public import AtiyahSinger.Topology.SingularHomologyEvaluation

/-!
# Coefficient change in the relative Kronecker pairing

Public module ID: M2078.

The original integral chain and cochain coefficient maps preserve their
evaluation pairing. Passing through the original homology quotients gives
the corresponding statement for integral classes and their images over an
arbitrary commutative ring.
This provides the normalization needed for fiber orientations over arbitrary coefficients;
it asserts no general rationalization isomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Changing both entries preserves the original relative Kronecker pairing. -/
theorem singularCochainHomologyEvaluation_changeCoefficients (R : Type) [CommRing R]
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (a : relativeSingularCohomology ℤ A n) (z : relativeSingularHomology ℤ A n) :
    (singularCochainHomologyEvaluation R (relativeSingularChains R A) n
      (relativeSingularCohomologyChangeCoefficients R A n a)
      (relativeSingularHomologyChangeCoefficients R A n z)).down =
        ((singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ A) n a z).down :
          R) := by
  -- The coefficient maps agree on the same original simplex, before taking quotients.
  let coefficient : singularCoefficient.{u} ℤ →ₛₗ[Int.castRingHom R]
      singularCoefficient.{u} R :=
    { toFun := fun a ↦ ULift.up (a.down : R)
      map_add' := by intros; apply ULift.ext; simp
      map_smul' := by intros; apply ULift.ext; simp }
  have hordinary (k : ℕ) (φ : (singularCochains ℤ X).X k)
      (c : (singularChains ℤ X).X k) :
      (show (singularChains R X).X k ⟶ singularCoefficient R from
          (singularCochainsChangeCoefficients R X).f k φ)
        ((singularChainsChangeCoefficients R X).f k c) =
          coefficient ((show (singularChains ℤ X).X k ⟶ singularCoefficient ℤ from φ) c) := by
    have heq : (singularChainsChangeCoefficients R X).f k ≫
        (ModuleCat.restrictScalars (Int.castRingHom R)).map
          (show (singularChains R X).X k ⟶ singularCoefficient R from
            (singularCochainsChangeCoefficients R X).f k φ) =
          (show (singularChains ℤ X).X k ⟶ singularCoefficient ℤ from φ) ≫
            ModuleCat.semilinearMapAddEquiv (Int.castRingHom R)
              (singularCoefficient ℤ) (singularCoefficient R) coefficient := by
      apply Sigma.hom_ext
      intro σ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      have hchain : (singularChainsChangeCoefficients R X).f k
          ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
            (R := singularCoefficient ℤ) σ t) =
          (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
            (R := singularCoefficient R) σ (ULift.up (t.down : R)) :=
        (existsUnique_singularChainsChangeCoefficients R X).exists.choose_spec k σ t.down
      change (show (singularChains R X).X k ⟶ singularCoefficient R from
        (singularCochainsChangeCoefficients R X).f k φ)
        ((singularChainsChangeCoefficients R X).f k
          ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
            (R := singularCoefficient ℤ) σ t)) = _
      rw [hchain]
      have hcochain := (existsUnique_singularCochainsChangeCoefficients R X).exists.choose_spec
        k φ σ
      let ιZ := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient ℤ) σ
      let ιQ := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R) σ
      let φQ : (singularChains R X).X k ⟶ singularCoefficient R :=
        (singularCochainsChangeCoefficients R X).f k φ
      let φZ : (singularChains ℤ X).X k ⟶ singularCoefficient ℤ := φ
      change φQ (ιQ (ULift.up 1)) = coefficient (φZ (ιZ (ULift.up 1))) at hcochain
      have htZ : ιZ t = t.down • ιZ (ULift.up 1) := by
        rw [← map_zsmul]
        apply congrArg ιZ
        apply ULift.ext
        simp
      have htQ : ιQ (ULift.up (t.down : R)) = (t.down : R) • ιQ (ULift.up 1) := by
        rw [← map_smul]
        apply congrArg ιQ
        apply ULift.ext
        simp
      change φQ (ιQ (ULift.up (t.down : R))) = coefficient (φZ (ιZ t))
      rw [htQ, map_smul, hcochain, htZ, map_zsmul, map_zsmul]
      exact Int.cast_smul_eq_zsmul R t.down (coefficient (φZ (ιZ (ULift.up 1))))
    exact congrArg (fun f ↦ f c) heq
  have hrelative (k : ℕ) (φ : (relativeSingularCochains ℤ A).X k)
      (c : (relativeSingularChains ℤ A).X k) :
      (show (relativeSingularChains R A).X k ⟶ singularCoefficient R from
          (relativeSingularCochainsChangeCoefficients R A).f k φ)
        ((relativeSingularChainsChangeCoefficients R A).f k c) =
          coefficient ((show (relativeSingularChains ℤ A).X k ⟶
            singularCoefficient ℤ from φ) c) := by
    obtain ⟨d, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((relativeSingularChainsProjection ℤ A).f k)).mp inferInstance c
    have hchain := congrArg (fun F ↦ F.f k d)
      (existsUnique_relativeSingularChainsChangeCoefficients R A).exists.choose_spec
    have hcochain := congrArg (fun F ↦ F.f k φ)
      (existsUnique_relativeSingularCochainsChangeCoefficients R A).exists.choose_spec
    change (show (relativeSingularChains R A).X k ⟶ singularCoefficient R from
      (relativeSingularCochainsChangeCoefficients R A).f k φ)
      ((relativeSingularChainsChangeCoefficients R A).f k
        ((relativeSingularChainsProjection ℤ A).f k d)) = _
    change (relativeSingularChainsChangeCoefficients R A).f k
      ((relativeSingularChainsProjection ℤ A).f k d) =
      (relativeSingularChainsProjection R A).f k
        ((singularChainsChangeCoefficients R X).f k d) at hchain
    rw [hchain]
    have hvalue := congrArg (fun f : (singularCochains R X).X k ↦
      (show (singularChains R X).X k ⟶ singularCoefficient R from f)
        ((singularChainsChangeCoefficients R X).f k d)) hcochain
    exact hvalue.trans (hordinary k
      (((singularCochainDualFunctor ℤ).map
        (relativeSingularChainsProjection ℤ A).op).f k φ) d)
  -- Use the canonical representative formula for each scalar-restriction comparison.
  have hrep (R : Type) [CommRing R] {shape : ComplexShape ℕ}
      (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  have hcycles (R S : Type) [CommRing R] [CommRing S] (ι : R →+* S)
      {shape : ComplexShape ℕ}
      (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (D : HomologicalComplex (ModuleCat.{u} S) shape)
      (F : C ⟶ (Functor.mapHomologicalComplex (ModuleCat.restrictScalars ι)
        shape).obj D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
  obtain ⟨φ, rfl⟩ := hrep ℤ (relativeSingularCochains ℤ A) n a
  obtain ⟨c, rfl⟩ := hrep ℤ (relativeSingularChains ℤ A) n z
  obtain ⟨φQ, hφQ⟩ := hcycles ℤ R (Int.castRingHom R)
    (relativeSingularCochains ℤ A) (relativeSingularCochains R A)
    (relativeSingularCochainsChangeCoefficients R A) n φ
  obtain ⟨cQ, hcQ⟩ := hcycles ℤ R (Int.castRingHom R)
    (relativeSingularChains ℤ A) (relativeSingularChains R A)
    (relativeSingularChainsChangeCoefficients R A) n c
  have hφ := homologyMap_restrictScalars_cocycleClass ℤ R (Int.castRingHom R) _ _
    (relativeSingularCochainsChangeCoefficients R A) n φ φQ hφQ.symm
  have hc := homologyMap_restrictScalars_cocycleClass ℤ R (Int.castRingHom R) _ _
    (relativeSingularChainsChangeCoefficients R A) n c cQ hcQ.symm
  change relativeSingularCohomologyChangeCoefficients R A n _ = _ at hφ
  change relativeSingularHomologyChangeCoefficients R A n _ = _ at hc
  rw [hφ, hc, singularCochainHomologyEvaluation_cycleClass,
    singularCochainHomologyEvaluation_cycleClass]
  change ((show (relativeSingularChains R A).X n ⟶
    singularCoefficient R from φQ.val) cQ.val).down = _
  rw [hφQ, hcQ]
  exact congrArg ULift.down (hrelative n φ.val c.val)

end AtiyahSinger
