/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularIntegralEvaluation
public import AtiyahSinger.Topology.RelativeSingularChainCoordinates
public import AtiyahSinger.Topology.SingularHomologyEvaluation

/-!
# Kronecker evaluation for a projective complex exact below the degree

Public module ID: M2151.

Over an arbitrary commutative ring, lower exactness of a nonnegative
projective chain complex splits its lower boundary sequences inductively.
Those splittings give precisely the two extension properties needed by the
actual Kronecker map. This replaces the PID hypothesis by lower exactness;
vanishing only in the adjacent degree would not suffice over a general ring.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Kronecker evaluation is bijective for a projective complex exact in every lower degree. -/
theorem singularCochainHomologyEvaluation_bijective_of_exact_below (R : Type) [CommRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) [∀ i, Module.Projective R (C.X i)]
    (n : ℕ) (hbelow : ∀ k < n, Subsingleton (C.homology k)) :
    Function.Bijective (singularCochainHomologyEvaluation R C n) := by
  -- Splitting a projective quotient gives an extension from the original submodule.
  have hext {V W : Type u} [AddCommGroup V] [Module R V]
      [AddCommGroup W] [Module R W] (P : Submodule R V)
      [Module.Projective R (V ⧸ P)] (f : P →ₗ[R] W) :
      ∃ g : V →ₗ[R] W, g.comp P.subtype = f := by
    obtain ⟨s, hs⟩ := P.mkQ.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr P.mkQ_surjective)
    let q : V →ₗ[R] V := LinearMap.id - s.comp P.mkQ
    have hq (z : V) : q z ∈ P := by
      apply (Submodule.Quotient.mk_eq_zero P).mp
      change P.mkQ (z - s (P.mkQ z)) = 0
      have hz := LinearMap.congr_fun hs (P.mkQ z)
      change P.mkQ (s (P.mkQ z)) = P.mkQ z at hz
      rw [map_sub, hz, sub_self]
    let p : V →ₗ[R] P := q.codRestrict P hq
    refine ⟨f.comp p, ?_⟩
    apply LinearMap.ext
    intro z
    change f (p z.val) = f z
    apply congrArg f
    apply Subtype.ext
    change z.val - s (P.mkQ z.val) = z.val
    have hz : P.mkQ z.val = 0 := (Submodule.Quotient.mk_eq_zero P).mpr z.property
    rw [hz, map_zero, sub_zero]
  -- Exactness below n makes each relevant boundary module a projective direct summand.
  have hrange_eq_ker (k : ℕ) (hk : k < n) :
      (C.d (k + 1) k).hom.range =
        (C.d k ((ComplexShape.down ℕ).next k)).hom.ker := by
    have hexact : (C.sc k).Exact := (C.exactAt_iff_isZero_homology k).mpr
      (ModuleCat.isZero_iff_subsingleton.mpr (hbelow k hk))
    apply le_antisymm
    · rintro z ⟨y, rfl⟩
      change C.d k ((ComplexShape.down ℕ).next k) (C.d (k + 1) k y) = 0
      exact congrArg (fun g : C.X (k + 1) ⟶
        C.X ((ComplexShape.down ℕ).next k) ↦ g y)
          (C.d_comp_d (k + 1) k ((ComplexShape.down ℕ).next k))
    · intro z hz
      have hy := (ShortComplex.moduleCat_exact_iff _).mp hexact z hz
      change ∃ x : C.X ((ComplexShape.down ℕ).prev k),
        C.d ((ComplexShape.down ℕ).prev k) k x = z at hy
      rw [ChainComplex.prev] at hy
      exact hy
  have hprojective (i : ℕ) (hi : i ≤ n) :
      Module.Projective R (C.d i ((ComplexShape.down ℕ).next i)).hom.range := by
    induction i with
    | zero =>
      rw [ChainComplex.next_nat_zero]
      have hd : (C.d 0 0).hom = 0 := by simp
      rw [hd, LinearMap.range_zero]
      exact Module.Projective.of_split (M := C.X 0) 0 0
        (LinearMap.ext fun z ↦ Subsingleton.elim _ _)
    | succ i ih =>
      have hp := ih (by omega)
      let d := (C.d i ((ComplexShape.down ℕ).next i)).hom
      let : Module.Projective R d.range := hp
      let : Module.Projective R (C.X i ⧸ d.ker) :=
        Module.Projective.of_equiv d.quotKerEquivRange.symm
      obtain ⟨g, hg⟩ := hext d.ker (LinearMap.id : d.ker →ₗ[R] d.ker)
      have hk : Module.Projective R d.ker :=
        Module.Projective.of_split d.ker.subtype g hg
      rw [ChainComplex.next_nat_succ, hrange_eq_ker i (by omega)]
      exact hk
  have hextKer (i : ℕ) (hi : i ≤ n)
      (f : (C.d i ((ComplexShape.down ℕ).next i)).hom.ker →ₗ[R]
        singularCoefficient R) :
      ∃ g : C.X i →ₗ[R] singularCoefficient R,
        g.comp (C.d i ((ComplexShape.down ℕ).next i)).hom.ker.subtype = f := by
    let d := (C.d i ((ComplexShape.down ℕ).next i)).hom
    let : Module.Projective R d.range := hprojective i hi
    let : Module.Projective R (C.X i ⧸ d.ker) :=
      Module.Projective.of_equiv d.quotKerEquivRange.symm
    exact hext d.ker f
  have hextRange
      (f : (C.d n ((ComplexShape.down ℕ).next n)).hom.range →ₗ[R]
        singularCoefficient R) :
      ∃ g : C.X ((ComplexShape.down ℕ).next n) →ₗ[R] singularCoefficient R,
        g.comp (C.d n ((ComplexShape.down ℕ).next n)).hom.range.subtype = f := by
    cases n with
    | zero =>
      revert f
      rw [ChainComplex.next_nat_zero]
      intro f
      have hd : (C.d 0 0).hom = 0 := by simp
      refine ⟨0, ?_⟩
      apply LinearMap.ext
      intro z
      have hz : z = 0 := by
        apply Subtype.ext
        obtain ⟨x, hx⟩ := z.property
        exact hx.symm.trans (LinearMap.congr_fun hd x)
      simp [hz]
    | succ k =>
      revert f
      rw [ChainComplex.next_nat_succ]
      intro f
      revert f
      rw [hrange_eq_ker k (by omega)]
      intro f
      exact hextKer k (by omega) f
  let S := C.sc n
  let D := (singularCochainDualFunctor R).obj (op C)
  let T := D.sc n
  have hrep {shape : ComplexShape ℕ} (A : HomologicalComplex (ModuleCat.{u} R) shape)
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
    have hzero (a : D.homology n) (ha : singularCochainHomologyEvaluation R C n a = 0) :
        a = 0 := by
      obtain ⟨φ, rfl⟩ := hrep D n a
      let d := (C.d n ((ComplexShape.down ℕ).next n)).hom
      have hker : d.ker ≤ (show C.X n ⟶ singularCoefficient R from φ.val).hom.ker := by
        intro z hz
        let c : S.moduleCatLeftHomologyData.K := ⟨z, hz⟩
        have hvalue := congrArg
          (fun f ↦ f (S.moduleCatHomologyIso.inv (S.moduleCatToCycles.range.mkQ c))) ha
        have heval := singularCochainHomologyEvaluation_cycleClass R C n φ c
        exact heval.symm.trans hvalue
      -- Extend the induced functional on the boundary image to obtain a cochain primitive.
      let f : d.range →ₗ[R] singularCoefficient R :=
        (d.ker.liftQ (show C.X n ⟶ singularCoefficient R from φ.val).hom hker).comp
          d.quotKerEquivRange.symm.toLinearMap
      obtain ⟨g, hg⟩ := hextRange f
      have hprimitive : C.d n ((ComplexShape.down ℕ).next n) ≫ ModuleCat.ofHom g = φ.val := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        have hvalue := LinearMap.congr_fun hg (d.rangeRestrict z)
        change g (d z) = (show C.X n ⟶ singularCoefficient R from φ.val) z
        calc
          g (d z) = f (d.rangeRestrict z) := hvalue
          _ = (show C.X n ⟶ singularCoefficient R from φ.val) z := congrArg
            (d.ker.liftQ (show C.X n ⟶ singularCoefficient R from φ.val).hom hker)
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
    let l : S.moduleCatLeftHomologyData.K →ₗ[R] singularCoefficient R :=
      (f.comp S.moduleCatHomologyIso.inv.hom).comp S.moduleCatToCycles.range.mkQ
    obtain ⟨g, hg⟩ := hextKer n le_rfl l
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
/-- A specified generator gives bijective cap evaluation when all lower homology vanishes. -/
theorem relativeSingularCapProduct_augmentation_bijective_of_exact_below
    (R : Type) [CommRing R]
    {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (z : relativeSingularHomology R A n)
    (hgen : Function.Bijective (fun a : R ↦ a • z))
    (hbelow : ∀ k < n, Subsingleton (relativeSingularHomology R A k)) :
    Function.Bijective (fun a : relativeSingularCohomology R A n ↦
      ((TopCat.of X).singularHomology₀ε (singularCoefficient R)
        (relativeSingularCapProduct R A n 0 a z)).down) := by
  -- Relative chains use the actual basis of simplices surviving the quotient.
  let C := relativeSingularChains R A
  let : ∀ i, Module.Free R (C.X i) := fun i ↦
    Module.Free.of_equiv (relativeSingularChainCoordinates R A i).symm
  have hdual := singularCochainHomologyEvaluation_bijective_of_exact_below R C n hbelow
  let e : R ≃ₗ[R] relativeSingularHomology R A n :=
    LinearEquiv.ofBijective ((LinearMap.id : R →ₗ[R] R).smulRight z) hgen
  have he : e 1 = z := one_smul R z
  constructor
  · -- Equality on the specified generator determines equality on every homology class.
    intro a b hab
    apply hdual.injective
    apply LinearMap.ext
    intro c
    obtain ⟨r, rfl⟩ := hgen.surjective c
    have hv : singularCochainHomologyEvaluation R C n a z =
        singularCochainHomologyEvaluation R C n b z := by
      apply ULift.ext
      exact (congrArg ULift.down
        (relativeSingularCapProduct_augmentation R A n a z)).symm.trans
        (hab.trans (congrArg ULift.down
          (relativeSingularCapProduct_augmentation R A n b z)))
    rw [map_smul, map_smul, hv]
  · -- Prescribe a value on this generator, then realize that functional by a cocycle.
    intro r
    let f : relativeSingularHomology R A n →ₗ[R] singularCoefficient R :=
      e.symm.toLinearMap.smulRight (ULift.up r)
    obtain ⟨a, ha⟩ := hdual.surjective f
    refine ⟨a, ?_⟩
    have hv := LinearMap.congr_fun ha z
    have hf : f z = ULift.up r := by rw [← he]; simp [f]
    exact (congrArg ULift.down (relativeSingularCapProduct_augmentation R A n a z)).trans
      (congrArg ULift.down (hv.trans hf))

end AtiyahSinger
