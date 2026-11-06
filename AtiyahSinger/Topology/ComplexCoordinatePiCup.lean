/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexOrientationClass
public import AtiyahSinger.Topology.RelativeCohomologyFiniteCup
public import AtiyahSinger.Topology.RelativeProductThom
public import AtiyahSinger.Topology.SingularCohomologyUnits
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Ordered coordinate cups on a finite complex product

Public module ID: M1706.

The ordered relative cup of the coordinate generators freely generates local
cohomology at the origin. The induction separates the first coordinate and
uses the actual relative product Thom map on the remaining coordinates.
The argument includes the empty product and works over any commutative ring.

Source: the relative Thom product and the coordinate proof of the local top
class, Milnor--Stasheff, Characteristic Classes, Sections 9 and 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

private def complexCoordinateSplit (m : ℕ) :
    (Fin (m + 1) → ULift.{u} ℂ) ≃ₜ ULift.{u} ℂ × (Fin m → ULift.{u} ℂ) where
  toFun z := (z 0, fun i ↦ z i.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv z := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · rfl
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi fun i ↦ continuous_apply i.succ)
  continuous_invFun := continuous_pi fun i ↦ by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd

private def complexCoordinateRealEquiv (m : ℕ) :
    (Fin m → ULift.{u} ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) := by
  apply ContinuousLinearEquiv.ofFinrankEq
  rw [Module.finrank_pi_fintype]
  simp only [finrank_ulift, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, finrank_euclideanSpace_fin]
  exact Nat.mul_comm m 2

private theorem iUnion_piCoordinateNonzero (m : ℕ) :
    (⋃ i : Fin m, {v : Fin m → ULift.{u} ℂ | v i ≠ 0}) = {v | v ≠ 0} := by
  classical
  ext v
  constructor
  · intro hv hzero
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact hi (congrFun hzero i)
  · intro hv
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h (Set.mem_iUnion.mpr ⟨i, hi⟩)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual ordered coordinate product of a complex-plane generator is a local generator. -/
theorem relativeSingularCohomologyFiniteCup_pi_is_generator (R : Type) [CommRing R]
    (m : ℕ) (c : relativeSingularCohomology R {z : ULift.{u} ℂ | z ≠ 0} 2)
    (hc : Function.Bijective (fun a : R ↦ a • c)) :
    Function.Bijective (fun a : R ↦ a • relativeSingularCohomologyFiniteCup R m
      (fun i ↦ {v : Fin m → ULift.{u} ℂ | v i ≠ 0})
      (fun i ↦ isOpen_ne_fun (continuous_apply i) continuous_const)
      (fun i ↦ relativeSingularCohomologyPullback R
        (⟨fun v : Fin m → ULift.{u} ℂ ↦ v i, continuous_apply i⟩ :
          C(Fin m → ULift.{u} ℂ, ULift.{u} ℂ))
        (A := {v | v i ≠ 0}) (B := {z | z ≠ 0}) (fun _ hv ↦ hv) 2 c)) := by
  let W (n : ℕ) := Fin n → ULift.{u} ℂ
  let U (n : ℕ) (i : Fin n) : Set (W n) := {v | v i ≠ 0}
  let hU (n : ℕ) (i : Fin n) : IsOpen (U n i) :=
    isOpen_ne_fun (continuous_apply i) continuous_const
  let a (n : ℕ) (i : Fin n) : relativeSingularCohomology R (U n i) 2 :=
    relativeSingularCohomologyPullback R
      (⟨fun v : W n ↦ v i, continuous_apply i⟩ : C(W n, ULift.{u} ℂ))
      (A := U n i) (B := {z | z ≠ 0}) (fun _ hv ↦ hv) 2 c
  let τ (n : ℕ) := relativeSingularCohomologyFiniteCup R n (U n) (hU n) (a n)
  change Function.Bijective (fun r : R ↦ r • τ m)
  induction m with
  | zero =>
    -- The empty coordinate family is the original unit on the actual point pair.
    let f : C(W 0, PUnit.{u + 1}) := ContinuousMap.const _ PUnit.unit
    let g : C(PUnit.{u + 1}, W 0) := ContinuousMap.const _ 0
    have hgf : g.comp f = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro v
      exact Subsingleton.elim _ _
    have hfg : f.comp g = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro v
      exact Subsingleton.elim _ _
    have : IsIso (singularCohomologyPullback R f 0) :=
      isIso_singularCohomologyPullback_of_homotopyInverse R f g
        (by rw [hgf]) (by rw [hfg]) 0
    have hone := (ConcreteCategory.bijective_of_isIso
      (singularCohomologyPullback R f 0)).comp (singularCohomologyOne_point_generator R)
    have hone' : Function.Bijective (fun r : R ↦ r • singularCohomologyOne R (W 0)) := by
      have heq : (fun r : R ↦ singularCohomologyPullback R f 0
          (r • singularCohomologyOne R PUnit.{u + 1})) =
            (fun r : R ↦ r • singularCohomologyOne R (W 0)) := by
        funext r
        rw [map_smul, singularCohomologyPullback_one]
      exact (congrArg Function.Bijective heq).mp hone
    have hempty : (⋃ i, U 0 i) = ∅ := by simp
    have hto : IsIso (relativeSingularCohomologyToOrdinary R (⋃ i, U 0 i) 0) := by
      rw [hempty]
      exact isIso_relativeSingularCohomologyToOrdinary_empty R (W 0) 0
    let := hto
    have hunit : relativeSingularCohomologyToOrdinary R (⋃ i, U 0 i) 0 (τ 0) =
        singularCohomologyOne R (W 0) := by
      apply singularEvenCohomologyOf_injective R (W 0) 0
      rw [relativeSingularCohomologyFiniteCup_toOrdinary, singularEvenCohomologyOf_one]
      simp
    apply ((ConcreteCategory.bijective_of_isIso
      (relativeSingularCohomologyToOrdinary R (⋃ i, U 0 i) 0)).of_comp_iff' _).mp
    have heq : (fun r : R ↦ relativeSingularCohomologyToOrdinary R (⋃ i, U 0 i) 0
        (r • τ 0)) = (fun r : R ↦ r • singularCohomologyOne R (W 0)) := by
      funext r
      rw [map_smul, hunit]
    exact (congrArg Function.Bijective heq).mpr hone'
  | succ n ih =>
    -- Separate the first coordinate, retaining the original ordered cup factors.
    let Y := ULift.{u} ℂ × W n
    let f : C(Y, W (n + 1)) :=
      ⟨(complexCoordinateSplit n).symm, (complexCoordinateSplit n).symm.continuous⟩
    let g : C(W (n + 1), Y) :=
      ⟨complexCoordinateSplit n, (complexCoordinateSplit n).continuous⟩
    let V (i : Fin (n + 1)) : Set Y := {z | (f z) i ≠ 0}
    let hV (i : Fin (n + 1)) : IsOpen (V i) :=
      isOpen_ne_fun ((continuous_apply i).comp f.continuous) continuous_const
    let d (i : Fin (n + 1)) : relativeSingularCohomology R (V i) 2 :=
      relativeSingularCohomologyPullback R
        (⟨fun z : Y ↦ f z i, (continuous_apply i).comp f.continuous⟩ : C(Y, ULift.{u} ℂ))
        (A := V i) (B := {z | z ≠ 0}) (fun _ hz ↦ hz) 2 c
    have hf : Set.MapsTo f (⋃ i, V i) (⋃ i, U (n + 1) i) := by
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    have hg : Set.MapsTo g (⋃ i, U (n + 1) i) (⋃ i, V i) := by
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change ((complexCoordinateSplit n).symm (complexCoordinateSplit n z)) i ≠ 0
      rw [Homeomorph.symm_apply_apply]
      exact hi
    have hgf : g.comp f = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      exact (complexCoordinateSplit n).apply_symm_apply
    have hfg : f.comp g = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      exact (complexCoordinateSplit n).symm_apply_apply
    let J := relativeSingularCohomologyPullback R f hf (2 * (n + 1))
    have : IsIso J := isIso_relativeSingularCohomologyPullback_of_inverse
      R f g hf hg hgf hfg (2 * (n + 1))
    have hd (i : Fin (n + 1)) : relativeSingularCohomologyPullback R f
        (A := V i) (B := U (n + 1) i) (fun _ hz ↦ hz) 2 (a (n + 1) i) = d i := by
      dsimp only [a, d]
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      rfl
    have hnat : J (τ (n + 1)) =
        relativeSingularCohomologyFiniteCup R (n + 1) V hV d := by
      have h := relativeSingularCohomologyPullback_finiteCup R f (n + 1)
        V (U (n + 1)) hV (hU (n + 1)) (fun _ _ hz ↦ hz) (a (n + 1))
      simpa only [hd] using h
    -- The entire tail pair is its original punctured vector space, including n=0.
    have hproduct (T : Set (W n)) (hT : IsOpen T) (heq : T = {v | v ≠ 0})
        (D : Set Y) (hD : IsOpen D)
        (hDT : D = (ContinuousMap.snd : C(Y, W n)) ⁻¹' T)
        (hmap : Set.MapsTo (ContinuousMap.snd : C(Y, W n)) D T)
        (t : relativeSingularCohomology R T (2 * n))
        (ht : Function.Bijective (fun r : R ↦ r • t)) :
        Function.Bijective (fun x : relativeSingularCohomology R
            {z : ULift.{u} ℂ | z ≠ 0} 2 ↦
          relativeSingularCohomologyUnionCup R (V 0) D (hV 0) hD 2 (2 * n)
            (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(Y, ULift.{u} ℂ))
              (A := V 0) (B := {z | z ≠ 0}) (fun _ hz ↦ hz) 2 x)
            (relativeSingularCohomologyPullback R (ContinuousMap.snd : C(Y, W n))
              (A := D) (B := T) hmap (2 * n) t)) := by
      subst D
      subst T
      exact relativeSingularCohomologyUnionCup_prod_bijective R (ULift.{u} ℂ)
        (2 * n) (complexCoordinateRealEquiv n) {z | z ≠ 0}
        (isOpen_ne_fun continuous_id continuous_const) t ht 2
    let B : Set Y := ⋃ i : Fin n, V i.succ
    have htail : relativeSingularCohomologyPullback R (ContinuousMap.snd : C(Y, W n))
        (A := B) (B := ⋃ i, U n i) (fun z hz ↦ by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          exact Set.mem_iUnion.mpr ⟨i, hi⟩) (2 * n) (τ n) =
        relativeSingularCohomologyFiniteCup R n (fun i ↦ V i.succ)
          (fun i ↦ hV i.succ) (fun i ↦ d i.succ) := by
      have hd' (i : Fin n) : relativeSingularCohomologyPullback R
          (ContinuousMap.snd : C(Y, W n)) (A := V i.succ) (B := U n i)
          (fun _ hz ↦ hz) 2 (a n i) = d i.succ := by
        dsimp only [a, d]
        rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
        rfl
      have h := relativeSingularCohomologyPullback_finiteCup R
        (ContinuousMap.snd : C(Y, W n)) n (fun i ↦ V i.succ) (U n)
        (fun i ↦ hV i.succ) (hU n) (fun _ _ hz ↦ hz) (a n)
      simpa only [hd'] using h
    have hB : B = (ContinuousMap.snd : C(Y, W n)) ⁻¹' (⋃ i, U n i) := by
      ext z
      change z ∈ (⋃ i : Fin n, V i.succ) ↔ z.2 ∈ ⋃ i, U n i
      simp only [Set.mem_iUnion]
      rfl
    have hb := hproduct (⋃ i, U n i) (isOpen_iUnion (hU n))
      (iUnion_piCoordinateNonzero n) B (isOpen_iUnion fun i ↦ hV i.succ) hB
      (fun z hz ↦ by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
        exact Set.mem_iUnion.mpr ⟨i, hi⟩) (τ n) ih
    rw [htail] at hb
    let b := relativeSingularCohomologyUnionCup R (V 0) B (hV 0)
      (isOpen_iUnion fun i ↦ hV i.succ) 2 (2 * n) (d 0)
      (relativeSingularCohomologyFiniteCup R n (fun i ↦ V i.succ)
        (fun i ↦ hV i.succ) (fun i ↦ d i.succ))
    have hbgen : Function.Bijective (fun r : R ↦ r • b) := by
      have h := hb.comp hc
      have heq : (fun r : R ↦ relativeSingularCohomologyUnionCup R (V 0) B (hV 0)
          (isOpen_iUnion fun i ↦ hV i.succ) 2 (2 * n)
          (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(Y, ULift.{u} ℂ))
            (A := V 0) (B := {z | z ≠ 0}) (fun _ hz ↦ hz) 2 (r • c))
          (relativeSingularCohomologyFiniteCup R n (fun i ↦ V i.succ)
            (fun i ↦ hV i.succ) (fun i ↦ d i.succ))) = (fun r : R ↦ r • b) := by
        funext r
        rw [map_smul, map_smul, LinearMap.smul_apply]
        rfl
      exact (congrArg Function.Bijective heq).mp h
    -- Only canonical support and degree equalities remain in the finite-cup recursion.
    let D := eqToIso (congrArg (relativeSingularCohomology R (V 0 ∪ B))
      (show 2 + 2 * n = 2 * (n + 1) by omega))
    let K := eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (2 * (n + 1)))
      (Set.iUnion_fin_add_one_eq_iUnion_succ V).symm)
    have htrans := (ConcreteCategory.bijective_of_isIso K.hom).comp
      ((ConcreteCategory.bijective_of_isIso D.hom).comp hbgen)
    have htrans' : Function.Bijective (fun r : R ↦ r •
        relativeSingularCohomologyFiniteCup R (n + 1) V hV d) := by
      have heq : (fun r : R ↦ K.hom (D.hom (r • b))) =
          (fun r : R ↦ r • relativeSingularCohomologyFiniteCup R (n + 1) V hV d) := by
        funext r
        rw [map_smul, map_smul]
        rfl
      exact (congrArg Function.Bijective heq).mp htrans
    apply ((ConcreteCategory.bijective_of_isIso J).of_comp_iff' _).mp
    have heq : (fun r : R ↦ J (r • τ (n + 1))) =
        (fun r : R ↦ r • relativeSingularCohomologyFiniteCup R (n + 1) V hV d) := by
      funext r
      rw [map_smul, hnat]
    exact (congrArg Function.Bijective heq).mpr htrans'

end AtiyahSinger
