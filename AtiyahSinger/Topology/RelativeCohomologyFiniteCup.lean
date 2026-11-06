/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EvenCohomologyPolynomialEvaluation
public import AtiyahSinger.Topology.RelativeSingularFunctoriality
public import AtiyahSinger.Topology.RelativeCohomologyUnionCup
public import Mathlib.Data.Fintype.Pi

/-!
# Finite relative products of degree-two classes

Public module ID: M2063.

The ordered finite product uses the original relative union cup. Its support
is the intersection of the individual supports, represented by the union of
their open complements. Forgetting that relative condition gives the product
in the original even cohomology ring. The empty product uses the canonical
empty-pair comparison and the original unit.

Source: the finite relative cup construction in Hatcher, Algebraic Topology,
Section 3.2, applied to the localized Euler classes of coordinate sections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

attribute [local irreducible] singularCohomologyCup

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual ordered relative product over a finite family of open complements. -/
def relativeSingularCohomologyFiniteCup :
    (n : ℕ) → (U : Fin n → Set X) → (∀ i, IsOpen (U i)) →
      ((i : Fin n) → relativeSingularCohomology R (U i) 2) →
        relativeSingularCohomology R (⋃ i, U i) (2 * n)
  | 0, U, _, _ => by
    letI := isIso_relativeSingularCohomologyToOrdinary_empty R X 0
    exact (eqToIso (congrArg (fun A ↦ relativeSingularCohomology R A 0)
      (show (∅ : Set X) = ⋃ i, U i by simp))).hom
      ((asIso (relativeSingularCohomologyToOrdinary R (∅ : Set X) 0)).inv
        (singularCohomologyOne R X))
  | n + 1, U, hU, a => by
    let b : relativeSingularCohomology R (U 0 ∪ ⋃ i : Fin n, U i.succ) (2 + 2 * n) :=
      relativeSingularCohomologyUnionCup R (U 0) (⋃ i : Fin n, U i.succ)
        (hU 0) (isOpen_iUnion fun i ↦ hU i.succ) 2 (2 * n) (a 0)
        (relativeSingularCohomologyFiniteCup n (fun i ↦ U i.succ)
          (fun i ↦ hU i.succ) (fun i ↦ a i.succ))
    exact (eqToIso (congrArg (fun A ↦ relativeSingularCohomology R A (2 * (n + 1)))
      (Set.iUnion_fin_add_one_eq_iUnion_succ U).symm)).hom
      ((eqToIso (congrArg (relativeSingularCohomology R (U 0 ∪ ⋃ i : Fin n, U i.succ))
        (show 2 + 2 * n = 2 * (n + 1) by omega))).hom b)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Forgetting the original finite relative condition gives the same homogeneous cup product. -/
theorem relativeSingularCohomologyFiniteCup_toOrdinary (n : ℕ)
    (U : Fin n → Set X) (hU : ∀ i, IsOpen (U i))
    (a : (i : Fin n) → relativeSingularCohomology R (U i) 2) :
    singularEvenCohomologyOf R X n
        (relativeSingularCohomologyToOrdinary R (⋃ i, U i) (2 * n)
          (relativeSingularCohomologyFiniteCup R n U hU a)) =
      ∏ i, singularEvenCohomologyOf R X 1
        (relativeSingularCohomologyToOrdinary R (U i) 2 (a i)) := by
  classical
  have hset (A B : Set X) (h : A = B) (k : ℕ)
      (b : relativeSingularCohomology R A k) :
      relativeSingularCohomologyToOrdinary R B k
          ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S k) h)).hom b) =
        relativeSingularCohomologyToOrdinary R A k b := by
    subst B
    rfl
  have hdegree (A : Set X) (p q : ℕ) (h : p = q)
      (b : relativeSingularCohomology R A p) :
      relativeSingularCohomologyToOrdinary R A q
          ((eqToIso (congrArg (relativeSingularCohomology R A) h)).hom b) =
        (eqToIso (congrArg (singularCohomology R X) h)).hom
          (relativeSingularCohomologyToOrdinary R A p b) := by
    subst q
    rfl
  have hcup (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
      (α : relativeSingularCohomology R A p) (β : relativeSingularCohomology R B q) :
      relativeSingularCohomologyToOrdinary R (A ∪ B) (p + q)
          (relativeSingularCohomologyUnionCup R A B hA hB p q α β) =
        singularCohomologyCup R X p q
          (relativeSingularCohomologyToOrdinary R A p α)
          (relativeSingularCohomologyToOrdinary R B q β) := by
    -- The original restriction-to-right formula identifies the ordinary image.
    let c := relativeSingularCohomologyUnionCup R A B hA hB p q α β
    have hn := (relativeSingularCohomologyToOrdinaryNatTrans R X (p + q)).naturality
      (homOfLE (show B ⊆ A ∪ B from fun _ h ↦ Or.inr h)).op
    have hv := congrArg (fun f ↦ f c) hn
    change relativeSingularCohomologyToOrdinary R B (p + q)
        (relativeSingularCohomologyRestriction R B (A ∪ B)
          (fun _ h ↦ Or.inr h) (p + q) c) =
      relativeSingularCohomologyToOrdinary R (A ∪ B) (p + q) c at hv
    rw [← hv]
    dsimp only [c]
    rw [relativeSingularCohomologyUnionCup_restrict_right,
      relativeSingularCohomologyToOrdinary_action]
  induction n with
  | zero =>
    let := isIso_relativeSingularCohomologyToOrdinary_empty R X 0
    rw [relativeSingularCohomologyFiniteCup, hset _ _ (by simp)]
    have hc := Iso.inv_hom_id_apply
      (asIso (relativeSingularCohomologyToOrdinary R (∅ : Set X) 0))
      (singularCohomologyOne R X)
    change relativeSingularCohomologyToOrdinary R (∅ : Set X) (2 * 0)
      ((asIso (relativeSingularCohomologyToOrdinary R (∅ : Set X) 0)).inv
        (singularCohomologyOne R X)) = singularCohomologyOne R X at hc
    rw [hc, singularEvenCohomologyOf_one]
    simp
  | succ n ih =>
    -- Canonical degree transport identifies the two-factor cup with even multiplication.
    let b := relativeSingularCohomologyUnionCup R (U 0) (⋃ i : Fin n, U i.succ)
      (hU 0) (isOpen_iUnion fun i ↦ hU i.succ) 2 (2 * n) (a 0)
      (relativeSingularCohomologyFiniteCup R n (fun i ↦ U i.succ)
        (fun i ↦ hU i.succ) (fun i ↦ a i.succ))
    have hd := hdegree (U 0 ∪ ⋃ i : Fin n, U i.succ) (2 + 2 * n) (2 * (n + 1))
      (by omega) b
    have hs := hset (U 0 ∪ ⋃ i : Fin n, U i.succ) (⋃ i, U i)
      (Set.iUnion_fin_add_one_eq_iUnion_succ U).symm (2 * (n + 1))
      ((eqToIso (congrArg (relativeSingularCohomology R (U 0 ∪ ⋃ i : Fin n, U i.succ))
        (show 2 + 2 * n = 2 * (n + 1) by omega))).hom b)
    have ht : relativeSingularCohomologyToOrdinary R (⋃ i, U i) (2 * (n + 1))
        (relativeSingularCohomologyFiniteCup R (n + 1) U hU a) =
      (eqToIso (congrArg (singularCohomology R X)
        (show 2 + 2 * n = 2 * (n + 1) by omega))).hom
        (relativeSingularCohomologyToOrdinary R (U 0 ∪ ⋃ i : Fin n, U i.succ)
          (2 + 2 * n) b) := hs.trans hd
    rw [ht]
    dsimp only [b]
    rw [hcup]
    have hm (x : singularCohomology R X 2) (y : singularCohomology R X (2 * n)) :
        singularEvenCohomologyOf R X (n + 1)
            ((eqToIso (congrArg (singularCohomology R X)
              (show 2 + 2 * n = 2 * (n + 1) by omega))).hom
              (singularCohomologyCup R X 2 (2 * n) x y)) =
          singularEvenCohomologyOf R X 1 x * singularEvenCohomologyOf R X n y := by
      rw [← singularEvenCohomologyOf_cup]
      have he := singularEvenCohomologyOf_eqToIso R X (Nat.add_comm 1 n)
        (singularCohomologyEvenCup R X 1 n x y)
      have htransport {p q t : ℕ} (hpq : p = q) (hqt : q = t) (hpt : p = t)
          (z : singularCohomology R X p) :
          (eqToIso (congrArg (singularCohomology R X) hqt)).hom
              ((eqToIso (congrArg (singularCohomology R X) hpq)).hom z) =
            (eqToIso (congrArg (singularCohomology R X) hpt)).hom z := by
        subst q
        subst t
        rfl
      have ht := htransport (show 2 + 2 * n = 2 * (1 + n) by omega)
        (congrArg (fun j ↦ 2 * j) (Nat.add_comm 1 n))
        (show 2 + 2 * n = 2 * (n + 1) by omega)
        (singularCohomologyCup R X 2 (2 * n) x y)
      change (eqToIso (congrArg (fun j ↦ singularCohomology R X (2 * j))
        (Nat.add_comm 1 n))).hom (singularCohomologyEvenCup R X 1 n x y) = _ at ht
      exact (congrArg (singularEvenCohomologyOf R X (n + 1)) ht.symm).trans he
    rw [hm, ih, Fin.prod_univ_succ]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite relative product commutes with the same map of all its pairs. -/
theorem relativeSingularCohomologyPullback_finiteCup
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (U : Fin n → Set X) (V : Fin n → Set Y)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hf : ∀ i, Set.MapsTo f (U i) (V i))
    (a : (i : Fin n) → relativeSingularCohomology R (V i) 2) :
    relativeSingularCohomologyPullback R f
        (A := ⋃ i, U i) (B := ⋃ i, V i)
        (fun _ hx ↦ by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨i, hf i hi⟩) (2 * n)
        (relativeSingularCohomologyFiniteCup R n V hV a) =
      relativeSingularCohomologyFiniteCup R n U hU
        (fun i ↦ relativeSingularCohomologyPullback R f (hf i) 2 (a i)) := by
  have hset (A A' : Set X) (B B' : Set Y) (hA : A = A') (hB : B = B')
      (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B') (k : ℕ)
      (b : relativeSingularCohomology R B k) :
      relativeSingularCohomologyPullback R f hf' k
          ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S k) hB)).hom b) =
        (eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S k) hA)).hom
          (relativeSingularCohomologyPullback R f hf k b) := by
    subst A'
    subst B'
    rfl
  have hdegree (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B)
      (p q : ℕ) (h : p = q) (b : relativeSingularCohomology R B p) :
      relativeSingularCohomologyPullback R f hf q
          ((eqToIso (congrArg (relativeSingularCohomology R B) h)).hom b) =
        (eqToIso (congrArg (relativeSingularCohomology R A) h)).hom
          (relativeSingularCohomologyPullback R f hf p b) := by
    subst q
    rfl
  induction n with
  | zero =>
    -- For the empty family the original empty-pair map identifies both products with one.
    have hUX : (⋃ i, U i) = ∅ := by simp
    have hX : IsIso (relativeSingularCohomologyToOrdinary R (⋃ i, U i) 0) := by
      rw [hUX]
      exact isIso_relativeSingularCohomologyToOrdinary_empty R X 0
    let := hX
    apply (ConcreteCategory.bijective_of_isIso
      (relativeSingularCohomologyToOrdinary R (⋃ i, U i) 0)).injective
    apply singularEvenCohomologyOf_injective R X 0
    have hn := relativeSingularCohomologyPullback_toOrdinary R f
      (A := ⋃ i, U i) (B := ⋃ i, V i)
      (fun _ hx ↦ by obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx; exact Fin.elim0 i) 0
    have hv := congrArg (fun g ↦ g (relativeSingularCohomologyFiniteCup R 0 V hV a)) hn
    change relativeSingularCohomologyToOrdinary R (⋃ i, U i) 0
        (relativeSingularCohomologyPullback R f _ 0
          (relativeSingularCohomologyFiniteCup R 0 V hV a)) =
      singularCohomologyPullback R f 0
        (relativeSingularCohomologyToOrdinary R (⋃ i, V i) 0
          (relativeSingularCohomologyFiniteCup R 0 V hV a)) at hv
    rw [hv]
    have hvone : relativeSingularCohomologyToOrdinary R (⋃ i, V i) 0
        (relativeSingularCohomologyFiniteCup R 0 V hV a) = singularCohomologyOne R Y := by
      apply singularEvenCohomologyOf_injective R Y 0
      rw [relativeSingularCohomologyFiniteCup_toOrdinary, singularEvenCohomologyOf_one]
      simp
    rw [hvone, singularCohomologyPullback_one, singularEvenCohomologyOf_one,
      relativeSingularCohomologyFiniteCup_toOrdinary]
    simp
  | succ n ih =>
    -- Naturality of the same binary union cup is compatible with both canonical transports.
    let A := U 0 ∪ ⋃ i : Fin n, U i.succ
    let B := V 0 ∪ ⋃ i : Fin n, V i.succ
    have htail : Set.MapsTo f (⋃ i : Fin n, U i.succ) (⋃ i : Fin n, V i.succ) := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hf i.succ hi⟩
    have hab : Set.MapsTo f A B :=
      fun _ hx ↦ hx.elim (fun hx ↦ Or.inl (hf 0 hx)) (fun hx ↦ Or.inr (htail hx))
    have hall : Set.MapsTo f (⋃ i, U i) (⋃ i, V i) := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hf i hi⟩
    let b : relativeSingularCohomology R B (2 + 2 * n) :=
      relativeSingularCohomologyUnionCup R (V 0) (⋃ i : Fin n, V i.succ)
        (hV 0) (isOpen_iUnion fun i ↦ hV i.succ) 2 (2 * n) (a 0)
        (relativeSingularCohomologyFiniteCup R n (fun i ↦ V i.succ)
          (fun i ↦ hV i.succ) (fun i ↦ a i.succ))
    let b' : relativeSingularCohomology R A (2 + 2 * n) :=
      relativeSingularCohomologyUnionCup R (U 0) (⋃ i : Fin n, U i.succ)
        (hU 0) (isOpen_iUnion fun i ↦ hU i.succ) 2 (2 * n)
        (relativeSingularCohomologyPullback R f (hf 0) 2 (a 0))
        (relativeSingularCohomologyFiniteCup R n (fun i ↦ U i.succ)
          (fun i ↦ hU i.succ)
          (fun i ↦ relativeSingularCohomologyPullback R f (hf i.succ) 2 (a i.succ)))
    have hn : relativeSingularCohomologyPullback R f hab (2 + 2 * n) b = b' := by
      dsimp only [b, b']
      rw [relativeSingularCohomologyPullback_unionCup, ih]
      exact htail
    let jA := (eqToIso (congrArg (relativeSingularCohomology R A)
      (show 2 + 2 * n = 2 * (n + 1) by omega))).hom
    let jB := (eqToIso (congrArg (relativeSingularCohomology R B)
      (show 2 + 2 * n = 2 * (n + 1) by omega))).hom
    let kA := (eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (2 * (n + 1)))
      (Set.iUnion_fin_add_one_eq_iUnion_succ U).symm)).hom
    have hs := hset A (⋃ i, U i) B (⋃ i, V i)
      (Set.iUnion_fin_add_one_eq_iUnion_succ U).symm
      (Set.iUnion_fin_add_one_eq_iUnion_succ V).symm hab hall (2 * (n + 1)) (jB b)
    have hd := hdegree A B hab (2 + 2 * n) (2 * (n + 1)) (by omega) b
    exact hs.trans (congrArg kA (hd.trans (congrArg jA hn)))

end AtiyahSinger
