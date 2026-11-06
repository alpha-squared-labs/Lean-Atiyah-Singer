/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocalSuspensionOrientationNormalization
public import AtiyahSinger.Topology.LocalSuspensionRationalization
public import AtiyahSinger.Topology.LocalZeroCupEvaluation
public import AtiyahSinger.Topology.PositiveStepNaturality
public import AtiyahSinger.Topology.RationalLocalOrientationEvaluation
public import AtiyahSinger.Topology.RelativeCohomologyUnionCupAssociativity

/-!
# Local normalization of the two-relative cup product

Public module ID: M1943.

The two point-supported factors pair multiplicatively with the original
positive cycle in base-first coordinates. Induction in the base dimension
uses the positive first-coordinate step, the actual local suspension, and
associativity of three genuinely relative factors.

The private coordinate adapters write the total dimension as `r + n` so
that induction in `n` adds its first coordinate without a type transport.
They still list all `n` base coordinates first and all `r` fiber coordinates
afterwards. This arithmetic convention never permutes coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex

universe u

-- The restriction adapter keeps all point supports visible in the induction.
private def localCupRestricted {X : Type u} [TopologicalSpace X]
    (A B P : Set X) (hA : IsOpen A) (hB : IsOpen B) (hP : P ⊆ A ∪ B)
    (p q : ℕ) (a : relativeSingularCohomology ℚ A p)
    (b : relativeSingularCohomology ℚ B q) :
    relativeSingularCohomology ℚ P (p + q) :=
  relativeSingularCohomologyPullback ℚ (ContinuousMap.id X) hP (p + q)
    (relativeSingularCohomologyUnionCup ℚ A B hA hB p q a b)

private theorem localCupPullback_comp {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (k : ℕ)
    (a : relativeSingularCohomology ℚ C k) :
    relativeSingularCohomologyPullback ℚ f hf k
        (relativeSingularCohomologyPullback ℚ g hg k a) =
      relativeSingularCohomologyPullback ℚ (g.comp f) (hg.comp hf) k a :=
  (congrArg (fun h ↦ h a) (relativeSingularCohomologyPullback_comp ℚ f g hf hg k)).symm

private theorem localCupPullback_congr {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f g : C(X, Y)) (h : f = g)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (k : ℕ) :
    relativeSingularCohomologyPullback ℚ f hf k =
      relativeSingularCohomologyPullback ℚ g hg k := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem localCupRestricted_natural {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A B P : Set X) (A' B' P' : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
    (hP : P ⊆ A ∪ B) (hP' : P' ⊆ A' ∪ B')
    (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') (hfP : Set.MapsTo f P P')
    (p q : ℕ) (a : relativeSingularCohomology ℚ A' p)
    (b : relativeSingularCohomology ℚ B' q) :
    relativeSingularCohomologyPullback ℚ f hfP (p + q)
        (localCupRestricted A' B' P' hA' hB' hP' p q a b) =
      localCupRestricted A B P hA hB hP p q
        (relativeSingularCohomologyPullback ℚ f hfA p a)
        (relativeSingularCohomologyPullback ℚ f hfB q b) := by
  let hfU : Set.MapsTo f (A ∪ B) (A' ∪ B') :=
    fun _ h ↦ h.elim (fun h ↦ Or.inl (hfA h)) (fun h ↦ Or.inr (hfB h))
  let c := relativeSingularCohomologyUnionCup ℚ A' B' hA' hB' p q a b
  have hnat := relativeSingularCohomologyPullback_unionCup ℚ f
    hA hB hA' hB' hfA hfB p q a b
  have hleft := localCupPullback_comp f (ContinuousMap.id Y) hfP hP' (p + q) c
  have hright := localCupPullback_comp (ContinuousMap.id X) f hP hfU (p + q) c
  have hmap := localCupPullback_congr ((ContinuousMap.id Y).comp f)
    (f.comp (ContinuousMap.id X)) (by ext x; rfl) (fun _ h ↦ hP' (hfP h)) (fun _ h ↦ hfU (hP h))
      (p + q)
  exact hleft.trans ((congrArg (fun g ↦ g c) hmap).trans
    (hright.symm.trans (congrArg
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.id X) hP (p + q)) hnat)))

private theorem localCupRestricted_self {X : Type u} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hU : A ∪ B ⊆ A ∪ B)
    (p q : ℕ) (a : relativeSingularCohomology ℚ A p)
    (b : relativeSingularCohomology ℚ B q) :
    localCupRestricted A B (A ∪ B) hA hB hU p q a b =
      relativeSingularCohomologyUnionCup ℚ A B hA hB p q a b := by
  have hid : relativeSingularCohomologyPullback ℚ (ContinuousMap.id X) hU (p + q) =
      𝟙 _ := by
    change (relativeSingularCohomologyFunctor ℚ X (p + q)).map (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  exact congrArg (fun h ↦ h (relativeSingularCohomologyUnionCup ℚ A B hA hB p q a b)) hid

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem localCupRestricted_assoc {X : Type u} [TopologicalSpace X]
    (A B C D E P : Set X) (hD : D = A ∪ B) (hE : E = B ∪ C)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hoD : IsOpen D) (hoE : IsOpen E)
    (hD' : D ⊆ A ∪ B) (hE' : E ⊆ B ∪ C) (hPL : P ⊆ D ∪ C) (hPR : P ⊆ A ∪ E)
    (p q r : ℕ) (a : relativeSingularCohomology ℚ A p)
    (b : relativeSingularCohomology ℚ B q) (c : relativeSingularCohomology ℚ C r) :
    cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_assoc p q r))
        (localCupRestricted D C P hoD hC hPL (p + q) r
          (localCupRestricted A B D hA hB hD' p q a b) c) =
      localCupRestricted A E P hA hoE hPR p (q + r) a
        (localCupRestricted B C E hB hC hE' q r b c) := by
  subst D
  subst E
  rw [localCupRestricted_self, localCupRestricted_self]
  have htransport (S T : Set X) (hST : S = T) (hS : P ⊆ S) (hT : P ⊆ T)
      (k l : ℕ) (hkl : k = l) (v : relativeSingularCohomology ℚ S k) :
      relativeSingularCohomologyPullback ℚ (ContinuousMap.id X) hT l
          ((eqToIso (by subst T; subst l; rfl) :
            relativeSingularCohomology ℚ S k ≅ relativeSingularCohomology ℚ T l).hom v) =
        cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ P j)) hkl)
          (relativeSingularCohomologyPullback ℚ (ContinuousMap.id X) hS k v) := by
    subst T
    subst l
    rfl
  have h := relativeSingularCohomologyUnionCup_assoc ℚ A B C hA hB hC p q r a b c
  have h' := congrArg
    (relativeSingularCohomologyPullback ℚ (ContinuousMap.id X) hPR (p + (q + r))) h
  have hc := htransport ((A ∪ B) ∪ C) (A ∪ (B ∪ C)) (Set.union_assoc A B C)
    hPL hPR ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
    (relativeSingularCohomologyUnionCup ℚ (A ∪ B) C hoD hC (p + q) r
      (relativeSingularCohomologyUnionCup ℚ A B hA hB p q a b) c)
  exact hc.symm.trans h'

-- These adapters only name specified coordinate maps used repeatedly in the induction.
private def localCupBaseProjection (n r : ℕ) :
    C(ULift.{u} (Fin (r + n) → ℝ), ULift.{u} (Fin n → ℝ)) :=
  ⟨fun x ↦ ULift.up (fun i ↦ x.down ⟨i.val, by omega⟩), by fun_prop⟩

private def localCupFiberProjection (n r : ℕ) :
    C(ULift.{u} (Fin (r + n) → ℝ), ULift.{u} (Fin r → ℝ)) :=
  ⟨fun x ↦ ULift.up (fun i ↦ x.down ⟨n + i.val, by omega⟩), by fun_prop⟩

private def localCupCoordinateBasis (n : ℕ) :
    Module.Basis (Fin n) ℝ (ULift.{u} (Fin n → ℝ)) :=
  (Pi.basisFun ℝ (Fin n)).map (ULift.moduleEquiv : ULift.{u} (Fin n → ℝ) ≃ₗ[ℝ] _).symm

private def localCupPositiveCycle (n : ℕ) :
    relativeSingularHomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n :=
  relativeSingularHomologyRationalization {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n
    (realOrientationCycle (localCupCoordinateBasis n) (localCupCoordinateBasis n).orientation)

private def localCupEvaluation (n : ℕ) :
    relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n →ₗ[ℚ] ℚ :=
  (ULift.moduleEquiv : ULift.{u} ℚ ≃ₗ[ℚ] ℚ).toLinearMap.comp
    ((singularCochainHomologyEvaluation ℚ
      (relativeSingularChains ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0}) n).flip
      (localCupPositiveCycle n))

private def localCupProduct (n r : ℕ)
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n)
    (b : relativeSingularCohomology ℚ {v : ULift.{u} (Fin r → ℝ) | v ≠ 0} r) :
    relativeSingularCohomology ℚ {v : ULift.{u} (Fin (r + n) → ℝ) | v ≠ 0} (r + n) := by
  let V := ULift.{u} (Fin n → ℝ)
  let W := ULift.{u} (Fin r → ℝ)
  let T := ULift.{u} (Fin (r + n) → ℝ)
  let f := localCupBaseProjection.{u} n r
  let g := localCupFiberProjection.{u} n r
  let A : Set T := f ⁻¹' {v : V | v ≠ 0}
  let B : Set T := g ⁻¹' {w : W | w ≠ 0}
  let P : Set T := {v | v ≠ 0}
  have hA : IsOpen A := (isOpen_ne_fun continuous_id continuous_const).preimage f.continuous
  have hB : IsOpen B := (isOpen_ne_fun continuous_id continuous_const).preimage g.continuous
  have hP : Set.MapsTo (ContinuousMap.id T) P (A ∪ B) := by
    intro z hz
    by_cases hf : f z ≠ 0
    · exact Or.inl hf
    · by_cases hg : g z ≠ 0
      · exact Or.inr hg
      · exfalso
        apply hz
        have hf0 : f z = 0 := not_ne_iff.mp hf
        have hg0 : g z = 0 := not_ne_iff.mp hg
        apply ULift.ext
        funext i
        by_cases hi : i.val < n
        · exact congrArg (fun y : V ↦ y.down ⟨i.val, hi⟩) hf0
        · let j : Fin r := ⟨i.val - n, by omega⟩
          have hidx : (⟨n + j.val, by omega⟩ : Fin (r + n)) = i := by
            apply Fin.ext
            dsimp only [j]
            omega
          have h := congrArg (fun y : W ↦ y.down j) hg0
          change z.down ⟨n + j.val, by omega⟩ = 0 at h
          exact (congrArg z.down hidx).symm.trans h
  let product := relativeSingularCohomologyUnionCup ℚ A B hA hB n r
    (relativeSingularCohomologyPullback ℚ f (A := A) (B := {v : V | v ≠ 0})
      (fun _ h ↦ h) n a)
    (relativeSingularCohomologyPullback ℚ g (A := B) (B := {w : W | w ≠ 0})
      (fun _ h ↦ h) r b)
  exact cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_comm n r))
    (relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r) product)

private def localCupSuspension (n : ℕ)
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n) :
    relativeSingularCohomology ℚ {v : ULift.{u} (Fin (n + 1) → ℝ) | v ≠ 0} (n + 1) := by
  let E := ULift.{u} (Fin n → ℝ)
  let X := ℝ × E
  let P : Set X := {z | z ≠ 0}
  let A : Set X := {z | z.1 ≠ 0}
  let B : Set X := {z | z.2 ≠ 0}
  let f : C(X, ℝ) := ⟨Prod.fst, continuous_fst⟩
  let g : C(X, E) := ⟨Prod.snd, continuous_snd⟩
  have hP : Set.MapsTo (ContinuousMap.id X) P (A ∪ B) := by
    intro z hz
    by_cases ht : z.1 = 0
    · right
      exact fun he ↦ hz (Prod.ext ht he)
    · exact Or.inl ht
  let v := relativeSingularCohomologyUnionCup ℚ A B
    (isOpen_ne_fun continuous_fst continuous_const)
    (isOpen_ne_fun continuous_snd continuous_const) 1 n
    (positiveStepBoundaryClass ℚ f)
    (relativeSingularCohomologyPullback ℚ g (A := B) (B := {y : E | y ≠ 0})
      (fun _ h ↦ h) n a)
  let w : relativeSingularCohomology ℚ P (n + 1) :=
    cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_comm 1 n))
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.id X) hP (1 + n) v)
  let s := euclideanLocalCoordinateSplit.{u} n
  exact relativeSingularCohomologyPullback ℚ (⟨s, s.continuous⟩ : C(_, X))
    (A := {v : ULift.{u} (Fin (n + 1) → ℝ) | v ≠ 0}) (B := P)
    (fun _ h he ↦ h (s.injective (he.trans (show s 0 = 0 from rfl).symm))) (n + 1) w

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem localCupEvaluation_suspension (n : ℕ)
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n) :
    localCupEvaluation (n + 1) (localCupSuspension n a) = localCupEvaluation n a := by
  let E := ULift.{u} (Fin n → ℝ)
  let V := ULift.{u} (Fin (n + 1) → ℝ)
  let P : Set (ℝ × E) := {z | z ≠ 0}
  let s := euclideanLocalCoordinateSplit.{u} n
  let f : C(V, ℝ × E) := ⟨s, s.continuous⟩
  let hf : Set.MapsTo f {v : V | v ≠ 0} P :=
    fun _ h he ↦ h (s.injective (he.trans (show s 0 = 0 from rfl).symm))
  let z := realOrientationCycle (localCupCoordinateBasis n) (localCupCoordinateBasis n).orientation
  let c := realOrientationCycle (localCupCoordinateBasis (n + 1))
    (localCupCoordinateBasis (n + 1)).orientation
  have hcycle : (euclideanLocalSuspensionIso ℚ E n).hom
      (relativeSingularHomologyMap ℚ f hf (n + 1) (localCupPositiveCycle (n + 1))) =
      localCupPositiveCycle n := by
    have hρ := relativeSingularHomologyRationalization_naturality f hf (n + 1) c
    have hρS := congrArg (fun w ↦ (euclideanLocalSuspensionIso ℚ E n).hom w) hρ.symm
    have hs := euclideanLocalSuspensionIso_rationalization E n
      (relativeSingularHomologyMap ℤ f hf (n + 1) c)
    have hstandard : (euclideanLocalSuspensionIso ℤ E n).hom
        (relativeSingularHomologyMap ℤ f hf (n + 1) c) = z :=
      realOrientationCycle_standard_suspension n
    exact hρS.trans (hs.trans (congrArg (relativeSingularHomologyRationalization
      {y : E | y ≠ 0} n) hstandard))
  let hP : Set.MapsTo (ContinuousMap.id (ℝ × E)) P
      ({z : ℝ × E | z.1 ≠ 0} ∪ {z : ℝ × E | z.2 ≠ 0}) := by
    intro z hz
    by_cases ht : z.1 = 0
    · exact Or.inr (fun he ↦ hz (Prod.ext ht he))
    · exact Or.inl ht
  let v := relativeSingularCohomologyUnionCup ℚ
    {z : ℝ × E | z.1 ≠ 0} {z : ℝ × E | z.2 ≠ 0}
    (isOpen_ne_fun continuous_fst continuous_const)
    (isOpen_ne_fun continuous_snd continuous_const) 1 n
    (positiveStepBoundaryClass ℚ (⟨Prod.fst, continuous_fst⟩ : C(ℝ × E, ℝ)))
    (relativeSingularCohomologyPullback ℚ (⟨Prod.snd, continuous_snd⟩ : C(ℝ × E, E))
      (A := {z : ℝ × E | z.2 ≠ 0}) (B := {y : E | y ≠ 0}) (fun _ h ↦ h) n a)
  let w : relativeSingularCohomology ℚ P (n + 1) :=
    cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_comm 1 n))
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.id (ℝ × E)) hP (1 + n) v)
  have hnat := singularCochainHomologyEvaluation_naturality ℚ
    (relativeSingularChains ℚ {v : V | v ≠ 0}) (relativeSingularChains ℚ P)
    (relativeSingularChainsMap ℚ f hf) (n + 1) w (localCupPositiveCycle (n + 1))
  have hstep := positiveStepBoundaryClass_cup_evaluation ℚ E n a
    (relativeSingularHomologyMap ℚ f hf (n + 1) (localCupPositiveCycle (n + 1))) hP
  have hvalue := hnat.symm.trans hstep
  rw [hcycle] at hvalue
  exact congrArg ULift.down hvalue

-- Degree transport adapters are shared by the suspension, product, and final coordinate comparison.
private theorem localCupPullback_cast {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (m n : ℕ) (h : m = n) (a : relativeSingularCohomology ℚ B m) :
    relativeSingularCohomologyPullback ℚ f hf n
        (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ B k)) h) a) =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ A k)) h)
        (relativeSingularCohomologyPullback ℚ f hf m a) := by
  subst n
  rfl

private theorem localCupRestricted_cast_left {X : Type u} [TopologicalSpace X]
    (A B P : Set X) (hA : IsOpen A) (hB : IsOpen B) (hP : P ⊆ A ∪ B)
    (p p' q : ℕ) (h : p = p') (a : relativeSingularCohomology ℚ A p)
    (b : relativeSingularCohomology ℚ B q) :
    localCupRestricted A B P hA hB hP p' q
        (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ A k)) h) a) b =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (congrArg (· + q) h)) (localCupRestricted A B P hA hB hP p q a b) := by
  subst p'
  rfl

private theorem localCupRestricted_cast_right {X : Type u} [TopologicalSpace X]
    (A B P : Set X) (hA : IsOpen A) (hB : IsOpen B) (hP : P ⊆ A ∪ B)
    (p q q' : ℕ) (h : q = q') (a : relativeSingularCohomology ℚ A p)
    (b : relativeSingularCohomology ℚ B q) :
    localCupRestricted A B P hA hB hP p q' a
        (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ B k)) h) b) =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (congrArg (p + ·) h)) (localCupRestricted A B P hA hB hP p q a b) := by
  subst q'
  rfl

private theorem localCupStep_natural {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(Y, ℝ)) (g : C(X, Y))
    (h : C(X, ℝ)) (heq : f.comp g = h)
    (hg : Set.MapsTo g {x : X | h x ≠ 0} {y : Y | f y ≠ 0}) :
    relativeSingularCohomologyPullback ℚ g hg 1 (positiveStepBoundaryClass ℚ f) =
      positiveStepBoundaryClass ℚ h := by
  subst h
  exact positiveStepBoundaryClass_natural ℚ f g

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem localCupSuspension_pullback {X : Type u} [TopologicalSpace X]
    (n : ℕ) (f : C(X, ULift.{u} (Fin (n + 1) → ℝ)))
    (g₀ : C(X, ℝ)) (g₁ : C(X, ULift.{u} (Fin n → ℝ)))
    (h₀ : ∀ x, (euclideanLocalCoordinateSplit n (f x)).1 = g₀ x)
    (h₁ : ∀ x, (euclideanLocalCoordinateSplit n (f x)).2 = g₁ x)
    (P : Set X) (hf : Set.MapsTo f P {v | v ≠ 0})
    (hP : P ⊆ {x : X | g₀ x ≠ 0} ∪ {x : X | g₁ x ≠ 0})
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n) :
    relativeSingularCohomologyPullback ℚ f hf (n + 1) (localCupSuspension n a) =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_comm 1 n))
        (localCupRestricted {x : X | g₀ x ≠ 0} {x : X | g₁ x ≠ 0} P
          (isOpen_ne_fun g₀.continuous continuous_const)
          (isOpen_ne_fun g₁.continuous continuous_const) hP 1 n
          (positiveStepBoundaryClass ℚ g₀)
          (relativeSingularCohomologyPullback ℚ g₁ (A := {x : X | g₁ x ≠ 0})
            (B := {v : ULift.{u} (Fin n → ℝ) | v ≠ 0}) (fun _ h ↦ h) n a)) := by
  let E := ULift.{u} (Fin n → ℝ)
  let Y := ℝ × E
  let A : Set X := {x | g₀ x ≠ 0}
  let B : Set X := {x | g₁ x ≠ 0}
  let A' : Set Y := {y | y.1 ≠ 0}
  let B' : Set Y := {y | y.2 ≠ 0}
  let P' : Set Y := {y | y ≠ 0}
  let t : C(Y, ℝ) := ⟨Prod.fst, continuous_fst⟩
  let v : C(Y, E) := ⟨Prod.snd, continuous_snd⟩
  let s : C(ULift.{u} (Fin (n + 1) → ℝ), Y) :=
    ⟨euclideanLocalCoordinateSplit n, (euclideanLocalCoordinateSplit n).continuous⟩
  let F := s.comp f
  have hs : Set.MapsTo s {z | z ≠ 0} P' := by
    intro z hz he
    exact hz ((euclideanLocalCoordinateSplit n).injective
      (he.trans (show s 0 = 0 from rfl).symm))
  have hP' : P' ⊆ A' ∪ B' := by
    intro z hz
    by_cases h : z.1 = 0
    · exact Or.inr (fun he ↦ hz (Prod.ext h he))
    · exact Or.inl h
  have hFA : Set.MapsTo F A A' := by
    intro x hx
    change (s (f x)).1 ≠ 0
    exact fun h ↦ hx ((h₀ x).symm.trans h)
  have hFB : Set.MapsTo F B B' := by
    intro x hx
    change (s (f x)).2 ≠ 0
    exact fun h ↦ hx ((h₁ x).symm.trans h)
  let c := relativeSingularCohomologyPullback ℚ v
    (A := B') (B := {z : E | z ≠ 0}) (fun _ h ↦ h) n a
  let d := localCupRestricted A' B' P'
    (isOpen_ne_fun continuous_fst continuous_const)
    (isOpen_ne_fun continuous_snd continuous_const) hP' 1 n
    (positiveStepBoundaryClass ℚ t) c
  have hc := localCupPullback_comp f s hf hs (n + 1)
    (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P' k)) (Nat.add_comm 1 n)) d)
  have hd := localCupPullback_cast F (hs.comp hf) (1 + n) (n + 1) (Nat.add_comm 1 n) d
  have hn := localCupRestricted_natural F A B P A' B' P'
    (isOpen_ne_fun g₀.continuous continuous_const)
    (isOpen_ne_fun g₁.continuous continuous_const)
    (isOpen_ne_fun continuous_fst continuous_const)
    (isOpen_ne_fun continuous_snd continuous_const) hP hP' hFA hFB (hs.comp hf)
    1 n (positiveStepBoundaryClass ℚ t) c
  have hstep := localCupStep_natural t F g₀ (ContinuousMap.ext h₀) hFA
  have hrest : relativeSingularCohomologyPullback ℚ F hFB n c =
      relativeSingularCohomologyPullback ℚ g₁
        (A := B) (B := {z : E | z ≠ 0}) (fun _ h ↦ h) n a := by
    exact (localCupPullback_comp F v hFB (fun _ h ↦ h) n a).trans
      (congrArg (fun h ↦ h a) (localCupPullback_congr (v.comp F) g₁
        (ContinuousMap.ext h₁) (fun _ h ↦ hFB h) (fun _ h ↦ h) n))
  have heq : relativeSingularCohomologyPullback ℚ F (hs.comp hf) (1 + n) d =
      localCupRestricted A B P (isOpen_ne_fun g₀.continuous continuous_const)
        (isOpen_ne_fun g₁.continuous continuous_const) hP 1 n
        (positiveStepBoundaryClass ℚ g₀)
        (relativeSingularCohomologyPullback ℚ g₁
          (A := B) (B := {z : E | z ≠ 0}) (fun _ h ↦ h) n a) := by
    exact hn.trans (congrArg₂ (localCupRestricted A B P
      (isOpen_ne_fun g₀.continuous continuous_const)
      (isOpen_ne_fun g₁.continuous continuous_const) hP 1 n) hstep hrest)
  exact hc.trans (hd.trans (congrArg
    (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
      (Nat.add_comm 1 n))) heq))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem localCupProduct_pullback {X : Type u} [TopologicalSpace X]
    (n r : ℕ) (f : C(X, ULift.{u} (Fin (r + n) → ℝ)))
    (g₀ : C(X, ULift.{u} (Fin n → ℝ))) (g₁ : C(X, ULift.{u} (Fin r → ℝ)))
    (h₀ : (localCupBaseProjection n r).comp f = g₀)
    (h₁ : (localCupFiberProjection n r).comp f = g₁)
    (P : Set X) (hf : Set.MapsTo f P {v | v ≠ 0})
    (hP : P ⊆ {x : X | g₀ x ≠ 0} ∪ {x : X | g₁ x ≠ 0})
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n)
    (b : relativeSingularCohomology ℚ {v : ULift.{u} (Fin r → ℝ) | v ≠ 0} r) :
    relativeSingularCohomologyPullback ℚ f hf (r + n) (localCupProduct n r a b) =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_comm n r))
        (localCupRestricted {x : X | g₀ x ≠ 0} {x : X | g₁ x ≠ 0} P
          (isOpen_ne_fun g₀.continuous continuous_const)
          (isOpen_ne_fun g₁.continuous continuous_const) hP n r
          (relativeSingularCohomologyPullback ℚ g₀ (A := {x : X | g₀ x ≠ 0})
            (B := {v : ULift.{u} (Fin n → ℝ) | v ≠ 0}) (fun _ h ↦ h) n a)
          (relativeSingularCohomologyPullback ℚ g₁ (A := {x : X | g₁ x ≠ 0})
            (B := {v : ULift.{u} (Fin r → ℝ) | v ≠ 0}) (fun _ h ↦ h) r b)) := by
  let Y := ULift.{u} (Fin (r + n) → ℝ)
  let A : Set X := {x | g₀ x ≠ 0}
  let B : Set X := {x | g₁ x ≠ 0}
  let v := localCupBaseProjection.{u} n r
  let w := localCupFiberProjection.{u} n r
  let A' : Set Y := {y | v y ≠ 0}
  let B' : Set Y := {y | w y ≠ 0}
  let P' : Set Y := {y | y ≠ 0}
  have hP' : P' ⊆ A' ∪ B' := by
    intro z hz
    by_cases hv : v z ≠ 0
    · exact Or.inl hv
    · by_cases hw : w z ≠ 0
      · exact Or.inr hw
      · exfalso
        apply hz
        have hv0 : v z = 0 := not_ne_iff.mp hv
        have hw0 : w z = 0 := not_ne_iff.mp hw
        apply ULift.ext
        funext i
        by_cases hi : i.val < n
        · exact congrArg (fun y : ULift.{u} (Fin n → ℝ) ↦ y.down ⟨i.val, hi⟩) hv0
        · let j : Fin r := ⟨i.val - n, by omega⟩
          have hj : (⟨n + j.val, by omega⟩ : Fin (r + n)) = i := by
            apply Fin.ext
            dsimp only [j]
            omega
          have h := congrArg (fun y : ULift.{u} (Fin r → ℝ) ↦ y.down j) hw0
          change z.down ⟨n + j.val, by omega⟩ = 0 at h
          exact (congrArg z.down hj).symm.trans h
  have hFA : Set.MapsTo f A A' := by
    intro x hx h
    exact hx ((congrArg (fun g ↦ g x) h₀).symm.trans h)
  have hFB : Set.MapsTo f B B' := by
    intro x hx h
    exact hx ((congrArg (fun g ↦ g x) h₁).symm.trans h)
  let av := relativeSingularCohomologyPullback ℚ v
    (A := A') (B := {z : ULift.{u} (Fin n → ℝ) | z ≠ 0}) (fun _ h ↦ h) n a
  let bw := relativeSingularCohomologyPullback ℚ w
    (A := B') (B := {z : ULift.{u} (Fin r → ℝ) | z ≠ 0}) (fun _ h ↦ h) r b
  let d := localCupRestricted A' B' P' (isOpen_ne_fun v.continuous continuous_const)
    (isOpen_ne_fun w.continuous continuous_const) hP' n r av bw
  have hc := localCupPullback_cast f hf (n + r) (r + n) (Nat.add_comm n r) d
  have hn := localCupRestricted_natural f A B P A' B' P'
    (isOpen_ne_fun g₀.continuous continuous_const)
    (isOpen_ne_fun g₁.continuous continuous_const)
    (isOpen_ne_fun v.continuous continuous_const)
    (isOpen_ne_fun w.continuous continuous_const) hP hP' hFA hFB hf n r av bw
  have ha : relativeSingularCohomologyPullback ℚ f hFA n av =
      relativeSingularCohomologyPullback ℚ g₀
        (A := A) (B := {z : ULift.{u} (Fin n → ℝ) | z ≠ 0}) (fun _ h ↦ h) n a :=
    (localCupPullback_comp f v hFA (fun _ h ↦ h) n a).trans
      (congrArg (fun h ↦ h a) (localCupPullback_congr (v.comp f) g₀ h₀
        (fun _ h ↦ hFA h) (fun _ h ↦ h) n))
  have hb : relativeSingularCohomologyPullback ℚ f hFB r bw =
      relativeSingularCohomologyPullback ℚ g₁
        (A := B) (B := {z : ULift.{u} (Fin r → ℝ) | z ≠ 0}) (fun _ h ↦ h) r b :=
    (localCupPullback_comp f w hFB (fun _ h ↦ h) r b).trans
      (congrArg (fun h ↦ h b) (localCupPullback_congr (w.comp f) g₁ h₁
        (fun _ h ↦ hFB h) (fun _ h ↦ h) r))
  exact hc.trans (congrArg
    (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_comm n r)))
    (hn.trans (congrArg₂ (localCupRestricted A B P
      (isOpen_ne_fun g₀.continuous continuous_const)
      (isOpen_ne_fun g₁.continuous continuous_const) hP n r) ha hb)))

private theorem localCupPullback_self {X : Type u} [TopologicalSpace X]
    (P : Set X) (k : ℕ) (a : relativeSingularCohomology ℚ P k) :
    relativeSingularCohomologyPullback ℚ (ContinuousMap.id X)
      (A := P) (B := P) (fun _ h ↦ h) k a = a := by
  have hid : relativeSingularCohomologyPullback ℚ (ContinuousMap.id X)
      (A := P) (B := P) (fun _ h ↦ h) k = 𝟙 _ := by
    change (relativeSingularCohomologyFunctor ℚ X k).map (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  exact congrArg (fun f ↦ f a) hid

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem localCupProduct_suspension (n r : ℕ)
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n)
    (b : relativeSingularCohomology ℚ {v : ULift.{u} (Fin r → ℝ) | v ≠ 0} r) :
    localCupProduct (n + 1) r (localCupSuspension n a) b =
      localCupSuspension (r + n) (localCupProduct n r a b) := by
  let X := ULift.{u} (Fin (r + (n + 1)) → ℝ)
  let f := localCupBaseProjection.{u} (n + 1) r
  let s := euclideanLocalCoordinateSplit.{u} (r + n)
  let t : C(X, ℝ) := ⟨fun z ↦ (s z).1, continuous_fst.comp s.continuous⟩
  let v : C(X, ULift.{u} (Fin (r + n) → ℝ)) :=
    ⟨fun z ↦ (s z).2, continuous_snd.comp s.continuous⟩
  let g := (localCupBaseProjection.{u} n r).comp v
  let h := localCupFiberProjection.{u} (n + 1) r
  let A : Set X := {z | t z ≠ 0}
  let B : Set X := {z | g z ≠ 0}
  let C : Set X := {z | h z ≠ 0}
  let D : Set X := {z | f z ≠ 0}
  let E : Set X := {z | v z ≠ 0}
  let P : Set X := {z | z ≠ 0}
  have hfirst (z : X) : (euclideanLocalCoordinateSplit n (f z)).1 = t z := rfl
  have hrest (z : X) : (euclideanLocalCoordinateSplit n (f z)).2 = g z := by
    apply ULift.ext
    funext i
    apply congrArg z.down
    apply Fin.ext
    rfl
  have hfiber : (localCupFiberProjection n r).comp v = h := by
    apply ContinuousMap.ext
    intro z
    apply ULift.ext
    funext i
    apply congrArg z.down
    apply Fin.ext
    change n + i.val + 1 = n + 1 + i.val
    omega
  -- These equalities retain the same three actual coordinate supports on both sides.
  have hD : D = A ∪ B := by
    ext z
    constructor
    · intro hz
      by_cases ht : t z = 0
      · right
        intro hg
        apply hz
        apply (euclideanLocalCoordinateSplit n).injective
        apply Prod.ext
        · exact (hfirst z).trans ht
        · exact (hrest z).trans hg
      · exact Or.inl ht
    · intro hz he
      rcases hz with ht | hg
      · apply ht
        exact (hfirst z).symm.trans (congrArg (fun y ↦
          (euclideanLocalCoordinateSplit n y).1) he)
      · apply hg
        exact (hrest z).symm.trans (congrArg (fun y ↦
          (euclideanLocalCoordinateSplit n y).2) he)
  have hE : E = B ∪ C := by
    ext z
    constructor
    · intro hz
      by_cases hg : g z ≠ 0
      · exact Or.inl hg
      · right
        intro hh
        apply hz
        have hg0 : g z = 0 := not_ne_iff.mp hg
        have hh0 : localCupFiberProjection n r (v z) = 0 :=
          (congrArg (fun q ↦ q z) hfiber).trans hh
        apply ULift.ext
        funext i
        by_cases hi : i.val < n
        · exact congrArg (fun y : ULift.{u} (Fin n → ℝ) ↦ y.down ⟨i.val, hi⟩) hg0
        · let j : Fin r := ⟨i.val - n, by omega⟩
          have hj : (⟨n + j.val, by omega⟩ : Fin (r + n)) = i := by
            apply Fin.ext
            dsimp only [j]
            omega
          have hzj := congrArg (fun y : ULift.{u} (Fin r → ℝ) ↦ y.down j) hh0
          change (v z).down ⟨n + j.val, by omega⟩ = 0 at hzj
          exact (congrArg (v z).down hj).symm.trans hzj
    · intro hz he
      rcases hz with hg | hh
      · apply hg
        exact congrArg (localCupBaseProjection n r) he
      · apply hh
        exact (congrArg (fun q ↦ q z) hfiber).symm.trans
          (congrArg (localCupFiberProjection n r) he)
  have hD' : D ⊆ A ∪ B := hD.subset
  have hE' : E ⊆ B ∪ C := hE.subset
  have hPR : P ⊆ A ∪ E := by
    intro z hz
    by_cases ht : t z = 0
    · right
      intro hv
      exact hz (s.injective (Prod.ext ht hv))
    · exact Or.inl ht
  have hPL : P ⊆ D ∪ C := by
    intro z hz
    rcases hPR hz with ha | he
    · exact Or.inl (hD.symm.subset (Or.inl ha))
    · rcases hE' he with hb | hc
      · exact Or.inl (hD.symm.subset (Or.inr hb))
      · exact Or.inr hc
  let hoA : IsOpen A := isOpen_ne_fun t.continuous continuous_const
  let hoB : IsOpen B := isOpen_ne_fun g.continuous continuous_const
  let hoC : IsOpen C := isOpen_ne_fun h.continuous continuous_const
  let hoD : IsOpen D := isOpen_ne_fun f.continuous continuous_const
  let hoE : IsOpen E := isOpen_ne_fun v.continuous continuous_const
  let a₀ := positiveStepBoundaryClass ℚ t
  let a₁ := relativeSingularCohomologyPullback ℚ g
    (A := B) (B := {z : ULift.{u} (Fin n → ℝ) | z ≠ 0}) (fun _ h ↦ h) n a
  let a₂ := relativeSingularCohomologyPullback ℚ h
    (A := C) (B := {z : ULift.{u} (Fin r → ℝ) | z ≠ 0}) (fun _ h ↦ h) r b
  let u := localCupRestricted D C P hoD hoC hPL (1 + n) r
    (localCupRestricted A B D hoA hoB hD' 1 n a₀ a₁) a₂
  let w := localCupRestricted A E P hoA hoE hPR 1 (n + r) a₀
    (localCupRestricted B C E hoB hoC hE' n r a₁ a₂)
  -- Naturality moves each suspension and product to those specified common supports.
  have hlift := localCupSuspension_pullback n f t g hfirst hrest D (fun _ h ↦ h) hD' a
  have hleft : localCupProduct (n + 1) r (localCupSuspension n a) b =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (show (1 + n) + r = r + (n + 1) by omega)) u := by
    have hc := localCupRestricted_cast_left D C P hoD hoC hPL
      (1 + n) (n + 1) r (Nat.add_comm 1 n)
      (localCupRestricted A B D hoA hoB hD' 1 n a₀ a₁) a₂
    have hh := congrArg (fun z ↦ localCupRestricted D C P hoD hoC hPL (n + 1) r z a₂)
      hlift
    have hcast := congrArg
      (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (Nat.add_comm (n + 1) r))) (hh.trans hc)
    exact hcast.trans (by simp only [cast_cast]; rfl)
  have hprod := localCupProduct_pullback n r v g h rfl hfiber E (fun _ h ↦ h) hE' a b
  have hsusp := localCupSuspension_pullback (r + n) (ContinuousMap.id X) t v
    (fun _ ↦ rfl) (fun _ ↦ rfl) P (fun _ h ↦ h) hPR (localCupProduct n r a b)
  have hsid := localCupPullback_self P (r + n + 1)
    (localCupSuspension (r + n) (localCupProduct n r a b))
  have hright : localCupSuspension (r + n) (localCupProduct n r a b) =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (show 1 + (n + r) = r + (n + 1) by omega)) w := by
    have hc := localCupRestricted_cast_right A E P hoA hoE hPR
      1 (n + r) (r + n) (Nat.add_comm n r) a₀
      (localCupRestricted B C E hoB hoC hE' n r a₁ a₂)
    have hh := congrArg (localCupRestricted A E P hoA hoE hPR 1 (r + n) a₀) hprod
    have hcast := congrArg
      (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (Nat.add_comm 1 (r + n)))) (hh.trans hc)
    exact hsid.symm.trans (hsusp.trans (hcast.trans (by simp only [cast_cast]; rfl)))
  -- The actual three-relative associativity accounts for the sole remaining transport.
  have hassoc := localCupRestricted_assoc A B C D E P hD hE hoA hoB hoC hoD hoE
    hD' hE' hPL hPR 1 n r a₀ a₁ a₂
  have hcast := congrArg
    (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
      (show 1 + (n + r) = r + (n + 1) by omega))) hassoc
  have hfinal : cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (show (1 + n) + r = r + (n + 1) by omega)) u =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (show 1 + (n + r) = r + (n + 1) by omega)) w := by
    simpa only [cast_cast] using hcast
  exact hleft.trans (hfinal.trans hright.symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem localCupEvaluation_product_zero (r : ℕ)
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin 0 → ℝ) | v ≠ 0} 0)
    (b : relativeSingularCohomology ℚ {v : ULift.{u} (Fin r → ℝ) | v ≠ 0} r) :
    localCupEvaluation r (localCupProduct 0 r a b) =
      localCupEvaluation 0 a * localCupEvaluation r b := by
  let X := ULift.{u} (Fin r → ℝ)
  let P : Set X := {v | v ≠ 0}
  let f : C(X, ULift.{u} (Fin 0 → ℝ)) := ContinuousMap.const X 0
  let g : C(X, X) := ContinuousMap.id X
  let A : Set X := {x | f x ≠ 0}
  have h₀ : (localCupBaseProjection 0 r).comp g = f := by
    apply ContinuousMap.ext
    intro x
    exact Subsingleton.elim _ _
  have h₁ : (localCupFiberProjection 0 r).comp g = g := by
    apply ContinuousMap.ext
    intro x
    apply ULift.ext
    funext i
    apply congrArg x.down
    apply Fin.ext
    change 0 + i.val = i.val
    exact Nat.zero_add _
  have hP : P ⊆ A ∪ P := fun _ h ↦ Or.inr h
  let hoA : IsOpen A := isOpen_ne_fun f.continuous continuous_const
  let hoP : IsOpen P := isOpen_ne_fun continuous_id continuous_const
  let a₀ := relativeSingularCohomologyPullback ℚ f
    (A := A) (B := {v : ULift.{u} (Fin 0 → ℝ) | v ≠ 0}) (fun _ h ↦ h) 0 a
  let d := localCupRestricted A P P hoA hoP hP 0 r a₀ b
  have hpull := localCupProduct_pullback 0 r g f g h₀ h₁ P (fun _ h ↦ h) hP a b
  have hidb := localCupPullback_self P r b
  have hidp := localCupPullback_self P r (localCupProduct 0 r a b)
  have hd : localCupProduct 0 r a b =
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.zero_add r)) d := by
    have h := congrArg
      (fun z ↦ cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
        (Nat.zero_add r)) (localCupRestricted A P P hoA hoP hP 0 r a₀ z)) hidb
    exact hidp.symm.trans (hpull.trans h)
  have hzero := relativeSingularCohomologyUnionCup_zero_evaluation
    (localCupCoordinateBasis.{u} 0) P hoP r a b (localCupPositiveCycle r)
  have hcastIso {V W : ModuleCat.{u} ℚ} (h : V = W) (z : V) :
      (eqToIso h).hom z = cast (congrArg ModuleCat.carrier h) z := by
    subst W
    rfl
  dsimp only at hzero
  rw [hcastIso] at hzero
  rw [hd]
  exact hzero

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem localCupEvaluation_product (n r : ℕ)
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n)
    (b : relativeSingularCohomology ℚ {v : ULift.{u} (Fin r → ℝ) | v ≠ 0} r) :
    localCupEvaluation (r + n) (localCupProduct n r a b) =
      localCupEvaluation n a * localCupEvaluation r b := by
  induction n with
  | zero => exact localCupEvaluation_product_zero r a b
  | succ n ih =>
    -- The same original rational cycle detects every local class, including its sign.
    have hn : Function.Bijective (localCupEvaluation.{u} n) :=
      rationalRealOrientationEvaluation_bijective
        (localCupCoordinateBasis n) (localCupCoordinateBasis n).orientation
    have hs : Function.Injective (localCupEvaluation.{u} (n + 1)) :=
      (rationalRealOrientationEvaluation_bijective
        (localCupCoordinateBasis (n + 1)) (localCupCoordinateBasis (n + 1)).orientation).1
    obtain ⟨c, hc⟩ := hn.2 (localCupEvaluation (n + 1) a)
    have heq : localCupSuspension n c = a :=
      hs ((localCupEvaluation_suspension n c).trans hc)
    -- First suspend the base class, then associate its first-coordinate step with the fiber.
    rw [← heq, localCupProduct_suspension]
    exact (localCupEvaluation_suspension (r + n) (localCupProduct n r c b)).trans
      ((ih c).trans (congrArg (fun q ↦ q * localCupEvaluation r b)
        (localCupEvaluation_suspension n c).symm))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Two local relative classes pair multiplicatively with the original positive coordinate cycle. -/
theorem relativeSingularCohomologyUnionCup_liftedPi_evaluation (n r : ℕ)
    (a : relativeSingularCohomology ℚ {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n)
    (b : relativeSingularCohomology ℚ {v : ULift.{u} (Fin r → ℝ) | v ≠ 0} r) :
    let V := ULift.{u} (Fin n → ℝ)
    let W := ULift.{u} (Fin r → ℝ)
    let T := ULift.{u} (Fin (r + n) → ℝ)
    let f : C(T, V) :=
      ⟨fun x ↦ ULift.up (fun i ↦ x.down ⟨i.val, by omega⟩), by dsimp only [T, V]; fun_prop⟩
    let g : C(T, W) :=
      ⟨fun x ↦ ULift.up (fun i ↦ x.down ⟨n + i.val, by omega⟩), by dsimp only [T, W]; fun_prop⟩
    let A : Set T := f ⁻¹' {v : V | v ≠ 0}
    let B : Set T := g ⁻¹' {w : W | w ≠ 0}
    let P : Set T := {v | v ≠ 0}
    ∀ hP : Set.MapsTo (ContinuousMap.id T) P (A ∪ B),
    let c := relativeSingularCohomologyUnionCup ℚ A B
      ((isOpen_ne_fun continuous_id continuous_const).preimage f.continuous)
      ((isOpen_ne_fun continuous_id continuous_const).preimage g.continuous) n r
      (relativeSingularCohomologyPullback ℚ f (A := A) (B := {v : V | v ≠ 0})
        (fun _ h ↦ h) n a)
      (relativeSingularCohomologyPullback ℚ g (A := B) (B := {w : W | w ≠ 0})
        (fun _ h ↦ h) r b)
    let d := cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
      (Nat.add_comm n r))
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r) c)
    let bV := (Pi.basisFun ℝ (Fin n)).map
      (ULift.moduleEquiv : V ≃ₗ[ℝ] _).symm
    let bW := (Pi.basisFun ℝ (Fin r)).map
      (ULift.moduleEquiv : W ≃ₗ[ℝ] _).symm
    let bT := (Pi.basisFun ℝ (Fin (r + n))).map
      (ULift.moduleEquiv : T ≃ₗ[ℝ] _).symm
    (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ P) (r + n) d
      (relativeSingularHomologyRationalization P (r + n)
        (realOrientationCycle bT bT.orientation))).down =
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {v : V | v ≠ 0}) n a
        (relativeSingularHomologyRationalization {v : V | v ≠ 0} n
          (realOrientationCycle bV bV.orientation))).down *
      (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {w : W | w ≠ 0}) r b
        (relativeSingularHomologyRationalization {w : W | w ≠ 0} r
          (realOrientationCycle bW bW.orientation))).down := by
  dsimp only
  intro hP
  exact localCupEvaluation_product n r a b

end AtiyahSinger
