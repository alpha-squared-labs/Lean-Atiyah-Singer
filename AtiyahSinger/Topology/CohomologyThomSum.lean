/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyThom
public import AtiyahSinger.Topology.RelativeCohomologyUnionCup

/-!
# The normalized Thom class of an actual direct sum

Public module ID: M1631.

The relative cup of two specified Thom classes is compared on the same
original fibers. A specified orientation unit is retained in this comparison,
so the theorem applies to the sign of real complexification. The two bundle
projections need no properness: their relative conditions combine before any
compact-support colimit is used. This is the Thom-class argument behind the
Euler product formula, retained here before forgetting relative support.

Source: Milnor--Stasheff, Sections 9 and 11, multiplicativity of Thom classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u

set_option maxHeartbeats 600000 in
-- All three native bundle models and the actual relative pair maps are retained.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original relative Thom cup carries exactly its specified fiber orientation unit. -/
theorem cohomologyThomClass_prod_of_fiberClass (R : Type) [CommRing R]
    (p q s : ℕ) (hdegree : p + q = s)
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin p)) E)]
    [FiberBundle (EuclideanSpace ℝ (Fin p)) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin p)) E]
    (F : X → Type u) [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin q)) F)]
    [FiberBundle (EuclideanSpace ℝ (Fin q)) F]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin q)) F]
    (G : X → Type u) [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℝ (G x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin s)) G)]
    [FiberBundle (EuclideanSpace ℝ (Fin s)) G]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin s)) G]
    (oE : CohomologyOrientation R p E) (oF : CohomologyOrientation R q F)
    (oG : CohomologyOrientation R s G) (ε : Rˣ)
    (qE : C(TotalSpace (EuclideanSpace ℝ (Fin s)) G,
      TotalSpace (EuclideanSpace ℝ (Fin p)) E))
    (qF : C(TotalSpace (EuclideanSpace ℝ (Fin s)) G,
      TotalSpace (EuclideanSpace ℝ (Fin q)) F))
    (e : ∀ x, G x ≃L[ℝ] E x × F x)
    (hqE : ∀ x v, qE ⟨x, v⟩ = ⟨x, (e x v).1⟩)
    (hqF : ∀ x v, qF ⟨x, v⟩ = ⟨x, (e x v).2⟩)
    (ho : ∀ x,
      let A : Set (E x × F x) := {z | z.1 ≠ 0}
      let B : Set (E x × F x) := {z | z.2 ≠ 0}
      let P : Set (E x × F x) := {z | z ≠ 0}
      ∀ hP : Set.MapsTo (ContinuousMap.id (E x × F x)) P (A ∪ B),
      relativeSingularCohomologyPullback R (⟨e x, (e x).continuous⟩ : C(G x, E x × F x))
        (A := {v | v ≠ 0}) (B := P)
        (fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm))) s
        (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology R P k)) hdegree)
          (relativeSingularCohomologyPullback R (ContinuousMap.id (E x × F x)) hP (p + q)
            (relativeSingularCohomologyUnionCup R A B
              (isOpen_ne_fun continuous_fst continuous_const)
              (isOpen_ne_fun continuous_snd continuous_const) p q
              (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(E x × F x, E x))
                (A := A) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) p (oE.fiberClass x))
              (relativeSingularCohomologyPullback R (ContinuousMap.snd : C(E x × F x, F x))
                (A := B) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) q (oF.fiberClass x))))) =
      (ε : R) • oG.fiberClass x) :
    let T := TotalSpace (EuclideanSpace ℝ (Fin s)) G
    let A : Set T := qE ⁻¹' bundleNonzero p E
    let B : Set T := qF ⁻¹' bundleNonzero q F
    let N := bundleNonzero s G
    ∀ (hA : IsOpen A) (hB : IsOpen B)
      (hN : Set.MapsTo (ContinuousMap.id T) N (A ∪ B)),
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology R N k)) hdegree)
        (relativeSingularCohomologyPullback R (ContinuousMap.id T) hN (p + q)
          (relativeSingularCohomologyUnionCup R A B hA hB p q
            (relativeSingularCohomologyPullback R qE (fun _ hv ↦ hv) p
              (cohomologyThomClass R p E oE))
            (relativeSingularCohomologyPullback R qF (fun _ hv ↦ hv) q
              (cohomologyThomClass R q F oF)))) =
      (ε : R) • cohomologyThomClass R s G oG := by
  classical
  subst s
  dsimp only
  intro hA hB hN
  let restrictedRelativeCup
      {X : Type u} [TopologicalSpace X]
      (A B P : Set X) (hA : IsOpen A) (hB : IsOpen B)
      (hP : Set.MapsTo (ContinuousMap.id X) P (A ∪ B))
      (p q s : ℕ) (hdegree : p + q = s)
      (a : relativeSingularCohomology R A p) (b : relativeSingularCohomology R B q) :
      relativeSingularCohomology R P s :=
    cast (congrArg (fun k ↦ ↥(relativeSingularCohomology R P k)) hdegree)
      (relativeSingularCohomologyPullback R (ContinuousMap.id X) hP (p + q)
        (relativeSingularCohomologyUnionCup R A B hA hB p q a b))
  have restrictedRelativeCup_naturality
      {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
      (A B P : Set X) (A' B' P' : Set Y)
      (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B')
      (hP : Set.MapsTo (ContinuousMap.id X) P (A ∪ B))
      (hP' : Set.MapsTo (ContinuousMap.id Y) P' (A' ∪ B'))
      (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') (hfP : Set.MapsTo f P P')
      (p q s : ℕ) (hdegree : p + q = s)
      (a : relativeSingularCohomology R A' p) (b : relativeSingularCohomology R B' q) :
      relativeSingularCohomologyPullback R f hfP s
        (restrictedRelativeCup A' B' P' hA' hB' hP' p q s hdegree a b) =
      restrictedRelativeCup A B P hA hB hP p q s hdegree
        (relativeSingularCohomologyPullback R f hfA p a)
        (relativeSingularCohomologyPullback R f hfB q b) := by
    subst s
    let hfU : Set.MapsTo f (A ∪ B) (A' ∪ B') :=
      fun _ hx ↦ hx.elim (fun ha ↦ Or.inl (hfA ha)) (fun hb ↦ Or.inr (hfB hb))
    have hcomp (c : relativeSingularCohomology R (A' ∪ B') (p + q)) :
        relativeSingularCohomologyPullback R f hfP (p + q)
          (relativeSingularCohomologyPullback R (ContinuousMap.id Y) hP' (p + q) c) =
        relativeSingularCohomologyPullback R (ContinuousMap.id X) hP (p + q)
          (relativeSingularCohomologyPullback R f hfU (p + q) c) := by
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp,
        ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      rfl
    exact (hcomp _).trans (congrArg
      (relativeSingularCohomologyPullback R (ContinuousMap.id X) hP (p + q))
      (relativeSingularCohomologyPullback_unionCup R f hA hB hA' hB' hfA hfB p q a b))
  let TE := TotalSpace (EuclideanSpace ℝ (Fin p)) E
  let TF := TotalSpace (EuclideanSpace ℝ (Fin q)) F
  let TG := TotalSpace (EuclideanSpace ℝ (Fin (p + q))) G
  let A : Set TG := qE ⁻¹' bundleNonzero p E
  let B : Set TG := qF ⁻¹' bundleNonzero q F
  let N := bundleNonzero (p + q) G
  let tE := cohomologyThomClass R p E oE
  let tF := cohomologyThomClass R q F oF
  have hqEA : Set.MapsTo qE A (bundleNonzero p E) := fun _ hv ↦ hv
  have hqFB : Set.MapsTo qF B (bundleNonzero q F) := fun _ hv ↦ hv
  let a : relativeSingularCohomology R A p :=
    relativeSingularCohomologyPullback R qE hqEA p tE
  let b : relativeSingularCohomology R B q :=
    relativeSingularCohomologyPullback R qF hqFB q tF
  let t := restrictedRelativeCup A B N hA hB hN p q (p + q) rfl a b
  -- The same two global Thom factors restrict to the specified product class on each fiber.
  have hfiber (x : X) : relativeSingularCohomologyPullback R
      (bundleFiberInclusion (p + q) G x)
      (A := {v : G x | v ≠ 0}) (B := bundleNonzero (p + q) G)
      (fun _ hv ↦ hv) (p + q) t =
        (ε : R) • oG.fiberClass x := by
    let j := bundleFiberInclusion (p + q) G x
    let k : C(G x, E x × F x) := ⟨e x, (e x).continuous⟩
    let f : C(G x, E x) := ContinuousMap.fst.comp k
    let g : C(G x, F x) := ContinuousMap.snd.comp k
    let U : Set (G x) := {v | f v ≠ 0}
    let V : Set (G x) := {v | g v ≠ 0}
    let P : Set (G x) := {v | v ≠ 0}
    let U' : Set (E x × F x) := {v | v.1 ≠ 0}
    let V' : Set (E x × F x) := {v | v.2 ≠ 0}
    let P' : Set (E x × F x) := {v | v ≠ 0}
    have hP' : Set.MapsTo (ContinuousMap.id (E x × F x)) P' (U' ∪ V') := by
      intro v hv
      by_cases h : v.1 = 0
      · exact Or.inr (fun h' ↦ hv (Prod.ext h h'))
      · exact Or.inl h
    have hkP : Set.MapsTo k P P' :=
      fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm))
    have hP : Set.MapsTo (ContinuousMap.id (G x)) P (U ∪ V) :=
      fun _ hv ↦ hP' (hkP hv)
    have hjU : Set.MapsTo j U A := by
      intro v hv
      change (qE ⟨x, v⟩).snd ≠ 0
      exact (congrArg (fun z : TE ↦ z.snd ≠ 0) (hqE x v)).mpr hv
    have hjV : Set.MapsTo j V B := by
      intro v hv
      change (qF ⟨x, v⟩).snd ≠ 0
      exact (congrArg (fun z : TF ↦ z.snd ≠ 0) (hqF x v)).mpr hv
    have hmapE : qE.comp j = (bundleFiberInclusion p E x).comp f := by
      apply ContinuousMap.ext
      exact hqE x
    have hmapF : qF.comp j = (bundleFiberInclusion q F x).comp g := by
      apply ContinuousMap.ext
      exact hqF x
    have hfactorE : relativeSingularCohomologyPullback R j hjU p a =
        relativeSingularCohomologyPullback R f (A := U) (B := {v | v ≠ 0})
          (fun _ hv ↦ hv) p (oE.fiberClass x) := by
      change relativeSingularCohomologyPullback R j hjU p
        (relativeSingularCohomologyPullback R qE hqEA p tE) = _
      erw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      simp only [hmapE]
      rw [relativeSingularCohomologyPullback_comp R f (bundleFiberInclusion p E x)
        (A := U) (B := {v : E x | v ≠ 0}) (C := bundleNonzero p E)
        (fun _ hv ↦ hv) (fun _ hv ↦ hv), ModuleCat.comp_apply]
      exact congrArg (relativeSingularCohomologyPullback R f (fun _ hv ↦ hv) p)
        ((existsUnique_cohomologyThomClass R p E oE).exists.choose_spec x)
    have hfactorF : relativeSingularCohomologyPullback R j hjV q b =
        relativeSingularCohomologyPullback R g (A := V) (B := {v | v ≠ 0})
          (fun _ hv ↦ hv) q (oF.fiberClass x) := by
      change relativeSingularCohomologyPullback R j hjV q
        (relativeSingularCohomologyPullback R qF hqFB q tF) = _
      erw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      simp only [hmapF]
      rw [relativeSingularCohomologyPullback_comp R g (bundleFiberInclusion q F x)
        (A := V) (B := {v : F x | v ≠ 0}) (C := bundleNonzero q F)
        (fun _ hv ↦ hv) (fun _ hv ↦ hv), ModuleCat.comp_apply]
      exact congrArg (relativeSingularCohomologyPullback R g (fun _ hv ↦ hv) q)
        ((existsUnique_cohomologyThomClass R q F oF).exists.choose_spec x)
    have hleft := restrictedRelativeCup_naturality j U V P A B N
      (isOpen_ne_fun f.continuous continuous_const) (isOpen_ne_fun g.continuous continuous_const)
      hA hB hP hN hjU hjV (fun _ hv ↦ hv) p q (p + q) rfl a b
    let a' : relativeSingularCohomology R U' p :=
      relativeSingularCohomologyPullback R (ContinuousMap.fst : C(E x × F x, E x))
        (A := U') (B := {v : E x | v ≠ 0})
        (fun _ hv ↦ hv) p (oE.fiberClass x)
    let b' : relativeSingularCohomology R V' q :=
      relativeSingularCohomologyPullback R (ContinuousMap.snd : C(E x × F x, F x))
        (A := V') (B := {v : F x | v ≠ 0})
        (fun _ hv ↦ hv) q (oF.fiberClass x)
    have hkU : Set.MapsTo k U U' := fun _ hv ↦ hv
    have hkV : Set.MapsTo k V V' := fun _ hv ↦ hv
    have hprodE : relativeSingularCohomologyPullback R k hkU p a' =
        relativeSingularCohomologyPullback R f (A := U) (B := {v | v ≠ 0})
          (fun _ hv ↦ hv) p (oE.fiberClass x) := by
      change relativeSingularCohomologyPullback R k hkU p
        (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(E x × F x, E x))
          (A := U') (B := {v : E x | v ≠ 0}) (fun _ hv ↦ hv) p _) = _
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    have hprodF : relativeSingularCohomologyPullback R k hkV q b' =
        relativeSingularCohomologyPullback R g (A := V) (B := {v | v ≠ 0})
          (fun _ hv ↦ hv) q (oF.fiberClass x) := by
      change relativeSingularCohomologyPullback R k hkV q
        (relativeSingularCohomologyPullback R (ContinuousMap.snd : C(E x × F x, F x))
          (A := V') (B := {v : F x | v ≠ 0}) (fun _ hv ↦ hv) q _) = _
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    have hright := restrictedRelativeCup_naturality k U V P U' V' P'
      (isOpen_ne_fun f.continuous continuous_const) (isOpen_ne_fun g.continuous continuous_const)
      (isOpen_ne_fun continuous_fst continuous_const)
      (isOpen_ne_fun continuous_snd continuous_const) hP hP' hkU hkV hkP p q (p + q) rfl a' b'
    have hcommon := congrArg₂ (restrictedRelativeCup U V P
      (isOpen_ne_fun f.continuous continuous_const) (isOpen_ne_fun g.continuous continuous_const)
      hP p q (p + q) rfl) (hfactorE.trans hprodE.symm) (hfactorF.trans hprodF.symm)
    exact hleft.trans (hcommon.trans (hright.symm.trans (ho x hP')))
  -- Multiplication by the inverse unit restores the prescribed fiber normalization.
  have hnormalized : ((ε⁻¹ : Rˣ) : R) • t = cohomologyThomClass R (p + q) G oG := by
    apply (existsUnique_cohomologyThomClass R (p + q) G oG).unique
    · intro x
      rw [map_smul]
      exact (congrArg (fun a ↦ ((ε⁻¹ : Rˣ) : R) • a) (hfiber x)).trans (by
        rw [smul_smul]
        simp)
    · exact (existsUnique_cohomologyThomClass R (p + q) G oG).exists.choose_spec
  have h := congrArg (fun a ↦ (ε : R) • a) hnormalized
  change t = (ε : R) • cohomologyThomClass R (p + q) G oG
  simpa only [smul_smul, Units.mul_inv, one_smul] using h

end AtiyahSinger
