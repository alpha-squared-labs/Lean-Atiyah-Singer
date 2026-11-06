/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.PositiveStepSuspension

/-!
# Positive one-dimensional cup evaluation

Public module ID: M1997.

The positive step coboundary in the first coordinate cups with a transverse
local class according to the original homology suspension. This comparison
uses the actual two-support cup, retaining the order of both factors.

Source: the positive-half-line normalization and the relative connecting-map
formula, Hatcher, Algebraic Topology, Sections 3.2 and 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex

universe u

variable (R : Type) [CommRing R]

/-- The pair coboundary of the positive step function of a real-valued coordinate. -/
def positiveStepBoundaryClass {X : Type u} [TopologicalSpace X] (f : C(X, ℝ)) :
    relativeSingularCohomology R {x : X | f x ≠ 0} 1 :=
  let B : Set X := {x | f x ≠ 0}
  let t : C(B, ℝ) := ⟨fun x ↦ f x.val, f.continuous.comp continuous_subtype_val⟩
  (shortExact_singularSubspaceCochains R B).δ 0 1 rfl
    (locallyConstantSingularCohomologyClass R B
      (positiveStepLocallyConstant R t (fun x ↦ x.property)))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Cup with the positive first-coordinate class evaluates by the original local suspension. -/
theorem positiveStepBoundaryClass_cup_evaluation (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (a : relativeSingularCohomology R {y : E | y ≠ 0} k)
    (c : relativeSingularHomology R {z : ℝ × E | z ≠ 0} (k + 1))
    (hP : Set.MapsTo (ContinuousMap.id (ℝ × E)) {z : ℝ × E | z ≠ 0}
      ({z : ℝ × E | z.1 ≠ 0} ∪ {z : ℝ × E | z.2 ≠ 0})) :
    singularCochainHomologyEvaluation R
        (relativeSingularChains R {z : ℝ × E | z ≠ 0}) (k + 1)
        (cast (congrArg (fun j ↦ ↥(relativeSingularCohomology R
          {z : ℝ × E | z ≠ 0} j)) (Nat.add_comm 1 k))
          (relativeSingularCohomologyPullback R (ContinuousMap.id (ℝ × E)) hP (1 + k)
            (relativeSingularCohomologyUnionCup R
              {z : ℝ × E | z.1 ≠ 0} {z : ℝ × E | z.2 ≠ 0}
              (isOpen_ne_fun continuous_fst continuous_const)
              (isOpen_ne_fun continuous_snd continuous_const) 1 k
              (positiveStepBoundaryClass R (⟨Prod.fst, continuous_fst⟩ : C(ℝ × E, ℝ)))
              (relativeSingularCohomologyPullback R
                (⟨Prod.snd, continuous_snd⟩ : C(ℝ × E, E))
                (A := {z : ℝ × E | z.2 ≠ 0}) (B := {y : E | y ≠ 0})
                (fun _ h ↦ h) k a)))) c =
      singularCochainHomologyEvaluation R (relativeSingularChains R {y : E | y ≠ 0}) k a
        ((euclideanLocalSuspensionIso R E k).hom c) := by
  let X := ℝ × E
  let A : Set X := {z | z.2 ≠ 0}
  let B : Set X := {z | z.1 ≠ 0}
  let U := B ∪ A
  let P : Set X := {z | z ≠ 0}
  let L := euclideanPuncturedHalfSpace E (-1)
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let LP : Set P := (Subtype.val : P → X) ⁻¹' L
  let LU : Set U := (Subtype.val : U → X) ⁻¹' L
  let t : C(B, ℝ) := ⟨fun z ↦ z.val.1, continuous_fst.comp continuous_subtype_val⟩
  let s := locallyConstantSingularCohomologyClass R B
    (positiveStepLocallyConstant R t (fun z ↦ z.property))
  let π : C(X, E) := ⟨Prod.snd, continuous_snd⟩
  let aX := relativeSingularCohomologyPullback R π (A := A) (B := {y : E | y ≠ 0})
    (fun _ h ↦ h) k a
  let ξ := relativeSingularCohomologyAction R AB 0 k s
    (relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
      (A := AB) (B := A) (fun _ h ↦ h) k aX)
  have hA : IsOpen A := isOpen_ne_fun continuous_snd continuous_const
  have hB : IsOpen B := isOpen_ne_fun continuous_fst continuous_const
  let product := relativeSingularCohomologyUnionCup R B A hB hA 1 k
    ((shortExact_singularSubspaceCochains R B).δ 0 1 rfl s) aX
  have hUP : U ⊆ P := by
    intro z hz heq
    rcases hz with hz | hz
    · exact hz (congrArg Prod.fst heq)
    · exact hz (congrArg Prod.snd heq)
  have hAL : A ⊆ L := fun _ h ↦ Or.inr h
  have hLU : L ⊆ U := by
    intro z hz
    rcases hz with ht | hy
    · left
      intro h
      simp only [h, mul_zero, lt_self_iff_false] at ht
    · exact Or.inr hy
  have hLP := euclideanPuncturedHalfSpace_subset E (-1)
  let i : C(B, P) := ⟨fun z ↦ ⟨z.val, fun h ↦ z.property (congrArg Prod.fst h)⟩,
    continuous_subtype_val.subtype_mk _⟩
  let j : C(U, P) := ⟨fun z ↦ ⟨z.val, hUP z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  let iU : C(B, U) := ⟨fun z ↦ ⟨z.val, Or.inl z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  obtain ⟨b, hb, hbH⟩ := exists_positiveStep_suspension_lift R E k a
  have hb' : relativeSingularCohomologyPullback R i (A := AB) (B := LP)
      (fun _ h ↦ Or.inr h) k b =
        cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R AB q)) (Nat.zero_add k)) ξ := by
    have hcomp := relativeSingularCohomologyPullback_comp R (ContinuousMap.subtypeVal B) π
      (A := AB) (B := A) (C := {y : E | y ≠ 0}) (fun _ h ↦ h) (fun _ h ↦ h) k
    have hvalue := congrArg (fun f ↦ f a) hcomp
    change relativeSingularCohomologyPullback R
      (⟨fun z ↦ z.val.2, continuous_snd.comp continuous_subtype_val⟩ : C(B, E))
      (A := AB) (B := {y : E | y ≠ 0}) (fun _ h ↦ h) k a =
        relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
          (A := AB) (B := A) (fun _ h ↦ h) k aX at hvalue
    exact hb.trans (congrArg (fun z ↦ cast
      (congrArg (fun q ↦ ↥(relativeSingularCohomology R AB q)) (Nat.zero_add k))
      (relativeSingularCohomologyAction R AB 0 k s z)) hvalue)
  let bU := relativeSingularCohomologyPullback R j (A := LU) (B := LP)
    (fun _ h ↦ h) k b
  let F (n : ℕ) := relativeSingularCohomologyPullback R (ContinuousMap.id X)
    (A := U) (B := P) (fun _ h ↦ hUP h) n
  let G (n : ℕ) := relativeSingularCohomologyPullback R (ContinuousMap.id X)
    (A := P) (B := U) hP n
  let d := (shortExact_relativeSingularCochainTripleSequence R L P hLP).δ k (k + 1) rfl b
  let T := relativeUnionSingularCochainSequence R A B
  have hT := shortExact_relativeUnionSingularCochainSequence R A B
  -- Naturality first transports the same triple to the actual union pair.
  have hd : F (k + 1) d =
      (shortExact_relativeSingularCochainTripleSequence R L U hLU).δ k (k + 1) rfl bU := by
    exact congrArg (fun f ↦ f b) (relativeSingularCohomologyTripleBoundary_natural R
      (ContinuousMap.id X) hLU hLP (fun _ h ↦ h) (fun _ h ↦ hUP h) k)
  have hrestrict : relativeSingularCohomologyPullback R iU (A := AB) (B := LU)
      (fun _ h ↦ Or.inr h) k bU =
      relativeSingularCohomologyPullback R i (A := AB) (B := LP)
        (fun _ h ↦ Or.inr h) k b := by
    exact (congrArg (fun f ↦ f b) (relativeSingularCohomologyPullback_comp R iU j
      (A := AB) (B := LU) (C := LP) (fun _ h ↦ Or.inr h) (fun _ h ↦ h) k)).symm
  have htriple : relativeUnionCohomologyComparison R B A (k + 1) (F (k + 1) d) =
      hT.δ k (k + 1) rfl
        (cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R AB q))
          (Nat.zero_add k)) ξ) := by
    rw [hd]
    have h := congrArg (fun f ↦ f bU)
      (relativeUnionSingularCohomologyBoundary_triple R A B L hAL hLU k)
    change relativeUnionCohomologyComparison R B A (k + 1)
        ((shortExact_relativeSingularCochainTripleSequence R L U hLU).δ k (k + 1) rfl bU) =
      hT.δ k (k + 1) rfl
        (relativeSingularCohomologyPullback R iU (A := AB) (B := LU)
          (fun _ h ↦ Or.inr h) k bU) at h
    exact h.trans (congrArg (fun z ↦ hT.δ k (k + 1) rfl z) (hrestrict.trans hb'))
  -- Transport degrees in the original connecting map; no sign accompanies these casts.
  have hδcast (m n : ℕ) (h : m = n) (z : T.X₃.homology m) :
      hT.δ n (n + 1) rfl (cast (congrArg (fun q ↦ ↥(T.X₃.homology q)) h) z) =
      cast (congrArg (fun q ↦ ↥(T.X₁.homology q)) (congrArg (· + 1) h))
        (hT.δ m (m + 1) rfl z) := by
    subst n
    rfl
  have hcastIso {V W : ModuleCat.{u} R} (h : V = W) (z : V) :
      (eqToIso h).hom z = cast (congrArg ModuleCat.carrier h) z := by
    subst W
    rfl
  have hcup := relativeUnionSingularCohomologyBoundary_cup R A B hA hB 0 k s aX
  rw [hcastIso] at hcup
  have hcompcast (m n : ℕ) (h : m = n) (z : relativeSingularCohomology R U m) :
      relativeUnionCohomologyComparison R B A n
        (cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R U q)) h) z) =
      cast (congrArg (fun q ↦ ↥(relativeUnionSingularCohomology R B A q)) h)
        (relativeUnionCohomologyComparison R B A m z) := by
    subst n
    rfl
  have hFd : F (k + 1) d =
      cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R U q))
        (Nat.add_comm 1 k)) product := by
    apply (relativeUnionCohomologyComparison_bijective R B A hB hA (k + 1)).injective
    calc
      _ = _ := htriple
      _ = cast (congrArg (fun q ↦ ↥(T.X₁.homology q))
          (congrArg (· + 1) (Nat.zero_add k)))
          (hT.δ (0 + k) (0 + k + 1) rfl ξ) := hδcast (0 + k) k (Nat.zero_add k) ξ
      _ = cast (congrArg (fun q ↦ ↥(relativeUnionSingularCohomology R B A q))
          (Nat.add_comm 1 k)) (relativeUnionCohomologyComparison R B A (1 + k) product) := by
        have h := congrArg (fun z : T.X₁.homology (0 + k + 1) ↦
          cast (congrArg (fun q ↦ ↥(T.X₁.homology q))
            (congrArg (· + 1) (Nat.zero_add k))) z) hcup
        refine h.trans ?_
        simp only [cast_cast]
        rfl
      _ = _ := (hcompcast (1 + k) (k + 1) (Nat.add_comm 1 k) product).symm
  -- The two identity pair maps are inverse, and the resulting class is the same cup.
  have hFG : F (k + 1) ≫ G (k + 1) = 𝟙 _ := by
    rw [← relativeSingularCohomologyPullback_comp]
    simp [relativeSingularCohomologyPullback, relativeSingularChainsMap, Limits.cokernel.map]
  have hGcast (m n : ℕ) (h : m = n) (z : relativeSingularCohomology R U m) :
      G n (cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R U q)) h) z) =
      cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R P q)) h) (G m z) := by
    subst n
    rfl
  have hprod : cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R P q))
      (Nat.add_comm 1 k)) (G (1 + k) product) = d := by
    rw [← hGcast (1 + k) (k + 1) (Nat.add_comm 1 k), ← hFd]
    exact congrArg (fun f ↦ f d) hFG
  change singularCochainHomologyEvaluation R (relativeSingularChains R P) (k + 1)
    (cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R P q))
      (Nat.add_comm 1 k)) (G (1 + k) product)) c = _
  rw [hprod]
  exact euclideanLocalSuspensionIso_evaluation R E k a b hbH c

end AtiyahSinger
