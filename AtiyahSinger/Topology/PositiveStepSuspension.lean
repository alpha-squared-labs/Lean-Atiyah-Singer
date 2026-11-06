/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocalSuspensionEvaluation
public import AtiyahSinger.Topology.LocallyConstantSingularCohomology
public import AtiyahSinger.Topology.RelativeUnionCupBoundary
public import AtiyahSinger.Topology.RelativeUnionTripleBoundary

/-!
# Positive step classes and the actual local suspension

Public module ID: M1999.

The function equal to one on the positive half-line and zero on the negative
half-line gives the original one-dimensional relative class by the pair
coboundary. Its left cup product is normalized by the original local
suspension, with no interchange of the two factors.

Source: the relative cup and connecting-map calculation in Hatcher, Algebraic
Topology, Sections 3.2 and 3.3. All support changes use the specified original
excision and joint-chain comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Topology

universe u

variable (R : Type) [CommRing R]

/-- The positive step function of a continuous real function which never vanishes. -/
def positiveStepLocallyConstant {X : Type u} [TopologicalSpace X]
    (f : C(X, ℝ)) (hf : ∀ x, f x ≠ 0) : LocallyConstant X R := by
  have hclopen : IsClopen {x : X | 0 < f x} := by
    refine ⟨?_, isOpen_lt continuous_const f.continuous⟩
    have hset : {x : X | 0 < f x} = {x : X | 0 ≤ f x} := by
      ext x
      change 0 < f x ↔ 0 ≤ f x
      constructor
      · intro hx
        exact le_of_lt hx
      · intro hx
        exact lt_of_le_of_ne hx (Ne.symm (hf x))
    rw [hset]
    exact isClosed_le continuous_const f.continuous
  exact (LocallyConstant.const X (1 : R)).indicator hclopen

/-- The step function has the prescribed positive and negative values. -/
theorem positiveStepLocallyConstant_apply {X : Type u} [TopologicalSpace X]
    (f : C(X, ℝ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    positiveStepLocallyConstant R f hf x = if 0 < f x then 1 else 0 := by
  classical
  unfold positiveStepLocallyConstant
  dsimp only
  exact LocallyConstant.indicator_apply_eq_if _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A transverse class has a suspension lift whose restriction is the actual positive step cup. -/
theorem exists_positiveStep_suspension_lift (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) (a : relativeSingularCohomology R {y : E | y ≠ 0} k) :
    let X := ℝ × E
    let B : Set X := {z | z.1 ≠ 0}
    let A : Set X := {z | z.2 ≠ 0}
    let P : Set X := {z | z ≠ 0}
    let L := euclideanPuncturedHalfSpace E (-1)
    let i : C(B, P) := ⟨fun z ↦ ⟨z.val, fun h ↦ z.property (congrArg Prod.fst h)⟩,
      continuous_subtype_val.subtype_mk _⟩
    let t : C(B, ℝ) := ⟨fun z ↦ z.val.1, continuous_fst.comp continuous_subtype_val⟩
    let s := positiveStepLocallyConstant R t (fun z ↦ z.property)
    ∃ b : relativeSingularCohomology R ((Subtype.val : P → X) ⁻¹' L) k,
      relativeSingularCohomologyPullback R i
          (A := (Subtype.val : B → X) ⁻¹' A)
          (B := (Subtype.val : P → X) ⁻¹' L) (fun _ hz ↦ Or.inr hz) k b =
        cast (congrArg (fun j ↦ ↥(relativeSingularCohomology R
          ((Subtype.val : B → X) ⁻¹' A) j)) (Nat.zero_add k))
          (relativeSingularCohomologyAction R ((Subtype.val : B → X) ⁻¹' A) 0 k
            (locallyConstantSingularCohomologyClass R B s)
            (relativeSingularCohomologyPullback R
              (⟨fun z ↦ z.val.2, continuous_snd.comp continuous_subtype_val⟩ : C(B, E))
              (A := (Subtype.val : B → X) ⁻¹' A) (B := {y : E | y ≠ 0})
              (fun _ hz ↦ hz) k a)) ∧
      relativeSingularCohomologyPullback R (euclideanLocalSuspensionInclusion E)
          (A := (Subtype.val : euclideanPuncturedHalfSpace E 1 → X) ⁻¹' L)
          (B := (Subtype.val : P → X) ⁻¹' L) (fun _ hz ↦ hz) k b =
        relativeSingularCohomologyPullback R (euclideanLocalSuspensionProjection E)
          (euclideanLocalSuspensionProjection_mapsTo E) k a := by
  classical
  dsimp only
  let X := ℝ × E
  let B : Set X := {z | z.1 ≠ 0}
  let A : Set X := {z | z.2 ≠ 0}
  let P : Set X := {z | z ≠ 0}
  let L := euclideanPuncturedHalfSpace E (-1)
  let H := euclideanPuncturedHalfSpace E 1
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let LB : Set B := (Subtype.val : B → X) ⁻¹' L
  let LP : Set P := (Subtype.val : P → X) ⁻¹' L
  let LH : Set H := (Subtype.val : H → X) ⁻¹' L
  let N : Set B := {z | 0 < (-1 : ℝ) * z.val.1}
  let i : C(B, P) := ⟨fun z ↦ ⟨z.val, fun h ↦ z.property (congrArg Prod.fst h)⟩,
    continuous_subtype_val.subtype_mk _⟩
  let t : C(B, ℝ) := ⟨fun z ↦ z.val.1, continuous_fst.comp continuous_subtype_val⟩
  let s := positiveStepLocallyConstant R t (fun z ↦ z.property)
  let π : C(B, E) := ⟨fun z ↦ z.val.2, continuous_snd.comp continuous_subtype_val⟩
  have hs : ∀ z ∈ N, s z = 0 := by
    intro z hz
    change 0 < (-1 : ℝ) * z.val.1 at hz
    have hz' : z.val.1 < 0 := by simpa only [neg_one_mul, neg_pos] using hz
    rw [positiveStepLocallyConstant_apply]
    exact ite_eq_right (not_lt_of_ge (le_of_lt hz'))
  let sN := relativeLocallyConstantSingularCohomologyClass R B N s hs
  have hN : IsOpen N := isOpen_lt continuous_const
    (continuous_const.mul (continuous_fst.comp continuous_subtype_val))
  have hAB : IsOpen AB := (isOpen_ne_fun continuous_snd continuous_const).preimage
    continuous_subtype_val
  let aB := relativeSingularCohomologyPullback R π (A := AB) (B := {y : E | y ≠ 0})
    (fun _ hz ↦ hz) k a
  let v : relativeSingularCohomology R LB (0 + k) :=
    relativeSingularCohomologyUnionCup R N AB hN hAB 0 k sN aB
  let β : relativeSingularCohomology R LB k :=
    cast (congrArg (fun j ↦ ↥(relativeSingularCohomology R LB j)) (Nat.zero_add k)) v
  -- Excision lifts the positive-supported class from the nonzero first-coordinate locus.
  have hiex : IsOpenEmbedding i := by
    apply IsOpenEmbedding.of_comp i
      (isOpen_ne_fun continuous_id continuous_const).isOpenEmbedding_subtypeVal
    exact (isOpen_ne_fun continuous_fst continuous_const).isOpenEmbedding_subtypeVal
  have hexc {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
      (f : C(Y, Z)) (hf : IsOpenEmbedding f) (S : Set Z) (hS : IsOpen S)
      (hcover : Sᶜ ⊆ Set.range f) {T : Set Y} (hT : T = f ⁻¹' S)
      (hmap : Set.MapsTo f T S) : IsIso (relativeSingularCohomologyPullback R f hmap k) := by
    subst T
    have hchains : HomologicalComplex.homotopyEquivalences
        (ModuleCat.{u} R) (ComplexShape.down ℕ)
        (relativeSingularChainsMap R f (A := f ⁻¹' S) (B := S) hmap) := by
      have haux {A' : Set Y} {B' : Set Z} (hA : A' = (f ⁻¹' Sᶜ)ᶜ)
          (hB : B' = Sᶜᶜ) (hm : Set.MapsTo f A' B') :
          HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
            (relativeSingularChainsMap R f hm) := by
        subst A' B'
        exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding
          R f hf Sᶜ hS.isClosed_compl hcover
      exact haux (by simp only [Set.preimage_compl, compl_compl])
        (compl_compl S).symm hmap
    exact isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R _ hchains k
  let F := relativeSingularCohomologyPullback R i (A := LB) (B := LP) (fun _ hz ↦ hz) k
  have hLP : IsOpen LP := (isOpen_euclideanPuncturedHalfSpace E (-1)).preimage
    continuous_subtype_val
  have hcover : LPᶜ ⊆ Set.range i := by
    intro z hz
    have hy : z.val.2 = 0 := by
      by_contra h
      exact hz (Or.inr h)
    have ht : z.val.1 ≠ 0 := fun h ↦ z.property (Prod.ext h hy)
    exact ⟨⟨z.val, ht⟩, rfl⟩
  let : IsIso F := hexc i hiex LP hLP hcover rfl (fun _ hz ↦ hz)
  let b := inv F β
  have hFb : F b = β := by
    exact Iso.inv_hom_id_apply (asIso F) β
  have hforget : relativeSingularCohomologyRestriction R AB LB
      (fun _ hz ↦ Or.inr hz) k β =
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology R AB j)) (Nat.zero_add k))
        (relativeSingularCohomologyAction R AB 0 k
          (locallyConstantSingularCohomologyClass R B s) aB) := by
    have h := relativeSingularCohomologyUnionCup_restrict_right R N AB hN hAB 0 k sN aB
    rw [relativeLocallyConstantSingularCohomologyClass_toOrdinary] at h
    have hcast (j l : ℕ) (e : j = l) (w : relativeSingularCohomology R LB j) :
        relativeSingularCohomologyRestriction R AB LB (fun _ hz ↦ Or.inr hz) l
          (cast (congrArg (fun m ↦ ↥(relativeSingularCohomology R LB m)) e) w) =
        cast (congrArg (fun m ↦ ↥(relativeSingularCohomology R AB m)) e)
          (relativeSingularCohomologyRestriction R AB LB (fun _ hz ↦ Or.inr hz) j w) := by
      subst l
      rfl
    exact (hcast (0 + k) k (Nat.zero_add k) v).trans (congrArg
      (fun w ↦ cast (congrArg (fun j ↦ ↥(relativeSingularCohomology R AB j)) (Nat.zero_add k)) w) h)
  have hbB : relativeSingularCohomologyPullback R i (A := AB) (B := LP)
      (fun _ hz ↦ Or.inr hz) k b =
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology R AB j)) (Nat.zero_add k))
        (relativeSingularCohomologyAction R AB 0 k
          (locallyConstantSingularCohomologyClass R B s) aB) := by
    have hcomp := relativeSingularCohomologyPullback_comp R (ContinuousMap.id B) i
      (A := AB) (B := LB) (C := LP) (fun _ hz ↦ Or.inr hz) (fun _ hz ↦ hz) k
    have hmap : relativeSingularCohomologyPullback R i (A := AB) (B := LP)
        (fun _ hz ↦ Or.inr hz) k = F ≫
          relativeSingularCohomologyRestriction R AB LB (fun _ hz ↦ Or.inr hz) k := hcomp
    rw [hmap, ModuleCat.comp_apply, hFb]
    exact hforget
  refine ⟨b, hbB, ?_⟩
  -- On the strictly positive half-space, the same step is one; excision detects equality.
  let C : Set X := {z | 0 < z.1}
  let AC : Set C := (Subtype.val : C → X) ⁻¹' A
  let j : C(C, B) := ⟨fun z ↦ ⟨z.val, ne_of_gt z.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  let l : C(C, H) := ⟨fun z ↦ ⟨z.val, Or.inl (by
    rw [one_mul]
    exact z.property)⟩,
    continuous_subtype_val.subtype_mk _⟩
  have hl : IsOpenEmbedding l := by
    apply IsOpenEmbedding.of_comp l
      (isOpen_euclideanPuncturedHalfSpace E 1).isOpenEmbedding_subtypeVal
    exact (isOpen_lt continuous_const continuous_fst).isOpenEmbedding_subtypeVal
  have hpre : AC = l ⁻¹' LH := by
    ext z
    constructor
    · exact Or.inr
    · intro hz
      rcases hz with hz | hz
      · change 0 < (-1 : ℝ) * z.val.1 at hz
        have hn : z.val.1 < 0 := by simpa only [neg_one_mul, neg_pos] using hz
        exact False.elim (lt_asymm z.property hn)
      · exact hz
  have hHC : LHᶜ ⊆ Set.range l := by
    intro z hz
    have hy : z.val.2 = 0 := by
      by_contra h
      exact hz (Or.inr h)
    have ht : 0 < z.val.1 := by
      have hzH : 0 < 1 * z.val.1 ∨ z.val.2 ≠ 0 := z.property
      simpa only [one_mul, hy, ne_self_iff_false, or_false] using hzH
    exact ⟨⟨z.val, ht⟩, rfl⟩
  let J := relativeSingularCohomologyPullback R l (A := AC) (B := LH)
    (fun _ hz ↦ Or.inr hz) k
  let : IsIso J := hexc l hl LH
    ((isOpen_euclideanPuncturedHalfSpace E (-1)).preimage continuous_subtype_val)
    hHC hpre (fun _ hz ↦ Or.inr hz)
  apply (ConcreteCategory.isIso_iff_bijective J).mp inferInstance |>.injective
  have hleft : relativeSingularCohomologyPullback R (euclideanLocalSuspensionInclusion E)
        (A := LH) (B := LP) (fun _ hz ↦ hz) k ≫ J =
      relativeSingularCohomologyPullback R i (A := AB) (B := LP)
        (fun _ hz ↦ Or.inr hz) k ≫
      relativeSingularCohomologyPullback R j (A := AC) (B := AB) (fun _ hz ↦ hz) k := by
    rw [← relativeSingularCohomologyPullback_comp, ← relativeSingularCohomologyPullback_comp]
    rfl
  have hright : relativeSingularCohomologyPullback R (euclideanLocalSuspensionProjection E)
        (euclideanLocalSuspensionProjection_mapsTo E) k ≫ J =
      relativeSingularCohomologyPullback R π (A := AB) (B := {y : E | y ≠ 0}) (fun _ hz ↦ hz) k ≫
        relativeSingularCohomologyPullback R j (A := AC) (B := AB) (fun _ hz ↦ hz) k := by
    rw [← relativeSingularCohomologyPullback_comp, ← relativeSingularCohomologyPullback_comp]
    rfl
  change (relativeSingularCohomologyPullback R (euclideanLocalSuspensionInclusion E)
    (A := LH) (B := LP) (fun _ hz ↦ hz) k ≫ J) b =
      (relativeSingularCohomologyPullback R (euclideanLocalSuspensionProjection E)
        (euclideanLocalSuspensionProjection_mapsTo E) k ≫ J) a
  rw [hleft, hright,
    ModuleCat.comp_apply, ModuleCat.comp_apply, hbB]
  have hcast (m n : ℕ) (e : m = n) (w : relativeSingularCohomology R AB m) :
      relativeSingularCohomologyPullback R j (A := AC) (B := AB) (fun _ hz ↦ hz) n
        (cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R AB q)) e) w) =
      cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R AC q)) e)
        (relativeSingularCohomologyPullback R j (A := AC) (B := AB) (fun _ hz ↦ hz) m w) := by
    subst n
    rfl
  rw [hcast (0 + k) k (Nat.zero_add k), relativeSingularCohomologyPullback_action,
    locallyConstantSingularCohomologyClass_natural]
  have hsone : s.comap j = LocallyConstant.const C (1 : R) := by
    ext z
    exact (positiveStepLocallyConstant_apply R t (fun z ↦ z.property) (j z)).trans
      (ite_eq_left z.property)
  rw [hsone, locallyConstantSingularCohomologyClass_const, one_smul]
  have hcastIso (m n : ℕ) (e : m = n) (w : relativeSingularCohomology R AC m) :
      cast (congrArg (fun q ↦ ↥(relativeSingularCohomology R AC q)) e) w =
        (eqToIso (congrArg (fun q ↦ relativeSingularCohomology R AC q) e) :
          relativeSingularCohomology R AC m ≅ relativeSingularCohomology R AC n).hom w := by
    subst n
    rfl
  rw [hcastIso (0 + k) k (Nat.zero_add k)]
  exact relativeSingularCohomologyAction_one R AC k
    (relativeSingularCohomologyPullback R j (A := AC) (B := AB) (fun _ hz ↦ hz) k aB)

end AtiyahSinger
