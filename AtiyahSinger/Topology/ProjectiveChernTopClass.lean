/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexCoordinateCupGenerator
public import AtiyahSinger.Topology.ProjectiveSectionThom
public import AtiyahSinger.Topology.RelativeCohomologyFiniteCup

/-!
# A projective top Chern power localized at its specified center

Public module ID: M2008.

The projections of an orthonormal basis of the perpendicular hyperplane vanish
simultaneously exactly at the chosen projective point. Their localized first
Chern classes therefore have a finite relative cup product supported at that
point. Its ordinary image is the top power of the original tautological class.

Source: the coordinate-section construction of the top projective Chern power,
Milnor--Stasheff, Characteristic Classes, Sections 9 and 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open Bundle CategoryTheory
open scoped ComplexOrder

universe u

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

attribute [local instance] tautologicalLineTopology isFiniteRank_tautologicalLine

/-- The perpendicular coordinate sections vanish simultaneously only at the specified center. -/
theorem iUnion_projectedSection_nonzero (m : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (b : OrthonormalBasis (Fin m) ℂ (innerSL ℂ e).ker) :
    (⋃ i : Fin m, {P | projectedSection V (b i).val P ≠ 0}) =
      {P | P ≠ ofVector e hne} := by
  classical
  let W := (innerSL ℂ e).ker
  let Q := ofVector e hne
  have hW : (ℂ ∙ e)ᗮ = W := by
    ext v
    exact Submodule.mem_orthogonal_singleton_iff_inner_right
  ext P
  constructor
  · intro h hPQ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    apply hi
    apply Subtype.ext
    change P.val (b i).val = 0
    rw [hPQ, apply_eq_inner_smul Q e he (ofVector_apply_self e hne)]
    rw [show inner ℂ e (b i).val = 0 from (b i).property, zero_smul]
  · intro hPQ
    by_contra hn
    have hcoords (i : Fin m) : P.val (b i).val = 0 := by
      have hz : projectedSection V (b i).val P = 0 :=
        not_not.mp (fun hi ↦ hn (Set.mem_iUnion.mpr ⟨i, hi⟩))
      exact congrArg Subtype.val hz
    let f : W →ₗ[ℂ] V := P.val.toLinearMap.comp W.subtype
    have hf : f = 0 := b.toBasis.ext fun i ↦ hcoords i
    have hzero (v : W) : P.val v.val = 0 := LinearMap.congr_fun hf v
    -- Self-adjointness makes the range perpendicular to every vector in the coordinate hyperplane.
    have hle : LinearMap.range P.val.toLinearMap ≤ ℂ ∙ e := by
      intro y hy
      rw [← Submodule.orthogonal_orthogonal (ℂ ∙ e), hW]
      apply (W.mem_orthogonal y).mpr
      intro v hv
      obtain ⟨z, rfl⟩ := hy
      change inner ℂ v (P.val z) = 0
      rw [← P.property.2.2 v z, hzero ⟨v, hv⟩, inner_zero_left]
    have hrange : LinearMap.range P.val.toLinearMap = ℂ ∙ e :=
      Submodule.eq_of_le_of_finrank_eq hle
        (P.property.2.1.trans (finrank_span_singleton hne).symm)
    have heRange : e ∈ LinearMap.range P.val.toLinearMap := by
      rw [hrange]
      exact Submodule.mem_span_singleton_self e
    have hPe : P.val e = e := by
      obtain ⟨z, rfl⟩ := heRange
      exact congrArg (fun f : V →L[ℂ] V ↦ f z) P.property.1
    exact hPQ (eq_of_fixed_nonzero P Q e hne hPe (ofVector_apply_self e hne))

/-- The integral product of the localized coordinate classes at the specified projective point. -/
def projectiveTopSectionClass (m : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (b : OrthonormalBasis (Fin m) ℂ (innerSL ℂ e).ker) :
    relativeSingularCohomology ℤ
      {P : HermitianProjectiveSpace V InnerProductSpace.toCore | P ≠ ofVector e hne} (2 * m) := by
  let U (i : Fin m) := {P | projectedSection V (b i).val P ≠ 0}
  have hU (i : Fin m) : IsOpen (U i) := by
    have heq : U i = {P | P.val (b i).val ≠ 0} := by
      ext P
      exact not_congr Subtype.ext_iff
    rw [heq]
    exact isOpen_affineChart_source (b i).val
  let a (i : Fin m) := complexLineSectionClass (TautologicalLine V)
    (fun P ↦ P.property.2.1) (projectedSection V (b i).val)
    (continuous_projectedSection V (b i).val)
  exact (eqToIso (congrArg (fun S ↦ relativeSingularCohomology ℤ S (2 * m))
    (iUnion_projectedSection_nonzero V m e he hne b))).hom
      (relativeSingularCohomologyFiniteCup ℤ m U hU a)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Forgetting the specified point support recovers the original top tautological Chern power. -/
theorem projectiveTopSectionClass_toOrdinary (m : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (b : OrthonormalBasis (Fin m) ℂ (innerSL ℂ e).ker) :
    relativeSingularCohomologyToOrdinary ℤ {P | P ≠ ofVector e hne} (2 * m)
        (projectiveTopSectionClass V m e he hne b) =
      singularCohomologyDegreeTwoPow ℤ (HermitianProjectiveSpace V InnerProductSpace.toCore)
        (tautologicalChernRoot V) m := by
  have hset (A B : Set (HermitianProjectiveSpace V InnerProductSpace.toCore)) (h : A = B)
      (a : relativeSingularCohomology ℤ A (2 * m)) :
      relativeSingularCohomologyToOrdinary ℤ B (2 * m)
          ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology ℤ S (2 * m)) h)).hom a) =
        relativeSingularCohomologyToOrdinary ℤ A (2 * m) a := by
    subst B
    rfl
  -- Every factor forgets to the same original first Chern class of the actual line.
  apply singularEvenCohomologyOf_injective ℤ
    (HermitianProjectiveSpace V InnerProductSpace.toCore) m
  unfold projectiveTopSectionClass
  rw [hset _ _ (iUnion_projectedSection_nonzero V m e he hne b),
    relativeSingularCohomologyFiniteCup_toOrdinary, singularEvenCohomologyOf_degreeTwoPow]
  simp_rw [complexLineSectionClass_toOrdinary]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

set_option maxHeartbeats 600000 in
-- The comparison retains dependent bundle fibers and both canonical support transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified projective top class is the coordinate Thom product in its original chart. -/
theorem projectiveTopSectionClass_pullback [FiniteDimensional ℂ V]
    (m : ℕ) (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (b : OrthonormalBasis (Fin m) ℂ (innerSL ℂ e).ker) :
    relativeSingularCohomologyPullback ℤ (chartEmbedding e he)
        (A := {v | v ≠ 0}) (B := {P | P ≠ ofVector e hne})
        (fun v hv hz ↦ hv ((chartEmbedding_eq_ofVector_iff e he hne v).mp hz)) (2 * m)
        (projectiveTopSectionClass V m e he hne b) = complexCoordinateCup m b := by
  let W := (innerSL ℂ e).ker
  let p := chartEmbedding e he
  let U (i : Fin m) := {P | projectedSection V (b i).val P ≠ 0}
  let S (i : Fin m) := {v : W | inner ℂ v (b i) ≠ 0}
  have hU (i : Fin m) : IsOpen (U i) := by
    have heq : U i = {P | P.val (b i).val ≠ 0} := by
      ext P
      exact not_congr Subtype.ext_iff
    rw [heq]
    exact isOpen_affineChart_source (b i).val
  have hS (i : Fin m) : IsOpen (S i) :=
    isOpen_ne_fun (continuous_id.inner continuous_const) continuous_const
  -- Every coordinate nonzero locus maps to the nonzero locus of its actual projected section.
  have hf (i : Fin m) : Set.MapsTo p (S i) (U i) := by
    intro v hv hz
    let P := p v
    have hPe : P.val e ≠ 0 := ((chart e he).symm v).property
    have hid : P.val (P.val e) = P.val e :=
      congrArg (fun f : V →L[ℂ] V ↦ f e) P.property.1
    have hd : inner ℂ e (P.val e) ≠ 0 := by
      have heq : inner ℂ e (P.val e) = inner ℂ (P.val e) (P.val e) := by
        rw [P.property.2.2, hid]
      rw [heq]
      exact fun h ↦ hPe (inner_self_eq_zero.mp h)
    have hee : inner ℂ e e = 1 := by rw [inner_self_eq_norm_sq_to_K, he]; simp
    have hex : inner ℂ e (e + v.val) = 1 := by
      rw [inner_add_right, hee, show inner ℂ e v.val = 0 from v.property, add_zero]
    have hzv : P.val (b i).val = 0 := congrArg Subtype.val hz
    rw [projectedSection_chart_formula V e he v (b i)] at hzv
    have hcoord := congrArg (inner ℂ e) hzv
    rw [inner_smul_right, hex, mul_one, inner_zero_right] at hcoord
    exact hv ((mul_eq_zero.mp hcoord).resolve_left hd)
  have hall : Set.MapsTo p (⋃ i, S i) (⋃ i, U i) := by
    intro v hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨i, hf i hi⟩
  have hp : Set.MapsTo p {v | v ≠ 0} {P | P ≠ ofVector e hne} :=
    fun v hv hz ↦ hv ((chartEmbedding_eq_ofVector_iff e he hne v).mp hz)
  have hset (A A' : Set W)
      (B B' : Set (HermitianProjectiveSpace V InnerProductSpace.toCore))
      (hA : A = A') (hB : B = B') (hf : Set.MapsTo p A B) (hf' : Set.MapsTo p A' B')
      (a : relativeSingularCohomology ℤ B (2 * m)) :
      relativeSingularCohomologyPullback ℤ p hf' (2 * m)
          ((eqToIso (congrArg (fun T ↦ relativeSingularCohomology ℤ T (2 * m)) hB)).hom a) =
        (eqToIso (congrArg (fun T ↦ relativeSingularCohomology ℤ T (2 * m)) hA)).hom
          (relativeSingularCohomologyPullback ℤ p hf (2 * m) a) := by
    subst A'
    subst B'
    rfl
  let a (i : Fin m) := complexLineSectionClass (TautologicalLine V)
    (fun P ↦ P.property.2.1) (projectedSection V (b i).val)
    (continuous_projectedSection V (b i).val)
  -- Naturality uses this one map for the whole support family, in the same finite order.
  have hn := relativeSingularCohomologyPullback_finiteCup ℤ p m S U hS hU hf a
  have hlocal (i : Fin m) : relativeSingularCohomologyPullback ℤ p (hf i) 2 (a i) =
      relativeSingularCohomologyPullback ℤ
        (⟨fun v : W ↦ ULift.up (inner ℂ v (b i)),
          continuous_uliftUp.comp (continuous_id.inner continuous_const)⟩ : C(W, ULift.{u} ℂ))
        (A := S i) (B := {z | z ≠ 0})
        (fun _ hv hz ↦ hv (congrArg ULift.down hz)) 2 complexOrientationClass.{u} :=
    complexLineSectionClass_projectedSection_pullback V e he hne (b i) (hf i)
  simp_rw [hlocal] at hn
  exact (hset (⋃ i, S i) {v | v ≠ 0} (⋃ i, U i) {P | P ≠ ofVector e hne}
    (iUnion_complexCoordinateNonzero m b) (iUnion_projectedSection_nonzero V m e he hne b)
    hall hp (relativeSingularCohomologyFiniteCup ℤ m U hU a)).trans (congrArg _ hn)

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
