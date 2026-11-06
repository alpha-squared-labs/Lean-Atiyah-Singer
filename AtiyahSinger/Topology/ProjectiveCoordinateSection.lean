/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexLineSectionClass
public import AtiyahSinger.Topology.HermitianProjectiveLocalCohomology
public import AtiyahSinger.Topology.ProjectiveTautologicalLine
public import AtiyahSinger.Topology.RelativeCohomologyContractibleProduct

/-!
# Projected coordinate sections and their affine Thom normalization

Public module ID: M2010.

Projecting a fixed vector gives a section of the actual tautological range line.
The affine frame is the vector e + v in the same range, with inner product one
against e. Pulling back the original line Thom class through this frame gives
the positive complex generator in its scalar coordinate. The contraction fixes
that scalar coordinate and therefore retains the original relative condition.

Source: the coordinate-section calculation of the tautological Euler class,
Milnor--Stasheff, Characteristic Classes, Sections 9 and 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open Bundle CategoryTheory

universe u

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

attribute [local instance] tautologicalLineTopology isFiniteRank_tautologicalLine

/-- Projection of a fixed vector is a section of the literal tautological range line. -/
def projectedSection (w : V) (P : HermitianProjectiveSpace V InnerProductSpace.toCore) :
    TautologicalLine V P :=
  ⟨P.val w, LinearMap.mem_range_self _ w⟩

/-- The projected section is continuous in the original induced total-space topology. -/
theorem continuous_projectedSection (w : V) :
    Continuous (fun P ↦ (⟨P, projectedSection V w P⟩ :
      TotalSpace Unit (TautologicalLine V))) := by
  apply continuous_induced_rng.mpr
  exact continuous_id.prodMk (continuous_subtype_val.clm_apply continuous_const)

/-- The specified affine frame sends a scalar to that scalar times the original vector e + v. -/
def tautologicalChartTotalMap (e : V) (he : ‖e‖ = 1) :
    C((innerSL ℂ e).ker × ULift.{u} ℂ, TotalSpace Unit (TautologicalLine V)) := by
  have hne (v : (innerSL ℂ e).ker) : e + v.val ≠ 0 := by
    intro hz
    have hee : inner ℂ e e = 1 := by rw [inner_self_eq_norm_sq_to_K, he]; simp
    have hinner : inner ℂ e (e + v.val) = 1 := by
      rw [inner_add_right, hee, show inner ℂ e v.val = 0 from v.property, add_zero]
    rw [hz, inner_zero_right] at hinner
    exact zero_ne_one hinner
  have hfixed (v : (innerSL ℂ e).ker) :
      (chartEmbedding e he v).val (e + v.val) = e + v.val := by
    change (ofVector (e + v.val) (hne v)).val (e + v.val) = _
    exact ofVector_apply_self _ _
  refine ⟨(fun z ↦ ⟨chartEmbedding e he z.1,
    ⟨z.2.down • (e + z.1.val), ?_⟩⟩), ?_⟩
  · refine ⟨z.2.down • (e + z.1.val), ?_⟩
    exact ((chartEmbedding e he z.1).val.map_smul z.2.down (e + z.1.val)).trans
      (congrArg (fun v ↦ z.2.down • v) (hfixed z.1))
  · apply continuous_induced_rng.mpr
    exact ((chartEmbedding e he).continuous.comp continuous_fst).prodMk
      ((continuous_uliftDown.comp continuous_snd).smul
        (continuous_const.add (continuous_subtype_val.comp continuous_fst)))

/-- The affine frame retains exactly the nonzero scalar locus. -/
theorem tautologicalChartTotalMap_nonzero_iff (e : V) (he : ‖e‖ = 1)
    (z : (innerSL ℂ e).ker × ULift.{u} ℂ) :
    (tautologicalChartTotalMap V e he z).snd ≠ 0 ↔ z.2 ≠ 0 := by
  constructor
  · intro h hz
    apply h
    apply Subtype.ext
    change z.2.down • (e + z.1.val) = 0
    rw [hz]
    simp
  · intro hz h
    have hee : inner ℂ e e = 1 := by rw [inner_self_eq_norm_sq_to_K, he]; simp
    have hez : inner ℂ e (e + z.1.val) = 1 := by
      rw [inner_add_right, hee, show inner ℂ e z.1.val = 0 from z.1.property, add_zero]
    have hv := congrArg Subtype.val h
    change z.2.down • (e + z.1.val) = 0 at hv
    have hc := congrArg (inner ℂ e) hv
    rw [inner_smul_right, hez, mul_one, inner_zero_right] at hc
    exact hz (ULift.ext hc)

set_option maxHeartbeats 600000 in


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same affine frame identifies the normalized line Thom class with its scalar generator. -/
theorem complexLineThomClass_pullback_tautologicalChart [FiniteDimensional ℂ V]
    (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (hmap : Set.MapsTo (tautologicalChartTotalMap V e he)
      {z : (innerSL ℂ e).ker × ULift.{u} ℂ | z.2 ≠ 0}
      {z : TotalSpace Unit (TautologicalLine V) | z.snd ≠ 0}) :
    relativeSingularCohomologyPullback ℤ (tautologicalChartTotalMap V e he) hmap 2
        (complexLineThomClass (TautologicalLine V) (fun P ↦ P.property.2.1)) =
      relativeSingularCohomologyPullback ℤ
        (ContinuousMap.snd : C((innerSL ℂ e).ker × ULift.{u} ℂ, ULift.{u} ℂ))
        (A := {z | z.2 ≠ 0}) (B := {z | z ≠ 0}) (fun _ hz ↦ hz) 2
        complexOrientationClass.{u} := by
  let P := ofVector e hne
  let L := TautologicalLine V
  let e' : L P := ⟨e, ⟨e, ofVector_apply_self e hne⟩⟩
  have he' : e' ≠ 0 := fun h ↦ hne (congrArg Subtype.val h)
  have hee : inner ℂ e e = 1 := by rw [inner_self_eq_norm_sq_to_K, he]; simp
  -- At the specified chart center the scalar coordinate is a positive complex-linear one.
  let c : L P ≃ₗ[ℂ] ℂ :=
    { toFun := fun v ↦ inner ℂ e v.val
      invFun := fun a ↦ a • e'
      map_add' := fun v w ↦ inner_add_right e v.val w.val
      map_smul' := fun a v ↦ inner_smul_right e v.val a
      left_inv := by
        intro v
        obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_eq_one P.property.2.1 he' v
        change (inner ℂ e (a • e)) • e' = a • e'
        rw [inner_smul_right, hee, mul_one]
      right_inv := by
        intro a
        change inner ℂ e (a • e) = a
        rw [inner_smul_right, hee, mul_one] }
  let d := c.toContinuousLinearEquiv
  let S := {z : (innerSL ℂ e).ker × ULift.{u} ℂ | z.2 ≠ 0}
  let A := {z : ULift.{u} ℂ | z ≠ 0}
  let T := {z : TotalSpace Unit L | z.snd ≠ 0}
  let f := tautologicalChartTotalMap V e he
  let s : C(ULift.{u} ℂ, (innerSL ℂ e).ker × ULift.{u} ℂ) :=
    ⟨fun z ↦ (0, z), continuous_const.prodMk continuous_id⟩
  let a := relativeSingularCohomologyPullback ℤ f hmap 2
    (complexLineThomClass L (fun Q ↦ Q.property.2.1))
  have hs : Set.MapsTo s A S := fun _ hz ↦ hz
  have hfs : f.comp s = complexLineFiberMap L P d := by
    apply ContinuousMap.ext
    intro z
    have hp : chartEmbedding e he 0 = P :=
      (chartEmbedding_eq_ofVector_iff e he hne 0).mpr rfl
    apply TotalSpace.ext hp
    change HEq (show L (chartEmbedding e he 0) from _) (d.symm z.down)
    apply (Subtype.heq_iff_coe_eq (fun x ↦ by rw [hp])).mpr
    change z.down • (e + (0 : (innerSL ℂ e).ker).val) = z.down • e
    simp
  have hfiber : relativeSingularCohomologyPullback ℤ s hs 2 a =
      complexOrientationClass.{u} := by
    change relativeSingularCohomologyPullback ℤ s hs 2
      (relativeSingularCohomologyPullback ℤ f hmap 2
        (complexLineThomClass L (fun Q ↦ Q.property.2.1))) = _
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    have hcongr (g₁ g₂ : C(ULift.{u} ℂ, TotalSpace Unit L)) (h : g₁ = g₂)
        (h₁ : Set.MapsTo g₁ A T) (h₂ : Set.MapsTo g₂ A T) :
        relativeSingularCohomologyPullback ℤ g₁ h₁ 2 =
          relativeSingularCohomologyPullback ℤ g₂ h₂ 2 := by
      subst g₂
      rfl
    have hd : Set.MapsTo (complexLineFiberMap L P d) A T := by
      intro z hz hzero
      apply hz
      apply ULift.ext
      exact d.symm.injective (hzero.trans d.symm.map_zero.symm)
    rw [hcongr _ _ hfs _ hd]
    exact complexLineThomClass_fiber L (fun Q ↦ Q.property.2.1) P d
  -- Contract the affine base while retaining every nonzero scalar in the same relative pair.
  have hprod := relativeSingularCohomology_prod_eq_pullback_fiber ℤ
    (0 : (innerSL ℂ e).ker) A 2 a
  change relativeSingularCohomologyPullback ℤ ContinuousMap.snd
      (A := S) (B := A) (fun _ hz ↦ hz) 2
      (relativeSingularCohomologyPullback ℤ s hs 2 a) = a at hprod
  rw [hfiber] at hprod
  exact hprod.symm

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
