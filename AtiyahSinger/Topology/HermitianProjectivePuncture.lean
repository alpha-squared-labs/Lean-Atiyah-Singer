/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveSubspace
public import Mathlib.Topology.Homotopy.Equiv

/-!
# A deleted point in orthogonal projective space

Public module ID: M1900.

Projection onto the orthogonal complement of a line fails exactly at that
projective point. The actual projective subspace deformation therefore gives
a homotopy equivalence from the deleted-point space to the lower-dimensional
projective space. Its maps retain the specified orthogonal projection and
inclusion, so products with any parameter space retain that parameter.

The affine chart centered at a unit vector sends precisely the specified
projective point to zero. This identifies the same puncture for relative
cohomology excision, without a change of projective model or of reference line.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open scoped ContinuousMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- Orthogonal projection onto the complementary hyperplane kills exactly its missing line. -/
theorem orthogonalProjectionOnto_comp_eq_zero_iff (e : V) (he : e ≠ 0)
    (P : HermitianProjectiveSpace V InnerProductSpace.toCore) :
    (Submodule.span ℂ {e})ᗮ.orthogonalProjectionOnto.comp P.val = 0 ↔
      P = ofVector e he := by
  let K := (Submodule.span ℂ {e})ᗮ
  have hker (v : V) : K.orthogonalProjectionOnto v = 0 ↔
      v ∈ Submodule.span ℂ {e} := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
    exact Iff.of_eq (congrArg (fun S : Submodule ℂ V ↦ v ∈ S)
      (Submodule.orthogonal_orthogonal (Submodule.span ℂ {e})))
  constructor
  · intro hz
    -- A nonzero range vector lies in the missing line and fixes both projectors.
    obtain ⟨v, hv⟩ : ∃ v : V, P.val v ≠ 0 := by
      by_contra hzero
      push Not at hzero
      have hP : P.val = 0 := ContinuousLinearMap.ext hzero
      have hlin : P.val.toLinearMap = 0 := congrArg ContinuousLinearMap.toLinearMap hP
      have hr := P.property.2.1
      rw [hlin, LinearMap.range_zero] at hr
      simp at hr
    have hmem : P.val v ∈ Submodule.span ℂ {e} :=
      (hker _).mp (congrArg (fun L : V →L[ℂ] K ↦ L v) hz)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    apply eq_of_fixed_nonzero P (ofVector e he) (P.val v) hv
    · exact congrArg (fun L : V →L[ℂ] V ↦ L v) P.property.1
    · rw [← ha, map_smul, ofVector_apply_self]
  · rintro rfl
    -- Every vector in this rank-one range is a multiple of the same fixed e.
    apply ContinuousLinearMap.ext
    intro v
    let Q := ofVector e he
    let w : LinearMap.range Q.val.toLinearMap := ⟨e, ⟨e, ofVector_apply_self e he⟩⟩
    have hw : w ≠ 0 := fun hz ↦ he (congrArg Subtype.val hz)
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one Q.property.2.1 hw
      (⟨Q.val v, LinearMap.mem_range_self _ v⟩ : LinearMap.range Q.val.toLinearMap)
    have hav : a • e = Q.val v := congrArg Subtype.val ha
    change K.orthogonalProjectionOnto (Q.val v) = 0
    rw [← hav, map_smul, (hker e).mpr (Submodule.mem_span_singleton_self e), smul_zero]

/-- Removing one projective point retracts onto its actual orthogonal projective hyperplane. -/
def puncturedHomotopyEquiv (e : V) (he : e ≠ 0) :
    {P : HermitianProjectiveSpace V InnerProductSpace.toCore // P ≠ ofVector e he} ≃ₕ
      HermitianProjectiveSpace (Submodule.span ℂ {e})ᗮ InnerProductSpace.toCore := by
  let K := (Submodule.span ℂ {e})ᗮ
  let d : {P : HermitianProjectiveSpace V InnerProductSpace.toCore // P ≠ ofVector e he} ≃ₜ
      SubspaceDomain K :=
    { toFun := fun P ↦ ⟨P.val, fun hz ↦ P.property
        ((orthogonalProjectionOnto_comp_eq_zero_iff e he P.val).mp hz)⟩
      invFun := fun P ↦ ⟨P.val, fun hz ↦ P.property
        ((orthogonalProjectionOnto_comp_eq_zero_iff e he P.val).mpr hz)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  let h : SubspaceDomain K ≃ₕ HermitianProjectiveSpace K InnerProductSpace.toCore :=
    { toFun := subspaceRetraction K
      invFun := subspaceSection K
      left_inv := ⟨subspaceDeformation K⟩
      right_inv := by rw [subspaceRetraction_comp_section] }
  exact d.toHomotopyEquiv.trans h

omit [FiniteDimensional ℂ V] in
/-- The affine chart carries its specified projective center to precisely the origin. -/
theorem chart_apply_eq_zero_iff (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (P : {P : HermitianProjectiveSpace V InnerProductSpace.toCore // P.val e ≠ 0}) :
    chart e he P = 0 ↔ P.val = ofVector e hne := by
  let Q : {P : HermitianProjectiveSpace V InnerProductSpace.toCore // P.val e ≠ 0} :=
    ⟨ofVector e hne, by rwa [ofVector_apply_self]⟩
  have hQ : chart e he Q = 0 := by
    apply Subtype.ext
    change (inner ℂ e ((ofVector e hne).val e))⁻¹ • (ofVector e hne).val e - e = 0
    rw [ofVector_apply_self, inner_self_eq_norm_sq_to_K, he]
    simp
  rw [← hQ, (chart e he).injective.eq_iff]
  exact Subtype.ext_iff

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
