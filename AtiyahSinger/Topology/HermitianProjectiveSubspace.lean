/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveLinearImage
public import Mathlib.Topology.Homotopy.Basic

/-!
# Retraction onto a projective subspace

Public module ID: M1902.

Orthogonal projection onto a subspace gives an actual projective retraction
on the open set of lines which it does not annihilate. Scaling the orthogonal
component from zero to one connects the included retraction to the identity. The special case of a
hyperplane is the deleted-point reduction for complex projective space.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped unitInterval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- Projective lines on which the specified orthogonal projection is nonzero. -/
abbrev SubspaceDomain (K : Submodule ℂ V) : Type _ :=
  {P : HermitianProjectiveSpace V InnerProductSpace.toCore //
    K.orthogonalProjectionOnto.comp P.val ≠ 0}

omit [FiniteDimensional ℂ V] in
/-- The subspace inclusion cannot kill a projective line. This certificate supplies
the nonvanishing premise in the exposed section and deformation constructions. -/
theorem subtype_comp_ne_zero (K : Submodule ℂ V)
    (P : HermitianProjectiveSpace K InnerProductSpace.toCore) : K.subtypeL.comp P.val ≠ 0 := by
  intro hz
  have hP : P.val = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply Subtype.val_injective
    exact congrArg (fun L : K →L[ℂ] V ↦ L v) hz
  have hlin : P.val.toLinearMap = 0 := congrArg ContinuousLinearMap.toLinearMap hP
  have hr := P.property.2.1
  rw [hlin, LinearMap.range_zero] at hr
  simp at hr

/-- The actual projective image of the orthogonal projection onto a subspace. -/
def subspaceRetraction (K : Submodule ℂ V) :
    C(SubspaceDomain K, HermitianProjectiveSpace K InnerProductSpace.toCore) where
  toFun P := linearImage K.orthogonalProjectionOnto P.val P.property
  continuous_toFun := by
    let g : SubspaceDomain K → {z : (V →L[ℂ] K) ×
        HermitianProjectiveSpace V InnerProductSpace.toCore // z.1.comp z.2.val ≠ 0} :=
      fun P ↦ ⟨(K.orthogonalProjectionOnto, P.val), P.property⟩
    have hg : Continuous g :=
      (continuous_const.prodMk continuous_subtype_val).subtype_mk (fun P ↦ P.property)
    have hc := (continuous_linearImage (V := V) (W := K)).comp hg
    exact hc

/-- The ordinary inclusion of a projective subspace lands in its projection domain. -/
def subspaceSection (K : Submodule ℂ V) :
    C(HermitianProjectiveSpace K InnerProductSpace.toCore, SubspaceDomain K) := by
  let i := linearImageMap K.subtypeL Subtype.val_injective
  have hsource (P : HermitianProjectiveSpace K InnerProductSpace.toCore) :
      K.orthogonalProjectionOnto.comp (i P).val ≠ 0 := by
    intro hz
    have hP : P.val = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      have hfix : (i P).val (P.val v).val = (P.val v).val := by
        dsimp only [i, linearImageMap]
        exact linearImage_apply_image K.subtypeL P (subtype_comp_ne_zero K P) v
      have hzero := congrArg (fun L : V →L[ℂ] K ↦ L (P.val v).val) hz
      change K.orthogonalProjectionOnto ((i P).val (P.val v).val) = 0 at hzero
      rw [hfix, K.orthogonalProjectionOnto_mem_subspace_eq_self] at hzero
      exact hzero
    have hlin : P.val.toLinearMap = 0 := congrArg ContinuousLinearMap.toLinearMap hP
    have hr := P.property.2.1
    rw [hlin, LinearMap.range_zero] at hr
    simp at hr
  exact ⟨fun P ↦ ⟨i P, hsource P⟩, i.continuous.subtype_mk hsource⟩

/-- Orthogonal projective retraction is the identity on the included projective subspace. -/
theorem subspaceRetraction_comp_section (K : Submodule ℂ V) :
    (subspaceRetraction K).comp (subspaceSection K) =
      ContinuousMap.id (HermitianProjectiveSpace K InnerProductSpace.toCore) := by
  apply ContinuousMap.ext
  intro P
  obtain ⟨v, hv⟩ : ∃ v : K, P.val v ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hP : P.val = 0 := ContinuousLinearMap.ext hzero
    have hlin : P.val.toLinearMap = 0 := congrArg ContinuousLinearMap.toLinearMap hP
    have hr := P.property.2.1
    rw [hlin, LinearMap.range_zero] at hr
    simp at hr
  let Q := (subspaceSection K P).val
  have hQ : Q.val (P.val v).val = (P.val v).val := by
    dsimp only [Q, subspaceSection, linearImageMap]
    exact linearImage_apply_image K.subtypeL P (subtype_comp_ne_zero K P) v
  have hR := linearImage_apply_image K.orthogonalProjectionOnto Q
    (subspaceSection K P).property (P.val v).val
  rw [hQ, K.orthogonalProjectionOnto_mem_subspace_eq_self] at hR
  apply eq_of_fixed_nonzero _ P (P.val v) hv hR
  exact congrArg (fun L : K →L[ℂ] K ↦ L v) P.property.1

/-- Scaling the orthogonal component from zero to one connects the retraction to the identity. -/
def subspaceDeformation (K : Submodule ℂ V) :
    ((subspaceSection K).comp (subspaceRetraction K)).Homotopy
      (ContinuousMap.id (SubspaceDomain K)) := by
  let D := SubspaceDomain K
  let A (t : unitInterval) : V →L[ℂ] V :=
    ((t : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V +
      (1 - ((t : ℝ) : ℂ)) • K.starProjection
  have hA : Continuous A := by
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const |>.add
      ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_subtype_val)).smul
        continuous_const)
  have hproj (t : unitInterval) (v : V) :
      K.orthogonalProjectionOnto (A t v) = K.orthogonalProjectionOnto v := by
    change K.orthogonalProjectionOnto
      (((t : ℝ) : ℂ) • v + (1 - ((t : ℝ) : ℂ)) • K.starProjection v) = _
    rw [map_add, map_smul, map_smul]
    have hfix : K.orthogonalProjectionOnto (K.starProjection v) =
        K.orthogonalProjectionOnto v :=
      K.orthogonalProjectionOnto_mem_subspace_eq_self (K.orthogonalProjectionOnto v)
    rw [hfix, ← add_smul, add_sub_cancel, one_smul]
  -- No intermediate map can kill a line whose orthogonal projection is nonzero.
  have hnonzero (t : unitInterval) (P : D) : (A t).comp P.val.val ≠ 0 := by
    intro hz
    apply P.property
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L : V →L[ℂ] V ↦ K.orthogonalProjectionOnto (L v)) hz
    change K.orthogonalProjectionOnto (A t (P.val.val v)) =
      K.orthogonalProjectionOnto 0 at h
    rwa [map_zero, hproj] at h
  let H (t : unitInterval) (P : D) := linearImage (A t) P.val (hnonzero t P)
  have hdomain (t : unitInterval) (P : D) :
      K.orthogonalProjectionOnto.comp (H t P).val ≠ 0 := by
    intro hz
    apply P.property
    apply ContinuousLinearMap.ext
    intro v
    have hfix := linearImage_apply_image (A t) P.val (hnonzero t P) v
    have h := congrArg (fun L : V →L[ℂ] K ↦ L (A t (P.val.val v))) hz
    change K.orthogonalProjectionOnto ((H t P).val (A t (P.val.val v))) = 0 at h
    rw [hfix, hproj] at h
    exact h
  have hexists (P : D) : ∃ v : V, K.orthogonalProjectionOnto (P.val.val v) ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact P.property (ContinuousLinearMap.ext hzero)
  have hzero (P : D) : H 0 P = ((subspaceSection K).comp (subspaceRetraction K) P).val := by
    obtain ⟨v, hv⟩ := hexists P
    let w := K.starProjection (P.val.val v)
    have hw : w ≠ 0 := by
      intro hz
      apply hv
      have h := congrArg K.orthogonalProjectionOnto hz
      change K.orthogonalProjectionOnto (K.starProjection (P.val.val v)) =
        K.orthogonalProjectionOnto 0 at h
      rw [map_zero] at h
      have hfix : K.orthogonalProjectionOnto (K.starProjection (P.val.val v)) =
          K.orthogonalProjectionOnto (P.val.val v) :=
        K.orthogonalProjectionOnto_mem_subspace_eq_self (K.orthogonalProjectionOnto (P.val.val v))
      exact hfix.symm.trans h
    have hH := linearImage_apply_image (A 0) P.val (hnonzero 0 P) v
    have hA0 (z : V) : A 0 z = K.starProjection z := by simp [A]
    rw [hA0] at hH
    let R := subspaceRetraction K P
    have hR : R.val (K.orthogonalProjectionOnto (P.val.val v)) =
        K.orthogonalProjectionOnto (P.val.val v) :=
      linearImage_apply_image K.orthogonalProjectionOnto P.val P.property v
    have hS : (subspaceSection K R).val.val
        (R.val (K.orthogonalProjectionOnto (P.val.val v))).val =
          (R.val (K.orthogonalProjectionOnto (P.val.val v))).val := by
      dsimp only [subspaceSection, linearImageMap]
      exact linearImage_apply_image K.subtypeL R (subtype_comp_ne_zero K R)
        (K.orthogonalProjectionOnto (P.val.val v))
    rw [hR] at hS
    exact eq_of_fixed_nonzero _ _ w hw hH hS
  have hone (P : D) : H 1 P = P.val := by
    obtain ⟨v, hv⟩ := hexists P
    have hv' : P.val.val v ≠ 0 := by
      intro hz
      apply hv
      rw [hz, map_zero]
    have hH := linearImage_apply_image (A 1) P.val (hnonzero 1 P) v
    have hA1 (z : V) : A 1 z = z := by simp [A]
    rw [hA1] at hH
    apply eq_of_fixed_nonzero _ _ (P.val.val v) hv' hH
    exact congrArg (fun L : V →L[ℂ] V ↦ L v) P.val.property.1
  -- Joint continuity of the original linear-image construction supplies the whole homotopy.
  let g : unitInterval × D → {z : (V →L[ℂ] V) ×
      HermitianProjectiveSpace V InnerProductSpace.toCore // z.1.comp z.2.val ≠ 0} :=
    fun z ↦ ⟨(A z.1, z.2.val), hnonzero z.1 z.2⟩
  have hg : Continuous g :=
    ((hA.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk (fun z ↦ hnonzero z.1 z.2)
  have hc := (continuous_linearImage (V := V) (W := V)).comp hg
  exact
    { toFun := fun z ↦ ⟨H z.1 z.2, hdomain z.1 z.2⟩
      continuous_toFun := hc.subtype_mk (fun z ↦ hdomain z.1 z.2)
      map_zero_left := fun P ↦ Subtype.ext (hzero P)
      map_one_left := fun P ↦ Subtype.ext (hone P) }

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
