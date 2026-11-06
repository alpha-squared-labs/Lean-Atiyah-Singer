/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.DisjointUnionKZero
public import AtiyahSinger.Topology.SphereDeRhamPoleModel
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# The two disjoint invariant windows for the original sphere endpoint

Public module ID: M2163.

The real parts of the actual complexified coordinates are restricted to the
open unit ball. Their two original tangent-chart images lie over opposite
open hemispheres. Their disjoint union is an equivariant open embedding
containing the entire original two-pole compact control, including rank zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Topology
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphereTangent
local instance (r : ℕ) :
    SMul (Matrix.orthogonalGroup (Fin r) ℝ) (EuclideanSpace ℂ (Fin r)) :=
  (orthogonalComplexificationDistribMulAction r).toSMul

/-- The actual invariant coordinate window used in either pole chart. -/
def orthogonalSphereDeRhamWindow (r : ℕ) :
    SubMulAction (Matrix.orthogonalGroup (Fin r) ℝ) (EuclideanSpace ℂ (Fin r)) where
  carrier := {z | ‖(WithLp.toLp 2 (fun j ↦ (z j).re) : EuclideanSpace ℝ (Fin r))‖ < 1}
  smul_mem' A z hz := by
    have hreal : (WithLp.toLp 2 (fun j ↦ ((A • z) j).re) : EuclideanSpace ℝ (Fin r)) =
        orthogonalEuclideanIsometry r A (WithLp.toLp 2 (fun j ↦ (z j).re)) := by
      ext j
      change (∑ l, (A.val j l : ℂ) * z l).re = ∑ l, A.val j l * (z l).re
      simp
    change ‖(WithLp.toLp 2 (fun j ↦ ((A • z) j).re) : EuclideanSpace ℝ (Fin r))‖ < 1
    rw [hreal, (orthogonalEuclideanIsometry r A).norm_map]
    exact hz

/-- The coordinate window is open in the original Euclidean topology. -/
theorem isOpen_orthogonalSphereDeRhamWindow (r : ℕ) :
    IsOpen (orthogonalSphereDeRhamWindow r : Set (EuclideanSpace ℂ (Fin r))) := by
  have hre : Continuous (fun z : EuclideanSpace ℂ (Fin r) ↦
      (WithLp.toLp 2 (fun j ↦ (z j).re) : EuclideanSpace ℝ (Fin r))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
      (continuous_pi fun j ↦ Complex.continuous_re.comp
        (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) j))
  exact isOpen_lt hre.norm continuous_const

/-- The window carries the original restricted matrix action. -/
instance sphereDeRhamWindowMulAction (r : ℕ) :
    MulAction (Matrix.orthogonalGroup (Fin r) ℝ) (orthogonalSphereDeRhamWindow r) := by
  letI : MulAction (Matrix.orthogonalGroup (Fin r) ℝ) (EuclideanSpace ℂ (Fin r)) :=
    (orthogonalComplexificationDistribMulAction r).toMulAction
  exact SubMulAction.SMulMemClass.toMulAction (orthogonalSphereDeRhamWindow r)

local instance (r : ℕ) :
    SMul (Matrix.orthogonalGroup (Fin r) ℝ) (orthogonalSphereDeRhamWindow r) :=
  (sphereDeRhamWindowMulAction r).toSMul

/-- The subspace action is continuous in the unchanged coordinate topology. -/
instance continuousSMul_sphereDeRhamWindow (r : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ) (orthogonalSphereDeRhamWindow r) := by
  let : ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ) (EuclideanSpace ℂ (Fin r)) :=
    orthogonalComplexification_continuousSMul r
  exact Topology.IsInducing.subtypeVal.continuousSMul
    (M := Matrix.orthogonalGroup (Fin r) ℝ) continuous_id (fun {_ _} ↦ rfl)

/-- Both components retain their native subspace topology and original restricted action. -/
abbrev SphereDeRhamWindows (r : ℕ) :=
  Σ _ : Bool, orthogonalSphereDeRhamWindow r

/-- The original matrix action keeps the component index fixed. -/
instance sphereDeRhamWindowsMulAction (r : ℕ) :
    MulAction (Matrix.orthogonalGroup (Fin r) ℝ) (SphereDeRhamWindows r) where
  smul A z := ⟨z.1, A • z.2⟩
  one_smul z := congrArg (Sigma.mk z.1) (one_smul _ z.2)
  mul_smul A B z := congrArg (Sigma.mk z.1) (mul_smul A B z.2)

/-- The unchanged action on the two components is jointly continuous. -/
instance continuousSMul_sphereDeRhamWindows (r : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ) (SphereDeRhamWindows r) where
  continuous_smul := by
    let H := Matrix.orthogonalGroup (Fin r) ℝ
    let W := orthogonalSphereDeRhamWindow r
    have h : Continuous (fun z : (Σ _ : Bool, W × H) ↦
        (⟨z.1, z.2.2 • z.2.1⟩ : SphereDeRhamWindows r)) := by
      apply continuous_sigma
      intro b
      exact continuous_sigmaMk.comp (continuous_snd.smul continuous_fst)
    exact h.comp (Homeomorph.sigmaProdDistrib.continuous.comp
      (Homeomorph.prodComm H (SphereDeRhamWindows r)).continuous)

/-- The two windows map through exactly the original specified pole tangent charts. -/
def sphereDeRhamWindowsMap (r : ℕ) :
    C(SphereDeRhamWindows r, TangentBundle (𝓡 r) (OrthogonalSphere r)) where
  toFun z := orthogonalSphereTangentChart r z.1 z.2.val
  continuous_toFun := continuous_sigma fun b ↦
    (orthogonalSphereTangentChart r b).continuous.comp continuous_subtype_val

/-- The disjoint-window map respects the same derivative action on the native tangent bundle. -/
theorem sphereDeRhamWindowsMap_equivariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : SphereDeRhamWindows r) :
    sphereDeRhamWindowsMap r (A • z) = A • sphereDeRhamWindowsMap r z := by
  exact orthogonalSphereTangentChart_equivariant r z.1 A z.2.val

/-- Opposite strict height signs separate the actual two chart images. -/
theorem sphereDeRhamWindowsMap_isOpenEmbedding (r : ℕ) :
    IsOpenEmbedding (sphereDeRhamWindowsMap r) := by
  let W := orthogonalSphereDeRhamWindow r
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  let j := sphereDeRhamWindowsMap r
  have hheight (b : Bool) (z : W) :
      let t := j ⟨b, z⟩
      if b then 0 < (t.proj.val.ofLp).2 else (t.proj.val.ofLp).2 < 0 := by
    let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun k ↦ (z.val k).re)
    have hnorm : ‖u‖ < 1 := z.property
    have hsq : ‖u‖ ^ 2 < 1 := by nlinarith [norm_nonneg u]
    have hden : 0 < 1 + ‖u‖ ^ 2 := by positivity
    have hx := orthogonalSphereNormalizedChart_inverse_formula r b u
    change if b then 0 < _ else _ < 0
    change (if b then 0 <
      (((orthogonalSphereNormalizedChart r b).symm u).val.ofLp).2 else
      (((orthogonalSphereNormalizedChart r b).symm u).val.ofLp).2 < 0)
    rw [hx]
    cases b
    · exact div_neg_of_neg_of_pos (by simpa using sub_neg.mpr hsq) hden
    · exact div_pos (sub_pos.mpr hsq) hden
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap j.continuous
  · rintro ⟨b, z⟩ ⟨c, w⟩ h
    have hbc : b = c := by
      by_contra hbc
      have hz := hheight b z
      have hw := hheight c w
      have ht := congrArg (fun t : T ↦ (t.proj.val.ofLp).2) h
      cases b <;> cases c
      · exact hbc rfl
      · simp only [Bool.false_eq_true, ↓reduceIte] at hz hw
        linarith
      · simp only [Bool.false_eq_true, ↓reduceIte] at hz hw
        linarith
      · exact hbc rfl
    subst c
    apply congrArg (Sigma.mk b)
    apply Subtype.ext
    exact (orthogonalSphereTangentChart_isOpenEmbedding r b).injective h
  · apply isOpenMap_sigma.mpr
    intro b
    exact ((orthogonalSphereTangentChart_isOpenEmbedding r b).comp
      (isOpen_orthogonalSphereDeRhamWindow r).isOpenEmbedding_subtypeVal).isOpenMap

/-- The disjoint union contains both zeros of the original endpoint representative. -/
theorem sphereDeRhamTriple_control_subset_range_windows (r : ℕ) :
    (sphereDeRhamTriple r 1).control ⊆ Set.range (sphereDeRhamWindowsMap r) := by
  intro t ht
  have ht' := ((sphereDeRhamVector_properties r).1 1 t).mp ht
  have hz : (0 : EuclideanSpace ℂ (Fin r)) ∈ orthogonalSphereDeRhamWindow r := by
    change ‖(WithLp.toLp 2 (fun j : Fin r ↦ (0 : ℂ).re) : EuclideanSpace ℝ (Fin r))‖ < 1
    change ‖(0 : EuclideanSpace ℝ (Fin r))‖ < 1
    simp
  have hp (b : Bool) : sphereDeRhamWindowsMap r ⟨b, ⟨0, hz⟩⟩ =
      (⟨orthogonalSpherePole r b, 0⟩ : TangentBundle (𝓡 r) (OrthogonalSphere r)) := by
    change (⟨(orthogonalSphereNormalizedChart r b).symm _,
      mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r b).symm _ _⟩ :
        TangentBundle (𝓡 r) (OrthogonalSphere r)) = _
    change (⟨(orthogonalSphereNormalizedChart r b).symm 0,
      mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r b).symm 0 0⟩ :
        TangentBundle (𝓡 r) (OrthogonalSphere r)) = _
    rw [map_zero]
    apply TotalSpace.ext (orthogonalSphereNormalizedChart_properties r b).2.2.1
    apply heq_of_eq
    rfl
  rcases ht'.2 with h | h | h
  · norm_num at h
  · refine ⟨⟨false, ⟨0, hz⟩⟩, (hp false).trans ?_⟩
    cases t
    cases h
    exact congrArg (TotalSpace.mk _) ht'.1.symm
  · refine ⟨⟨true, ⟨0, hz⟩⟩, (hp true).trans ?_⟩
    cases t
    cases h
    exact congrArg (TotalSpace.mk _) ht'.1.symm

end AtiyahSinger
