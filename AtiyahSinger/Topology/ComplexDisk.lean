/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportFunctoriality
public import AtiyahSinger.Topology.RelativeKZero
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The standard complex disk pair and its open complement

Public module ID: M1707.

KL01/K03. Use mathlib's `Complex.UnitClosedDisc`, its actual norm-one boundary,
and its boundary inclusion into the disk. The boundary homeomorphism to `Circle`
keeps the same complex coordinate, without conjugation or an orientation choice.
The complement of the product boundary is identified with the complex plane by
mathlib's radial `Homeomorph.unitBall`, whose inverse is positive real radial
rescaling. The resulting relative K-group comparison reuses the existing quotient
and compact-support constructions; no new K-group model is introduced.

Sources: Karoubi, K-Theory, III.1.2--1.8 (disk-boundary clutching comparison);
Lawson--Michelsohn, Spin Geometry, I.9 (relative K-theory and compact support).
These are coordinate and functoriality constructions, not Bott periodicity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The standard closed complex disk is compact, by the closed-ball instance. -/
theorem complexUnitClosedDisc_compactSpace : CompactSpace Complex.UnitClosedDisc := by
  /- The carrier and topology are those of the closed unit ball in the complex
  plane. Apply compactness of closed bounded sets in this finite-dimensional
  normed space, then retain the induced subtype topology. -/
  exact inferInstanceAs (CompactSpace (Metric.closedBall (0 : ℂ) 1))

/-- The standard closed complex disk has the Hausdorff subtype topology. -/
theorem complexUnitClosedDisc_t2Space : T2Space Complex.UnitClosedDisc := by
  /- The closed disk has the subspace topology inherited from the complex
  plane. Hausdorff separation restricts to every subspace, including this one. -/
  exact inferInstanceAs (T2Space (Metric.closedBall (0 : ℂ) 1))

attribute [local instance] complexUnitClosedDisc_compactSpace complexUnitClosedDisc_t2Space

/-- The actual norm-one boundary inside the standard closed complex disk. -/
def complexDiskBoundary : Set Complex.UnitClosedDisc :=
  {z | ‖(z : ℂ)‖ = 1}

/-- The disk boundary is closed in the disk. -/
theorem isClosed_complexDiskBoundary : IsClosed complexDiskBoundary := by
  /- Restrict the continuous complex norm to the disk. The boundary is its
  inverse image of the closed singleton {1}, hence is closed in the disk. -/
  exact isClosed_eq Complex.UnitClosedDisc.continuous_coe.norm continuous_const

/-- The disk boundary is the unit circle with unchanged complex coordinate. -/
def complexDiskBoundaryHomeomorph : complexDiskBoundary ≃ₜ Circle where
  toFun z := ⟨(z.val : ℂ), mem_sphere_zero_iff_norm.mpr z.property⟩
  invFun z := ⟨Complex.UnitClosedDisc.mk (z : ℂ) (le_of_eq z.norm_coe), z.norm_coe⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  continuous_toFun :=
    (Complex.UnitClosedDisc.continuous_coe.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable (X : Type*) [TopologicalSpace X]

/-- The product boundary in the compact disk pair over a base space. -/
def complexDiskBoundaryProduct : Set (X × Complex.UnitClosedDisc) :=
  {z | z.2 ∈ complexDiskBoundary}

/-- The product boundary is closed, with no compactness assumption on the base. -/
theorem isClosed_complexDiskBoundaryProduct : IsClosed (complexDiskBoundaryProduct X) := by
  /- The product boundary is exactly the inverse image of the disk boundary
  under the continuous second projection. Apply closedness under this preimage. -/
  exact isClosed_complexDiskBoundary.preimage continuous_snd

/-- The open complement of the product boundary is the product with the complex plane.
The forward radial coordinate is `w / sqrt (1 - ‖w‖²)`, as in mathlib. -/
def complexDiskComplementHomeomorph :
    ((complexDiskBoundaryProduct X)ᶜ : Set (X × Complex.UnitClosedDisc)) ≃ₜ X × ℂ :=
  let e : ((complexDiskBoundaryProduct X)ᶜ : Set (X × Complex.UnitClosedDisc)) ≃ₜ
      X × Metric.ball (0 : ℂ) 1 :=
    { toFun := fun z ↦
        (z.val.1, ⟨(z.val.2 : ℂ), mem_ball_zero_iff.mpr
          (lt_of_le_of_ne z.val.2.norm_le_one z.property)⟩)
      invFun := fun z ↦
        ⟨(z.1, Complex.UnitClosedDisc.mk z.2.val
          (le_of_lt (mem_ball_zero_iff.mp z.2.property))),
          (mem_ball_zero_iff.mp z.2.property).ne⟩
      left_inv := fun _ ↦ Subtype.ext (Prod.ext rfl (Subtype.ext rfl))
      right_inv := fun _ ↦ Prod.ext rfl (Subtype.ext rfl)
      continuous_toFun := continuous_subtype_val.fst.prodMk
        ((Complex.UnitClosedDisc.continuous_coe.comp continuous_subtype_val.snd).subtype_mk _)
      continuous_invFun :=
        (continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_snd).subtype_mk _)).subtype_mk _ }
  e.trans ((Homeomorph.refl X).prodCongr (Homeomorph.unitBall (E := ℂ)).symm)

/-- The disk pair gives the existing compact-support K-group of the plane product. -/
def complexDiskRelativeKZeroEquiv [CompactSpace X] [T2Space X] :
    RelativeKZero (complexDiskBoundaryProduct X) (isClosed_complexDiskBoundaryProduct X) ≃+
      CompactSupportKZero (X × ℂ) :=
  letI := (isClosed_complexDiskBoundaryProduct X).isOpen_compl.locallyCompactSpace
  (relativeKZeroCompactSupportEquiv (complexDiskBoundaryProduct X)
    (isClosed_complexDiskBoundaryProduct X)).trans
      (compactSupportKZeroHomeomorphEquiv (complexDiskComplementHomeomorph X))

end AtiyahSinger
