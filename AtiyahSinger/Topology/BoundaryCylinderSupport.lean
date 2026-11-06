/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKMinusOneSuspension
public import AtiyahSinger.Topology.KTheoryBoundaryCylinder
public import AtiyahSinger.Topology.SuspendedKExcision

/-!
# The closed half-open tube in the boundary cylinder

Public module ID: M1570.

Karoubi II.4.9 uses the closed complement of the open base in
`Z = X × {0} ∪ A × [0,1)`. This complement includes the attaching locus
`A × {0}`; it is not the positive-height open tube. We identify it with
`A × ℝ≥0` by the actual increasing parameter `r ↦ r/(1+r)`.

After adjoining the existing `Fin n → ℝ` coordinates, the same closed
complement is a half-ray product with base `A × (Fin n → ℝ)`. Both of its
supported groups vanish by the independent II.4.8 contraction. The II.4.7
sequence therefore makes extension from the actual open base bijective.
These are the vanishing inputs for alpha bijectivity. The vanishing proof
uses neither alpha bijectivity nor the suspended exact sequence.

The grouped vanishing statement is the half-open-tube conclusion used in II.4.9.
This module does not identify the cylinder boundary with the clutching boundary.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped NNReal

variable {X : Type*} [TopologicalSpace X]

/-- The entire closed tube uses the increasing half-ray parameter, including its zero end. -/
def boundaryCylinderClosedTubeHomeomorph (A : Set X) :
    (A × ℝ≥0) ≃ₜ ((boundaryCylinderBaseOpen A)ᶜ : Set (BoundaryCylinder A)) where
  toFun p :=
    ⟨⟨(p.1.val, (p.2 : ℝ) / (1 + (p.2 : ℝ))),
      div_nonneg p.2.property (by positivity),
      (div_lt_one (by positivity)).mpr (by linarith), Or.inr p.1.property⟩,
        by simp [boundaryCylinderBaseOpen, p.1.property]⟩
  invFun z :=
    (⟨z.val.val.1, by simpa [boundaryCylinderBaseOpen] using z.property⟩,
      ⟨z.val.val.2 / (1 - z.val.val.2),
        div_nonneg z.val.property.1 (sub_nonneg.mpr z.val.property.2.1.le)⟩)
  left_inv p := by
    -- The reciprocal rational substitution recovers the original half-ray coordinate.
    apply Prod.ext
    · rfl
    · apply NNReal.eq
      change ((p.2 : ℝ) / (1 + (p.2 : ℝ))) /
        (1 - (p.2 : ℝ) / (1 + (p.2 : ℝ))) = (p.2 : ℝ)
      have h : 0 < 1 + (p.2 : ℝ) := by positivity
      field_simp
      ring
  right_inv z := by
    -- The original height is strictly below one, so the same substitution is invertible.
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (z.val.val.2 / (1 - z.val.val.2)) /
        (1 + z.val.val.2 / (1 - z.val.val.2)) = z.val.val.2
      have h : 0 < 1 - z.val.val.2 := sub_pos.mpr z.val.property.2.1
      field_simp
      ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    refine (continuous_subtype_val.comp continuous_fst).prodMk ?_
    exact (NNReal.continuous_coe.comp continuous_snd).div
      (continuous_const.add (NNReal.continuous_coe.comp continuous_snd))
      (fun p ↦ by positivity)
  continuous_invFun := by
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_subtype_val).snd.div
        (continuous_const.sub (continuous_subtype_val.comp continuous_subtype_val).snd)
        (fun z ↦ ne_of_gt (sub_pos.mpr z.val.property.2.1))

/-- The suspended closed complement keeps every old real coordinate and moves the ray last. -/
def boundaryCylinderSuspendedClosedTubeHomeomorph (n : ℕ) (A : Set X) :
    ((A × (Fin n → ℝ)) × ℝ≥0) ≃ₜ
      (((Prod.fst : BoundaryCylinder A × (Fin n → ℝ) → BoundaryCylinder A) ⁻¹'
        boundaryCylinderBaseOpen A)ᶜ : Set (BoundaryCylinder A × (Fin n → ℝ))) :=
  (Homeomorph.prodAssoc A (Fin n → ℝ) ℝ≥0).trans
    (((Homeomorph.refl A).prodCongr (Homeomorph.prodComm (Fin n → ℝ) ℝ≥0)).trans
      ((Homeomorph.prodAssoc A ℝ≥0 (Fin n → ℝ)).symm.trans
        (((boundaryCylinderClosedTubeHomeomorph A).prodCongr
          (Homeomorph.refl (Fin n → ℝ))).trans
            (subspaceProdHomeomorph (boundaryCylinderBaseOpen A)ᶜ (Fin n → ℝ)))))

/-- KA II.4.9: both predecessor groups vanish on this same suspended closed half-open tube. -/
theorem boundaryCylinderSuspendedClosedTube_vanishing
    [LocallyCompactSpace X] [T2Space X] (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := locallyCompactSpace_boundaryCylinder A hA
    let U := (Prod.fst : BoundaryCylinder A × (Fin n → ℝ) → BoundaryCylinder A) ⁻¹'
      boundaryCylinderBaseOpen A
    let hU : IsOpen U := (isOpen_boundaryCylinderBaseOpen A hA).preimage continuous_fst
    letI := hU.isClosed_compl.locallyCompactSpace
    Subsingleton (CompactSupportKZero (Uᶜ : Set (BoundaryCylinder A × (Fin n → ℝ)))) ∧
      Subsingleton (ComplexBundle.CompactSupportBundleKMinusOne
        (Uᶜ : Set (BoundaryCylinder A × (Fin n → ℝ)))) := by
  /- Stage 1: closedness of A makes its original subtype locally compact. Thus
  A × (Fin n → ℝ) is locally compact Hausdorff, without a compactness,
  connectedness or nonemptiness assumption. Use the same half-ray contraction
  on this base to obtain compactSupportKZero_halfRay_subsingleton and
  compactSupportBundleKMinusOne_halfRay_subsingleton.
  Stage 2: transport these two vanishing results along exactly
  boundaryCylinderSuspendedClosedTubeHomeomorph n A. Its image is the closed
  complement of the suspended base open, including height zero over A. Transport
  uses the existing proper-homeomorphism equivalences in the two supported groups.
  This supplies the vanishing inputs to the independent II.4.7 sequence. Its
  exactness and the resulting alpha bijectivity are not used here; neither is a
  claim that K-minus-one of a point vanishes. -/
  -- The same closed subtype A is a locally compact base for the ray contraction.
  let := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let := locallyCompactSpace_boundaryCylinder A hA
  let U := (Prod.fst : BoundaryCylinder A × (Fin n → ℝ) → BoundaryCylinder A) ⁻¹'
    boundaryCylinderBaseOpen A
  let hU : IsOpen U := (isOpen_boundaryCylinderBaseOpen A hA).preimage continuous_fst
  let := hU.isClosed_compl.locallyCompactSpace
  let := compactSupportKZero_halfRay_subsingleton (A × (Fin n → ℝ))
  let := ComplexBundle.compactSupportBundleKMinusOne_halfRay_subsingleton (A × (Fin n → ℝ))
  -- Both transports use the identical closed-tube homeomorphism, including height zero.
  let e := boundaryCylinderSuspendedClosedTubeHomeomorph n A
  exact ⟨(compactSupportKZeroHomeomorphEquiv e).symm.injective.subsingleton,
    (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv e).symm.injective.subsingleton⟩

end AtiyahSinger
