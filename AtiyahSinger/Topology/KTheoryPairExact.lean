/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BoundaryCylinderSupport
public import AtiyahSinger.Topology.KTheoryBoundaryCylinder
public import AtiyahSinger.Topology.SuspendedKExcision

/-!
# The specified boundary and exact sequence of a closed pair

Public module ID: M1919.

Karoubi II.4.9 constructs the boundary using the actual space
Z = X × {0} ∪ A × [0,1). The open base complement is X ∖ A and the open tube
is A × ℝ, with increasing interval coordinates. Extension from the base is
an isomorphism α; extension from the tube is β. The boundary is α⁻¹ β.
We retain these maps in every nonpositive degree, with the new real coordinate
first in `Fin (n+1) → ℝ`. No arbitrary exactness witness defines the map.
Moving this new coordinate to the last position changes the usual oriented
suspension comparison by (-1)^n (KA II.4.10). We do not claim that comparison
has positive sign in every degree. The common convention preserves exactness.

The proof of invertibility of α uses the earlier compact-pair Puppe sequence
(KA II.3.23, II.3.29), its compactification reduction (II.4.6--4.8), and the
based contraction of the half-open cylinder. These independently established
inputs prove base-extension bijectivity below without using the later exactness
theorems, whose specified boundary is only defined after α is inverted.

Base-extension bijectivity and all three suspended pair-exactness statements are proved
below. Their proofs use the independent supported pair sequence, without a clutching input.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/-- KA II.4.9: α is extension from the actual open base complement of the cylinder. -/
def compactSupportKBoundaryBase (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := hA.isOpen_compl.locallyCompactSpace
    letI := locallyCompactSpace_boundaryCylinder A hA
    CompactSupportK n (Aᶜ : Set X) →+ CompactSupportK n (BoundaryCylinder A) :=
  letI := hA.isOpen_compl.locallyCompactSpace
  letI := locallyCompactSpace_boundaryCylinder A hA
  letI := (isOpen_boundaryCylinderBaseOpen A hA).locallyCompactSpace
  (compactSupportKOpenExtension n _ (isOpen_boundaryCylinderBaseOpen A hA)).comp
    (compactSupportKHomeomorphEquiv n (boundaryCylinderBaseHomeomorph A)).toAddMonoidHom

/-- KA II.4.9: extension from the base complement is bijective in each suspended degree. -/
theorem compactSupportKBoundaryBase_bijective (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := hA.isOpen_compl.locallyCompactSpace
    letI := locallyCompactSpace_boundaryCylinder A hA
    Function.Bijective (compactSupportKBoundaryBase n A hA) := by
  /- Stage 1: the complement of the open base is A × [0,1). Its one-point
  compactification has a based contraction towards the deleted endpoint, so its
  reduced K group and its predecessor vanish, also after n real suspensions.
  Stage 2: use the independently established loop/Puppe compact-pair sequence
  of II.3.23 and II.3.29, passed to compact supports in II.4.6--4.8. Exactness
  between these two zero groups makes this specified open extension bijective.
  The suspended pair sequence below is not an input to this argument. -/
  classical
  let := hA.isOpen_compl.locallyCompactSpace
  let := locallyCompactSpace_boundaryCylinder A hA
  let Z := BoundaryCylinder A
  let V := Fin n → ℝ
  let B := boundaryCylinderBaseOpen A
  have hB : IsOpen B := isOpen_boundaryCylinderBaseOpen A hA
  let := hB.locallyCompactSpace
  let U : Set (Z × V) := Prod.fst ⁻¹' B
  have hU : IsOpen U := hB.preimage continuous_fst
  let := hU.locallyCompactSpace
  let := hU.isClosed_compl.locallyCompactSpace
  -- Both adjacent groups vanish on the same closed tube, including its attaching locus.
  have hvanish := boundaryCylinderSuspendedClosedTube_vanishing n A hA
  let : Subsingleton (CompactSupportKZero (Uᶜ : Set (Z × V))) := hvanish.1
  let : Subsingleton (ComplexBundle.CompactSupportBundleKMinusOne
    (Uᶜ : Set (Z × V))) := hvanish.2
  let E := compactSupportKZeroOpenExtension U hU
  let hUU := hU.isClosed_compl.isOpen_compl
  let := hUU.locallyCompactSpace
  -- Independent positive-boundary exactness proves injectivity of this exact extension.
  have hE' : Function.Bijective (compactSupportKZeroOpenExtension Uᶜᶜ hUU) := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro a ha
      have hpair := ComplexBundle.range_compactSupportBundleKMinusOneBoundary Uᶜ
        hU.isClosed_compl
      obtain ⟨b, hb⟩ := hpair.ge ha
      have hbzero : b = 0 := Subsingleton.elim _ _
      rw [hbzero, map_zero] at hb
      exact hb.symm
    · intro b
      have hpair := ComplexBundle.range_compactSupportKZeroOpenExtension Uᶜ
        hU.isClosed_compl
      -- The following closed restriction lands in the other zero group.
      have hb : b ∈ (compactSupportKZeroPullback
          (⟨Subtype.val, continuous_subtype_val⟩ : C((Uᶜ : Set (Z × V)), Z × V))
          hU.isClosed_compl.isClosedEmbedding_subtypeVal.isProperMap).ker := by
        exact Subsingleton.elim _ _
      exact hpair.ge hb
  -- Eliminate the double-complement equality together with its openness certificate.
  have transport (W : Set (Z × V)) (hW : IsOpen W) (hWU : W = U) :
      Function.Bijective (compactSupportKZeroOpenExtension W hW) →
        Function.Bijective E := by
    subst W
    exact id
  have hE : Function.Bijective E := transport _ hUU (compl_compl U) hE'
  -- Retain the original product-subspace map and the original base homeomorphism.
  have hopen : Function.Bijective (compactSupportKOpenExtension n B hB) :=
    hE.comp (compactSupportKZeroHomeomorph_bijective
      (subspaceProdHomeomorph B V))
  exact hopen.comp (compactSupportKHomeomorphEquiv n
    (boundaryCylinderBaseHomeomorph A)).bijective

/-- KA II.4.9: β extends the tube after inserting the first suspension coordinate. -/
def compactSupportKBoundaryTube (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := locallyCompactSpace_boundaryCylinder A hA
    CompactSupportK (n + 1) A →+ CompactSupportK n (BoundaryCylinder A) :=
  letI := hA.locallyCompactSpace
  letI := locallyCompactSpace_boundaryCylinder A hA
  letI := (isOpen_boundaryCylinderTubeOpen A).locallyCompactSpace
  (compactSupportKOpenExtension n _ (isOpen_boundaryCylinderTubeOpen A)).comp
    ((compactSupportKHomeomorphEquiv n (boundaryCylinderTubeHomeomorph A)).toAddMonoidHom.comp
      (compactSupportKZeroHomeomorphEquiv
        (suspensionCoordinateHomeomorph A n).symm).toAddMonoidHom)

/-- The boundary of a closed pair is the specified composite α⁻¹ ∘ β. -/
def compactSupportKBoundary (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    CompactSupportK (n + 1) A →+ CompactSupportK n (Aᶜ : Set X) :=
  letI := hA.locallyCompactSpace
  letI := hA.isOpen_compl.locallyCompactSpace
  letI := locallyCompactSpace_boundaryCylinder A hA
  (AddEquiv.ofBijective (compactSupportKBoundaryBase n A hA)
    (compactSupportKBoundaryBase_bijective n A hA)).symm.toAddMonoidHom.comp
      (compactSupportKBoundaryTube n A hA)

/-- KA II.4.13: exactness at the suspended closed subspace. -/
theorem range_compactSupportKClosedRestriction_eq_ker_boundary
    (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    (compactSupportKClosedRestriction (n + 1) A hA).range =
      (compactSupportKBoundary n A hA).ker := by
  /- Stage 1: the whole closed bottom of the suspended cylinder is X × ℝⁿ.
  Apply the independent positive-boundary exactness theorem to this bottom.
  Stage 2: extend the specified increasing tube parameter to a half-ray including
  zero. Proper half-ray naturality identifies that positive boundary with the
  actual tube extension β after the same first-coordinate suspension transport.
  Stage 3: the resulting image is ker β. The independently bijective α identifies
  this kernel with ker(α⁻¹β), giving exactness for the specified boundary. -/
  classical

  have parameterExtension (p : ℝ ≃o Set.Ioo (0 : ℝ) 1) :
      ∃ e : NNReal ≃ₜ Set.Ico (0 : ℝ) 1,
        (e 0).val = 0 ∧
          ∀ t : ℝ, (e ⟨Real.exp t, (Real.exp_pos t).le⟩).val = (p t).val := by
    classical
    let F : NNReal → Set.Ico (0 : ℝ) 1 := fun r ↦
      if hr : r = 0 then ⟨0, le_rfl, zero_lt_one⟩
      else ⟨(p (Real.log (r : ℝ))).val,
        (p (Real.log (r : ℝ))).property.1.le,
        (p (Real.log (r : ℝ))).property.2⟩
    have hF : StrictMono F := by
      intro r s hrs
      have hs : s ≠ 0 := ne_of_gt ((show 0 ≤ r from zero_le).trans_lt hrs)
      by_cases hr : r = 0
      · change (F r).val < (F s).val
        simp only [F, hr, hs, ↓reduceDIte]
        exact (p (Real.log (s : ℝ))).property.1
      · change (F r).val < (F s).val
        simp only [F, hr, hs, ↓reduceDIte]
        exact p.strictMono (Real.log_lt_log (by exact_mod_cast pos_iff_ne_zero.mpr hr)
          (by exact_mod_cast hrs))
    let G : Set.Ico (0 : ℝ) 1 → NNReal := fun t ↦
      if ht : t.val = 0 then 0
      else ⟨Real.exp (p.symm ⟨t.val, lt_of_le_of_ne t.property.1 (Ne.symm ht),
        t.property.2⟩), (Real.exp_pos _).le⟩
    have hFG : Function.RightInverse G F := by
      intro t
      by_cases ht : t.val = 0
      · apply Subtype.ext
        simp [G, ht, F]
      · have hexp : (⟨Real.exp (p.symm ⟨t.val, lt_of_le_of_ne t.property.1 (Ne.symm ht),
            t.property.2⟩), (Real.exp_pos _).le⟩ : NNReal) ≠ 0 := by
          exact NNReal.coe_ne_zero.mp (Real.exp_ne_zero _)
        apply Subtype.ext
        simp only [G, ht, ↓reduceDIte]
        dsimp only [F]
        split_ifs with hz
        · exact (hexp hz).elim
        · change (p (Real.log (Real.exp (p.symm
            ⟨t.val, lt_of_le_of_ne t.property.1 (Ne.symm ht), t.property.2⟩)))).val = t.val
          rw [Real.log_exp]
          exact congrArg Subtype.val (p.apply_symm_apply _)
    let e := (StrictMono.orderIsoOfRightInverse F hF G hFG).toHomeomorph
    refine ⟨e, ?_, ?_⟩
    · change (F 0).val = 0
      simp [F]
    · intro t
      have ht : (⟨Real.exp t, (Real.exp_pos t).le⟩ : NNReal) ≠ 0 := by
        exact NNReal.coe_ne_zero.mp (Real.exp_ne_zero _)
      change (F ⟨Real.exp t, (Real.exp_pos t).le⟩).val = (p t).val
      dsimp only [F]
      split_ifs with hz
      · exact (ht hz).elim
      · change (p (Real.log (Real.exp t))).val = (p t).val
        rw [Real.log_exp]
  have boundaryNaturalOfPreimageEq {P Q : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      (A : Set Q) (hA : IsClosed A)
      (f : C(P, Q)) (hf : IsProperMap f) (B : Set P) (hB : IsClosed B)
      (hpre : f ⁻¹' A = B) (g : C(B, A)) (hg : IsProperMap g)
      (j : C((Bᶜ : Set P), (Aᶜ : Set Q))) (hj : IsProperMap j)
      (hgval : ∀ b : B, (g b).val = f b.val)
      (hjval : ∀ b : (Bᶜ : Set P), (j b).val = f b.val) :
      letI := hA.locallyCompactSpace
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := hB.locallyCompactSpace
      letI := hB.isOpen_compl.locallyCompactSpace
      (compactSupportKZeroPullback j hj).comp
          (ComplexBundle.compactSupportBundleKMinusOneBoundary A hA) =
        (ComplexBundle.compactSupportBundleKMinusOneBoundary B hB).comp
          (ComplexBundle.compactSupportBundleKMinusOnePullback g hg) := by
    subst B
    have hg' : g = preimageSubspaceMap A f := by
      ext b
      exact hgval b
    have hj' : j = preimageSubspaceMap (Aᶜ : Set Q) f := by
      ext b
      exact hjval b
    subst g
    subst j
    exact ComplexBundle.compactSupportBundleKMinusOneBoundary_natural A hA f hf
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let := locallyCompactSpace_boundaryCylinder A hA
  let Z := BoundaryCylinder A
  let V := Fin n → ℝ
  -- Use the independent positive boundary at the whole closed bottom.
  let D : Set (Z × V) := {z | z.1.val.2 = 0}
  have hD : IsClosed D := isClosed_eq
    ((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).snd.comp
      continuous_fst) continuous_const
  let := hD.locallyCompactSpace
  let := hD.isOpen_compl.locallyCompactSpace
  let eD : (X × V) ≃ₜ D := {
    toFun := fun q ↦ ⟨(⟨(q.1, 0), le_rfl, zero_lt_one, Or.inl rfl⟩, q.2), rfl⟩
    invFun := fun q ↦ (q.val.1.val.1, q.val.2)
    left_inv := fun _ ↦ rfl
    right_inv := by
      intro q
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext rfl q.property.symm
      · rfl
    continuous_toFun := by fun_prop
    continuous_invFun :=
      ((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).comp
        continuous_subtype_val.fst).fst.prodMk continuous_subtype_val.snd }
  let f : C(A × V, X × V) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).prodMap (ContinuousMap.id V)
  have hf : IsProperMap f := hA.isProperMap_subtypeVal.prodMap isProperMap_id
  let shuffle (P : Type _) [TopologicalSpace P] :
      ((P × V) × ℝ) ≃ₜ ((P × ℝ) × V) :=
    (Homeomorph.prodAssoc P V ℝ).trans
      (((Homeomorph.refl P).prodCongr (Homeomorph.prodComm V ℝ)).trans
        (Homeomorph.prodAssoc P ℝ V).symm)
  let coord (P : Type _) [TopologicalSpace P] :
      ((P × V) × ℝ) ≃ₜ P × (Fin (n + 1) → ℝ) :=
    (shuffle P).trans (suspensionCoordinateHomeomorph P n)
  let kX := (ComplexBundle.compactSupportBundleKMinusOneSuspensionEquiv (X × V)).trans
    (compactSupportKZeroHomeomorphEquiv (coord X))
  let kA := (ComplexBundle.compactSupportBundleKMinusOneSuspensionEquiv (A × V)).trans
    (compactSupportKZeroHomeomorphEquiv (coord A))
  have hrestriction (a : ComplexBundle.CompactSupportBundleKMinusOne (X × V)) :
      compactSupportKClosedRestriction (n + 1) A hA (kX a) =
        kA (ComplexBundle.compactSupportBundleKMinusOnePullback f hf a) := by
    let fR := f.prodMap (ContinuousMap.id ℝ)
    let fN := (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).prodMap
      (ContinuousMap.id (Fin (n + 1) → ℝ))
    have hcoords : (⟨(coord X).symm, (coord X).symm.continuous⟩ :
        C(X × (Fin (n + 1) → ℝ), (X × V) × ℝ)).comp fN =
      fR.comp ⟨(coord A).symm, (coord A).symm.continuous⟩ := rfl
    have htransport : (compactSupportKZeroPullback fN
        (hA.isProperMap_subtypeVal.prodMap isProperMap_id)).comp
          (compactSupportKZeroHomeomorph (coord X)) =
        (compactSupportKZeroHomeomorph (coord A)).comp
          (compactSupportKZeroPullback fR (hf.prodMap isProperMap_id)) := by
      change (compactSupportKZeroPullback fN _).comp
        (compactSupportKZeroPullback _ (coord X).symm.isProperMap) =
          (compactSupportKZeroPullback _ (coord A).symm.isProperMap).comp
            (compactSupportKZeroPullback fR _)
      have hleft := compactSupportKZeroPullback_comp fN
        ⟨(coord X).symm, (coord X).symm.continuous⟩
        (hA.isProperMap_subtypeVal.prodMap isProperMap_id) (coord X).symm.isProperMap
      have hright := compactSupportKZeroPullback_comp
        ⟨(coord A).symm, (coord A).symm.continuous⟩ fR
        (coord A).symm.isProperMap (hf.prodMap isProperMap_id)
      exact hleft.symm.trans (by simpa only [hcoords] using hright)
    have hn := DFunLike.congr_fun
      (ComplexBundle.compactSupportBundleKMinusOneSuspension_natural f hf) a
    simp only [AddMonoidHom.comp_apply] at hn
    change compactSupportKZeroPullback fN _
      (compactSupportKZeroHomeomorph (coord X)
        (ComplexBundle.compactSupportBundleKMinusOneSuspension (X × V) a)) = _
    rw [← AddMonoidHom.comp_apply, htransport, AddMonoidHom.comp_apply, hn]
    rfl
  -- Extend the actual increasing parameter to the half-ray including zero.
  let affine := affineHomeomorph (1 / 2 : ℝ) (1 / 2) (by norm_num)
  let interval : Set.Ioo (-1 : ℝ) 1 ≃ₜ Set.Ioo (0 : ℝ) 1 := affine.subtype (by
    intro t
    change (-1 < t ∧ t < 1) ↔
      (0 < 1 / 2 * t + 1 / 2 ∧ 1 / 2 * t + 1 / 2 < 1)
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2])
  let p := (orderIsoIooNegOneOne ℝ).toHomeomorph.trans interval
  have hp : StrictMono p := by
    intro x y hxy
    change 1 / 2 * ((orderIsoIooNegOneOne ℝ) x).val + 1 / 2 <
      1 / 2 * ((orderIsoIooNegOneOne ℝ) y).val + 1 / 2
    have ho := (orderIsoIooNegOneOne ℝ).strictMono hxy
    change ((orderIsoIooNegOneOne ℝ) x).val <
      ((orderIsoIooNegOneOne ℝ) y).val at ho
    linarith [ho]
  let po := StrictMono.orderIsoOfRightInverse p hp p.symm p.apply_symm_apply
  obtain ⟨ray, hray0, hrayexp⟩ := parameterExtension po
  let C : Set Z := {z | z.val.1 ∈ A}
  have hC : IsClosed C := hA.preimage continuous_subtype_val.fst
  let := hC.locallyCompactSpace
  let eRay : (A × NNReal) ≃ₜ C := {
    toFun := fun q ↦ ⟨⟨(q.1.val, (ray q.2).val), (ray q.2).property.1,
      (ray q.2).property.2, Or.inr q.1.property⟩, q.1.property⟩
    invFun := fun z ↦ (⟨z.val.val.1, z.property⟩,
      ray.symm ⟨z.val.val.2, z.val.property.1, z.val.property.2.1⟩)
    left_inv := fun q ↦ Prod.ext rfl (ray.symm_apply_apply q.2)
    right_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl (congrArg Subtype.val (ray.apply_symm_apply _))
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (ray.continuous.comp continuous_snd))
    continuous_invFun := by
      apply Continuous.prodMk
      · exact ((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).fst.comp
          continuous_subtype_val).subtype_mk _
      · exact ray.symm.continuous.comp
          (((continuous_subtype_val : Continuous (Subtype.val : Z → X × ℝ)).snd.comp
            continuous_subtype_val).subtype_mk _) }
  let toRay : ((A × V) × NNReal) ≃ₜ ((A × NNReal) × V) :=
    (Homeomorph.prodAssoc A V NNReal).trans
      (((Homeomorph.refl A).prodCongr (Homeomorph.prodComm V NNReal)).trans
        (Homeomorph.prodAssoc A NNReal V).symm)
  let inc : C(C, Z) := ⟨Subtype.val, continuous_subtype_val⟩
  let F : C((A × V) × NNReal, Z × V) :=
    (inc.prodMap (ContinuousMap.id V)).comp
      ⟨toRay.trans (eRay.prodCongr (Homeomorph.refl V)),
        (toRay.trans (eRay.prodCongr (Homeomorph.refl V))).continuous⟩
  have hF : IsProperMap F :=
    (hC.isProperMap_subtypeVal.prodMap isProperMap_id).comp
      (toRay.trans (eRay.prodCongr (Homeomorph.refl V))).isProperMap
  let E := halfRayZeroSection (A × V)
  have hE : IsClosed E := isClosed_halfRayZeroSection (A × V)
  let := hE.locallyCompactSpace
  let := hE.isOpen_compl.locallyCompactSpace
  let eZero := halfRayZeroSectionHomeomorph (A × V)
  let g : C(E, D) := (⟨eD, eD.continuous⟩ : C(X × V, D)).comp
    (f.comp ⟨eZero.symm, eZero.symm.continuous⟩)
  have hg : IsProperMap g := eD.isProperMap.comp (hf.comp eZero.symm.isProperMap)
  let U : Set (Z × V) := Prod.fst ⁻¹' boundaryCylinderTubeOpen A
  have hU : IsOpen U := (isOpen_boundaryCylinderTubeOpen A).preimage continuous_fst
  let := hU.locallyCompactSpace
  have hUD : U = Dᶜ := by
    ext z
    change 0 < z.1.val.2 ↔ z.1.val.2 ≠ 0
    constructor
    · exact ne_of_gt
    · intro hz
      exact lt_of_le_of_ne z.1.property.1 (Ne.symm hz)
  let eUD := Homeomorph.setCongr hUD
  let eTube := (shuffle A).trans
    (((boundaryCylinderTubeHomeomorph A).prodCongr (Homeomorph.refl V)).trans
      ((subspaceProdHomeomorph (boundaryCylinderTubeOpen A) V).trans eUD))
  let half := halfRayComplementHomeomorph (A × V)
  let j : C((Eᶜ : Set ((A × V) × NNReal)), (Dᶜ : Set (Z × V))) :=
    ⟨half.trans eTube, (half.trans eTube).continuous⟩
  have hj : IsProperMap j := (half.trans eTube).isProperMap
  have hpre : F ⁻¹' D = E := by
    ext q
    change (ray q.2).val = 0 ↔ q.2 = 0
    constructor
    · intro hq
      exact ray.injective (Subtype.ext (hq.trans hray0.symm))
    · intro hq
      rw [hq]
      exact hray0
  have hgval (q : E) : (g q).val = F q.val := by
    apply Prod.ext
    · apply Subtype.ext
      refine Prod.ext rfl ?_
      change 0 = (ray q.val.2).val
      rw [q.property]
      exact hray0.symm
    · rfl
  have hjval (q : (Eᶜ : Set ((A × V) × NNReal))) : (j q).val = F q.val := by
    have hq : 0 < (q.val.2 : ℝ) := by
      exact lt_of_le_of_ne q.val.2.property (Ne.symm (NNReal.coe_ne_zero.mpr q.property))
    have hre : (⟨Real.exp (Real.log (q.val.2 : ℝ)),
        (Real.exp_pos _).le⟩ : NNReal) = q.val.2 := NNReal.eq (Real.exp_log hq)
    have hh := hrayexp (Real.log (q.val.2 : ℝ))
    rw [hre] at hh
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext rfl hh.symm
    · rfl
  have hn := boundaryNaturalOfPreimageEq D hD F hF E hE hpre g hg j hj hgval hjval
  have hzeroSquare (a : ComplexBundle.CompactSupportBundleKMinusOne (X × V)) :
      ComplexBundle.compactSupportBundleKMinusOnePullback g hg
          (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eD a) =
        ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eZero
          (ComplexBundle.compactSupportBundleKMinusOnePullback f hf a) := by
    change ComplexBundle.compactSupportBundleKMinusOnePullback g hg
      (ComplexBundle.compactSupportBundleKMinusOnePullback
        ⟨eD.symm, eD.symm.continuous⟩ eD.symm.isProperMap a) =
      ComplexBundle.compactSupportBundleKMinusOnePullback
        ⟨eZero.symm, eZero.symm.continuous⟩ eZero.symm.isProperMap
        (ComplexBundle.compactSupportBundleKMinusOnePullback f hf a)
    rw [← AddMonoidHom.comp_apply,
      ← ComplexBundle.compactSupportBundleKMinusOnePullback_comp,
      ← AddMonoidHom.comp_apply,
      ← ComplexBundle.compactSupportBundleKMinusOnePullback_comp]
    have heq : (⟨eD.symm, eD.symm.continuous⟩ : C(D, X × V)).comp g =
        f.comp ⟨eZero.symm, eZero.symm.continuous⟩ := by
      apply ContinuousMap.ext
      intro q
      exact eD.symm_apply_apply (f (eZero.symm q))
    simp only [heq]
  have hboundary (a : ComplexBundle.CompactSupportBundleKMinusOne (X × V)) :
      ComplexBundle.compactSupportBundleKMinusOneBoundary D hD
          (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eD a) =
        compactSupportKZeroHomeomorph eTube
          (ComplexBundle.compactSupportBundleKMinusOneSuspension (A × V)
            (ComplexBundle.compactSupportBundleKMinusOnePullback f hf a)) := by
    apply (compactSupportKZeroHomeomorph_bijective (half.trans eTube).symm).1
    have he := DFunLike.congr_fun hn
      (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eD a)
    simp only [AddMonoidHom.comp_apply] at he
    rw [hzeroSquare] at he
    change compactSupportKZeroPullback j hj _ = _
    rw [he]
    change _ = compactSupportKZeroPullback ⟨half.trans eTube, (half.trans eTube).continuous⟩
      (half.trans eTube).isProperMap
      (compactSupportKZeroPullback ⟨eTube.symm, eTube.symm.continuous⟩
        eTube.symm.isProperMap
        (compactSupportKZeroPullback ⟨half.symm, half.symm.continuous⟩
          half.symm.isProperMap _))
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    have hid : (⟨half.symm, half.symm.continuous⟩ :
        C((A × V) × ℝ, (Eᶜ : Set ((A × V) × NNReal)))).comp
        ((⟨eTube.symm, eTube.symm.continuous⟩ : C((Dᶜ : Set (Z × V)), (A × V) × ℝ)).comp j) =
        ContinuousMap.id (Eᶜ : Set ((A × V) × NNReal)) := by
      apply ContinuousMap.ext
      intro q
      exact (half.trans eTube).symm_apply_apply q
    dsimp only [j] at hid
    simp only [hid]
    exact (DFunLike.congr_fun (compactSupportKZeroPullback_id
      (X := (Eᶜ : Set ((A × V) × NNReal)))) _).symm
  -- Identify the original tube map, including its original first-coordinate convention.
  have hopen (a : CompactSupportKZero U) :
      compactSupportKZeroOpenExtension Dᶜ hD.isOpen_compl
          (compactSupportKZeroHomeomorph eUD a) =
        compactSupportKZeroOpenExtension U hU a := by
    have transport (B C : Set (Z × V)) (hB : IsOpen B) (hC : IsOpen C)
        (hBC : B = C) :
        letI := hB.locallyCompactSpace
        letI := hC.locallyCompactSpace
        ∀ b : CompactSupportKZero B,
          compactSupportKZeroOpenExtension C hC
              (compactSupportKZeroHomeomorph (Homeomorph.setCongr hBC) b) =
            compactSupportKZeroOpenExtension B hB b := by
      subst C
      let := hB.locallyCompactSpace
      intro b
      change compactSupportKZeroOpenExtension B hB
        (compactSupportKZeroPullback (ContinuousMap.id B) isProperMap_id b) = _
      rw [compactSupportKZeroPullback_id]
      rfl
    exact transport U Dᶜ hU hD.isOpen_compl hUD a
  have hbeta (a : ComplexBundle.CompactSupportBundleKMinusOne (A × V)) :
      compactSupportKBoundaryTube n A hA (kA a) =
        compactSupportKZeroOpenExtension Dᶜ hD.isOpen_compl
          (compactSupportKZeroHomeomorph eTube
            (ComplexBundle.compactSupportBundleKMinusOneSuspension (A × V) a)) := by
    let := (isOpen_boundaryCylinderTubeOpen A).locallyCompactSpace
    let s := ComplexBundle.compactSupportBundleKMinusOneSuspension (A × V) a
    let eW := subspaceProdHomeomorph (boundaryCylinderTubeOpen A) V
    let eT := (boundaryCylinderTubeHomeomorph A).prodCongr (Homeomorph.refl V)
    have hcoords : compactSupportKZeroHomeomorph eUD
        (compactSupportKZeroHomeomorph eW (compactSupportKZeroHomeomorph eT
          (compactSupportKZeroHomeomorph (suspensionCoordinateHomeomorph A n).symm
            (compactSupportKZeroHomeomorph (coord A) s)))) =
        compactSupportKZeroHomeomorph eTube s := by
      change compactSupportKZeroPullback _ _
        (compactSupportKZeroPullback _ _ (compactSupportKZeroPullback _ _
          (compactSupportKZeroPullback _ _ (compactSupportKZeroPullback _ _ s)))) =
          compactSupportKZeroPullback _ _ s
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      congr 1
    rw [← hcoords, hopen]
    rfl
  have hseq := ComplexBundle.range_compactSupportBundleKMinusOneBoundary D hD
  have htube : (compactSupportKClosedRestriction (n + 1) A hA).range =
      (compactSupportKBoundaryTube n A hA).ker := by
    apply le_antisymm
    · rintro a ⟨b, rfl⟩
      obtain ⟨c, rfl⟩ := kX.surjective b
      change compactSupportKBoundaryTube n A hA
        (compactSupportKClosedRestriction (n + 1) A hA (kX c)) = 0
      rw [hrestriction, hbeta, ← hboundary]
      exact hseq.le ⟨_, rfl⟩
    · intro a ha
      obtain ⟨b, rfl⟩ := kA.surjective a
      have hz : compactSupportKZeroHomeomorph eTube
          (ComplexBundle.compactSupportBundleKMinusOneSuspension (A × V) b) ∈
          (compactSupportKZeroOpenExtension Dᶜ hD.isOpen_compl).ker := by
        change compactSupportKZeroOpenExtension Dᶜ hD.isOpen_compl _ = 0
        rw [← hbeta]
        exact ha
      obtain ⟨c, hc⟩ := hseq.ge hz
      obtain ⟨d, rfl⟩ :=
        (ComplexBundle.compactSupportBundleKMinusOneHomeomorphEquiv eD).surjective c
      rw [hboundary] at hc
      have heq : ComplexBundle.compactSupportBundleKMinusOnePullback f hf d = b :=
        (ComplexBundle.compactSupportBundleKMinusOneSuspension_bijective (A × V)).1
          ((compactSupportKZeroHomeomorph_bijective eTube).1 hc)
      exact ⟨kX d, (hrestriction d).trans (congrArg kA heq)⟩
  -- The same independently bijective alpha changes neither the zero kernel nor its preimages.
  let alpha := AddEquiv.ofBijective (compactSupportKBoundaryBase n A hA)
    (compactSupportKBoundaryBase_bijective n A hA)
  have hcancel (a : CompactSupportK (n + 1) A) :
      alpha (compactSupportKBoundary n A hA a) = compactSupportKBoundaryTube n A hA a :=
    alpha.apply_symm_apply _
  rw [htube]
  ext a
  change compactSupportKBoundaryTube n A hA a = 0 ↔
    compactSupportKBoundary n A hA a = 0
  rw [← hcancel]
  exact map_eq_zero_iff alpha alpha.injective

/-- KA II.4.13: exactness at the open complement. -/
theorem range_compactSupportKBoundary_eq_ker_openExtension
    (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    (compactSupportKBoundary n A hA).range =
      (compactSupportKOpenExtension n Aᶜ hA.isOpen_compl).ker := by
  /- Stage 1: the complement of the positive-height tube is the whole closed
  bottom, homeomorphic to X × ℝⁿ. Independent supported K-zero exactness makes
  the image of the actual tube extension β the kernel of bottom restriction.
  Stage 2: proper base change identifies bottom restriction after α with the
  original open extension from X ∖ A. Cancelling the same bijective α gives
  range(α⁻¹β) equal to that open extension's kernel. -/
  classical
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let := locallyCompactSpace_boundaryCylinder A hA
  let Z := BoundaryCylinder A
  let V := Fin n → ℝ
  -- the actual closed bottom is homeomorphic to X × R^n.
  let U : Set (Z × V) := Prod.fst ⁻¹' boundaryCylinderTubeOpen A
  have hU : IsOpen U := (isOpen_boundaryCylinderTubeOpen A).preimage continuous_fst
  let D := Uᶜ
  have hD : IsClosed D := hU.isClosed_compl
  let := hU.locallyCompactSpace
  let := hD.locallyCompactSpace
  let := hD.isOpen_compl.locallyCompactSpace
  let eD : (X × V) ≃ₜ D := {
    toFun := fun p ↦ ⟨(⟨(p.1, 0), le_rfl, zero_lt_one, Or.inl rfl⟩, p.2),
      by change ¬ 0 < (0 : ℝ); exact lt_irrefl 0⟩
    invFun := fun p ↦ (p.val.1.val.1, p.val.2)
    left_inv := fun _ ↦ rfl
    right_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hp : ¬ 0 < p.val.1.val.2 := p.property
          exact (le_antisymm (not_lt.mp hp) p.val.1.property.1).symm
      · rfl
    continuous_toFun := by fun_prop
    continuous_invFun :=
      ((continuous_subtype_val : Continuous
        (Subtype.val : BoundaryCylinder A → X × ℝ)).comp
          continuous_subtype_val.fst).fst.prodMk continuous_subtype_val.snd }
  let iD : C(D, Z × V) := ⟨Subtype.val, continuous_subtype_val⟩
  let qD : C(X × V, D) := ⟨eD, eD.continuous⟩
  let j := iD.comp qD
  have hiD : IsProperMap iD := hD.isProperMap_subtypeVal
  have hj : IsProperMap j := hiD.comp eD.isProperMap
  let R := compactSupportKZeroPullback iD hiD
  let Q := compactSupportKZeroPullback qD eD.isProperMap
  let P := compactSupportKZeroPullback j hj
  have hQinj : Function.Injective Q :=
    (compactSupportKZeroHomeomorph_bijective eD.symm).1
  have hbottom (a : CompactSupportK n Z) : Q (R a) = P a := by
    rw [← AddMonoidHom.comp_apply]
    exact DFunLike.congr_fun (compactSupportKZeroPullback_comp qD iD
      eD.isProperMap hiD).symm a
  -- independent K-zero exactness identifies the image of the same beta.
  let W := boundaryCylinderTubeOpen A
  have hW : IsOpen W := isOpen_boundaryCylinderTubeOpen A
  let := hW.locallyCompactSpace
  let eW := subspaceProdHomeomorph W V
  let eT := compactSupportKHomeomorphEquiv n (boundaryCylinderTubeHomeomorph A)
  let eS := compactSupportKZeroHomeomorphEquiv (suspensionCoordinateHomeomorph A n).symm
  let T := (compactSupportKZeroHomeomorph eW).comp
    (eT.toAddMonoidHom.comp eS.toAddMonoidHom)
  have hTbij : Function.Bijective T :=
    (compactSupportKZeroHomeomorph_bijective eW).comp
      (eT.bijective.comp eS.bijective)
  have hbeta (a : CompactSupportK (n + 1) A) :
      compactSupportKBoundaryTube n A hA a = compactSupportKZeroOpenExtension U hU (T a) :=
    rfl
  have hseq : (compactSupportKZeroOpenExtension U hU).range = P.ker := by
    have hs := ComplexBundle.range_compactSupportKZeroOpenExtension D hD
    have hu : Dᶜ = U := compl_compl U
    have htransport (C : Set (Z × V)) (hC : IsOpen C) (hCU : C = U) :
        (compactSupportKZeroOpenExtension C hC).range = R.ker →
          (compactSupportKZeroOpenExtension U hU).range = R.ker := by
      subst C
      exact id
    have hs' := htransport Dᶜ hD.isOpen_compl hu hs
    apply le_antisymm
    · intro a ha
      change P a = 0
      rw [← hbottom, hs'.le ha, map_zero]
    · intro a ha
      apply hs'.ge
      change R a = 0
      apply hQinj
      rw [map_zero, hbottom]
      exact ha
  have hbetaseq : (compactSupportKBoundaryTube n A hA).range = P.ker := by
    apply le_antisymm
    · rintro a ⟨b, rfl⟩
      apply hseq.le
      exact ⟨T b, (hbeta b).symm⟩
    · intro a ha
      obtain ⟨b, hb⟩ := hseq.ge ha
      obtain ⟨c, hc⟩ := hTbij.2 b
      exact ⟨c, (hbeta c).trans (by rw [hc]; exact hb)⟩
  -- proper base change identifies bottom restriction after alpha.
  let B : Set (Z × V) := Prod.fst ⁻¹' boundaryCylinderBaseOpen A
  have hB : IsOpen B := (isOpen_boundaryCylinderBaseOpen A hA).preimage continuous_fst
  let C : Set (X × V) := Prod.fst ⁻¹' Aᶜ
  have hC : IsOpen C := hA.isOpen_compl.preimage continuous_fst
  let := hB.locallyCompactSpace
  let := hC.locallyCompactSpace
  let := (hB.preimage j.continuous).locallyCompactSpace
  let := (isOpen_boundaryCylinderBaseOpen A hA).locallyCompactSpace
  let eB := subspaceProdHomeomorph (boundaryCylinderBaseOpen A) V
  let eBase := (boundaryCylinderBaseHomeomorph A).prodCongr (Homeomorph.refl V)
  let eC := subspaceProdHomeomorph Aᶜ V
  let k := preimageSubspaceMap B j
  have hk : IsProperMap k := isProperMap_preimageSubspaceMap B j hj
  have hcoords (a : CompactSupportK n (Aᶜ : Set X)) :
      compactSupportKZeroPullback k hk
          (compactSupportKZeroHomeomorph eB (compactSupportKZeroHomeomorph eBase a)) =
        compactSupportKZeroHomeomorph eC a := by
    change compactSupportKZeroPullback k hk
        (compactSupportKZeroPullback ⟨eB.symm, eB.symm.continuous⟩ eB.symm.isProperMap
          (compactSupportKZeroPullback ⟨eBase.symm, eBase.symm.continuous⟩
            eBase.symm.isProperMap a)) =
      compactSupportKZeroPullback ⟨eC.symm, eC.symm.continuous⟩ eC.symm.isProperMap a
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  have halpha (a : CompactSupportK n (Aᶜ : Set X)) :
      P (compactSupportKBoundaryBase n A hA a) =
        compactSupportKOpenExtension n Aᶜ hA.isOpen_compl a := by
    have hn := compactSupportKZeroPullback_openExtension B hB j hj
    change P (compactSupportKZeroOpenExtension B hB
        (compactSupportKZeroHomeomorph eB (compactSupportKZeroHomeomorph eBase a))) = _
    calc
      _ = compactSupportKZeroOpenExtension C hC
          (compactSupportKZeroPullback k hk
            (compactSupportKZeroHomeomorph eB (compactSupportKZeroHomeomorph eBase a))) :=
        DFunLike.congr_fun hn _
      _ = compactSupportKZeroOpenExtension C hC (compactSupportKZeroHomeomorph eC a) := by
        rw [hcoords]
      _ = compactSupportKOpenExtension n Aᶜ hA.isOpen_compl a := rfl
  -- Cancel the original bijective alpha to obtain the boundary range.
  let alpha := AddEquiv.ofBijective (compactSupportKBoundaryBase n A hA)
    (compactSupportKBoundaryBase_bijective n A hA)
  have hcancel (a : CompactSupportK (n + 1) A) :
      alpha (compactSupportKBoundary n A hA a) = compactSupportKBoundaryTube n A hA a :=
    alpha.apply_symm_apply _
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    change compactSupportKOpenExtension n Aᶜ hA.isOpen_compl
      (compactSupportKBoundary n A hA b) = 0
    rw [← halpha]
    change P (alpha (compactSupportKBoundary n A hA b)) = 0
    rw [hcancel]
    exact hbetaseq.le ⟨b, rfl⟩
  · intro a ha
    have hz : P (alpha a) = 0 := by
      change P (compactSupportKBoundaryBase n A hA a) = 0
      rw [halpha]
      exact ha
    obtain ⟨b, hb⟩ := hbetaseq.ge hz
    refine ⟨b, alpha.injective ?_⟩
    exact (hcancel b).trans hb

/-- KA II.4.13: exactness at the ambient space, with actual restriction and extension. -/
theorem range_compactSupportKOpenExtension_eq_ker_closedRestriction
    (n : ℕ) (A : Set X) (hA : IsClosed A) :
    letI := hA.locallyCompactSpace
    letI := hA.isOpen_compl.locallyCompactSpace
    (compactSupportKOpenExtension n Aᶜ hA.isOpen_compl).range =
      (compactSupportKClosedRestriction n A hA).ker := by
  /- Stage 1: apply the independent supported K-zero exactness theorem to the
  closed product pair in X × ℝⁿ. Its restriction is pullback along the same
  inclusion used by the suspended closed restriction.
  Stage 2: transport that image-kernel equality through the actual product-subspace
  homeomorphisms on the closed set and its open complement. Their bijectivity
  preserves the prescribed restriction and extension maps. -/
  classical
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  -- use the original closed product pair and its actual subspace maps.
  let V := Fin n → ℝ
  let B : Set (X × V) := Prod.fst ⁻¹' A
  have hB : IsClosed B := hA.preimage continuous_fst
  let := hB.locallyCompactSpace
  let := hB.isOpen_compl.locallyCompactSpace
  let := (hA.isOpen_compl.preimage
    (continuous_fst : Continuous (Prod.fst : X × V → X))).locallyCompactSpace
  let eA := subspaceProdHomeomorph A V
  let eC := subspaceProdHomeomorph Aᶜ V
  -- restriction is pullback along the very same product inclusion.
  let j : C(B, X × V) := ⟨Subtype.val, continuous_subtype_val⟩
  let i : C(A × V, X × V) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).prodMap (ContinuousMap.id V)
  let q : C(A × V, B) := ⟨eA, eA.continuous⟩
  have hi : IsProperMap i := hA.isProperMap_subtypeVal.prodMap isProperMap_id
  have hj : IsProperMap j := hB.isProperMap_subtypeVal
  let R := compactSupportKZeroPullback j hj
  let Q := compactSupportKZeroPullback q eA.isProperMap
  have hQinj : Function.Injective Q :=
    (compactSupportKZeroHomeomorph_bijective eA.symm).1
  have hrestriction (a : CompactSupportK n X) :
      Q (R a) = compactSupportKClosedRestriction n A hA a := by
    change compactSupportKZeroPullback q eA.isProperMap
      (compactSupportKZeroPullback j hj a) = compactSupportKZeroPullback i hi a
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  -- transport independent supported exactness through both equivalences.
  have hseq := ComplexBundle.range_compactSupportKZeroOpenExtension B hB
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    change compactSupportKClosedRestriction n A hA
      (compactSupportKZeroOpenExtension Bᶜ hB.isOpen_compl
        (compactSupportKZeroHomeomorph eC b)) = 0
    rw [← hrestriction]
    have hz : R (compactSupportKZeroOpenExtension Bᶜ hB.isOpen_compl
        (compactSupportKZeroHomeomorph eC b)) = 0 :=
      hseq.le ⟨compactSupportKZeroHomeomorph eC b, rfl⟩
    rw [hz, map_zero]
  · intro a ha
    have hzero : R a = 0 := by
      apply hQinj
      rw [map_zero, hrestriction]
      exact ha
    obtain ⟨b, hb⟩ := hseq.ge hzero
    obtain ⟨c, hc⟩ := (compactSupportKZeroHomeomorph_bijective eC).2 b
    refine ⟨c, ?_⟩
    change compactSupportKZeroOpenExtension Bᶜ hB.isOpen_compl
      (compactSupportKZeroHomeomorph eC c) = a
    rw [hc]
    exact hb

end AtiyahSinger
