/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanSpinStructure
public import AtiyahSinger.Geometry.SmoothSpinPrincipalAtlas
public import AtiyahSinger.Geometry.SpinStructure
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Smooth lifting of the original spin frames

Public module ID: M1457.

A continuous lift to the original spin subgroup is smooth exactly when its
actual vector representation is smooth. The continuity assumption matters:
a discontinuous choice between the two central lifts has the same vector
matrix. Smoothness here is measured in the already specified real Clifford
coordinates, not in a newly selected group topology.

The compatible principal atlas of a topological spin structure is obtained
by lifting local smooth positive orthonormal frames of the original smooth
metric bundle. Its transition functions and its actual frame columns are
smooth. Abstractly smooth principal transitions alone would not rule out a
continuous nonsmooth gauge change of the original frame map.

Sources: SG I.2 Theorem 2.10 and II.1 Definition 1.3, pp.20 and 80, with the
separate low-dimensional conventions of II.1; Gilkey section 3.3 pp.165--171.
The ambient-coordinate smooth-lift criterion expands the local smooth
covering argument. For dimension two the covering is not universal; rank
zero in the criterion is the project's native one-element group extension.
The continuous metric certificate is retained from the existing topological
spin input; it is redundant mathematically with smooth metric compatibility.
No existence of a spin structure, connection, curvature or Dirac operator
is asserted. The Clifford-coordinate smooth-lift criterion and compatible
principal-atlas constructions are proved on the original carriers below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

attribute [local instance] realSpinorCliffordNormedAddCommGroup
  realSpinorCliffordNormedSpace spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

/-- The even elements commuting with every original Euclidean vector are precisely scalars. -/
theorem euclideanSpin_exists_scalar_of_involute_eq_of_commute (r : ℕ)
    (a : CliffordAlgebra (euclideanSpinQuadraticForm r))
    (heven : CliffordAlgebra.involute a = a)
    (hcomm : ∀ v : EuclideanSpace ℝ (Fin r),
      CliffordAlgebra.ι (euclideanSpinQuadraticForm r) v * a =
        a * CliffordAlgebra.ι (euclideanSpinQuadraticForm r) v) :
    ∃ t : ℝ, a = algebraMap ℝ _ t := by
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let Q := euclideanSpinQuadraticForm r
  -- The graded commutator with a vector is contraction by its polar functional.
  have hpolar (v w : V) : QuadraticMap.polar Q v w = -2 * inner ℝ v w := by
    change QuadraticMap.polar (-⇑(LinearMap.BilinMap.toQuadraticMap (innerₗ V))) v w = _
    rw [QuadraticMap.polar_neg, LinearMap.BilinMap.polar_toQuadraticMap]
    change -(inner ℝ v w + inner ℝ w v) = _
    rw [real_inner_comm w v]
    ring
  have hgraded (v : V) (b : CliffordAlgebra Q) :
      CliffordAlgebra.contractLeft ((-2 : ℝ) • innerₛₗ ℝ v) b =
        CliffordAlgebra.ι Q v * b - CliffordAlgebra.involute b * CliffordAlgebra.ι Q v := by
    induction b using CliffordAlgebra.left_induction with
    | algebraMap t =>
      rw [CliffordAlgebra.contractLeft_algebraMap, CliffordAlgebra.involute.commutes]
      exact (sub_eq_zero.mpr (Algebra.commutes t (CliffordAlgebra.ι Q v)).symm).symm
    | add b c hb hc =>
      simp only [map_add, mul_add, add_mul, hb, hc]
      abel
    | ι_mul b w hb =>
      rw [CliffordAlgebra.contractLeft_ι_mul, hb, map_mul, CliffordAlgebra.involute_ι]
      change (-2 * inner ℝ v w) • b -
          CliffordAlgebra.ι Q w *
            (CliffordAlgebra.ι Q v * b - CliffordAlgebra.involute b * CliffordAlgebra.ι Q v) = _
      rw [← hpolar, Algebra.smul_def, ← CliffordAlgebra.ι_mul_ι_add_swap]
      noncomm_ring
  have hcontract (v : V) : CliffordAlgebra.contractLeft (innerₛₗ ℝ v) a = 0 := by
    have h := hgraded v a
    rw [heven, hcomm, sub_self] at h
    have hz : (-2 : ℝ) • CliffordAlgebra.contractLeft (innerₛₗ ℝ v) a = 0 := by
      simpa only [map_smul, LinearMap.smul_apply] using h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  -- Form change commutes with contraction, so the corresponding exterior vector is a vacuum.
  let a' := CliffordAlgebra.equivExterior Q a
  have ha' (v : V) : CliffordAlgebra.contractLeft (innerₛₗ ℝ v) a' = 0 := by
    change CliffordAlgebra.contractLeft (innerₛₗ ℝ v)
      (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof a) = 0
    rw [← CliffordAlgebra.changeForm_contractLeft, hcontract, map_zero]
  let e (i : Fin r) : V := EuclideanSpace.single i (1 : ℝ)
  let z (i : Fin r) : ExteriorAlgebra ℝ V := ExteriorAlgebra.ι ℝ (e i)
  let w (i : Fin r) : Module.End ℝ (ExteriorAlgebra ℝ V) := LinearMap.mul ℝ _ (z i)
  let c (i : Fin r) : Module.End ℝ (ExteriorAlgebra ℝ V) :=
    CliffordAlgebra.contractLeft (innerₛₗ ℝ (e i))
  let mon (l : List (Fin r)) : ExteriorAlgebra ℝ V := (l.map z).prod
  -- Occupation by coordinate i acts diagonally on the ordered exterior basis.
  have hc (i j : Fin r) (x : ExteriorAlgebra ℝ V) :
      c i (z j * x) = (if i = j then x else 0) - z j * c i x := by
    change CliffordAlgebra.contractLeft (innerₛₗ ℝ (e i))
      (CliffordAlgebra.ι (0 : QuadraticForm ℝ _) (e j) * x) = _
    rw [CliffordAlgebra.contractLeft_ι_mul]
    congr 1
    change (inner ℝ (e i) (e j)) • x = _
    rw [EuclideanSpace.inner_single_left]
    by_cases hij : i = j
    · subst j
      simp [e]
    · simp [e, hij]
  have hz (i j : Fin r) : z i * z j = -(z j * z i) := by
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e i) (e j))
  have hn (i : Fin r) (l : List (Fin r)) :
      (w i * c i) (mon l) = if i ∈ l then mon l else 0 := by
    change z i * c i (mon l) = _
    induction l with
    | nil => simp [mon, c]
    | cons j l ih =>
      change z i * c i (z j * mon l) = _
      rw [hc, mul_sub]
      by_cases hij : i = j
      · subst j
        simp [mon, ← mul_assoc (z i) (z i), z]
      · rw [ite_eq_right hij, mul_zero, ← mul_assoc, hz, neg_mul, zero_sub, neg_neg,
          mul_assoc, ih]
        simp [mon, hij]
  let b : Module.Basis (Finset (Fin r)) ℝ (ExteriorAlgebra ℝ V) :=
    (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.ExteriorAlgebra
  let seq (s : Finset (Fin r)) : List (Fin r) :=
    List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl))
  have hseq (s : Finset (Fin r)) (i : Fin r) : i ∈ seq s ↔ i ∈ s := by
    exact (List.mem_ofFn' _ _).trans
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _)
  have hb (s : Finset (Fin r)) : b s = mon (seq s) := by
    rw [ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl]
    simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
      Function.comp_def, mon, seq, List.map_ofFn]
    congr 2
    funext i
    simp [z, e]
  have hnb (i : Fin r) (s : Finset (Fin r)) :
      (w i * c i) (b s) = if i ∈ s then b s else 0 := by
    simp only [hb, hn, hseq]
  have hcoeff (s : Finset (Fin r)) (hs : s.Nonempty) : b.repr a' s = 0 := by
    obtain ⟨i, hi⟩ := hs
    have hzero : (w i * c i) a' = 0 := by
      change w i (c i a') = 0
      rw [ha' (e i), map_zero]
    have hsum : (w i * c i) a' =
        ∑ t : Finset (Fin r), (b.repr a' t) • (if i ∈ t then b t else 0) := by
      conv_lhs => rw [← b.sum_repr a']
      rw [map_sum]
      simp only [map_smul, hnb]
    have h := congrArg (fun x ↦ b.repr x s) (hsum.symm.trans hzero)
    simp only [map_sum, map_smul, apply_ite, map_zero, b.repr_self] at h
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.finsetSum_apply] at h
    simp only [apply_ite (fun z : (Finset (Fin r)) →₀ ℝ ↦ z s),
      Finsupp.single_apply, Finsupp.zero_apply] at h
    have hite (t : Finset (Fin r)) :
        (if i ∈ t then if t = s then b.repr a' t else 0 else 0) =
          if t = s then b.repr a' t else 0 := by
      by_cases hts : t = s
      · subst t
        simp [hi]
      · simp [hts]
    simp only [smul_zero, Finsupp.zero_apply] at h
    have h2 : (∑ t : Finset (Fin r),
        if i ∈ t then if t = s then b.repr a' t else 0 else 0) = 0 := h
    simp_rw [hite] at h2
    simpa using h2
  have ha_scalar : a' = (b.repr a' ∅) • b ∅ := by
    apply b.repr.injective
    ext s
    by_cases hs : s = ∅
    · subst s
      simp
    · simp [hcoeff s (Finset.nonempty_iff_ne_empty.mpr hs), hs]
  have hbempty : b ∅ = 1 := by
    rw [hb]
    simp [mon, seq]
  refine ⟨b.repr a' ∅, ?_⟩
  apply (CliffordAlgebra.equivExterior Q).injective
  change a' = CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof
    (algebraMap ℝ _ (b.repr a' ∅))
  rw [CliffordAlgebra.changeForm_algebraMap, Algebra.algebraMap_eq_smul_one]
  exact ha_scalar.trans (congrArg ((b.repr a' ∅) • ·) hbempty)


variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] (I : ModelWithCorners ℝ EB HB)
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]

section GeneralDimension

attribute [local instance] euclideanSpinGroupTopology euclideanSpinGroup_isTopologicalGroup
  euclideanOrientedFrameTopology

set_option maxHeartbeats 1000000 in
-- The inverse-function argument uses the full finite Clifford coordinate space.
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In every dimension, a continuous native spin lift is smooth iff its vector matrix is smooth. -/
theorem contMDiffOn_euclideanSpin_iff_vectorRepresentation (r : ℕ) (U : Set B)
    (f : B → spinGroup (euclideanSpinQuadraticForm r)) (hf : ContinuousOn f U) :
    ContMDiffOn I 𝓘(ℝ, Finset (Fin r) → ℝ) ∞
        (fun x ↦ euclideanSpinCliffordCoordinates r (f x).val) U ↔
      ∀ i : Fin r,
        ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞
          (fun x ↦ euclideanSpinVectorRepresentation r (f x)
            (EuclideanSpace.basisFun (Fin r) ℝ i)) U := by
  let Q := euclideanSpinQuadraticForm r
  let C := CliffordAlgebra Q
  let := euclideanSpinCliffordNormedAddCommGroup r
  let := euclideanSpinCliffordNormedSpace r
  let : FiniteDimensional ℝ C :=
    FiniteDimensional.of_injective (euclideanSpinCliffordCoordinates r).toLinearMap
      (euclideanSpinCliffordCoordinates r).injective
  constructor
  · intro h i
    -- Clifford multiplication is a finite-dimensional bilinear operation.
    let product : C →L[ℝ] C →L[ℝ] C :=
      (LinearMap.toContinuousLinearMap.toLinearMap.comp
        (LinearMap.mul ℝ C)).toContinuousLinearMap
    let coordinates : C ≃L[ℝ] (Finset (Fin r) → ℝ) :=
      (euclideanSpinCliffordCoordinates r).toContinuousLinearEquiv
    have hval : ContMDiffOn I 𝓘(ℝ, C) ∞ (fun x ↦ (f x).val) U := by
      have hc := coordinates.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn h
      convert hc using 1
      funext x
      exact (coordinates.symm_apply_apply (f x).val).symm
    -- On the original spin group, inversion is the linear Clifford conjugation.
    let conjugate : C →L[ℝ] C :=
      (CliffordAlgebra.reverse.comp CliffordAlgebra.involute.toLinearMap).toContinuousLinearMap
    have hinv : ContMDiffOn I 𝓘(ℝ, C) ∞
        (fun x ↦ ((f x)⁻¹ : spinGroup Q).val) U := by
      exact conjugate.contMDiff.comp_contMDiffOn hval
    have hconj : ContMDiffOn I 𝓘(ℝ, C) ∞
        (fun x ↦ (f x).val *
          CliffordAlgebra.ι Q (EuclideanSpace.basisFun (Fin r) ℝ i) *
            ((f x)⁻¹ : spinGroup Q).val) U :=
      (product.contMDiff.comp_contMDiffOn
        ((product.contMDiff.comp_contMDiffOn hval).clm_apply contMDiffOn_const)).clm_apply hinv
    -- A fixed linear left inverse extracts precisely the original vector coordinates.
    have hinjective : Function.Injective (CliffordAlgebra.ι Q) := by
      intro v w hvw
      exact (euclideanSpinVectorEmbeddingEquiv r).injective (Subtype.ext hvw)
    have hleft := LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr hinjective)
    have hformula (x : B) :
        (CliffordAlgebra.ι Q).leftInverse
          ((f x).val * CliffordAlgebra.ι Q (EuclideanSpace.basisFun (Fin r) ℝ i) *
            ((f x)⁻¹ : spinGroup Q).val) =
          euclideanSpinVectorRepresentation r (f x) (EuclideanSpace.basisFun (Fin r) ℝ i) := by
      rw [← (euclideanSpinVectorRepresentation_properties r (f x)
        (EuclideanSpace.basisFun (Fin r) ℝ i)).1]
      apply hleft
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', hformula] using
      (CliffordAlgebra.ι Q).leftInverse.toContinuousLinearMap.contMDiff.comp_contMDiffOn hconj
  · intro h
    -- The inverse function theorem recovers the specified sheet near the original group unit.
    have hunit (x : B) (f : B → spinGroup (euclideanSpinQuadraticForm r))
        (hf : ContinuousWithinAt f U x) (hfx : f x = 1)
        (hA : ∀ i : Fin r,
          ContMDiffWithinAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞
            (fun y ↦ euclideanSpinVectorRepresentation r (f y)
              (EuclideanSpace.basisFun (Fin r) ℝ i)) U x) :
        ContMDiffWithinAt I 𝓘(ℝ, Finset (Fin r) → ℝ) ∞
          (fun y ↦ euclideanSpinCliffordCoordinates r (f y).val) U x := by
      let Q := euclideanSpinQuadraticForm r
      let C := CliffordAlgebra Q
      let : AddCommGroup C := (euclideanSpinCliffordNormedAddCommGroup r).toAddCommGroup
      let : FiniteDimensional ℝ C :=
        FiniteDimensional.of_injective (euclideanSpinCliffordCoordinates r).toLinearMap
          (euclideanSpinCliffordCoordinates r).injective
      let product : C →L[ℝ] C →L[ℝ] C :=
        (LinearMap.toContinuousLinearMap.toLinearMap.comp
          (LinearMap.mul ℝ C)).toContinuousLinearMap
      let conjugate : C →L[ℝ] C :=
        (CliffordAlgebra.reverse.comp CliffordAlgebra.involute.toLinearMap).toContinuousLinearMap
      let involution : C →L[ℝ] C := CliffordAlgebra.involute.toLinearMap.toContinuousLinearMap
      let e (i : Fin r) : C := CliffordAlgebra.ι Q (EuclideanSpace.basisFun (Fin r) ℝ i)
      let D := (Fin r → C) × C × C
      -- Record conjugation, the unit-norm equation and parity in one ambient polynomial map.
      let P : C → D := fun q ↦
        ((fun i ↦ q * e i * conjugate q), conjugate q * q, involution q - q)
      have hP : ContDiff ℝ ∞ P := by
        apply ContDiff.prodMk
        · apply contDiff_pi.mpr
          intro i
          exact ((product.contDiff.comp
            ((product.contDiff.comp contDiff_id).clm_apply contDiff_const)).clm_apply
              conjugate.contDiff)
        · exact ((product.contDiff.comp conjugate.contDiff).clm_apply contDiff_id).prodMk
            (involution.contDiff.sub contDiff_id)
      let dP : C →L[ℝ] D :=
        (ContinuousLinearMap.pi fun i ↦ product.flip (e i) + (product (e i)).comp conjugate).prod
          ((conjugate + ContinuousLinearMap.id ℝ C).prod
            (involution - ContinuousLinearMap.id ℝ C))
      have hdP : HasFDerivAt P dP (1 : C) := by
        apply HasFDerivAt.prodMk
        · apply hasFDerivAt_pi.mpr
          intro i
          have hd := product.hasFDerivAt_of_bilinear
            ((product.flip (e i)).hasFDerivAt (x := (1 : C))) (conjugate.hasFDerivAt (x := (1 : C)))
          refine hd.congr_fderiv ?_
          ext a
          change (1 * e i) * conjugate a + (a * e i) * conjugate 1 =
            a * e i + e i * conjugate a
          have hc1 : conjugate 1 = 1 := by
            change CliffordAlgebra.reverse (CliffordAlgebra.involute (1 : C)) = 1
            simp
          rw [hc1, one_mul, mul_one, add_comm]
        · have hn := product.hasFDerivAt_of_bilinear
            (conjugate.hasFDerivAt (x := (1 : C))) (hasFDerivAt_id (1 : C))
          have hp := (involution.hasFDerivAt (x := (1 : C))).sub (hasFDerivAt_id (1 : C))
          refine (hn.prodMk hp).congr_fderiv ?_
          apply ContinuousLinearMap.ext
          intro a
          change (conjugate 1 * a + conjugate a * 1, involution a - a) =
            (conjugate a + a, involution a - a)
          have hc1 : conjugate 1 = 1 := by
            change CliffordAlgebra.reverse (CliffordAlgebra.involute (1 : C)) = 1
            simp
          rw [hc1, one_mul, mul_one, add_comm]
      -- The derivative kernel consists of scalar skew-adjoint elements, hence is zero.
      have hinj : Function.Injective dP := by
        intro a b hab
        suffices ∀ q : C, dP q = 0 → q = 0 by
          apply sub_eq_zero.mp
          apply this (a - b)
          rw [map_sub, hab, sub_self]
        intro q hq
        have hnorm : conjugate q + q = 0 := congrArg (fun z : D ↦ z.2.1) hq
        have hpar : involution q - q = 0 := congrArg (fun z : D ↦ z.2.2) hq
        have hstar : conjugate q = -q := eq_neg_of_add_eq_zero_left hnorm
        have hcomm (v : EuclideanSpace ℝ (Fin r)) :
            CliffordAlgebra.ι Q v * q = q * CliffordAlgebra.ι Q v := by
          have heq : (LinearMap.mul ℝ C q).comp (CliffordAlgebra.ι Q) =
              ((LinearMap.mul ℝ C).flip q).comp (CliffordAlgebra.ι Q) := by
            apply (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.ext
            intro i
            have hi : q * e i + e i * conjugate q = 0 :=
              congrArg (fun z : D ↦ z.1 i) hq
            rw [hstar, mul_neg, ← sub_eq_add_neg] at hi
            exact sub_eq_zero.mp hi
          exact (LinearMap.congr_fun heq v).symm
        obtain ⟨t, ht⟩ := euclideanSpin_exists_scalar_of_involute_eq_of_commute r q
          (sub_eq_zero.mp hpar) hcomm
        have htzero : t = 0 := by
          have hnorm' : algebraMap ℝ C (t + t) = 0 := by
            calc
              algebraMap ℝ C (t + t) = conjugate q + q := by
                rw [ht]
                change algebraMap ℝ C (t + t) =
                  CliffordAlgebra.reverse (CliffordAlgebra.involute (algebraMap ℝ C t)) +
                    algebraMap ℝ C t
                rw [map_add, CliffordAlgebra.involute.commutes, CliffordAlgebra.reverse.commutes]
              _ = 0 := hnorm
          have ht' : t + t = 0 := (algebraMap ℝ C).injective (hnorm'.trans (map_zero _).symm)
          linarith
        simp [ht, htzero]
      let L : D →L[ℝ] C := dP.toLinearMap.leftInverse.toContinuousLinearMap
      have hLP : L.comp dP = ContinuousLinearMap.id ℝ C := by
        ext q
        exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hinj) q
      let F : C → C := fun q ↦ L (P q)
      have hF : ContDiffAt ℝ ∞ F (1 : C) := (L.contDiff.comp hP).contDiffAt
      have hdF : HasFDerivAt F (ContinuousLinearEquiv.refl ℝ C : C →L[ℝ] C) (1 : C) := by
        exact (L.hasFDerivAt.comp (1 : C) hdP).congr_fderiv hLP
      let inv := hF.localInverse hdF (by simp)
      have hinv : ContDiffAt ℝ ∞ inv (F 1) := hF.to_localInverse hdF (by simp)
      have hleft : ∀ᶠ q in nhds (1 : C), inv (F q) = q :=
        (hF.hasStrictFDerivAt' hdF (by simp)).eventually_left_inverse
      -- On the actual spin group the polynomial data are the given vector columns and constants.
      have hPspin (y : B) : P (f y).val =
          ((fun i ↦ CliffordAlgebra.ι Q
            (euclideanSpinVectorRepresentation r (f y)
              (EuclideanSpace.basisFun (Fin r) ℝ i))), 1, 0) := by
        apply Prod.ext
        · funext i
          exact (euclideanSpinVectorRepresentation_properties r (f y)
            (EuclideanSpace.basisFun (Fin r) ℝ i)).1.symm
        · apply Prod.ext
          · exact spinGroup.star_mul_self_of_mem (f y).property
          · exact sub_eq_zero.mpr (spinGroup.involute_eq (f y).property)
      have hPf : ContMDiffWithinAt I 𝓘(ℝ, D) ∞ (fun y ↦ P (f y).val) U x := by
        simp_rw [hPspin]
        apply ContMDiffWithinAt.prodMk_space
        · apply contMDiffWithinAt_pi_space.mpr
          intro i
          exact (CliffordAlgebra.ι Q).toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt
            x (hA i)
        · exact contMDiffWithinAt_const.prodMk_space contMDiffWithinAt_const
      have hFf : ContMDiffWithinAt I 𝓘(ℝ, C) ∞ (fun y ↦ F (f y).val) U x :=
        L.contMDiffAt.comp_contMDiffWithinAt x hPf
      have hval : ContinuousWithinAt (fun y ↦ (f y).val) U x :=
        continuous_subtype_val.continuousAt.comp_continuousWithinAt hf
      have heq : ∀ᶠ y in nhdsWithin x U, inv (F (f y).val) = (f y).val := by
        have hval' : Filter.Tendsto (fun y ↦ (f y).val) (nhdsWithin x U) (nhds (1 : C)) := by
          change Filter.Tendsto (fun y ↦ (f y).val) (nhdsWithin x U) (nhds (f x).val) at hval
          simpa only [hfx, OneMemClass.coe_one] using hval
        exact hval'.eventually hleft
      have hresult : ContMDiffWithinAt I 𝓘(ℝ, C) ∞ (fun y ↦ (f y).val) U x := by
        have hx : F (f x).val = F 1 := by rw [hfx]; rfl
        rw [← hx] at hinv
        have hlocal := hinv.comp_contMDiffWithinAt (f := fun y : B ↦ F (f y).val) hFf
        apply hlocal.congr_of_eventuallyEq (Filter.EventuallyEq.symm heq)
        change (f x).val = inv (F (f x).val)
        rw [hfx]
        exact (hF.localInverse_apply_image hdF (by simp)).symm
      exact (euclideanSpinCliffordCoordinates r).toContinuousLinearEquiv.toContinuousLinearMap
        |>.contMDiffAt.comp_contMDiffWithinAt x hresult
    -- Translate the original continuous lift to the unit and then translate its coordinates back.
    intro x hx
    let g := f x
    let f' (y : B) : spinGroup Q := g⁻¹ * f y
    have hf' : ContinuousWithinAt f' U x := continuousWithinAt_const.mul (hf x hx)
    have hfx : f' x = 1 := by simp [f', g]
    have hA' (i : Fin r) :
        ContMDiffWithinAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞
          (fun y ↦ euclideanSpinVectorRepresentation r (f' y)
            (EuclideanSpace.basisFun (Fin r) ℝ i)) U x := by
      let L := (euclideanSpinVectorRepresentation r g⁻¹).toContinuousLinearEquiv
      have hh := L.toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt x (h i x hx)
      convert! hh using 1
      funext y
      simp only [f', map_mul, LinearEquiv.mul_apply]
      rfl
    have hcoordinates := hunit x f' hf' hfx hA'
    let coordinates : C ≃L[ℝ] (Finset (Fin r) → ℝ) :=
      (euclideanSpinCliffordCoordinates r).toContinuousLinearEquiv
    have hval' : ContMDiffWithinAt I 𝓘(ℝ, C) ∞ (fun y ↦ (f' y).val) U x := by
      have hh :=
        coordinates.symm.toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt x hcoordinates
      convert hh using 1
      funext y
      exact (coordinates.symm_apply_apply (f' y).val).symm
    let leftMul : C →L[ℝ] C := (LinearMap.mul ℝ C g.val).toContinuousLinearMap
    have hrestore (y : B) : leftMul (f' y).val = (f y).val := by
      change (g * (g⁻¹ * f y)).val = (f y).val
      rw [mul_inv_cancel_left]
    have hval : ContMDiffWithinAt I 𝓘(ℝ, C) ∞ (fun y ↦ (f y).val) U x := by
      simpa only [Function.comp_def, hrestore] using
        leftMul.contMDiffAt.comp_contMDiffWithinAt x hval'
    exact coordinates.toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt x hval

variable {r : ℕ} {P : Type*} [TopologicalSpace P]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) E]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) E I]
  [IsContMDiffRiemannianBundle I ∞ (EuclideanSpace ℝ (Fin r)) E]
  [IsManifold I ∞ B]
  {o : ∀ x, Orientation ℝ (E x) (Fin r)}
  [MulAction (spinGroup (euclideanSpinQuadraticForm r))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (euclideanSpinQuadraticForm r))ᵐᵒᵖ P]
  {projection : P → B}
  {hP : IsPrincipalBundle (spinGroup (euclideanSpinQuadraticForm r)) projection}

/-- The same arbitrary-rank spin lift admits compatible smooth original principal charts. -/
theorem EuclideanSpinStructure.exists_compatible_smoothPrincipalCharts
    (S : EuclideanSpinStructure r E o hP) :
    ∃ t : B → Trivialization (spinGroup (euclideanSpinQuadraticForm r)) projection,
      (∀ b : B, b ∈ (t b).baseSet) ∧
      (∀ (b : B) (g : spinGroup (euclideanSpinQuadraticForm r)) (p : P),
        projection p ∈ (t b).baseSet →
          (t b (MulOpposite.op g • p)).2 = (t b p).2 * g) ∧
      (∀ b₀ b₁ : B,
        ContMDiffOn I 𝓘(ℝ, Finset (Fin r) → ℝ) ∞
          (fun x : B ↦ euclideanSpinCliffordCoordinates r
            (((t b₁) ((t b₀).toOpenPartialHomeomorph.symm (x, 1))).2.val))
          ((t b₀).baseSet ∩ (t b₁).baseSet)) ∧
      ∀ (b : B) (i : Fin r),
        ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
          (fun x : B ↦
            let p := (t b).toOpenPartialHomeomorph.symm (x, 1)
            let q := S.frameMap p
            (⟨q.val.1, q.val.2 (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
              TotalSpace (EuclideanSpace ℝ (Fin r)) E)) (t b).baseSet := by
  classical
  let G : Type := spinGroup (euclideanSpinQuadraticForm r)
  -- A continuous local section changes a given principal chart by its actual gauge coordinate.
  have chartOfSection (e : Trivialization G projection)
      (hequiv : ∀ (g : G) (p : P), projection p ∈ e.baseSet →
        (e (MulOpposite.op g • p)).2 = (e p).2 * g)
      (W : Set B) (hW : IsOpen W) (hsub : W ⊆ e.baseSet)
      (s : B → P) (hs : ContinuousOn s W)
      (hproj : ∀ x ∈ W, projection (s x) = x) :
      ∃ t : Trivialization G projection, t.baseSet = W ∧
        (∀ (g : G) (p : P), projection p ∈ t.baseSet →
          (t (MulOpposite.op g • p)).2 = (t p).2 * g) ∧
        ∀ x ∈ W, t.toOpenPartialHomeomorph.symm (x, 1) = s x := by
    let γ (x : B) : G := (e (s x)).2
    have hs_source (x : B) (hx : x ∈ W) : s x ∈ e.source := by
      apply e.mem_source.mpr
      rw [hproj x hx]
      exact hsub hx
    have hγ : ContinuousOn γ W :=
      (e.toOpenPartialHomeomorph.continuousOn.comp hs hs_source).snd
    have hp : Continuous projection := hP.projection_properties.1
    let φ (p : P) : B × G := (projection p, (γ (projection p))⁻¹ * (e p).2)
    let ψ (q : B × G) : P := e.toOpenPartialHomeomorph.symm (q.1, γ q.1 * q.2)
    have hψproj (q : B × G) (hq : q.1 ∈ W) : projection (ψ q) = q.1 :=
      e.proj_symm_apply' (hsub hq)
    have hφψ (q : B × G) (hq : q.1 ∈ W) : φ (ψ q) = q := by
      have he : e (ψ q) = (q.1, γ q.1 * q.2) :=
        e.apply_symm_apply (e.mem_target.mpr (hsub hq))
      dsimp only [φ]
      rw [hψproj q hq, he]
      simp
    have hψφ (p : P) (hp : projection p ∈ W) : ψ (φ p) = p := by
      have hpe : p ∈ e.source := e.mem_source.mpr (hsub hp)
      dsimp only [ψ, φ]
      rw [mul_inv_cancel_left]
      have he : (projection p, (e p).2) = e p := by
        apply Prod.ext
        · exact (e.coe_fst hpe).symm
        · rfl
      rw [he]
      exact e.toOpenPartialHomeomorph.left_inv hpe
    have hφ : ContinuousOn φ (projection ⁻¹' W) := by
      have hγp := hγ.comp hp.continuousOn (fun _ hx ↦ hx)
      have he := e.toOpenPartialHomeomorph.continuousOn.mono (fun _ hx ↦ e.mem_source.mpr (hsub hx))
      exact hp.continuousOn.prodMk (hγp.inv.mul he.snd)
    have hψ : ContinuousOn ψ (W ×ˢ Set.univ) := by
      apply e.toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_fst.continuousOn.prodMk
          ((hγ.comp continuous_fst.continuousOn (fun _ hx ↦ hx.1)).mul
            continuous_snd.continuousOn))
      intro q hq
      exact e.mem_target.mpr (hsub hq.1)
    let t : Trivialization G projection :=
      { toFun := φ
        invFun := ψ
        source := projection ⁻¹' W
        target := W ×ˢ Set.univ
        map_source' := fun {_} hp ↦ ⟨hp, Set.mem_univ _⟩
        map_target' := by
          intro q hq
          change projection (ψ q) ∈ W
          rw [hψproj q hq.1]
          exact hq.1
        left_inv' := fun {p} hp ↦ hψφ p hp
        right_inv' := fun {q} hq ↦ hφψ q hq.1
        open_source := hW.preimage hp
        open_target := hW.prod isOpen_univ
        continuousOn_toFun := hφ
        continuousOn_invFun := hψ
        baseSet := W
        open_baseSet := hW
        source_eq := rfl
        target_eq := rfl
        proj_toFun := fun _ _ ↦ rfl }
    refine ⟨t, rfl, ?_, ?_⟩
    · intro g p hp
      change (γ (projection (MulOpposite.op g • p)))⁻¹ *
        (e (MulOpposite.op g • p)).2 = ((γ (projection p))⁻¹ * (e p).2) * g
      rw [hP.projection_smul, hequiv g p (hsub hp), mul_assoc]
    · intro x hx
      change e.toOpenPartialHomeomorph.symm (x, γ x * 1) = s x
      rw [mul_one]
      have he : (x, γ x) = e (s x) := by
        apply Prod.ext
        · rw [e.coe_fst (hs_source x hx), hproj x hx]
        · rfl
      rw [he]
      exact e.toOpenPartialHomeomorph.left_inv (hs_source x hx)
  -- The specified covering lifts a continuous frame locally through the original point of P.
  have liftFrame (b : B) (U : Set B) (hU : IsOpen U) (hb : b ∈ U)
      (s : B → EuclideanOrientedFrameBundle r E o) (hs : ContinuousOn s U)
      (p : P) (hp : s b = S.frameMap p) :
      ∃ W : Set B, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧
        ∃ l : B → P, ContinuousOn l W ∧ ∀ x ∈ W, S.frameMap (l x) = s x := by
    obtain ⟨e, hpe, he⟩ := S.is_covering_map.isLocalHomeomorph p
    have htarget : s b ∈ e.target := by
      rw [hp, he]
      exact e.map_source hpe
    have hpre : s ⁻¹' e.target ∈ nhds b :=
      (hs.continuousAt (hU.mem_nhds hb)).preimage_mem_nhds (e.open_target.mem_nhds htarget)
    obtain ⟨W, hWsub, hW, hbW⟩ := mem_nhds_iff.mp
      (Filter.inter_mem (hU.mem_nhds hb) hpre)
    refine ⟨W, hW, hbW, fun x hx ↦ (hWsub hx).1,
      fun x ↦ e.symm (s x), ?_, ?_⟩
    · exact e.continuousOn_symm.comp (hs.mono (fun x hx ↦ (hWsub hx).1))
        (fun x hx ↦ (hWsub hx).2)
    · intro x hx
      rw [he]
      exact e.right_inv (hWsub hx).2
  -- Use the already proved smooth orthogonal atlas, transporting only its actual base equality.
  let := orthogonalFrameTopology r E
  obtain ⟨hAction, hAtlas⟩ := exists_smoothOrthogonalFrameAtlas r E I
  let := hAction
  obtain ⟨A, hA⟩ := hAtlas
  let q (b x : B) : OrthogonalFrameBundle r E :=
    (A.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
  have hq (b x : B) (hx : x ∈ (A.trivialization b).baseSet) : (q b x).1 = x :=
    (A.trivialization b).proj_symm_apply' hx
  let L (b x : B) : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E x :=
    if hx : x ∈ (A.trivialization b).baseSet then hq b x hx ▸ (q b x).2
    else hq x x (A.mem_baseSet x) ▸ (q x x).2
  have hcast {x y : B} (h : x = y)
      (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E x) (v : EuclideanSpace ℝ (Fin r)) :
      (h ▸ e) v = cast (congrArg E h) (e v) := by
    cases h
    rfl
  have hL (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
        (fun x ↦ (⟨x, L b x (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin r)) E)) (A.trivialization b).baseSet := by
    apply (hA b i).congr
    intro x hx
    dsimp only [L]
    rw [dite_eq_left hx, hcast]
    exact TotalSpace.mk_cast (F := EuclideanSpace ℝ (Fin r)) (hq b x hx) _
  -- Original principal sections supply a continuous positive frame for the specified orientation.
  choose eP heP hePeq using hP.exists_trivialization
  let p₀ (b x : B) : P :=
    if hx : x ∈ (eP b).baseSet then (eP b).toOpenPartialHomeomorph.symm (x, 1)
    else (eP x).toOpenPartialHomeomorph.symm (x, 1)
  have hp₀ (b x : B) : projection (p₀ b x) = x := by
    dsimp only [p₀]
    split_ifs with hx
    · exact (eP b).proj_symm_apply' hx
    · exact (eP x).proj_symm_apply' (heP x)
  let q₀ (b x : B) : EuclideanOrientedFrameBundle r E o := S.frameMap (p₀ b x)
  have hq₀ (b x : B) : (q₀ b x).val.1 = x :=
    (S.frameMap_projection (p₀ b x)).trans (hp₀ b x)
  let T (b x : B) : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E x :=
    hq₀ b x ▸ (q₀ b x).val.2
  have hcast_positive {x y : B} (h : x = y)
      (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E x)
      (he : Orientation.map (Fin r) e.toLinearEquiv
        (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.orientation = o x) :
      Orientation.map (Fin r) (h ▸ e).toLinearEquiv
        (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.orientation = o y := by
    cases h
    exact he
  have hTpositive (b x : B) :
      Orientation.map (Fin r) (T b x).toLinearEquiv
        (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.orientation = o x :=
    hcast_positive (hq₀ b x) (q₀ b x).val.2 (q₀ b x).property
  have hp₀cont (b : B) : ContinuousOn (p₀ b) (eP b).baseSet := by
    have h := (eP b).toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_id.continuousOn.prodMk (continuous_const (y := (1 : G))).continuousOn)
      (fun x hx ↦ (eP b).mem_target.mpr hx)
    apply h.congr
    intro x hx
    simp only [p₀, dite_eq_left hx, Function.comp_def, id_eq]
  have hcolumn (i : Fin r) : Continuous
      (fun p : OrthogonalFrameBundle r E ↦
        (⟨p.1, p.2 (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin r)) E)) := by
    let embedding (p : OrthogonalFrameBundle r E) :=
      (p.1, fun j : Fin r ↦ (⟨p.1, p.2 (EuclideanSpace.basisFun (Fin r) ℝ j)⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin r)) E))
    have hinducing : Topology.IsInducing embedding := ⟨rfl⟩
    exact (continuous_apply i).comp (continuous_snd.comp hinducing.continuous)
  have hTcont (b : B) (i : Fin r) : ContinuousOn
      (fun x ↦ (⟨x, T b x (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin r)) E)) (eP b).baseSet := by
    have hsub : Continuous (fun q : EuclideanOrientedFrameBundle r E o ↦ q.val) :=
      continuous_induced_dom
    have hraw := ((hcolumn i).comp hsub).comp S.frameMap.continuous
    have h := hraw.continuousOn.comp (hp₀cont b) (fun _ _ ↦ Set.mem_univ _)
    apply h.congr
    intro x hx
    change (⟨x, T b x (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
      TotalSpace (EuclideanSpace ℝ (Fin r)) E) = _
    dsimp only [T]
    rw [hcast]
    exact TotalSpace.mk_cast (F := EuclideanSpace ℝ (Fin r)) (hq₀ b x) _
  -- A fixed orthogonal change of model coordinates makes the smooth frame match T at the base.
  let b₀ := EuclideanSpace.basisFun (Fin r) ℝ
  let R (b : B) := (T b b).trans (L b b).symm
  let H (b x : B) : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E x := (R b).trans (L b x)
  have hHbase (b : B) : H b b = T b b := by
    ext v
    exact (L b b).apply_symm_apply (T b b v)
  have hH (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
        (fun x ↦ (⟨x, H b x (b₀ i)⟩ : TotalSpace (EuclideanSpace ℝ (Fin r)) E))
        (A.trivialization b).baseSet := by
    have hformula (x : B) : H b x (b₀ i) =
        ∑ j : Fin r, (b₀.toBasis.repr (R b (b₀ i)) j) • L b x (b₀ j) := by
      change L b x (R b (b₀ i)) = _
      conv_lhs => rw [← b₀.toBasis.sum_repr (R b (b₀ i))]
      rw [map_sum]
      simp only [map_smul, OrthonormalBasis.coe_toBasis]
    simp_rw [hformula]
    exact ContMDiffOn.sum_section
      (fun j _ ↦ (hL b j).const_smul_section
        (a := b₀.toBasis.repr (R b (b₀ i)) j))
  let U (b : B) := (A.trivialization b).baseSet ∩ (eP b).baseSet
  have hU (b : B) : IsOpen (U b) :=
    (A.trivialization b).open_baseSet.inter (eP b).open_baseSet
  have hbU (b : B) : b ∈ U b := ⟨A.mem_baseSet b, heP b⟩
  let gram (b x : B) : Matrix (Fin r) (Fin r) ℝ :=
    fun i j ↦ inner ℝ (T b x (b₀ i)) (H b x (b₀ j))
  have hgram (b : B) : ContinuousOn (gram b) (U b) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact ((hTcont b i).mono Set.inter_subset_right).inner_bundle
      ((hH b j).continuousOn.mono Set.inter_subset_left)
  have hgram_base (b : B) : gram b b = 1 := by
    ext i j
    change inner ℝ (T b b (b₀ i)) (H b b (b₀ j)) = _
    rw [hHbase, (T b b).inner_map_map]
    simpa only [Matrix.one_apply] using (orthonormal_iff_ite.mp b₀.orthonormal i j)
  have hdet (b : B) : ContinuousOn (fun x ↦ (gram b x).det) (U b) :=
    (continuous_id.matrix_det).comp_continuousOn (hgram b)
  have hpositive (b : B) :
      ∃ W : Set B, IsOpen W ∧ b ∈ W ∧ W ⊆ U b ∧ ∀ x ∈ W, 0 < (gram b x).det := by
    have hdetb : 0 < (gram b b).det := by rw [hgram_base, Matrix.det_one]; norm_num
    have hnhds : {x | 0 < (gram b x).det} ∈ nhds b :=
      (hdet b |>.continuousAt (hU b |>.mem_nhds (hbU b))).preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hdetb)
    obtain ⟨W, hWsub, hW, hbW⟩ := mem_nhds_iff.mp
      (Filter.inter_mem (hU b |>.mem_nhds (hbU b)) hnhds)
    exact ⟨W, hW, hbW, fun _ hx ↦ (hWsub hx).1, fun _ hx ↦ (hWsub hx).2⟩
  have hHpositive (b x : B) (hx : 0 < (gram b x).det) :
      Orientation.map (Fin r) (H b x).toLinearEquiv b₀.toBasis.orientation = o x := by
    let β := b₀.map (T b x)
    let γ := b₀.map (H b x)
    have hmatrix : β.toBasis.toMatrix γ.toBasis = gram b x := by
      ext i j
      change β.toBasis.repr (γ.toBasis j) i = _
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rfl
    have horient : β.toBasis.orientation = γ.toBasis.orientation := by
      apply (β.toBasis.orientation_eq_iff_det_pos γ.toBasis).mpr
      rwa [Module.Basis.det_apply, hmatrix]
    have hβ : β.toBasis.orientation =
        Orientation.map (Fin r) (T b x).toLinearEquiv b₀.toBasis.orientation :=
      b₀.toBasis.orientation_map (T b x).toLinearEquiv
    have hγ : γ.toBasis.orientation =
        Orientation.map (Fin r) (H b x).toLinearEquiv b₀.toBasis.orientation :=
      b₀.toBasis.orientation_map (H b x).toLinearEquiv
    rw [← hγ, ← horient, hβ]
    exact hTpositive b x
  choose W hW hbW hWsub hWpos using hpositive
  let F (b x : B) : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E x :=
    if x ∈ W b then H b x else T b x
  have hFpositive (b x : B) :
      Orientation.map (Fin r) (F b x).toLinearEquiv b₀.toBasis.orientation = o x := by
    dsimp only [F]
    split_ifs with hx
    · exact hHpositive b x (hWpos b x hx)
    · exact hTpositive b x
  let s (b x : B) : EuclideanOrientedFrameBundle r E o :=
    ⟨⟨x, F b x⟩, hFpositive b x⟩
  have hscol (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
        (fun x ↦ (⟨(s b x).val.1, (s b x).val.2 (b₀ i)⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin r)) E)) (W b) := by
    apply ((hH b i).mono (fun x hx ↦ (hWsub b hx).1)).congr
    intro x hx
    simp only [s, F, ite_eq_left hx]
  have hscont (b : B) : ContinuousOn (s b) (W b) := by
    have hsub : Topology.IsInducing
        (fun p : EuclideanOrientedFrameBundle r E o ↦ p.val) := ⟨rfl⟩
    apply hsub.continuousOn_iff.mpr
    let embedding (p : OrthogonalFrameBundle r E) :=
      (p.1, fun j : Fin r ↦ (⟨p.1, p.2 (b₀ j)⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin r)) E))
    have hinducing : Topology.IsInducing embedding := ⟨rfl⟩
    apply hinducing.continuousOn_iff.mpr
    exact continuous_id.continuousOn.prodMk
      (continuousOn_pi.mpr (fun i ↦ (hscol b i).continuousOn))
  have hsbase (b : B) : s b b = S.frameMap (p₀ b b) := by
    apply Subtype.ext
    change (⟨b, F b b⟩ : OrthogonalFrameBundle r E) = (q₀ b b).val
    rw [show F b b = T b b by simp only [F, ite_eq_left (hbW b), hHbase]]
    have htransport {x y : B} (h : x = y)
        (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E x) :
        (⟨y, h ▸ e⟩ : OrthogonalFrameBundle r E) = ⟨x, e⟩ := by
      cases h
      rfl
    exact htransport (hq₀ b b) (q₀ b b).val.2
  -- Lift these very positive frames, then use their lifts as unit sections of principal charts.
  have hlocal (b : B) :
      ∃ t : Trivialization G projection, b ∈ t.baseSet ∧
        (∀ (g : G) (p : P), projection p ∈ t.baseSet →
          (t (MulOpposite.op g • p)).2 = (t p).2 * g) ∧
        ∀ i : Fin r,
          ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
            (fun x ↦
              let q := S.frameMap (t.toOpenPartialHomeomorph.symm (x, 1))
              (⟨q.val.1, q.val.2 (b₀ i)⟩ : TotalSpace (EuclideanSpace ℝ (Fin r)) E))
            t.baseSet := by
    obtain ⟨V, hV, hbV, hVsub, l, hl, hlf⟩ :=
      liftFrame b (W b) (hW b) (hbW b) (s b) (hscont b) (p₀ b b) (hsbase b)
    have hlproj (x : B) (hx : x ∈ V) : projection (l x) = x := by
      rw [← S.frameMap_projection, hlf x hx]
    obtain ⟨t, htbase, hteq, htunit⟩ := chartOfSection (eP b) (hePeq b) V hV
      (fun x hx ↦ (hWsub b (hVsub hx)).2) l hl hlproj
    refine ⟨t, htbase.symm ▸ hbV, hteq, ?_⟩
    intro i
    rw [htbase]
    apply ((hscol b i).mono hVsub).congr
    intro x hx
    rw [htunit x hx, hlf x hx]
  choose t htbase hteq htcol using hlocal
  -- Express the very same transition element through the two selected smooth frames.
  let p (b x : B) : P := (t b).toOpenPartialHomeomorph.symm (x, 1)
  let q' (b x : B) : EuclideanOrientedFrameBundle r E o := S.frameMap (p b x)
  have hq' (b x : B) (hx : x ∈ (t b).baseSet) : (q' b x).val.1 = x :=
    (S.frameMap_projection (p b x)).trans ((t b).proj_symm_apply' hx)
  let K (b x : B) : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] E x :=
    if hx : x ∈ (t b).baseSet then hq' b x hx ▸ (q' b x).val.2
    else T b x
  have hKcol (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
        (fun x ↦ (⟨x, K b x (b₀ i)⟩ : TotalSpace (EuclideanSpace ℝ (Fin r)) E))
        (t b).baseSet := by
    apply (htcol b i).congr
    intro x hx
    dsimp only [K]
    rw [dite_eq_left hx, hcast]
    exact TotalSpace.mk_cast (F := EuclideanSpace ℝ (Fin r)) (hq' b x hx) _
  have hKraw (b x : B) (hx : x ∈ (t b).baseSet) (v : EuclideanSpace ℝ (Fin r)) :
      (⟨x, K b x v⟩ : TotalSpace (EuclideanSpace ℝ (Fin r)) E) =
        ⟨(q' b x).val.1, (q' b x).val.2 v⟩ := by
    dsimp only [K]
    rw [dite_eq_left hx, hcast]
    exact TotalSpace.mk_cast (F := EuclideanSpace ℝ (Fin r)) (hq' b x hx) _
  refine ⟨t, htbase, hteq, ?_, htcol⟩
  intro c d
  let V : Set B := (t c).baseSet ∩ (t d).baseSet
  let g (x : B) : G := (t d (p c x)).2
  have hproj (b x : B) (hx : x ∈ (t b).baseSet) : projection (p b x) = x :=
    (t b).proj_symm_apply' hx
  have hcont : ContinuousOn g V := by
    have hp : ContinuousOn (p c) V :=
      (t c).toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_id.continuousOn.prodMk
        (continuous_const (y := (1 : G))).continuousOn)
      (fun x hx ↦ (t c).mem_target.mpr hx.1)
    exact ((t d).toOpenPartialHomeomorph.continuousOn.comp hp
      (fun x hx ↦ (t d).mem_source.mpr (by rw [hproj c x hx.1]; exact hx.2))).snd
  apply (contMDiffOn_euclideanSpin_iff_vectorRepresentation I r V g hcont).mpr
  intro i
  have haction (x : B) (hx : x ∈ V) : MulOpposite.op (g x) • p d x = p c x := by
    have hpd : p d x ∈ (t d).source :=
      (t d).mem_source.mpr (by rw [hproj d x hx.2]; exact hx.2)
    have hpc : p c x ∈ (t d).source :=
      (t d).mem_source.mpr (by rw [hproj c x hx.1]; exact hx.2)
    have hacted : MulOpposite.op (g x) • p d x ∈ (t d).source := by
      apply (t d).mem_source.mpr
      rw [hP.projection_smul, hproj d x hx.2]
      exact hx.2
    apply (t d).toOpenPartialHomeomorph.injOn hacted hpc
    change t d (MulOpposite.op (g x) • p d x) = t d (p c x)
    apply Prod.ext
    · rw [(t d).coe_fst hacted, (t d).coe_fst hpc,
        hP.projection_smul, hproj d x hx.2, hproj c x hx.1]
    · rw [hteq d (g x) (p d x) ((t d).mem_source.mp hpd)]
      have hunit : t d (p d x) = (x, 1) := (t d).apply_symm_apply' hx.2
      rw [hunit, one_mul]
  have hframe (x : B) (hx : x ∈ V) (v : EuclideanSpace ℝ (Fin r)) :
      K c x v = K d x (euclideanSpinVectorRepresentation r (g x) v) := by
    apply TotalSpace.mk_injective x
    rw [hKraw c x hx.1, hKraw d x hx.2]
    change (⟨(S.frameMap (p c x)).val.1, (S.frameMap (p c x)).val.2 v⟩ :
      TotalSpace (EuclideanSpace ℝ (Fin r)) E) = _
    rw [← haction x hx]
    exact S.equivariant (g x) (p d x) v
  have hformula (x : B) (hx : x ∈ V) :
      euclideanSpinVectorRepresentation r (g x) (b₀ i) =
        ∑ j : Fin r, inner ℝ (K d x (b₀ j)) (K c x (b₀ i)) • b₀ j := by
    rw [hframe x hx]
    simp_rw [(K d x).inner_map_map, ← b₀.repr_apply_apply]
    exact (b₀.sum_repr _).symm
  have hsum : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin r)) ∞
      (fun x ↦ ∑ j : Fin r, inner ℝ (K d x (b₀ j)) (K c x (b₀ i)) • b₀ j) V := by
    apply contMDiffOn_finsetSum
    intro j _
    exact (((hKcol d j).mono Set.inter_subset_right).inner_bundle
      ((hKcol c i).mono Set.inter_subset_left)).smul contMDiffOn_const
  exact hsum.congr hformula

end GeneralDimension

variable {m : ℕ} {P : Type*} [TopologicalSpace P]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin (2 * m))) E I]
  [IsContMDiffRiemannianBundle I ∞ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsManifold I ∞ B]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B} {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

/-- Compatibility means smoothness of the actual lifted frame columns in the original bundle. -/
def TopologicalSpinStructure.IsCompatibleSmoothAtlas
    (S : TopologicalSpinStructure m E o hm hP)
    (A : SmoothSpinPrincipalAtlas m I projection) : Prop :=
  ∀ (b : B) (i : Fin (2 * m)),
    ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))) ∞
      (fun x : B ↦
        let p := (A.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
        let q := S.frameMap p
        (⟨q.val.1, q.val.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E))
      (A.trivialization b).baseSet

/-- Every original topological spin lift has a smooth principal atlas compatible with its frames. -/
theorem TopologicalSpinStructure.exists_compatible_smoothPrincipalAtlas
    (S : TopologicalSpinStructure m E o hm hP) :
    ∃ A : SmoothSpinPrincipalAtlas m I projection, S.IsCompatibleSmoothAtlas I A := by
  classical
  let := euclideanSpinCliffordNormedAddCommGroup (2 * m)
  let := euclideanSpinCliffordNormedSpace (2 * m)
  -- The existing even-dimensional equivalence transports only group coordinates and action data.
  obtain ⟨action, hAction⟩ := exists_spinStructure_even_equiv m E o hm hP
  let := action
  obtain ⟨continuousAction, hContinuousAction⟩ := hAction
  let := continuousAction
  obtain ⟨hQ, e, haction, hframe⟩ := hContinuousAction
  obtain ⟨u, hu, hueq, hutrans, hucol⟩ :=
    (e S).exists_compatible_smoothPrincipalCharts I
  let eG := euclideanSpinEvenEquiv m
  let eH : spinGroup (euclideanSpinQuadraticForm (2 * m)) ≃ₜ
      spinGroup (realSpinorQuadraticForm m) :=
    { eG.toEquiv with
      continuous_toFun := (continuous_euclideanSpinEvenEquiv m).1
      continuous_invFun := (continuous_euclideanSpinEvenEquiv m).2 }
  let t (b : B) := (u b).transFiberHomeomorph eH
  have htunit (b x : B) : (t b).toOpenPartialHomeomorph.symm (x, 1) =
      (u b).toOpenPartialHomeomorph.symm (x, 1) := by
    change (u b).toOpenPartialHomeomorph.symm (x, eG.symm 1) = _
    rw [map_one]
  -- Clifford coordinates change by a fixed finite-dimensional real linear equivalence.
  let M := ((euclideanSpinCliffordCoordinates (2 * m)).symm.trans
    (euclideanSpinCliffordEvenEquiv m).toLinearEquiv).trans
      (realSpinorCliffordCoordinates m)
  have hM : ContDiff ℝ ∞ M := M.toContinuousLinearEquiv.contDiff
  let A : SmoothSpinPrincipalAtlas m I projection := {
    projection_smul := hP.projection_smul
    trivialization := t
    mem_baseSet := hu
    equivariant := by
      intro b g p hp
      change eG ((u b (MulOpposite.op g • p)).2) = eG ((u b p).2) * g
      have ha := haction (eG.symm g) p
      rw [eG.apply_symm_apply] at ha
      rw [← ha, hueq b (eG.symm g) p hp, map_mul, eG.apply_symm_apply]
    contMDiffOn_transition := by
      intro b c
      have h := hM.contMDiff.comp_contMDiffOn (hutrans b c)
      apply h.congr
      intro x hx
      rw [htunit]
      change realSpinorCliffordCoordinates m
        (euclideanSpinCliffordEvenEquiv m
          ((u c ((u b).toOpenPartialHomeomorph.symm (x, 1))).2.val)) = _
      simp only [M, LinearEquiv.trans_apply, Function.comp_apply,
        LinearEquiv.symm_apply_apply, AlgEquiv.toLinearEquiv_apply] }
  refine ⟨A, ?_⟩
  intro b i
  change ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))) ∞
    (fun x ↦
      let q := S.frameMap ((t b).toOpenPartialHomeomorph.symm (x, 1))
      (⟨q.val.1, q.val.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)) (u b).baseSet
  apply (hucol b i).congr
  intro x hx
  rw [htunit]
  exact congrArg (fun q : EuclideanOrientedFrameBundle (2 * m) E o ↦
    (⟨q.val.1, q.val.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)⟩ :
      TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E))
    (hframe S ((u b).toOpenPartialHomeomorph.symm (x, 1))).symm

/-- The compatible smooth atlas selected on this very original spin principal bundle. -/
def TopologicalSpinStructure.smoothPrincipalAtlas
    (S : TopologicalSpinStructure m E o hm hP) :
    SmoothSpinPrincipalAtlas m I projection :=
  (S.exists_compatible_smoothPrincipalAtlas I).choose

/-- The chosen principal atlas retains smoothness of the same original frame lift. -/
theorem TopologicalSpinStructure.smoothPrincipalAtlas_compatible
    (S : TopologicalSpinStructure m E o hm hP) :
    S.IsCompatibleSmoothAtlas I (S.smoothPrincipalAtlas I) := by
  -- Read compatibility from the same existence witness that defines this atlas.
  exact (S.exists_compatible_smoothPrincipalAtlas I).choose_spec

end AtiyahSinger
