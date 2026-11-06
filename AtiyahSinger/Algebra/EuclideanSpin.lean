/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinCoordinates
public import AtiyahSinger.Algebra.SpinTopology
public import AtiyahSinger.Algebra.SpinZero
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion

/-!
# The native spin group of real Euclidean n-space

Public module ID: M0016.

The quadratic form is the negative Euclidean norm squared. Its spin group is
mathlib's original subgroup in that Clifford algebra, with the Clifford
finite-dimensional topology. Its vector representation is the actual native
Clifford conjugation on the canonical vector image, transported back to the
same real Euclidean space. No topology is pulled back from the vector action.

In even dimension the actual interleaved realSpinorCoordinateIsometry induces
a Clifford algebra equivalence. Its restriction identifies these spin groups
with the existing realSpinorQuadraticForm groups and their actual vector
actions. Thus this general-dimensional entrance does not replace the earlier
spinor representation or alter its chirality convention.

Sources: SG I.2, the Clifford construction of Spin(n), and II.1, pp.78--81.
The positive-dimensional groups cover SO(n) twice, including the disconnected
Spin(1) and the connected, nonuniversal double cover at n=2. Covering lifts
are defined separately. At n=0 the unit-generated native group is trivial;
its one-sheeted endpoint is an explicit empty-product extension, not a claim
that SG II.1 defines a zero-dimensional double cover.
All statements below are proved for the original native groups and specified coordinate maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The negative Euclidean quadratic form in every real dimension. -/
def euclideanSpinQuadraticForm (n : ℕ) : QuadraticForm ℝ (EuclideanSpace ℝ (Fin n)) :=
  -LinearMap.BilinMap.toQuadraticMap (innerₗ (EuclideanSpace ℝ (Fin n)))

/-- The original Clifford algebra in its finite real exterior coordinates. -/
def euclideanSpinCliffordCoordinates (n : ℕ) :
    CliffordAlgebra (euclideanSpinQuadraticForm n) ≃ₗ[ℝ] (Finset (Fin n) → ℝ) :=
  (CliffordAlgebra.equivExterior (euclideanSpinQuadraticForm n)).trans
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ExteriorAlgebra.equivFun

/-- The real coordinate norm on the same Clifford algebra carrier. -/
@[instance_reducible]
def euclideanSpinCliffordNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (CliffordAlgebra (euclideanSpinQuadraticForm n)) :=
  NormedAddCommGroup.induced _ _ (euclideanSpinCliffordCoordinates n)
    (euclideanSpinCliffordCoordinates n).injective

attribute [local instance] euclideanSpinCliffordNormedAddCommGroup

/-- Real scalar multiplication for the same Clifford coordinate norm. -/
@[instance_reducible]
def euclideanSpinCliffordNormedSpace (n : ℕ) :
    NormedSpace ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n)) :=
  NormedSpace.induced ℝ _ _ (euclideanSpinCliffordCoordinates n)

attribute [local instance] euclideanSpinCliffordNormedSpace

/-- The original spin subgroup with its Clifford subspace topology. -/
@[instance_reducible]
def euclideanSpinGroupTopology (n : ℕ) :
    TopologicalSpace (spinGroup (euclideanSpinQuadraticForm n)) :=
  TopologicalSpace.induced
    (Subtype.val : spinGroup (euclideanSpinQuadraticForm n) →
      CliffordAlgebra (euclideanSpinQuadraticForm n)) inferInstance

attribute [local instance] euclideanSpinGroupTopology

/-- Clifford multiplication and conjugation restrict continuously to this native spin group. -/
theorem euclideanSpinGroup_isTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (spinGroup (euclideanSpinQuadraticForm n)) := by
  let : FiniteDimensional ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n)) :=
    FiniteDimensional.of_injective (euclideanSpinCliffordCoordinates n).toLinearMap
      (euclideanSpinCliffordCoordinates n).injective
  -- The original Clifford product is jointly continuous by finite-dimensional bilinearity.
  let product : CliffordAlgebra (euclideanSpinQuadraticForm n) →ₗ[ℝ]
      CliffordAlgebra (euclideanSpinQuadraticForm n) →L[ℝ]
        CliffordAlgebra (euclideanSpinQuadraticForm n) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mul ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n)))
  have hproduct : Continuous (fun p : CliffordAlgebra (euclideanSpinQuadraticForm n) ×
      CliffordAlgebra (euclideanSpinQuadraticForm n) ↦ p.1 * p.2) :=
    (product.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply Continuous.subtype_mk
    exact hproduct.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  · -- Native inversion is the same real-linear Clifford conjugation restricted to the group.
    apply Continuous.subtype_mk
    change Continuous (fun g : spinGroup (euclideanSpinQuadraticForm n) ↦
      CliffordAlgebra.reverse (CliffordAlgebra.involute (g :
        CliffordAlgebra (euclideanSpinQuadraticForm n))))
    exact CliffordAlgebra.reverse.continuous_of_finiteDimensional.comp
      (CliffordAlgebra.involute.toLinearMap.continuous_of_finiteDimensional.comp
        continuous_subtype_val)

/-- The canonical vector embedding identifies real Euclidean space with its actual image. -/
def euclideanSpinVectorEmbeddingEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ]
      LinearMap.range (CliffordAlgebra.ι (euclideanSpinQuadraticForm n)) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι (euclideanSpinQuadraticForm n)) (by
    -- The Clifford-to-exterior equivalence retains exactly the original vector generators.
    intro v w h
    apply (ExteriorAlgebra.ι_inj ℝ v w).mp
    have h' := congrArg (CliffordAlgebra.equivExterior (euclideanSpinQuadraticForm n)) h
    simpa only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
      CliffordAlgebra.changeForm_ι] using h')

/-- The native spin conjugation action on the original real Euclidean vectors. -/
def euclideanSpinVectorRepresentation (n : ℕ) :
    spinGroup (euclideanSpinQuadraticForm n) →*
      (EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
  let e := euclideanSpinVectorEmbeddingEquiv n
  let c (g : spinGroup (euclideanSpinQuadraticForm n)) :
      LinearMap.range (CliffordAlgebra.ι (euclideanSpinQuadraticForm n)) ≃ₗ[ℝ]
        LinearMap.range (CliffordAlgebra.ι (euclideanSpinQuadraticForm n)) :=
    (DistribMulAction.toLinearEquiv ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n))
      (ConjAct.toConjAct (spinGroup.toUnits g))).ofSubmodules _ _ (by
        -- Native spin conjugation preserves this exact Clifford vector image.
        have hmap :
            (DistribMulAction.toLinearEquiv ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n))
              (ConjAct.toConjAct (spinGroup.toUnits g))).toLinearMap =
            DistribSMul.toLinearMap ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n))
              (ConjAct.toConjAct (spinGroup.toUnits g)) := by
          ext a
          rfl
        rw [hmap]
        simpa only [Submodule.pointwise_smul_def] using
          (spinGroup.conjAct_smul_range_ι (x := spinGroup.toUnits g) g.property))
  exact {
    toFun := fun g ↦ e.trans ((c g).trans e.symm)
    map_one' := by
      -- The identity conjugation remains the identity after the same vector identification.
      apply LinearEquiv.ext
      intro v
      apply e.injective
      apply Subtype.ext
      change (e (e.symm (c 1 (e v))) : CliffordAlgebra (euclideanSpinQuadraticForm n)) = e v
      rw [e.apply_symm_apply]
      change ConjAct.toConjAct
          (spinGroup.toUnits (1 : spinGroup (euclideanSpinQuadraticForm n))) •
        (e v : CliffordAlgebra (euclideanSpinQuadraticForm n)) = e v
      simp only [map_one, one_smul]
    map_mul' := by
      -- Cancel the intermediate image coordinates before composing the two conjugations.
      intro g h
      apply LinearEquiv.ext
      intro v
      apply e.injective
      apply Subtype.ext
      change (e (e.symm (c (g * h) (e v))) :
          CliffordAlgebra (euclideanSpinQuadraticForm n)) =
        e (e.symm (c g (e (e.symm (c h (e v))))))
      simp only [e.apply_symm_apply]
      change ConjAct.toConjAct (spinGroup.toUnits (g * h)) •
          (e v : CliffordAlgebra (euclideanSpinQuadraticForm n)) =
        ConjAct.toConjAct (spinGroup.toUnits g) •
          (ConjAct.toConjAct (spinGroup.toUnits h) •
            (e v : CliffordAlgebra (euclideanSpinQuadraticForm n)))
      simp only [map_mul, mul_smul] }

/-- The original vector action is orientation-preserving Clifford conjugation and an isometry. -/
theorem euclideanSpinVectorRepresentation_properties (n : ℕ)
    (g : spinGroup (euclideanSpinQuadraticForm n)) (v : EuclideanSpace ℝ (Fin n)) :
    CliffordAlgebra.ι (euclideanSpinQuadraticForm n) (euclideanSpinVectorRepresentation n g v) =
        (g : CliffordAlgebra (euclideanSpinQuadraticForm n)) *
          CliffordAlgebra.ι (euclideanSpinQuadraticForm n) v *
            ((g⁻¹ : spinGroup (euclideanSpinQuadraticForm n)) :
              CliffordAlgebra (euclideanSpinQuadraticForm n)) ∧
      ‖euclideanSpinVectorRepresentation n g v‖ = ‖v‖ ∧
      LinearMap.det (euclideanSpinVectorRepresentation n g).toLinearMap = 1 := by
  -- Unwrap the original vector-image coordinates; the remaining map is native conjugation.
  have hconj :
      CliffordAlgebra.ι (euclideanSpinQuadraticForm n) (euclideanSpinVectorRepresentation n g v) =
        (g : CliffordAlgebra (euclideanSpinQuadraticForm n)) *
          CliffordAlgebra.ι (euclideanSpinQuadraticForm n) v *
            ((g⁻¹ : spinGroup (euclideanSpinQuadraticForm n)) :
              CliffordAlgebra (euclideanSpinQuadraticForm n)) := by
    change ((euclideanSpinVectorEmbeddingEquiv n)
      ((euclideanSpinVectorEmbeddingEquiv n).symm _)).val = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hgg : (g : CliffordAlgebra (euclideanSpinQuadraticForm n)) *
      ((g⁻¹ : spinGroup (euclideanSpinQuadraticForm n)) :
        CliffordAlgebra (euclideanSpinQuadraticForm n)) = 1 :=
    congrArg Subtype.val (mul_inv_cancel g)
  have hgg' : ((g⁻¹ : spinGroup (euclideanSpinQuadraticForm n)) :
      CliffordAlgebra (euclideanSpinQuadraticForm n)) *
        (g : CliffordAlgebra (euclideanSpinQuadraticForm n)) = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  -- Squaring the same conjugation identity preserves the scalar quadratic value.
  have hform : euclideanSpinQuadraticForm n (euclideanSpinVectorRepresentation n g v) =
      euclideanSpinQuadraticForm n v := by
    apply (algebraMap ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n))).injective
    rw [← CliffordAlgebra.ι_sq_scalar, hconj]
    calc
      _ = (g : CliffordAlgebra (euclideanSpinQuadraticForm n)) *
          (CliffordAlgebra.ι (euclideanSpinQuadraticForm n) v *
            CliffordAlgebra.ι (euclideanSpinQuadraticForm n) v) *
          ((g⁻¹ : spinGroup (euclideanSpinQuadraticForm n)) :
            CliffordAlgebra (euclideanSpinQuadraticForm n)) := by
        simp only [mul_assoc]
        rw [← mul_assoc ((g⁻¹ : spinGroup (euclideanSpinQuadraticForm n)) :
          CliffordAlgebra (euclideanSpinQuadraticForm n)) g, hgg', one_mul]
      _ = _ := by
        rw [CliffordAlgebra.ι_sq_scalar,
          ← Algebra.commutes (euclideanSpinQuadraticForm n v)
            (g : CliffordAlgebra (euclideanSpinQuadraticForm n)),
          mul_assoc, hgg, mul_one]
  refine ⟨hconj, ?_, ?_⟩
  · -- Equality of negative squared norms gives equality of the original nonnegative norms.
    have hnorm (w : EuclideanSpace ℝ (Fin n)) : euclideanSpinQuadraticForm n w = -‖w‖ ^ 2 := by
      change -(inner ℝ w w) = -‖w‖ ^ 2
      rw [real_inner_self_eq_norm_sq]
    rw [hnorm, hnorm] at hform
    nlinarith [norm_nonneg (euclideanSpinVectorRepresentation n g v), norm_nonneg v]
  · -- Track determinant and parity together on the actual unit-generated Lipschitz subgroup.
    let V := EuclideanSpace ℝ (Fin n)
    let Q := euclideanSpinQuadraticForm n
    let P (u : (CliffordAlgebra Q)ˣ) : Prop :=
      ∃ (L : V ≃ₗ[ℝ] V) (s : ℝ),
        (∀ v : V, CliffordAlgebra.ι Q (L v) =
          (u : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * (u⁻¹ : (CliffordAlgebra Q)ˣ)) ∧
        CliffordAlgebra.involute (u : CliffordAlgebra Q) = s • (u : CliffordAlgebra Q) ∧
        LinearMap.det L.toLinearMap = s ^ (n + 1)
    have hgenerator (u : (CliffordAlgebra Q)ˣ)
        (hu : u ∈ ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q) : Set (CliffordAlgebra Q)ˣ)) :
        P u ∧ P u⁻¹ := by
      -- A vector generator and its inverse induce the same line reflection.
      obtain ⟨a, ha⟩ := hu
      have hane : a ≠ 0 := by
        intro ha0
        rw [ha0, map_zero] at ha
        exact u.ne_zero ha.symm
      let := u.invertible
      let : Invertible (CliffordAlgebra.ι Q a) := by rwa [ha]
      let : Invertible (Q a) := CliffordAlgebra.invertibleOfInvertibleι Q a
      have hainv : ⅟(CliffordAlgebra.ι Q a) = (u⁻¹ : (CliffordAlgebra Q)ˣ) := by
        apply invOf_eq_right_inv
        rw [ha]
        exact u.mul_inv
      let K : Submodule ℝ V := ℝ ∙ a
      let L : V ≃ₗ[ℝ] V := K.reflection.toLinearEquiv
      have hform (v : V) : Q v = -‖v‖ ^ 2 := by
        change -(inner ℝ v v) = -‖v‖ ^ 2
        rw [real_inner_self_eq_norm_sq]
      have hpolar (v : V) : QuadraticMap.polar Q a v = -2 * inner ℝ a v := by
        change QuadraticMap.polar (-⇑(LinearMap.BilinMap.toQuadraticMap (innerₗ V))) a v = _
        rw [QuadraticMap.polar_neg, LinearMap.BilinMap.polar_toQuadraticMap]
        change -(inner ℝ a v + inner ℝ v a) = _
        rw [real_inner_comm a v]
        ring
      have hreflect (v : V) : L v = (⅟(Q a) * QuadraticMap.polar Q a v) • a - v := by
        change K.reflection v = _
        rw [Submodule.reflection_singleton_apply, hpolar, invOf_eq_inv, hform]
        simp only [two_smul, ← add_smul, RCLike.ofReal_real_eq_id, id_eq]
        congr 2
        ring
      -- A line reflection fixes its one-dimensional span and negates its orthogonal complement.
      have hdet : LinearMap.det L.toLinearMap = (-1 : ℝ) ^ (n + 1) := by
        change LinearMap.det K.reflection.toLinearMap = _
        rw [Submodule.det_reflection]
        have hdim := Submodule.finrank_add_finrank_orthogonal K
        rw [show Module.finrank ℝ K = 1 from finrank_span_singleton hane] at hdim
        have hdimn : 1 + Module.finrank ℝ Kᗮ = n := by simpa [V] using hdim
        rw [show n + 1 = Module.finrank ℝ Kᗮ + 2 by omega, pow_add]
        norm_num
      constructor
      · refine ⟨L, -1, ?_, ?_, hdet⟩
        · intro v
          have h := (CliffordAlgebra.ι_mul_ι_mul_invOf_ι Q a v).symm
          rw [hainv, ha, ← hreflect] at h
          exact h
        · rw [← ha, CliffordAlgebra.involute_ι]
          simp
      · refine ⟨L, -1, ?_, ?_, hdet⟩
        · intro v
          have h := (CliffordAlgebra.invOf_ι_mul_ι_mul_ι Q a v).symm
          rw [hainv, ha, ← hreflect] at h
          simpa only [inv_inv] using h
        · rw [← hainv, CliffordAlgebra.invOf_ι]
          simp
    -- Both the conjugation operator and the involution scalar multiply along subgroup words.
    have hclosure (u : (CliffordAlgebra Q)ˣ) (hu : u ∈ lipschitzGroup Q) : P u := by
      induction hu using Subgroup.closure_induction'' with
      | mem u hu => exact (hgenerator u hu).1
      | inv_mem u hu => exact (hgenerator u hu).2
      | one =>
        refine ⟨LinearEquiv.refl ℝ V, 1, ?_, ?_, ?_⟩
        · intro v
          simp
        · simp
        · simp
      | mul u w hu hw ihu ihw =>
        obtain ⟨L, s, hL, hs, hdetL⟩ := ihu
        obtain ⟨M, t, hM, ht, hdetM⟩ := ihw
        refine ⟨L * M, s * t, ?_, ?_, ?_⟩
        · intro v
          change CliffordAlgebra.ι Q (L (M v)) = _
          rw [hL, hM]
          simp only [Units.val_mul, mul_inv_rev, mul_assoc]
        · simp only [Units.val_mul, map_mul, hs, ht,
            smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm s t]
        · change LinearMap.det (L.toLinearMap ∘ₗ M.toLinearMap) = _
          rw [LinearMap.det_comp, hdetL, hdetM, mul_pow]
    -- Native spin evenness makes the tracked involution scalar one; units cannot vanish.
    obtain ⟨L, s, hL, hs, hdetL⟩ := hclosure (spinGroup.toUnits g)
      (spinGroup.units_mem_lipschitzGroup g.property)
    have hnonzero : (g : CliffordAlgebra Q) ≠ 0 := (spinGroup.toUnits g).ne_zero
    have hsone : s = 1 := by
      change CliffordAlgebra.involute (g : CliffordAlgebra Q) = s • (g : CliffordAlgebra Q) at hs
      rw [spinGroup.involute_eq g.property] at hs
      have hsub : (s - 1) • (g : CliffordAlgebra Q) = 0 := by
        rw [sub_smul, one_smul, ← hs, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hnonzero)
    -- Identify the tracked operator with the original vector representation by its actual image.
    have hsame : euclideanSpinVectorRepresentation n g = L := by
      apply LinearEquiv.ext
      intro v
      apply (euclideanSpinVectorEmbeddingEquiv n).injective
      apply Subtype.ext
      change CliffordAlgebra.ι Q (euclideanSpinVectorRepresentation n g v) =
        CliffordAlgebra.ι Q (L v)
      rw [hL]
      change ((euclideanSpinVectorEmbeddingEquiv n)
        ((euclideanSpinVectorEmbeddingEquiv n).symm _)).val = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [hsame, hdetL, hsone, one_pow]

/-- Joint continuity of this same native vector action. -/
theorem continuous_euclideanSpinVectorRepresentation (n : ℕ) :
    Continuous (fun p : spinGroup (euclideanSpinQuadraticForm n) ×
      EuclideanSpace ℝ (Fin n) ↦ euclideanSpinVectorRepresentation n p.1 p.2) := by
  let := euclideanSpinGroup_isTopologicalGroup n
  let : FiniteDimensional ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n)) :=
    FiniteDimensional.of_injective (euclideanSpinCliffordCoordinates n).toLinearMap
      (euclideanSpinCliffordCoordinates n).injective
  -- Use the original Clifford product and the native continuous group inverse.
  let product : CliffordAlgebra (euclideanSpinQuadraticForm n) →ₗ[ℝ]
      CliffordAlgebra (euclideanSpinQuadraticForm n) →L[ℝ]
        CliffordAlgebra (euclideanSpinQuadraticForm n) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mul ℝ (CliffordAlgebra (euclideanSpinQuadraticForm n)))
  have hproduct : Continuous (fun p : CliffordAlgebra (euclideanSpinQuadraticForm n) ×
      CliffordAlgebra (euclideanSpinQuadraticForm n) ↦ p.1 * p.2) :=
    (product.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd
  have hg : Continuous (fun p : spinGroup (euclideanSpinQuadraticForm n) ×
      EuclideanSpace ℝ (Fin n) ↦ (p.1 : CliffordAlgebra (euclideanSpinQuadraticForm n))) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun p : spinGroup (euclideanSpinQuadraticForm n) ×
      EuclideanSpace ℝ (Fin n) ↦ CliffordAlgebra.ι (euclideanSpinQuadraticForm n) p.2) :=
    (CliffordAlgebra.ι (euclideanSpinQuadraticForm n)).continuous_of_finiteDimensional.comp
      continuous_snd
  have hinv : Continuous (fun p : spinGroup (euclideanSpinQuadraticForm n) ×
      EuclideanSpace ℝ (Fin n) ↦ ((p.1⁻¹ : spinGroup (euclideanSpinQuadraticForm n)) :
        CliffordAlgebra (euclideanSpinQuadraticForm n))) :=
    continuous_subtype_val.comp (continuous_inv.comp continuous_fst)
  -- The specified injective linear vector map is an embedding for these exact topologies.
  have hinjective : Function.Injective (CliffordAlgebra.ι (euclideanSpinQuadraticForm n)) := by
    intro v w hvw
    apply (euclideanSpinVectorEmbeddingEquiv n).injective
    exact Subtype.ext hvw
  have hembedding := LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr hinjective)
  apply hembedding.isEmbedding.continuous_iff.mpr
  change Continuous (fun p : spinGroup (euclideanSpinQuadraticForm n) ×
    EuclideanSpace ℝ (Fin n) ↦ CliffordAlgebra.ι (euclideanSpinQuadraticForm n)
      (euclideanSpinVectorRepresentation n p.1 p.2))
  have hconj (g : spinGroup (euclideanSpinQuadraticForm n))
      (v : EuclideanSpace ℝ (Fin n)) :
      CliffordAlgebra.ι (euclideanSpinQuadraticForm n)
        (euclideanSpinVectorRepresentation n g v) =
      (g : CliffordAlgebra (euclideanSpinQuadraticForm n)) *
        CliffordAlgebra.ι (euclideanSpinQuadraticForm n) v *
          ((g⁻¹ : spinGroup (euclideanSpinQuadraticForm n)) :
            CliffordAlgebra (euclideanSpinQuadraticForm n)) := by
    change ((euclideanSpinVectorEmbeddingEquiv n)
      ((euclideanSpinVectorEmbeddingEquiv n).symm _)).val = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simp_rw [hconj]
  exact hproduct.comp ((hproduct.comp (hg.prodMk hv)).prodMk hinv)

/-- The prescribed interleaved isometry preserves the two original negative quadratic forms. -/
theorem realSpinorCoordinateIsometry_quadraticForm (m : ℕ)
    (v : EuclideanSpace ℝ (Fin (2 * m))) :
    realSpinorQuadraticForm m (realSpinorCoordinateIsometry m v) =
      euclideanSpinQuadraticForm (2 * m) v := by
  -- Both original forms evaluate to minus the squared norm in the specified real models.
  have hreal (w : EuclideanSpace ℂ (Fin m)) : realSpinorQuadraticForm m w = -‖w‖ ^ 2 := by
    let := InnerProductSpace.complexToReal (G := EuclideanSpace ℂ (Fin m))
    change -(inner ℝ w w) = -‖w‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  rw [hreal, (realSpinorCoordinateIsometry m).norm_map]
  change -‖v‖ ^ 2 = -(inner ℝ v v)
  rw [real_inner_self_eq_norm_sq]

/-- The actual Clifford algebra equivalence induced by the original interleaved isometry. -/
def euclideanSpinCliffordEvenEquiv (m : ℕ) :
    CliffordAlgebra (euclideanSpinQuadraticForm (2 * m)) ≃ₐ[ℝ]
      CliffordAlgebra (realSpinorQuadraticForm m) :=
  CliffordAlgebra.equivOfIsometry
    { (realSpinorCoordinateIsometry m).toLinearEquiv with
      map_app' := realSpinorCoordinateIsometry_quadraticForm m }

/-- The actual Clifford equivalence preserves precisely the two native spin subgroups. -/
theorem euclideanSpinCliffordEvenEquiv_mem_spinGroup (m : ℕ)
    (a : CliffordAlgebra (euclideanSpinQuadraticForm (2 * m))) :
    euclideanSpinCliffordEvenEquiv m a ∈ spinGroup (realSpinorQuadraticForm m) ↔
      a ∈ spinGroup (euclideanSpinQuadraticForm (2 * m)) := by
  -- Isometries preserve the actual generating units, Clifford star, and the even subalgebra.
  have hmap {E F : Type} [AddCommGroup E] [Module ℝ E]
      [AddCommGroup F] [Module ℝ F] (Q : QuadraticForm ℝ E) (Q' : QuadraticForm ℝ F)
      (f : Q →qᵢ Q') (x : CliffordAlgebra Q) (hx : x ∈ spinGroup Q) :
      CliffordAlgebra.map f x ∈ spinGroup Q' := by
    let A := CliffordAlgebra.map f
    have hstar (y : CliffordAlgebra Q) : A (star y) = star (A y) := by
      induction y using CliffordAlgebra.induction with
      | algebraMap r => simp [A]
      | ι v => simp [A]
      | mul x y hx hy => simp only [star_mul, map_mul, hx, hy]
      | add x y hx hy => simp only [star_add, map_add, hx, hy]
    -- Transport every generator of the native Lipschitz subgroup before imposing unitarity.
    have hlipschitz (u : (CliffordAlgebra Q)ˣ) (hu : u ∈ lipschitzGroup Q) :
        Units.map A.toMonoidHom u ∈ lipschitzGroup Q' := by
      induction hu using Subgroup.closure_induction with
      | mem u hu =>
        obtain ⟨v, hv⟩ := hu
        apply Subgroup.subset_closure
        refine ⟨f v, ?_⟩
        change CliffordAlgebra.ι Q' (f v) = A u
        rw [← hv]
        exact (CliffordAlgebra.map_apply_ι f v).symm
      | one => simp
      | mul u v hu hv ihu ihv => simpa using (lipschitzGroup Q').mul_mem ihu ihv
      | inv u hu ihu => simpa using (lipschitzGroup Q').inv_mem ihu
    obtain ⟨hpin, heven⟩ := spinGroup.mem_iff.mp hx
    obtain ⟨hlip, hunit⟩ := pinGroup.mem_iff.mp hpin
    refine spinGroup.mem_iff.mpr ⟨pinGroup.mem_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨u, hu, rfl⟩ := hlip
      exact ⟨Units.map A.toMonoidHom u, hlipschitz u hu, rfl⟩
    · change star (A x) * A x = 1 ∧ A x * star (A x) = 1
      constructor
      · rw [← hstar, ← map_mul, hunit.1, map_one]
      · rw [← hstar, ← map_mul, hunit.2, map_one]
    · change A x ∈ CliffordAlgebra.evenOdd Q' 0
      clear hx hpin hlip hunit
      change x ∈ CliffordAlgebra.evenOdd Q 0 at heven
      induction x, heven using CliffordAlgebra.even_induction with
      | algebraMap r =>
        rw [AlgHom.commutes]
        exact SetLike.algebraMap_mem_graded _ _
      | add x y hx hy ihx ihy =>
        rw [map_add]
        exact (CliffordAlgebra.evenOdd Q' 0).add_mem ihx ihy
      | ι_mul_ι_mul v w x hx ih =>
        simp only [A, map_mul, CliffordAlgebra.map_apply_ι]
        exact (CliffordAlgebra.even Q').mul_mem
          (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q' (f v) (f w)) ih
  -- Apply the same argument to the prescribed isometry and its actual inverse.
  let e : (euclideanSpinQuadraticForm (2 * m)).IsometryEquiv (realSpinorQuadraticForm m) :=
    { (realSpinorCoordinateIsometry m).toLinearEquiv with
      map_app' := realSpinorCoordinateIsometry_quadraticForm m }
  constructor
  · intro h
    have hinv := hmap _ _ e.symm.toIsometry _ h
    change (euclideanSpinCliffordEvenEquiv m).symm
      (euclideanSpinCliffordEvenEquiv m a) ∈ _ at hinv
    simpa only [AlgEquiv.symm_apply_apply] using hinv
  · exact hmap _ _ e.toIsometry a

/-- Restriction of the actual Clifford equivalence to the two original even-dimensional groups. -/
def euclideanSpinEvenEquiv (m : ℕ) :
    spinGroup (euclideanSpinQuadraticForm (2 * m)) ≃*
      spinGroup (realSpinorQuadraticForm m) where
  toFun g := ⟨euclideanSpinCliffordEvenEquiv m g,
    (euclideanSpinCliffordEvenEquiv_mem_spinGroup m g).mpr g.property⟩
  invFun g := ⟨(euclideanSpinCliffordEvenEquiv m).symm g,
    (euclideanSpinCliffordEvenEquiv_mem_spinGroup m
      ((euclideanSpinCliffordEvenEquiv m).symm g)).mp (by
        simpa only [AlgEquiv.apply_symm_apply] using g.property)⟩
  left_inv g := Subtype.ext ((euclideanSpinCliffordEvenEquiv m).symm_apply_apply g)
  right_inv g := Subtype.ext ((euclideanSpinCliffordEvenEquiv m).apply_symm_apply g)
  map_mul' g h := Subtype.ext ((euclideanSpinCliffordEvenEquiv m).map_mul g h)

attribute [local instance] spinGroupTopology

/-- The same even-dimensional group identification is continuous in both original topologies. -/
theorem continuous_euclideanSpinEvenEquiv (m : ℕ) :
    Continuous (euclideanSpinEvenEquiv m) ∧ Continuous (euclideanSpinEvenEquiv m).symm := by
  let := realSpinorCliffordNormedAddCommGroup m
  let := realSpinorCliffordNormedSpace m
  -- Both recorded Clifford coordinate topologies make the same linear equivalence continuous.
  let : FiniteDimensional ℝ (CliffordAlgebra (euclideanSpinQuadraticForm (2 * m))) :=
    FiniteDimensional.of_injective (euclideanSpinCliffordCoordinates (2 * m)).toLinearMap
      (euclideanSpinCliffordCoordinates (2 * m)).injective
  let : FiniteDimensional ℝ (CliffordAlgebra (realSpinorQuadraticForm m)) :=
    FiniteDimensional.of_injective (realSpinorCliffordCoordinates m).toLinearMap
      (realSpinorCliffordCoordinates m).injective
  constructor
  · apply Continuous.subtype_mk
    exact (euclideanSpinCliffordEvenEquiv m).toLinearMap.continuous_of_finiteDimensional.comp
      continuous_subtype_val
  · apply Continuous.subtype_mk
    exact (euclideanSpinCliffordEvenEquiv m).symm.toLinearMap.continuous_of_finiteDimensional.comp
      continuous_subtype_val

/-- The two actual vector actions agree through the same interleaved group and vector maps. -/
theorem euclideanSpinEvenEquiv_vectorRepresentation (m : ℕ)
    (g : spinGroup (euclideanSpinQuadraticForm (2 * m)))
    (v : EuclideanSpace ℝ (Fin (2 * m))) :
    realSpinorCoordinateIsometry m (euclideanSpinVectorRepresentation (2 * m) g v) =
      realSpinVectorRepresentation m (euclideanSpinEvenEquiv m g)
        (realSpinorCoordinateIsometry m v) := by
  -- Track the original generator map and conjugation before comparing vector coordinates.
  let Q := euclideanSpinQuadraticForm (2 * m)
  let Q' := realSpinorQuadraticForm m
  let A := euclideanSpinCliffordEvenEquiv m
  have hmap (v : EuclideanSpace ℝ (Fin (2 * m))) :
      A (CliffordAlgebra.ι Q v) =
        CliffordAlgebra.ι Q' (realSpinorCoordinateIsometry m v) := by
    exact CliffordAlgebra.map_apply_ι _ v
  have hconj : CliffordAlgebra.ι Q (euclideanSpinVectorRepresentation (2 * m) g v) =
      (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        ((g⁻¹ : spinGroup Q) : CliffordAlgebra Q) := by
    change ((euclideanSpinVectorEmbeddingEquiv (2 * m))
      ((euclideanSpinVectorEmbeddingEquiv (2 * m)).symm _)).val = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  -- The algebra equivalence and its subgroup restriction use exactly the same inverse.
  apply (realSpinorVectorEmbeddingEquiv m).injective
  apply Subtype.ext
  change CliffordAlgebra.ι Q' _ = CliffordAlgebra.ι Q' _
  rw [(realSpinVectorRepresentation_properties m _ _).1, ← hmap, hconj, map_mul, map_mul, hmap]
  change A g * CliffordAlgebra.ι Q' (realSpinorCoordinateIsometry m v) * A ↑g⁻¹ =
    A g * CliffordAlgebra.ι Q' (realSpinorCoordinateIsometry m v) *
      (((euclideanSpinEvenEquiv m g)⁻¹ : spinGroup Q') : CliffordAlgebra Q')
  congr 1
  exact congrArg Subtype.val ((euclideanSpinEvenEquiv m).map_inv g)

/-- The native zero-dimensional Euclidean spin group is the identity subgroup. -/
theorem euclideanSpinGroup_zero_eq_bot : spinGroup (euclideanSpinQuadraticForm 0) = ⊥ := by
  -- There are no invertible vector images in the zero-dimensional Clifford algebra.
  have hgenerators : ((↑) ⁻¹' Set.range (CliffordAlgebra.ι (euclideanSpinQuadraticForm 0)) :
      Set (CliffordAlgebra (euclideanSpinQuadraticForm 0))ˣ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨v, hv⟩ := hu
    have hvzero : v = 0 := Subsingleton.elim v 0
    rw [hvzero, map_zero] at hv
    exact u.ne_zero hv.symm
  -- The generated subgroup is trivial before imposing unitary and even conditions.
  have hlipschitz : lipschitzGroup (euclideanSpinQuadraticForm 0) = ⊥ := by
    rw [lipschitzGroup, hgenerators, Subgroup.closure_empty]
  simp [spinGroup, pinGroup, hlipschitz]

end AtiyahSinger
