/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Haar averaging of finite-dimensional Hermitian forms

Public module ID: M0358.

The form is the actual Haar integral of the original inner product along the
given representation. Haar measure is normalized on the whole compact group
using mathlib's existing `haarMeasure` construction. Joint action continuity
is explicit. The resulting positive Hermitian form is stored as explicit Core
data; it does not replace the original norm or install a new global instance.

Invariant coordinates take values in the genuine Euclidean space with its
usual inner product, rather than the supremum-norm function space. The norm
bounds compare the averaged form with the original topology. This is the
finite-dimensional averaging ingredient of SG III.9, printed p.212. It does
not average a varying bundle metric or construct equivariant quantization.
The integral identities, positivity, invariant coordinates, and comparison
bounds below are proved for these original objects and norms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory TopologicalSpace
open scoped ComplexConjugate

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The original Hermitian pairing averaged against Haar measure of total mass one. -/
def averagedHermitianPairing (ρ : ContRepresentation ℂ G E) (x y : E) : ℂ :=
  ∫ g : G, inner ℂ (ρ g x) (ρ g y) ∂(Measure.haarMeasure (⊤ : PositiveCompacts G))

variable [FiniteDimensional ℂ E]

set_option linter.unusedSectionVars false in
/-- The averaged pairing is a positive Hermitian form on the original vector space. -/
theorem averagedHermitianPairing_core_axioms (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    (∀ x y : E, conj (averagedHermitianPairing ρ y x) =
      averagedHermitianPairing ρ x y) ∧
    (∀ x : E, 0 ≤ (averagedHermitianPairing ρ x x).re) ∧
    (∀ x y z : E, averagedHermitianPairing ρ (x + y) z =
      averagedHermitianPairing ρ x z + averagedHermitianPairing ρ y z) ∧
    (∀ (x y : E) (c : ℂ), averagedHermitianPairing ρ (c • x) y =
      conj c * averagedHermitianPairing ρ x y) ∧
    (∀ x : E, averagedHermitianPairing ρ x x = 0 → x = 0) := by
  /- Stage 1: joint continuity gives continuous matrix coefficients and the
  continuity of each scalar integrand. The compact group has finite Haar mass,
  so these functions are integrable; the totalized integral is not being used
  without integrability. Haar normalization on the whole group has mass one.
  Stage 2: commute conjugation, addition and scalar multiplication with the
  integral. Pointwise nonnegative squared norms give the nonnegative real part.
  Stage 3: a nonnegative integrable function with zero integral vanishes
  almost everywhere. Continuity and positivity of Haar measure on nonempty
  open sets promote this to pointwise vanishing. Evaluation at the identity
  then gives x=0. This grouped certificate supplies the fields of one standard
  positive Hermitian form. -/
  -- Every actual matrix coefficient is integrable for this compact Haar measure.
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  have haction (x : E) : Continuous (fun g : G ↦ ρ g x) :=
    hρ.comp (continuous_id.prodMk continuous_const)
  have hcoeff (x y : E) : Continuous (fun g : G ↦ inner ℂ (ρ g x) (ρ g y)) :=
    (haction x).inner (haction y)
  have hint (x y : E) : Integrable (fun g : G ↦ inner ℂ (ρ g x) (ρ g y)) μ :=
    (hcoeff x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    -- Conjugation commutes with the integral and reverses the original pairing.
    unfold averagedHermitianPairing
    rw [← integral_conj]
    simp only [inner_conj_symm]
  · intro x
    change 0 ≤ RCLike.re (∫ g : G, inner ℂ (ρ g x) (ρ g x) ∂μ)
    rw [← integral_re (hint x x)]
    exact integral_nonneg (fun g ↦ inner_self_nonneg)
  · intro x y z
    unfold averagedHermitianPairing
    simp only [map_add, inner_add_left]
    exact integral_add (hint x z) (hint y z)
  · intro x y c
    unfold averagedHermitianPairing
    simp only [map_smul, inner_smul_left]
    exact integral_const_mul (conj c) _
  · intro x hx
    -- A nonnegative continuous function with zero integral vanishes everywhere
    -- because Haar measure is positive on every nonempty open set.
    have hz : (∫ g : G, RCLike.re (inner ℂ (ρ g x) (ρ g x)) ∂μ) = 0 := by
      rw [integral_re (hint x x)]
      exact congrArg Complex.re hx
    have hae : (fun g : G ↦ RCLike.re (inner ℂ (ρ g x) (ρ g x))) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun g ↦ inner_self_nonneg)
        ((Complex.continuous_re.comp (hcoeff x x)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))).mp hz
    have hall := ((Complex.continuous_re.comp (hcoeff x x)).ae_eq_iff_eq μ
      continuous_const).mp hae
    have hone := congrFun hall (1 : G)
    -- The original representation acts as identity at the group identity.
    change RCLike.re (inner ℂ (ρ 1 x) (ρ 1 x)) = 0 at hone
    simpa only [map_one, one_apply_eq_self, inner_self_eq_norm_sq,
      sq_eq_zero_iff, norm_eq_zero] using hone

/-- The explicit averaged Hermitian form, without changing the original norm or scalar action. -/
@[reducible]
def averagedHermitianCore (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) : InnerProductSpace.Core ℂ E where
  inner := averagedHermitianPairing ρ
  conj_inner_symm := (averagedHermitianPairing_core_axioms ρ hρ).1
  re_inner_nonneg := (averagedHermitianPairing_core_axioms ρ hρ).2.1
  add_left := (averagedHermitianPairing_core_axioms ρ hρ).2.2.1
  smul_left := (averagedHermitianPairing_core_axioms ρ hρ).2.2.2.1
  definite := (averagedHermitianPairing_core_axioms ρ hρ).2.2.2.2


set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- The actual averaged pairing is invariant under the specified compact-group representation. -/
theorem averagedHermitianPairing_invariant (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (g : G) (x y : E) :
    averagedHermitianPairing ρ (ρ g x) (ρ g y) = averagedHermitianPairing ρ x y := by
  /- The representation law identifies the new integrand at h with the old
  one at h*g. A normalized Haar measure on a compact group is also right
  invariant: right translation preserves left invariance and total mass, so
  Haar uniqueness identifies it with the original measure. Change variables
  by this right translation. Left invariance alone would not justify this
  step for the displayed convention. Integrability follows from compactness. -/
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  -- The chosen normalization is on the whole compact group, so its mass is one.
  let : IsProbabilityMeasure μ := ⟨by
    change Measure.haarMeasure (⊤ : PositiveCompacts G) Set.univ = 1
    exact Measure.haarMeasure_self⟩
  -- Right translation preserves Haar measure by uniqueness with this same total mass.
  let : μ.IsMulRightInvariant := ⟨fun a ↦
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure (μ.map (· * a)) μ⟩
  unfold averagedHermitianPairing
  have hmul (a : G) :
      inner ℂ (ρ a (ρ g x)) (ρ a (ρ g y)) = inner ℂ (ρ (a * g) x) (ρ (a * g) y) := by
    rw [map_mul]
    rfl
  simp_rw [hmul]
  exact integral_mul_right_eq_self (μ := μ)
    (fun a : G ↦ inner ℂ (ρ a x) (ρ a y)) g

/-- A finite continuous representation of a compact group has invariant unitary coordinates. -/
theorem exists_unitary_coordinates (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    ∃ e : E ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)),
      (∀ x y : E, inner ℂ (e x) (e y) = averagedHermitianPairing ρ x y) ∧
      ∀ g : G, Isometry (fun z ↦ e (ρ g (e.symm z))) := by
  /- Stage 1: apply finite-dimensional orthonormal-basis construction to the
  explicit averaged positive Hermitian form. Its coordinate map is linear and
  bijective onto the stated Euclidean space; finite-dimensional norm equivalence
  makes it and its inverse continuous for the original topology. The same map
  identifies the Euclidean pairing with the actual integral, not merely some
  unspecified invariant form.
  Stage 2: invariance of that pairing implies norm preservation by each
  conjugated action. Linearity then gives an isometry. The empty orthonormal
  basis covers dimension zero. The exported continuous linear equivalence
  retains the original norm, topology, and scalar action on E. -/
  classical
  -- Use the averaged form only inside an auxiliary construction of linear coordinates.
  -- Its local norm never occurs in the exported linear equivalence or in the final topology.
  have hcoordinates : ∃ e₀ : E ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)),
      ∀ x y : E, inner ℂ (e₀ x) (e₀ y) = averagedHermitianPairing ρ x y := by
    let c := averagedHermitianCore ρ hρ
    let moduleE : Module ℂ E := inferInstance
    let : InnerProductSpace.Core ℂ E := c
    let : NormedAddCommGroup E := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    let : Module ℂ E := moduleE
    let : InnerProductSpace ℂ E :=
      InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ E)
    let b := stdOrthonormalBasis ℂ E
    exact ⟨b.repr.toLinearEquiv, fun x y ↦ b.repr.inner_map_map x y⟩
  obtain ⟨e₀, he₀⟩ := hcoordinates
  -- Finite dimensionality makes these same linear coordinates continuous for the original norm.
  let e : E ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
    e₀.toContinuousLinearEquiv
  have he (x y : E) : inner ℂ (e x) (e y) = averagedHermitianPairing ρ x y := he₀ x y
  refine ⟨e, he, ?_⟩
  intro g
  let L := e.toLinearEquiv.toLinearMap.comp
    ((ρ g).toLinearMap.comp e.symm.toLinearEquiv.toLinearMap)
  have hinner (u v : EuclideanSpace ℂ (Fin (Module.finrank ℂ E))) :
      inner ℂ (L u) (L v) = inner ℂ u v := by
    change inner ℂ (e (ρ g (e.symm u))) (e (ρ g (e.symm v))) = _
    rw [he, averagedHermitianPairing_invariant ρ hρ, ← he]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  -- Preservation of the actual averaged pairing gives the required Euclidean isometry.
  exact (L.isometryOfInner hinner).isometry

/-- The averaged form induces a norm equivalent to the original finite-dimensional norm. -/
theorem averagedHermitianPairing_norm_bounds (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : E,
      c * ‖x‖ ^ 2 ≤ (averagedHermitianPairing ρ x x).re ∧
      (averagedHermitianPairing ρ x x).re ≤ C * ‖x‖ ^ 2 := by
  /- The actual invariant coordinates identify the averaged quadratic form
  with their Euclidean squared norm. The continuous linear coordinate map and
  its inverse are bounded for the original norm on E. Increase each operator
  norm by one and square the resulting two inequalities to obtain strictly
  positive comparison constants. This also covers the zero-dimensional space,
  where both operator norms vanish and both constants are one. -/
  -- The actual averaged coordinates are continuous for the original norm on E.
  obtain ⟨e, he, _⟩ := exists_unitary_coordinates ρ hρ
  let B : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  let C : ℝ := ‖e.toContinuousLinearMap‖ + 1
  have hB : 0 < B := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  have hC : 0 < C := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  refine ⟨1 / B ^ 2, C ^ 2, div_pos zero_lt_one (sq_pos_of_pos hB),
    sq_pos_of_pos hC, ?_⟩
  intro x
  have hq : (averagedHermitianPairing ρ x x).re = ‖e x‖ ^ 2 := by
    rw [← he]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (e x)
  rw [hq]
  -- Bound the same coordinates and their inverse by their original operator norms.
  have hupper : ‖e x‖ ≤ C * ‖x‖ := by
    apply (e.toContinuousLinearMap.le_opNorm x).trans
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg x)
  have hlower : ‖x‖ ≤ B * ‖e x‖ := by
    have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) (norm_nonneg (e x)))
  constructor
  · rw [one_div, mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    have hsq := pow_le_pow_left₀ (norm_nonneg x) hlower 2
    nlinarith [hsq]
  · have hsq := pow_le_pow_left₀ (norm_nonneg (e x)) hupper 2
    nlinarith [hsq]


end AtiyahSinger
