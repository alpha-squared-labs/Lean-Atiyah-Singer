/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.MultiplicativeSequencePaired
public import AtiyahSinger.Topology.GlobalChernConjugation
public import AtiyahSinger.Topology.RealComplexification
public import AtiyahSinger.Topology.RealComplexificationConjugation
public import AtiyahSinger.Topology.ToddClass

/-!
# Pontryagin and A-hat classes of the original real bundle

Public module ID: M1993.

Integral Pontryagin classes are (-1)^k c_(2k) of the genuine original
complexification. The A-hat classes evaluate the actual universal polynomial
of its normalized characteristic series on their rationalizations. The
original real bundle may have locally varying rank; no orientation is supplied.

Sources: MS section 15, Lemma 15.1, p.173, and its consequence on p.174;
SG III.11, Example 11.13
and Proposition 11.14. SG states the latter for oriented bundles and proves
it using paired roots. The displayed unoriented version is a project
supplement: canonical conjugation makes odd complexification Chern classes
2-torsion, so they vanish rationally. A universal paired-root polynomial
identity then proves the equality without assuming a geometric paired-root
splitting of an unoriented bundle.

Integral Pontryagin Whitney multiplicativity is deliberately not asserted:
products of odd 2-torsion Chern classes can obstruct it. A-hat multiplicativity
and the Todd square identity are rational. All identities are degreewise
finite convolutions. Metrics are auxiliary and explicitly independent;
their existence on arbitrary nonparacompact bases is not assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RealBundle

open Bundle CategoryTheory
open scoped TensorProduct

universe u v w

variable {X : Type u} [TopologicalSpace X]
  (G : Type*) (V : X → Type v) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace G V)] [IsFiniteRank G V]
  (h : letI := ComplexBundle.complexificationTopology G V
    ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] V x))

/-- The integral Pontryagin class of the original real bundle, in cohomological degree 4k. -/
def pontryaginClass (k : ℕ) : singularCohomology ℤ X (2 * (2 * k)) :=
  letI := ComplexBundle.complexificationTopology G V
  letI := isFiniteRank_complexification G V
  (-1 : ℤ) ^ k • ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] V x) h (2 * k)

/-- The degree-4k A-hat class evaluates its universal polynomial on actual Pontryagin classes. -/
def aHatClassComponent (k : ℕ) : singularCohomology ℚ X (2 * (2 * k)) :=
  singularCohomologyWeightedPolynomial X (fun i : Fin k ↦ 2 * (i.val + 1))
    (fun i ↦ singularCohomologyRationalization X (2 * (2 * (i.val + 1)))
      (pontryaginClass G V h (i.val + 1)))
    (MultiplicativeSequence.polynomial aHatCharacteristicSeries k) (2 * k)

open Classical in
/-- The same A-hat class as an even-degree family, zero outside degrees divisible by four. -/
def aHatEvenComponent (k : ℕ) : singularCohomology ℚ X (2 * k) :=
  if hk : Even k then
    (eqToIso (by
      rcases hk with ⟨m, hm⟩
      congr 1
      omega) : singularCohomology ℚ X (2 * (2 * (k / 2))) ≅
        singularCohomology ℚ X (2 * k)).hom (aHatClassComponent G V h (k / 2))
  else 0

/-- The original Pontryagin and A-hat constructions do not depend on the presentation metric. -/
theorem pontryagin_aHat_metric_independent
    (h' : letI := ComplexBundle.complexificationTopology G V
      ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] V x)) (k : ℕ) :
    pontryaginClass G V h k = pontryaginClass G V h' k ∧
      aHatClassComponent G V h k = aHatClassComponent G V h' k ∧
      aHatEvenComponent G V h k = aHatEvenComponent G V h' k := by
  let := ComplexBundle.complexificationTopology G V
  let := isFiniteRank_complexification G V
  -- The same original complexification has metric-independent signed even Chern classes.
  have hp (j : ℕ) : pontryaginClass G V h j = pontryaginClass G V h' j := by
    dsimp only [pontryaginClass]
    rw [ComplexBundle.globalChernClass_metric_independent (fun x ↦ ℂ ⊗[ℝ] V x) h h']
  -- Rationalization and evaluation use the identical finite polynomial and coefficients.
  have ha (j : ℕ) : aHatClassComponent G V h j = aHatClassComponent G V h' j := by
    dsimp only [aHatClassComponent]
    simp_rw [hp]
  refine ⟨hp k, ha k, ?_⟩
  -- The parity test and its canonical degree transport do not involve the metric.
  dsimp only [aHatEvenComponent]
  split_ifs with hk
  · rw [ha]
  · rfl

/-- MS section 15, p.174: odd Chern classes of the actual complexification are 2-torsion.
This is the consequence following the self-conjugacy lemma 15.1, not its literal statement. -/
theorem two_smul_globalChernClass_complexification_odd (k : ℕ) :
    letI := ComplexBundle.complexificationTopology G V
    letI := isFiniteRank_complexification G V
    (2 : ℤ) • ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] V x) h (2 * k + 1) = 0 := by
  /- Stage 1: conjugate the scalar in the actual tensor z tensor v. This
  involution is continuous for the original real/imaginary topology.
  Stage 2: average the supplied metric with its conjugate pullback. The same
  involution then conjugates the actual orthogonal projectors. Its restriction
  to the tautological lines reverses their normalized first Chern classes.
  Uniqueness of the original projective power expansion signs every Chern
  coefficient. Metric independence and the original rank-stratum detection
  return this identity for the specified global classes and supplied metric.
  In odd degree the sign is minus one, giving the stated integral 2-torsion.
  No orientation of V or restriction on its locally varying rank is used. -/
  let := ComplexBundle.complexificationTopology G V
  let := isFiniteRank_complexification G V
  -- The tensor conjugation is continuous for the original real/imaginary topology.
  have hconj := ComplexBundle.globalChernClass_eq_neg_one_pow_smul_of_conjugateLinear_involution
    (fun x ↦ ℂ ⊗[ℝ] V x) h (fun x ↦ complexificationConjugation (V x))
    (fun x ↦ complexificationConjugation_involutive (V x))
    (complexificationConjugationTotalHomeomorph G V).continuous (2 * k + 1)
  have hsign : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hsign, neg_one_zsmul] at hconj
  simpa only [two_zsmul] using eq_neg_iff_add_eq_zero.mp hconj

/-- The degree-zero Pontryagin and A-hat classes have the standard unit normalization. -/
theorem pontryagin_aHat_zero :
    pontryaginClass G V h 0 = singularCohomologyOne ℤ X ∧
      aHatClassComponent G V h 0 = singularCohomologyOne ℚ X := by
  /- The original zeroth Chern class is the unit and (-1)^0=1. The
  weight-zero A-hat polynomial is the constant one; its empty list of
  original cup factors evaluates to the rational unit. Rank-zero fibers
  and empty bases are included without selecting any roots. -/
  let := ComplexBundle.complexificationTopology G V
  let := isFiniteRank_complexification G V
  constructor
  · simpa only [pontryaginClass, mul_zero, pow_zero, one_smul] using
      ComplexBundle.globalChernClass_zero (fun x ↦ ℂ ⊗[ℝ] V x) h
  · rw [aHatClassComponent, MultiplicativeSequence.polynomial_zero]
    exact singularCohomologyWeightedPolynomial_one_zero X _ _

variable (H : Type*) (W : X → Type w)
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [TopologicalSpace (TotalSpace H W)] [IsFiniteRank H W]
  (hW : letI := ComplexBundle.complexificationTopology H W
    ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] W x))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Rational A-hat classes multiply for the actual direct sum of original real bundles. -/
theorem aHatClassComponent_sum
    (hSum : letI := ComplexBundle.complexificationTopology (G × H) (V ×ᵇ W)
      ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] (V x × W x))) (k : ℕ) :
    letI := isFiniteRank_prod G V H W
    aHatClassComponent (G × H) (V ×ᵇ W) hSum k =
      ∑ i : Fin (k + 1),
        (eqToIso (by
          congr 1
          omega) : singularCohomology ℚ X (2 * (2 * i.val + 2 * (k - i.val))) ≅
            singularCohomology ℚ X (2 * (2 * k))).hom
          (singularCohomologyEvenCup ℚ X (2 * i.val) (2 * (k - i.val))
            (aHatClassComponent G V h i.val)
            (aHatClassComponent H W hW (k - i.val))) := by
  /- Stage 1: the actual complexificationSumIso identifies the tensor
  complexification of the original real sum with the sum of the two actual
  complexifications. Apply the original integral Whitney formula there.
  Rationalization kills every odd Chern class by the preceding 2-torsion
  theorem. The remaining even terms and signs give rational Pontryagin
  multiplicativity; integral Pontryagin multiplicativity is not required.
  Stage 2: apply the multiplicative-sequence universal polynomial identity
  for a(x), evaluating it by the original even cup products with doubled
  weights. Its degree k is the displayed finite convolution in degree 4k.
  Metric independence permits the supplied hSum without requiring the
  canonical complexification sum isomorphism to be unitary. -/
  classical
  let := isFiniteRank_prod G V H W
  let := ComplexBundle.complexificationTopology G V
  let := ComplexBundle.complexificationTopology H W
  let := ComplexBundle.complexificationTopology (G × H) (V ×ᵇ W)
  let := isFiniteRank_complexification G V
  let := isFiniteRank_complexification H W
  let := isFiniteRank_complexification (G × H) (V ×ᵇ W)
  let b : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X j (singularCohomologyRationalization X (2 * j)
      (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] V x) h j))
  let c : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X j (singularCohomologyRationalization X (2 * j)
      (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] W x) hW j))
  let d : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X j (singularCohomologyRationalization X (2 * j)
      (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] (V x × W x)) hSum j))
  let p : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X (2 * j)
      (singularCohomologyRationalization X (2 * (2 * j)) (pontryaginClass G V h j))
  let q : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X (2 * j)
      (singularCohomologyRationalization X (2 * (2 * j)) (pontryaginClass H W hW j))
  let r : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X (2 * j) (singularCohomologyRationalization X (2 * (2 * j))
      (pontryaginClass (G × H) (V ×ᵇ W) hSum j))
  -- First apply Whitney to the given tensor distributivity isomorphism, with the supplied metric.
  have ht {i j : ℕ} (hij : i = j) (a : singularCohomology ℤ X (2 * i)) :
      singularEvenCohomologyOf ℚ X j (singularCohomologyRationalization X (2 * j)
        ((eqToIso (congrArg (fun n ↦ singularCohomology ℤ X (2 * n)) hij)).hom a)) =
      singularEvenCohomologyOf ℚ X i (singularCohomologyRationalization X (2 * i) a) := by
    subst j
    rfl
  have hd : d = b * c := by
    apply PowerSeries.ext
    intro j
    simp only [d, b, c, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
    rw [ComplexBundle.globalChernClass_sum (fun x ↦ ℂ ⊗[ℝ] V x) h
      (fun x ↦ ℂ ⊗[ℝ] W x) hW (fun x ↦ ℂ ⊗[ℝ] (V x × W x)) hSum
      (complexificationSumIso G V H W) j, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ht (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)),
      singularCohomologyRationalization_evenCup, singularEvenCohomologyOf_cup]
  -- Rationalization kills the original odd two-torsion classes before any multiplication.
  have hrat {j : ℕ} (a : singularCohomology ℤ X (2 * j)) (ha : (2 : ℤ) • a = 0) :
      singularCohomologyRationalization X (2 * j) a = 0 := by
    have hz := congrArg (singularCohomologyRationalization X (2 * j)) ha
    rw [map_zsmul, map_zero] at hz
    have hz' : (2 : ℚ) • singularCohomologyRationalization X (2 * j) a = 0 := by
      simpa only [Int.cast_ofNat, ← Int.cast_smul_eq_zsmul ℚ] using hz
    exact (smul_eq_zero.mp hz').resolve_left (by norm_num)
  have hencode (a : (j : ℕ) → singularCohomology ℤ X (2 * j))
      (ha : ∀ j : ℕ, (2 : ℤ) • a (2 * j + 1) = 0) :
      (PowerSeries.mk fun j ↦ singularEvenCohomologyOf ℚ X j
        (singularCohomologyRationalization X (2 * j) (a j))) =
      PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1)
        (PowerSeries.mk fun j ↦ singularEvenCohomologyOf ℚ X (2 * j)
          (singularCohomologyRationalization X (2 * (2 * j)) ((-1 : ℤ) ^ j • a (2 * j))))) := by
    apply PowerSeries.ext
    intro j
    by_cases hj : 2 ∣ j
    · obtain ⟨i, rfl⟩ := hj
      rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_rescale]
      simp only [PowerSeries.coeff_mk, map_zsmul, zsmul_eq_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one]
      have hsign (z : SingularEvenCohomology ℚ X) : z = (-1) ^ i * ((-1) ^ i * z) := by
        rw [← mul_assoc, ← mul_pow]
        simp
      exact hsign _
    · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hj, PowerSeries.coeff_mk]
      obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + 1 := ⟨j / 2, by omega⟩
      rw [hrat _ (ha i), map_zero]
  have hb : b = PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) p) := by
    exact hencode (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] V x) h)
      (two_smul_globalChernClass_complexification_odd G V h)
  have hc : c = PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) q) := by
    exact hencode (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] W x) hW)
      (two_smul_globalChernClass_complexification_odd H W hW)
  have hr : d = PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) r) := by
    exact hencode (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] (V x × W x)) hSum)
      (two_smul_globalChernClass_complexification_odd (G × H) (V ×ᵇ W) hSum)
  have hpq : r = p * q := by
    -- Expansion by two is coefficientwise injective; rescaling twice by minus one is identity.
    have he : PowerSeries.rescale (-1) r = PowerSeries.rescale (-1) (p * q) := by
      rw [hb, hc, hr, ← map_mul, ← map_mul] at hd
      apply PowerSeries.ext
      intro j
      have hj := congrArg (PowerSeries.coeff (2 * j)) hd
      simpa only [PowerSeries.coeff_expand_mul] using hj
    have he' := congrArg (PowerSeries.rescale (-1)) he
    simpa only [PowerSeries.rescale_rescale, neg_mul_neg, one_mul,
      PowerSeries.rescale_one, RingHom.id_apply] using he'
  -- The signed even Chern inputs retain their original degree-zero units.
  have hp : p.constantCoeff = 1 := by
    change singularEvenCohomologyOf ℚ X 0
      (singularCohomologyRationalization X 0 (pontryaginClass G V h 0)) = 1
    rw [(pontryagin_aHat_zero G V h).1, singularCohomologyRationalization_one]
    exact singularEvenCohomologyOf_one ℚ X
  have hq : q.constantCoeff = 1 := by
    change singularEvenCohomologyOf ℚ X 0
      (singularCohomologyRationalization X 0 (pontryaginClass H W hW 0)) = 1
    rw [(pontryagin_aHat_zero H W hW).1, singularCohomologyRationalization_one]
    exact singularEvenCohomologyOf_one ℚ X
  -- Doubling the weights assigns the j-th universal polynomial cohomological degree 4j.
  have hweight (j : ℕ) :
      (MultiplicativeSequence.polynomial aHatCharacteristicSeries j).IsWeightedHomogeneous
        (fun i : Fin j ↦ 2 * (i.val + 1)) (2 * j) := by
    intro m hm
    have hw := MultiplicativeSequence.polynomial_isWeightedHomogeneous
      aHatCharacteristicSeries j hm
    calc
      Finsupp.weight (fun i : Fin j ↦ 2 * (i.val + 1)) m =
          2 * Finsupp.weight (fun i : Fin j ↦ i.val + 1) m := by
        simp [Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum, mul_left_comm]
      _ = 2 * j := congrArg (2 * ·) hw
  have hV (j : ℕ) : singularEvenCohomologyOf ℚ X (2 * j) (aHatClassComponent G V h j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform aHatCharacteristicSeries p) := by
    simp only [aHatClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, p]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ (2 * j) (hweight j)
  have hW' (j : ℕ) : singularEvenCohomologyOf ℚ X (2 * j) (aHatClassComponent H W hW j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform aHatCharacteristicSeries q) := by
    simp only [aHatClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, q]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ (2 * j) (hweight j)
  have hSum' (j : ℕ) : singularEvenCohomologyOf ℚ X (2 * j)
        (aHatClassComponent (G × H) (V ×ᵇ W) hSum j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform aHatCharacteristicSeries r) := by
    simp only [aHatClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, r]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ (2 * j) (hweight j)
  apply singularEvenCohomologyOf_injective ℚ X (2 * k)
  rw [hSum', hpq, MultiplicativeSequence.transform_mul aHatCharacteristicSeries
    characteristicSeries_normalization.2.1 p q hp hq, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [singularEvenCohomologyOf_eqToIso ℚ X (show 2 * i.val + 2 * (k - i.val) = 2 * k by
    have hi := i.isLt
    omega), singularEvenCohomologyOf_cup, hV, hW']

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The Todd class of the genuine complexification is the square of the A-hat class.
This is the unoriented rational extension of SG Proposition 11.14, in every even degree. -/
theorem todd_complexification_eq_aHat_sq (k : ℕ) :
    letI := ComplexBundle.complexificationTopology G V
    letI := isFiniteRank_complexification G V
    ComplexBundle.toddClassComponent (fun x ↦ ℂ ⊗[ℝ] V x) h k =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
          singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
            singularCohomology ℚ X (2 * k)).hom
          (singularCohomologyEvenCup ℚ X i.val (k - i.val)
            (aHatEvenComponent G V h i.val) (aHatEvenComponent G V h (k - i.val))) := by
  /- Stage 1: in sufficiently many independent formal roots x_j, use
  td(x_j)td(-x_j)=a(x_j^2)^2. The paired elementary Chern classes have
  odd terms zero and even terms (-1)^j times the elementary polynomials
  in x_j^2. Algebraic independence and polynomial_esymm identify this
  as an identity of stable universal polynomials in the Pontryagin variables.
  The number of independent pairs is chosen large enough for the degree
  under comparison; no geometric paired-root splitting is an input.
  Stage 2: the original real bundle's actual complexification has rational
  odd Chern classes zero by the consequence following MS Lemma 15.1, p.174.
  Its even classes are (-1)^j times the defined rational Pontryagin classes. Evaluate the universal
  identity on these original cohomology classes, using the actual cups.
  Stage 3: read its degree-2k component. A-hat has only fourfold degrees,
  represented by aHatEvenComponent, so the same finite convolution covers
  both even and odd k. This is the claimed square identity in all degrees.
  SG's geometric proof assumes orientation; the universal rational argument
  here removes that assumption. No compactness, rank bound or orientation
  of V is used; existence of the displayed auxiliary metric is separate. -/
  classical
  let := ComplexBundle.complexificationTopology G V
  let := isFiniteRank_complexification G V
  let c : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X j (singularCohomologyRationalization X (2 * j)
      (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] V x) h j))
  let p : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X (2 * j)
      (singularCohomologyRationalization X (2 * (2 * j)) (pontryaginClass G V h j))
  -- The same integral self-conjugacy kills every odd coefficient after rationalization.
  have hodd (j : ℕ) : singularCohomologyRationalization X (2 * (2 * j + 1))
      (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] V x) h (2 * j + 1)) = 0 := by
    have hz := congrArg (singularCohomologyRationalization X (2 * (2 * j + 1)))
      (two_smul_globalChernClass_complexification_odd G V h j)
    rw [map_zsmul, map_zero] at hz
    have hz' : (2 : ℚ) • singularCohomologyRationalization X (2 * (2 * j + 1))
        (ComplexBundle.globalChernClass (fun x ↦ ℂ ⊗[ℝ] V x) h (2 * j + 1)) = 0 := by
      simpa only [Int.cast_ofNat, ← Int.cast_smul_eq_zsmul ℚ] using hz
    exact (smul_eq_zero.mp hz').resolve_left (by norm_num)
  have hencode : c = PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-1) p) := by
    apply PowerSeries.ext
    intro j
    by_cases hj : 2 ∣ j
    · obtain ⟨i, rfl⟩ := hj
      rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_rescale]
      simp only [c, p, pontryaginClass, PowerSeries.coeff_mk, map_zsmul, zsmul_eq_mul,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
      have hsign (z : SingularEvenCohomology ℚ X) : z = (-1) ^ i * ((-1) ^ i * z) := by
        rw [← mul_assoc, ← mul_pow]
        simp
      exact hsign _
    · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hj]
      obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + 1 := ⟨j / 2, by omega⟩
      simp only [c, PowerSeries.coeff_mk, hodd, map_zero]
  -- The original Todd evaluator is the coefficient transform on the actual Chern series.
  have ht (j : ℕ) : singularEvenCohomologyOf ℚ X j
      (ComplexBundle.toddClassComponent (fun x ↦ ℂ ⊗[ℝ] V x) h j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform toddCharacteristicSeries c) := by
    simp only [ComplexBundle.toddClassComponent, MultiplicativeSequence.transform,
      PowerSeries.coeff_mk, c]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ j
      (MultiplicativeSequence.polynomial_isWeightedHomogeneous toddCharacteristicSeries j)
  -- Doubled homogeneous weights retain the Pontryagin inputs in degrees divisible by four.
  have hweight (j : ℕ) :
      (MultiplicativeSequence.polynomial aHatCharacteristicSeries j).IsWeightedHomogeneous
        (fun i : Fin j ↦ 2 * (i.val + 1)) (2 * j) := by
    intro d hd
    have hw := MultiplicativeSequence.polynomial_isWeightedHomogeneous
      aHatCharacteristicSeries j hd
    calc
      Finsupp.weight (fun i : Fin j ↦ 2 * (i.val + 1)) d =
          2 * Finsupp.weight (fun i : Fin j ↦ i.val + 1) d := by
        simp [Finsupp.weight_apply, Finsupp.sum, Finset.mul_sum, mul_left_comm]
      _ = 2 * j := congrArg (2 * ·) hw
  have ha (j : ℕ) : singularEvenCohomologyOf ℚ X (2 * j) (aHatClassComponent G V h j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform aHatCharacteristicSeries p) := by
    simp only [aHatClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, p]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ (2 * j) (hweight j)
  -- The specified parity inclusions are precisely substitution of t² in the A-hat series.
  have haEven (j : ℕ) : singularEvenCohomologyOf ℚ X j (aHatEvenComponent G V h j) =
      PowerSeries.coeff j (PowerSeries.expand 2 (by decide)
        (MultiplicativeSequence.transform aHatCharacteristicSeries p)) := by
    unfold aHatEvenComponent
    rw [PowerSeries.coeff_expand]
    by_cases hj : Even j
    · have hdvd : 2 ∣ j := hj.two_dvd
      rw [dite_eq_left hj, ite_eq_left hdvd,
        singularEvenCohomologyOf_eqToIso ℚ X (Nat.mul_div_cancel' hdvd), ha]
    · have hdvd : ¬ 2 ∣ j := fun h ↦ hj (even_iff_two_dvd.mpr h)
      rw [dite_eq_right hj, ite_eq_right hdvd, map_zero]
  -- Descend the finite paired-root identity and read its exact Cauchy coefficient.
  apply singularEvenCohomologyOf_injective ℚ X k
  rw [ht, hencode, MultiplicativeSequence.transform_expand_rescale_neg_one_eq_sq
    toddCharacteristicSeries aHatCharacteristicSeries characteristicSeries_normalization.1
    characteristicSeries_normalization.2.1 toddCharacteristicSeries_mul_evalNeg,
    pow_two, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [singularEvenCohomologyOf_eqToIso ℚ X
    (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup,
    haEven, haEven]

end AtiyahSinger.RealBundle
