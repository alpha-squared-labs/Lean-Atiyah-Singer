/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CharacteristicSeries
public import AtiyahSinger.Topology.EvenCohomologyWeightedComponents
public import AtiyahSinger.Topology.EvenCohomologyWeightedEvaluation
public import AtiyahSinger.Topology.HermitianMetricPullback
public import AtiyahSinger.Topology.HermitianMetricSum
public import AtiyahSinger.Topology.VariableRankChernOperations

/-!
# Actual degreewise Todd classes

Public module ID: M2255.

C02, SG III.11, Example 11.11 and the preceding multiplicative-sequence
construction. The actual universal Todd polynomial is evaluated on the
rationalizations of the original normalized integral Chern classes.
The supplied Hermitian metric only presents those classes; independence
follows from metric independence of the Chern classes.
Rank may vary without bound between components.

The flag formula uses the original rank-piece flag projection and the
already normalized actual range-line roots. Its finite root-product
coefficient is evaluated using the original cup product. Multiplicativity
is a finite degreewise convolution, with no infinite sum in H*(X).
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u v w

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

/-- The degree-2k Todd class evaluates its universal polynomial in the original Chern classes. -/
def toddClassComponent (k : ℕ) : singularCohomology ℚ X (2 * k) :=
  singularCohomologyWeightedPolynomial X (fun i : Fin k ↦ i.val + 1)
    (fun i ↦ singularCohomologyRationalization X (2 * (i.val + 1))
      (globalChernClass E h (i.val + 1)))
    (MultiplicativeSequence.polynomial toddCharacteristicSeries k) k

/-- The Todd construction is independent of the auxiliary original Hermitian metric. -/
theorem toddClassComponent_metric_independent (h' : ContinuousHermitianMetric E) (k : ℕ) :
    toddClassComponent E h k = toddClassComponent E h' k := by
  /- Every variable of the same finite universal polynomial is the
  rationalization of an original integral Chern class. Their established
  metric independence makes these input classes equal. The polynomial,
  original cup product and canonical degree transports do not change. -/
  dsimp only [toddClassComponent]
  simp_rw [globalChernClass_metric_independent E h h']

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degree-zero Todd class is the original unit, including for rank zero. -/
theorem toddClassComponent_zero :
    toddClassComponent E h 0 = singularCohomologyOne ℚ X := by
  /- The weight-zero universal polynomial is the constant one in no
  variables. Its only monomial has the empty factor list, whose original
  cup evaluation is the unit. No nonempty or positive-rank assumption is used. -/
  rw [toddClassComponent, MultiplicativeSequence.polynomial_zero,
    singularCohomologyWeightedPolynomial_one_zero]

attribute [local instance] sumTopology isFiniteRank_sum

variable (F : X → Type w) [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (hF : ContinuousHermitianMetric F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Todd classes multiply under the actual direct sum, as a finite convolution in each degree. -/
theorem toddClassComponent_sum (k : ℕ) :
    toddClassComponent (E ×ᵇ F) (h.sum hF) k =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
          singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
            singularCohomology ℚ X (2 * k)).hom
          (singularCohomologyEvenCup ℚ X i.val (k - i.val)
            (toddClassComponent E h i.val) (toddClassComponent F hF (k - i.val))) := by
  /- Stage 1: the original Whitney formula identifies the Chern sequence
  of the actual sum with the Cauchy product of the two original sequences.
  Rationalization preserves these cups and the unit.
  Stage 2: apply the universal multiplicative-sequence polynomial identity
  for the normalized series td. Weighted homogeneity permits its evaluation
  in the original even cohomology degree by degree: the explicit finite
  monomial evaluator uses the same cups. Degree k gives precisely the finite
  displayed convolution. Empty or varying local ranks require no truncation. -/
  classical
  let b : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X j
      (singularCohomologyRationalization X (2 * j) (globalChernClass E h j))
  let c : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X j
      (singularCohomologyRationalization X (2 * j) (globalChernClass F hF j))
  let d : PowerSeries (SingularEvenCohomology ℚ X) := PowerSeries.mk fun j ↦
    singularEvenCohomologyOf ℚ X j
      (singularCohomologyRationalization X (2 * j)
        (globalChernClass (E ×ᵇ F) (h.sum hF) j))
  -- Rationalization respects the original transports and cups in the Whitney formula.
  have ht {p q : ℕ} (hpq : p = q) (a : singularCohomology ℤ X (2 * p)) :
      singularEvenCohomologyOf ℚ X q (singularCohomologyRationalization X (2 * q)
        ((eqToIso (congrArg (fun j ↦ singularCohomology ℤ X (2 * j)) hpq)).hom a)) =
      singularEvenCohomologyOf ℚ X p (singularCohomologyRationalization X (2 * p) a) := by
    subst q
    rfl
  have hd : d = b * c := by
    apply PowerSeries.ext
    intro j
    simp only [d, b, c, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
    rw [globalChernClass_sum E h F hF (E ×ᵇ F) (h.sum hF) (Iso.refl _) j,
      map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ht (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)),
      singularCohomologyRationalization_evenCup, singularEvenCohomologyOf_cup]
  -- Both input series have the original unit coefficient, including on empty bases.
  have hb : b.constantCoeff = 1 := by
    change singularEvenCohomologyOf ℚ X 0
      (singularCohomologyRationalization X 0 (globalChernClass E h 0)) = 1
    rw [globalChernClass_zero]
    exact (congrArg (singularEvenCohomologyOf ℚ X 0)
      (singularCohomologyRationalization_one X)).trans (singularEvenCohomologyOf_one ℚ X)
  have hc : c.constantCoeff = 1 := by
    change singularEvenCohomologyOf ℚ X 0
      (singularCohomologyRationalization X 0 (globalChernClass F hF 0)) = 1
    rw [globalChernClass_zero]
    exact (congrArg (singularEvenCohomologyOf ℚ X 0)
      (singularCohomologyRationalization_one X)).trans (singularEvenCohomologyOf_one ℚ X)
  -- Weighted homogeneity identifies every transformed coefficient with its original Todd class.
  have hEvalE (j : ℕ) : singularEvenCohomologyOf ℚ X j (toddClassComponent E h j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform toddCharacteristicSeries b) := by
    simp only [toddClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, b]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ j
      (MultiplicativeSequence.polynomial_isWeightedHomogeneous toddCharacteristicSeries j)
  have hEvalF (j : ℕ) : singularEvenCohomologyOf ℚ X j (toddClassComponent F hF j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform toddCharacteristicSeries c) := by
    simp only [toddClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, c]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ j
      (MultiplicativeSequence.polynomial_isWeightedHomogeneous toddCharacteristicSeries j)
  have hSum (j : ℕ) :
      singularEvenCohomologyOf ℚ X j (toddClassComponent (E ×ᵇ F) (h.sum hF) j) =
      PowerSeries.coeff j (MultiplicativeSequence.transform toddCharacteristicSeries d) := by
    simp only [toddClassComponent, MultiplicativeSequence.transform, PowerSeries.coeff_mk, d]
    exact singularEvenCohomologyOf_weightedPolynomial X _ _ _ j
      (MultiplicativeSequence.polynomial_isWeightedHomogeneous toddCharacteristicSeries j)
  -- The universal multiplication identity now applies to the actual Chern coefficient series.
  apply singularEvenCohomologyOf_injective ℚ X k
  rw [hSum, hd, MultiplicativeSequence.transform_mul toddCharacteristicSeries
    characteristicSeries_normalization.1 b c hb hc, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [singularEvenCohomologyOf_eqToIso ℚ X
    (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)), singularEvenCohomologyOf_cup, hEvalE, hEvalF]

attribute [local instance] isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullback preserves the actual Todd component on the original pulled-back bundle. -/
theorem toddClassComponent_pullback {Y : Type u} [TopologicalSpace Y]
    (f : C(Y, X)) (k : ℕ) :
    singularCohomologyPullback ℚ f (2 * k) (toddClassComponent E h k) =
      toddClassComponent ((f : Y → X) *ᵖ E) (h.pullback f) k := by
  /- Naturality of the original integral Chern classes and rationalization
  identifies all polynomial inputs. Naturality of the explicit finite
  weighted evaluator then gives this equality. The target is the same
  original pullback family, total topology and pulled-back metric. -/
  unfold toddClassComponent
  rw [singularCohomologyWeightedPolynomial_pullback]
  congr 1
  funext i
  rw [← singularCohomologyRationalization_naturality]
  congr 1
  exact (globalChernClass_pullback E h f ((f : Y → X) *ᵖ E) (h.pullback f)
    (Iso.refl _) (i.val + 1)).symm

section OriginalFlags

variable (V : X → Type u) [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [TopologicalSpace (TotalSpace Unit V)] [IsFiniteRank V]
  (hV : ContinuousHermitianMetric V)

attribute [local instance] rankFlagTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On each original rank flag, the Todd class is the product of the actual Todd root series. -/
theorem toddClassComponent_rankFlag_pullback (r k : ℕ) :
    singularCohomologyPullback ℚ
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum V r, X)).comp
          (rankFlagProjection V hV r)) (2 * k) (toddClassComponent V hV k) =
      singularCohomologyWeightedPolynomial (RankFlagBundle V hV r)
        (fun _ : Fin r ↦ 1)
        (fun i ↦ singularCohomologyRationalization (RankFlagBundle V hV r) 2
          (rankFlagChernRoot V hV r i))
        (PowerSeries.coeff k (MultiplicativeSequence.rootProduct toddCharacteristicSeries r))
        k := by
  /- Stage 1: the global Chern comparison restricts to the exact original
  rank stratum. Pull back further by that same rank flag projection. Each
  integral Chern class becomes the corresponding elementary symmetric class
  in the already normalized original range-line roots.
  Stage 2: use polynomial_esymm for the actual normalized Todd series.
  Evaluate its free-root identity using these same rationalized roots and
  the original even cup product. The component comparison identifies the
  degree-k expression with the displayed finite polynomial evaluation.
  Thus this is literally the degree-2k coefficient of product td(x_i),
  with no unspecified root list or independent splitting witness. -/
  classical
  let Q := RankFlagBundle V hV r
  let ι : C(rankStratum V r, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let p : C(Q, rankStratum V r) := rankFlagProjection V hV r
  let roots : Fin r → singularCohomology ℚ Q 2 := fun i ↦
    singularCohomologyRationalization Q 2 (rankFlagChernRoot V hV r i)
  -- Restriction and flag pullback use the same original rank stratum and normalized roots.
  have hchern (j : ℕ) :
      singularCohomologyPullback ℚ (ι.comp p) (2 * j)
          (singularCohomologyRationalization X (2 * j) (globalChernClass V hV j)) =
        singularCohomologyElementarySymmetric ℚ Q (List.ofFn roots) j := by
    rw [← singularCohomologyRationalization_naturality]
    have hcomp (a : singularCohomology ℤ X (2 * j)) :
        singularCohomologyPullback ℤ (ι.comp p) (2 * j) a =
          singularCohomologyPullback ℤ p (2 * j)
            (singularCohomologyPullback ℤ ι (2 * j) a) := by
      exact congrArg (fun f ↦ f a)
        ((singularCohomologyFunctor ℤ (2 * j)).map_comp
          (TopCat.ofHom ι).op (TopCat.ofHom p).op)
    rw [hcomp, (globalChern_rank_restriction V hV r j).1,
      rankStratumChernClass_flag_pullback, singularCohomologyRationalization_elementarySymmetric]
    simp only [List.map_ofFn]
    rfl
  dsimp only [Q, ι, p] at hchern
  unfold toddClassComponent
  rw [singularCohomologyWeightedPolynomial_pullback]
  change singularCohomologyWeightedPolynomial Q _ _ _ k = _
  simp_rw [hchern]
  rw [singularCohomologyWeightedPolynomial_eq_component,
    singularCohomologyWeightedPolynomial_eq_component]
  apply congrArg (singularEvenCohomologyComponent ℚ Q k)
  let y : Fin r → SingularEvenCohomology ℚ Q :=
    fun i ↦ singularEvenCohomologyOf ℚ Q 1 (roots i)
  -- Substitution of these same root classes evaluates the universal symmetric identity.
  have heval (i : Fin k) :
      singularEvenCohomologyOf ℚ Q (i.val + 1)
          (singularCohomologyElementarySymmetric ℚ Q (List.ofFn roots) (i.val + 1)) =
        MvPolynomial.aeval y (MvPolynomial.esymm (Fin r) ℚ (i.val + 1)) := by
    rw [singularEvenCohomologyOf_elementarySymmetric,
      MvPolynomial.aeval_esymm_eq_multiset_esymm, ← Fin.univ_val_map, Multiset.map_map]
    rfl
  calc
    _ = MvPolynomial.aeval
        (fun i : Fin k ↦ MvPolynomial.aeval y (MvPolynomial.esymm (Fin r) ℚ (i.val + 1)))
        (MultiplicativeSequence.polynomial toddCharacteristicSeries k) := by
      apply congrArg (fun a : Fin k → SingularEvenCohomology ℚ Q ↦
        MvPolynomial.aeval a (MultiplicativeSequence.polynomial toddCharacteristicSeries k))
      funext i
      exact heval i
    _ = MvPolynomial.aeval y
        (MvPolynomial.aeval (fun i : Fin k ↦ MvPolynomial.esymm (Fin r) ℚ (i.val + 1))
          (MultiplicativeSequence.polynomial toddCharacteristicSeries k)) :=
      (MvPolynomial.comp_aeval_apply
        (fun i : Fin k ↦ MvPolynomial.esymm (Fin r) ℚ (i.val + 1))
        (MvPolynomial.aeval y) _).symm
    _ = _ := congrArg (MvPolynomial.aeval y) (MultiplicativeSequence.polynomial_esymm
      toddCharacteristicSeries characteristicSeries_normalization.1 r k)

end OriginalFlags

end AtiyahSinger.ComplexBundle
