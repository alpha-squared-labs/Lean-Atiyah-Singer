/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HomogeneousQuantization
public import AtiyahSinger.Analysis.Parametrix

/-!
# Parametrices from elliptic homogeneous principal data

Public module ID: M0452.

A04/SL01: the homogeneous-leading subclass of SG III.4.6 and Remark 4.7.
The input P is the original PDO, not a newly chosen quantization. Its principal
class is explicitly identified with regularized punctured homogeneous data.
Quantizing the inverse first gives two errors of order -1. The global asymptotic
correction then gives a two-sided parametrix modulo genuine smooth kernels.
General inverse-bound ellipticity of full symbols remains outside this interface.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

/-- The initial inverse operator is a fixed quantization of the actual inverse principal data. -/
def QuantizationPresentation.quantizeInverse
    (B : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (m : ℝ) (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a) :
    PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m) :=
  B.quantizeHomogeneous B μ (-m) (globalSymbolInverse a)
    (isSmoothOffZeroGlobalSymbol_inverse a hs he) hh.inverse

include hM hT2 hSC hC hE hF hμ

/-- The initial left inverse has order-minus-one error on the original input sections. -/
theorem isPseudodifferentialOperator_quantizeInverse_comp_sub_id {m : ℝ}
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a)
    (hP : P.principalSymbol =
      globalPrincipalSymbolClass E F m (A.regularizedSymbol m a hs hh)) :
    IsPseudodifferentialOperator E E μ (-1)
      ((B.quantizeInverse μ m a hs hh he).toLinearMap.comp P.toLinearMap - LinearMap.id) := by
  /- The actual product has order zero. Its principal representative differs
  from the fiber identity by order -1, so the original quotient criterion lowers
  that same operator residual. The quantizer and inverse symbol remain fixed. -/
  have lower (l : ℝ) (hl : l = 0)
      (C : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ l)
      (p : globalSymbolSpace (n := n) (r := r) (q := r) E E l)
      (hC : C.principalSymbol = globalPrincipalSymbolClass E E l p)
      (hp : IsGlobalSymbol (n := n) (r := r) (q := r) E E (l - 1)
        (p.val - globalSymbolId E)) :
      IsPseudodifferentialOperator E E μ (-1) (C.toLinearMap - LinearMap.id) := by
    subst l
    have hclass : C.principalSymbol =
        (PseudodifferentialOperator.id (n := n) (r := r) (E := E) μ).principalSymbol := by
      rw [hC, PseudodifferentialOperator.principalSymbol_id, globalPrincipalSymbolClass_eq_iff]
      exact hp
    simpa only [zero_sub, PseudodifferentialOperator.id] using
      (C.principalSymbol_eq_iff (PseudodifferentialOperator.id μ)).mp hclass
  let Q := B.quantizeInverse μ m a hs hh he
  let p := A.regularizedSymbol m a hs hh
  let b := B.regularizedSymbol (-m) (globalSymbolInverse a)
    (isSmoothOffZeroGlobalSymbol_inverse a hs he) hh.inverse
  have hQ : Q.principalSymbol = globalPrincipalSymbolClass F E (-m) b :=
    B.principalSymbol_quantize μ b
  have hcomp : (Q.comp P).principalSymbol =
      globalPrincipalSymbolClass E E (-m + m) (globalSymbolSpaceComp b p) := by
    rw [Q.principalSymbol_comp P, hQ, hP, globalPrincipalSymbolComp_class]
  exact lower (-m + m) (by ring) (Q.comp P) (globalSymbolSpaceComp b p) hcomp
    (isGlobalSymbol_inverse_regularized_comp_sub_id (A := A) (B := B) m ((-m + m) - 1) a hs hh he)

/-- The initial right inverse has order-minus-one error on the original output sections. -/
theorem isPseudodifferentialOperator_comp_quantizeInverse_sub_id {m : ℝ}
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a)
    (hP : P.principalSymbol =
      globalPrincipalSymbolClass E F m (A.regularizedSymbol m a hs hh)) :
    IsPseudodifferentialOperator F F μ (-1)
      (P.toLinearMap.comp (B.quantizeInverse μ m a hs hh he).toLinearMap - LinearMap.id) := by
  /- The actual product has order zero. Its principal representative differs
  from the fiber identity by order -1, so the original quotient criterion lowers
  that same operator residual. The quantizer and inverse symbol remain fixed. -/
  have lower (l : ℝ) (hl : l = 0)
      (C : PseudodifferentialOperator (n := n) (r := q) (q := q) F F μ l)
      (p : globalSymbolSpace (n := n) (r := q) (q := q) F F l)
      (hC : C.principalSymbol = globalPrincipalSymbolClass F F l p)
      (hp : IsGlobalSymbol (n := n) (r := q) (q := q) F F (l - 1)
        (p.val - globalSymbolId F)) :
      IsPseudodifferentialOperator F F μ (-1) (C.toLinearMap - LinearMap.id) := by
    subst l
    have hclass : C.principalSymbol =
        (PseudodifferentialOperator.id (n := n) (r := q) (E := F) μ).principalSymbol := by
      rw [hC, PseudodifferentialOperator.principalSymbol_id, globalPrincipalSymbolClass_eq_iff]
      exact hp
    simpa only [zero_sub, PseudodifferentialOperator.id] using
      (C.principalSymbol_eq_iff (PseudodifferentialOperator.id μ)).mp hclass
  let Q := B.quantizeInverse μ m a hs hh he
  let p := A.regularizedSymbol m a hs hh
  let b := B.regularizedSymbol (-m) (globalSymbolInverse a)
    (isSmoothOffZeroGlobalSymbol_inverse a hs he) hh.inverse
  have hQ : Q.principalSymbol = globalPrincipalSymbolClass F E (-m) b :=
    B.principalSymbol_quantize μ b
  have hcomp : (P.comp Q).principalSymbol =
      globalPrincipalSymbolClass F F (m + -m) (globalSymbolSpaceComp p b) := by
    rw [P.principalSymbol_comp Q, hP, hQ, globalPrincipalSymbolComp_class]
  exact lower (m + -m) (by ring) (P.comp Q) (globalSymbolSpaceComp p b) hcomp
    (isGlobalSymbol_regularized_comp_inverse_sub_id (A := A) (B := B) m ((m + -m) - 1) a hs hh he)

/-- An actual PDO with elliptic homogeneous principal data has a two-sided smoothing parametrix. -/
theorem exists_parametrix_of_homogeneous_principalSymbol {m : ℝ}
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a)
    (hP : P.principalSymbol =
      globalPrincipalSymbolClass E F m (A.regularizedSymbol m a hs hh)) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m),
      IsParametrix μ P.toLinearMap Q.toLinearMap := by
  /- Stage 1: choose the explicit B.quantizeInverse, using smooth inversion
  off zero, negative homogeneity, and the existing regularization construction.
  The two preceding theorems give its left and right errors of order -1.
  Stage 2: apply exists_parametrix_of_order_neg_one. Its geometric corrections
  and asymptotic summation produce a single Q of order -m whose two errors
  have smooth kernels. This follows SG's inverse/correction/summation route.
  The homogeneous-leading hypothesis includes elliptic differential principal
  data through the separate differential-to-homogeneous bridge. It is
  narrower than arbitrary full-symbol inverse-bound ellipticity in Remark 4.7;
  no Fredholm, regularity, or canonical-quantizer result is claimed here. -/
  let Q₀ := B.quantizeInverse μ m a hs hh he
  exact exists_parametrix_of_order_neg_one μ P Q₀
    (isPseudodifferentialOperator_quantizeInverse_comp_sub_id μ A B P a hs hh he hP)
    (isPseudodifferentialOperator_comp_quantizeInverse_sub_id μ A B P a hs hh he hP)

end AtiyahSinger
