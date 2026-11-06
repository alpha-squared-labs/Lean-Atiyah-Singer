/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalFullSymbolEllipticity
public import AtiyahSinger.Analysis.PseudodifferentialIndexStability

/-!
# Elliptic PDOs with general full symbols

Public module ID: M0655.

SG III.4.7, III.5.2--5.3 in the coordinate inverse-bound
model. Ellipticity is a condition on a representative of the existing principal
class; it does not contain a parametrix, Fredholmness, or an index conclusion.
The inverse-symbol and composition steps feed the existing asymptotic correction.
All conclusions concern the original smooth section map and its Sobolev extension.
Metric/cosphere comparisons and local distributional regularity are not asserted.
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
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- Standard full-symbol ellipticity of the PDO's principal class, with no analytic conclusions. -/
def IsElliptic : Prop :=
  ∃ a : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
    P.principalSymbol = globalPrincipalSymbolClass E F m a ∧
      IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val

/-- Any given representative tests the same ellipticity condition. -/
theorem isElliptic_iff_of_principalSymbol_eq
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hPa : P.principalSymbol = globalPrincipalSymbolClass E F m a) :
    P.IsElliptic ↔ IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val := by
  /- Forward: compare the existential representative with a by hPa and use
  representative invariance. Reverse: use a itself as the witness. No inverse
  operator, homogeneous representative, or Fredholm certificate is supplied. -/
  constructor
  · rintro ⟨b, hPb, hb⟩
    -- The original chosen principal class identifies these two full representatives.
    have hba : globalPrincipalSymbolClass E F m b =
        globalPrincipalSymbolClass E F m a := hPb.symm.trans hPa
    exact (isEllipticFullGlobalSymbol_iff_of_class_eq b a hba).mp hb
  · intro ha
    exact ⟨a, hPa, ha⟩

/-- Equal principal classes preserve full-symbol ellipticity of the original operators. -/
theorem isElliptic_iff_of_principalSymbol_eq_operator
    (R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPR : P.principalSymbol = R.principalSymbol) : P.IsElliptic ↔ R.IsElliptic := by
  /- Rewrite the principal-class equality in each existential witness. The
  witness and its quantitative inverse bound are unchanged in both directions. -/
  constructor
  · rintro ⟨a, hPa, ha⟩
    exact ⟨a, hPR.symm.trans hPa, ha⟩
  · rintro ⟨a, hRa, ha⟩
    exact ⟨a, hPR.trans hRa, ha⟩

include hM hT2 hSC hC hE hF hμ

/-- A fixed quantization is elliptic exactly when its supplied full symbol is elliptic. -/
theorem isElliptic_quantize_iff
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (A.quantize μ a).IsElliptic ↔
      IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val := by
  /- The principal class of the fixed quantization is precisely the class of a.
  Apply the representative test above; no requirement on a at zero is introduced. -/
  exact (A.quantize μ a).isElliptic_iff_of_principalSymbol_eq a
    (A.principalSymbol_quantize μ a)

/-- Quantizing one inverse symbol gives both order-minus-one errors for this same P. -/
theorem exists_inverse_mod_order_neg_one (hP : P.IsElliptic) :
    ∃ Q₀ : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m),
      IsPseudodifferentialOperator E E μ (-1)
        (Q₀.toLinearMap.comp P.toLinearMap - LinearMap.id) ∧
      IsPseudodifferentialOperator F F μ (-1)
        (P.toLinearMap.comp Q₀.toLinearMap - LinearMap.id) := by
  /- One actual inverse full symbol supplies both residual estimates. Quantize it
  once, then compare the two product principal classes with their respective
  identity classes. Order-zero representatives are kept until the quotient
  criterion lowers each original section-map residual to order -1. -/
  obtain ⟨a, hPa, ha⟩ := hP
  obtain ⟨b, hb⟩ := exists_inverse_globalSymbol_of_isEllipticFullGlobalSymbol a ha
  obtain ⟨B⟩ := nonempty_quantizationPresentation (n := n) (r := q) (q := r) (E := F) (F := E)
  let Q := B.quantize μ b
  have hQ : Q.principalSymbol = globalPrincipalSymbolClass F E (-m) b :=
    B.principalSymbol_quantize μ b
  have lowerE (l : ℝ) (hl : l = 0)
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
  have lowerF (l : ℝ) (hl : l = 0)
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
  refine ⟨Q, ?_, ?_⟩
  · have hcomp : (Q.comp P).principalSymbol =
        globalPrincipalSymbolClass E E (-m + m) (globalSymbolSpaceComp b a) := by
      rw [Q.principalSymbol_comp P, hQ, hPa, globalPrincipalSymbolComp_class]
    exact lowerE (-m + m) (by ring) (Q.comp P) (globalSymbolSpaceComp b a)
      hcomp (hb ((-m + m) - 1)).1
  · have hcomp : (P.comp Q).principalSymbol =
        globalPrincipalSymbolClass F F (m + -m) (globalSymbolSpaceComp a b) := by
      rw [P.principalSymbol_comp Q, hPa, hQ, globalPrincipalSymbolComp_class]
    exact lowerF (m + -m) (by ring) (P.comp Q) (globalSymbolSpaceComp a b)
      hcomp (hb ((m + -m) - 1)).2

/-- SG III.4.7: every quantitatively elliptic PDO has a two-sided smooth-kernel parametrix. -/
theorem exists_parametrix_of_isElliptic (hP : P.IsElliptic) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m),
      IsParametrix μ P.toLinearMap Q.toLinearMap := by
  /- Obtain the single initial inverse Q₀ and its two order-minus-one errors.
  Apply exists_parametrix_of_order_neg_one, whose actual geometric corrections
  and asymptotic summation improve both errors to genuine smooth kernels.
  No homogeneous leading term, continuous inverse choice, or Fredholm conclusion
  is assumed. Uniqueness modulo smooth kernels uses the existing parametrix lemma. -/
  obtain ⟨Q₀, hleft, hright⟩ := P.exists_inverse_mod_order_neg_one hP
  exact exists_parametrix_of_order_neg_one μ P Q₀ hleft hright

variable (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- Quantitative ellipticity makes every critical real-order Sobolev realization Fredholm. -/
theorem isFredholm_sobolevExtension_of_isElliptic (hP : P.IsElliptic) (s : ℝ) :
    (P.sobolevExtension A B s).IsFredholm := by
  /- Construct the two-sided parametrix from hP. Both smooth-kernel errors
  extend compactly to the fixed Sobolev spaces. The existing Atkinson argument
  gives closed range and finite kernel and cokernel for the original realization. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  exact P.isFredholm_sobolevExtension_of_isParametrix Q A B hQ s

include A B in
/-- The kernel of the original smooth elliptic map is finite-dimensional. -/
theorem finiteDimensional_ker_of_isElliptic (hP : P.IsElliptic) :
    FiniteDimensional ℂ P.toLinearMap.ker := by
  /- Construct a parametrix, use Fredholmness of a Sobolev realization, and
  transfer finite dimensionality along the existing natural smooth-kernel map. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  exact P.finiteDimensional_ker_of_isParametrix A B Q hQ

include A B in
/-- The algebraic cokernel of the original smooth elliptic map is finite-dimensional. -/
theorem finiteDimensional_coker_of_isElliptic (hP : P.IsElliptic) :
    FiniteDimensional ℂ (smoothSections (n := n) (r := q) F ⧸ P.toLinearMap.range) := by
  /- Construct the two-sided parametrix. Regularity and density identify the
  smooth cokernel with the finite Sobolev cokernel; no closure replaces the range. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  exact P.finiteDimensional_coker_of_isParametrix A B Q hQ

/-- An elliptic Sobolev solution with smooth data has a unique smooth representative. -/
theorem existsUnique_smooth_lift_of_isElliptic (hP : P.IsElliptic)
    (s : ℝ) (u : A.SobolevSpace s) (v : smoothSections (n := n) (r := q) F)
    (hu : P.sobolevExtension A B s u = B.smoothToSobolev (s - m) v) :
    ∃! w : smoothSections (n := n) (r := r) E,
      A.smoothToSobolev s w = u ∧ P.toLinearMap w = v := by
  /- Take the left smooth-kernel error of the constructed two-sided parametrix.
  Apply the existing smooth lifting theorem to the same u and v. This is global
  Sobolev regularity; no local statement for arbitrary distribution sections follows here. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  exact P.existsUnique_smooth_lift_of_isSmoothingOperator Q A B hQ.1 s u v hu

/-- The elliptic estimate uses any lower Sobolev norm of the original input. -/
theorem exists_estimate_of_isElliptic (hP : P.IsElliptic)
    (s l : ℝ) (hls : l ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.SobolevSpace s,
      ‖u‖ ≤ C * (‖P.sobolevExtension A B s u‖ + ‖A.sobolevInclusion s l hls u‖) := by
  /- The constructed left parametrix identity writes u=Q(Pu)-K(u).
  Use the order-minus-m bound for Q and the arbitrary-order smooth-kernel bound
  for K. Their operator norms give one nonnegative constant independent of u. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  exact P.exists_estimate_of_isSmoothingOperator Q A B hQ.1 s l hls

/-- SG III.5.3 for general full-symbol ellipticity, with finiteness established above. -/
theorem index_sobolevExtension_eq_of_isElliptic (hP : P.IsElliptic) (s : ℝ) :
    (P.sobolevExtension A B s).index = P.toLinearMap.index := by
  /- Use the constructed parametrix in index_sobolevExtension_eq_of_isParametrix.
  The natural kernel and cokernel comparisons justify the integer index of the
  original smooth map, rather than using a totalized infinite-dimensional index. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  exact P.index_sobolevExtension_eq_of_isParametrix A B Q hQ s

include A B in
/-- Equal principal classes give equal smooth indices for generally elliptic PDOs. -/
theorem index_eq_of_isElliptic_of_principalSymbol_eq (hP : P.IsElliptic)
    (R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPR : P.principalSymbol = R.principalSymbol) :
    P.toLinearMap.index = R.toLinearMap.index := by
  /- Transfer ellipticity from P to R through their common principal class.
  Construct parametrices for both and compare each smooth index with its s=0
  Sobolev index. Their bounded difference is compact because it loses one order;
  compact perturbation invariance identifies these two Fredholm indices. -/
  -- The common class transfers the same quantitative ellipticity condition to R.
  have hR : R.IsElliptic := (P.isElliptic_iff_of_principalSymbol_eq_operator R hPR).mp hP
  have hfred := P.isFredholm_sobolevExtension_of_isElliptic A B hP 0
  -- Compare both smooth indices through these fixed Sobolev realizations.
  calc
    P.toLinearMap.index = (P.sobolevExtension A B 0).index :=
      (P.index_sobolevExtension_eq_of_isElliptic A B hP 0).symm
    _ = (R.sobolevExtension A B 0).index :=
      P.index_sobolevExtension_eq_of_principalSymbol_eq A B R hPR 0 hfred
    _ = R.toLinearMap.index := R.index_sobolevExtension_eq_of_isElliptic A B hR 0

end PseudodifferentialOperator

attribute [local instance] globalSymbolTopology

include hM hT2 hSC hC hE hF hμ in
/-- A continuous path of generally elliptic full symbols has constant quantized smooth index. -/
theorem QuantizationPresentation.index_quantize_eq_of_continuous_of_isElliptic
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (m : ℝ)
    (p : unitInterval → globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : Continuous p)
    (he : ∀ t, IsEllipticFullGlobalSymbol (r := r) (q := q) E F m (p t).val) :
    (C.quantize μ (p 0)).toLinearMap.index = (C.quantize μ (p 1)).toLinearMap.index := by
  /- Each quantization is elliptic by its actual full representative, so the
  constructed parametrices give the pointwise existence required by the existing
  continuous-symbol index theorem. Apply it with hp in the weighted symbol topology.
  The inverse radii and constants may depend on t; no uniform or continuous
  parametrix family is needed. Continuity in the full-symbol topology is essential. -/
  apply C.index_quantize_eq_of_continuous_of_isParametrix A B p hp
  intro t
  exact (C.quantize μ (p t)).exists_parametrix_of_isElliptic
    ((PseudodifferentialOperator.isElliptic_quantize_iff C (p t)).mpr (he t))

end AtiyahSinger
