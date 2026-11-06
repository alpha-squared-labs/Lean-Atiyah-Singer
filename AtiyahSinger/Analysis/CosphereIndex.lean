/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereHomotopy
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.HomogeneousSymbolFamilies

/-!
# From C-zero cosphere homotopy to the original operator index

Public module ID: M0417.

A08: radial reconstruction and relative smoothing now bridge a merely continuous
elliptic cosphere homotopy to the existing smooth-seminorm path theorem. Endpoint
principal classes, fixed quantization, and the actual smooth operator index are
kept explicit. Only operators with the displayed homogeneous principal data are
covered; this does not assign a homogeneous symbol to every general S^m operator.
Sources: SG III.7.10--7.11 and III.3.19, with the C-zero approximation step marked
as a project supplement. Regularization, ellipticity comparisons and the resulting
operator-index equalities are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable (g : SmoothCotangentMetric (n := n) (M := M))

namespace QuantizationPresentation

variable (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)

/-- Cosphere ellipticity agrees with quantitative ellipticity of its full-symbol realization. -/
theorem isEllipticFullGlobalSymbol_regularizedCosphere_iff (m : ℝ)
    (a : smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g) :
    IsEllipticFullGlobalSymbol (r := r) (q := q) E F m
      (R.regularizedSymbol m (smoothCosphereExtension (r := r) (q := q) g m a).val
        (smoothCosphereExtension (r := r) (q := q) g m a).property.1
        (smoothCosphereExtension (r := r) (q := q) g m a).property.2).val ↔
      IsEllipticCosphereSymbol g a.val := by
  /- The existing regularization theorem equates quantitative local
  inverse bounds with off-zero homogeneous invertibility. The cosphere extension
  equivalence then equates this with unit-covector invertibility. No new full-symbol
  definition or assertion of invertibility near the zero section is introduced. -/
  -- Compare the actual regularized extension with its original unit-covector data.
  exact (isEllipticFullGlobalSymbol_regularizedSymbol_iff R m
    (smoothCosphereExtension (r := r) (q := q) g m a).val
    (smoothCosphereExtension (r := r) (q := q) g m a).property.1
    (smoothCosphereExtension (r := r) (q := q) g m a).property.2).trans
      (isEllipticGlobalSymbol_cosphereExtension_iff g m a.val)

/-- Regularization eliminates the arbitrary zero-section values of homogeneous data. -/
theorem regularizedSymbol_cosphereRestriction (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    R.regularizedSymbol m
        (smoothCosphereExtension (r := r) (q := q) g m
      (smoothCosphereRestriction (r := r) (q := q) g m a)).val
        (smoothCosphereExtension (r := r) (q := q) g m
      (smoothCosphereRestriction (r := r) (q := q) g m a)).property.1
        (smoothCosphereExtension (r := r) (q := q) g m
      (smoothCosphereRestriction (r := r) (q := q) g m a)).property.2 =
      R.regularizedSymbol m a.val a.property.1 a.property.2 := by
  /- Homogeneous reconstruction identifies the functions off zero.
  Apply regularizedSymbolFunction_congr: the fixed frequency cutoff annihilates
  all zero-section values. Subtype extensionality gives equality of the actual full symbols. -/
  apply Subtype.ext
  -- Reconstruction changes only zero-section values, which this same cutoff removes.
  exact R.regularizedSymbolFunction_congr _ _
    (fun x ξ hξ ↦ cosphereExtension_restriction g m a.val a.property.2 x ξ hξ)

/-- Reconstructing the same homogeneous data using either metric gives the same regularization. -/
theorem regularizedSymbol_cosphere_metric_independent
    (k : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    R.regularizedSymbol m
        (smoothCosphereExtension (r := r) (q := q) g m
      (smoothCosphereRestriction (r := r) (q := q) g m a)).val
        (smoothCosphereExtension (r := r) (q := q) g m
      (smoothCosphereRestriction (r := r) (q := q) g m a)).property.1
        (smoothCosphereExtension (r := r) (q := q) g m
      (smoothCosphereRestriction (r := r) (q := q) g m a)).property.2 =
      R.regularizedSymbol m
        (smoothCosphereExtension k m (smoothCosphereRestriction k m a)).val
        (smoothCosphereExtension k m (smoothCosphereRestriction k m a)).property.1
        (smoothCosphereExtension k m (smoothCosphereRestriction k m a)).property.2 := by
  /- Each side equals the regularization of the original homogeneous
  data by regularizedSymbol_cosphereRestriction. The fixed cutoff presentation R
  is identical on both sides; only the auxiliary sphere used for reconstruction changes. -/
  -- Retain the specified presentation R while comparing both sphere reconstructions.
  exact (R.regularizedSymbol_cosphereRestriction g m a).trans
    (R.regularizedSymbol_cosphereRestriction k m a).symm

variable [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : MeasureTheory.Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
  (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

include hM hT2 hE hF hSC hC hμ A B D in
/-- C-zero elliptic cosphere homotopies preserve the index of homogeneous quantizations. -/
theorem index_quantizeHomogeneous_eq_of_cosphereHomotopic (m : ℝ)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hab : EllipticCosphereHomotopic (r := r) (q := q) g (cosphereRestriction g a.val)
      (cosphereRestriction g b.val)) :
    (C.quantizeHomogeneous R μ m a.val a.property.1 a.property.2).toLinearMap.index =
      (C.quantizeHomogeneous R μ m b.val b.property.1 b.property.2).toLinearMap.index := by
  /- Stage 1: relative smoothing produces a continuous homogeneous
  elliptic path whose endpoint data agree with a and b off zero. Stage 2: apply
  the existing smooth-topology homogeneous path index theorem using the fixed
  presentations and density. Stage 3: regularization removes endpoint zero-value
  discrepancies, so its quantizations are exactly those displayed in the conclusion. -/
  obtain ⟨K, hK, he, h₀, h₁⟩ :=
    exists_continuous_homogeneous_path_of_cosphereHomotopic g m a b hab
  -- The fixed cutoff annihilates the only possible discrepancies, at the zero section.
  let reg (c : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :=
    R.regularizedSymbol m c.val c.property.1 c.property.2
  have hreg₀ : reg (K 0) = reg a :=
    Subtype.ext (R.regularizedSymbolFunction_congr _ _ h₀)
  have hreg₁ : reg (K 1) = reg b :=
    Subtype.ext (R.regularizedSymbolFunction_congr _ _ h₁)
  -- Apply the smooth-seminorm path theorem, then recover the exact two quantizations.
  have hindex := R.index_quantizeHomogeneous_eq_of_continuous m μ C A B D K hK he
  change (C.quantize μ (reg (K 0))).toLinearMap.index =
    (C.quantize μ (reg (K 1))).toLinearMap.index at hindex
  change (C.quantize μ (reg a)).toLinearMap.index = (C.quantize μ (reg b)).toLinearMap.index
  rwa [hreg₀, hreg₁] at hindex

end QuantizationPresentation

namespace PseudodifferentialOperator

variable [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : MeasureTheory.Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

/-- For a displayed homogeneous principal class, ellipticity is detected on the cosphere. -/
theorem isElliptic_iff_cosphere (m : ℝ)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) :
    P.IsElliptic ↔ IsEllipticCosphereSymbol g (cosphereRestriction g a.val) := by
  /- Use invariance of quantitative ellipticity under equality of the
  actual principal quotient class. The regularized homogeneous representative is
  elliptic exactly off zero, which by homogeneity is equivalent to ellipticity on
  the metric cosphere. An arbitrary full symbol is not assumed to be homogeneous. -/
  -- First test the same regularized representative, then recover its off-zero values.
  rw [P.isElliptic_iff_of_principalSymbol_eq
    (R.regularizedSymbol m a.val a.property.1 a.property.2) hP,
    isEllipticFullGlobalSymbol_regularizedSymbol_iff R m a.val a.property.1 a.property.2]
  exact (isEllipticCosphereSymbol_restriction_iff g m a.val a.property.2).symm

include hM hT2 hE hF hSC hC hμ in
/-- SG regular-homotopy index invariance with an explicit C-zero cosphere hypothesis. -/
theorem index_eq_of_cosphereHomotopic
    (m : ℝ) (P Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hab : EllipticCosphereHomotopic (r := r) (q := q) g (cosphereRestriction g a.val)
      (cosphereRestriction g b.val))
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2))
    (hQ : Q.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m b.val b.property.1 b.property.2)) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  /- Replace the continuous cosphere homotopy by the homogeneous
  smooth-space path constructed above. Regularization of its endpoints agrees
  with that of a and b because they agree off zero. Apply the existing original-PDO
  homogeneous path theorem with these principal-class equalities. Lower-order and
  smoothing terms of P and Q are unrestricted. This uses Fredholmness supplied
  by ellipticity; it does not infer index invariance from raw algebraic index notation. -/
  obtain ⟨K, hK, he, h₀, h₁⟩ :=
    exists_continuous_homogeneous_path_of_cosphereHomotopic g m a b hab
  -- Keep the original P and Q while replacing their displayed endpoint representatives.
  have hreg₀ : R.regularizedSymbol m (K 0).val (K 0).property.1 (K 0).property.2 =
      R.regularizedSymbol m a.val a.property.1 a.property.2 :=
    Subtype.ext (R.regularizedSymbolFunction_congr _ _ h₀)
  have hreg₁ : R.regularizedSymbol m (K 1).val (K 1).property.1 (K 1).property.2 =
      R.regularizedSymbol m b.val b.property.1 b.property.2 :=
    Subtype.ext (R.regularizedSymbolFunction_congr _ _ h₁)
  apply index_eq_of_continuous_homogeneous_principalSymbol μ m P Q R C D A B K hK he
  · rwa [hreg₀]
  · rwa [hreg₁]

include hM hT2 hE hF hSC hC hμ in
/-- Equal elliptic cosphere restrictions suffice for equality of original operator indices. -/
theorem index_eq_of_cosphereRestriction_eq
    (m : ℝ) (P Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (he : IsEllipticCosphereSymbol g (cosphereRestriction g a.val))
    (hab : cosphereRestriction g a.val = cosphereRestriction g b.val)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2))
    (hQ : Q.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m b.val b.property.1 b.property.2)) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  /- The common restriction is smooth and thus continuous. Its constant
  elliptic path witnesses homotopy; the stated restriction equality supplies the
  second endpoint. Invoke index_eq_of_cosphereHomotopic with the unchanged original
  operators and actual principal-class hypotheses. -/
  have hc : IsContinuousCosphereSymbol (r := r) (q := q) g (cosphereRestriction g a.val) :=
    IsSmoothCosphereSymbol.continuous g (isSmoothCosphereSymbol_restriction g a.val a.property.1)
  have hhom := EllipticCosphereHomotopic.refl g (cosphereRestriction g a.val) hc he
  -- Only the second endpoint changes, by the supplied exact restriction equality.
  have hhom' : EllipticCosphereHomotopic (r := r) (q := q) g
      (cosphereRestriction g a.val) (cosphereRestriction g b.val) := by
    rw [← hab]
    exact hhom
  exact index_eq_of_cosphereHomotopic g μ m P Q R C D A B a b hhom' hP hQ

end PseudodifferentialOperator

end AtiyahSinger
