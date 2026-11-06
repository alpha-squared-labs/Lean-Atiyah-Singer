/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolKClass

/-!
# Cosphere symbol classes and radial compatibility

Public module ID: M0418.

SG III.1 (1.6)–(1.7), III.13 (13.1). The degree-zero extension defines a class on
the actual cotangent space. Positive radial homotopies show degree independence;
metric transport must retain the degree-dependent weight. Empty cospheres are
allowed and do not force the source-minus-target class to vanish.
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

open ComplexBundle

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- Metric transport preserves total-space continuity with its full radial weight. -/
theorem IsContinuousCosphereSymbol.metricTransport
    (k : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    {a : CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a) :
    IsContinuousCosphereSymbol (r := r) (q := q) k (cosphereMetricTransport g k m a) := by
  /- Continuously extend the original section off zero at degree m and restrict it to the
  k-cosphere. The extension includes the positive g-length power, which must be retained
  whenever m differs from zero. -/
  exact (isContinuousOffZeroGlobalSymbol_cosphereExtension g m a ha).cosphereRestriction k

variable [CompactSpace M] [T2Space M]

/-- The cotangent support class of a continuous elliptic cosphere symbol. -/
def cosphereKClass (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (hi : IsEllipticCosphereSymbol g a) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  symbolKClass (cosphereExtension g 0 a)
    (isContinuousOffZeroGlobalSymbol_cosphereExtension g 0 a ha)
    ((isEllipticGlobalSymbol_cosphereExtension_iff g 0 a).mpr hi)

/-- The canonical cosphere class uses exactly the degree-zero original extension. -/
theorem cosphereKClass_eq_extension_zero (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (hi : IsEllipticCosphereSymbol g a) :
    cosphereKClass g a ha hi = symbolKClass (cosphereExtension g 0 a)
      (isContinuousOffZeroGlobalSymbol_cosphereExtension g 0 a ha)
      ((isEllipticGlobalSymbol_cosphereExtension_iff g 0 a).mpr hi) := by
  /- Unfold the cosphere-class definition. Both sides apply the previously constructed symbol
  class to the exact same degree-zero radial function, with its original source and target
  bundles. -/
  rfl

/-- Changing radial degree leaves the cotangent support class unchanged. -/
theorem symbolKClass_extension_degree (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (hi : IsEllipticCosphereSymbol g a) (m l : ℝ) :
    symbolKClass (cosphereExtension g m a)
      (isContinuousOffZeroGlobalSymbol_cosphereExtension g m a ha)
    ((isEllipticGlobalSymbol_cosphereExtension_iff g m a).mpr hi) =
    symbolKClass (cosphereExtension g l a)
      (isContinuousOffZeroGlobalSymbol_cosphereExtension g l a ha)
    ((isEllipticGlobalSymbol_cosphereExtension_iff g l a).mpr hi) := by
  /- Use the explicit affine-degree family. It is jointly continuous on the punctured cotangent
  space and elliptic at every time because all radial factors are positive. Its exact
  endpoints are the two extensions, and the zero section is one compact control for the
  whole family. Apply symbol-class homotopy invariance. -/
  exact symbolKClass_eq_of_family _ _ _ _ _ _ (cosphereDegreeFamily g m l a)
    (isContinuousOffZeroSymbolFamily_degree g m l a ha)
    (isEllipticGlobalSymbol_degree g m l a hi)
    (cosphereDegreeFamily_zero g m l a) (cosphereDegreeFamily_one g m l a)

/-- Every real homogeneous extension represents the canonical cosphere class. -/
theorem symbolKClass_extension (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (hi : IsEllipticCosphereSymbol g a) (m : ℝ) :
    symbolKClass (cosphereExtension g m a)
      (isContinuousOffZeroGlobalSymbol_cosphereExtension g m a ha)
    ((isEllipticGlobalSymbol_cosphereExtension_iff g m a).mpr hi) =
      cosphereKClass g a ha hi := by
  /- Compare degree m with degree zero using the positive radial homotopy. The latter extension
  is precisely the function used to define the cosphere class. -/
  exact symbolKClass_extension_degree g a ha hi m 0

/-- Restriction of homogeneous data computes its original cotangent class. -/
theorem symbolKClass_eq_cosphere (m : ℝ) (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (hi : IsEllipticGlobalSymbol E F a) :
    symbolKClass a ha hi = cosphereKClass g (cosphereRestriction g a)
      (ha.cosphereRestriction g)
      ((isEllipticCosphereSymbol_restriction_iff g m a hh).mpr hi) := by
  /- Reconstruction from unit directions at the same degree agrees with the original
  homogeneous symbol at every nonzero covector. Apply off-zero invariance, then independence
  of the extension degree. Arbitrary values of the original symbol at zero are not
  identified. -/
  let b := cosphereRestriction g a
  have hb : IsContinuousCosphereSymbol (r := r) (q := q) g b := ha.cosphereRestriction g
  have hj : IsEllipticCosphereSymbol g b :=
    (isEllipticCosphereSymbol_restriction_iff g m a hh).mpr hi
  calc
    symbolKClass a ha hi = symbolKClass (cosphereExtension g m b)
        (isContinuousOffZeroGlobalSymbol_cosphereExtension g m b hb)
        ((isEllipticGlobalSymbol_cosphereExtension_iff g m b).mpr hj) := by
      apply symbolKClass_congr
      intro x ξ hξ
      exact (cosphereExtension_restriction g m a hh x ξ hξ).symm
    _ = cosphereKClass g b hb hj := symbolKClass_extension g b hb hj m

/-- Equal cosphere sections have equal classes, with proof certificates irrelevant. -/
theorem cosphereKClass_congr (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (hi : IsEllipticCosphereSymbol g a)
    (b : CosphereSymbolFunction (E := E) (F := F) g)
    (hb : IsContinuousCosphereSymbol (r := r) (q := q) g b)
    (hj : IsEllipticCosphereSymbol g b) (hab : a = b) :
    cosphereKClass g a ha hi = cosphereKClass g b hb hj := by
  /- Substitute equality of the original sections into the explicit degree-zero extension. The
  remaining continuity and ellipticity arguments are proofs of propositions. -/
  cases hab
  rfl

/-- A continuous elliptic cosphere homotopy preserves the actual cotangent class. -/
theorem cosphereKClass_eq_of_homotopic (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (hi : IsEllipticCosphereSymbol g a)
    (b : CosphereSymbolFunction (E := E) (F := F) g)
    (hb : IsContinuousCosphereSymbol (r := r) (q := q) g b)
    (hj : IsEllipticCosphereSymbol g b)
    (hab : EllipticCosphereHomotopic (r := r) (q := q) g a b) :
    cosphereKClass g a ha hi = cosphereKClass g b hb hj := by
  /- Choose the jointly continuous elliptic cosphere family and extend it radially at degree
  zero. This gives one jointly continuous off-zero family, elliptic for all times and
  controlled by the same compact zero section. Its endpoints are the two original
  extensions. -/
  obtain ⟨H, hH, hI, h₀, h₁⟩ := hab
  apply symbolKClass_eq_of_family _ _ _ _ _ _
    (fun t ↦ cosphereExtension g 0 (H t)) (hH.extension g 0)
  · intro t
    exact (isEllipticGlobalSymbol_cosphereExtension_iff g 0 (H t)).mpr (hI t)
  · exact congrArg (cosphereExtension g 0) h₀
  · exact congrArg (cosphereExtension g 0) h₁

/-- Changing the cotangent metric preserves the class with the correct transport. -/
theorem cosphereKClass_metricTransport (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (hi : IsEllipticCosphereSymbol g a)
    (k : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ) :
    cosphereKClass k (cosphereMetricTransport g k m a) (ha.metricTransport g k m)
      ((isEllipticCosphereSymbol_metricTransport_iff g k m a).mpr hi) =
      cosphereKClass g a ha hi := by
  /- Represent both classes using degree m rather than degree zero. The metric transport
  theorem identifies these full radial extensions exactly, because it retains the length
  weight. Their symbol classes coincide, and degree independence returns the canonical
  classes. -/
  let b := cosphereMetricTransport g k m a
  have hb : IsContinuousCosphereSymbol (r := r) (q := q) k b :=
    ha.metricTransport g k m
  have hj : IsEllipticCosphereSymbol k b :=
    (isEllipticCosphereSymbol_metricTransport_iff g k m a).mpr hi
  calc
    cosphereKClass k b hb hj = symbolKClass (cosphereExtension k m b)
        (isContinuousOffZeroGlobalSymbol_cosphereExtension k m b hb)
        ((isEllipticGlobalSymbol_cosphereExtension_iff k m b).mpr hj) :=
      (symbolKClass_extension k b hb hj m).symm
    _ = symbolKClass (cosphereExtension g m a)
        (isContinuousOffZeroGlobalSymbol_cosphereExtension g m a ha)
        ((isEllipticGlobalSymbol_cosphereExtension_iff g m a).mpr hi) := by
      apply symbolKClass_congr
      intro x ξ hξ
      exact congrFun (congrFun (cosphereExtension_metricTransport g k m a) x) ξ
    _ = cosphereKClass g a ha hi := symbolKClass_extension g a ha hi m

/-- The class obtained by restricting fixed homogeneous data is metric independent. -/
theorem cosphereKClass_restriction_metric_independent
    (k : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (hi : IsEllipticGlobalSymbol E F a) :
    cosphereKClass g (cosphereRestriction g a) (ha.cosphereRestriction g)
      ((isEllipticCosphereSymbol_restriction_iff g m a hh).mpr hi) =
    cosphereKClass k (cosphereRestriction k a) (ha.cosphereRestriction k)
      ((isEllipticCosphereSymbol_restriction_iff k m a hh).mpr hi) := by
  /- Each restricted class equals the original symbol class on the same cotangent total space.
  Compose those two equalities. This compares auxiliary metrics without silently replacing
  cotangent by tangent. -/
  exact (symbolKClass_eq_cosphere g m a ha hh hi).symm.trans
    (symbolKClass_eq_cosphere k m a ha hh hi)

/-- The empty-cosphere case still records the source and target bundle difference. -/
theorem cosphereKClass_of_dim_zero (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (hi : IsEllipticCosphereSymbol g a) (hn : n = 0) :
    compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback
        ⟨(cotangentProjectionHomeomorphOfDimZero hn).symm,
          (cotangentProjectionHomeomorphOfDimZero hn).symm.continuous⟩
        (cotangentProjectionHomeomorphOfDimZero hn).symm.isProperMap
        (cosphereKClass g a ha hi)) =
      (modelFiniteBundle (EuclideanSpace ℂ (Fin r)) E).kZeroClass -
        (modelFiniteBundle (EuclideanSpace ℂ (Fin q)) F).kZeroClass := by
  /- Apply the dimension-zero formula to the degree-zero extension used in the definition.
  Although the cosphere and boundary are empty, the triple retains both original bundles on
  its entire compact control, giving their difference rather than a forced zero class. -/
  exact symbolKClass_of_dim_zero (cosphereExtension g 0 a)
    (isContinuousOffZeroGlobalSymbol_cosphereExtension g 0 a ha)
    ((isEllipticGlobalSymbol_cosphereExtension_iff g 0 a).mpr hi) hn

end AtiyahSinger
