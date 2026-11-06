/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticParametrix
public import AtiyahSinger.Analysis.ParametricQuantization
public import AtiyahSinger.Analysis.PseudodifferentialIndex

/-!
# Principal-class and homotopy invariance of the actual smooth PDO index

Public module ID: M0893.

A07/A08: connect SG III.5.2--5.3 to III.7.8--7.11. The original operator is
Fredholm when its principal class has elliptic homogeneous data. Equal principal
classes give compact differences, and symbol-seminorm continuous paths yield
operator-norm continuous Fredholm paths on fixed Sobolev spaces.
General inverse-bound full-symbol ellipticity and construction of a continuous
full-symbol lift from a cosphere homotopy remain separate obligations.
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

include hM hT2 hSC hC hE hF hμ

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

include A B

/-- Elliptic homogeneous principal data make the original PDO Fredholm at every real order. -/
theorem isFredholm_sobolevExtension_of_homogeneous_principalSymbol
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a)
    (hP : P.principalSymbol =
      globalPrincipalSymbolClass E F m (C.regularizedSymbol m a hs hh)) (s : ℝ) :
    (P.sobolevExtension A B s).IsFredholm := by
  /- First apply exists_parametrix_of_homogeneous_principalSymbol to the original
  P, using D only to construct the inverse symbol quantization. The returned
  order -m PDO is a two-sided smoothing parametrix. Its actual Sobolev realizations
  then satisfy the compact residual criterion for Fredholmness at the specified s. -/
  obtain ⟨Q, hQ⟩ := exists_parametrix_of_homogeneous_principalSymbol μ C D P a hs hh he hP
  exact P.isFredholm_sobolevExtension_of_isParametrix Q A B hQ s

/-- The index of an elliptic homogeneous-principal PDO is its original smooth-map index. -/
theorem index_sobolevExtension_eq_of_homogeneous_principalSymbol
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a)
    (hP : P.principalSymbol =
      globalPrincipalSymbolClass E F m (C.regularizedSymbol m a hs hh)) (s : ℝ) :
    (P.sobolevExtension A B s).index = P.toLinearMap.index := by
  /- Produce the actual two-sided parametrix from the homogeneous principal data.
  Apply index_sobolevExtension_eq_of_isParametrix. Its natural kernel and cokernel
  comparisons certify the finite smooth dimensions, for this same operator P. -/
  obtain ⟨Q, hQ⟩ := exists_parametrix_of_homogeneous_principalSymbol μ C D P a hs hh he hP
  exact P.index_sobolevExtension_eq_of_isParametrix A B Q hQ s

/-- Equality of principal classes preserves Fredholmness of the actual bounded realizations. -/
theorem isFredholm_sobolevExtension_of_principalSymbol_eq
    (R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPR : P.principalSymbol = R.principalSymbol) (s : ℝ)
    (hP : (P.sobolevExtension A B s).IsFredholm) :
    (R.sobolevExtension A B s).IsFredholm := by
  /- The existing principal-class comparison makes R_s-P_s compact at the
  critical Sobolev target. Write R_s=P_s+(R_s-P_s) and apply compact-perturbation
  invariance of Fredholmness. No pointwise inverse for an arbitrary full symbol
  is inferred from this abstract bounded-operator hypothesis. -/
  -- The same principal class makes the actual critical-order difference compact.
  have hcompact := R.isCompactOperator_sub_sobolevExtension A B P hPR.symm s
  have hsum : P.sobolevExtension A B s +
      (R.sobolevExtension A B s - P.sobolevExtension A B s) =
        R.sobolevExtension A B s := by abel
  -- Use that difference as a perturbation of the specified Fredholm realization.
  rw [← hsum]
  exact isFredholm_add_compact _ _ hP hcompact

/-- Equal principal classes give the same bounded Fredholm index. -/
theorem index_sobolevExtension_eq_of_principalSymbol_eq
    (R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPR : P.principalSymbol = R.principalSymbol) (s : ℝ)
    (hP : (P.sobolevExtension A B s).IsFredholm) :
    (P.sobolevExtension A B s).index = (R.sobolevExtension A B s).index := by
  /- The difference R_s-P_s is compact. Apply index_add_compact to P_s and this
  difference, then rewrite the sum as R_s. Equivalently the straight line segment
  consists of Fredholm operators in one fixed normed operator space. -/
  -- Compact perturbation preserves the index on the original fixed Sobolev spaces.
  have hcompact := R.isCompactOperator_sub_sobolevExtension A B P hPR.symm s
  have hsum : P.sobolevExtension A B s +
      (R.sobolevExtension A B s - P.sobolevExtension A B s) =
        R.sobolevExtension A B s := by abel
  have hindex := index_add_compact (P.sobolevExtension A B s)
    (R.sobolevExtension A B s - P.sobolevExtension A B s) hP hcompact
  rw [hsum] at hindex
  exact hindex.symm

/-- SG III.7.9: the smooth index depends only on the elliptic homogeneous principal class. -/
theorem index_eq_of_homogeneous_principalSymbol
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a)
    (hP : P.principalSymbol =
      globalPrincipalSymbolClass E F m (C.regularizedSymbol m a hs hh))
    (R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPR : P.principalSymbol = R.principalSymbol) :
    P.toLinearMap.index = R.toLinearMap.index := by
  /- The same principal data satisfy the hypotheses for R by hPR, so both
  operators have actual smoothing parametrices. At one fixed Sobolev order their
  realizations have equal indices by the compact difference theorem. Compare
  both indices with the original smooth maps; no smooth finite-dimensionality
  is assumed merely from equality of principal classes. -/
  -- The prescribed homogeneous data represent both actual principal classes.
  have hR := hPR.symm.trans hP
  have hfred := P.isFredholm_sobolevExtension_of_homogeneous_principalSymbol
    A B C D a hs hh he hP 0
  -- Compact perturbation compares the bounded indices; regularity returns to smooth maps.
  calc
    P.toLinearMap.index = (P.sobolevExtension A B 0).index :=
      (P.index_sobolevExtension_eq_of_homogeneous_principalSymbol
        A B C D a hs hh he hP 0).symm
    _ = (R.sobolevExtension A B 0).index :=
      P.index_sobolevExtension_eq_of_principalSymbol_eq A B R hPR 0 hfred
    _ = R.toLinearMap.index := R.index_sobolevExtension_eq_of_homogeneous_principalSymbol
      A B C D a hs hh he hR 0

/-- SG III.7.8 for an actual norm-continuous family with pointwise smoothing parametrices. -/
theorem index_eq_of_continuous_sobolevExtension
    (P : unitInterval →
      PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) (s : ℝ)
    (hP : Continuous (fun t ↦ (P t).sobolevExtension A B s))
    (hQ : ∀ t, ∃ Q : PseudodifferentialOperator
      (n := n) (r := q) (q := r) F E μ (-m),
      IsParametrix μ (P t).toLinearMap Q.toLinearMap) :
    (P 0).toLinearMap.index = (P 1).toLinearMap.index := by
  /- Stage 1: at each parameter, its parametrix makes the displayed extension
  Fredholm. The parameter interval and hP define a path in one fixed operator
  norm topology. No continuity of the chosen parametrices is needed.
  Stage 2: index_eq_of_fredholm_path identifies the bounded endpoint indices.
  The smooth/Sobolev comparison at each endpoint gives the displayed equality. -/
  -- The pointwise witnesses supply Fredholmness, without a continuous choice of Q.
  have hfredholm (t : unitInterval) : ((P t).sobolevExtension A B s).IsFredholm := by
    obtain ⟨Q, hQ⟩ := hQ t
    exact (P t).isFredholm_sobolevExtension_of_isParametrix Q A B hQ s
  let path : Path ((P 0).sobolevExtension A B s) ((P 1).sobolevExtension A B s) :=
    { toFun := fun t ↦ (P t).sobolevExtension A B s
      continuous_toFun := hP
      source' := rfl
      target' := rfl }
  have hindex := index_eq_of_fredholm_path path hfredholm
  -- Compare each endpoint with its own original smooth map using its given parametrix.
  obtain ⟨Q₀, hQ₀⟩ := hQ 0
  obtain ⟨Q₁, hQ₁⟩ := hQ 1
  rw [(P 0).index_sobolevExtension_eq_of_isParametrix A B Q₀ hQ₀ s,
    (P 1).index_sobolevExtension_eq_of_isParametrix A B Q₁ hQ₁ s] at hindex
  exact hindex

end PseudodifferentialOperator

namespace QuantizationPresentation

variable {m : ℝ}
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

include A B

/-- Both regularization and quantization choices preserve the index of fixed elliptic data. -/
theorem index_quantizeHomogeneous_eq
    (C C' R R' : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a) :
    (C.quantizeHomogeneous R μ m a hs hh).toLinearMap.index =
      (C'.quantizeHomogeneous R' μ m a hs hh).toLinearMap.index := by
  /- Each actual quantization has the principal class of its regularized data.
  Changing regularization leaves that class unchanged. Both operators therefore
  have the same elliptic homogeneous principal class; use the preceding smooth
  index comparison. If the quantizer changes, its difference need only improve
  by one order, so this proof uses compactness and does not assert a smooth kernel. -/
  -- Each operator realizes its own regularization of the same off-zero data.
  have hclass : (C.quantizeHomogeneous R μ m a hs hh).principalSymbol =
      (C'.quantizeHomogeneous R' μ m a hs hh).principalSymbol := by
    rw [C.principalSymbol_quantizeHomogeneous R μ, C'.principalSymbol_quantizeHomogeneous R' μ]
    exact (R.regularizedSymbol_class_eq_iff R' m a a hs hh hs hh).mpr
      (fun _ _ _ ↦ rfl)
  exact (C.quantizeHomogeneous R μ m a hs hh).index_eq_of_homogeneous_principalSymbol
    A B R D a hs hh he (C.principalSymbol_quantizeHomogeneous R μ m a hs hh)
    (C'.quantizeHomogeneous R' μ m a hs hh) hclass

-- These paths use the explicit weighted-derivative symbol topology.
attribute [local instance] globalSymbolTopology

/-- Continuous symbols with pointwise parametrices give a constant smooth quantized index. -/
theorem index_quantize_eq_of_continuous_of_isParametrix
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (p : unitInterval → globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : Continuous p)
    (hQ : ∀ t, ∃ Q : PseudodifferentialOperator
      (n := n) (r := q) (q := r) F E μ (-m),
      IsParametrix μ (C.quantize μ (p t)).toLinearMap Q.toLinearMap) :
    (C.quantize μ (p 0)).toLinearMap.index = (C.quantize μ (p 1)).toLinearMap.index := by
  /- Fix one real Sobolev order. continuous_sobolevQuantization sends the
  specified symbol-topology path to an operator-norm-continuous path. Apply
  index_eq_of_continuous_sobolevExtension with hQ. Pointwise symbol continuity
  alone would not give the required Sobolev operator-norm continuity. -/
  exact PseudodifferentialOperator.index_eq_of_continuous_sobolevExtension A B
    (fun t ↦ C.quantize μ (p t)) 0 (C.continuous_sobolevQuantization μ A B 0 m p hp) hQ

/-- SG III.7.10--7.11 for a continuous full-symbol path with elliptic homogeneous principal data. -/
theorem index_quantize_eq_of_homogeneous_principalSymbol_path
    (C R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (D : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (p : unitInterval → globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : Continuous p) (a : unitInterval → GlobalSymbolFunction (n := n) E F)
    (hs : ∀ t, IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F (a t))
    (hh : ∀ t, IsHomogeneousGlobalSymbol E F m (a t))
    (he : ∀ t, IsEllipticGlobalSymbol E F (a t))
    (hpa : ∀ t, globalPrincipalSymbolClass E F m (p t) =
      globalPrincipalSymbolClass E F m (R.regularizedSymbol m (a t) (hs t) (hh t))) :
    (C.quantize μ (p 0)).toLinearMap.index = (C.quantize μ (p 1)).toLinearMap.index := by
  /- Stage 1: principalSymbol_quantize and hpa identify the actual principal
  class at each t. The elliptic homogeneous parametrix theorem yields a pointwise
  two-sided smoothing parametrix, without requiring a continuous choice of inverses.
  Stage 2: apply the preceding continuous-symbol index statement using hp.
  Continuity is assumed for the actual full-symbol lift in its seminorm topology;
  a path of values on a cosphere has not yet been shown to supply such a lift. -/
  apply C.index_quantize_eq_of_continuous_of_isParametrix A B p hp
  intro t
  -- Use the actual quantization class at t, without making a continuous inverse choice.
  have hclass := (C.principalSymbol_quantize μ (p t)).trans (hpa t)
  exact exists_parametrix_of_homogeneous_principalSymbol μ R D
    (C.quantize μ (p t)) (a t) (hs t) (hh t) (he t) hclass

end QuantizationPresentation

end AtiyahSinger
