/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ComponentAnalyticIndex
public import AtiyahSinger.Analysis.FullSymbolRadialFactorization
public import AtiyahSinger.Analysis.SemiclassicalQuantizationIndex

/-!
# Analytic index of an arbitrary elliptic full symbol

Public module ID: M2310.

Sources: SG III.13 (13.1), (13.5)--(13.8), with the explicit radial factorization
in M2294 and the quantitative inverse argument in M2308. SG means H. Blaine
Lawson, Jr. and Marie-Louise Michelsohn, *Spin Geometry* (Princeton University
Press, 1989). The passage from a general full symbol to a homogeneous radial
model is a project supplement; it does not assert a homogeneous representative
for the original principal quotient class.

The original ellipticity predicate supplies its own full representative. Its
compact-support K class is independent of that choice. One radial factorization
relates its quantized index to a homogeneous model by an everywhere invertible
target factor. Both actual kernel and cokernel finiteness statements justify
composition of smooth indices. The final theorem evaluates the same original
operator without a displayed homogeneous representative or an extra estimate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [MeasurableSpace M] [hB : BorelSpace M]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- The standard symbol K class, choosing a full representative from original ellipticity. -/
def fullSymbolKClass (hi : P.IsElliptic) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  AtiyahSinger.fullSymbolKClass (Classical.choose hi) (Classical.choose_spec hi).2

/-- Every elliptic representative of the original principal class computes the same K class. -/
theorem fullSymbolKClass_eq_of_principalSymbol_eq (hi : P.IsElliptic)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hPa : P.principalSymbol = globalPrincipalSymbolClass E F m a)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val) :
    P.fullSymbolKClass hi = AtiyahSinger.fullSymbolKClass a ha := by
  -- Principal-class invariance applies to the actual representative chosen by hi.
  exact fullSymbolKClass_eq_of_principalClass_eq (Classical.choose hi) a
    (Classical.choose_spec hi).2 ha ((Classical.choose_spec hi).1.symm.trans hPa)

end PseudodifferentialOperator

include hM hT hSC hC hE hF hB hμ

/-- The actual quantization of every elliptic full symbol realizes its compact-support index. -/
theorem QuantizationPresentation.analyticIndexOfComponents_fullSymbolKClass {m : ℝ}
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val) :
    analyticIndexOfComponents μ (fullSymbolKClass a ha) =
      (A.quantize μ a).toLinearMap.index := by
  classical
  /- Choose the Sobolev presentations and the target quantizer internally. Keep
  exactly one radial tuple, including its original-symbol K-class equality. -/
  obtain ⟨AE⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨AF⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  obtain ⟨C⟩ := nonempty_quantizationPresentation (n := n) (r := q) (q := q)
    (E := F) (F := F)
  let g : SmoothCotangentMetric (n := n) (M := M) := SmoothCotangentMetric.nonempty.some
  obtain ⟨p, hp, b, hb, u, v, hUV, hVU, hfactor, heU, hclass, hK⟩ :=
    ha.exists_radialFactorization g A
  let Qa := A.quantize μ a
  let Qb := A.quantize μ b
  let Qu := C.quantize μ u
  have hiQa : Qa.IsElliptic := (PseudodifferentialOperator.isElliptic_quantize_iff A a).mpr ha
  have hiQb : Qb.IsElliptic := (PseudodifferentialOperator.isElliptic_quantize_iff A b).mpr hb
  have hiQu : Qu.IsElliptic := (PseudodifferentialOperator.isElliptic_quantize_iff C u).mpr heU
  -- The inverse identities are the actual two fiberwise products on the same target bundle.
  have hQuZero : Qu.toLinearMap.index = 0 :=
    C.index_quantize_eq_zero_of_isElliptic_of_inverse μ AF u v heU
      (fun x ξ ↦ congrFun (congrFun hUV x) ξ)
      (fun x ξ ↦ congrFun (congrFun hVU x) ξ)
  /- Repackage only the real order 0 + m = m. The actual composite section map
  remains Qu ∘ Qb. Its principal class is that of a by the supplied u*b=a. -/
  let S : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m := {
    toLinearMap := Qu.toLinearMap.comp Qb.toLinearMap
    isPseudodifferentialOperator := by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        (Qu.comp Qb).isPseudodifferentialOperator }
  have hprincipalFullComp {l t w : ℝ} (horder : l + t = w)
      (d : globalSymbolSpace (n := n) (r := r) (q := q) E F t)
      (e : globalSymbolSpace (n := n) (r := q) (q := q) F F l)
      (f : globalSymbolSpace (n := n) (r := r) (q := q) E F w)
      (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ t)
      (Q : PseudodifferentialOperator (n := n) (r := q) (q := q) F F μ l)
      (R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ w)
      (hP : P.principalSymbol = globalPrincipalSymbolClass E F t d)
      (hQ : Q.principalSymbol = globalPrincipalSymbolClass F F l e)
      (hR : R.toLinearMap = Q.toLinearMap.comp P.toLinearMap)
      (hproduct : globalSymbolComp e.val d.val = f.val) :
      R.principalSymbol = globalPrincipalSymbolClass E F w f := by
    subst w
    have hraw : (Q.comp P).principalSymbol = globalPrincipalSymbolClass E F (l + t) f := by
      rw [Q.principalSymbol_comp P, hQ, hP, globalPrincipalSymbolComp_class]
      exact congrArg (globalPrincipalSymbolClass E F (l + t)) (Subtype.ext hproduct)
    exact (R.principalSymbol_eq_of_toLinearMap_eq μ (Q.comp P) hR).trans hraw
  have hSa : S.principalSymbol = globalPrincipalSymbolClass E F m a :=
    hprincipalFullComp (zero_add m) b u a Qb Qu S
      (A.principalSymbol_quantize μ b) (C.principalSymbol_quantize μ u) rfl hfactor
  have hQaS : Qa.principalSymbol = S.principalSymbol :=
    (A.principalSymbol_quantize μ a).trans hSa.symm
  -- The composition index uses all four finiteness statements for these actual maps.
  let : FiniteDimensional ℂ Qb.toLinearMap.ker :=
    Qb.finiteDimensional_ker_of_isElliptic AE AF hiQb
  let : FiniteDimensional ℂ (smoothSections (n := n) (r := q) F ⧸ Qb.toLinearMap.range) :=
    Qb.finiteDimensional_coker_of_isElliptic AE AF hiQb
  let : FiniteDimensional ℂ Qu.toLinearMap.ker :=
    Qu.finiteDimensional_ker_of_isElliptic AF AF hiQu
  let : FiniteDimensional ℂ (smoothSections (n := n) (r := q) F ⧸ Qu.toLinearMap.range) :=
    Qu.finiteDimensional_coker_of_isElliptic AF AF hiQu
  have hQaQb : Qa.toLinearMap.index = Qb.toLinearMap.index := by
    calc
      Qa.toLinearMap.index = S.toLinearMap.index :=
        Qa.index_eq_of_isElliptic_of_principalSymbol_eq AE AF hiQa S hQaS
      _ = Qu.toLinearMap.index + Qb.toLinearMap.index :=
        LinearMap.index_comp Qu.toLinearMap Qb.toLinearMap
      _ = Qb.toLinearMap.index := by rw [hQuZero, zero_add]
  -- Evaluate only the frozen homogeneous model, then use the original tuple's K equality.
  have hQbp : Qb.principalSymbol = globalPrincipalSymbolClass E F m
      (A.regularizedSymbol m p.val p.property.1 p.property.2) :=
    (A.principalSymbol_quantize μ b).trans hclass
  have heval := Qb.analyticIndexOfComponents_symbolKClassOfHomogeneous μ A p hQbp hiQb
  rw [PseudodifferentialOperator.symbolKClassOfHomogeneous_eq,
    homogeneousSymbolKClass_eq_symbol] at heval
  rw [hK]
  exact heval.trans hQaQb.symm

set_option maxHeartbeats 1000000 in
-- Elaborating the full-class equality unfolds several dependent bundle maps.
/-- The standard analytic index evaluates the same original generally elliptic operator. -/
theorem PseudodifferentialOperator.analyticIndexOfComponents_fullSymbolKClass {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hi : P.IsElliptic) :
    analyticIndexOfComponents μ (P.fullSymbolKClass hi) = P.toLinearMap.index := by
  /- Use the original existential representative and internally produced quantizer.
  Same-principal index invariance keeps the given operator's complete smooth action. -/
  obtain ⟨a, hPa, ha⟩ := hi
  obtain ⟨A⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := q)
    (E := E) (F := F)
  obtain ⟨AE⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨AF⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) (E := F)
  have hiP : P.IsElliptic := ⟨a, hPa, ha⟩
  have hPQuant : P.principalSymbol = (A.quantize μ a).principalSymbol :=
    hPa.trans (A.principalSymbol_quantize μ a).symm
  calc
    analyticIndexOfComponents μ (P.fullSymbolKClass hiP) =
        analyticIndexOfComponents μ (AtiyahSinger.fullSymbolKClass a ha) :=
      congrArg (analyticIndexOfComponents μ)
        (P.fullSymbolKClass_eq_of_principalSymbol_eq hiP a hPa ha)
    _ = (A.quantize μ a).toLinearMap.index :=
      A.analyticIndexOfComponents_fullSymbolKClass a ha
    _ = P.toLinearMap.index :=
      (P.index_eq_of_isElliptic_of_principalSymbol_eq AE AF hiP
        (A.quantize μ a) hPQuant).symm

end AtiyahSinger
