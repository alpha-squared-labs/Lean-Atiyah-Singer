/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialPrincipalSymbol
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.SmoothKernelDensity

/-!
# The same PDO under another auxiliary density

Public module ID: M0889.

D05/A02/A04/A07: preserve the actual section map while replacing only its local
representation certificate. The principal class, Sobolev extensions, ellipticity,
parametrices and algebraic smooth index are then compared explicitly.
Sources: SG III.3.15--3.19 and III.5.2--5.3; all density transports are project deductions.
The base, bundle norms and Sobolev presentations stay fixed.
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
  (μ ν : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hT2 hSC hC hE hF hμ hν

/-- The two-sided smooth-kernel parametrix condition is independent of positive density. -/
theorem isParametrix_measure_iff
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E) :
    IsParametrix μ P Q ↔ IsParametrix ν P Q := by
  /- Apply smooth-kernel density independence separately to the two actual
  residual maps QP-I and PQ-I. Their signs, source fibers and target fibers
  are unchanged; neither parametrix is replaced by an unrelated existence witness. -/
  exact and_congr
    (isSmoothingOperator_measure_iff μ ν (Q.comp P - LinearMap.id))
    (isSmoothingOperator_measure_iff μ ν (P.comp Q - LinearMap.id))

namespace PseudodifferentialOperator

variable {μ} {m : ℝ}
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- The same smooth-section map, certified as a PDO relative to the new density. -/
def changeMeasure : PseudodifferentialOperator (n := n) (r := r) (q := q) E F ν m where
  toLinearMap := P.toLinearMap
  isPseudodifferentialOperator :=
    (isPseudodifferentialOperator_measure_iff (μ := μ) ν m P.toLinearMap).mp
      P.isPseudodifferentialOperator

/-- Density transport preserves the exact section operator. -/
theorem toLinearMap_changeMeasure : (P.changeMeasure ν).toLinearMap = P.toLinearMap := by
  /- This is the defining data field of changeMeasure. Only the proof of the
  standard local PDO representation changes; no quantization is performed again. -/
  rfl

omit hν in
/-- Changing to the original density leaves the bundled PDO unchanged. -/
theorem changeMeasure_self : P.changeMeasure μ = P := by
  /- Both structures have the same actual section map. Their representation
  fields are propositions, so proof irrelevance identifies the bundled operators. -/
  cases P
  rfl

/-- Consecutive density changes have the same result as the direct one. -/
theorem changeMeasure_trans (κ : Measure M) [IsSmoothPositiveMeasure (n := n) κ] :
    (P.changeMeasure ν).changeMeasure κ = P.changeMeasure κ := by
  /- Both constructions retain P.toLinearMap literally. Use structure
  extensionality; the differently obtained representation certificates carry no data. -/
  rfl

/-- The principal quotient class is unchanged by transport of the same operator. -/
theorem principalSymbol_changeMeasure :
    (P.changeMeasure ν).principalSymbol = P.principalSymbol := by
  /- Retain the same finite local pieces and reweight only the smooth kernel.
  The sum of their global symbols is unchanged. Equivalently apply the existing
  cross-density principal-class comparison to the exact section-map equality. -/
  exact (P.changeMeasure ν).principalSymbol_eq_of_toLinearMap_eq μ P rfl

/-- Every original real-order Sobolev extension is literally unchanged by density transport. -/
theorem sobolevExtension_changeMeasure
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (s : ℝ) :
    (P.changeMeasure ν).sobolevExtension A B s = P.sobolevExtension A B s := by
  /- The Sobolev spaces here are fixed localized completions, independent of
  the density. Both continuous extensions agree with P on the same dense smooth
  image, so extension uniqueness identifies them as actual bounded operators. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    ((P.changeMeasure ν).sobolevExtension A B s).continuous
    (P.sobolevExtension A B s).continuous
  funext u
  exact ((P.changeMeasure ν).sobolevExtension_smoothToSobolev A B s u).trans
    (P.sobolevExtension_smoothToSobolev A B s u).symm

/-- Coordinate inverse-bound ellipticity is unaffected by changing the auxiliary density. -/
theorem isElliptic_changeMeasure_iff : (P.changeMeasure ν).IsElliptic ↔ P.IsElliptic := by
  /- The ellipticity predicate asks for an inverse-bound representative of the
  principal class. The preceding class equality gives exactly the same possible
  representatives and bounds; no Hermitian or cosphere comparison is used. -/
  unfold IsElliptic
  rw [P.principalSymbol_changeMeasure ν]

/-- The algebraic smooth index of the same section map cannot depend on density. -/
theorem index_changeMeasure : (P.changeMeasure ν).toLinearMap.index = P.toLinearMap.index := by
  /- The two section maps are definitionally identical. Their algebraic kernels
  and cokernels, and hence the totalized integer index, coincide. This equality
  needs no ellipticity; using it as a Fredholm index requires the separate theorem. -/
  rfl

/-- Finite local addition commutes with density transport. -/
theorem changeMeasure_add (Q : PseudodifferentialOperator (n := n) (r := r) (q := q)
    E F μ m) : (P.add Q).changeMeasure ν = (P.changeMeasure ν).add (Q.changeMeasure ν) := by
  /- Both sides are the sum of the two original section maps. Equality of
  that data field and proof irrelevance identify the structures, without choosing
  or comparing any new local symbol representatives. -/
  rfl

/-- Complex scaling commutes with density transport. -/
theorem changeMeasure_smul (c : ℂ) :
    (P.smul c).changeMeasure ν = (P.changeMeasure ν).smul c := by
  /- The density change preserves the underlying linear map, and the scalar
  construction scales precisely that map. Compare these fields and use proof irrelevance. -/
  rfl

end PseudodifferentialOperator

namespace DifferentialOperator

/-- The exact differential inclusion commutes with density transport, including order zero. -/
theorem toPseudodifferentialOperator_changeMeasure {k : ℕ}
    (Q : DifferentialOperator (n := n) (r := r) (q := q) E F k) :
    (Q.toPseudodifferentialOperator μ).changeMeasure ν = Q.toPseudodifferentialOperator ν := by
  /- Both exact differential inclusions have Q.toLinearMap as their data field.
  Density transport preserves that field. This applies for every natural order,
  including zero, and does not assume the differential operator is elliptic. -/
  rfl

end DifferentialOperator

end AtiyahSinger
