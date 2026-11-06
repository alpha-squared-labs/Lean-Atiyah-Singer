/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianMetricAdjoint

/-!
# The integral formal-adjoint identity for explicit metrics

Public module ID: M0722.

D02: a standard formal-adjoint relation on actual smooth linear maps. Its symmetry,
uniqueness and change-of-metric laws are independent of a PDO presentation.
Sources: SG III.5 (5.1), pp.193–195; metric-change formulas are project deductions.
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

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

variable [MeasurableSpace M] (μ : Measure M)

/-- The same-density integral identity, with both metrics supplied as data. -/
def IsMetricFormalAdjoint
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E) :
    Prop :=
  ∀ u v, k.sectionPairing μ (P u) v = h.sectionPairing μ u (Q v)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hBorel : BorelSpace M] [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hμ

namespace IsMetricFormalAdjoint

variable {h k μ}
  {P R : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F}
  {Q S : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E}

/-- The integral identity determines the reversed section map uniquely. -/
theorem unique (hPQ : IsMetricFormalAdjoint h k μ P Q)
    (hPS : IsMetricFormalAdjoint h k μ P S) : Q = S := by
  /- Subtract the identities for fixed v and test with u=Qv-Sv. Positivity
  of the integral pairing makes that smooth section zero; extensionality then
  identifies the linear maps. Full support of the positive density is essential. -/
  let core : InnerProductSpace.Core ℂ (smoothSections (n := n) (r := r) E) :=
    h.smoothL2SectionCore μ
  apply LinearMap.ext
  intro v
  have hzero : h.sectionPairing μ (Q v - S v) (Q v - S v) = 0 := by
    change core.inner (Q v - S v) (Q v - S v) = 0
    rw [InnerProductSpace.Core.inner_sub_right]
    change h.sectionPairing μ (Q v - S v) (Q v) -
      h.sectionPairing μ (Q v - S v) (S v) = 0
    rw [← hPQ, ← hPS, sub_self]
  exact sub_eq_zero.mp ((h.sectionPairing_self_eq_zero_iff μ _).mp hzero)

/-- Hermitian symmetry reverses the formal-adjoint relation. -/
theorem symm (hPQ : IsMetricFormalAdjoint h k μ P Q) :
    IsMetricFormalAdjoint k h μ Q P := by
  /- Conjugate the identity for each u,v and apply conjugate symmetry of
  both integrals. Swapping the test variables gives exactly the reversed relation. -/
  intro v u
  have hconj := congrArg (starRingEnd ℂ) (hPQ u v)
  rw [k.sectionPairing_conj_symm, h.sectionPairing_conj_symm] at hconj
  exact hconj.symm

/-- Adding two paired section maps adds their adjoints. -/
theorem add (hPQ : IsMetricFormalAdjoint h k μ P Q)
    (hRS : IsMetricFormalAdjoint h k μ R S) :
    IsMetricFormalAdjoint h k μ (P + R) (Q + S) := by
  /- Expand both integral pairings using integrability on the compact
  base. Substitute the two given identities and recombine the second-slot sums. -/
  let core : InnerProductSpace.Core ℂ (smoothSections (n := n) (r := r) E) :=
    h.smoothL2SectionCore μ
  intro u v
  -- The first slot splits by integrability, and the positive integral core splits the second.
  change k.sectionPairing μ (P u + R u) v =
    core.inner u (Q v + S v)
  rw [k.sectionPairing_add_left, InnerProductSpace.Core.inner_add_right]
  exact congrArg₂ (· + ·) (hPQ u v) (hRS u v)

/-- Scaling the original map conjugates the scalar in its adjoint. -/
theorem smul (hPQ : IsMetricFormalAdjoint h k μ P Q) (c : ℂ) :
    IsMetricFormalAdjoint h k μ (c • P) (conj c • Q) := by
  /- The first slot of the target metric conjugates c. Move that same
  scalar into the linear second slot of the source metric after applying the
  given adjunction identity; compactness justifies the integral scalar laws. -/
  let core : InnerProductSpace.Core ℂ (smoothSections (n := n) (r := r) E) :=
    h.smoothL2SectionCore μ
  intro u v
  change k.sectionPairing μ (c • P u) v =
    core.inner u (conj c • Q v)
  rw [k.sectionPairing_smul_left, InnerProductSpace.Core.inner_smul_right]
  exact congrArg (conj c * ·) (hPQ u v)

/-- Changing the metrics conjugates the actual reversed section map. -/
theorem change (hPQ : IsMetricFormalAdjoint h k μ P Q)
    (h' : SmoothHermitianMetric (n := n) (r := r) E)
    (k' : SmoothHermitianMetric (n := n) (r := q) F) :
    IsMetricFormalAdjoint h' k' μ P
      ((h'.changeSections h).toLinearMap.comp (Q.comp (k.changeSections k').toLinearMap)) := by
  /- Convert the k' pairing to k using B_F in the second slot, apply hPQ,
  and convert the h pairing to h' using B_E⁻¹. These pointwise metric identities
  give the exact section-map conjugation without an ellipticity assumption. -/
  intro u v
  change k'.sectionPairing μ (P u) v =
    h'.sectionPairing μ u (h'.changeSections h (Q (k.changeSections k' v)))
  rw [h'.sectionPairing_change, ← k.sectionPairing_change μ k']
  exact hPQ u (k.changeSections k' v)

end IsMetricFormalAdjoint

set_option linter.unusedSectionVars false in
/-- The zero map has zero formal adjoint. -/
theorem isMetricFormalAdjoint_zero :
    IsMetricFormalAdjoint h k μ
      (0 : smoothSections (n := n) (r := r) E →ₗ[ℂ]
        smoothSections (n := n) (r := q) F) 0 := by
  /- Both integral expressions vanish pointwise by sesquilinearity.
  Integrating the zero function gives the claimed relation for all test sections. -/
  intro u v
  change (∫ x, k.pairing x 0 (v.val x) ∂μ) = ∫ x, h.pairing x (u.val x) 0 ∂μ
  have hkzero (x : M) : k.pairing x 0 (v.val x) = 0 := by
    let := k.toCore x
    exact InnerProductSpace.Core.inner_zero_left _
  have hzero (x : M) : h.pairing x (u.val x) 0 = 0 := by
    let := h.toCore x
    exact InnerProductSpace.Core.inner_zero_right _
  simp_rw [hkzero, hzero]

set_option linter.unusedSectionVars false in
/-- Identity is formally self-adjoint with respect to a single metric. -/
theorem isMetricFormalAdjoint_id : IsMetricFormalAdjoint h h μ LinearMap.id LinearMap.id := by
  /- The identity maps leave the two test sections unchanged. The two
  integrands therefore coincide exactly, proving the same-density adjunction. -/
  intro u v
  rfl

variable {a : ℕ}
  {G : M → Type*}
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) G]

set_option linter.unusedSectionVars false in
/-- Formal adjunction reverses composition with the shared middle metric. -/
theorem IsMetricFormalAdjoint.comp (l : SmoothHermitianMetric (n := n) (r := a) G)
    {P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F}
    {Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E}
    {R : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := a) G}
    {S : smoothSections (n := n) (r := a) G →ₗ[ℂ] smoothSections (n := n) (r := q) F}
    (hPQ : IsMetricFormalAdjoint h k μ P Q) (hRS : IsMetricFormalAdjoint k l μ R S) :
    IsMetricFormalAdjoint h l μ (R.comp P) (Q.comp S) := by
  /- First use hRS with Pu and the final test section. Then use hPQ with
  u and S applied to that test. The common middle metric disappears from the
  equation, leaving the reversed composition in the original source pairing. -/
  intro u w
  exact (hRS (P u) w).trans (hPQ u (S w))

end AtiyahSinger
