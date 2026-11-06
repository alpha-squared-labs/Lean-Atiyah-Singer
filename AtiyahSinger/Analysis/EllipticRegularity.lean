/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialParametrix
public import AtiyahSinger.Analysis.SobolevParametrix

/-!
# Global Sobolev consequences for elliptic differential operators

Public module ID: M0453.

A06: SG III.5.2, with the original differential Sobolev extension. First identify
that extension with its PDO realization. The parametrix then gives Fredholmness
at every real order, global finite-order and smooth regularity, and the fundamental
elliptic estimate. Local regularity on arbitrary open subsets, cokernel comparison,
and independence of the index are established separately.
The bounded-realization comparison and all four global consequences are proved
using the original differential parametrix-existence theorem.
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

include hM hT2 hSC hC hE hF hμ

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The PDO inclusion and the original differential operator have the same bounded extension. -/
theorem sobolevExtension_toPseudodifferentialOperator (s : ℝ) :
    (P.toPseudodifferentialOperator μ).sobolevExtension A B s =
      P.sobolevExtension A B s := by
  /- Both bounded maps realize exactly P.toLinearMap on the same dense smooth
  image and take values in H^(s-m)(F). Their unique continuous extensions agree.
  No ellipticity, formal adjoint, or change of Sobolev presentation is needed. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    ((P.toPseudodifferentialOperator μ).sobolevExtension A B s).continuous
    (P.sobolevExtension A B s).continuous
  funext u
  simp only [Function.comp_apply]
  rw [PseudodifferentialOperator.sobolevExtension_smoothToSobolev,
    P.sobolevExtension_smoothToSobolev]
  rfl

/-- SG III.5.2(ii), Fredholmness of the original differential extension at every real order. -/
theorem isFredholm_sobolevExtension (hP : P.IsElliptic) (s : ℝ) :
    (P.sobolevExtension A B s).IsFredholm := by
  /- Stage 1: obtain an actual order -m two-sided smoothing parametrix for P.
  Since the PDO inclusion retains P.toLinearMap, this is also a parametrix for
  that bundled PDO. Apply its Sobolev Fredholm theorem using A and B.
  Stage 2: replace the PDO extension by the preceding equality. This includes
  closed range and finite-dimensional kernel and cokernel, but does not yet
  compare their dimensions across s or identify the smooth analytic index. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  rw [← P.sobolevExtension_toPseudodifferentialOperator μ A B s]
  exact (P.toPseudodifferentialOperator μ).isFredholm_sobolevExtension_of_isParametrix
    Q A B hQ s

/-- Global elliptic regularity lifts a solution when its right-hand side has higher order. -/
theorem existsUnique_sobolev_lift (hP : P.IsElliptic)
    (s t : ℝ) (hst : s ≤ t) (u : A.SobolevSpace s) (v : B.SobolevSpace (t - m))
    (hu : P.sobolevExtension A B s u =
      B.sobolevInclusion (t - m) (s - m) (by linarith) v) :
    ∃! w : A.SobolevSpace t,
      A.sobolevInclusion t s hst w = u ∧ P.sobolevExtension A B t w = v := by
  /- Choose the differential parametrix and use its left smoothing error. Compare
  the differential and PDO realizations at both s and t, then apply the parametrix
  lifting theorem. Both the inclusion equality and the equation refer to the
  supplied u and v, so this states regularity of the original solution. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  rw [← P.sobolevExtension_toPseudodifferentialOperator μ A B s] at hu
  simpa only [P.sobolevExtension_toPseudodifferentialOperator μ A B t] using
    (P.toPseudodifferentialOperator μ).existsUnique_sobolev_lift_of_isSmoothingOperator
      Q A B hQ.1 s t hst u v hu

/-- SG III.5.2(i) on the whole closed base: a smooth right-hand side gives a smooth solution. -/
theorem existsUnique_smooth_lift (hP : P.IsElliptic)
    (s : ℝ) (u : A.SobolevSpace s) (v : smoothSections (n := n) (r := q) F)
    (hu : P.sobolevExtension A B s u = B.smoothToSobolev (s - m) v) :
    ∃! w : smoothSections (n := n) (r := r) E,
      A.smoothToSobolev s w = u ∧ P.toLinearMap w = v := by
  /- Choose the actual differential parametrix and apply the smooth lifting
  theorem to its left error after comparing the bounded extensions. The PDO
  inclusion retains exactly P's smooth action, so the returned equation is P w=v.
  This proves global smoothness for an already given Sobolev solution. It does
  not assert uniqueness among all solutions of P w=v or solvability for every v. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  rw [← P.sobolevExtension_toPseudodifferentialOperator μ A B s] at hu
  exact (P.toPseudodifferentialOperator μ).existsUnique_smooth_lift_of_isSmoothingOperator
    Q A B hQ.1 s u v hu

/-- SG III.5.2(iii): the fundamental elliptic estimate on actual Sobolev completions. -/
theorem exists_elliptic_estimate (hP : P.IsElliptic) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.SobolevSpace s,
      ‖u‖ ≤ C * (‖P.sobolevExtension A B s u‖ +
        ‖A.sobolevInclusion s (s - m) (sub_le_self s (Nat.cast_nonneg m)) u‖) := by
  /- Choose the parametrix Q and its left error K=QP-I. The parametrix estimate
  at lower order s-m bounds u by Q(Pu) and the all-order extension of K applied
  to u in H^(s-m). Compare the original differential and PDO extensions.
  The constant depends on P, s and the chosen presentations, but is chosen before
  u. Natural m gives s-m<=s. For m=0 the estimate is valid without a strict gain. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  simpa only [P.sobolevExtension_toPseudodifferentialOperator μ A B s] using
    (P.toPseudodifferentialOperator μ).exists_estimate_of_isSmoothingOperator Q A B hQ.1
      s (s - m) (sub_le_self s (Nat.cast_nonneg m))

end DifferentialOperator

end AtiyahSinger
