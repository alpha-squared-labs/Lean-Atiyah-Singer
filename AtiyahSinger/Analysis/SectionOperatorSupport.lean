/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricFormalAdjoint
public import AtiyahSinger.Geometry.OpenSections
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Support of actual operators on smooth bundle sections

Public module ID: M0956.

UL03/P02: the standard two-sided operator support of SG III.3, p.183, on actual
bundle sections. Output support and annihilation of inputs supported away from K
are separate requirements. Input control concerns a germ near K, not merely the
values on K. On a compact base the actual integral adjoint has the same support.
The latter is a project supplement to the two-kernel argument of III.13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

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

/-- Both projections of operator support lie in K, expressed on actual smooth sections. -/
def HasSectionOperatorSupport (K : Set M)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F) : Prop :=
  (∀ u, closure {x | (P u).val x ≠ 0} ⊆ K) ∧
    ∀ u, Disjoint (closure {x | u.val x ≠ 0}) K → P u = 0

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hB : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hSC hC hB hE hF


set_option linter.unusedSectionVars false in
/-- The actual integral adjoint of a supported operator has the same two-sided support. -/
theorem IsMetricFormalAdjoint.hasSectionOperatorSupport
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F)
    (R : smoothSections (n := n) (r := q) F →ₗ[ℂ]
      smoothSections (n := n) (r := r) E)
    (hPR : IsMetricFormalAdjoint h k μ P R)
    (K : Set M) (hK : IsClosed K) (hP : HasSectionOperatorSupport K P) :
    HasSectionOperatorSupport K R := by
  /- Stage 1: if u is supported away from K, Pu=0, so adjunction makes the
  pairing of u with Rv zero for every v. At a point outside closed K, take
  a mathlib smooth bump χ supported in the complement and equal to one at
  that point. Test with χ²Rv; the same integral is the self-pairing of χRv.
  Positive density and the metric force χRv=0, hence Rv vanishes at the point.
  This uses the local bump case of the cutoff argument; taking closures
  keeps the output support in K.
  Stage 2: if v is supported away from K, the pairing of Pu with v is zero
  because Pu is supported in K. Adjunction then gives <u,Rv>=0 for every u.
  Test with u=Rv and use definiteness on the compact base to obtain Rv=0.
  No PDO or ellipticity assumption is needed, but the full integral adjunction
  identity is supplied; this does not construct a noncompact formal adjoint. -/
  classical
  constructor
  · intro v
    apply closure_minimal _ hK
    intro x hx
    by_contra hxK
    -- A local smooth bump separates this point from the closed operator support.
    obtain ⟨χ, _, hχ⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x).mem_iff.mp
          (hK.isOpen_compl.mem_nhds hxK)
    let mulSection (u : smoothSections (n := n) (r := r) E) :
        smoothSections (n := n) (r := r) E :=
      ⟨fun y ↦ (χ y : ℂ) • u.val y, by
        intro e he
        let := he
        apply (χ.contMDiff.contMDiffOn.smul (u.property e he)).congr
        intro y hy
        change (e.linearEquivAt ℂ y hy) ((χ y : ℂ) • u.val y) =
          χ y • (e.linearEquivAt ℂ y hy) (u.val y)
        rw [map_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
        rfl⟩
    let w := mulSection (R v)
    let u := mulSection w
    have husupport : closure {y | u.val y ≠ 0} ⊆ tsupport χ := by
      apply closure_minimal _ isClosed_closure
      intro y hy
      apply subset_closure
      change χ y ≠ 0
      intro hz
      apply hy
      change (χ y : ℂ) • w.val y = 0
      simp only [hz, Complex.ofReal_zero, zero_smul]
    have huK : Disjoint (closure {y | u.val y ≠ 0}) K := by
      apply Set.disjoint_left.mpr
      intro y hy hyK
      exact hχ (husupport hy) hyK
    -- The squared cutoff moves to the opposite Hermitian slot without conjugation loss.
    have hpair : h.sectionPairing μ w w = h.sectionPairing μ u (R v) := by
      apply integral_congr_ae
      filter_upwards [] with y
      let : InnerProductSpace.Core ℂ (E y) := h.toCore y
      change (h.toCore y).inner ((χ y : ℂ) • (R v).val y) ((χ y : ℂ) • (R v).val y) =
        (h.toCore y).inner ((χ y : ℂ) • ((χ y : ℂ) • (R v).val y)) ((R v).val y)
      simp only [InnerProductSpace.Core.inner_smul_left,
        InnerProductSpace.Core.inner_smul_right, Complex.conj_ofReal]
    have hwzero : w = 0 := by
      apply (h.sectionPairing_self_eq_zero_iff μ w).mp
      rw [hpair, ← hPR, hP.2 u huK]
      change (∫ y, k.pairing y 0 (v.val y) ∂μ) = 0
      apply integral_eq_zero_of_ae
      filter_upwards [] with y
      let : InnerProductSpace.Core ℂ (F y) := k.toCore y
      exact InnerProductSpace.Core.inner_zero_left _
    -- Since the same bump equals one at x, the original output must vanish there.
    have hxzero := congrArg (fun s : smoothSections (n := n) (r := r) E ↦ s.val x) hwzero
    change (χ x : ℂ) • (R v).val x = 0 at hxzero
    rw [χ.eq_one, Complex.ofReal_one, one_smul] at hxzero
    exact hx hxzero
  · intro v hv
    -- Disjoint supports annihilate the actual pointwise integrand for every output of P.
    apply (h.sectionPairing_self_eq_zero_iff μ (R v)).mp
    rw [← hPR]
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    let : InnerProductSpace.Core ℂ (F x) := k.toCore x
    by_cases hx : (P (R v)).val x = 0
    · rw [hx]
      exact InnerProductSpace.Core.inner_zero_left _
    · have hxK : x ∈ K := hP.1 (R v) (subset_closure hx)
      have hvzero : v.val x = 0 := by
        by_contra hvx
        exact Set.disjoint_left.mp hv (subset_closure hvx) hxK
      rw [hvzero]
      exact InnerProductSpace.Core.inner_zero_right _

end AtiyahSinger
