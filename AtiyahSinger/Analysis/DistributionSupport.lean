/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Distributional support in Euclidean space

Public module ID: M2280.

The standard support bound is containment of the actual distributional support,
including for nonclosed bounding sets. For closed bounds it agrees with vanishing
on compact smooth tests supported away from the bound.

Source: Taylor, Pseudodifferential Operators, I.1, Definition 1.3, printed p.12.
The proof uses the actual mathlib support and a subordinate smooth partition of unity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff Manifold SchwartzMap Topology

variable {n r : ℕ}

/-- The actual distributional support is contained in the specified set. -/
def IsSupportedIn
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Distribution.dsupport u ⊆ K

/-- A supported distribution vanishes on every disjoint compact smooth test. -/
theorem IsSupportedIn.apply_eq_zero
    {u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hu : IsSupportedIn u K)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hφ : HasCompactSupport φ)
    (hφK : Disjoint (tsupport φ) K) : u φ = 0 := by
  /- Every point of the compact test support has a neighborhood where u vanishes.
  A subordinate partition decomposes the same test into finitely many such pieces;
  linearity then recombines their zero pairings. -/
  classical
  have local_vanishing (x : tsupport φ) :
      ∃ U : Set (EuclideanSpace ℝ (Fin n)),
        Distribution.IsVanishingOn u U ∧ IsOpen U ∧ x.1 ∈ U := by
    apply (Distribution.notMem_dsupport_iff (f := u) x.1).mp
    intro hx
    exact Set.disjoint_left.mp hφK x.2 (hu hx)
  choose U huU hU hxU using local_vanishing
  have hcover : tsupport φ ⊆ ⋃ i : tsupport φ, U i := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (isClosed_tsupport φ) U hU hcover
  have hfinite :
      {i : tsupport φ | (Function.support (ρ i) ∩ tsupport φ).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hφ
  let S : Finset (tsupport φ) := hfinite.toFinset
  let ψ (i : tsupport φ) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (hφ.smul_left (f := fun x ↦ ρ i x)).toSchwartzMap
      ((ρ i).contMDiff.contDiff.smul (φ.smooth ⊤))
  have hψU (i : tsupport φ) : tsupport (ψ i) ⊆ U i :=
    (tsupport_smul_subset_left (fun x ↦ ρ i x) φ).trans (hρ i)
  have hdecomp : φ = ∑ i ∈ S, ψ i := by
    ext x
    by_cases hx : φ x = 0
    · simp [ψ, hx]
    have hxφ : x ∈ tsupport φ := subset_tsupport φ hx
    have hsum : ∑ i ∈ S, ρ i x = 1 := by
      apply ρ.sum_finsupport' x hxφ
      intro i hi
      have hiρ : x ∈ Function.support (ρ i) := by
        simpa only [SmoothPartitionOfUnity.mem_finsupport, Function.mem_support] using hi
      exact hfinite.mem_toFinset.mpr ⟨x, hiρ, hxφ⟩
    simp only [sum_apply]
    change φ x = ∑ i ∈ S, ρ i x • φ x
    rw [← Finset.sum_smul, hsum, one_smul]
  rw [hdecomp, map_sum]
  exact Finset.sum_eq_zero (fun i _ ↦ huU i (ψ i) (hψU i))

/-- For a closed bounding set, compact tests characterize the standard support bound. -/
theorem isSupportedIn_iff_compact_tests
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K) :
    IsSupportedIn u K ↔
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        HasCompactSupport φ → Disjoint (tsupport φ) K → u φ = 0 := by
  /- The forward implication needs no closedness. Conversely, each point outside
  the closed bound has a bounded open ball in its complement. Tests supported
  inside that ball are compactly supported, so u vanishes on the ball. -/
  constructor
  · intro hu φ hφ hφK
    exact hu.apply_eq_zero φ hφ hφK
  intro htests x hx
  by_contra hxK
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hK.isOpen_compl.mem_nhds hxK)
  apply ((Distribution.notMem_dsupport_iff (f := u) x).mpr ?_) hx
  refine ⟨Metric.ball x ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε⟩
  intro φ hφ
  apply htests φ
  · exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport φ)
      (Metric.isBounded_ball.subset hφ)
  · exact Set.disjoint_left.mpr (fun y hy hyK ↦ hball (hφ hy) hyK)

end AtiyahSinger
