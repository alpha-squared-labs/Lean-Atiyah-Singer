/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.EquivariantVectorBundle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Invariant Hermitian metrics on equivariant complex bundles

Public module ID: M1786.

The pairing is the actual normalized Haar integral of the original metric after
the specified action on its moving fibers. It defines a continuous positive
Hermitian metric on the same original bundle and is invariant under that action.
Continuity is joint on the original same-base double total space. No norm,
inner-product instance or new topology is installed on any fiber.

For a supplied continuous metric the averaging construction needs only a compact
Hausdorff Borel topological group and a jointly continuous complex-linear action.
The supplied metric certifies local finite rank on the original bundle. Averaging
requires no further rank restriction, and the base need not be compact, locally
compact, Hausdorff or paracompact. The existence theorem separately uses a
paracompact Hausdorff base and the original local finite-rank bundle structure.

This is the moving-base Hermitian averaging argument used in SG III.9,
pp.211--214, combined with the ordinary metric existence theorem of Husemoller
III.9.5 and Karoubi I.8.7. The first slot is conjugate-linear as in mathlib.
Right invariance of normalized Haar measure is essential for the displayed
action convention. The metric certificate, invariance, and existence are proved
below. The grouped certificate is part of this one metric construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle MeasureTheory TopologicalSpace
open scoped ComplexConjugate

attribute [local instance] sumTopology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {X : Type*} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

namespace ContinuousHermitianMetric

variable (h : ContinuousHermitianMetric E) (σ : EquivariantStructure G E)

/-- Average the specified metric along the original moving-fiber action, with Haar mass one. -/
def averagedPairing (x : X) (u v : E x) : ℂ :=
  ∫ g : G, (h.toCore (g • x)).inner (σ.linearMap g x u) (σ.linearMap g x v)
    ∂(Measure.haarMeasure (⊤ : PositiveCompacts G))

set_option linter.unusedSectionVars false in
-- Keep the original compact Hausdorff group parameter in this public certificate.
/-- The actual averaged pairing is positive Hermitian and jointly continuous
on the double bundle. -/
theorem averagedPairing_properties :
    (∀ x : X,
      (∀ u v : E x, conj (h.averagedPairing σ x v u) = h.averagedPairing σ x u v) ∧
      (∀ u : E x, 0 ≤ (h.averagedPairing σ x u u).re) ∧
      (∀ u v w : E x, h.averagedPairing σ x (u + v) w =
        h.averagedPairing σ x u w + h.averagedPairing σ x v w) ∧
      (∀ (u v : E x) (c : ℂ), h.averagedPairing σ x (c • u) v =
        conj c * h.averagedPairing σ x u v) ∧
      (∀ u : E x, h.averagedPairing σ x u u = 0 → u = 0)) ∧
    Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      h.averagedPairing σ z.proj z.snd.1 z.snd.2) := by
  /- Stage 1: use the direct-sum action σ.sum σ on the original double total
  space. Composing its joint continuity with h.continuous_pairing gives joint
  continuity of the scalar integrand in the group element and both vectors.
  At any fixed double vector, compactness of G gives integrability against the
  finite normalized Haar measure. The totalized integral is never used here
  without this integrability justification.
  Stage 2: integrate the original conjugate symmetry, additivity and scalar law.
  Pointwise nonnegative real diagonal values yield a nonnegative real integral.
  If u is nonzero, the action by the identity identifies its diagonal with the
  strictly positive original one. Continuity makes it bounded below by a
  positive number on an open identity neighborhood, whose Haar measure is
  positive. The diagonal integral therefore cannot vanish. This also covers
  zero-dimensional fibers without an extra positive-rank assumption.
  Stage 3: for each fixed double vector z, continuity of the integrand on
  G × {z}, compactness of G and a finite-cover argument give a neighborhood of
  z on which the scalar integrands are uniformly close. Integration against
  Haar mass one gives continuity of the displayed pairing on the original
  double topology. This compact-parameter argument does not require local
  compactness, paracompactness or a countable neighborhood basis of the base,
  and does not install norms on the original fibers. -/
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let τ := σ.sum σ
  let B (z : TotalSpace Unit (E ×ᵇ E)) : ℂ :=
    (h.toCore z.proj).inner z.snd.1 z.snd.2
  let Φ (p : G × TotalSpace Unit (E ×ᵇ E)) : ℂ :=
    (h.toCore (p.1 • p.2.proj)).inner
      (σ.linearMap p.1 p.2.proj p.2.snd.1) (σ.linearMap p.1 p.2.proj p.2.snd.2)
  -- The original sum action gives joint continuity without assumptions on the base topology.
  have hΦ : Continuous Φ := h.continuous_pairing.comp τ.continuous_action
  have hcoeff (x : X) (u v : E x) :
      Continuous (fun g : G ↦ Φ (g, ⟨x, (u, v)⟩)) :=
    hΦ.comp (continuous_id.prodMk continuous_const)
  have hint (x : X) (u v : E x) :
      Integrable (fun g : G ↦ Φ (g, ⟨x, (u, v)⟩)) μ :=
    (hcoeff x u v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨?_, ?_⟩
  · intro x
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u v
      -- Integrate the Hermitian identity of the original explicit metric.
      unfold averagedPairing
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards with g
      exact (h.toCore (g • x)).conj_inner_symm _ _
    · intro u
      change 0 ≤ RCLike.re (∫ g : G, Φ (g, ⟨x, (u, u)⟩) ∂μ)
      rw [← integral_re (hint x u u)]
      exact integral_nonneg (fun g ↦ (h.toCore (g • x)).re_inner_nonneg _)
    · intro u v w
      unfold averagedPairing
      simp only [map_add, (h.toCore _).add_left]
      exact integral_add (hint x u w) (hint x v w)
    · intro u v c
      unfold averagedPairing
      simp only [map_smul, (h.toCore _).smul_left]
      exact integral_const_mul (conj c) _
    · intro u hu
      -- A continuous nonnegative function with zero integral vanishes on the whole group.
      have hreal := Complex.continuous_re.comp (hcoeff x u u)
      have hz : (∫ g : G, RCLike.re (Φ (g, ⟨x, (u, u)⟩)) ∂μ) = 0 := by
        rw [integral_re (hint x u u)]
        exact congrArg Complex.re hu
      have hae : (fun g : G ↦ RCLike.re (Φ (g, ⟨x, (u, u)⟩))) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg
          (fun g ↦ (h.toCore (g • x)).re_inner_nonneg _)
          (hreal.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hz
      have hall := (hreal.ae_eq_iff_eq μ continuous_const).mp hae
      -- The original total-space identity action transports the identity coefficient back to x.
      have hone : (Φ ((1 : G), ⟨x, (u, u)⟩)).re = 0 := congrFun hall 1
      have hidentity : (Φ ((1 : G), ⟨x, (u, u)⟩)).re = ((h.toCore x).inner u u).re :=
        congrArg (fun z ↦ (B z).re) (τ.one_map x (u, u))
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      exact (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp (hidentity.symm.trans hone)
  · -- A compact integration parameter gives uniform control for every original double vector.
    -- The compact-support integral theorem requires no regularity of this parameter space.
    change Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ ∫ g : G, Φ (g, z) ∂μ)
    apply continuousOn_univ.mp
    exact continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
      (hΦ.comp continuous_swap).continuousOn (by simp)

/-- The invariant averaged metric on the original fibers with their original total topology. -/
def average : ContinuousHermitianMetric E where
  toCore x :=
    { inner := h.averagedPairing σ x
      conj_inner_symm := ((h.averagedPairing_properties σ).1 x).1
      re_inner_nonneg := ((h.averagedPairing_properties σ).1 x).2.1
      add_left := ((h.averagedPairing_properties σ).1 x).2.2.1
      smul_left := ((h.averagedPairing_properties σ).1 x).2.2.2.1
      definite := ((h.averagedPairing_properties σ).1 x).2.2.2.2 }
  continuous_pairing := (h.averagedPairing_properties σ).2
  isFiniteRank := h.isFiniteRank

/-- The constructed average preserves the Hermitian pairing under the specified moving action. -/
theorem average_invariant (g : G) (x : X) (u v : E x) :
    ((h.average σ).toCore (g • x)).inner (σ.linearMap g x u) (σ.linearMap g x v) =
      ((h.average σ).toCore x).inner u v := by
  /- Stage 1: unfold only the actual averaged pairings. The total-space
  composition law identifies the integrand obtained by first acting by g with
  the original integrand at k*g, including its moving base point. Equality is
  transported along this actual action law; no independent fiber choices occur.
  Stage 2: normalized Haar measure on a compact group is right invariant.
  Indeed its right translate remains left invariant and has the same total
  mass one, so Haar uniqueness identifies it with the original measure.
  Change variables by k ↦ k*g. All scalar integrands are continuous on compact
  G and hence integrable. Left invariance alone would not justify this change
  of variables for the formula used here. -/
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  -- The actual Haar normalization has mass one, so its right translates coincide by uniqueness.
  let : IsProbabilityMeasure μ := ⟨by
    change Measure.haarMeasure (⊤ : PositiveCompacts G) Set.univ = 1
    exact Measure.haarMeasure_self⟩
  let : μ.IsMulRightInvariant := ⟨fun a ↦
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure (μ.map (· * a)) μ⟩
  let B (z : TotalSpace Unit (E ×ᵇ E)) : ℂ :=
    (h.toCore z.proj).inner z.snd.1 z.snd.2
  have hmul (a : G) :
      (h.toCore (a • (g • x))).inner
          (σ.linearMap a (g • x) (σ.linearMap g x u))
          (σ.linearMap a (g • x) (σ.linearMap g x v)) =
        (h.toCore ((a * g) • x)).inner (σ.linearMap (a * g) x u)
          (σ.linearMap (a * g) x v) :=
    congrArg B ((σ.sum σ).mul_map a g x (u, v)).symm
  -- This total-space action identity includes the actual moving-base transport.
  change (∫ a : G, (h.toCore (a • (g • x))).inner
      (σ.linearMap a (g • x) (σ.linearMap g x u))
      (σ.linearMap a (g • x) (σ.linearMap g x v)) ∂μ) =
    ∫ a : G, (h.toCore (a • x)).inner (σ.linearMap a x u) (σ.linearMap a x v) ∂μ
  simp_rw [hmul]
  exact integral_mul_right_eq_self (μ := μ)
    (fun a : G ↦ (h.toCore (a • x)).inner (σ.linearMap a x u) (σ.linearMap a x v)) g

end ContinuousHermitianMetric

/-- A finite-rank equivariant bundle over a paracompact Hausdorff base has an invariant metric. -/
theorem exists_invariant_continuousHermitianMetric
    [T2Space X] [ParacompactSpace X] [IsFiniteRank E]
    (σ : EquivariantStructure G E) :
    ∃ h : ContinuousHermitianMetric E, ∀ (g : G) (x : X) (u v : E x),
      (h.toCore (g • x)).inner (σ.linearMap g x u) (σ.linearMap g x v) =
        (h.toCore x).inner u v := by
  /- Stage 1: use nonempty_continuousHermitianMetric on the original locally
  finite-rank bundle over its paracompact Hausdorff base. This is the only step
  using the base hypotheses to obtain the supplied finite-rank metric.
  No compactness of the base is needed.
  Stage 2: average that specified metric by the given compact-group action.
  The actual construction has the original fibers and topology, and
  average_invariant supplies the stated equality for all group elements and
  fiber vectors. Locally varying rank, zero-rank fibers and an empty base are
  all admitted by the ordinary metric-existence theorem and by averaging. -/
  -- Ordinary existence supplies the metric and its original local finite-rank context.
  obtain ⟨h⟩ := nonempty_continuousHermitianMetric E
  exact ⟨h.average σ, fun g x u v ↦ h.average_invariant σ g x u v⟩

end AtiyahSinger.ComplexBundle
