/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.FiniteBundle

/-!
# A universe-compatible presentation of the original finite-rank bundle

Public module ID: M1572.

The existing singular-cohomology characteristic construction uses fibers in
the base universe. The standard small-bundle isomorphism followed by ULift
provides such a presentation without changing the base or its cohomology.
The total topology is transported along the displayed fiberwise equivalence;
the metric is uniquely the pullback of the original metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u v

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- A fiber presentation in exactly the base universe, with no global rank bound. -/
abbrev CohomologyModel (x : X) : Type u := ULift.{u} ((smallBundle E).Fiber x)

/-- The specified complex-linear identification with the original fiber. -/
def cohomologyModelLinearEquiv (x : X) : CohomologyModel E x ≃ₗ[ℂ] E x :=
  ULift.moduleEquiv.trans ((smallBundleIso E).linearEquiv x).symm

/-- The same identification on total spaces, preserving each base point. -/
def cohomologyModelTotalEquiv : TotalSpace Unit (CohomologyModel E) ≃ TotalSpace Unit E where
  toFun z := ⟨z.proj, cohomologyModelLinearEquiv E z.proj z.snd⟩
  invFun z := ⟨z.proj, (cohomologyModelLinearEquiv E z.proj).symm z.snd⟩
  left_inv z := by
    cases z
    simp
  right_inv z := by
    cases z
    simp

/-- Precisely the original total topology, transported through the specified equivalence. -/
@[reducible]
def cohomologyModelTopology : TopologicalSpace (TotalSpace Unit (CohomologyModel E)) :=
  TopologicalSpace.induced (cohomologyModelTotalEquiv E) inferInstance

attribute [local instance] cohomologyModelTopology

/-- The transported original local charts retain local finite rank. -/
theorem isFiniteRank_cohomologyModel : IsFiniteRank (CohomologyModel E) := by
  /- Compose the original finite linear charts with cohomologyModelLinearEquiv.
  Their total maps are continuous in both directions by the transported
  topology. Keep the original open domains and their original local ranks;
  the ULift changes only universe, not any vector or base point. -/
  -- Reverse the specified total homeomorphism, retaining every original chart domain.
  let i : Iso (CohomologyModel E) E :=
    { linearEquiv := cohomologyModelLinearEquiv E
      continuous_total :=
        ((cohomologyModelTotalEquiv E).toHomeomorphOfIsInducing ⟨rfl⟩).continuous
      continuous_symm :=
        ((cohomologyModelTotalEquiv E).toHomeomorphOfIsInducing ⟨rfl⟩).symm.continuous }
  exact i.symm.isFiniteRank

/-- The specified model identifies the original topology in both directions. -/
def cohomologyModelIso : Iso (CohomologyModel E) E where
  linearEquiv := cohomologyModelLinearEquiv E
  continuous_total :=
    ((cohomologyModelTotalEquiv E).toHomeomorphOfIsInducing ⟨rfl⟩).continuous
  continuous_symm :=
    ((cohomologyModelTotalEquiv E).toHomeomorphOfIsInducing ⟨rfl⟩).symm.continuous

/-- The model metric is uniquely specified by the original form on the original vectors. -/
theorem existsUnique_cohomologyModelMetric (h : ContinuousHermitianMetric E) :
    ∃! g : ContinuousHermitianMetric (CohomologyModel E),
      ∀ (x : X) (a b : CohomologyModel E x),
        (g.toCore x).inner a b = (h.toCore x).inner
          (cohomologyModelLinearEquiv E x a) (cohomologyModelLinearEquiv E x b) := by
  /- Pull the Hermitian core back through the specified linear equivalence.
  Positivity and definiteness follow from its injectivity. The induced map
  on same-base doubles is continuous for precisely the transported topology,
  hence the pairing is jointly continuous. Equality of the inner fields and
  proof irrelevance give uniqueness, with no change to the original metric. -/
  let : TopologicalSpace (TotalSpace Unit (CohomologyModel E ×ᵇ CohomologyModel E)) :=
    sumTopology
  let : TopologicalSpace (TotalSpace Unit (E ×ᵇ E)) := sumTopology
  -- Pull back the given form through the original, specified fiber equivalence.
  let c (x : X) : InnerProductSpace.Core ℂ (CohomologyModel E x) :=
    { inner := fun a b ↦ (h.toCore x).inner
        (cohomologyModelLinearEquiv E x a) (cohomologyModelLinearEquiv E x b)
      conj_inner_symm a b := (h.toCore x).conj_inner_symm _ _
      re_inner_nonneg a := (h.toCore x).re_inner_nonneg _
      add_left a b d := by
        rw [map_add, (h.toCore x).add_left]
      smul_left a b z := by
        rw [map_smul, (h.toCore x).smul_left]
      definite a ha := by
        apply (cohomologyModelLinearEquiv E x).injective
        rw [map_zero]
        exact (h.toCore x).definite _ ha }
  -- The same-base double map is continuous in the two original induced topologies.
  let pair : TotalSpace Unit (CohomologyModel E ×ᵇ CohomologyModel E) →
      TotalSpace Unit (E ×ᵇ E) := fun z ↦
    ⟨z.proj, cohomologyModelLinearEquiv E z.proj z.snd.1,
      cohomologyModelLinearEquiv E z.proj z.snd.2⟩
  have hpair : Continuous pair := by
    apply continuous_induced_rng.mpr
    exact ((cohomologyModelIso E).continuous_total.comp
      (continuous_sum_fst (E := CohomologyModel E) (F := CohomologyModel E))).prodMk
      ((cohomologyModelIso E).continuous_total.comp
        (continuous_sum_snd (E := CohomologyModel E) (F := CohomologyModel E)))
  let g : ContinuousHermitianMetric (CohomologyModel E) :=
    { toCore := c
      continuous_pairing := h.continuous_pairing.comp hpair
      isFiniteRank := isFiniteRank_cohomologyModel E }
  refine ⟨g, fun _ _ _ ↦ rfl, ?_⟩
  -- The prescribed inner field determines the full form; other fields are certificates.
  intro g' hg'
  have hcore_ext (x : X) (a b : InnerProductSpace.Core ℂ (CohomologyModel E x))
      (hab : a.inner = b.inner) : a = b := by
    rcases a with ⟨⟨⟨f⟩, hs, hp, ha, hm⟩, hd⟩
    rcases b with ⟨⟨⟨f'⟩, hs', hp', ha', hm'⟩, hd'⟩
    change f = f' at hab
    cases hab
    rfl
  cases g' with
  | mk c' hc' _ =>
    have hc : c' = c := by
      funext x
      exact hcore_ext x (c' x) (c x) (funext fun a ↦ funext fun b ↦ hg' x a b)
    cases hc
    rfl

/-- The actual original Hermitian form in the universe-compatible presentation. -/
def cohomologyModelMetric (h : ContinuousHermitianMetric E) :
    ContinuousHermitianMetric (CohomologyModel E) :=
  (existsUnique_cohomologyModelMetric E h).exists.choose

end AtiyahSinger.ComplexBundle
