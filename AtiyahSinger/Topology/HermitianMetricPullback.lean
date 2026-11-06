/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric

/-!
# Pullback of an explicit continuous Hermitian metric

Public module ID: M1888.

The fiber form at x is the original form at f(x), on exactly the original fiber
vectors. Joint continuity uses the original induced pullback topology and the
same-base double-bundle topology. No norm, new fiber topology, or chosen metric
is installed. The original local finite-rank bundle structure pulls back along f.
No properness, local compactness or paracompactness is required.

This is the standard pullback of the Hermitian form of Karoubi I.8 and
Husemoller III.9, used in the naturality of the specified Thom construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle

attribute [local instance] sumTopology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- Pull back the original Hermitian form by evaluation at the actual image base point. -/
def pullback (h : ContinuousHermitianMetric E) (f : C(X, Y)) :
    ContinuousHermitianMetric ((f : X → Y) *ᵖ E) where
  toCore x := h.toCore (f x)
  continuous_pairing := by
    -- Both original vectors lift continuously from the same pulled-back fiber.
    have hpair : Continuous
        (fun z : TotalSpace Unit (((f : X → Y) *ᵖ E) ×ᵇ ((f : X → Y) *ᵖ E)) ↦
          (⟨f z.proj, z.snd⟩ : TotalSpace Unit (E ×ᵇ E))) := by
      apply continuous_induced_rng.mpr
      exact ((_root_.Pullback.continuous_lift Unit E f).comp
        (continuous_sum_fst (E := (f : X → Y) *ᵖ E) (F := (f : X → Y) *ᵖ E))).prodMk
          ((_root_.Pullback.continuous_lift Unit E f).comp
            (continuous_sum_snd (E := (f : X → Y) *ᵖ E) (F := (f : X → Y) *ᵖ E)))
    -- Evaluate the same original jointly continuous pairing on this actual pair.
    exact h.continuous_pairing.comp hpair
  isFiniteRank := by
    let := h.isFiniteRank
    exact isFiniteRank_pullback f

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
