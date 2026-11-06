/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.UnitaryOperatorAverageEquivariance
public import AtiyahSinger.Analysis.EquivariantFredholmIndex

/-!
# Stability under averaged norm perturbations

Public module ID: M0471.

A sufficiently small bounded perturbation of a fixed equivariant Fredholm
operator has the same full representation index after strong Haar averaging.
The averaging and index interfaces are required to carry literally the same
specified unitary actions. This is applied on the fixed original Hilbert graph
of the geometric tensor operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory

variable {G E F : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Averaging a small perturbation preserves the full index on the fixed unitary spaces. -/
theorem exists_radius_equivariantFredholmIndex_average_eq
    (ν : Measure G) [IsProbabilityMeasure ν] [Measure.IsMulLeftInvariant ν]
    (ρ : ContRepresentation ℂ G E) (τ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hτ : Continuous (fun p : G × F ↦ τ p.1 p.2))
    (R : G →* (E ≃ₗᵢ[ℂ] E)) (S : G →* (F ≃ₗᵢ[ℂ] F))
    (hR : ∀ g x, R g x = ρ g x) (hS : ∀ g y, S g y = τ g y)
    (T₀ : E →L[ℂ] F) (hT₀g : ∀ g, T₀.comp (ρ g) = (τ g).comp T₀)
    (hT₀ : T₀.IsFredholm) :
    let A := unitaryOperatorAverage ν R S
      (hρ.congr (fun p ↦ (hR p.1 p.2).symm))
      (hτ.congr (fun p ↦ (hS p.1 p.2).symm))
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : E →L[ℂ] F, ‖T - T₀‖ < ε →
      ∃ hAg : ∀ g, (A T).comp (ρ g) = (τ g).comp (A T),
        ∃ hA : (A T).IsFredholm,
          equivariantFredholmIndex ρ τ hρ hτ (A T) hAg hA =
            equivariantFredholmIndex ρ τ hρ hτ T₀ hT₀g hT₀ := by
  let hRc := hρ.congr (fun p ↦ (hR p.1 p.2).symm)
  let hSc := hτ.congr (fun p ↦ (hS p.1 p.2).symm)
  let A := unitaryOperatorAverage ν R S hRc hSc
  have hρu (g : G) : Isometry (ρ g) := by
    simpa only [funext (hR g)] using (R g).isometry
  have hτu (g : G) : Isometry (τ g) := by
    simpa only [funext (hS g)] using (S g).isometry
  obtain ⟨ε, hε, hstable⟩ :=
    exists_radius_equivariantFredholmIndex_eq ρ τ hρ hτ hρu hτu T₀ hT₀g hT₀
  -- The original equivariant operator is fixed, so contraction controls the same difference.
  have hfixed : A T₀ = T₀ := by
    apply unitaryOperatorAverage_eq_self
    intro g x
    rw [hR, hS]
    exact DFunLike.congr_fun (hT₀g g) x
  refine ⟨ε, hε, ?_⟩
  intro T hT
  have hclose : ‖A T - T₀‖ < ε := by
    rw [← hfixed, ← map_sub]
    exact (norm_unitaryOperatorAverage_le ν R S hRc hSc (T - T₀)).trans_lt hT
  have hAg (g : G) : (A T).comp (ρ g) = (τ g).comp (A T) := by
    apply ContinuousLinearMap.ext
    intro x
    change A T (ρ g x) = τ g (A T x)
    rw [← hR, ← hS]
    exact unitaryOperatorAverage_intertwines ν R S hRc hSc T g x
  -- Stability is the existing full representation theorem on these same fixed spaces.
  exact ⟨hAg, hstable (A T) hclose hAg⟩

end AtiyahSinger
