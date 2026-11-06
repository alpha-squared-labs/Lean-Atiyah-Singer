/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ClopenCohomology
public import AtiyahSinger.Topology.EquivariantRankStrata

/-!
# Cohomology on the actual rank strata

Public module ID: M2031.

The original fiber-rank function is locally constant. Its actual rank-stratum
inclusions identify singular cohomology with the unrestricted product over all
natural ranks. This is the comparison used both to assemble characteristic
classes and to detect equality on the original locally varying-rank base.
There is no compactness, separation, connectedness or uniform rank hypothesis.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u v

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- Original rank-stratum pullbacks identify cohomology with the product of all rank pieces. -/
theorem singularCohomologyPullback_rankStrata_bijective (n : ℕ) :
    Function.Bijective (fun c : singularCohomology R X n ↦ fun r : ℕ ↦
      singularCohomologyPullback R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum E r, X)) n c) := by
  -- The general comparison uses exactly these fibers and their original inclusions.
  exact singularCohomologyPullback_fibers_bijective R
    (fun x : X ↦ Module.finrank ℂ (E x)) (isLocallyConstant_finrank E) n

end AtiyahSinger.ComplexBundle
