/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedGraphRepresentation

/-!
# The original complete domain from a core graph estimate

Public module ID: M0334.

A reverse estimate on the specified dense smooth core extends to its original
complete domain. The paired input and output map has closed range, so this range
is exactly the closure of the original core graph. The resulting continuous
linear equivalence retains both specified maps and the Hilbert graph norm.

This is the standard completion step needed after the geometric joint-domain
estimate; neither a new domain nor a replacement operator is chosen.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E F X S : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [AddCommGroup S] [Module ℂ S]

/-- The reverse core estimate identifies the given complete domain with the original graph. -/
theorem LinearPMap.exists_graphDomainEquiv_of_core_bound
    (D : E →ₗ.[ℂ] F) (hD : D.IsClosed)
    (J : X →L[ℂ] E) (T : X →L[ℂ] F) (hJ : Function.Injective J)
    (i : S →ₗ[ℂ] X) (hi : DenseRange i)
    (hgraph : D.graph = ((J.prod T).toLinearMap.comp i).range.topologicalClosure)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s : S, ‖i s‖ ≤ C * (‖J (i s)‖ + ‖T (i s)‖)) :
    let Γ := D.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
    ∃ Φ : X ≃L[ℂ] Γ, ∀ x, (Φ x).val = WithLp.toLp 2 (J x, T x) := by
  let A := J.prod T
  let core := (A.toLinearMap.comp i).range
  -- Continuity extends the same reverse bound from the specified dense core.
  have hclosed : IsClosed {x : X | ‖x‖ ≤ C * (‖J x‖ + ‖T x‖)} :=
    isClosed_le continuous_norm (by fun_prop)
  have hbound' (x : X) : ‖x‖ ≤ C * (‖J x‖ + ‖T x‖) := by
    apply closure_minimal (t := {x : X | ‖x‖ ≤ C * (‖J x‖ + ‖T x‖)}) ?_ hclosed (hi x)
    rintro _ ⟨s, rfl⟩
    exact hbound s
  -- The paired map is bounded below for the original complete domain norm.
  have hanti : AntilipschitzWith (Real.toNNReal (2 * C)) A := by
    apply A.antilipschitz_of_bound
    intro x
    rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hC)]
    change ‖x‖ ≤ (2 * C) * max ‖J x‖ ‖T x‖
    calc
      ‖x‖ ≤ C * (‖J x‖ + ‖T x‖) := hbound' x
      _ ≤ C * (max ‖J x‖ ‖T x‖ + max ‖J x‖ ‖T x‖) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_max_left _ _) (le_max_right _ _)) hC
      _ = _ := by ring
  have hArange : IsClosed (A.range : Set (E × F)) :=
    hanti.isClosed_range A.uniformContinuous
  have hcore : core.topologicalClosure = A.range := by
    apply le_antisymm
    · apply Submodule.topologicalClosure_minimal core ?_ hArange
      rintro _ ⟨s, rfl⟩
      exact ⟨i s, rfl⟩
    · rintro _ ⟨x, rfl⟩
      have hpre : IsClosed (A ⁻¹' (core.topologicalClosure : Set (E × F))) :=
        core.isClosed_topologicalClosure.preimage A.continuous
      apply closure_minimal (t := A ⁻¹' (core.topologicalClosure : Set (E × F))) ?_ hpre (hi x)
      rintro _ ⟨s, rfl⟩
      exact core.le_topologicalClosure ⟨s, rfl⟩
  -- The original closed-graph equivalence now applies to exactly these two maps.
  exact LinearPMap.exists_graphDomainEquiv D hD J T hJ (hgraph.trans hcore)

end AtiyahSinger
