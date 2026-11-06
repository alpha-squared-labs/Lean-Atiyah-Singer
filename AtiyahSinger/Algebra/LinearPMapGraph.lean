/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Graph of an injectively parametrized partial linear map

Public module ID: M0038.

This implementation lemma identifies the original partial-map graph with the
range of its domain and value parametrizations. It is used for the four smooth
factor cores of a graded tensor operator, whose source and target universes can
differ.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The graph retains the same injective domain parametrization and linear output. -/
theorem linearPMap_graph_of_injective_parametrization {R S H K : Type*} [Ring R]
    [AddCommGroup S] [Module R S]
    [AddCommGroup H] [Module R H] [AddCommGroup K] [Module R K]
    (i : S →ₗ[R] H) (hi : Function.Injective i) (p : S →ₗ[R] K) :
    ({ domain := i.range
       toFun := p.comp (LinearEquiv.ofInjective i hi).symm.toLinearMap } : H →ₗ.[R] K).graph =
      (i.prod p).range := by
  let e := LinearEquiv.ofInjective i hi
  let D : H →ₗ.[R] K := { domain := i.range, toFun := p.comp e.symm.toLinearMap }
  change D.graph = (i.prod p).range
  apply Submodule.ext
  intro z
  constructor
  · intro hz
    obtain ⟨v, rfl⟩ := D.mem_graph_iff'.mp hz
    refine ⟨e.symm v, ?_⟩
    apply Prod.ext
    · exact congrArg Subtype.val (e.apply_symm_apply v)
    · rfl
  · rintro ⟨v, rfl⟩
    apply D.mem_graph_iff.mpr
    refine ⟨e v, rfl, ?_⟩
    exact congrArg p (e.symm_apply_apply v)

end AtiyahSinger
