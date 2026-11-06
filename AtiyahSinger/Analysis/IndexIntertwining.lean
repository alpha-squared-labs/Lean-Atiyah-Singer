/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Index invariance under specified linear equivalences

Public module ID: M0758.

The exact intertwining square identifies both the actual kernel and the
actual quotient cokernel. No finiteness assumptions are needed to compare
the algebraic index. This is used for native atlas and clopen section models.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Intertwining by the specified source and target equivalences preserves the algebraic index. -/
theorem index_eq_of_linearEquiv {𝕜 E F G H : Type*} [DivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    [AddCommGroup G] [Module 𝕜 G] [AddCommGroup H] [Module 𝕜 H]
    (P : E →ₗ[𝕜] F) (Q : G →ₗ[𝕜] H) (S : E ≃ₗ[𝕜] G) (T : F ≃ₗ[𝕜] H)
    (h : ∀ u, Q (S u) = T (P u)) : P.index = Q.index := by
  let e : P.ker ≃ₗ[𝕜] Q.ker := {
    toFun u := ⟨S u.val, by rw [LinearMap.mem_ker, h, u.property, map_zero]⟩
    invFun u := ⟨S.symm u.val, by
      apply T.injective
      rw [map_zero, ← h, S.apply_symm_apply]
      exact u.property⟩
    left_inv u := Subtype.ext (S.symm_apply_apply u.val)
    right_inv u := Subtype.ext (S.apply_symm_apply u.val)
    map_add' u v := Subtype.ext (S.map_add u.val v.val)
    map_smul' z u := Subtype.ext (S.map_smul z u.val) }
  -- The same target equivalence sends precisely the first range onto the second.
  have hrange : P.range.map T.toLinearMap = Q.range := by
    ext v
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨S u, h u⟩
    · rintro ⟨u, rfl⟩
      exact ⟨P (S.symm u), ⟨S.symm u, rfl⟩,
        (h (S.symm u)).symm.trans (congrArg Q (S.apply_symm_apply u))⟩
  let c := Submodule.Quotient.equiv P.range Q.range T hrange
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    e.finrank_eq, c.finrank_eq]

end AtiyahSinger
