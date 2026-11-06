/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Ring

/-!
# Additivity of the index under direct sum

Public module ID: M0756.

The algebraic fact used both for identity stabilization and for
additivity in SG III.13, p.247, (13.8). Only the kernels and cokernels must be
finite-dimensional; the original spaces may be infinite-dimensional. This
does not assert additivity of the totalized index without these hypotheses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {𝕜 E F G H : Type*} [DivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [AddCommGroup H] [Module 𝕜 H]

/-- The index of a direct sum of maps with finite kernel and cokernel is additive. -/
theorem index_prodMap (P : E →ₗ[𝕜] F) (Q : G →ₗ[𝕜] H)
    [FiniteDimensional 𝕜 P.ker] [FiniteDimensional 𝕜 (F ⧸ P.range)]
    [FiniteDimensional 𝕜 Q.ker] [FiniteDimensional 𝕜 (H ⧸ Q.range)] :
    (P.prodMap Q).index = P.index + Q.index := by
  -- The product equivalence expresses the kernel dimension as the sum of two dimensions.
  have hker : Module.finrank 𝕜 (P.prodMap Q).ker =
      Module.finrank 𝕜 P.ker + Module.finrank 𝕜 Q.ker := by
    rw [LinearMap.ker_prodMap]
    exact (Submodule.prodEquiv P.ker Q.ker).finrank_eq.trans Module.finrank_prod
  -- The product quotient map is surjective, with kernel equal to the product operator's range.
  let quotientMap : F × H →ₗ[𝕜] (F ⧸ P.range) × (H ⧸ Q.range) :=
    P.range.mkQ.prodMap Q.range.mkQ
  have hsurj : Function.Surjective quotientMap := by
    rintro ⟨y, z⟩
    obtain ⟨x, rfl⟩ := P.range.mkQ_surjective y
    obtain ⟨w, rfl⟩ := Q.range.mkQ_surjective z
    exact ⟨(x, w), rfl⟩
  have hquotientKer : quotientMap.ker = (P.prodMap Q).range := by
    simp [quotientMap]
  have hcoker : Module.finrank 𝕜 ((F × H) ⧸ (P.prodMap Q).range) =
      Module.finrank 𝕜 (F ⧸ P.range) + Module.finrank 𝕜 (H ⧸ Q.range) := by
    have hdim := (quotientMap.quotKerEquivOfSurjective hsurj).finrank_eq
    rw [hquotientKer, Module.finrank_prod] at hdim
    exact hdim
  -- Substitute the dimension sums into the index definition and rearrange in the integers.
  simp only [LinearMap.index_eq_finrank_sub, hker, hcoker, Nat.cast_add]
  ring

end AtiyahSinger
