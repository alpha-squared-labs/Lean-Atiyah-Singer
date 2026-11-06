/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Fredholm

/-!
# Kernel-cokernel duality for a Fredholm pair

Public module ID: M0646.

For two Fredholm operators with opposite indices, injections from each kernel
into the other operator's cokernel must both be isomorphisms. The resulting
equivalences retain the supplied maps, so they preserve their geometric meaning.

This elementary Fredholm duality criterion is used after fixed-domain
approximations have established both Fredholm properties and the index relation.
It does not infer maximal-adjoint regularity from minimal graph closure.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Opposite Fredholm indices make the two specified kernel-cokernel injections equivalences. -/
theorem exists_ker_coker_equiv_of_index_add_eq_zero
    (T : E →L[ℂ] F) (S : G →L[ℂ] H) (hT : T.IsFredholm) (hS : S.IsFredholm)
    (e : T.ker →ₗ[ℂ] (H ⧸ S.range)) (f : S.ker →ₗ[ℂ] (F ⧸ T.range))
    (he : Function.Injective e) (hf : Function.Injective f)
    (hindex : T.index + S.index = 0) :
    ∃ e' : T.ker ≃ₗ[ℂ] (H ⧸ S.range), e'.toLinearMap = e ∧
      ∃ f' : S.ker ≃ₗ[ℂ] (F ⧸ T.range), f'.toLinearMap = f := by
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ S.ker := hS.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : FiniteDimensional ℂ (H ⧸ S.range) := hS.finite_coker
  -- Both defect dimensions can only decrease under the given injections.
  have heDim : Module.finrank ℂ T.ker ≤ Module.finrank ℂ (H ⧸ S.range) :=
    LinearMap.finrank_le_finrank_of_injective he
  have hfDim : Module.finrank ℂ S.ker ≤ Module.finrank ℂ (F ⧸ T.range) :=
    LinearMap.finrank_le_finrank_of_injective hf
  -- The index sum is the sum of the two nonpositive dimension defects.
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub] at hindex
  have heEq : Module.finrank ℂ T.ker = Module.finrank ℂ (H ⧸ S.range) := by
    omega
  have hfEq : Module.finrank ℂ S.ker = Module.finrank ℂ (F ⧸ T.range) := by
    omega
  -- Equal finite dimensions make these same maps surjective; no new map is chosen.
  have heSurj : Function.Surjective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heEq).mp he
  have hfSurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfEq).mp hf
  exact ⟨LinearEquiv.ofBijective e ⟨he, heSurj⟩, rfl,
    LinearEquiv.ofBijective f ⟨hf, hfSurj⟩, rfl⟩

end AtiyahSinger
