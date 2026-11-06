/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FredholmPairFormalAdjoint
public import AtiyahSinger.Analysis.SemiFredholmApproximation

/-!
# Formal-adjoint duality from paired Fredholm approximations

Public module ID: M0645.

On fixed complete domains, a formally paired pair with closed ranges and finite
kernels inherits Fredholmness and opposite indices from norm approximations.
The actual domain inclusions then identify each kernel with the opposite
cokernel. Local constancy is applied only after Fredholmness of both limits
has been established.

This is the functional analytic step for the original associated graded
operator and its signed transpose. The geometric domain estimates, the
approximating operators and their index relation remain explicit inputs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter
open scoped Topology

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Paired norm approximations give duality through the original domain inclusions. -/
theorem exists_ker_coker_equiv_of_formalAdjoint_of_tendsto
    (T : E →L[ℂ] Y) (S : F →L[ℂ] X) (i : E →ₗ[ℂ] X) (j : F →ₗ[ℂ] Y)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hpair : ∀ u v, inner ℂ (T u) (j v) = inner ℂ (i u) (S v))
    (hTrange : IsClosed (T.range : Set Y)) (hSrange : IsClosed (S.range : Set X))
    (hTker : FiniteDimensional ℂ T.ker) (hSker : FiniteDimensional ℂ S.ker)
    {ι : Type*} (l : Filter ι) [l.NeBot]
    (Ts : ι → E →L[ℂ] Y) (Ss : ι → F →L[ℂ] X)
    (hTs : Tendsto Ts l (𝓝 T)) (hSs : Tendsto Ss l (𝓝 S))
    (hFredholm : ∀ᶠ a in l, (Ts a).IsFredholm ∧ (Ss a).IsFredholm)
    (hindex : ∀ᶠ a in l, (Ts a).index + (Ss a).index = 0) :
    T.IsFredholm ∧ S.IsFredholm ∧ T.index + S.index = 0 ∧
      ∃ e : T.ker ≃ₗ[ℂ] (X ⧸ S.range),
        (∀ u : T.ker, e u = S.range.mkQ (i u.val)) ∧
        ∃ f : S.ker ≃ₗ[ℂ] (Y ⧸ T.range),
          ∀ v : S.ker, f v = T.range.mkQ (j v.val) := by
  -- The supplied closed-range and finite-kernel bounds establish Fredholmness before index stability.
  have hT : T.IsFredholm :=
    isFredholm_of_closed_range_of_finite_ker_of_mem_closure T hTrange hTker
      (mem_closure_of_tendsto hTs (hFredholm.mono fun _ h ↦ h.1))
  have hS : S.IsFredholm :=
    isFredholm_of_closed_range_of_finite_ker_of_mem_closure S hSrange hSker
      (mem_closure_of_tendsto hSs (hFredholm.mono fun _ h ↦ h.2))
  -- Both eventual equalities use the same parameter filter and the same fixed domains.
  have hTindex : ∀ᶠ a in l, (Ts a).index = T.index :=
    hTs.eventually hT.eventually_nhds_index_eq
  have hSindex : ∀ᶠ a in l, (Ss a).index = S.index :=
    hSs.eventually hS.eventually_nhds_index_eq
  have hlimit : T.index + S.index = 0 := by
    obtain ⟨a, hTa, hSa, ha⟩ := (hTindex.and (hSindex.and hindex)).exists
    simpa only [hTa, hSa] using ha
  -- The supplied pairing gives the actual quotient maps, not just matching dimensions.
  exact ⟨hT, hS, hlimit,
    exists_ker_coker_equiv_of_formalAdjoint_of_index_add_eq_zero
      T S i j hi hj hpair hT hS hlimit⟩

end AtiyahSinger
