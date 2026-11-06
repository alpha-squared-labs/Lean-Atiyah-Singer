/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FredholmPairDuality

/-!
# Natural cokernel representatives for a formal-adjoint Fredholm pair

Public module ID: M0647.

Two operators on their fixed domains may have different domain and ambient
Hilbert norms. Their actual injective domain inclusions and formal pairing
give natural injections from each kernel into the opposite cokernel. When
both operators are Fredholm and their indices sum to zero, the same quotient
maps are equivalences. No equality of maximal and minimal domains is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- The original domain inclusions identify both opposite kernels with the actual cokernels. -/
theorem exists_ker_coker_equiv_of_formalAdjoint_of_index_add_eq_zero
    (T : E →L[ℂ] Y) (S : F →L[ℂ] X) (i : E →ₗ[ℂ] X) (j : F →ₗ[ℂ] Y)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hpair : ∀ u v, inner ℂ (T u) (j v) = inner ℂ (i u) (S v))
    (hT : T.IsFredholm) (hS : S.IsFredholm) (hindex : T.index + S.index = 0) :
    ∃ e : T.ker ≃ₗ[ℂ] (X ⧸ S.range),
      (∀ u : T.ker, e u = S.range.mkQ (i u.val)) ∧
      ∃ f : S.ker ≃ₗ[ℂ] (Y ⧸ T.range),
        ∀ v : S.ker, f v = T.range.mkQ (j v.val) := by
  let e := S.range.mkQ.comp (i.comp T.ker.subtype)
  let f := T.range.mkQ.comp (j.comp S.ker.subtype)
  -- A kernel vector lying in the opposite range has zero squared ambient norm.
  have he : Function.Injective e := by
    apply (injective_iff_map_eq_zero e).mpr
    intro u hu
    obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero S.range).mp hu
    change S v = i u.val at hv
    have hzero : T u.val = 0 := u.property
    have hnorm : inner ℂ (i u.val) (i u.val) = 0 := by
      calc
        _ = inner ℂ (i u.val) (S v) := congrArg (inner ℂ (i u.val)) hv.symm
        _ = inner ℂ (T u.val) (j v) := (hpair u.val v).symm
        _ = 0 := by rw [hzero, inner_zero_left]
    apply Subtype.ext
    apply hi
    exact (inner_self_eq_zero.mp hnorm).trans i.map_zero.symm
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero T.range).mp hv
    change T u = j v.val at hu
    have hzero : S v.val = 0 := v.property
    have hnorm : inner ℂ (j v.val) (j v.val) = 0 := by
      calc
        _ = inner ℂ (T u) (j v.val) := congrArg (fun y ↦ inner ℂ y (j v.val)) hu.symm
        _ = inner ℂ (i u) (S v.val) := hpair u v.val
        _ = 0 := by rw [hzero, inner_zero_right]
    apply Subtype.ext
    apply hj
    exact (inner_self_eq_zero.mp hnorm).trans j.map_zero.symm
  -- The index relation makes both natural quotient injections onto.
  obtain ⟨e', he', f', hf'⟩ :=
    exists_ker_coker_equiv_of_index_add_eq_zero T S hT hS e f he hf hindex
  refine ⟨e', ?_, f', ?_⟩
  · intro u
    exact LinearMap.congr_fun he' u
  · intro v
    exact LinearMap.congr_fun hf' v

end AtiyahSinger
