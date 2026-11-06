/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DiffeomorphBundlePullback

/-!
# Restricting an open parametrization to its full source

Public module ID: M1377.

The full open subspace carries the original smooth charts. Restricting a given
bundle map to it keeps every fiber action and its native matrix columns. These
adapters feed a parametrization into the two-open-region extension interfaces.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {n m : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]

/-- The specified diffeomorphism with its domain presented as the full open subspace. -/
def diffeomorphFromTop
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ M) :
    (⊤ : Opens O) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ M where
  toFun x := e x.val
  invFun y := ⟨e.symm y, Set.mem_univ _⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := e.apply_symm_apply y
  contMDiff_toFun := e.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp e.symm.contMDiff

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Full-source restriction preserves the original native smooth fiber map. -/
theorem IsSmoothBundleMap.fromTop
    (E : SmoothFiniteComplexBundle (n := n) O)
    (G : SmoothFiniteComplexBundle (n := m) M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ M)
    (a : ∀ x : O, E.Fiber x →ₗ[ℂ] G.Fiber (e x))
    (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
      (E := E.Fiber) (F := ((⟨e, e.continuous⟩ : C(O, M)) : O → M) *ᵖ G.Fiber) a) :
    IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank) (M := (⊤ : Opens O))
      (E := (ContinuousMap.subtypeVal ((⊤ : Opens O) : Set O) : (⊤ : Opens O) → O) *ᵖ E.Fiber)
      (F := ((⟨diffeomorphFromTop e, (diffeomorphFromTop e).continuous⟩ :
        C((⊤ : Opens O), M)) : (⊤ : Opens O) → M) *ᵖ G.Fiber)
      (fun x ↦ a x.val) := by
  rintro _ ⟨d, hd, rfl⟩ _ ⟨t, ht, rfl⟩ j
  let := hd
  let := ht
  let p : C(O, M) := ⟨e, e.continuous⟩
  let i : C((⊤ : Opens O), O) := ContinuousMap.subtypeVal ((⊤ : Opens O) : Set O)
  let : MemTrivializationAtlas (t.pullback p) := ⟨t, ht, rfl⟩
  have hs := (ha d (t.pullback p) j).comp
    (contMDiff_subtype_val (U := (⊤ : Opens O))).contMDiffOn (fun x hx ↦ hx)
  apply hs.congr
  intro x hx
  have hdv : (d.pullback i).symmL ℂ x (EuclideanSpace.single j 1) =
      d.symmL ℂ x.val (EuclideanSpace.single j 1) := by
    rw [(d.pullback i).symmL_apply hx.1, d.symmL_apply hx.1,
      (d.pullback i).symm_apply hx.1]
    rfl
  change (t ⟨e x.val, a x.val ((d.pullback i).symmL ℂ x (EuclideanSpace.single j 1))⟩).2 =
    (t ⟨e x.val, a x.val (d.symmL ℂ x.val (EuclideanSpace.single j 1))⟩).2
  rw [hdv]

end AtiyahSinger
