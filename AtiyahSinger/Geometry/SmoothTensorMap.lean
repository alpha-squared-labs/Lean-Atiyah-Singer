/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothTensorAtlas

/-!
# Tensor products of smooth maps in the original bundle atlases

Public module ID: M1418.

The tensor product of two smooth fiberwise linear maps is smooth in the
specified tensor atlases. Its matrix is the product of the two original
matrix entries, with the prescribed order of factors and local ranks.
This supplies the base-coefficient extension of the associated evaluation
map in SG III.13.6 without changing either tensor bundle topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  {E₀ F₀ : M → Type*} {E₁ F₁ : N → Type*}
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, AddCommGroup (F₀ x)] [∀ x, Module ℂ (F₀ x)]
  [∀ x, AddCommGroup (F₁ x)] [∀ x, Module ℂ (F₁ x)]
  [TopologicalSpace (TotalSpace Unit E₀)] [TopologicalSpace (TotalSpace Unit E₁)]
  [TopologicalSpace (TotalSpace Unit F₀)] [TopologicalSpace (TotalSpace Unit F₁)]

attribute [local instance] ComplexBundle.tensorTopology

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring the two specified smooth bundle maps preserves their original tensor atlases. -/
theorem IsSmoothAtlasBundleMapOver.tensor
    {A₀ : SmoothComplexBundleAtlas (n := n) E₀}
    {A₁ : SmoothComplexBundleAtlas (n := m) E₁}
    {B₀ : SmoothComplexBundleAtlas (n := n) F₀}
    {B₁ : SmoothComplexBundleAtlas (n := m) F₁}
    {f : M → N} {a : ∀ x, E₀ x →ₗ[ℂ] E₁ (f x)}
    {b : ∀ x, F₀ x →ₗ[ℂ] F₁ (f x)}
    (ha : IsSmoothAtlasBundleMapOver A₀ A₁ f a)
    (hb : IsSmoothAtlasBundleMapOver B₀ B₁ f b) :
    IsSmoothAtlasBundleMapOver (tensorSmoothAtlas A₀ B₀) (tensorSmoothAtlas A₁ B₁) f
      (fun x ↦ TensorProduct.map (a x) (b x)) := by
  classical
  let S := tensorSmoothAtlas A₀ B₀
  let T := tensorSmoothAtlas A₁ B₁
  have hS (p : A₀.Index × B₀.Index) := (ComplexBundle.exists_tensor_trivialization
    (A₀.chart p.1) (B₀.chart p.2) (A₀.linear p.1) (B₀.linear p.2)).choose_spec
  have hT (p : A₁.Index × B₁.Index) := (ComplexBundle.exists_tensor_trivialization
    (A₁.chart p.1) (B₁.chart p.2) (A₁.linear p.1) (B₁.linear p.2)).choose_spec
  have hscalar (p q : Prop) [Decidable p] [Decidable q] :
      (if p ∧ q then (1 : ℂ) else 0) =
        (if p then (1 : ℂ) else 0) * (if q then (1 : ℂ) else 0) := by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  -- A tensor-frame basis vector is exactly the tensor of its two source-frame vectors.
  have hframe (p : A₀.Index × B₀.Index) (x : M) (hx : x ∈ (S.chart p).baseSet)
      (k : Fin (S.rank p)) :
      (S.frameLinearEquiv p x hx).symm (Pi.single k 1) =
        (A₀.frameLinearEquiv p.1 x ((hS p).1 ▸ hx).1).symm
            (Pi.single (finProdFinEquiv.symm k).1 1) ⊗ₜ[ℂ]
          (B₀.frameLinearEquiv p.2 x ((hS p).1 ▸ hx).2).symm
            (Pi.single (finProdFinEquiv.symm k).2 1) := by
    apply (S.frameLinearEquiv p x hx).injective
    rw [LinearEquiv.apply_symm_apply]
    funext l
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective l
    change (Pi.single k 1 : Fin (S.rank p) → ℂ) (finProdFinEquiv (i, j)) =
      (S.chart p ⟨x, _ ⊗ₜ[ℂ] _⟩).2 (finProdFinEquiv (i, j))
    have hpure := (hS p).2.2 x ((hS p).1 ▸ hx)
      ((A₀.frameLinearEquiv p.1 x ((hS p).1 ▸ hx).1).symm
        (Pi.single (finProdFinEquiv.symm k).1 1))
      ((B₀.frameLinearEquiv p.2 x ((hS p).1 ▸ hx).2).symm
        (Pi.single (finProdFinEquiv.symm k).2 1)) i j
    change (S.chart p ⟨x, _ ⊗ₜ[ℂ] _⟩).2 (finProdFinEquiv (i, j)) = _ at hpure
    rw [hpure]
    change (Pi.single k 1 : Fin (S.rank p) → ℂ) (finProdFinEquiv (i, j)) =
      ((A₀.frameLinearEquiv p.1 x ((hS p).1 ▸ hx).1)
        ((A₀.frameLinearEquiv p.1 x ((hS p).1 ▸ hx).1).symm _)) i *
      ((B₀.frameLinearEquiv p.2 x ((hS p).1 ▸ hx).2)
        ((B₀.frameLinearEquiv p.2 x ((hS p).1 ▸ hx).2).symm _)) j
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hk : k = finProdFinEquiv
        ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2) :=
      (finProdFinEquiv.apply_symm_apply k).symm
    conv_lhs => rw [hk]
    clear hk
    simp only [Pi.single_apply, finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
    exact hscalar _ _
  refine ⟨ha.1, ?_⟩
  intro p q k
  apply contMDiffOn_pi_space.mpr
  intro l
  let k₁ := (finProdFinEquiv.symm k).1
  let k₂ := (finProdFinEquiv.symm k).2
  let l₁ := (finProdFinEquiv.symm l).1
  let l₂ := (finProdFinEquiv.symm l).2
  have hA := (contMDiffOn_pi_space.mp (ha.2 p.1 q.1 k₁) l₁).mono
    (show (S.chart p).baseSet ∩ f ⁻¹' (T.chart q).baseSet ⊆
        (A₀.chart p.1).baseSet ∩ f ⁻¹' (A₁.chart q.1).baseSet from by
      intro x hx
      exact ⟨((hS p).1 ▸ hx.1).1, ((hT q).1 ▸ hx.2).1⟩)
  have hB := (contMDiffOn_pi_space.mp (hb.2 p.2 q.2 k₂) l₂).mono
    (show (S.chart p).baseSet ∩ f ⁻¹' (T.chart q).baseSet ⊆
        (B₀.chart p.2).baseSet ∩ f ⁻¹' (B₁.chart q.2).baseSet from by
      intro x hx
      exact ⟨((hS p).1 ▸ hx.1).2, ((hT q).1 ▸ hx.2).2⟩)
  -- Each target matrix entry is the product of these two original smooth entries.
  apply ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
    (hA.prodMk_space hB)).congr
  intro x hx
  rw [dite_eq_left hx.1, hframe p x hx.1, TensorProduct.map_tmul]
  dsimp only [Function.comp_apply]
  rw [dite_eq_left ((hS p).1 ▸ hx.1).1, dite_eq_left ((hS p).1 ▸ hx.1).2]
  have h := (hT q).2.2 (f x) ((hT q).1 ▸ hx.2)
    (a x ((A₀.frameLinearEquiv p.1 x ((hS p).1 ▸ hx.1).1).symm (Pi.single k₁ 1)))
    (b x ((B₀.frameLinearEquiv p.2 x ((hS p).1 ▸ hx.1).2).symm (Pi.single k₂ 1))) l₁ l₂
  simpa only [T, tensorSmoothAtlas, tensorBundleChart, k₁, k₂, l₁, l₂,
    Prod.mk.eta, Equiv.apply_symm_apply] using h

end AtiyahSinger
