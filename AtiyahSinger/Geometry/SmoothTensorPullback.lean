/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothAtlasPullback
public import AtiyahSinger.Geometry.SmoothTensorAtlas

/-!
# Pulling back sections in the original tensor atlases

Public module ID: M1419.

A smooth section of the specified tensor bundle pulls back smoothly to the
tensor of the two original pullback atlases. Their chart choices need not
be equal: the proof compares their actual coordinate maps on every tensor.
This keeps the original tensor topology and prescribed order of factors.

The result supplies the coefficient pullback in associated kernel evaluation
and other tensor bundle maps over a specified smooth base map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]

attribute [local instance] tensorTopology

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tensor section pulls back to the tensor of the two specified pullback atlases. -/
theorem isSmoothSection_tensor_pullback
    (A : SmoothComplexBundleAtlas (n := n) E) (B : SmoothComplexBundleAtlas (n := n) F)
    (f : C(N, M)) (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (u : ∀ x, E x ⊗[ℂ] F x) (hu : (tensorSmoothAtlas A B).IsSmoothSection u) :
    (tensorSmoothAtlas (E := (f : N → M) *ᵖ E) (F := (f : N → M) *ᵖ F)
      (A.pullback f hf) (B.pullback f hf)).IsSmoothSection (fun y ↦ u (f y)) := by
  classical
  let T := tensorSmoothAtlas A B
  let Ap := A.pullback f hf
  let Bp := B.pullback f hf
  let S := tensorSmoothAtlas (E := (f : N → M) *ᵖ E) (F := (f : N → M) *ᵖ F) Ap Bp
  have hT (p : A.Index × B.Index) :=
    (exists_tensor_trivialization (A.chart p.1) (B.chart p.2)
      (A.linear p.1) (B.linear p.2)).choose_spec
  have hS (p : A.Index × B.Index) :=
    (exists_tensor_trivialization (Ap.chart p.1) (Bp.chart p.2)
      (Ap.linear p.1) (Bp.linear p.2)).choose_spec
  have hbase (p : A.Index × B.Index) : (S.chart p).baseSet = f ⁻¹' (T.chart p).baseSet := by
    calc
      (S.chart p).baseSet = (Ap.chart p.1).baseSet ∩ (Bp.chart p.2).baseSet := (hS p).1
      _ = (f ⁻¹' (A.chart p.1).baseSet) ∩ (f ⁻¹' (B.chart p.2).baseSet) :=
        congrArg₂ Set.inter (A.exists_pullbackChart f p.1).choose_spec.1
          (B.exists_pullbackChart f p.2).choose_spec.1
      _ = f ⁻¹' (T.chart p).baseSet := congrArg (Set.preimage f) (hT p).1.symm
  intro p
  change A.Index × B.Index at p
  have h := (hu p).comp hf.contMDiffOn (fun y hy ↦ (hbase p).subset hy)
  apply h.congr
  intro y hy
  have hyT : f y ∈ (T.chart p).baseSet := (hbase p).subset hy
  have hcoords (v : E (f y) ⊗[ℂ] F (f y)) :
      (S.chart p ⟨y, v⟩).2 = (T.chart p ⟨f y, v⟩).2 := by
    induction v using TensorProduct.inductionOn with
    | tmul v w =>
      funext k
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      have h₁ := (hS p).2.2 y ((hS p).1 ▸ hy) v w i j
      have h₂ := (hT p).2.2 (f y) ((hT p).1 ▸ hyT) v w i j
      change (S.chart p ⟨y, v ⊗ₜ[ℂ] w⟩).2 _ = _ at h₁
      change (T.chart p ⟨f y, v ⊗ₜ[ℂ] w⟩).2 _ = _ at h₂
      have hA := (A.exists_pullbackChart f p.1).choose_spec.2
        (⟨y, v⟩ : TotalSpace Unit ((f : N → M) *ᵖ E))
      have hB := (B.exists_pullbackChart f p.2).choose_spec.2
        (⟨y, w⟩ : TotalSpace Unit ((f : N → M) *ᵖ F))
      change (Ap.chart p.1 ⟨y, v⟩).2 = _ at hA
      change (Bp.chart p.2 ⟨y, w⟩).2 = _ at hB
      exact h₁.trans ((congrArg₂ (· * ·) (congrFun hA i) (congrFun hB j)).trans h₂.symm)
    | add v w hv hw =>
      rw [(S.linear p y hy).map_add, (T.linear p (f y) hyT).map_add, hv, hw]
  exact hcoords (u (f y))

end AtiyahSinger
