/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundlePullback
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.LinearAlgebra.Pi

/-!
# Pullback of actual smooth sections

Public module ID: M1412.

D01/E01/UL03: section pullback uses the original value at the image point in
mathlib's native pullback bundle. A diffeomorphism gives an equivalence, also
with prescribed support. These standard constructions make explicit the natural
section identifications in SG III.13.4, pp.248--249. They impose no compactness,
properness, or new metric, and do not assert operator covariance.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n m r : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  (E : N → Type*) [∀ y, NormedAddCommGroup (E y)] [∀ y, NormedSpace ℂ (E y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

include hM hN

set_option linter.unusedSectionVars false in
/-- Smooth base change pulls back a smooth section to its actual composite. -/
theorem isSmoothSection_pullback (f : C(M, N))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (s : smoothSections (n := m) (r := r) E) :
    IsSmoothSection (n := n) (r := r) ((f : M → N) *ᵖ E) (fun x ↦ s.val (f x)) := by
  /- In each native pullback frame the section coordinates are exactly the
  original coordinates composed with f. Smooth composition on the preimage
  of the frame domain gives the assertion. Neither compactness nor properness
  is needed; pullback along a general map need not preserve compact support. -/
  intro e he
  rcases he with ⟨e, he, rfl⟩
  -- Native pullback coordinates are the original coordinates composed with the base map.
  exact (s.property e he).comp hf.contMDiffOn (fun x hx ↦ hx)

/-- Pullback of smooth sections, with the original fiber value and linear operations. -/
def smoothSectionPullback (f : C(M, N))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) :
    smoothSections (n := m) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := r) ((f : M → N) *ᵖ E) where
  toFun s := ⟨fun x ↦ s.val (f x), isSmoothSection_pullback E f hf s⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A diffeomorphism both preserves and detects smoothness in the native pullback bundle. -/
theorem isSmoothSection_pullback_diffeomorph_iff
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N)
    (s : ∀ y, E y) :
    IsSmoothSection (n := n) (r := r)
        (((⟨e, e.continuous⟩ : C(M, N)) : M → N) *ᵖ E) (fun x ↦ s (e x)) ↔
      IsSmoothSection (n := m) (r := r) E s := by
  /- The reverse implication is smooth section pullback. For the forward
  implication, each original frame pulls back to its full inverse-image domain.
  Compose the smooth pulled-back coordinates with e.symm on that frame domain.
  The identity e(e.symm y)=y recovers the original coordinates. Surjectivity is
  essential here; an arbitrary smooth base map need not detect regularity. -/
  constructor
  · intro hs t ht
    have ht' : MemTrivializationAtlas (t.pullback (⟨e, e.continuous⟩ : C(M, N))) :=
      ⟨t, ht, rfl⟩
    -- Pull back this original frame, then compose its smooth coordinates with the inverse.
    have h := (hs _ ht').comp e.symm.contMDiff.contMDiffOn
      (show Set.MapsTo e.symm t.baseSet
        (t.pullback (⟨e, e.continuous⟩ : C(M, N))).baseSet from
        fun y hy ↦ by simpa using hy)
    apply h.congr
    intro y hy
    change (t ⟨y, s y⟩).2 = (t ⟨e (e.symm y), s (e (e.symm y))⟩).2
    rw [e.apply_symm_apply]
  · intro hs
    exact isSmoothSection_pullback E (⟨e, e.continuous⟩ : C(M, N)) e.contMDiff ⟨s, hs⟩

/-- A diffeomorphism identifies smooth sections by actual pullback, with its inverse transport. -/
def smoothSectionDiffeomorphEquiv
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N) :
    smoothSections (n := m) (r := r) E ≃ₗ[ℂ]
      smoothSections (n := n) (r := r)
        (((⟨e, e.continuous⟩ : C(M, N)) : M → N) *ᵖ E) := by
  -- Use the standard dependent-function equivalence to retain the necessary fiber casts.
  let A := LinearEquiv.piCongrLeft ℂ E e.toEquiv
  refine
    { toFun := smoothSectionPullback E (⟨e, e.continuous⟩ : C(M, N)) e.contMDiff
      invFun := fun t ↦ ⟨A t.val, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  · apply (isSmoothSection_pullback_diffeomorph_iff E e (A t.val)).mp
    change IsSmoothSection (n := n) (r := r)
      (((⟨e, e.continuous⟩ : C(M, N)) : M → N) *ᵖ E) (A.symm (A t.val))
    erw [A.symm_apply_apply]
    exact t.property
  · intro s
    apply Subtype.ext
    exact A.apply_symm_apply s.val
  · intro t
    apply Subtype.ext
    exact A.symm_apply_apply t.val

/-- Actual diffeomorphism pullback identifies sections with corresponding support constraints. -/
def supportedSmoothSectionDiffeomorphEquiv
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N)
    (K : Set N) :
    supportedSmoothSections (n := m) (r := r) E K ≃ₗ[ℂ]
      supportedSmoothSections (n := n) (r := r)
        (((⟨e, e.continuous⟩ : C(M, N)) : M → N) *ᵖ E) (e ⁻¹' K) := by
  let A := smoothSectionDiffeomorphEquiv (r := r) E e
  refine
    { toFun := fun s ↦ ⟨A s.val, fun x hx ↦ s.property (e x) hx⟩
      invFun := fun t ↦ ⟨A.symm t.val, ?_⟩
      left_inv := fun s ↦ Subtype.ext (A.symm_apply_apply s.val)
      right_inv := fun t ↦ Subtype.ext (A.apply_symm_apply t.val)
      map_add' := fun s t ↦ Subtype.ext (A.map_add s.val t.val)
      map_smul' := fun c s ↦ Subtype.ext (A.map_smul c s.val) }
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have h := congrArg (fun s ↦ s.val x) (A.apply_symm_apply t.val)
    change (A.symm t.val).val (e x) = t.val.val x at h
    exact h.trans (t.property x hy)

end AtiyahSinger
