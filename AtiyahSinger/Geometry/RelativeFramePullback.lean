/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DiffeomorphBundlePullback

/-!
# Pullback of a specified smooth exterior frame

Public module ID: M1353.

A smooth frame on an open submanifold pulls back through the specified smooth
base map on any open set mapped into its domain. The original fiber action,
canonical trivial target and both native pullback atlases are retained. This
adapter is used twice when transporting the two exterior frames in excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {n m q : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pull back the same exterior frame into the canonical trivial target on the new open set. -/
theorem isSmoothBundleMap_exteriorFrame_pullback
    (E : SmoothFiniteComplexBundle (n := n) M)
    (U : Opens M) (V : Opens N) (f : C(N, M))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hVU : ∀ x : V, f x.val ∈ U)
    (b : ∀ x : U, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin q))
    (hb : IsSmoothBundleMap (n := n) (r := E.rank) (q := q) (M := U)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber))
      (F := Bundle.Trivial U (EuclideanSpace ℂ (Fin q))) (fun x ↦ (b x).toLinearMap)) :
    IsSmoothBundleMap (n := m) (r := E.rank) (q := q) (M := V)
      (E := ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ
        ((f : N → M) *ᵖ E.Fiber)))
      (F := Bundle.Trivial V (EuclideanSpace ℂ (Fin q)))
      (fun x ↦ (b ⟨f x.val, hVU x⟩).toLinearMap) := by
  let iU : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let iV : C(V, N) := ContinuousMap.subtypeVal (V : Set N)
  let j : V → U := fun x ↦ ⟨f x.val, hVU x⟩
  have hj : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff U j).mp (hf.comp contMDiff_subtype_val)
  let t := Bundle.Trivial.trivialization U (EuclideanSpace ℂ (Fin q))
  let : MemTrivializationAtlas t := ⟨rfl⟩
  intro d hd a ha k
  obtain ⟨d₁, hd₁, rfl⟩ := hd
  obtain ⟨d₀, hd₀, rfl⟩ := hd₁
  let : MemTrivializationAtlas d₀ := hd₀
  let : MemTrivializationAtlas (d₀.pullback iU) := ⟨d₀, hd₀, rfl⟩
  obtain rfl := Bundle.Trivial.eq_trivialization V (EuclideanSpace ℂ (Fin q)) a
  have hs := (hb (d₀.pullback iU) t k).comp hj.contMDiffOn
    (fun x (hx : x ∈ ((d₀.pullback f).pullback iV).baseSet ∩ Set.univ) ↦
      ⟨hx.1, Set.mem_univ _⟩)
  apply hs.congr
  intro x hx
  -- Both nested new frames and the old restricted frame select the same original fiber vector.
  have hV : ((d₀.pullback f).pullback iV).symmL ℂ x (EuclideanSpace.single k 1) =
      (d₀.pullback f).symmL ℂ (iV x) (EuclideanSpace.single k 1) := by
    rw [((d₀.pullback f).pullback iV).symmL_apply (R := ℂ) hx.1]
    rw [(d₀.pullback f).symmL_apply (R := ℂ) hx.1,
      ((d₀.pullback f).pullback iV).symm_apply hx.1]
    rfl
  have hf' : (d₀.pullback f).symmL ℂ (iV x) (EuclideanSpace.single k 1) =
      d₀.symmL ℂ (f x.val) (EuclideanSpace.single k 1) := by
    have hxf : f (iV x) ∈ d₀.baseSet := hx.1
    rw [(d₀.pullback f).symmL_apply (R := ℂ) hxf]
    change (d₀.pullback f).symm (iV x) (EuclideanSpace.single k 1) =
      d₀.symmL ℂ (f (iV x)) (EuclideanSpace.single k 1)
    rw [d₀.symmL_apply (R := ℂ) hxf, (d₀.pullback f).symm_apply hxf]
    rfl
  have hU : (d₀.pullback iU).symmL ℂ (j x) (EuclideanSpace.single k 1) =
      d₀.symmL ℂ (f x.val) (EuclideanSpace.single k 1) := by
    have hxU : iU (j x) ∈ d₀.baseSet := hx.1
    rw [(d₀.pullback iU).symmL_apply (R := ℂ) hxU]
    change (d₀.pullback iU).symm (j x) (EuclideanSpace.single k 1) =
      d₀.symmL ℂ (iU (j x)) (EuclideanSpace.single k 1)
    rw [d₀.symmL_apply (R := ℂ) hxU, (d₀.pullback iU).symm_apply hxU]
    rfl
  change b (j x) (((d₀.pullback f).pullback iV).symmL ℂ x _) =
    b (j x) ((d₀.pullback iU).symmL ℂ (j x) _)
  rw [hV, hf', hU]

end AtiyahSinger
