/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMapPullback
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth extension of an exterior bundle map

Public module ID: M1227.

On a Hausdorff second-countable smooth manifold, a map smooth on an exterior
open submanifold extends to the original bundles on the whole manifold,
with equality on a farther exterior. A smooth cutoff
kills it near the original compact exception. This standard relative extension
preserves the specified fiber action and does not assert interior invertibility.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

include hM hT hSC

/-- Extend the same exterior map after allowing a larger compact exception. -/
theorem exists_smoothBundleMap_extension_of_exterior (U : Opens M)
    (K : Set M) (hK : IsCompact K) (hKU : Kᶜ ⊆ (U : Set M))
    (a : ∀ x : U, E x.val →L[ℂ] F x.val)
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) (M := U)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E))
      (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F))
      (fun x ↦ (a x).toLinearMap)) :
    ∃ L : Set M, IsCompact L ∧ K ⊆ interior L ∧
      ∃ c : ∀ x, E x →L[ℂ] F x,
        IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (c x).toLinearMap) ∧
        ∀ (x : U), x.val ∉ L → c x.val = a x := by
  classical
  let H := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let Z := EuclideanSpace ℂ (Fin q)
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨L, hL, hKL, _⟩ := exists_compact_between hK isOpen_univ (Set.subset_univ K)
  obtain ⟨η, hηone, hηzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ, H) hK.isClosed hKL
  let c (x : M) : E x →L[ℂ] F x :=
    if hx : x ∈ U then (((1 - η x : ℝ) : ℂ) • a ⟨x, hx⟩) else 0
  -- Descend native pullback columns through the open-submanifold inclusion.
  have haLocal (e : Trivialization V (π V E)) [MemTrivializationAtlas e]
      (f : Trivialization Z (π Z F)) [MemTrivializationAtlas f]
      (j : Fin r) (x : M) (hx : x ∈ e.baseSet ∩ f.baseSet) (hxU : x ∈ U) :
      ContMDiffAt 𝓘(ℝ, H) 𝓘(ℝ, Z) ∞
        (fun y ↦ if hy : y ∈ U then
          (f ⟨y, a ⟨y, hy⟩ (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 else 0) x := by
    let x' : U := ⟨x, hxU⟩
    let : MemTrivializationAtlas (e.pullback i) := ⟨e, inferInstance, rfl⟩
    let : MemTrivializationAtlas (f.pullback i) := ⟨f, inferInstance, rfl⟩
    have hx' : x' ∈ (e.pullback i).baseSet ∩ (f.pullback i).baseSet := hx
    have hlocal := (ha (e.pullback i) (f.pullback i) j).contMDiffAt
      (((e.pullback i).open_baseSet.inter (f.pullback i).open_baseSet).mem_nhds hx')
    apply (contMDiffAt_subtype_iff (U := U) (x := x')).mp
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [((e.pullback i).open_baseSet.inter
      (f.pullback i).open_baseSet).mem_nhds hx'] with y hy
    have heq : (e.pullback i).symmL ℂ y (EuclideanSpace.single j 1) =
        e.symmL ℂ y.val (EuclideanSpace.single j 1) := by
      rw [(e.pullback i).symmL_apply (R := ℂ) hy.1]
      change (e.pullback i).symm y (EuclideanSpace.single j 1) =
        e.symmL ℂ (i y) (EuclideanSpace.single j 1)
      rw [e.symmL_apply (R := ℂ) hy.1, (e.pullback i).symm_apply hy.1]
      rfl
    erw [dite_eq_left y.property]
    change (f ⟨y.val, a y (e.symmL ℂ y.val (EuclideanSpace.single j 1))⟩).2 =
      (f ⟨y.val, a y ((e.pullback i).symmL ℂ y (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  refine ⟨L, hL, hKL, c, ?_, ?_⟩
  · intro e he f hf j x hx
    let := he
    let := hf
    by_cases hxK : x ∈ K
    · -- The cutoff kills the map on a neighborhood, including the boundary of its domain.
      have hηx : ∀ᶠ y in 𝓝 x, η y = 1 := hηone.filter_mono (nhds_le_nhdsSet hxK)
      apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : Z))).congr_of_eventuallyEq
      filter_upwards [hηx, f.open_baseSet.mem_nhds hx.2] with y hηy hyf
      have hcy : c y = 0 := by
        dsimp only [c]
        split_ifs
        · rw [hηy, sub_self, Complex.ofReal_zero, zero_smul]
        · rfl
      change (f ⟨y, c y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 = 0
      rw [hcy, zero_apply]
      exact (f.linearEquivAt ℂ y hyf).map_zero
    · -- Elsewhere the original columns are smooth, multiplied by the smooth scalar cutoff.
      have hxU := hKU hxK
      have hscalar : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, ℂ) ∞
          (fun y ↦ ((1 - η y : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub η.contMDiff)
      have hmul : ContDiff ℝ ∞ (fun t : ℂ × Z ↦ t.1 • t.2) := contDiff_smul
      have hs := hmul.contMDiff.contMDiffAt.comp x
        (hscalar.contMDiffAt.prodMk_space (haLocal e f j x hx hxU))
      apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [U.isOpen.mem_nhds hxU, f.open_baseSet.mem_nhds hx.2] with y hyU hyf
      change (f ⟨y, c y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 =
        ((1 - η y : ℝ) : ℂ) • (if hy : y ∈ U then
          (f ⟨y, a ⟨y, hy⟩ (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 else 0)
      have hcy : c y = (((1 - η y : ℝ) : ℂ) • a ⟨y, hyU⟩) := dite_eq_left hyU
      rw [hcy]
      erw [dite_eq_left hyU]
      exact (f.linearEquivAt ℂ y hyf).map_smul _ _
  · intro x hx
    dsimp only [c]
    rw [dite_eq_left x.property, hηzero x.val hx, sub_zero, Complex.ofReal_one, one_smul]

end AtiyahSinger
