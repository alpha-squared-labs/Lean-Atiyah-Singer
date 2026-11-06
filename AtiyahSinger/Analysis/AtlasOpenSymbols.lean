/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Analysis.OpenSymbolCoordinates
public import AtiyahSinger.Geometry.SmoothAtlasRestriction

/-!
# Restricting the original atlas symbols to an open submanifold

Public module ID: M0272.

The open inclusion has the identity tangent derivative in the inherited charts.
Its restricted bundle atlases retain exactly the original fiber coordinates.
Consequently their local symbols are the same functions on smaller coordinate
domains. Smoothness, every symbol estimate and positive homogeneity restrict
without any replacement of the symbol or its original cotangent vector.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] in
/-- The restricted coordinate domain is contained in the original domain of the same frames. -/
theorem atlasSymbolChartDomain_restrictOpen_subset (U : Opens M) (hU : Nonempty U)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (i : A.Index) (j : B.Index) :
    atlasSymbolChartDomain (A.restrictOpen U) (B.restrictOpen U) (c.subtypeRestr hU) i j ⊆
      atlasSymbolChartDomain A B c i j := by
  intro z hz
  have hr := c.subtypeRestr_symm_apply hU hz.1.1
  have hA : ((A.restrictOpen U).chart i).baseSet =
      Subtype.val ⁻¹' (A.chart i).baseSet := (A.exists_restrictOpenChart U i).choose_spec.1
  have hB : ((B.restrictOpen U).chart j).baseSet =
      Subtype.val ⁻¹' (B.chart j).baseSet := (B.exists_restrictOpenChart U j).choose_spec.1
  refine ⟨⟨c.subtypeRestr_target_subset hU hz.1.1, ?_⟩, ?_⟩
  · have hx := hz.1.2
    change (c.subtypeRestr hU).symm z ∈ ((A.restrictOpen U).chart i).baseSet at hx
    rw [hA] at hx
    change c.symm z ∈ (A.chart i).baseSet
    rw [← hr]
    exact hx
  · have hx := hz.2
    change (c.subtypeRestr hU).symm z ∈ ((B.restrictOpen U).chart j).baseSet at hx
    rw [hB] at hx
    change c.symm z ∈ (B.chart j).baseSet
    rw [← hr]
    exact hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the restricted chart domain the original symbol and both fiber coordinates are unchanged. -/
theorem atlasGlobalSymbolInChart_restrictOpen
    (U : Opens M) (hU : Nonempty U)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (a : AtlasSymbolFunction (n := n) E F) (i : A.Index) (j : B.Index)
    (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ atlasSymbolChartDomain (A.restrictOpen U) (B.restrictOpen U)
      (c.subtypeRestr hU) i j) (η : EuclideanSpace ℝ (Fin n)) :
    atlasGlobalSymbolInChart (A.restrictOpen U) (B.restrictOpen U)
        (fun x ξ ↦ a x.val ξ) (c.subtypeRestr hU) i j z η =
      atlasGlobalSymbolInChart A B a c i j z η := by
  classical
  let d := c.subtypeRestr hU
  let x : U := d.symm z
  have hxreturn : x.val = c.symm z := c.subtypeRestr_symm_apply hU hz.1.1
  have hxsource : x.val ∈ c.source := by
    rw [hxreturn]
    exact c.map_target (c.subtypeRestr_target_subset hU hz.1.1)
  have hAbase : (A.restrictOpenChart U i).baseSet =
      Subtype.val ⁻¹' (A.chart i).baseSet := (A.exists_restrictOpenChart U i).choose_spec.1
  have hBbase : (B.restrictOpenChart U j).baseSet =
      Subtype.val ⁻¹' (B.chart j).baseSet := (B.exists_restrictOpenChart U j).choose_spec.1
  have hAr : (c.subtypeRestr hU).symm z ∈ ((A.restrictOpen U).chart i).baseSet := hz.1.2
  have hBr : (c.subtypeRestr hU).symm z ∈ ((B.restrictOpen U).chart j).baseSet := hz.2
  have hAx : x.val ∈ (A.chart i).baseSet := by
    have h : x ∈ (A.restrictOpenChart U i).baseSet := hz.1.2
    rw [hAbase] at h
    exact h
  have hBx : x.val ∈ (B.chart j).baseSet := by
    have h : x ∈ (B.restrictOpenChart U j).baseSet := hz.2
    rw [hBbase] at h
    exact h
  have hAz : c.symm z ∈ (A.chart i).baseSet := hxreturn ▸ hAx
  have hBz : c.symm z ∈ (B.chart j).baseSet := hxreturn ▸ hBx
  -- The chart composite has the original derivative, since the open inclusion has derivative id.
  have hder : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) d x =
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c x.val := by
    have h := mfderiv_comp x
      (mdifferentiableAt_atlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hc hxsource)
      ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) x)
    rw [mfderiv_openSubtypeVal] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h
  have hcov : covectorFromChart d x η = covectorFromChart c x.val η := by
    unfold covectorFromChart
    rw [hder]
  have hAi : (A.restrictOpen U).frameLinearEquiv i x hz.1.2 =
      A.frameLinearEquiv i x.val hAx := by
    apply LinearEquiv.ext
    intro v
    exact (A.exists_restrictOpenChart U i).choose_spec.2 ⟨x, v⟩
  have hBj : (B.restrictOpen U).frameLinearEquiv j x hz.2 =
      B.frameLinearEquiv j x.val hBx := by
    apply LinearEquiv.ext
    intro v
    exact (B.exists_restrictOpenChart U j).choose_spec.2 ⟨x, v⟩
  -- Both finite-coordinate conversions now use literally the same maps and cotangent vector.
  simp only [atlasGlobalSymbolInChart, hAr, hBr, hAz, hBz,
    and_self, dite_true]
  change LinearMap.toContinuousLinearMap
      ((((B.restrictOpen U).frameLinearEquiv j x hz.2).trans
          (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.toLinearEquiv).toLinearMap.comp
        ((a x.val (covectorFromChart d x η)).comp
          (((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toLinearEquiv.trans
            ((A.restrictOpen U).frameLinearEquiv i x hz.1.2).symm).toLinearMap))) = _
  rw [hAi, hBj, hcov]
  let value (y : M) (hyA : y ∈ (A.chart i).baseSet) (hyB : y ∈ (B.chart j).baseSet) :
      EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (B.rank j)) :=
    LinearMap.toContinuousLinearMap
      (((B.frameLinearEquiv j y hyB).trans
        (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.toLinearEquiv).toLinearMap.comp
          ((a y (covectorFromChart c y η)).comp
            (((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toLinearEquiv.trans
              (A.frameLinearEquiv i y hyA).symm).toLinearMap)))
  change value x.val hAx hBx = value (c.symm z) hAz hBz
  have hvalue (y : M) (hyA : y ∈ (A.chart i).baseSet) (hyB : y ∈ (B.chart j).baseSet)
      (hxy : x.val = y) : value x.val hAx hBx = value y hyA hyB := by
    subst y
    rfl
  exact hvalue _ _ _ hxreturn

/-- Every actual full-symbol estimate survives restriction to the original open submanifold. -/
theorem IsAtlasGlobalSymbol.restrictOpen {m : ℝ} {a : AtlasSymbolFunction (n := n) E F}
    (ha : IsAtlasGlobalSymbol A B m a) (U : Opens M) :
    IsAtlasGlobalSymbol (A.restrictOpen U) (B.restrictOpen U) m (fun x ξ ↦ a x.val ξ) := by
  intro c hc i j
  have hU : Nonempty U := by
    rcases hc with ⟨_, ⟨x, _⟩, _⟩
    exact ⟨x⟩
  obtain ⟨x, rfl⟩ := Opens.chart_eq hU hc
  let d := chartAt (EuclideanSpace ℝ (Fin n)) x.val
  let D := atlasSymbolChartDomain (A.restrictOpen U) (B.restrictOpen U)
    (d.subtypeRestr hU) i j
  have hD : IsOpen D := by
    simpa only [D, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      (d.subtypeRestr hU).continuousOn_symm.isOpen_inter_preimage
        (d.subtypeRestr hU).open_target
        (((A.restrictOpen U).chart i).open_baseSet.inter
          ((B.restrictOpen U).chart j).open_baseSet)
  have h := (ha d (chart_mem_atlas _ x.val) i j).restrict
    (atlasSymbolChartDomain_restrictOpen_subset A B U hU d i j)
  apply h.congr_on hD
  intro z hz
  funext η
  exact (atlasGlobalSymbolInChart_restrictOpen A B U hU d
    (chart_mem_atlas _ x.val) a i j z hz η).symm

/-- Off-zero smoothness restricts in the inherited charts and bundle frames. -/
theorem IsSmoothOffZeroAtlasSymbol.restrictOpen {a : AtlasSymbolFunction (n := n) E F}
    (ha : IsSmoothOffZeroAtlasSymbol A B a) (U : Opens M) :
    IsSmoothOffZeroAtlasSymbol (A.restrictOpen U) (B.restrictOpen U) (fun x ξ ↦ a x.val ξ) := by
  intro c hc i j
  have hU : Nonempty U := by
    rcases hc with ⟨_, ⟨x, _⟩, _⟩
    exact ⟨x⟩
  obtain ⟨x, rfl⟩ := Opens.chart_eq hU hc
  let d := chartAt (EuclideanSpace ℝ (Fin n)) x.val
  apply ((ha d (chart_mem_atlas _ x.val) i j).mono
    (Set.prod_mono (atlasSymbolChartDomain_restrictOpen_subset A B U hU d i j)
      Set.Subset.rfl)).congr
  intro z hz
  exact atlasGlobalSymbolInChart_restrictOpen A B U hU d
    (chart_mem_atlas _ x.val) a i j z.1 hz.1 z.2

end AtiyahSinger
