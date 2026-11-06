/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle

/-!
# Smooth bundle maps and their action on sections

Public module ID: M1378.

D01/E01/D03: the standard local-matrix definition of a smooth complex-linear
bundle map over a real manifold. Smoothness is real, while the fiber maps are
complex-linear. No continuity or smoothness is inferred merely from fiberwise
linearity. The finite model makes smoothness of all matrix columns equivalent
to smoothness of the full matrix. Inverse smoothness is a theorem.

SG III.1, p.167, and III.13.4, p.248, use such maps as zero-order operators.
The explicit section maps and inverse criterion are standard project supplements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- A fiberwise complex-linear map is smooth when all its local matrix columns are real-smooth. -/
def IsSmoothBundleMap (a : ∀ x, E x →ₗ[ℂ] F x) : Prop :=
  ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e],
    ∀ (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f],
      ∀ j : Fin r,
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
          (fun x ↦ (f ⟨x, a x (e.symmL ℂ x (EuclideanSpace.single j 1))⟩).2)
          (e.baseSet ∩ f.baseSet)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

set_option linter.unusedSectionVars false in
/-- A smooth bundle map acts on the original smooth sections by its fiberwise action. -/
theorem IsSmoothBundleMap.isSmoothSection (a : ∀ x, E x →ₗ[ℂ] F x)
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a)
    (s : smoothSections (n := n) (r := r) E) :
    IsSmoothSection (n := n) (r := q) F (fun x ↦ a x (s.val x)) := by
  /- In a pair of valid bundle frames, expand the source section in the finite
  standard basis. The target coordinates are the sum of its smooth scalar
  coordinates times the smooth columns of a. This proves smoothness on each
  overlap. Source frames cover the base, so smoothness holds in every target frame.
  The case of a zero-dimensional source model is the empty sum. -/
  classical
  intro f hf x hx
  let := hf
  let d := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  have hdx : x ∈ d.baseSet := mem_baseSet_trivializationAt _ _ x
  have hopen := d.open_baseSet.inter f.open_baseSet
  -- Expand in one source frame that is valid near the chosen point.
  have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
      (fun y ↦ ∑ j : Fin r, (d ⟨y, s.val y⟩).2 j •
        (f ⟨y, a y (d.symmL ℂ y (EuclideanSpace.single j 1))⟩).2)
      (d.baseSet ∩ f.baseSet) := by
    apply contMDiffOn_finsetSum
    intro j _
    have hcoeff := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn ((s.property d inferInstance).mono
        (Set.inter_subset_left (t := f.baseSet)))
    have hmul : ContDiff ℝ ∞
        (fun p : ℂ × EuclideanSpace ℂ (Fin q) ↦ p.1 • p.2) := contDiff_smul
    exact hmul.contMDiff.comp_contMDiffOn (hcoeff.prodMk_space (ha d f j))
  have hlocal := hsum.congr (f₁ := fun y ↦ (f ⟨y, a y (s.val y)⟩).2) ?_
  · exact (hlocal.contMDiffAt (hopen.mem_nhds ⟨hdx, hx⟩)).contMDiffWithinAt
  · intro y hy
    let L := (f.linearMapAt ℂ y).comp ((a y).comp (d.symmL ℂ y).toLinearMap)
    have hbasis := (EuclideanSpace.basisFun (Fin r) ℂ).sum_repr (d ⟨y, s.val y⟩).2
    have hexpand := congrArg L hbasis
    simpa [L, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hy.2,
      d.symmL_apply hy.1, d.symm_apply_apply_mk hy.1] using hexpand.symm

set_option linter.unusedSectionVars false in
/-- A smooth family of fiber isomorphisms has smooth inverse on the same actual bundles. -/
theorem IsSmoothBundleMap.symm (e : ∀ x, E x ≃ₗ[ℂ] F x)
    (he : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (e x).toLinearMap)) :
    IsSmoothBundleMap (n := n) (r := q) (q := r) (fun x ↦ (e x).symm.toLinearMap) := by
  /- Assemble the smooth columns into the actual finite-dimensional coordinate
  operator. At each point of the overlap the given fiber equivalence makes this
  operator a continuous linear equivalence, so smooth inversion applies there.
  Its inverse columns are the original inverse fiber map in the reversed frames.
  This argument permits different model types and needs no global rank equality,
  nonempty base, metric, compactness, or continuous choice of inverse. -/
  classical
  intro f hf d hd j x hx
  let L : M → EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) := fun y ↦
    ((f.linearMapAt ℂ y).comp ((e y).toLinearMap.comp
      (d.symmL ℂ y).toLinearMap)).toContinuousLinearMap
  -- The finite sum of the prescribed columns recovers the same coordinate operator.
  have hL : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞ L
      (d.baseSet ∩ f.baseSet) := by
    have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (fun y ↦ ∑ k : Fin r,
          ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
            (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) k)
            ((f ⟨y, e y (d.symmL ℂ y (EuclideanSpace.single k 1))⟩).2))
        (d.baseSet ∩ f.baseSet) := by
      apply contMDiffOn_finsetSum
      intro k _
      exact ((ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
        (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) k)).restrictScalars
          ℝ).contMDiff.comp_contMDiffOn (he d f k)
    apply hsum.congr
    intro y hy
    apply ContinuousLinearMap.ext
    intro v
    have hexpand := congrArg (L y) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
    simpa [L, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hy.2] using hexpand.symm
  -- Invertibility comes from the given fiber equivalence in these exact frames.
  let C (y : M) (hy : y ∈ d.baseSet ∩ f.baseSet) :
      EuclideanSpace ℂ (Fin r) ≃L[ℂ] EuclideanSpace ℂ (Fin q) :=
    (((d.linearEquivAt ℂ y hy.1).symm.trans (e y)).trans
      (f.linearEquivAt ℂ y hy.2)).toContinuousLinearEquiv
  have hC (y : M) (hy : y ∈ d.baseSet ∩ f.baseSet) : (C y hy).toContinuousLinearMap = L y := by
    apply ContinuousLinearMap.ext
    intro v
    simp [C, L, f.coe_linearMapAt_of_mem hy.2, d.symmL_apply hy.1,
      Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply]
  have hinversion := (contDiffAt_map_inverse (n := ∞) (C x hx.symm)).restrict_scalars ℝ
  rw [hC x hx.symm] at hinversion
  have hinv := hinversion.comp_contMDiffAt
    (hL.contMDiffAt ((d.open_baseSet.inter f.open_baseSet).mem_nhds hx.symm))
  have hcolumn := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin r))
    (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ).contDiff.comp_contMDiffAt hinv
  -- Identify inverse columns locally, where both original trivializations are valid.
  apply (hcolumn.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(d.open_baseSet.inter f.open_baseSet).mem_nhds hx.symm] with y hy
  change (d ⟨y, (e y).symm (f.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 =
    (L y).inverse (EuclideanSpace.single j 1)
  rw [← hC y hy, ContinuousLinearMap.inverse_equiv]
  simp [C, f.symmL_apply hy.2, Bundle.Trivialization.linearEquivAt_symm_apply,
    Bundle.Trivialization.linearEquivAt_apply]

/-- The actual complex-linear map on smooth sections induced by a smooth bundle map. -/
def smoothSectionMap (a : ∀ x, E x →ₗ[ℂ] F x)
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F where
  toFun s := ⟨fun x ↦ a x (s.val x), ha.isSmoothSection a s⟩
  map_add' s t := by
    apply Subtype.ext
    funext x
    exact (a x).map_add _ _
  map_smul' c s := by
    apply Subtype.ext
    funext x
    exact (a x).map_smul c _

/-- The section equivalence retains the specified fiber map and its original inverse. -/
def smoothSectionEquiv (e : ∀ x, E x ≃ₗ[ℂ] F x)
    (he : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (e x).toLinearMap)) :
    smoothSections (n := n) (r := r) E ≃ₗ[ℂ] smoothSections (n := n) (r := q) F where
  toLinearMap := smoothSectionMap (fun x ↦ (e x).toLinearMap) he
  invFun := smoothSectionMap (fun x ↦ (e x).symm.toLinearMap) (he.symm e)
  left_inv s := by
    apply Subtype.ext
    funext x
    exact (e x).symm_apply_apply (s.val x)
  right_inv s := by
    apply Subtype.ext
    funext x
    exact (e x).apply_symm_apply (s.val x)

end AtiyahSinger
