/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle

/-!
# Actual bundle transitions in local analytic coordinates

Public module ID: M1258.

D01/D05/A02: connect the ordinary smooth complex bundle atlas to the matrix
transitions needed by SG III.3.15 and 3.18. `e.coordChangeL ℂ e' x` sends old
e-coordinates to new e'-coordinates. Hom coordinates therefore transform by
the forward output transition and inverse input transition, with no adjoint.

The smoothness statements hold along any smooth map into the overlap, including
an inverse manifold chart. No compactness, density, or Hermitian metric is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- Pulling an actual forward frame transition into smooth Euclidean coordinates is smooth. -/
theorem contDiffOn_coordChangeL_comp [IsSmoothComplexBundle (n := n) (r := r) E]
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → M)
    (hc : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ c U)
    (hcover : Set.MapsTo c U (e.baseSet ∩ e'.baseSet)) :
    ContDiffOn ℝ ∞ (fun x ↦ (e.coordChangeL ℂ e' (c x)).toContinuousLinearMap) U := by
  /- Use the real-smooth transition condition of IsSmoothComplexBundle and
  compose it with c using hcover. Both source and target of the resulting map
  are normed vector spaces with their identity model, so manifold smoothness
  is exactly ContDiffOn. Nothing is asserted outside the stated overlap. -/
  exact ((IsSmoothComplexBundle.contMDiffOn_coordChange e e').comp hc hcover).contDiffOn

/-- The inverse transition has the same real smoothness, obtained by swapping the frames. -/
theorem contDiffOn_symm_coordChangeL_comp [IsSmoothComplexBundle (n := n) (r := r) E]
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → M)
    (hc : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ c U)
    (hcover : Set.MapsTo c U (e.baseSet ∩ e'.baseSet)) :
    ContDiffOn ℝ ∞
      (fun x ↦ (e.coordChangeL ℂ e' (c x)).symm.toContinuousLinearMap) U := by
  /- On the overlap, mathlib's symm_coordChangeL identifies the inverse with
  e'.coordChangeL e. Apply the preceding smoothness statement with the frames
  swapped and then use equality on U. This does not replace inverse by adjoint
  or impose bounds on the transition outside the local coordinate domain. -/
  have hswap := contDiffOn_coordChangeL_comp E e' e U c hc
    (fun x hx ↦ (hcover hx).symm)
  apply hswap.congr
  intro x hx
  rw [e.symm_coordChangeL e' (hcover hx).symm]

/-- Section coefficients in the new frame are the forward transition of the old ones. -/
theorem coordChangeL_section_coordinates
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    (s : ∀ x, E x) (x : M) (hx : x ∈ e.baseSet ∩ e'.baseSet) :
    (e' ⟨x, s x⟩).2 = e.coordChangeL ℂ e' x (e ⟨x, s x⟩).2 := by
  /- The transition first applies the inverse of e and then e'. On the common
  base set the inverse of e sends the old coordinates back to the actual fiber
  vector s(x). This fixes the direction of the transition without requiring
  smoothness of the section or a norm/metric preservation property. -/
  rw [e.coordChangeL_apply e' hx, e.symm_apply_apply_mk hx.1]

variable (F : M → Type*) [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- A fiber Hom map changes coordinates by forward output and inverse input transitions. -/
theorem homInFrames_coordChange
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    (f f' : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas f] [MemTrivializationAtlas f']
    (x : M) (he : x ∈ e.baseSet ∩ e'.baseSet) (hf : x ∈ f.baseSet ∩ f'.baseSet)
    (L : E x →L[ℂ] F x) :
    (f'.continuousLinearMapAt ℂ x).comp (L.comp (e'.symmL ℂ x)) =
      (f.coordChangeL ℂ f' x).toContinuousLinearMap.comp
        (((f.continuousLinearMapAt ℂ x).comp (L.comp (e.symmL ℂ x))).comp
          (e.coordChangeL ℂ e' x).symm.toContinuousLinearMap) := by
  /- Identify each frame map on its base set with its continuous linear
  equivalence. Insert the old input and output identities around L and group
  the factors. The output transition is f' f⁻¹ and the inverse input transition
  is e e'⁻¹. This is the Hom-bundle transition law underlying the principal symbol. -/
  ext v
  -- Express the inverse input transition using the same two actual frame inverses.
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [e.symm_coordChangeL e' he.symm, e'.coordChangeL_apply e he.symm,
    e.symmL_apply he.1, e'.symmL_apply he.2, e.symm_apply_apply_mk he.1,
    f.continuousLinearMapAt_apply_of_mem ℂ hf.1, f'.continuousLinearMapAt_apply_of_mem ℂ hf.2,
    f.coordChangeL_apply f' hf, f.symm_apply_apply_mk hf.1]

end AtiyahSinger
