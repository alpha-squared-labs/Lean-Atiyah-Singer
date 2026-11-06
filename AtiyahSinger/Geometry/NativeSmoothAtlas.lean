/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothComplexBundleAtlas
public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# The original fixed-rank bundle atlas as a smooth finite-rank atlas

Public module ID: M1307.

D01: convert each designated native complex bundle chart into a chart of the
same fibers with the Unit phantom total-space model. The topology is exactly
the one transported by the existing unitTotalHomeomorph. The coordinate space
changes from EuclideanSpace to the finite product by its canonical continuous
linear equivalence; no basis of an original bundle fiber is selected.

The resulting indexed atlas consists of all original designated charts, with
their original base sets. Its smooth sections are exactly the previously
defined smooth sections, as predicates on the same dependent functions. This
is a compatibility construction for the standard transition description in
SG III.1, p.167, not a new smooth structure chosen on the original bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]

/-- Retype the original chart and its model coordinates, preserving its base and fiber vectors. -/
def nativeFiniteBundleChart
    (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    Trivialization (Fin r → ℂ) (π Unit E) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  (e.compHomeomorph (unitTotalHomeomorph (EuclideanSpace ℂ (Fin r)) E)).transFiberHomeomorph
    (EuclideanSpace.equiv (Fin r) ℂ).toHomeomorph

variable [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hE in
/-- The retyped chart transitions are the original smooth transitions in finite coordinates. -/
theorem contMDiffOn_nativeFiniteBundleChart_coordChange
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] (a : Fin r) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin r → ℂ) ∞
      (fun x : M ↦ (nativeFiniteBundleChart E e'
        ((nativeFiniteBundleChart E e).toPartialEquiv.symm (x, Pi.single a 1))).2)
      ((nativeFiniteBundleChart E e).baseSet ∩ (nativeFiniteBundleChart E e').baseSet) := by
  /- Stage 1: on the original overlap, the two phantom-model conversions
  cancel. The converted inverse sends the standard coordinate vector to
  the same original fiber vector as e.symmL applied to its Euclidean
  counterpart. Applying e' gives the original coordChangeL acting on that
  vector; the remaining model equivalence reads its finite coordinates.
  Stage 2: the original operator-valued transition is real smooth by hE.
  Evaluate it on the fixed standard vector and compose with the canonical
  real-smooth linear model equivalence. The base sets have not changed,
  so this proves the stated column condition on exactly the old overlap.
  Empty overlaps and rank zero require no selected vector or inverse bound. -/
  let e₀ := EuclideanSpace.equiv (Fin r) ℂ
  -- Evaluate the original operator-valued transition on the same fixed coordinate vector.
  have ht := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := E) e e'
  have heval : ContDiff ℝ ∞
      (fun T : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) ↦
        T (e₀.symm (Pi.single a 1))) :=
    (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
  have hv := heval.contMDiff.comp_contMDiffOn ht
  have hmodel := (e₀.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
  apply (hmodel.comp_contMDiffOn hv).congr
  intro x hx
  -- The phantom-model homeomorphisms cancel, leaving the actual native chart transition.
  change e₀ (e' (e.toOpenPartialHomeomorph.symm
    (x, e₀.symm (Pi.single a 1)))).2 = _
  exact congrArg e₀ (e.coordChangeL_apply' e' hx _).symm

/-- The smooth finite-rank atlas consisting of every original designated native chart. -/
def nativeSmoothComplexBundleAtlas :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    SmoothComplexBundleAtlas (n := n) E :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  { Index := {e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E) // MemTrivializationAtlas e}
    rank := fun _ ↦ r
    chart := fun i ↦ nativeFiniteBundleChart E i.val
    covers := by
      intro x
      -- The original chosen chart covers x and belongs to the original designated atlas.
      refine ⟨⟨trivializationAt (EuclideanSpace ℂ (Fin r)) E x, inferInstance⟩, ?_⟩
      exact mem_baseSet_trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    linear := by
      intro i x hx
      let := i.property
      -- Compose the original fiberwise linear chart with the canonical model equivalence.
      change IsLinearMap ℂ
        (fun z : E x ↦ (EuclideanSpace.equiv (Fin r) ℂ) (i.val ⟨x, z⟩).2)
      exact ((EuclideanSpace.equiv (Fin r) ℂ).toLinearMap.comp
        ((i.val.linear ℂ hx).mk' _)).isLinear
    contMDiffOn_coordChange := by
      intro i j a
      let := i.property
      let := j.property
      exact contMDiffOn_nativeFiniteBundleChart_coordChange E i.val j.val a }

/-- The converted atlas tests exactly the old smooth sections on the original fibers. -/
theorem isSmoothSection_nativeSmoothComplexBundleAtlas_iff (s : ∀ x : M, E x) :
    (letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
     (nativeSmoothComplexBundleAtlas (n := n) (r := r) E).IsSmoothSection s) ↔
      IsSmoothSection (n := n) (r := r) E s := by
  /- Stage 1: each chart of the converted atlas is indexed by an original
  designated native chart, and every such chart occurs. Its coordinate
  expression for s is the canonical finite-coordinate linear equivalence
  applied to the old expression, with exactly the same base set.
  Stage 2: that model equivalence and its inverse are real smooth. Compose
  with them in the two directions to identify the coordinate smoothness
  assertions chart by chart. The original dependent function s is never
  transported, resized or replaced, and no compactness or rank positivity
  is used. This compares the actual two predicates rather than an abstract
  isomorphism between potentially different spaces of sections. -/
  let e₀ := EuclideanSpace.equiv (Fin r) ℂ
  constructor
  · intro hs e he
    -- Recover the original native coordinates through the inverse model equivalence.
    have hc := hs ⟨e, he⟩
    have hmodel := (e₀.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
    exact (hmodel.comp_contMDiffOn hc).congr (fun x _ ↦ rfl)
  · intro hs i
    -- Every designated native chart occurs in the converted atlas with the same base set.
    have hc := hs i.val i.property
    have hmodel := (e₀.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
    exact hmodel.comp_contMDiffOn hc

end AtiyahSinger
