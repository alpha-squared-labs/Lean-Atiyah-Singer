/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasHermitianCoordinates
public import AtiyahSinger.Geometry.AtlasNativeModel
public import AtiyahSinger.Geometry.HermitianMetric

/-!
# The original atlas metric on a specified native model

Public module ID: M1099.

Transport the given positive forms through the same supplied bundle isomorphism
that identifies the original atlas with its native model. Smoothness is checked
using the smooth inverse map, the original atlas Gram operator, and the actual
native frame vectors. No replacement model, norm, pairing, or isomorphism is chosen.
This standard metric transport is needed when realizing associated tensor sections
in the native Hilbert spaces used for the product-index argument (SG III.13).
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

set_option maxSynthPendingDepth 40 in
/-- The prescribed native model carries the metric with exactly the original fiber pairings. -/
theorem exists_native_smoothHermitianMetric
    (A : SmoothComplexBundleAtlas (n := n) E)
    (h : ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (F : SmoothFiniteComplexBundle (n := n) M) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (e : Iso E F.Fiber),
      IsSmoothAtlasBundleMap
        (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) A
        e.symm.toHom.linearMap →
      ∃ k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber,
        ∀ (x : M) (v w : E x),
          k.pairing x (e.linearEquiv x v) (e.linearEquiv x w) =
            (h.toCore x).inner v w := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  intro e he
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
  let f (x : M) := (e.linearEquiv x).symm
  -- The positive forms are pulled through the specified inverse on the same native fibers.
  let core (x : M) : InnerProductSpace.Core ℂ (F.Fiber x) := {
    inner := fun v w ↦ (h.toCore x).inner (f x v) (f x w)
    conj_inner_symm := fun v w ↦ (h.toCore x).conj_inner_symm _ _
    re_inner_nonneg := fun v ↦ (h.toCore x).re_inner_nonneg _
    add_left := by
      intro u v w
      rw [(f x).map_add]
      exact (h.toCore x).add_left _ _ _
    smul_left := by
      intro v w c
      change (h.toCore x).inner (f x (c • v)) (f x w) = _
      rw [(f x).map_smul]
      exact (h.toCore x).smul_left _ _ _
    definite := by
      intro v hv
      apply (f x).injective
      exact ((h.toCore x).definite _ hv).trans ((f x).map_zero.symm) }
  have hsmooth : ∀ (d : Trivialization (EuclideanSpace ℂ (Fin F.rank))
      (π (EuclideanSpace ℂ (Fin F.rank)) F.Fiber)) [MemTrivializationAtlas d],
      ∀ a b : Fin F.rank,
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ (core x).inner (d.symmL ℂ x (EuclideanSpace.single a 1))
            (d.symmL ℂ x (EuclideanSpace.single b 1))) d.baseSet := by
    intro d hd a b x hx
    obtain ⟨j, hj⟩ := A.covers x
    let i : B.Index := ⟨d, hd⟩
    let V := EuclideanSpace ℂ (Fin (A.rank j))
    let c := EuclideanSpace.equiv (Fin (A.rank j)) ℂ
    let v (k : Fin F.rank) (y : M) : F.Fiber y :=
      d.symmL ℂ y (EuclideanSpace.single k 1)
    let u (k : Fin F.rank) (y : M) : V := c.symm (A.chart j ⟨y, f y (v k y)⟩).2
    -- The atlas induced by the native bundle has exactly the native inverse frame vectors.
    have hframe (y : M) (hy : y ∈ d.baseSet) (k : Fin F.rank) :
        (B.frameLinearEquiv i y hy).symm (Pi.single k 1) = v k y := by
      apply (B.frameLinearEquiv i y hy).injective
      rw [LinearEquiv.apply_symm_apply]
      change Pi.single k 1 = (EuclideanSpace.equiv (Fin F.rank) ℂ)
        ((d ⟨y, d.symmL ℂ y (EuclideanSpace.single k 1)⟩).2)
      rw [← d.continuousLinearMapAt_apply_of_mem ℂ hy,
        d.continuousLinearMapAt_symmL hy]
      rfl
    have hu (k : Fin F.rank) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞
          (u k) (d.baseSet ∩ (A.chart j).baseSet) := by
      have hcolumn := (c.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
        |>.comp_contMDiffOn (he.2 i j k)
      apply hcolumn.congr
      intro y hy
      change u k y = c.symm (if hy' : y ∈ d.baseSet then
        (A.chart j ⟨y, f y ((B.frameLinearEquiv i y hy').symm (Pi.single k 1))⟩).2
          else 0)
      have hyd : y ∈ d.baseSet := hy.1
      rw [dite_eq_left hyd, hframe y hyd k]
    -- The original Gram operator computes the transported pairing on this overlap.
    have hgram := (A.contMDiffOn_hermitianGramOperator h hh j).mono
      (Set.inter_subset_right (s := d.baseSet))
    have happly : ContDiff ℝ ∞ (fun p : (V →L[ℂ] V) × V ↦ p.1 p.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hinner : ContDiff ℝ ∞ (fun p : V × V ↦ inner ℂ p.1 p.2) := contDiff_inner
    have hlocal := hinner.contMDiff.comp_contMDiffOn
      ((hu a).prodMk_space (happly.contMDiff.comp_contMDiffOn (hgram.prodMk_space (hu b))))
    have hpair := hlocal.congr (f₁ := fun y ↦ (core y).inner (v a y) (v b y)) (by
      intro y hy
      exact A.pairing_eq_hermitianGramOperator h j y hy.2 _ _)
    exact (hpair.contMDiffAt
      ((d.open_baseSet.inter (A.chart j).open_baseSet).mem_nhds ⟨hx, hj⟩)).contMDiffWithinAt
  refine ⟨⟨core, hsmooth, inferInstance⟩, ?_⟩
  intro x v w
  change (h.toCore x).inner ((e.linearEquiv x).symm (e.linearEquiv x v))
    ((e.linearEquiv x).symm (e.linearEquiv x w)) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end AtiyahSinger.SmoothComplexBundleAtlas
