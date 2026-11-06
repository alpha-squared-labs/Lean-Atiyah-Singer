/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasNativeMetric
public import AtiyahSinger.Geometry.SmoothAtlasSum
public import AtiyahSinger.Topology.HermitianMetricSum

/-!
# A native model of the prescribed smooth orthogonal sum

Public module ID: M1408.

The sum uses the two original atlases and their original Hermitian metrics.
Over a compact Hausdorff base with specified constant ranks, one native model
carries both smooth comparison maps and the exact orthogonal sum pairing.
Thus subsequent graded operators, their adjoints, and the symbol
bundle comparison can use the same model and the same metric.

This is the standard smooth orthogonal direct sum of SG III.1. The product
fiber topology is retained; its supremum norm is never treated as a Hilbert norm.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] sumTopology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The dependent sum-frame inverse and both Gram coordinate identities are checked together.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Smoothness is checked in the original concatenated coordinates.
/-- The orthogonal sum of the specified smooth metrics is smooth in their sum atlas. -/
theorem isSmoothHermitianMetric_sum
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (h : ContinuousHermitianMetric E) (k : ContinuousHermitianMetric F)
    (hh : A.IsSmoothHermitianMetric h) (hk : B.IsSmoothHermitianMetric k) :
    (A.sum B).IsSmoothHermitianMetric (h.sum k) := by
  classical
  rintro ⟨i, j⟩ a b
  let c : ((Fin (A.rank i) → ℂ) × (Fin (B.rank j) → ℂ)) ≃L[ℂ]
      (Fin (A.rank i + B.rank j) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin (A.rank i)) (Fin (B.rank j)) ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (A.rank i + B.rank j) ↦ ℂ)
        finSumFinEquiv)).toContinuousLinearEquiv
  let u := c.symm (Pi.single a 1)
  let v := c.symm (Pi.single b 1)
  let e := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  let f := EuclideanSpace.equiv (Fin (B.rank j)) ℂ
  -- Each diagonal block is the original smooth Gram operator on constant coordinates.
  have hleft : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ inner ℂ (e.symm u.1) (A.hermitianGramOperator h i x (e.symm v.1)))
      ((A.chart i).baseSet ∩ (B.chart j).baseSet) := by
    have hgram := (A.contMDiffOn_hermitianGramOperator h hh i).mono
      (Set.inter_subset_left (t := (B.chart j).baseSet))
    have happly : ContDiff ℝ ∞ (fun T : EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
        EuclideanSpace ℂ (Fin (A.rank i)) ↦ T (e.symm v.1)) :=
      (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
    exact contDiff_inner.contMDiff.comp_contMDiffOn
      (contMDiffOn_const.prodMk_space (happly.contMDiff.comp_contMDiffOn hgram))
  have hright : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ inner ℂ (f.symm u.2) (B.hermitianGramOperator k j x (f.symm v.2)))
      ((A.chart i).baseSet ∩ (B.chart j).baseSet) := by
    have hgram := (B.contMDiffOn_hermitianGramOperator k hk j).mono
      (Set.inter_subset_right (s := (A.chart i).baseSet))
    have happly : ContDiff ℝ ∞ (fun T : EuclideanSpace ℂ (Fin (B.rank j)) →L[ℂ]
        EuclideanSpace ℂ (Fin (B.rank j)) ↦ T (f.symm v.2)) :=
      (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
    exact contDiff_inner.contMDiff.comp_contMDiffOn
      (contMDiffOn_const.prodMk_space (happly.contMDiff.comp_contMDiffOn hgram))
  apply (hleft.add hright).congr
  intro x hx
  have hx' : x ∈ ((A.sum B).chart (i, j)).baseSet := hx
  rw [dite_eq_left hx']
  -- Inverting the same concatenated frame recovers exactly the two original vectors.
  have hframe (w : Fin (A.rank i + B.rank j) → ℂ) :
      ((A.sum B).frameLinearEquiv (i, j) x hx).symm w =
        ((A.frameLinearEquiv i x hx.1).symm (c.symm w).1,
          (B.frameLinearEquiv j x hx.2).symm (c.symm w).2) := by
    apply ((A.sum B).frameLinearEquiv (i, j) x hx).injective
    rw [LinearEquiv.apply_symm_apply]
    change w = c
      ((A.frameLinearEquiv i x hx.1) ((A.frameLinearEquiv i x hx.1).symm (c.symm w).1),
        (B.frameLinearEquiv j x hx.2) ((B.frameLinearEquiv j x hx.2).symm (c.symm w).2))
    simp only [LinearEquiv.apply_symm_apply, Prod.eta]
    exact (c.apply_symm_apply w).symm
  change (h.toCore x).inner
      (((A.sum B).frameLinearEquiv (i, j) x hx).symm (Pi.single a 1)).1
      (((A.sum B).frameLinearEquiv (i, j) x hx).symm (Pi.single b 1)).1 +
    (k.toCore x).inner
      (((A.sum B).frameLinearEquiv (i, j) x hx).symm (Pi.single a 1)).2
      (((A.sum B).frameLinearEquiv (i, j) x hx).symm (Pi.single b 1)).2 = _
  rw [hframe, hframe]
  rw [A.pairing_eq_hermitianGramOperator h i x hx.1,
    B.pairing_eq_hermitianGramOperator k j x hx.2]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

variable [CompactSpace M] [T2Space M]

set_option maxSynthPendingDepth 40 in
/-- One native sum model retains both smooth comparison maps and the exact original pairing. -/
theorem exists_native_orthogonal_sum
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F) (r s : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E x) = r)
    (hs : ∀ x : M, Module.finrank ℂ (F x) = s)
    (h : ContinuousHermitianMetric E) (k : ContinuousHermitianMetric F)
    (hh : A.IsSmoothHermitianMetric h) (hk : B.IsSmoothHermitianMetric k) :
    ∃ N : SmoothFiniteComplexBundle (n := n) M, N.rank = r + s ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
      ∃ e : Iso (E ×ᵇ F) N.Fiber,
        IsSmoothAtlasBundleMap (A.sum B)
          (nativeSmoothComplexBundleAtlas (n := n) (r := N.rank) N.Fiber)
          e.toHom.linearMap ∧
        IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n) (r := N.rank) N.Fiber)
          (A.sum B) e.symm.toHom.linearMap ∧
        ∃ l : SmoothHermitianMetric (n := n) (r := N.rank) N.Fiber,
          ∀ x (u v : E x × F x), l.pairing x (e.linearEquiv x u) (e.linearEquiv x v) =
            (h.toCore x).inner u.1 v.1 + (k.toCore x).inner u.2 v.2 := by
  let := A.isFiniteRank
  let := B.isFiniteRank
  have hdim (x : M) : Module.finrank ℂ ((E ×ᵇ F) x) = r + s := by
    let := finite_fiber (E := E) x
    let := finite_fiber (E := F) x
    change Module.finrank ℂ (E x × F x) = r + s
    rw [Module.finrank_prod, hr x, hs x]
  -- Choose the model once, then transport the original sum metric through its same inverse.
  obtain ⟨N, hN, e, he, hei⟩ := (A.sum B).exists_native_model_with_atlasMaps (r + s) hdim
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  obtain ⟨l, hl⟩ := (A.sum B).exists_native_smoothHermitianMetric (h.sum k)
    (A.isSmoothHermitianMetric_sum B h k hh hk) N e hei
  exact ⟨N, hN, e, he, hei, l, hl⟩

end AtiyahSinger.SmoothComplexBundleAtlas
