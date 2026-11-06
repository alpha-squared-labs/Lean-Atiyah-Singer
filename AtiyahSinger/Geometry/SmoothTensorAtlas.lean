/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.SmoothAtlasSections
public import AtiyahSinger.Topology.BundleTensor

/-!
# Smooth tensor atlases on the original algebraic tensor fibers

Public module ID: M1417.

The original tensor total topology is retained. Charts are the actual tensor
charts of the supplied factor atlases, indexed by pairs of their indices.
Their ranks are local products; no global rank is assumed. Pure tensors have
exactly the product of the given factor coordinates. The resulting smooth
sections and later tensor connections use this same selected atlas.

Sources: Hatcher, Vector Bundles and K-Theory, pp.13--15, and SG II.3--4.
Smooth transitions are the Kronecker products of the original transitions.
The selected atlas and its section certificates refer to those same tensor
charts and actual fiber coordinates.
-/

@[expose] public noncomputable section

universe u v

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas.{u} (n := n) E)
  (B : SmoothComplexBundleAtlas.{v} (n := n) F)

attribute [local instance] ComplexBundle.tensorTopology

/-- The tensor chart chosen from the actual two original factor charts. -/
def tensorBundleChart (i : A.Index) (j : B.Index) :
    Trivialization (Fin (A.rank i * B.rank j) → ℂ)
      (π Unit (fun x ↦ E x ⊗[ℂ] F x)) :=
  (ComplexBundle.exists_tensor_trivialization (A.chart i) (B.chart j)
    (A.linear i) (B.linear j)).choose

/-- The original tensor charts form a covering smooth complex-linear atlas.
This grouped construction certificate concerns the one specified chart family. -/
theorem tensorBundleCharts_properties :
    (∀ x : M, ∃ p : A.Index × B.Index, x ∈ (tensorBundleChart A B p.1 p.2).baseSet) ∧
      (∀ (p q : A.Index × B.Index) (a : Fin (A.rank p.1 * B.rank p.2)),
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, Fin (A.rank q.1 * B.rank q.2) → ℂ) ∞
          (fun x : M ↦ (tensorBundleChart A B q.1 q.2
            ((tensorBundleChart A B p.1 p.2).toPartialEquiv.symm
              (x, Pi.single a 1))).2)
          ((tensorBundleChart A B p.1 p.2).baseSet ∩
            (tensorBundleChart A B q.1 q.2).baseSet)) := by
  /- Stage 1: choose a chart of each original factor containing x. The
  tensor chart has exactly their intersection as its base set, so these
  same charts cover M, including zero-rank components and the empty base.
  Stage 2: the pure-vector formula of exists_tensor_trivialization identifies
  each transition with the Kronecker product of the two factor transitions.
  Pure tensors span, so this determines every matrix column. Each entry is
  a product of the original smooth entries on the same fourfold overlap.
  Finite products and sums are smooth. The final tensor topology and the
  original chart inverses are already those of tensorBundleChart. -/
  classical
  have hspec (i : A.Index) (j : B.Index) :=
    (ComplexBundle.exists_tensor_trivialization (A.chart i) (B.chart j)
      (A.linear i) (B.linear j)).choose_spec
  constructor
  · intro x
    obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨j, hj⟩ := B.covers x
    exact ⟨(i, j), (hspec i j).1.symm ▸ ⟨hi, hj⟩⟩
  · intro p q a
    -- Each column is the pure tensor of the two original source-frame vectors.
    let aE := (finProdFinEquiv.symm a).1
    let aF := (finProdFinEquiv.symm a).2
    have hcolumn (x : M)
        (hx : x ∈ (tensorBundleChart A B p.1 p.2).baseSet ∩
          (tensorBundleChart A B q.1 q.2).baseSet)
        (b : Fin (A.rank q.1 * B.rank q.2)) :
        (tensorBundleChart A B q.1 q.2
          ((tensorBundleChart A B p.1 p.2).toPartialEquiv.symm
            (x, Pi.single a 1))).2 b =
          (A.chart q.1 ((A.chart p.1).toPartialEquiv.symm
            (x, Pi.single aE 1))).2 (finProdFinEquiv.symm b).1 *
          (B.chart q.2 ((B.chart p.2).toPartialEquiv.symm
            (x, Pi.single aF 1))).2 (finProdFinEquiv.symm b).2 := by
      have hp : x ∈ (A.chart p.1).baseSet ∩ (B.chart p.2).baseSet :=
        (hspec p.1 p.2).1 ▸ hx.1
      have hq : x ∈ (A.chart q.1).baseSet ∩ (B.chart q.2).baseSet :=
        (hspec q.1 q.2).1 ▸ hx.2
      let u := (A.frameLinearEquiv p.1 x hp.1).symm (Pi.single aE 1)
      let v := (B.frameLinearEquiv p.2 x hp.2).symm (Pi.single aF 1)
      have hu : (⟨x, u⟩ : TotalSpace Unit E) =
          (A.chart p.1).toPartialEquiv.symm (x, Pi.single aE 1) :=
        TotalSpace.mk_cast (F := Unit) (E := E) ((A.chart p.1).proj_symm_apply' hp.1) _
      have hv : (⟨x, v⟩ : TotalSpace Unit F) =
          (B.chart p.2).toPartialEquiv.symm (x, Pi.single aF 1) :=
        TotalSpace.mk_cast (F := Unit) (E := F) ((B.chart p.2).proj_symm_apply' hp.2) _
      have hsource : tensorBundleChart A B p.1 p.2 ⟨x, u ⊗ₜ[ℂ] v⟩ =
          (x, Pi.single a 1) := by
        apply Prod.ext
        · exact (tensorBundleChart A B p.1 p.2).proj_toFun _
            ((tensorBundleChart A B p.1 p.2).mem_source.mpr hx.1)
        · funext k
          obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
          change ((ComplexBundle.exists_tensor_trivialization _ _
            (A.linear p.1) (B.linear p.2)).choose ⟨x, u ⊗ₜ[ℂ] v⟩).2 _ = _
          rw [(hspec p.1 p.2).2.2 x hp u v i j]
          have hucoord : (A.chart p.1 ⟨x, u⟩).2 = Pi.single aE 1 :=
            (A.frameLinearEquiv p.1 x hp.1).apply_symm_apply _
          have hvcoord : (B.chart p.2 ⟨x, v⟩).2 = Pi.single aF 1 :=
            (B.frameLinearEquiv p.2 x hp.2).apply_symm_apply _
          rw [hucoord, hvcoord]
          have ha : a = finProdFinEquiv (aE, aF) :=
            (finProdFinEquiv.apply_symm_apply a).symm
          rw [ha]
          by_cases hi : i = aE <;> by_cases hj : j = aF <;>
            simp [hi, hj]
      have hinverse : (tensorBundleChart A B p.1 p.2).toPartialEquiv.symm
          (x, Pi.single a 1) = (⟨x, u ⊗ₜ[ℂ] v⟩ :
            TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x)) := by
        rw [← hsource]
        exact (tensorBundleChart A B p.1 p.2).toPartialEquiv.left_inv
          ((tensorBundleChart A B p.1 p.2).mem_source.mpr hx.1)
      rw [hinverse]
      have ht := (hspec q.1 q.2).2.2 x hq u v
        (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2
      simpa only [tensorBundleChart, Prod.mk.eta, Equiv.apply_symm_apply, hu, hv] using ht
    -- The original transition entries are smooth on the same fourfold overlap.
    apply contMDiffOn_pi_space.mpr
    intro b
    have hE := (contMDiffOn_pi_space.mp
      (A.contMDiffOn_coordChange p.1 q.1 aE) (finProdFinEquiv.symm b).1).mono
      (show (tensorBundleChart A B p.1 p.2).baseSet ∩
        (tensorBundleChart A B q.1 q.2).baseSet ⊆
          (A.chart p.1).baseSet ∩ (A.chart q.1).baseSet from by
        intro x hx
        exact ⟨((hspec p.1 p.2).1 ▸ hx.1).1, ((hspec q.1 q.2).1 ▸ hx.2).1⟩)
    have hF := (contMDiffOn_pi_space.mp
      (B.contMDiffOn_coordChange p.2 q.2 aF) (finProdFinEquiv.symm b).2).mono
      (show (tensorBundleChart A B p.1 p.2).baseSet ∩
        (tensorBundleChart A B q.1 q.2).baseSet ⊆
          (B.chart p.2).baseSet ∩ (B.chart q.2).baseSet from by
        intro x hx
        exact ⟨((hspec p.1 p.2).1 ▸ hx.1).2, ((hspec q.1 q.2).1 ▸ hx.2).2⟩)
    exact ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
      (hE.prodMk_space hF)).congr (fun x hx ↦ hcolumn x hx b)

/-- The smooth tensor atlas on the original fibers and original tensor topology. -/
def tensorSmoothAtlas : SmoothComplexBundleAtlas.{max u v} (n := n)
    (fun x ↦ E x ⊗[ℂ] F x) where
  Index := A.Index × B.Index
  rank p := A.rank p.1 * B.rank p.2
  chart p := tensorBundleChart A B p.1 p.2
  covers := (tensorBundleCharts_properties A B).1
  linear p := (ComplexBundle.exists_tensor_trivialization
    (A.chart p.1) (B.chart p.2) (A.linear p.1) (B.linear p.2)).choose_spec.2.1
  contMDiffOn_coordChange := (tensorBundleCharts_properties A B).2

/-- Products of original smooth sections are smooth in those same tensor charts. -/
theorem isSmoothSection_tensor (s : A.smoothSections) (t : B.smoothSections) :
    (tensorSmoothAtlas A B).IsSmoothSection (fun x ↦ s.val x ⊗ₜ[ℂ] t.val x) := by
  /- On each selected tensor chart, the actual coordinate formula is the
  product s_a(x)t_b(x). The original sections have smooth coordinates in
  the two factor charts; restriction to their intersection and multiplication
  give smoothness. The chart's exact base set excludes any unsupported claim
  of smooth zero extension at its boundary. -/
  intro p
  have hspec := (ComplexBundle.exists_tensor_trivialization
    (A.chart p.1) (B.chart p.2) (A.linear p.1) (B.linear p.2)).choose_spec
  change ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    𝓘(ℝ, Fin (A.rank p.1 * B.rank p.2) → ℂ) ∞
    (fun x ↦ (tensorBundleChart A B p.1 p.2 ⟨x, s.val x ⊗ₜ[ℂ] t.val x⟩).2)
    (tensorBundleChart A B p.1 p.2).baseSet
  apply contMDiffOn_pi_space.mpr
  intro a
  have hE := (contMDiffOn_pi_space.mp (s.property p.1)
    (finProdFinEquiv.symm a).1).mono
    (show (tensorBundleChart A B p.1 p.2).baseSet ⊆ (A.chart p.1).baseSet from
      fun x hx ↦ (hspec.1 ▸ hx).1)
  have hF := (contMDiffOn_pi_space.mp (t.property p.2)
    (finProdFinEquiv.symm a).2).mono
    (show (tensorBundleChart A B p.1 p.2).baseSet ⊆ (B.chart p.2).baseSet from
      fun x hx ↦ (hspec.1 ▸ hx).2)
  apply ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
      (hE.prodMk_space hF)).congr
  intro x hx
  dsimp only [Function.comp_apply]
  simpa only [tensorBundleChart, Prod.mk.eta, Equiv.apply_symm_apply] using
    hspec.2.2 x (hspec.1 ▸ hx) (s.val x) (t.val x)
      (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

/-- The actual pure tensor of two smooth sections in the specified tensor atlas. -/
def tensorSmoothSection (s : A.smoothSections) (t : B.smoothSections) :
    (tensorSmoothAtlas A B).smoothSections :=
  ⟨fun x ↦ s.val x ⊗ₜ[ℂ] t.val x, isSmoothSection_tensor A B s t⟩

end AtiyahSinger
