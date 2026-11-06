/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPrincipalSymbol

import AtiyahSinger.Geometry.AtlasFrame

/-!
# Joint smoothness of the locally finite-rank differential principal symbol

Public module ID: M0277.

D03: the symbol is a smooth linear map from the actual cotangent pullback of
the source bundle to the actual cotangent pullback of the target bundle.
The theorem spells out its local matrix evaluation, using the same selected
smooth atlases and pullback by the derivative of the manifold chart. All real
frequencies are included, including the zero section. No fiber norm, common
global rank, metric or compactness is added to the bundle data.

Source: Spin Geometry III.1, Definitions 1.1-1.3 and formulas (1.2)-(1.5),
pp.167-168. The project uses order at most m and D_j = -i partial_j; hence
the top coefficient polynomial has no additional factor of i^m.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

namespace AtlasDifferentialOperator

/-- The principal symbol is jointly smooth in the original base and cotangent coordinates.
The inverse source chart supplies the actual input vector, without a new fiber model. -/
theorem contDiffOn_principalSymbol_in_chart {m : ℕ} (P : AtlasDifferentialOperator A B m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (i : A.Index) (j : B.Index) (v : Fin (A.rank i) → ℂ) :
    ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        let w := (A.chart i).toPartialEquiv.symm (c.symm z.1, v)
        (B.chart j ⟨w.proj, P.principalSymbol w.proj
          ((innerSL ℝ z.2).comp
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
              𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c w.proj)) w.snd⟩).2)
      ((c.target ∩ c.symm ⁻¹' (A.chart i).baseSet ∩
        c.symm ⁻¹' (B.chart j).baseSet) ×ˢ Set.univ) := by
  /- Stage 1: on this overlap the inverse source trivialization has base point
  c.symm z.1 and source coordinate exactly v. The inverse function identity for
  the manifold chart recovers z.2 from the displayed real covector. Thus the
  local principal-symbol specification identifies this expression with the
  top coefficient polynomial in the same source and target frames.
  Stage 2: near every base point choose a finite differential expression.
  Its coefficients are smooth and its frequency monomials are polynomial, so
  evaluation at the fixed v is jointly real smooth, including frequency zero.
  Smoothness is local, and the representing neighborhoods cover the displayed
  domain. Taking v through a finite basis gives every local matrix column;
  linearity gives the standard smooth pullback bundle map on all input vectors.
  The two local fiber ranks may differ and need not be fixed on other charts. -/
  classical
  intro z hz
  -- Choose one original expression around this point, with the given two frame indices.
  have hx : c.symm z.1 ∈ c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet :=
    ⟨⟨c.map_target hz.1.1.1, hz.1.1.2⟩, hz.1.2⟩
  obtain ⟨U, hU, hxU, Q, hQ⟩ :=
    P.isAtlasDifferentialOperator c hc i j (c.symm z.1) hx
  have hUs : U ⊆ c.source := fun y hy ↦ (hQ.1 hy).1.1
  have hV : IsOpen (c '' U) := c.isOpen_image_of_subset_source hU hUs
  have hzV : z.1 ∈ c '' U := ⟨c.symm z.1, hxU, c.right_inv hz.1.1.1⟩
  let eA := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  let eB := EuclideanSpace.equiv (Fin (B.rank j)) ℂ
  -- Smooth coefficient maps and finite monomials give full frequency smoothness locally.
  have htop : ContDiffOn ℝ ∞ (Function.uncurry Q.principalSymbol)
      ((c '' U) ×ˢ Set.univ) := by
    unfold CoordinateDifferentialOperator.principalSymbol Function.uncurry
    apply ContDiffOn.sum
    intro α _
    have hmonomial : ContDiff ℝ ∞
        (fun w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          ∏ a : Fin m, w.2 (α a)) := by
      exact contDiff_prod fun a _ ↦
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) (α a)).contDiff.comp contDiff_snd
    exact hmonomial.contDiffOn.smul
      ((Q.smooth_coefficient ⟨m, Nat.lt_succ_self m⟩ α).comp contDiffOn_fst
        (fun w hw ↦ hw.1))
  have htopAt : ContDiffAt ℝ ∞
      (fun w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        Q.principalSymbol w.1 w.2 (eA.symm v)) z :=
    (htop.contDiffAt ((hV.prod isOpen_univ).mem_nhds
      ⟨hzV, Set.mem_univ z.2⟩)).continuousLinearMap_comp
        ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin (B.rank j)))
          (eA.symm v)).restrictScalars ℝ)
  apply ContDiffAt.contDiffWithinAt
  apply (htopAt.continuousLinearMap_comp
    (eB.toContinuousLinearMap.restrictScalars ℝ)).congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt (hV.mem_nhds hzV)] with w hw
  obtain ⟨y, hy, hcy⟩ := hw
  have hyc := hUs hy
  have hyi := (hQ.1 hy).1.2
  have hbase : c.symm w.1 = y := by rw [← hcy, c.left_inv hyc]
  -- The actual inverse atlas chart lies over y and has precisely the given coordinate v.
  have hpoint : (A.chart i).toPartialEquiv.symm (y, v) =
      (⟨y, (A.frameLinearEquiv i y hyi).symm v⟩ : TotalSpace Unit E) := by
    exact (TotalSpace.mk_cast (F := Unit) (E := E)
      ((A.chart i).proj_symm_apply' (x := v) hyi)
      ((A.chart i).toOpenPartialHomeomorph.symm (y, v)).2).symm
  change (let u := (A.chart i).toPartialEquiv.symm (c.symm w.1, v)
    (B.chart j ⟨u.proj, P.principalSymbol u.proj
      ((innerSL ℝ w.2).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c u.proj)) u.snd⟩).2) =
      eB (Q.principalSymbol w.1 w.2 (eA.symm v))
  rw [hbase, hpoint]
  have hcov : covectorInChart c y ((innerSL ℝ w.2).comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c y)) = w.2 := by
    have hderiv := (mdifferentiable_of_mem_atlas
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hc).comp_symm_deriv (c.map_source hyc)
    rw [c.left_inv hyc] at hderiv
    ext a
    change inner ℝ w.2 ((mfderiv _ _ c y)
      ((mfderiv _ _ c.symm (c y)) (EuclideanSpace.single a 1))) = w.2 a
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) ↦ L (EuclideanSpace.single a 1)) hderiv
    change (mfderiv _ _ c y) ((mfderiv _ _ c.symm (c y))
      (EuclideanSpace.single a 1)) = EuclideanSpace.single a 1 at h
    rw [h]
    simp [EuclideanSpace.inner_single_right]
  have hspec := P.hasAtlasPrincipalSymbol c hc i j U hU Q hQ y hy
    ((innerSL ℝ w.2).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c y)) ((A.frameLinearEquiv i y hyi).symm v)
  have hcoords : (A.chart i ⟨y, (A.frameLinearEquiv i y hyi).symm v⟩).2 = v :=
    (A.frameLinearEquiv i y hyi).apply_symm_apply v
  rw [hcov, hcoords, hcy] at hspec
  exact eB.symm.injective (hspec.trans (eB.symm_apply_apply _).symm)

end AtlasDifferentialOperator

end AtiyahSinger
