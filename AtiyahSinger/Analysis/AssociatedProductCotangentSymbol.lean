/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.ProductSymbolCutoff
public import AtiyahSinger.Geometry.AssociatedSphereProductChart

import AtiyahSinger.Analysis.FiniteAtlasProductCutoff

/-!
# Horizontal covectors in actual associated product transitions

The cotangent transform of the actual regularized product symbol, evaluated
on a horizontal covector, is the base symbol transformed by the original base
chart change. The original sphere cutoff is evaluated in the source sphere
coordinate and is retained explicitly. The proof uses the base projection of
the actual associated trivializations, so it allows their base-dependent sphere
transition and does not replace them by a fixed product map.

This exact formula is the coordinate input to the finite partition cancellation
in the horizontal reverse estimate. It does not assert cancellation of a single
sphere cutoff or discard any lower-order coordinate/frame remainder.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set
open scoped ContDiff Manifold Topology

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r k l : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

set_option maxSynthPendingDepth 30

set_option maxHeartbeats 1600000 in

/-- The actual associated chart transition retains the source cutoff on horizontal covectors. -/
theorem cotangentSymbol_productCutoffSymbol_associatedSphereProductChart
    (b₁ b₂ : B)
    (c₁ c₂ : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (hc₁ : c₁ ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (hc₂ : c₂ ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (d₁ d₂ : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
    (hd₁ : d₁ ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
    (hd₂ : d₂ ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
    (a : SymbolFunction n k l) (χ : EuclideanSpace ℝ (Fin r) → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let e := (associatedSphereProductChart S b₁ c₁ d₁).symm.trans
      (associatedSphereProductChart S b₂ c₂ d₂)
    ∀ z ∈ e.target, ∀ ξ : EuclideanSpace ℝ (Fin n),
      cotangentSymbol e (productCutoffSymbol a χ ε) z (split.symm (ξ, 0)) =
        (χ (split (e.symm z)).2 : ℂ) •
          a (split (e.symm z)).1
            ((fderiv ℝ (c₁.symm.trans c₂) (split (e.symm z)).1).adjoint ξ) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin r)
  let H := EuclideanSpace ℝ (Fin (n + r))
  let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
  let base : Z → B := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let split : H ≃L[ℝ] X × Y := EuclideanSpace.finAddEquivProd
  let pr : H →L[ℝ] X := (ContinuousLinearMap.fst ℝ X Y).comp split.toContinuousLinearMap
  let C₁ := associatedSphereProductChart S b₁ c₁ d₁
  let C₂ := associatedSphereProductChart S b₂ c₂ d₂
  let e := C₁.symm.trans C₂
  let f := c₁.symm.trans c₂
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  change ∀ z ∈ e.target, ∀ ξ : X, _
  intro z hz ξ
  -- Both actual product charts have the unchanged original bundle projection as first factor.
  have hchart (b : B) (c : OpenPartialHomeomorph B X)
      (d : OpenPartialHomeomorph (OrthogonalSphere r) Y) (w : Z)
      (hw : w ∈ (associatedSphereProductChart S b c d).source) :
      base w ∈ c.source ∧ pr (associatedSphereProductChart S b c d w) = c (base w) := by
    let t := associatedSphereTrivialization S b
    have ht : w ∈ t.source := hw.1.1
    have hc : (t w).1 ∈ c.source := hw.1.2.1
    rw [t.coe_fst ht] at hc
    refine ⟨hc, ?_⟩
    change (split (split.symm ((c.prod d) (t w)))).1 = c (base w)
    rw [split.apply_symm_apply]
    change c (t w).1 = c (base w)
    rw [t.coe_fst ht]
  have hinverse (w : H) (hw : w ∈ C₁.target) : base (C₁.symm w) = c₁.symm (pr w) := by
    have hc := hchart b₁ c₁ d₁ (C₁.symm w) (C₁.map_target hw)
    calc
      _ = c₁.symm (c₁ (base (C₁.symm w))) := (c₁.left_inv hc.1).symm
      _ = c₁.symm (pr (C₁ (C₁.symm w))) := congrArg c₁.symm hc.2.symm
      _ = _ := by rw [C₁.right_inv hw]
  have hbase (w : H) (hw : w ∈ e.source) : pr w ∈ f.source ∧ pr (e w) = f (pr w) := by
    have h₁ := hchart b₁ c₁ d₁ (C₁.symm w) (C₁.map_target hw.1)
    have h₂ := hchart b₂ c₂ d₂ (C₁.symm w) hw.2
    have hcoord : pr w = c₁ (base (C₁.symm w)) := by
      have hc : pr (C₁ (C₁.symm w)) = c₁ (base (C₁.symm w)) := h₁.2
      rwa [C₁.right_inv hw.1] at hc
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hcoord]
      exact c₁.map_source h₁.1
    · change c₁.symm (pr w) ∈ c₂.source
      rw [← hinverse w hw.1]
      exact h₂.1
    · change pr (C₂ (C₁.symm w)) = c₂ (c₁.symm (pr w))
      rw [h₂.2, hinverse w hw.1]
  -- Compatibility gives smooth actual transitions; differentiation of the first factor is exact.
  have hC₁ := associatedSphereProductChart_mem_maximalAtlas S b₁ c₁ hc₁ d₁ hd₁
  have hC₂ := associatedSphereProductChart_mem_maximalAtlas S b₂ c₂ hc₂ d₂ hd₂
  have he : ContDiffOn ℝ ∞ e e.source := by
    intro w hw
    exact (((contMDiffAt_of_mem_maximalAtlas hC₂ hw.2).comp w
      (contMDiffAt_symm_of_mem_maximalAtlas hC₁ hw.1)).contDiffAt).contDiffWithinAt
  have hf : ContDiffOn ℝ ∞ f f.source := by
    intro w hw
    have hc := (contMDiffAt_of_mem_maximalAtlas
      (subset_maximalAtlas (I := 𝓡 n) (n := ∞) hc₂) hw.2).comp w
        (contMDiffAt_symm_of_mem_maximalAtlas
          (subset_maximalAtlas (I := 𝓡 n) (n := ∞) hc₁) hw.1)
    exact hc.contDiffAt.contDiffWithinAt
  let w := e.symm z
  have hw : w ∈ e.source := e.map_target hz
  have heD : DifferentiableAt ℝ e w :=
    (he.contDiffAt (e.open_source.mem_nhds hw)).differentiableAt (by simp)
  have hfD : DifferentiableAt ℝ f (pr w) :=
    (hf.contDiffAt (f.open_source.mem_nhds (hbase w hw).1)).differentiableAt (by simp)
  have hnear : (fun y ↦ pr (e y)) =ᶠ[𝓝 w] (fun y ↦ f (pr y)) :=
    Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hw) (fun y hy ↦ (hbase y hy).2)
  have hder : pr.comp (fderiv ℝ e w) = (fderiv ℝ f (pr w)).comp pr := by
    have hd := hnear.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (pr ∘ e) w = fderiv ℝ (f ∘ pr) w at hd
    rw [fderiv_comp w pr.differentiableAt heD,
      fderiv_comp w hfD pr.differentiableAt] at hd
    simpa only [ContinuousLinearMap.fderiv] using hd
  -- Euclidean concatenation identifies horizontal Riesz covectors with the first projection.
  have hinner (η : X) (u : H) :
      inner ℝ (split.symm (η, 0)) u = inner ℝ η (pr u) := by
    have hleft (i : Fin n) : split.symm (η, 0) (Fin.castAdd r i) = η i :=
      congrArg (fun p : X × Y ↦ p.1 i) (split.apply_symm_apply (η, 0))
    have hright (j : Fin r) : split.symm (η, 0) (Fin.natAdd n j) = 0 :=
      congrArg (fun p : X × Y ↦ p.2 j) (split.apply_symm_apply (η, 0))
    change (∑ i : Fin (n + r), u i * split.symm (η, 0) i) =
      ∑ i : Fin n, pr u i * η i
    rw [Fin.sum_univ_add]
    simp only [hleft, hright, mul_zero, Finset.sum_const_zero, add_zero]
    rfl
  have hcovector : (fderiv ℝ e w).adjoint (split.symm (ξ, 0)) =
      split.symm ((fderiv ℝ f (pr w)).adjoint ξ, 0) := by
    apply ext_inner_right ℝ
    intro u
    rw [ContinuousLinearMap.adjoint_inner_left, hinner, hinner]
    have hd := congrArg (fun L : H →L[ℝ] X ↦ L u) hder
    change pr (fderiv ℝ e w u) = fderiv ℝ f (pr w) (pr u) at hd
    rw [hd, ContinuousLinearMap.adjoint_inner_left]
  -- The positive product cutoff is exactly one on this horizontal frequency, even at zero.
  change productCutoffSymbol a χ ε w ((fderiv ℝ e w).adjoint (split.symm (ξ, 0))) = _
  rw [hcovector]
  change (productFrequencyCutoff ε
    ‖(split (split.symm ((fderiv ℝ f (pr w)).adjoint ξ, 0))).1‖
    ‖(split (split.symm ((fderiv ℝ f (pr w)).adjoint ξ, 0))).2‖ : ℂ) •
      ((χ (split w).2 : ℂ) • a (split w).1
        (split (split.symm ((fderiv ℝ f (pr w)).adjoint ξ, 0))).1) =
      (χ (split w).2 : ℂ) • a (pr w) ((fderiv ℝ f (pr w)).adjoint ξ)
  rw [split.apply_symm_apply, norm_zero]
  rw [productFrequencyCutoff_eq_one_of_mul_le ε _ 0 hε (norm_nonneg _) le_rfl
    (by simpa only [mul_zero] using norm_nonneg ((fderiv ℝ f (pr w)).adjoint ξ))]
  simp only [Complex.ofReal_one, one_smul]
  rfl

end AtiyahSinger
