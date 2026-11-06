/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.ProductSymbolCutoff
public import AtiyahSinger.Geometry.AssociatedSphereProductChart

/-!
# Compact bounds for the actual associated product cotangent blocks

Public module ID: M0103.

The original associated product chart transition has a triangular derivative.
Its base and vertical diagonal blocks and their adjoints have uniform inverse
bounds on every compact subset of the exact overlap. The mixed block is
bounded on that same set. These are the actual blocks used by the full-symbol
cutoff formula, not a replacement product transition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set
open scoped ContDiff Manifold Topology

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

set_option maxSynthPendingDepth 30

set_option maxHeartbeats 2400000 in

/-- The diagonal cotangent blocks have upper and inverse bounds on each compact window;
the mixed block has an upper bound. -/
theorem exists_associatedSphereProductChart_cotangent_block_bounds
    (b₁ b₂ : B)
    (c₁ c₂ : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (hc₁ : c₁ ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (hc₂ : c₂ ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (d₁ d₂ : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
    (hd₁ : d₁ ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
    (hd₂ : d₂ ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
    (K : Set (EuclideanSpace ℝ (Fin (n + r)))) (hK : IsCompact K) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let e := (associatedSphereProductChart S b₁ c₁ d₁).symm.trans
      (associatedSphereProductChart S b₂ c₂ d₂)
    let pr := (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin r))).comp split.toContinuousLinearMap
    let qr := (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin r))).comp split.toContinuousLinearMap
    let inx := split.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin r)))
    let iny := split.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin r)))
    K ⊆ e.target → ∃ D : ℝ, 1 ≤ D ∧ ∀ z ∈ K,
      let A := fderiv ℝ (c₁.symm.trans c₂) (pr (e.symm z))
      let B := qr.comp ((fderiv ℝ e (e.symm z)).comp inx)
      let V := qr.comp ((fderiv ℝ e (e.symm z)).comp iny)
      ‖A.adjoint‖ ≤ D ∧ (∀ ξ, ‖ξ‖ ≤ D * ‖A.adjoint ξ‖) ∧
        ‖B.adjoint‖ ≤ D ∧ ‖V.adjoint‖ ≤ D ∧ ∀ η, ‖η‖ ≤ D * ‖V.adjoint η‖ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin r)
  let H := EuclideanSpace ℝ (Fin (n + r))
  let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
  let base : Z → B := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let split : H ≃L[ℝ] X × Y := EuclideanSpace.finAddEquivProd
  let pr : H →L[ℝ] X := (ContinuousLinearMap.fst ℝ X Y).comp split.toContinuousLinearMap
  let qr : H →L[ℝ] Y := (ContinuousLinearMap.snd ℝ X Y).comp split.toContinuousLinearMap
  let inx : X →L[ℝ] H := split.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ X Y)
  let iny : Y →L[ℝ] H := split.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ X Y)
  let C₁ := associatedSphereProductChart S b₁ c₁ d₁
  let C₂ := associatedSphereProductChart S b₂ c₂ d₂
  let e := C₁.symm.trans C₂
  let f := c₁.symm.trans c₂
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  change K ⊆ e.target → _
  intro hKe
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
  have hei : ContDiffOn ℝ ∞ e.symm e.target := by
    intro z hz
    exact (((contMDiffAt_of_mem_maximalAtlas hC₁ hz.2).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hC₂ hz.1)).contDiffAt).contDiffWithinAt
  have hfi : ContDiffOn ℝ ∞ f.symm f.target := by
    intro z hz
    have hc := (contMDiffAt_of_mem_maximalAtlas
      (subset_maximalAtlas (I := 𝓡 n) (n := ∞) hc₁) hz.2).comp z
        (contMDiffAt_symm_of_mem_maximalAtlas
          (subset_maximalAtlas (I := 𝓡 n) (n := ∞) hc₂) hz.1)
    exact hc.contDiffAt.contDiffWithinAt
  have htarget (z : H) (hz : z ∈ e.target) :
      pr z ∈ f.target ∧ f (pr (e.symm z)) = pr z := by
    have hb := hbase (e.symm z) (e.map_target hz)
    have heq : f (pr (e.symm z)) = pr z := by
      simpa only [e.right_inv hz] using hb.2.symm
    exact ⟨heq ▸ f.map_source hb.1, heq⟩
  -- Differentiate the actual inverse identities; the resulting inverse maps are explicit.
  have hinverse {m : ℕ}
      (g : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)))
      (hg : ContDiffOn ℝ ∞ g g.source) (hgi : ContDiffOn ℝ ∞ g.symm g.target)
      (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ g.target) :
      (fderiv ℝ g (g.symm z)).comp (fderiv ℝ g.symm z) = ContinuousLinearMap.id ℝ _ ∧
        (fderiv ℝ g.symm z).comp (fderiv ℝ g (g.symm z)) =
          ContinuousLinearMap.id ℝ _ := by
    have hd := (hg.contDiffAt (g.open_source.mem_nhds (g.map_target hz))).differentiableAt
      (by simp)
    have hi := (hgi.contDiffAt (g.open_target.mem_nhds hz)).differentiableAt (by simp)
    constructor
    · apply (hd.hasFDerivAt.comp z hi.hasFDerivAt).unique
      apply (hasFDerivAt_id z).congr_of_eventuallyEq
      filter_upwards [g.open_target.mem_nhds hz] with y hy
      exact g.right_inv hy
    · have hi' : HasFDerivAt g.symm (fderiv ℝ g.symm z) (g (g.symm z)) := by
        simpa only [g.right_inv hz] using hi.hasFDerivAt
      apply (hi'.comp (g.symm z) hd.hasFDerivAt).unique
      apply (hasFDerivAt_id (g.symm z)).congr_of_eventuallyEq
      filter_upwards [g.open_source.mem_nhds (g.map_target hz)] with y hy
      exact g.left_inv hy
  let F (z : H) : H →L[ℝ] H := fderiv ℝ e (e.symm z)
  let Fi (z : H) : H →L[ℝ] H := fderiv ℝ e.symm z
  let A (z : H) : X →L[ℝ] X := fderiv ℝ f (pr (e.symm z))
  let Ai (z : H) : X →L[ℝ] X := fderiv ℝ f.symm (pr z)
  let B (z : H) : X →L[ℝ] Y := qr.comp ((F z).comp inx)
  let V (z : H) : Y →L[ℝ] Y := qr.comp ((F z).comp iny)
  let Vi (z : H) : Y →L[ℝ] Y := qr.comp ((Fi z).comp iny)
  have hF (z : H) (hz : z ∈ e.target) :
      (F z).comp (Fi z) = ContinuousLinearMap.id ℝ H ∧
        (Fi z).comp (F z) = ContinuousLinearMap.id ℝ H := hinverse e he hei z hz
  have hA (z : H) (hz : z ∈ e.target) :
      (A z).comp (Ai z) = ContinuousLinearMap.id ℝ X ∧
        (Ai z).comp (A z) = ContinuousLinearMap.id ℝ X := by
    have hb := hbase (e.symm z) (e.map_target hz)
    have h := hinverse f hf hfi (pr z) (htarget z hz).1
    have heq : f.symm (pr z) = pr (e.symm z) := by
      rw [← (htarget z hz).2, f.left_inv hb.1]
    simpa only [heq, A, Ai] using h
  have htriangular (z : H) (hz : z ∈ e.target) : pr.comp (F z) = (A z).comp pr := by
    let w := e.symm z
    have hw : w ∈ e.source := e.map_target hz
    have heD : DifferentiableAt ℝ e w :=
      (he.contDiffAt (e.open_source.mem_nhds hw)).differentiableAt (by simp)
    have hfD : DifferentiableAt ℝ f (pr w) :=
      (hf.contDiffAt (f.open_source.mem_nhds (hbase w hw).1)).differentiableAt (by simp)
    have hnear : (fun y ↦ pr (e y)) =ᶠ[𝓝 w] (fun y ↦ f (pr y)) :=
      Filter.eventuallyEq_of_mem (e.open_source.mem_nhds hw) (fun y hy ↦ (hbase y hy).2)
    have hd := hnear.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (pr ∘ e) w = fderiv ℝ (f ∘ pr) w at hd
    rw [fderiv_comp w pr.differentiableAt heD,
      fderiv_comp w hfD pr.differentiableAt] at hd
    simpa only [ContinuousLinearMap.fderiv] using hd
  have hpriny (η : Y) : pr (iny η) = 0 := by
    change (split (split.symm (0, η))).1 = 0
    rw [split.apply_symm_apply]
  have hqriny (η : Y) : qr (iny η) = η := by
    change (split (split.symm (0, η))).2 = η
    rw [split.apply_symm_apply]
  have hsplit (u : H) (hu : pr u = 0) : u = iny (qr u) := by
    apply split.injective
    change split u = split (split.symm (0, qr u))
    rw [split.apply_symm_apply]
    exact Prod.ext hu rfl
  -- The inverse full derivative restricts to the same vertical block.
  have hV (z : H) (hz : z ∈ e.target) :
      (V z).comp (Vi z) = ContinuousLinearMap.id ℝ Y := by
    apply ContinuousLinearMap.ext
    intro η
    have hfull : F z (Fi z (iny η)) = iny η :=
      congrArg (fun L : H →L[ℝ] H ↦ L (iny η)) (hF z hz).1
    have hbaseZero : A z (pr (Fi z (iny η))) = 0 := by
      have h := congrArg (fun L : H →L[ℝ] X ↦ L (Fi z (iny η))) (htriangular z hz)
      change pr (F z (Fi z (iny η))) = A z (pr (Fi z (iny η))) at h
      rw [hfull, hpriny] at h
      exact h.symm
    have hprZero : pr (Fi z (iny η)) = 0 := by
      have h := congrArg (Ai z) hbaseZero
      have hi := congrArg (fun L : X →L[ℝ] X ↦ L (pr (Fi z (iny η)))) (hA z hz).2
      change Ai z (A z (pr (Fi z (iny η)))) = pr (Fi z (iny η)) at hi
      simpa only [hi, map_zero] using h
    change qr (F z (iny (qr (Fi z (iny η))))) = η
    rw [← hsplit _ hprZero, hfull, hqriny]
  have hFcont : ContinuousOn F e.target := by
    intro z hz
    exact (((he.contDiffAt (e.open_source.mem_nhds (e.map_target hz))).fderiv_right
      (m := ∞) (by simp)).continuousAt.comp
        (hei.contDiffAt (e.open_target.mem_nhds hz)).continuousAt).continuousWithinAt
  have hFicont : ContinuousOn Fi e.target := by
    intro z hz
    exact ((hei.contDiffAt (e.open_target.mem_nhds hz)).fderiv_right
      (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hAcont : ContinuousOn A e.target := by
    intro z hz
    have hc := (pr.contDiff.contDiffAt.comp z
      (hei.contDiffAt (e.open_target.mem_nhds hz))).continuousAt
    exact (((hf.contDiffAt (f.open_source.mem_nhds
      (hbase (e.symm z) (e.map_target hz)).1)).fderiv_right
        (m := ∞) (by simp)).continuousAt.comp
          (f := fun z : H ↦ pr (e.symm z)) (x := z) hc).continuousWithinAt
  have hAicont : ContinuousOn Ai e.target := by
    intro z hz
    exact (((hfi.contDiffAt (f.open_target.mem_nhds (htarget z hz).1)).fderiv_right
      (m := ∞) (by simp)).continuousAt.comp pr.continuous.continuousAt).continuousWithinAt
  have hBcont : ContinuousOn B e.target :=
    continuousOn_const.clm_comp (hFcont.clm_comp continuousOn_const)
  have hVcont : ContinuousOn V e.target :=
    continuousOn_const.clm_comp (hFcont.clm_comp continuousOn_const)
  have hVicont : ContinuousOn Vi e.target :=
    continuousOn_const.clm_comp (hFicont.clm_comp continuousOn_const)
  -- Bound all original blocks and the explicit diagonal inverses on the same compact window.
  let fNorm (z : H) : ℝ := ‖A z‖ + ‖Ai z‖ + ‖B z‖ + ‖V z‖ + ‖Vi z‖
  have hnorm : ContinuousOn fNorm e.target :=
    (((hAcont.norm.add hAicont.norm).add hBcont.norm).add hVcont.norm).add hVicont.norm
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hnorm.mono hKe)
  let D := max M 1
  refine ⟨D, le_max_right _ _, ?_⟩
  intro z hz
  have htotal : fNorm z ≤ D := by
    have h := hM z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ fNorm z by dsimp [fNorm]; positivity)] at h
    exact h.trans (le_max_left _ _)
  have hbounds : ‖A z‖ ≤ D ∧ ‖Ai z‖ ≤ D ∧ ‖B z‖ ≤ D ∧ ‖V z‖ ≤ D ∧ ‖Vi z‖ ≤ D := by
    dsimp only [fNorm] at htotal
    have h₁ := norm_nonneg (A z)
    have h₂ := norm_nonneg (Ai z)
    have h₃ := norm_nonneg (B z)
    have h₄ := norm_nonneg (V z)
    have h₅ := norm_nonneg (Vi z)
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  change ‖(A z).adjoint‖ ≤ D ∧ (∀ ξ, ‖ξ‖ ≤ D * ‖(A z).adjoint ξ‖) ∧
    ‖(B z).adjoint‖ ≤ D ∧ ‖(V z).adjoint‖ ≤ D ∧ ∀ η, ‖η‖ ≤ D * ‖(V z).adjoint η‖
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ContinuousLinearMap.adjoint.norm_map] using hbounds.1
  · intro ξ
    have hinv := congrArg ContinuousLinearMap.adjoint (hA z (hKe hz)).1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hinv
    have hξ := congrArg (fun L : X →L[ℝ] X ↦ L ξ) hinv
    change (Ai z).adjoint ((A z).adjoint ξ) = ξ at hξ
    calc
      ‖ξ‖ = ‖(Ai z).adjoint ((A z).adjoint ξ)‖ := congrArg norm hξ.symm
      _ ≤ ‖(Ai z).adjoint‖ * ‖(A z).adjoint ξ‖ := ((Ai z).adjoint).le_opNorm _
      _ ≤ D * ‖(A z).adjoint ξ‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        exact mul_le_mul_of_nonneg_right hbounds.2.1 (norm_nonneg _)
  · simpa only [ContinuousLinearMap.adjoint.norm_map] using hbounds.2.2.1
  · simpa only [ContinuousLinearMap.adjoint.norm_map] using hbounds.2.2.2.1
  · intro η
    have hinv := congrArg ContinuousLinearMap.adjoint (hV z (hKe hz))
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hinv
    have hη := congrArg (fun L : Y →L[ℝ] Y ↦ L η) hinv
    change (Vi z).adjoint ((V z).adjoint η) = η at hη
    calc
      ‖η‖ = ‖(Vi z).adjoint ((V z).adjoint η)‖ := congrArg norm hη.symm
      _ ≤ ‖(Vi z).adjoint‖ * ‖(V z).adjoint η‖ := ((Vi z).adjoint).le_opNorm _
      _ ≤ D * ‖(V z).adjoint η‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        exact mul_le_mul_of_nonneg_right hbounds.2.2.2.2 (norm_nonneg _)

end AtiyahSinger
