/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Geometry.AssociatedSphereProductChart

/-!
# The original covector coordinates under an associated product chart change

Public module ID: M0104.

The actual coordinate covector, including the inverse chart derivative, is
identified with all three original triangular blocks. This exposes the full
covector formula used by the cutoff-symbol computation, so finite saturation
can be applied to the literal frequency weights in the associated factors.
The base-dependent mixed block is retained.
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

/-- The actual product-chart covector has the original base, mixed and vertical components. -/
theorem covectorInChart_associatedSphereProductChart_split
    (b₁ b₂ : B)
    (c₁ c₂ : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (hc₁ : c₁ ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (hc₂ : c₂ ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (d₁ d₂ : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
    (hd₁ : d₁ ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
    (hd₂ : d₂ ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
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
    ∀ z ∈ e.target, ∀ (ξ : EuclideanSpace ℝ (Fin n)) (η : EuclideanSpace ℝ (Fin r)),
      let w := e.symm z
      let A := fderiv ℝ (c₁.symm.trans c₂) (pr w)
      let B := qr.comp ((fderiv ℝ e w).comp inx)
      let C := qr.comp ((fderiv ℝ e w).comp iny)
      covectorInChart (associatedSphereProductChart S b₁ c₁ d₁)
          ((associatedSphereProductChart S b₂ c₂ d₂).symm z)
          (covectorFromChart (associatedSphereProductChart S b₂ c₂ d₂)
            ((associatedSphereProductChart S b₂ c₂ d₂).symm z) (split.symm (ξ, η))) =
        split.symm (A.adjoint ξ + B.adjoint η, C.adjoint η) := by
  classical
  let I := 𝓡 (n + r)
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
  change ∀ z ∈ e.target, ∀ (ξ : X) (η : Y), _
  intro z hz ξ η
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
  let A : X →L[ℝ] X := fderiv ℝ f (pr w)
  let B : X →L[ℝ] Y := qr.comp ((fderiv ℝ e w).comp inx)
  let C : Y →L[ℝ] Y := qr.comp ((fderiv ℝ e w).comp iny)
  -- Euclidean concatenation pairs with both original projections, including the vertical part.
  have hinner (α : X) (β : Y) (u : H) :
      inner ℝ (split.symm (α, β)) u = inner ℝ α (pr u) + inner ℝ β (qr u) := by
    have hleft (i : Fin n) : split.symm (α, β) (Fin.castAdd r i) = α i :=
      congrArg (fun p : X × Y ↦ p.1 i) (split.apply_symm_apply (α, β))
    have hright (j : Fin r) : split.symm (α, β) (Fin.natAdd n j) = β j :=
      congrArg (fun p : X × Y ↦ p.2 j) (split.apply_symm_apply (α, β))
    change (∑ i : Fin (n + r), u i * split.symm (α, β) i) =
      (∑ i : Fin n, pr u i * α i) + ∑ j : Fin r, qr u j * β j
    rw [Fin.sum_univ_add]
    simp only [hleft, hright]
    rfl
  have hsplit (u : H) : u = inx (pr u) + iny (qr u) := by
    change u = split.symm (pr u, 0) + split.symm (0, qr u)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    change u = split.symm (split u)
    exact (split.symm_apply_apply u).symm
  have hvertical (u : H) : qr (fderiv ℝ e w u) = B (pr u) + C (qr u) := by
    calc
      qr (fderiv ℝ e w u) = qr (fderiv ℝ e w (inx (pr u) + iny (qr u))) :=
        congrArg (fun v ↦ qr (fderiv ℝ e w v)) (hsplit u)
      _ = B (pr u) + C (qr u) := by
        simp only [map_add]
        rfl
  have hcovector : (fderiv ℝ e w).adjoint (split.symm (ξ, η)) =
      split.symm (A.adjoint ξ + B.adjoint η, C.adjoint η) := by
    apply ext_inner_right ℝ
    intro u
    rw [ContinuousLinearMap.adjoint_inner_left, hinner, hinner, inner_add_left]
    have hhorizontal := congrArg (fun L : H →L[ℝ] X ↦ L u) hder
    change pr (fderiv ℝ e w u) = A (pr u) at hhorizontal
    rw [hhorizontal, hvertical, inner_add_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
    ring
  -- The original inverse source chart and forward target chart produce this same adjoint.
  have hfreq : covectorInChart C₁ (C₂.symm z)
      (covectorFromChart C₂ (C₂.symm z) (split.symm (ξ, η))) =
        (fderiv ℝ e (e.symm z)).adjoint (split.symm (ξ, η)) := by
    have hsource := hz.2
    have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I)
      (f := C₁.symm) (g := C₂) (C₁ (C₂.symm z))
      (by
        simpa only [C₁.left_inv hsource] using
          (contMDiffAt_of_mem_maximalAtlas hC₂ (C₂.map_target hz.1)).mdifferentiableAt
            (by simp))
      ((contMDiffAt_symm_of_mem_maximalAtlas hC₁ (C₁.map_source hsource)).mdifferentiableAt
        (by simp))
    rw [mfderiv_eq_fderiv] at hcomp
    dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
    rw [C₁.left_inv hsource] at hcomp
    have htcomp : fderiv ℝ e (e.symm z) =
        (mfderiv I I C₂ (C₂.symm z)).comp
          (mfderiv I I C₁.symm (C₁ (C₂.symm z))) := hcomp
    ext j
    change inner ℝ (split.symm (ξ, η)) ((mfderiv I I C₂ (C₂.symm z))
        ((mfderiv I I C₁.symm (C₁ (C₂.symm z))) (EuclideanSpace.single j 1))) =
      ((fderiv ℝ e (e.symm z)).adjoint (split.symm (ξ, η))) j
    have hadj := (fderiv ℝ e (e.symm z)).adjoint_inner_left
      (EuclideanSpace.single j 1) (split.symm (ξ, η))
    calc
      _ = inner ℝ (split.symm (ξ, η))
          ((fderiv ℝ e (e.symm z)) (EuclideanSpace.single j 1)) := by
        rw [htcomp]
        rfl
      _ = inner ℝ ((fderiv ℝ e (e.symm z)).adjoint (split.symm (ξ, η)))
          (EuclideanSpace.single j 1) := hadj.symm
      _ = _ := by
        simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) j 1
          ((fderiv ℝ e (e.symm z)).adjoint (split.symm (ξ, η)))
  exact hfreq.trans hcovector

end AtiyahSinger
