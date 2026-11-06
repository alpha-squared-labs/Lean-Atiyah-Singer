/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactCoordinateAmplitudeFamilies
public import AtiyahSinger.Analysis.EquivariantCoordinateFamilies
public import AtiyahSinger.Analysis.EquivariantLocalizedAmplitude
public import AtiyahSinger.Analysis.EquivariantCutoffFrameFamilies

import all AtiyahSinger.Analysis.CoordinateJacobianFamilies

/-!
# Uniform estimates for the actual localized conjugate amplitude

Public module ID: M0457.

The shared original amplitude is evaluated in the fixed cutoffs of the group
neighborhood. Its weighted joint support is a compact image of the original
cutoff support. The coordinate and frame families are differentiated only in
space; continuous group inversion and continuous partition weights suffice.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set Topology
open scoped ContDiff Manifold

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)

include hσ hτ in
set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 2500000 in
-- This combines the same geometric support, spatial jets, and original mixed derivative bounds.
/-- The specified localized amplitude retains uniform real-order estimates under compact weights. -/
theorem PseudodifferentialPiece.uniform_equivariantLocalizedAmplitude {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (γ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ₀ : ContDiff ℝ ∞ γ₀) (hcγ₀ : HasCompactSupport γ₀)
    (U : Set G) (hU : IsOpen U)
    (W : Set (G × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
    (hW : IsOpen W)
    (w : G → ℂ) (hw : Continuous w) (hwU : tsupport w ⊆ U) :
    let X := EuclideanSpace ℝ (Fin n)
    let t (g : G) := L.chart.symm.trans
      ((Diffeomorph.smul (M := M) IG 𝓘(ℝ, X) ∞ g).toHomeomorph.toOpenPartialHomeomorph.trans c)
    (∀ p ∈ W, segment ℝ p.2.2 p.2.1 ⊆ (t p.1).target ∧
      (averagedFDeriv (t p.1).symm p.2.1 p.2.2).IsInvertible) →
    (∀ g ∈ U, tsupport A.cutoff ⊆ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
      (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) →
    (∀ g ∈ U, ∀ z ∈ tsupport γ₀, z.1 ∈ (t g).source ∧ z.2 ∈ (t g).source ∧
      (g, (t g z.1, t g z.2)) ∈ W) →
    let a : G → AmplitudeFunction n r q := fun g x y ξ ↦
      w g • L.equivariantLocalizedAmplitude IG σ τ c A B γ₀ g x y ξ
    (∀ g, IsAmplitude m (a g)) ∧
    (∀ g, tsupport (Function.uncurry (a g)) ⊆ tsupport A.cutoff ×ˢ tsupport A.cutoff) ∧
    (∀ k : ℕ, Continuous (fun b : G × ((X × X) × X) ↦
      iteratedFDeriv ℝ k (fun z ↦ a b.1 z.1.1 z.1.2 z.2) b.2)) ∧
    (∀ i j k : ℕ, Continuous (fun b : G × ((X × X) × X) ↦
      amplitudeDerivative (a b.1) i j k b.2.1.1 b.2.1.2 b.2.2)) ∧
    (∀ i j k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ g x y ξ,
      ‖amplitudeDerivative (a g) i j k x y ξ‖ ≤
        D * (1 + ‖ξ‖) ^ (m - (k : ℝ))) := by
  classical
  dsimp only
  intro hvalid hoverlap hγvalid
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let X := EuclideanSpace ℝ (Fin n)
  let R := EuclideanSpace ℂ (Fin r)
  let Q := EuclideanSpace ℂ (Fin q)
  let H := R →L[ℂ] Q
  let I := 𝓘(ℝ, X)
  let d (g : G) := Diffeomorph.smul (M := M) IG I ∞ g
  let t (g : G) := L.chart.symm.trans
    ((d g).toHomeomorph.toOpenPartialHomeomorph.trans c)
  let p := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  have hp : IsSymbol univ m p := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff
    L.output.compact_support L.input.compact_support
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) L.chart_mem_atlas
  have ht (g : G) : ContDiffOn ℝ ∞ (t g) (t g).source := by
    intro y hy
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1
    have hmove := (d g).contMDiffAt.comp y hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hcM hy.2.2).comp y hmove).contDiffAt.contDiffWithinAt
  have hψ (g : G) : ContDiffOn ℝ ∞ (t g).symm (t g).target := by
    intro y hy
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1
    have hmove := (d g).symm.contMDiffAt.comp y hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y hmove).contDiffAt.contDiffWithinAt
  let D : Set (G × X) := {b | b.2 ∈ (t b.1).target}
  have hD : IsOpen D := by
    let moved (b : G × X) : M := b.1⁻¹ • c.symm b.2
    have hm : ContinuousOn moved (univ ×ˢ c.target) :=
      continuous_fst.inv.continuousOn.smul
        (c.continuousOn_symm.comp continuous_snd.continuousOn (fun _ hb ↦ hb.2))
    have h := hm.isOpen_inter_preimage (isOpen_univ.prod c.open_target) L.chart.open_source
    convert h using 1
    ext b
    change ((b.2 ∈ c.target ∧ c.symm b.2 ∈ (univ : Set M)) ∧
      b.1⁻¹ • c.symm b.2 ∈ L.chart.source) ↔
        (b.1 ∈ (univ : Set G) ∧ b.2 ∈ c.target) ∧ moved b ∈ L.chart.source
    simp only [mem_univ, and_true, true_and, moved]
  have hψj (k : ℕ) : ContinuousOn
      (fun b : G × X ↦ iteratedFDeriv ℝ k (t b.1).symm b.2) D := by
    have h := continuousOn_iteratedFDeriv_inverse_smul_chart (G := G) IG c L.chart
      hc L.chart_mem_atlas k
    apply h.mono
    intro b hb
    exact ⟨hb.1.1, hb.2⟩
  let N := W ∩ (U ×ˢ univ)
  have hN : IsOpen N := hW.inter (hU.prod isOpen_univ)
  have hseg (b : G × (X × X)) (hb : b ∈ N) :
      segment ℝ b.2.2 b.2.1 ⊆ (t b.1).target := (hvalid b hb.1).1
  have hinv (b : G × (X × X)) (hb : b ∈ N) :
      (averagedFDeriv (t b.1).symm b.2.1 b.2.2).IsInvertible := (hvalid b hb.1).2
  let φ (g : G) (z : X × X) : X := (t g).symm z.1
  let Θ (g : G) (z : X × X) : X →L[ℝ] X := coordinateFrequencyChange (t g) z.1 z.2
  let J (g : G) (z : X × X) : ℝ := coordinateJacobianFactor (t g) z.1 z.2
  have hfactors (g : G) : ContDiffOn ℝ ∞
      (fun z ↦ ((φ g z, Θ g z), J g z)) {z | (g, z) ∈ N} :=
    contDiffOn_coordinateChange_factors (t g) (ht g) (hψ g) _
      (hN.preimage (continuous_const.prodMk continuous_id))
      (fun z hz ↦ hseg (g, z) hz) (fun z hz ↦ hinv (g, z) hz)
  have hφj (k : ℕ) : ContinuousOn
      (fun b : G × (X × X) ↦ iteratedFDeriv ℝ k (φ b.1) b.2) N := by
    let pr : X × X →L[ℝ] X := ContinuousLinearMap.fst ℝ X X
    let P : (X [×k]→L[ℝ] X) →L[ℝ] ((X × X) [×k]→L[ℝ] X) :=
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k ↦ pr)
    have hm : Continuous (fun b : G × (X × X) ↦ (b.1, b.2.1)) :=
      continuous_fst.prodMk continuous_snd.fst
    have hj : ContinuousOn
        (fun b : G × (X × X) ↦ iteratedFDeriv ℝ k (t b.1).symm b.2.1) N :=
      (hψj k).comp (f := fun b : G × (X × X) ↦ (b.1, b.2.1)) hm.continuousOn
        (fun b hb ↦ hseg b hb (right_mem_segment ℝ b.2.2 b.2.1))
    have H : ContinuousOn
        (fun b : G × (X × X) ↦ P (iteratedFDeriv ℝ k (t b.1).symm b.2.1)) N :=
      P.continuous.comp_continuousOn hj
    apply H.congr
    intro b hb
    have hx : pr b.2 ∈ (t b.1).target :=
      hseg b hb (right_mem_segment ℝ b.2.2 b.2.1)
    have hopen : IsOpen (pr ⁻¹' (t b.1).target) :=
      (t b.1).open_target.preimage pr.continuous
    have heq := pr.iteratedFDerivWithin_comp_right (hψ b.1)
      (t b.1).open_target.uniqueDiffOn hopen.uniqueDiffOn hx (i := k) (by simp)
    rw [iteratedFDerivWithin_of_isOpen _ hopen hx,
      iteratedFDerivWithin_of_isOpen _ (t b.1).open_target hx] at heq
    exact heq
  have hΘj := continuousOn_iteratedFDeriv_coordinateFrequencyChange t hψ hD hψj N hN hseg hinv
  have hJj := continuousOn_iteratedFDeriv_coordinateJacobianFactor t ht hψ hD hψj N hN hseg hinv
  have hds (b : G × (X × X)) (hb : b ∈ N) :
      ContDiffAt ℝ ∞ (fun z ↦ ((φ b.1 z, Θ b.1 z), J b.1 z)) b.2 :=
    (hfactors b.1).contDiffAt
      ((hN.preimage (continuous_const.prodMk continuous_id)).mem_nhds hb)
  have hdataj := continuousOn_jet_pair_family φ Θ N
    (fun b hb ↦ (hds b hb).fst.fst) (fun b hb ↦ (hds b hb).fst.snd) hφj hΘj
  have hΘinv (b : G × (X × X)) (hb : b ∈ N) : (Θ b.1 b.2).IsInvertible := by
    let K := averagedFDeriv (t b.1).symm b.2.1 b.2.2
    have hi : K.adjoint.IsInvertible := by
      apply ContinuousLinearMap.IsInvertible.of_inverse (g := K.inverse.adjoint)
      · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
          congrArg ContinuousLinearMap.adjoint (hinv b hb).inverse_comp_self
      · simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
          congrArg ContinuousLinearMap.adjoint (hinv b hb).self_comp_inverse
    exact hi.inverse
  -- The cutoff frame matrices use the very same forward and backward fiber transports.
  let data := equivariantSymbolCoordinateData σ τ L.chart c
    L.input.frame A.frame L.output.frame B.frame
  let FP := (Q →L[ℂ] Q) × (R →L[ℂ] R)
  let pair (g : G) (x : X) : FP :=
    (cutoffMatrix A.cutoff (fun z ↦ (data g z).2.2.1) x,
      cutoffMatrix A.cutoff (fun z ↦ (data g z).2.2.2) x)
  have hpair := equivariantCutoffFramePair_regularity IG σ τ hσ hτ L.chart c
    L.chart_mem_atlas hc L.input.frame A.frame L.output.frame B.frame
    A.cutoff A.smooth_cutoff U (fun g hg z hz ↦
      ⟨⟨A.support_subset hz, (B.support_subset (by rwa [← hAB])).2⟩, hoverlap g hg hz⟩)
  have hpairAt (g : G) (hg : g ∈ U) (x : X) : ContDiffAt ℝ ∞ (pair g) x :=
    (hpair.1 g hg).contDiffAt
  have hpairj (k : ℕ) : ContinuousOn
      (fun b : G × X ↦ iteratedFDeriv ℝ k (pair b.1) b.2) (U ×ˢ univ) := hpair.2 k
  let ψ₂ (g : G) (z : X × X) : X := (t g).symm z.2
  have hψ₂At (b : G × (X × X)) (hb : b ∈ N) : ContDiffAt ℝ ∞ (ψ₂ b.1) b.2 :=
    ((hψ b.1).contDiffAt ((t b.1).open_target.mem_nhds
      (hseg b hb (left_mem_segment ℝ b.2.2 b.2.1)))).comp b.2 contDiffAt_snd
  have hψ₂j (k : ℕ) : ContinuousOn
      (fun b : G × (X × X) ↦ iteratedFDeriv ℝ k (ψ₂ b.1) b.2) N := by
    let pr : X × X →L[ℝ] X := ContinuousLinearMap.snd ℝ X X
    let P : (X [×k]→L[ℝ] X) →L[ℝ] ((X × X) [×k]→L[ℝ] X) :=
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k ↦ pr)
    have hm : Continuous (fun b : G × (X × X) ↦ (b.1, b.2.2)) :=
      continuous_fst.prodMk continuous_snd.snd
    have hj : ContinuousOn
        (fun b : G × (X × X) ↦ iteratedFDeriv ℝ k (t b.1).symm b.2.2) N :=
      (hψj k).comp (f := fun b : G × (X × X) ↦ (b.1, b.2.2)) hm.continuousOn
        (fun b hb ↦ hseg b hb (left_mem_segment ℝ b.2.2 b.2.1))
    have H : ContinuousOn
        (fun b : G × (X × X) ↦ P (iteratedFDeriv ℝ k (t b.1).symm b.2.2)) N :=
      P.continuous.comp_continuousOn hj
    apply H.congr
    intro b hb
    have hx : pr b.2 ∈ (t b.1).target :=
      hseg b hb (left_mem_segment ℝ b.2.2 b.2.1)
    have hopen : IsOpen (pr ⁻¹' (t b.1).target) :=
      (t b.1).open_target.preimage pr.continuous
    have heq := pr.iteratedFDerivWithin_comp_right (hψ b.1)
      (t b.1).open_target.uniqueDiffOn hopen.uniqueDiffOn hx (i := k) (by simp)
    rw [iteratedFDerivWithin_of_isOpen _ hopen hx,
      iteratedFDerivWithin_of_isOpen _ (t b.1).open_target hx] at heq
    exact heq
  let ψpair (g : G) (z : X × X) := (φ g z, ψ₂ g z)
  have hψpairAt (b : G × (X × X)) (hb : b ∈ N) :
      ContDiffAt ℝ ∞ (ψpair b.1) b.2 := ((hds b hb).fst.fst).prodMk (hψ₂At b hb)
  have hψpairj := continuousOn_jet_pair_family φ ψ₂ N
    (fun b hb ↦ (hds b hb).fst.fst) hψ₂At hφj hψ₂j
  have hpairXj (k : ℕ) : ContinuousOn (fun b : G × (X × X) ↦
      iteratedFDeriv ℝ k (fun z : X × X ↦ pair b.1 z.1) b.2) N := by
    let pr : X × X →L[ℝ] X := ContinuousLinearMap.fst ℝ X X
    let P : (X [×k]→L[ℝ] FP) →L[ℝ] ((X × X) [×k]→L[ℝ] FP) :=
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k ↦ pr)
    have hm : Continuous (fun b : G × (X × X) ↦ (b.1, b.2.1)) :=
      continuous_fst.prodMk continuous_snd.fst
    have hj : ContinuousOn
        (fun b : G × (X × X) ↦ iteratedFDeriv ℝ k (pair b.1) b.2.1) N :=
      (hpairj k).comp (f := fun b : G × (X × X) ↦ (b.1, b.2.1)) hm.continuousOn
        (fun _ hb ↦ ⟨hb.2.1, mem_univ _⟩)
    have H := P.continuous.comp_continuousOn hj
    apply H.congr
    intro b hb
    exact pr.iteratedFDeriv_comp_right (hpair.1 b.1 hb.2.1) b.2 (by simp)
  have hpairYj (k : ℕ) : ContinuousOn (fun b : G × (X × X) ↦
      iteratedFDeriv ℝ k (fun z : X × X ↦ pair b.1 z.2) b.2) N := by
    let pr : X × X →L[ℝ] X := ContinuousLinearMap.snd ℝ X X
    let P : (X [×k]→L[ℝ] FP) →L[ℝ] ((X × X) [×k]→L[ℝ] FP) :=
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k ↦ pr)
    have hm : Continuous (fun b : G × (X × X) ↦ (b.1, b.2.2)) :=
      continuous_fst.prodMk continuous_snd.snd
    have hj : ContinuousOn
        (fun b : G × (X × X) ↦ iteratedFDeriv ℝ k (pair b.1) b.2.2) N :=
      (hpairj k).comp (f := fun b : G × (X × X) ↦ (b.1, b.2.2)) hm.continuousOn
        (fun _ hb ↦ ⟨hb.2.1, mem_univ _⟩)
    have H := P.continuous.comp_continuousOn hj
    apply H.congr
    intro b hb
    exact pr.iteratedFDeriv_comp_right (hpair.1 b.1 hb.2.1) b.2 (by simp)
  let pairXY (g : G) (z : X × X) := (pair g z.1, pair g z.2)
  have hpairXYAt (b : G × (X × X)) (hb : b ∈ N) :
      ContDiffAt ℝ ∞ (pairXY b.1) b.2 :=
    ((hpairAt b.1 hb.2.1 b.2.1).comp b.2 contDiffAt_fst).prodMk
      ((hpairAt b.1 hb.2.1 b.2.2).comp b.2 contDiffAt_snd)
  have hpairXYj := continuousOn_jet_pair_family
    (fun g (z : X × X) ↦ pair g z.1) (fun g (z : X × X) ↦ pair g z.2) N
      (fun b hb ↦ (hpairAt b.1 hb.2.1 b.2.1).comp b.2 contDiffAt_fst)
      (fun b hb ↦ (hpairAt b.1 hb.2.1 b.2.2).comp b.2 contDiffAt_snd) hpairXj hpairYj
  have hwj (k : ℕ) : ContinuousOn (fun b : G × (X × X) ↦
      iteratedFDeriv ℝ k (fun _ : X × X ↦ w b.1) b.2) N := by
    cases k with
    | zero =>
      have h : Continuous (fun b : G × (X × X) ↦
          (continuousMultilinearCurryFin0 ℝ (X × X) ℂ).symm (w b.1)) :=
        (continuousMultilinearCurryFin0 ℝ (X × X) ℂ).symm.continuous.comp
          (hw.comp continuous_fst)
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply] using h.continuousOn
    | succ k =>
      simp only [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k), Pi.zero_apply]
      exact continuousOn_const
  let d₁ (g : G) (z : X × X) := (J g z, pairXY g z)
  have hd₁At (b : G × (X × X)) (hb : b ∈ N) : ContDiffAt ℝ ∞ (d₁ b.1) b.2 :=
    ((hds b hb).snd).prodMk (hpairXYAt b hb)
  have hd₁j := continuousOn_jet_pair_family J pairXY N
    (fun b hb ↦ (hds b hb).snd) hpairXYAt hJj hpairXYj
  let d₂ (g : G) (z : X × X) := (d₁ g z, w g)
  have hd₂At (b : G × (X × X)) (hb : b ∈ N) : ContDiffAt ℝ ∞ (d₂ b.1) b.2 :=
    (hd₁At b hb).prodMk contDiffAt_const
  have hd₂j := continuousOn_jet_pair_family d₁ (fun g _ ↦ w g) N hd₁At
    (fun _ _ ↦ contDiffAt_const) hd₁j hwj
  let d₃ (g : G) (z : X × X) := (ψpair g z, d₂ g z)
  have hd₃At (b : G × (X × X)) (hb : b ∈ N) : ContDiffAt ℝ ∞ (d₃ b.1) b.2 :=
    (hψpairAt b hb).prodMk (hd₂At b hb)
  have hd₃j := continuousOn_jet_pair_family ψpair d₂ N hψpairAt hd₂At hψpairj hd₂j
  let D₄ := ((X × X) × ((ℝ × (FP × FP)) × ℂ)) × (X × X)
  let d₄ (g : G) (z : X × X) : D₄ := (d₃ g z, z)
  have hd₄At (b : G × (X × X)) (hb : b ∈ N) : ContDiffAt ℝ ∞ (d₄ b.1) b.2 :=
    (hd₃At b hb).prodMk contDiffAt_id
  have hd₄j := continuousOn_jet_pair_family d₃ (fun _ : G ↦ id) N hd₃At
    (fun _ _ ↦ contDiffAt_id) hd₃j
    (fun k ↦ ((contDiff_id : ContDiff ℝ ∞ (id : X × X → X × X)).continuous_iteratedFDeriv
        (by simp)).comp continuous_snd |>.continuousOn)
  let Rclm := ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ
  let Nclm (a : Q →L[ℂ] Q) (b : R →L[ℂ] R) : H →L[ℝ] H :=
    Rclm (((ContinuousLinearMap.compL ℂ R Q Q) a).comp
      ((ContinuousLinearMap.compL ℂ R R Q).flip b))
  let f₄ (z : D₄) : H →L[ℝ] H :=
    (z.1.2.2 * (((A.cutoff z.2.1 * A.cutoff z.2.2) * γ₀ z.1.1 * z.1.2.1.1 : ℝ) : ℂ)) •
      Nclm z.1.2.1.2.1.1 z.1.2.1.2.2.2
  have hNclm : ContDiff ℝ ∞ (fun z : (Q →L[ℂ] Q) × (R →L[ℂ] R) ↦ Nclm z.1 z.2) := by
    have hcomplex : ContDiff ℂ ∞ (fun z : (Q →L[ℂ] Q) × (R →L[ℂ] R) ↦
        ((ContinuousLinearMap.compL ℂ R Q Q) z.1).comp
          ((ContinuousLinearMap.compL ℂ R R Q).flip z.2)) :=
      ((ContinuousLinearMap.compL ℂ R Q Q).contDiff.comp contDiff_fst).clm_comp
        ((ContinuousLinearMap.compL ℂ R R Q).flip.contDiff.comp contDiff_snd)
    exact Rclm.contDiff.comp (hcomplex.restrict_scalars ℝ)
  have hf₄ : ContDiff ℝ ∞ f₄ := by
    have hχ : ContDiff ℝ ∞ (fun z : D₄ ↦
        (A.cutoff z.2.1 * A.cutoff z.2.2) * γ₀ z.1.1 * z.1.2.1.1) :=
      (((A.smooth_cutoff.comp contDiff_snd.fst).mul
        (A.smooth_cutoff.comp contDiff_snd.snd)).mul
          (hγ₀.comp contDiff_fst.fst)).mul contDiff_fst.snd.fst.fst
    exact (contDiff_fst.snd.snd.mul (Complex.ofRealCLM.contDiff.comp hχ)).smul
      (hNclm.comp (contDiff_fst.snd.fst.snd.fst.fst.prodMk
        contDiff_fst.snd.fst.snd.snd.snd))
  let coeff (g : G) (z : X × X) : H →L[ℝ] H := f₄ (d₄ g z)
  have hcoeff (g : G) : ContDiffOn ℝ ∞ (coeff g) {z | (g, z) ∈ N} :=
    fun z hz ↦ (hf₄.contDiffAt.comp z (hd₄At (g, z) hz)).contDiffWithinAt
  have hcoeffj := continuousOn_jet_postcomp_family d₄ f₄ N univ isOpen_univ
    (fun _ _ ↦ mem_univ _) hd₄At hf₄.contDiffOn hd₄j
  -- The same compact original cutoff is transported into the valid frequency locus.
  let C₀ := tsupport w ×ˢ tsupport γ₀
  let move (b : G × (X × X)) : G × (X × X) :=
    (b.1, (t b.1 b.2.1, t b.1 b.2.2))
  have hmove : ContinuousOn move C₀ := by
    have hc₁ : ContinuousOn (fun b : G × (X × X) ↦ L.chart.symm b.2.1) C₀ :=
      L.chart.continuousOn_symm.comp continuous_snd.fst.continuousOn
        (fun b hb ↦ (hγvalid b.1 (hwU hb.1) b.2 hb.2).1.1)
    have hc₂ : ContinuousOn (fun b : G × (X × X) ↦ L.chart.symm b.2.2) C₀ :=
      L.chart.continuousOn_symm.comp continuous_snd.snd.continuousOn
        (fun b hb ↦ (hγvalid b.1 (hwU hb.1) b.2 hb.2).2.1.1)
    have h₁ := c.continuousOn.comp (continuous_fst.continuousOn.smul hc₁)
      (fun b hb ↦ (hγvalid b.1 (hwU hb.1) b.2 hb.2).1.2.2)
    have h₂ := c.continuousOn.comp (continuous_fst.continuousOn.smul hc₂)
      (fun b hb ↦ (hγvalid b.1 (hwU hb.1) b.2 hb.2).2.1.2.2)
    exact continuous_fst.continuousOn.prodMk (h₁.prodMk h₂)
  let C := move '' C₀ ∩ (univ ×ˢ (tsupport A.cutoff ×ˢ tsupport A.cutoff))
  have hC₀ : IsCompact C₀ := (HasCompactSupport.of_compactSpace w).prod hcγ₀
  have hC : IsCompact C := (hC₀.image_of_continuousOn hmove).inter_right
    (isClosed_univ.prod ((isClosed_tsupport _).prod (isClosed_tsupport _)))
  have hCN : C ⊆ N := by
    rintro b ⟨⟨a, ha, rfl⟩, _⟩
    exact ⟨(hγvalid a.1 (hwU ha.1) a.2 ha.2).2.2, ⟨hwU ha.1, mem_univ _⟩⟩
  have hzero (b : G × (X × X)) (hb : b ∉ C) : coeff b.1 b.2 = 0 := by
    by_cases hw₀ : w b.1 = 0
    · simp only [coeff, f₄, d₄, d₃, d₂, hw₀, zero_mul, zero_smul]
    by_cases hx : A.cutoff b.2.1 = 0
    · simp only [coeff, f₄, d₄, d₃, d₂, hx, zero_mul, Complex.ofReal_zero,
        mul_zero, zero_smul]
    by_cases hy : A.cutoff b.2.2 = 0
    · simp only [coeff, f₄, d₄, d₃, d₂, hy, mul_zero, zero_mul, Complex.ofReal_zero,
        zero_smul]
    by_cases hγ : γ₀ (ψpair b.1 b.2) = 0
    · simp only [coeff, f₄, d₄, d₃, d₂, hγ, mul_zero, zero_mul, Complex.ofReal_zero,
        zero_smul]
    have hgw : b.1 ∈ tsupport w := subset_tsupport _ hw₀
    have hgU := hwU hgw
    have hxs : b.2.1 ∈ tsupport A.cutoff := subset_tsupport _ hx
    have hys : b.2.2 ∈ tsupport A.cutoff := subset_tsupport _ hy
    have hxt : b.2.1 ∈ (t b.1).target :=
      ⟨⟨(A.support_subset hxs).1, mem_univ _⟩, (hoverlap b.1 hgU hxs).1.1⟩
    have hyt : b.2.2 ∈ (t b.1).target :=
      ⟨⟨(A.support_subset hys).1, mem_univ _⟩, (hoverlap b.1 hgU hys).1.1⟩
    exfalso
    apply hb
    refine ⟨⟨(b.1, ψpair b.1 b.2), ⟨hgw, subset_tsupport _ hγ⟩, ?_⟩,
      ⟨mem_univ _, hxs, hys⟩⟩
    change (b.1, (t b.1 ((t b.1).symm b.2.1), t b.1 ((t b.1).symm b.2.2))) = b
    rw [(t b.1).right_inv hxt, (t b.1).right_inv hyt]
  have hcert := uniform_amplitude_family_of_compact_coordinate_data m p hp N C hN hC hCN
    φ Θ coeff (fun g ↦ (hfactors g).fst) hdataj hΘinv hcoeff hcoeffj hzero
  have hid : (fun g x y ξ ↦ coeff g (x, y) (p (φ g (x, y)) (Θ g (x, y) ξ))) =
      (fun g x y ξ ↦ w g • L.equivariantLocalizedAmplitude IG σ τ c A B γ₀ g x y ξ) := by
    funext g x y ξ
    change (w g * (((A.cutoff x * A.cutoff y) * γ₀ ((t g).symm x, (t g).symm y) *
      coordinateJacobianFactor (t g) x y : ℝ) : ℂ)) •
      ((pair g x).1.comp ((p ((t g).symm x) (coordinateFrequencyChange (t g) x y ξ)).comp
        (pair g y).2)) = _
    simp only [PseudodifferentialPiece.equivariantLocalizedAmplitude, coordinateAmplitude,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      ← Complex.coe_smul, smul_smul]
    rfl
  rw [hid] at hcert
  refine ⟨hcert.1, ?_, hcert.2.2⟩
  intro g z hz
  obtain ⟨b, hb, rfl⟩ := hcert.2.1 g hz
  exact hb.2.2

end AtiyahSinger
