/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolJetFamilies

import all AtiyahSinger.Analysis.EquivariantSymbolOrbitBounds

/-!
# Fixed cutoffs of the original moving-frame matrices

Public module ID: M0498.

The original coordinate tuple supplies both action matrices in exactly the
frames used by localized conjugation. A fixed spatial cutoff supported in their
common moving overlap makes both matrices globally smooth in space, with all
spatial jets continuous in the original topological group parameter. The result
uses the actual closed cutoff support and introduces no smooth inverse action.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle Set Topology
open scoped ContDiff Manifold
set_option maxSynthPendingDepth 20

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
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

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

variable [hG : IsManifold IG ∞ G]
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)


include hG hM hσ hτ in
/-- A common fixed cutoff gives smooth slices and continuous jets for both original frame maps. -/
theorem equivariantCutoffFramePair_regularity
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f']
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ) (U : Set G)
    (hsupp : ∀ g ∈ U, tsupport χ ⊆ {x | x ∈ symbolChartDomain E F d e' f' ∧
      g⁻¹ • d.symm x ∈ c.source ∩ e.baseSet ∩ f.baseSet}) :
    let data := equivariantSymbolCoordinateData σ τ c d e e' f f'
    let pair (g : G) (x : EuclideanSpace ℝ (Fin n)) :=
      (cutoffMatrix χ (fun z ↦ (data g z).2.2.1) x,
        cutoffMatrix χ (fun z ↦ (data g z).2.2.2) x)
    (∀ g ∈ U, ContDiff ℝ ∞ (pair g)) ∧ ∀ k : ℕ,
      ContinuousOn (fun z : G × EuclideanSpace ℝ (Fin n) ↦
        iteratedFDeriv ℝ k (pair z.1) z.2) (U ×ˢ univ) := by
  let X := EuclideanSpace ℝ (Fin n)
  let R := EuclideanSpace ℂ (Fin r)
  let Q := EuclideanSpace ℂ (Fin q)
  let Y := X × ((X →L[ℝ] X) × ((Q →L[ℂ] Q) × (R →L[ℂ] R)))
  let V := (Q →L[ℂ] Q) × (R →L[ℂ] R)
  let data := equivariantSymbolCoordinateData σ τ c d e e' f f'
  let pair (g : G) (x : X) : V :=
    (cutoffMatrix χ (fun z ↦ (data g z).2.2.1) x,
      cutoffMatrix χ (fun z ↦ (data g z).2.2.2) x)
  let O := symbolChartDomain E F d e' f'
  let W : Set (G × X) := {z | z.2 ∈ O ∧
    z.1⁻¹ • d.symm z.2 ∈ c.source ∩ e.baseSet ∩ f.baseSet}
  have hO : IsOpen O := isOpen_symbolChartDomain E F d e' f'
  have hmove : ContinuousOn (fun z : G × X ↦ z.1⁻¹ • d.symm z.2) (univ ×ˢ O) :=
    continuous_fst.inv.continuousOn.smul (d.continuousOn_symm.comp
      continuous_snd.continuousOn (fun z hz ↦ hz.2.1.1))
  have hW : IsOpen W := by
    have h := hmove.isOpen_inter_preimage (isOpen_univ.prod hO)
      ((c.open_source.inter e.open_baseSet).inter f.open_baseSet)
    convert h using 1
    ext z
    simp only [W, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, true_and, mem_preimage]
  have hdsmooth (g : G) : ContDiffOn ℝ ∞ (data g) {x | (g, x) ∈ W} :=
    contDiffOn_equivariantSymbolCoordinateData IG σ τ hσ hτ c d hc hd e e' f f' g
  have hdata (k : ℕ) : ContinuousOn
      (fun z : G × X ↦ iteratedFDeriv ℝ k (data z.1) z.2) W :=
    continuousOn_iteratedFDeriv_equivariantSymbolCoordinateData
      IG σ τ hσ hτ c d hc hd e e' f f' k
  have hds (z : G × X) (hz : z ∈ W) : ContDiffAt ℝ ∞ (data z.1) z.2 :=
    (hdsmooth z.1).contDiffAt ((hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
  have hdcont : ContinuousOn (fun z : G × X ↦ data z.1 z.2) W := by
    have h := (continuousMultilinearCurryFin0 ℝ X Y).continuous
      |>.comp_continuousOn (hdata 0)
    change ContinuousOn (fun z : G × X ↦ (iteratedFDeriv ℝ 0 (data z.1) z.2).curry0) W at h
    simpa only [ContinuousMultilinearMap.curry0_apply, iteratedFDeriv_zero_apply] using h
  -- The fixed cutoff is paired with the original tuple before a single smooth multiplication.
  let F (g : G) (x : X) : ℝ × Y := (χ x, data g x)
  have hF (z : G × X) (hz : z ∈ W) : ContDiffAt ℝ ∞ (F z.1) z.2 :=
    hχ.contDiffAt.prodMk (hds z hz)
  have hFjets (k : ℕ) : ContinuousOn
      (fun z : G × X ↦ iteratedFDeriv ℝ k (F z.1) z.2) W := by
    have hχjets : ContinuousOn
        (fun z : G × X ↦ iteratedFDeriv ℝ k χ z.2) W :=
      ((hχ.continuous_iteratedFDeriv (by simp)).comp continuous_snd).continuousOn
    have h := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin k ↦ X) ℝ Y).continuous
      |>.comp_continuousOn (hχjets.prodMk (hdata k))
    apply h.congr
    intro z hz
    exact iteratedFDeriv_prodMk hχ.contDiffAt (hds z hz) (by simp)
  let P (z : ℝ × Y) : V := z.1 • z.2.2.2
  have hP : ContDiff ℝ ∞ P := contDiff_fst.smul contDiff_snd.snd.snd
  have hFcont : ContinuousOn (fun z : G × X ↦ F z.1 z.2) W :=
    (hχ.continuous.comp continuous_snd).continuousOn.prodMk hdcont
  have hpjets (k : ℕ) : ContinuousOn
      (fun z : G × X ↦ iteratedFDeriv ℝ k (pair z.1) z.2) W :=
    continuousOn_iteratedFDeriv_comp_family (fun _ : G ↦ P) F W
      (fun _ _ ↦ hP.contDiffAt) hF
      (fun j ↦ (hP.continuous_iteratedFDeriv (by simp)).comp_continuousOn hFcont) hFjets k
  refine ⟨?_, ?_⟩
  · intro g hg
    have hU : IsOpen {x : X | (g, x) ∈ W} :=
      hW.preimage (continuous_const.prodMk continuous_id)
    exact (contDiff_cutoffMatrix _ hU _ (hdsmooth g).snd.snd.fst χ hχ (hsupp g hg)).prodMk
      (contDiff_cutoffMatrix _ hU _ (hdsmooth g).snd.snd.snd χ hχ (hsupp g hg))
  · intro k z hz
    by_cases hs : z.2 ∈ tsupport χ
    · have hzW : z ∈ W := hsupp z.1 hz.1 hs
      exact ((hpjets k z hzW).continuousAt (hW.mem_nhds hzW)).continuousWithinAt
    · -- Outside the same closed spatial support, both matrices and every jet vanish locally.
      have hzero (g : G) (x : X) (hx : x ∉ tsupport χ) :
          iteratedFDeriv ℝ k (pair g) x = 0 := by
        have heq : pair g =ᶠ[nhds x] (fun _ ↦ (0 : V)) := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
          change χ y = 0 at hy
          simp only [pair, cutoffMatrix, hy, zero_smul]
          rfl
        rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply]
      apply ContinuousAt.continuousWithinAt
      apply (continuousAt_const (y := (0 : X [×k]→L[ℝ] V))).congr_of_eventuallyEq
      filter_upwards [((isClosed_tsupport χ).isOpen_compl.preimage continuous_snd).mem_nhds hs]
        with w hw
      exact hzero w.1 w.2 hw

end AtiyahSinger
