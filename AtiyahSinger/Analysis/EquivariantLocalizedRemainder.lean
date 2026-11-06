/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactKernelLift
public import AtiyahSinger.Analysis.CompactPieceRefinement
public import AtiyahSinger.Analysis.EquivariantLocalizedAmplitude
public import AtiyahSinger.Analysis.FixedAmplitudeRemainder

import all AtiyahSinger.Analysis.CoordinateChange
import all AtiyahSinger.Analysis.EquivariantPrincipalSymbol

/-!
# Fixed native remainders for localized conjugation

Public module ID: M0537.

A fixed original near-diagonal cutoff splits an original coordinate operator.
One larger source plateau lifts its actual smooth-kernel remainder to the
original bundles and measure. The new plateau uses the original frames and
reconstructs the original section operator without multiplying its old
cutoffs a second time.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- A fixed near-diagonal splitting gives one actual native kernel remainder,
using new source plateaus in the original frames and the original measure. -/
theorem PseudodifferentialPiece.exists_fixed_native_kernel_remainder {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (β δ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβone : tsupport L.output.cutoff ∪ tsupport L.input.cutoff ⊆
      interior {x | β x = 1})
    (hδ : ContDiff ℝ ∞ δ) (hcδ : HasCompactSupport δ)
    (hδsupp : tsupport δ ⊆
      symbolChartDomain E F L.chart L.input.frame L.output.frame)
    (hδone : tsupport β ⊆ {x | δ x = 1})
    (γ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ₀ : ContDiff ℝ ∞ γ₀) (hcγ₀ : HasCompactSupport γ₀)
    (hγ₀supp : tsupport γ₀ ⊆ tsupport β ×ˢ tsupport β)
    (hoff : ∀ x : EuclideanSpace ℝ (Fin n),
      (fun z ↦ β z.1 * β z.2 - γ₀ z) =ᶠ[𝓝 (x, x)] (fun _ ↦ 0)) :
    ∃ (C : BundleChartCutoff (r := r) E L.chart)
      (D : BundleChartCutoff (r := q) F L.chart)
      (N Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
      (S : SmoothKernel (n := n) (r := r) (q := q) E F),
      C.frame = L.input.frame ∧ D.frame = L.output.frame ∧
      C.cutoff = δ ∧ D.cutoff = δ ∧
      (∀ v x, N v x = amplitudeApply
        (localizedAmplitude γ₀ (cutoffSymbol L.output.cutoff L.input.cutoff L.symbol)) v x) ∧
      HasOperatorSupport (tsupport β) N ∧ HasOperatorSupport (tsupport β) Q ∧
      L.coordinateOperator = N + Q ∧
      S.toLinearMap μ = (D.extendLinearMap L.chart_mem_atlas).comp
        (Q.toLinearMap.comp (C.localizeLinearMap L.chart_mem_atlas)) ∧
      L.toLinearMap = (D.extendLinearMap L.chart_mem_atlas).comp
        (N.toLinearMap.comp (C.localizeLinearMap L.chart_mem_atlas)) + S.toLinearMap μ := by
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let p := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  have hp : IsSymbol univ m p := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff
    L.output.compact_support L.input.compact_support
  -- The same original coordinate operator and fixed cutoff supply Q and its actual kernel.
  obtain ⟨Q, k, hk, _, hkQ, hQ, hsplit⟩ := exists_fixed_amplitude_kernel_remainder
    m p hp L.coordinateOperator L.coordinateOperator_eq_quantize
    (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)
    L.hasOperatorSupport_coordinateOperator β hβ hcβ hβone γ₀ hγ₀ hcγ₀ hγ₀supp hoff
  let A := localizedAmplitude γ₀ p
  have hA : IsAmplitude m A := isAmplitude_localizedAmplitude m p hp γ₀ hγ₀
  have hAsupp : tsupport (Function.uncurry A) ⊆ tsupport γ₀ := by
    apply closure_minimal ?_ (isClosed_tsupport γ₀)
    intro z hz
    by_contra hout
    apply hz
    funext ξ
    simp only [A, Function.uncurry, localizedAmplitude, Prod.eta,
      image_eq_zero_of_notMem_tsupport hout, zero_smul, Pi.zero_apply]
  have hcA : HasCompactSupport (Function.uncurry A) :=
    hcγ₀.of_isClosed_subset (isClosed_tsupport _) hAsupp
  let N := amplitudeOperator m A hA hcA
  have hN (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      N v x = amplitudeApply A v x := amplitudeOperator_apply m A hA hcA v x
  have hNsupport : HasOperatorSupport (tsupport β) N :=
    hasOperatorSupport_amplitudeOperator m A hA hcA (tsupport β)
      (isClosed_tsupport β) (hAsupp.trans hγ₀supp)
  have hcoordinate : L.coordinateOperator = N + Q := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    exact (hsplit v x).trans (congrArg (fun z ↦ z + Q v x) (hN v x).symm)
  -- New common plateaus reconstruct L; its old input/output cutoffs occur only inside p.
  let C : BundleChartCutoff (r := r) E L.chart := {
    L.input with
    cutoff := δ
    smooth_cutoff := hδ
    compact_support := hcδ
    support_subset := fun z hz ↦ (hδsupp hz).1 }
  let D : BundleChartCutoff (r := q) F L.chart := {
    L.output with
    cutoff := δ
    smooth_cutoff := hδ
    compact_support := hcδ
    support_subset := fun z hz ↦ ⟨(hδsupp hz).1.1, (hδsupp hz).2⟩ }
  have hplateau (z : X) (hz : z ∈ tsupport L.output.cutoff ∪ tsupport L.input.cutoff) :
      δ z = 1 := by
    apply hδone
    apply subset_tsupport β
    have hβz : β z = 1 := interior_subset (s := {x | β x = 1}) (hβone hz)
    change β z ≠ 0
    rw [hβz]
    exact one_ne_zero
  have hnative := L.extend_coordinateOperator_localize C D rfl rfl
    (fun z hz ↦ hplateau z (Or.inr hz)) (fun z hz ↦ hplateau z (Or.inl hz))
  obtain ⟨S, _, hS⟩ := exists_compactKernelLift μ L.chart L.chart_mem_atlas C D k hk Q hkQ
  have hSmap : S.toLinearMap μ = (D.extendLinearMap L.chart_mem_atlas).comp
      (Q.toLinearMap.comp (C.localizeLinearMap L.chart_mem_atlas)) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    exact hS u x
  refine ⟨C, D, N, Q, S, rfl, rfl, rfl, rfl, hN, hNsupport, hQ,
    hcoordinate, hSmap, ?_⟩
  rw [← hnative, hcoordinate, hSmap]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  exact congrArg (fun v : smoothSections (n := n) (r := q) F ↦ v.val x)
    (map_add (D.extendLinearMap L.chart_mem_atlas)
      (N (C.localize L.chart_mem_atlas u)) (Q (C.localize L.chart_mem_atlas u)))

private theorem amplitudeApply_comp_multipliers
    (m : ℝ) (a : AmplitudeFunction n r q) (ha : IsAmplitude m a)
    (hca : HasCompactSupport (Function.uncurry a))
    (Cout : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (Cin : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hCin : ContDiff ℝ ∞ Cin) (hcCin : HasCompactSupport Cin)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    amplitudeApply (fun x y ξ ↦ (Cout x).comp ((a x y ξ).comp (Cin y))) u x =
      Cout x (amplitudeApply a (matrixMultiplierCLM Cin hCin hcCin u) x) := by
  let v := matrixMultiplierCLM Cin hCin hcCin u
  have hv (y : EuclideanSpace ℝ (Fin n)) : v y = Cin y (u y) :=
    matrixMultiplierCLM_apply Cin hCin hcCin u y
  unfold amplitudeApply
  rw [ContinuousLinearMap.map_smul_of_tower]
  congr 1
  rw [← (Cout x).integral_comp_comm (integrable_amplitudeApply_outer m a ha hca v x)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [← (Cout x).integral_comp_comm (integrable_amplitudeApply_inner m a ha hca v x ξ)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [ContinuousLinearMap.comp_apply, map_smul, hv]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)

omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in
-- All coordinate changes, frame maps, cutoffs and the native near operator are fixed witnesses.
/-- The agreed localized amplitude is the actual conjugate of the fixed native near part. -/
theorem PseudodifferentialPiece.amplitudeApply_equivariantLocalizedAmplitude {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (β δ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hδone : tsupport β ⊆ {x | δ x = 1})
    (C : BundleChartCutoff (r := r) E L.chart)
    (D : BundleChartCutoff (r := q) F L.chart)
    (hCframe : C.frame = L.input.frame) (hDframe : D.frame = L.output.frame)
    (hCcut : C.cutoff = δ) (hDcut : D.cutoff = δ)
    (γ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (hγ₀ : ContDiff ℝ ∞ γ₀) (hcγ₀ : HasCompactSupport γ₀)
    (hγ₀supp : tsupport γ₀ ⊆ tsupport β ×ˢ tsupport β)
    (N : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hN : ∀ v x, N v x = amplitudeApply
      (localizedAmplitude γ₀ (cutoffSymbol L.output.cutoff L.input.cutoff L.symbol)) v x)
    (hNsupp : HasOperatorSupport (tsupport β) N)
    (g : G) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (hoverlap : tsupport A.cutoff ⊆ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
      (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) :
    let X := EuclideanSpace ℝ (Fin n)
    let d := Diffeomorph.smul (M := M) IG 𝓘(ℝ, X) ∞ g
    let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
    let γ := fun z : X × X ↦ A.cutoff z.1 * A.cutoff z.2 * γ₀ (t.symm z.1, t.symm z.2)
    ∀ (W : Set (X × X)), IsOpen W →
      tsupport δ ⊆ t.source →
      (∀ z ∈ W, segment ℝ z.2 z.1 ⊆ t.target) →
      (∀ z ∈ W, (averagedFDeriv t.symm z.1 z.2).IsInvertible) →
      ContDiff ℝ ∞ γ → HasCompactSupport γ → tsupport γ ⊆ W →
      (∀ z ∈ t '' tsupport β, A.cutoff z = 1) →
      ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) z,
        amplitudeApply (L.equivariantLocalizedAmplitude IG σ τ c A B γ₀ g) u z =
          B.localize hc (τ.smoothSectionRepresentation IG hτ g
            (D.extend L.chart_mem_atlas (N (C.localize L.chart_mem_atlas
              (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u)))))) z := by
  classical
  dsimp only
  intro W hW hδt hseg hinv hγ hcγ hγW hAone u z
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
  let I := 𝓘(ℝ, X)
  let d := Diffeomorph.smul (M := M) IG I ∞ g
  let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
  let old (y : X) := g⁻¹ • c.symm y
  let γ (y : X × X) := A.cutoff y.1 * A.cutoff y.2 * γ₀ (t.symm y.1, t.symm y.2)
  let p := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  have hp : IsSymbol univ m p := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff
    L.output.compact_support L.input.compact_support
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) L.chart_mem_atlas
  have ht : ContDiffOn ℝ ∞ t t.source := by
    intro y hy
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1
    have hmove := d.contMDiffAt.comp y hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hcM hy.2.2).comp y hmove).contDiffAt.contDiffWithinAt
  have hts : ContDiffOn ℝ ∞ t.symm t.target := by
    intro y hy
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1
    have hmove := d.symm.contMDiffAt.comp y hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y hmove).contDiffAt.contDiffWithinAt
  let V₀ := symbolChartDomain E F c A.frame B.frame ∩ (fun y ↦ old y) ⁻¹'
    (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)
  have hcV : ContMDiffOn I I ∞ c.symm (symbolChartDomain E F c A.frame B.frame) := by
    intro y hy
    exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1).contMDiffWithinAt
  have holdV := d.symm.contMDiff.comp_contMDiffOn hcV
  have hV : IsOpen V₀ := holdV.continuousOn.isOpen_inter_preimage
    (isOpen_symbolChartDomain E F c A.frame B.frame)
    ((L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet)
  have hAV : tsupport A.cutoff ⊆ V₀ := by
    intro y hy
    exact ⟨⟨A.support_subset hy, (B.support_subset (by rwa [← hAB])).2⟩, hoverlap hy⟩
  have hVt : V₀ ⊆ t.target := fun y hy ↦ ⟨⟨hy.1.1.1, mem_univ _⟩, hy.2.1.1⟩
  let Ri (y : X) := (L.input.frame.continuousLinearMapAt ℂ (old y)).comp
    ((σ.linearMap g⁻¹ (c.symm y)).toContinuousLinearMap.comp (A.frame.symmL ℂ (c.symm y)))
  let Ro (y : X) := (B.frame.continuousLinearMapAt ℂ (g • old y)).comp
    ((τ.linearMap g (old y)).toContinuousLinearMap.comp (L.output.frame.symmL ℂ (old y)))
  let Cin := cutoffMatrix A.cutoff Ri
  let Cout := cutoffMatrix A.cutoff Ro
  have hRi : ContDiffOn ℝ ∞ Ri V₀ :=
    contDiffOn_equivariantFrameMap IG σ hσ g⁻¹ A.frame L.input.frame V₀ c.symm
      (hcV.mono inter_subset_left) (fun y hy ↦ hy.1.1.2) (fun y hy ↦ hy.2.1.2)
  have hCin : ContDiff ℝ ∞ Cin :=
    contDiff_cutoffMatrix V₀ hV Ri hRi A.cutoff A.smooth_cutoff hAV
  have hcCin : HasCompactSupport Cin :=
    hasCompactSupport_cutoffMatrix A.cutoff Ri A.compact_support
  let Tin := matrixMultiplierCLM Cin hCin hcCin
  have hTin (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (y : X) :
      Tin v y = A.cutoff y • Ri y (v y) := by
    rw [matrixMultiplierCLM_apply]
    rfl
  have hδ : ContDiff ℝ ∞ δ := hCcut ▸ C.smooth_cutoff
  have hcδ : HasCompactSupport δ := hCcut ▸ C.compact_support
  have hβt : tsupport β ⊆ t.source := by
    intro y hy
    apply hδt
    apply subset_tsupport δ
    change δ y ≠ 0
    rw [hδone hy]
    exact one_ne_zero
  -- On one open neighborhood of the near operator's support, the actual
  -- source localization equals the compact coordinate input pullback.
  have hinputFrame (v : smoothSections (n := n) (r := r) E) (y : X) (hy : y ∈ V₀) :
      Ri y ((A.frame ⟨c.symm y, v.val (c.symm y)⟩).2) =
        (L.input.frame ⟨old y,
          (σ.smoothSectionRepresentation IG hσ g⁻¹ v).val (old y)⟩).2 := by
    change _ = (L.input.frame ⟨g⁻¹ • c.symm y,
      σ.sectionLinearMap g⁻¹ v.val (g⁻¹ • c.symm y)⟩).2
    rw [σ.sectionLinearMap_smul]
    simp [Ri, old, ContinuousLinearMap.comp_apply,
      A.frame.symmL_apply hy.1.1.2,
      A.frame.symm_apply_apply_mk hy.1.1.2,
      L.input.frame.continuousLinearMapAt_apply_of_mem ℂ hy.2.1.2]
  let v := C.localize L.chart_mem_atlas
    (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u))
  let v' := cutoffPullbackCLM t.source t.open_source t ht δ hδ hcδ hδt (Tin u)
  let O := t.source ∩ t ⁻¹' V₀
  have hO : IsOpen O := t.continuousOn.isOpen_inter_preimage t.open_source hV
  have hβO : tsupport β ⊆ O := by
    intro y hy
    refine ⟨hβt hy, hAV ?_⟩
    apply subset_tsupport A.cutoff
    change A.cutoff (t y) ≠ 0
    rw [hAone _ ⟨y, hy, rfl⟩]
    exact one_ne_zero
  have hvnear (y : X) (hy : y ∈ O) : v' y = v y := by
    have hyt := hy.1
    have hyV := hy.2
    have hcw : c.symm (t y) = g • L.chart.symm y := c.left_inv hyt.2.2
    have hOld : old (t y) = L.chart.symm y := by
      change g⁻¹ • c.symm (t y) = _
      rw [hcw, inv_smul_smul]
    have hframes := hinputFrame (A.extend hc u) (t y) hyV
    have hframeExt : (A.frame ⟨c.symm (t y), (A.extend hc u).val (c.symm (t y))⟩).2 =
        (A.cutoff (t y) : ℂ) • u (t y) := by
      change (A.frame ⟨c.symm (t y), A.extendedFunction u (c.symm (t y))⟩).2 = _
      rw [BundleChartCutoff.extendedFunction,
        ite_eq_left (c.map_target hyV.1.1.1), c.right_inv hyV.1.1.1]
      change (A.frame.linearEquivAt ℂ _ hyV.1.1.2)
        ((A.cutoff (t y) : ℂ) • A.frame.symmL ℂ (c.symm (t y)) (u (t y))) = _
      rw [map_smul, A.frame.symmL_apply hyV.1.1.2]
      exact LinearEquiv.apply_symm_apply _ _ |> congrArg ((A.cutoff (t y) : ℂ) • ·)
    rw [hframeExt, map_smul, hOld] at hframes
    change (cutoffPullbackCLM t.source t.open_source t ht δ hδ hcδ hδt (Tin u)) y =
      C.localizedFunction (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u)) y
    rw [cutoffPullbackCLM_apply, hTin]
    simp only [BundleChartCutoff.localizedFunction, sectionInChart,
      hCcut, hCframe]
    rw [← hframes]
    simp only [Complex.coe_smul]
    have hychart : y ∈ L.chart.target := hyt.1
    rw [ite_eq_left hychart]
  have hNinput : N v' = N v := by
    have hdis : Disjoint (tsupport (v' - v)) (tsupport β) := by
      apply Set.disjoint_left.mpr
      intro y hy hyβ
      apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hy
      filter_upwards [hO.mem_nhds (hβO hyβ)] with w hw
      simp only [sub_apply, hvnear w hw, sub_self, Pi.zero_apply]
    exact sub_eq_zero.mp (by simpa only [map_sub] using hNsupp.2 (v' - v) hdis)
  -- The fixed source cutoff transforms to precisely the agreed target cutoff.
  have hγsource : tsupport γ₀ ⊆ t.source ×ˢ t.source :=
    hγ₀supp.trans (Set.prod_mono hβt hβt)
  have hspec (y : X × X) (hy : y ∈ t.source ×ˢ t.source) :
      γ₀ y = γ (t y.1, t y.2) := by
    simp only [γ, t.left_inv hy.1, t.left_inv hy.2]
    by_cases h : γ₀ y = 0
    · simp [h]
    · have hs := hγ₀supp (subset_tsupport γ₀ h)
      rw [hAone _ ⟨y.1, hs.1, rfl⟩, hAone _ ⟨y.2, hs.2, rfl⟩]
      simp
  have hδγ : Prod.snd '' tsupport γ₀ ⊆ {y | δ y = 1} := by
    rintro y ⟨w, hw, rfl⟩
    exact hδone (hγ₀supp hw).2
  have hcoord : IsAmplitude m (coordinateAmplitude t γ p) :=
    isAmplitude_coordinateAmplitude t ht hts m p (hp.restrict (subset_univ _))
      W hW hseg hinv γ hγ hcγ hγW
  have hccoord : HasCompactSupport (Function.uncurry (coordinateAmplitude t γ p)) :=
    hasCompactSupport_coordinateAmplitude t γ p hcγ
  have hmatrix : amplitudeApply (L.equivariantLocalizedAmplitude IG σ τ c A B γ₀ g) u z =
      Cout z (amplitudeApply (coordinateAmplitude t γ p) (Tin u) z) :=
    amplitudeApply_comp_multipliers m (coordinateAmplitude t γ p) hcoord hccoord
      Cout Cin hCin hcCin u z
  rw [hmatrix]
  by_cases hz : z ∈ tsupport A.cutoff
  · have hzV := hAV hz
    have hzt := hVt hzV
    rw [← amplitudeApply_coordinateAmplitude_eq t ht hts m p hp W hW hseg hinv γ γ₀
      hγ hcγ hγW hγ₀ hcγ₀ hγsource hspec δ hδ hcδ hδt hδγ (Tin u) z hzt,
      ← hN]
    change Cout z (N v' (t.symm z)) = _
    rw [hNinput]
    let s := D.extend L.chart_mem_atlas (N v)
    have hδout : δ (t.symm z) • N v (t.symm z) = N v (t.symm z) := by
      by_cases hs : t.symm z ∈ tsupport β
      · rw [hδone hs, one_smul]
      · have hzero : N v (t.symm z) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h ↦ hs (hNsupp.1 v h))
        rw [hzero, smul_zero]
    have hsframe : (L.output.frame ⟨old z, s.val (old z)⟩).2 = N v (t.symm z) := by
      change (L.output.frame ⟨old z, D.extendedFunction (N v) (old z)⟩).2 = _
      rw [BundleChartCutoff.extendedFunction, ite_eq_left hzV.2.1.1, hDcut]
      simp only [hDframe]
      change (L.output.frame.linearEquivAt ℂ (old z) hzV.2.2)
        ((δ (t.symm z) : ℂ) • L.output.frame.symmL ℂ (old z) (N v (t.symm z))) = _
      rw [map_smul, L.output.frame.symmL_apply hzV.2.2]
      change (δ (t.symm z) : ℂ) • (L.output.frame.linearEquivAt ℂ (old z) hzV.2.2)
        ((L.output.frame.linearEquivAt ℂ (old z) hzV.2.2).symm (N v (t.symm z))) = _
      rw [LinearEquiv.apply_symm_apply, Complex.coe_smul]
      exact hδout
    have houtputFrame : Ro z ((L.output.frame ⟨old z, s.val (old z)⟩).2) =
        (B.frame ⟨c.symm z,
          (τ.smoothSectionRepresentation IG hτ g s).val (c.symm z)⟩).2 := by
      have hreturn : g • old z = c.symm z := smul_inv_smul g (c.symm z)
      have hBbase : g • old z ∈ B.frame.baseSet := hreturn ▸ hzV.1.2
      have hpair := τ.mk_sectionLinearMap g s.val (c.symm z)
      change (⟨c.symm z, (τ.smoothSectionRepresentation IG hτ g s).val (c.symm z)⟩ :
        TotalSpace Unit F) = ⟨g • old z, τ.linearMap g (old z) (s.val (old z))⟩ at hpair
      have hframepair := congrArg (fun v : TotalSpace Unit F ↦
        (B.frame (⟨v.proj, v.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin q)) F)).2) hpair
      rw [hframepair]
      simp [Ro, ContinuousLinearMap.comp_apply, L.output.frame.symmL_apply hzV.2.2,
        L.output.frame.symm_apply_apply_mk hzV.2.2,
        B.frame.continuousLinearMapAt_apply_of_mem ℂ hBbase]
    change A.cutoff z • Ro z (N v (t.symm z)) =
      B.localizedFunction (τ.smoothSectionRepresentation IG hτ g s) z
    rw [← hsframe, houtputFrame]
    simp only [BundleChartCutoff.localizedFunction, sectionInChart,
      ite_eq_left hzV.1.1.1, ← hAB, Complex.coe_smul]
  · have hAz : A.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hz
    have hBz : B.cutoff z = 0 := by rwa [← hAB]
    simp [Cout, cutoffMatrix, hAz, BundleChartCutoff.localize,
      BundleChartCutoff.localizedFunction, hBz]

omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
omit [T2Space M] [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsManifold IG ∞ G] in
set_option maxSynthPendingDepth 30 in
include hσ hτ in
/-- The fixed localized amplitude is smooth and has compact spatial support. -/
theorem PseudodifferentialPiece.contDiff_equivariantLocalizedAmplitude {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (γ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (g : G) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (hoverlap : tsupport A.cutoff ⊆ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
      (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) :
    let X := EuclideanSpace ℝ (Fin n)
    let d := Diffeomorph.smul (M := M) IG 𝓘(ℝ, X) ∞ g
    let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
    let γ := fun z : X × X ↦ A.cutoff z.1 * A.cutoff z.2 * γ₀ (t.symm z.1, t.symm z.2)
    ∀ (W : Set (X × X)), IsOpen W →
      (∀ z ∈ W, segment ℝ z.2 z.1 ⊆ t.target) →
      (∀ z ∈ W, (averagedFDeriv t.symm z.1 z.2).IsInvertible) →
      ContDiff ℝ ∞ γ → HasCompactSupport γ → tsupport γ ⊆ W →
      ContDiff ℝ ∞ (fun z : (X × X) × X ↦
        L.equivariantLocalizedAmplitude IG σ τ c A B γ₀ g z.1.1 z.1.2 z.2) ∧
      HasCompactSupport (Function.uncurry
        (L.equivariantLocalizedAmplitude IG σ τ c A B γ₀ g)) := by
  classical
  dsimp only
  intro W hW hseg hinv hγ hcγ hγW
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
  let I := 𝓘(ℝ, X)
  let d := Diffeomorph.smul (M := M) IG I ∞ g
  let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
  let old (y : X) := g⁻¹ • c.symm y
  let γ (y : X × X) := A.cutoff y.1 * A.cutoff y.2 * γ₀ (t.symm y.1, t.symm y.2)
  let p := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  have hp : IsSymbol univ m p := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff
    L.output.compact_support L.input.compact_support
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) L.chart_mem_atlas
  have ht : ContDiffOn ℝ ∞ t t.source := by
    intro y hy
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1
    have hmove := d.contMDiffAt.comp y hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hcM hy.2.2).comp y hmove).contDiffAt.contDiffWithinAt
  have hts : ContDiffOn ℝ ∞ t.symm t.target := by
    intro y hy
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1
    have hmove := d.symm.contMDiffAt.comp y hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y hmove).contDiffAt.contDiffWithinAt
  let V₀ := symbolChartDomain E F c A.frame B.frame ∩ (fun y ↦ old y) ⁻¹'
    (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)
  have hcV : ContMDiffOn I I ∞ c.symm (symbolChartDomain E F c A.frame B.frame) := by
    intro y hy
    exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1).contMDiffWithinAt
  have holdV := d.symm.contMDiff.comp_contMDiffOn hcV
  have hV : IsOpen V₀ := holdV.continuousOn.isOpen_inter_preimage
    (isOpen_symbolChartDomain E F c A.frame B.frame)
    ((L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet)
  have hAV : tsupport A.cutoff ⊆ V₀ := by
    intro y hy
    exact ⟨⟨A.support_subset hy, (B.support_subset (by rwa [← hAB])).2⟩, hoverlap hy⟩
  have hVt : V₀ ⊆ t.target := fun y hy ↦ ⟨⟨hy.1.1.1, mem_univ _⟩, hy.2.1.1⟩
  let Ri (y : X) := (L.input.frame.continuousLinearMapAt ℂ (old y)).comp
    ((σ.linearMap g⁻¹ (c.symm y)).toContinuousLinearMap.comp (A.frame.symmL ℂ (c.symm y)))
  let Ro (y : X) := (B.frame.continuousLinearMapAt ℂ (g • old y)).comp
    ((τ.linearMap g (old y)).toContinuousLinearMap.comp (L.output.frame.symmL ℂ (old y)))
  let Cin := cutoffMatrix A.cutoff Ri
  let Cout := cutoffMatrix A.cutoff Ro
  have hRi : ContDiffOn ℝ ∞ Ri V₀ :=
    contDiffOn_equivariantFrameMap IG σ hσ g⁻¹ A.frame L.input.frame V₀ c.symm
      (hcV.mono inter_subset_left) (fun y hy ↦ hy.1.1.2) (fun y hy ↦ hy.2.1.2)
  have hCin : ContDiff ℝ ∞ Cin :=
    contDiff_cutoffMatrix V₀ hV Ri hRi A.cutoff A.smooth_cutoff hAV
  have hcCin : HasCompactSupport Cin :=
    hasCompactSupport_cutoffMatrix A.cutoff Ri A.compact_support
  have hRo : ContDiffOn ℝ ∞ Ro V₀ := by
    apply contDiffOn_equivariantFrameMap IG τ hτ g L.output.frame B.frame V₀ old
      (holdV.mono inter_subset_left) (fun y hy ↦ hy.2.2)
    intro y hy
    change g • (g⁻¹ • c.symm y) ∈ B.frame.baseSet
    rw [smul_inv_smul]
    exact hy.1.2
  have hCout : ContDiff ℝ ∞ Cout :=
    contDiff_cutoffMatrix V₀ hV Ro hRo A.cutoff A.smooth_cutoff hAV
  have hcoord : IsAmplitude m (coordinateAmplitude t γ p) :=
    isAmplitude_coordinateAmplitude t ht hts m p (hp.restrict (subset_univ _))
      W hW hseg hinv γ hγ hcγ hγW
  constructor
  · change ContDiff ℝ ∞ (fun z : (X × X) × X ↦
      (Cout z.1.1).comp ((coordinateAmplitude t γ p z.1.1 z.1.2 z.2).comp (Cin z.1.2)))
    have hcomp {a b c : ℕ} : ContDiff ℝ ∞
        (fun z : (EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c)) ×
          (EuclideanSpace ℂ (Fin a) →L[ℂ] EuclideanSpace ℂ (Fin b)) ↦ z.1.comp z.2) :=
      (contDiff_fst.clm_comp contDiff_snd : ContDiff ℂ ∞ _).restrict_scalars ℝ
    exact hcomp.comp ((hCout.comp (contDiff_fst.comp contDiff_fst)).prodMk
      (hcomp.comp (hcoord.1.prodMk (hCin.comp (contDiff_snd.comp contDiff_fst)))))
  · have hs : tsupport (Function.uncurry
        (L.equivariantLocalizedAmplitude IG σ τ c A B γ₀ g)) ⊆
        tsupport A.cutoff ×ˢ tsupport A.cutoff := by
      apply closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
      intro z hz
      by_contra h
      rcases not_and_or.mp h with h | h
      · apply hz
        funext ξ
        change (Cout z.1).comp ((coordinateAmplitude t γ p z.1 z.2 ξ).comp (Cin z.2)) = 0
        simp [Cout, cutoffMatrix, image_eq_zero_of_notMem_tsupport h]
      · apply hz
        funext ξ
        change (Cout z.1).comp ((coordinateAmplitude t γ p z.1 z.2 ξ).comp (Cin z.2)) = 0
        simp [Cin, cutoffMatrix, image_eq_zero_of_notMem_tsupport h]
    exact (A.compact_support.prod A.compact_support).of_isClosed_subset
      (isClosed_tsupport _) hs

omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
set_option maxSynthPendingDepth 30 in
/-- Target plateaus remove both localization round trips from the same near operator. -/
theorem PseudodifferentialPiece.extend_localize_equivariant_near {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (β : EuclideanSpace ℝ (Fin n) → ℝ) (hcβ : HasCompactSupport β)
    (C : BundleChartCutoff (r := r) E L.chart)
    (D : BundleChartCutoff (r := q) F L.chart)
    (N : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
    (hNsupp : HasOperatorSupport (tsupport β) N)
    (g : G) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff) :
    let d := Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g
    let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
    tsupport β ⊆ t.source → t '' tsupport β ⊆ interior {z | A.cutoff z = 1} →
    ∀ u : smoothSections (n := n) (r := r) E,
      B.extend hc (B.localize hc (τ.smoothSectionRepresentation IG hτ g
        (D.extend L.chart_mem_atlas (N (C.localize L.chart_mem_atlas
          (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc (A.localize hc u)))))))) =
      τ.smoothSectionRepresentation IG hτ g
        (D.extend L.chart_mem_atlas (N (C.localize L.chart_mem_atlas
          (σ.smoothSectionRepresentation IG hσ g⁻¹ u)))) := by
  classical
  dsimp only
  intro hβt hone u
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let d := Diffeomorph.smul (M := M) IG 𝓘(ℝ, X) ∞ g
  let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
  let K₀ := L.chart.symm '' tsupport β
  let K := (fun x : M ↦ g • x) '' K₀
  have hK₀ : IsCompact K₀ := hcβ.image_of_continuousOn
    (L.chart.continuousOn_symm.mono (fun y hy ↦ (hβt hy).1))
  have hK : IsCompact K := hK₀.image (continuous_const_smul g)
  have hχone (y : X) (hy : y ∈ t.source)
      (hχ : A.cutoff (t y) = 1) :
      g • L.chart.symm y ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet := by
    have hs : t y ∈ tsupport A.cutoff := subset_tsupport _ (by
      change A.cutoff (t y) ≠ 0
      rw [hχ]
      exact one_ne_zero)
    have hreturn : c.symm (t y) = g • L.chart.symm y := c.left_inv hy.2.2
    exact ⟨⟨hy.2.2, hreturn ▸ (A.support_subset hs).2⟩,
      hreturn ▸ (B.support_subset (by rwa [← hAB])).2⟩
  have hbase : K ⊆ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet := by
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact hχone z (hβt hz)
      (interior_subset (s := {z | A.cutoff z = 1}) (hone ⟨z, hz, rfl⟩))
  have hKone (x : M) (hx : x ∈ K) : A.cutoff (c x) = 1 := by
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
    exact interior_subset (s := {z | A.cutoff z = 1}) (hone ⟨z, hz, rfl⟩)
  have hinputRoundtrip (x : M) (hxc : x ∈ c.source) (hxf : x ∈ A.frame.baseSet)
      (hχ : A.cutoff (c x) = 1) : (A.extend hc (A.localize hc u)).val x = u.val x := by
    change A.extendedFunction (A.localize hc u) x = _
    simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
    change (A.cutoff (c x) : ℂ) • A.frame.symmL ℂ x (A.localizedFunction u (c x)) = _
    rw [hχ, Complex.ofReal_one, one_smul]
    simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
      sectionInChart]
    rw [c.left_inv hxc, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ hxf]
    rw [hχ, Complex.ofReal_one, one_smul, A.frame.symmL_continuousLinearMapAt hxf]
  -- The input difference vanishes on an open neighborhood of the specified near support.
  let v₁ := C.localize L.chart_mem_atlas
    (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc (A.localize hc u)))
  let v₂ := C.localize L.chart_mem_atlas (σ.smoothSectionRepresentation IG hσ g⁻¹ u)
  let O := t.source ∩ t ⁻¹' interior {z | A.cutoff z = 1}
  have hO : IsOpen O := t.continuousOn.isOpen_inter_preimage t.open_source isOpen_interior
  have hβO : tsupport β ⊆ O := fun y hy ↦ ⟨hβt hy, hone ⟨y, hy, rfl⟩⟩
  have hinput : N v₁ = N v₂ := by
    have hdiff : Disjoint (tsupport (v₁ - v₂)) (tsupport β) := by
      apply Set.disjoint_left.mpr
      intro y hy hyβ
      apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hy
      filter_upwards [hO.mem_nhds (hβO hyβ)] with z hz
      have hχ : A.cutoff (t z) = 1 := interior_subset (s := {z | A.cutoff z = 1}) hz.2
      have hbasez := hχone z hz.1 hχ
      have hvalues : (σ.smoothSectionRepresentation IG hσ g⁻¹
          (A.extend hc (A.localize hc u))).val (L.chart.symm z) =
          (σ.smoothSectionRepresentation IG hσ g⁻¹ u).val (L.chart.symm z) := by
        apply TotalSpace.mk_injective (F := Unit) (L.chart.symm z)
        change (⟨L.chart.symm z, σ.sectionLinearMap g⁻¹
          (A.extend hc (A.localize hc u)).val (L.chart.symm z)⟩ : TotalSpace Unit E) =
          ⟨L.chart.symm z, σ.sectionLinearMap g⁻¹ u.val (L.chart.symm z)⟩
        rw [σ.mk_sectionLinearMap, σ.mk_sectionLinearMap, inv_inv]
        rw [hinputRoundtrip _ hbasez.1.1 hbasez.1.2 hχ]
      change C.localizedFunction _ z - C.localizedFunction _ z = 0
      simp only [BundleChartCutoff.localizedFunction, sectionInChart, hvalues, sub_self]
    exact sub_eq_zero.mp (by simpa only [map_sub] using hNsupp.2 (v₁ - v₂) hdiff)
  -- The native near output is supported in the very same transported compact set.
  have hnativeSupport : closure {x | (D.extend L.chart_mem_atlas (N v₂)).val x ≠ 0} ⊆ K₀ := by
    apply closure_minimal ?_ hK₀.isClosed
    intro x hx
    by_contra hout
    apply hx
    change D.extendedFunction (N v₂) x = 0
    by_cases hxc : x ∈ L.chart.source
    · have hcoord : L.chart x ∉ tsupport β := fun h ↦ hout ⟨L.chart x, h, L.chart.left_inv hxc⟩
      have hz : N v₂ (L.chart x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hcoord (hNsupp.1 v₂ h))
      simp [BundleChartCutoff.extendedFunction, hxc, hz]
    · simp [BundleChartCutoff.extendedFunction, hxc]
  let s := τ.smoothSectionRepresentation IG hτ g (D.extend L.chart_mem_atlas (N v₂))
  have hsupp : closure {x | s.val x ≠ 0} ⊆ K := by
    change closure {x | τ.sectionLinearMap g
      (D.extend L.chart_mem_atlas (N v₂)).val x ≠ 0} ⊆ _
    rw [τ.closure_support_sectionLinearMap]
    exact Set.image_mono hnativeSupport
  have houtput : B.extend hc (B.localize hc s) = s := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ K
    · have hxc := (hbase hx).1.1
      have hxf := (hbase hx).2
      have hχ : B.cutoff (c x) = 1 := by rw [← hAB]; exact hKone x hx
      change B.extendedFunction (B.localize hc s) x = s.val x
      simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
      change (B.cutoff (c x) : ℂ) • B.frame.symmL ℂ x (B.localizedFunction s (c x)) = _
      rw [hχ, Complex.ofReal_one, one_smul]
      simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
        sectionInChart]
      rw [c.left_inv hxc, ← B.frame.continuousLinearMapAt_apply_of_mem ℂ hxf]
      rw [hχ, Complex.ofReal_one, one_smul, B.frame.symmL_continuousLinearMapAt hxf]
    · have hz : s.val x = 0 := by
        by_contra hne
        exact hx (hsupp (subset_closure hne))
      change B.extendedFunction (B.localize hc s) x = s.val x
      by_cases hxc : x ∈ c.source
      · simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
        change (B.cutoff (c x) : ℂ) • B.frame.symmL ℂ x (B.localizedFunction s (c x)) = _
        simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
          sectionInChart]
        rw [c.left_inv hxc, hz]
        by_cases hxf : x ∈ B.frame.baseSet
        · rw [show (B.frame ⟨x, (0 : F x)⟩).2 = 0 from (B.frame.linear ℂ hxf).map_zero]
          simp
        · rw [B.frame.symmL_apply_of_notMem (R := ℂ) hxf]
          simp
      · simp [BundleChartCutoff.extendedFunction, hxc, hz]
  change B.extend hc (B.localize hc (τ.smoothSectionRepresentation IG hτ g
    (D.extend L.chart_mem_atlas (N v₁)))) = s
  rw [hinput]
  exact houtput

end AtiyahSinger
