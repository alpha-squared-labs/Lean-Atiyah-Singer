/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DualTranspose
public import AtiyahSinger.Analysis.FrameChange
public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator
public import AtiyahSinger.Analysis.LocalTranspose

import AtiyahSinger.Geometry.HermitianMetricDual

/-!
# Global pseudodifferential transposes on actual dual bundles

Public module ID: M0684.

SG III.(3.18) and Theorem 3.17(iv), with arbitrary real order.
Transpose the smooth kernel by swapping its variables and precomposing covectors.
For a local PDO piece, swap cutoffs and use the local bilinear transpose with the
positive density weight. Finite sums give the unique global transpose and its order.
The Sobolev transpose is actual precomposition transported by geometric duality.
A Hermitian metric is not part of the transpose data. No ellipticity, closed-range
or homogeneous-symbol hypothesis is imposed.
The global principal-symbol transpose comparison remains a separate interface.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 15

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

/-- Swapping the variables and taking the continuous dual map preserves kernel smoothness. -/
theorem SmoothKernel.isSmooth_transpose
    (K : SmoothKernel (n := n) (r := r) (q := q) E F) :
    IsSmoothKernel (n := n) (r := q) (q := r) (DualBundle F) (DualBundle E)
      (fun x y ↦ (ContinuousLinearMap.compL ℂ (E x) (F y) ℂ).flip (K.toFun y x)) := by
  /- In induced dual frames the new matrix is the ordinary transpose of the old
  matrix at (y,x). The swap of product variables and this fixed complex-linear
  matrix operation preserve real smoothness. Every frame in the dual atlas is an
  induced frame, so these local identities give precisely IsSmoothKernel. -/
  classical
  rintro _ _ ⟨f, hf, rfl⟩ ⟨e, he, rfl⟩
  let := hf
  let := he
  rw [dualFrame_baseSet, dualFrame_baseSet]
  let D := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin r))
    (EuclideanSpace ℂ (Fin q)) ℂ).flip
  let R := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin q))
    (StrongDual ℂ (EuclideanSpace ℂ (Fin q)))
    (StrongDual ℂ (EuclideanSpace ℂ (Fin r)))).flip
      (dualModelEquiv q).symm.toContinuousLinearMap
  let L := ((ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin q))
    (StrongDual ℂ (EuclideanSpace ℂ (Fin r))) (EuclideanSpace ℂ (Fin r)))
      (dualModelEquiv r).toContinuousLinearMap).comp (R.comp D)
  -- Swap the original product variables and apply a fixed linear transpose on model fibers.
  have hmatrix := (K.isSmooth e f).comp
    (contMDiffOn_snd.prodMk contMDiffOn_fst)
    (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ ⟨hz.2, hz.1⟩)
  apply ((L.restrictScalars ℝ).contMDiff.comp_contMDiffOn hmatrix).congr
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  -- Induced dual coordinates recover the same covector, without any Hermitian conjugation.
  let β := (dualFrame F f).symmL ℂ z.2 v
  have hβ : β.comp (f.symmL ℂ z.2) = (dualModelEquiv q).symm v := by
    apply (dualModelEquiv q).injective
    rw [(dualModelEquiv q).apply_symm_apply]
    calc
      dualModelEquiv q (β.comp (f.symmL ℂ z.2)) =
          (dualFrame F f).continuousLinearMapAt ℂ z.2 β := by
        rw [(dualFrame F f).continuousLinearMapAt_apply_of_mem ℂ
          (by simpa only [dualFrame_baseSet] using hz.2)]
        rw [dualFrame_apply_snd F f (fun y ↦ (dualFrame F f).symmL ℂ y v) z.2 hz.2]
        ext j
        rw [dualModelEquiv_apply]
        change β (f.symmL ℂ z.2 (EuclideanSpace.single j 1)) = _
        rfl
      _ = v := (dualFrame F f).continuousLinearMapAt_symmL
        (by simpa only [dualFrame_baseSet] using hz.2) v
  ext j
  change ((dualFrame E e).continuousLinearMapAt ℂ z.1
    (β.comp (K.toFun z.2 z.1))) j =
      dualModelEquiv r (((dualModelEquiv q).symm v).comp
        (kernelInFrames E F K.toFun e f (z.2, z.1))) j
  rw [(dualFrame E e).continuousLinearMapAt_apply_of_mem ℂ
    (by simpa only [dualFrame_baseSet] using hz.1)]
  rw [dualFrame_apply_snd E e (fun y ↦ β.comp (K.toFun z.2 y)) z.1 hz.1]
  rw [dualModelEquiv_apply, ← hβ]
  change β (K.toFun z.2 z.1 (e.symmL ℂ z.1 (EuclideanSpace.single j 1))) =
    β (f.symmL ℂ z.2 (f.continuousLinearMapAt ℂ z.2
      (K.toFun z.2 z.1 (e.symmL ℂ z.1 (EuclideanSpace.single j 1)))))
  rw [f.symmL_continuousLinearMapAt hz.2]

/-- The actual transpose kernel sends α at y to α composed with K(y,x) at x. -/
def SmoothKernel.transpose (K : SmoothKernel (n := n) (r := r) (q := q) E F) :
    SmoothKernel (n := n) (r := q) (q := r) (DualBundle F) (DualBundle E) where
  toFun x y := (ContinuousLinearMap.compL ℂ (E x) (F y) ℂ).flip (K.toFun y x)
  isSmooth := K.isSmooth_transpose

variable [MeasurableSpace M] {μ : Measure M}

/-- The metric-free formal transpose is defined by actual dual evaluation with the same density. -/
def IsFormalTranspose
    (μ : Measure M)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E)) : Prop :=
  ∀ α u, (∫ x, (T α).val x (u.val x) ∂μ) = ∫ x, α.val x ((P u).val x) ∂μ

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSecond : SecondCountableTopology M]
  [hCompact : CompactSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hμ : IsSmoothPositiveMeasure (n := n) μ]

/-- Fubini identifies the swapped dual kernel with the formal transpose of its integral map. -/
theorem SmoothKernel.isFormalTranspose_toLinearMap
    (K : SmoothKernel (n := n) (r := r) (q := q) E F) :
    IsFormalTranspose μ (K.toLinearMap μ) (K.transpose.toLinearMap μ) := by
  /- On compact M times M the scalar function α(x)(K(x,y)u(y)) is integrable:
  finite frames reduce it to bounded smooth coefficients and the finite density.
  Move covector evaluation through the fiber integral, apply scalar Fubini, and
  rename x,y. The inner integral is exactly the swapped dual kernel's output.
  No conjugation or density ratio occurs because both sides use the same μ. -/
  classical
  intro α u
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let Φ (z : M × M) : ℂ := α.val z.1 (K.toFun z.1 z.2 (u.val z.2))
  -- In original frames, joint kernel evaluation is a composition of smooth bilinear maps.
  have hΦ : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, ℂ) ∞ Φ Set.univ := by
    intro z _
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z.2
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z.1
    have he : z.2 ∈ e.baseSet := mem_baseSet_trivializationAt _ _ z.2
    have hf : z.1 ∈ f.baseSet := mem_baseSet_trivializationAt _ _ z.1
    have hu := (u.property e inferInstance).comp
      (contMDiffOn_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
      (s := f.baseSet ×ˢ e.baseSet) (fun w hw ↦ hw.2)
    have hα := (((dualSectionsEquiv F).symm α).property f inferInstance).comp
      (contMDiffOn_fst (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
      (s := f.baseSet ×ˢ e.baseSet) (fun w hw ↦ hw.1)
    have hv := ((dualModelEquiv q).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn hα
    have happly : ContDiff ℝ ∞ (fun p :
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
          EuclideanSpace ℂ (Fin r) ↦ p.1 p.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hvalue := happly.contMDiff.comp_contMDiffOn ((K.isSmooth e f).prodMk_space hu)
    have heval : ContDiff ℝ ∞ (fun p :
        StrongDual ℂ (EuclideanSpace ℂ (Fin q)) × EuclideanSpace ℂ (Fin q) ↦
          p.1 p.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hlocal := heval.contMDiff.comp_contMDiffOn (hv.prodMk_space hvalue)
    have hactual := hlocal.congr (f₁ := Φ) (by
      intro w hw
      have hdual : (dualModelEquiv q).symm
          (dualSectionInFrame F f α.val w.1) = (α.val w.1).comp (f.symmL ℂ w.1) := by
        apply (dualModelEquiv q).injective
        rw [(dualModelEquiv q).apply_symm_apply]
        ext j
        rw [dualModelEquiv_apply]
        rfl
      change α.val w.1 (K.toFun w.1 w.2 (u.val w.2)) =
        (dualModelEquiv q).symm (dualSectionInFrame F f α.val w.1)
          (kernelInFrames E F K.toFun e f w ((e ⟨w.2, u.val w.2⟩).2))
      rw [hdual]
      change α.val w.1 (K.toFun w.1 w.2 (u.val w.2)) =
        α.val w.1 (f.symmL ℂ w.1 (f.continuousLinearMapAt ℂ w.1
          (K.toFun w.1 w.2 (e.symmL ℂ w.2 ((e ⟨w.2, u.val w.2⟩).2)))))
      rw [f.symmL_continuousLinearMapAt hw.1,
        ← e.continuousLinearMapAt_apply_of_mem ℂ hw.2,
        e.symmL_continuousLinearMapAt hw.2])
    exact (hactual.contMDiffAt ((f.open_baseSet.prod e.open_baseSet).mem_nhds
      ⟨hf, he⟩)).contMDiffWithinAt
  have hint : Integrable Φ (μ.prod μ) :=
    (continuousOn_univ.mp hΦ.continuousOn).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Evaluation commutes with each original fiber integral; scalar Fubini exchanges the inputs.
  calc
    (∫ x, (K.transpose.toLinearMap μ α).val x (u.val x) ∂μ) =
        ∫ x, ∫ y, Φ (y, x) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦
        K.transpose.dual_apply μ α x (ContinuousLinearMap.apply ℂ ℂ (u.val x)))
    _ = ∫ x, ∫ y, Φ (x, y) ∂μ ∂μ := (integral_integral_swap hint).symm
    _ = ∫ x, α.val x ((K.toLinearMap μ u).val x) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (K.dual_apply μ u x (α.val x)).symm)

include hM hT2 hSecond hCompact hBorel hE hF hμ in
/-- Smooth primal test sections uniquely determine the smooth transpose for a positive density. -/
theorem IsFormalTranspose.unique
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (T T' : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E))
    (hT : IsFormalTranspose μ P T) (hT' : IsFormalTranspose μ P T') : T = T' := by
  /- Fix a smooth dual input and subtract the two pairing identities. Choose
  an auxiliary smooth Hermitian metric and let w be the primal section dual to
  this difference. Its self-pairing is zero by those identities. Positivity of
  the density and metric forces w, and hence the dual difference, to vanish.
  Extensionality gives equality of the two smooth-section maps. -/
  classical
  have _sourceSmooth := hE
  have _targetSmooth := hF
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) E
  apply LinearMap.ext
  intro α
  let β := (dualSectionsEquiv E).symm (T α) - (dualSectionsEquiv E).symm (T' α)
  -- Subtract the two identities against every smooth primal test, using the same density.
  have hzero (u : smoothSections (n := n) (r := r) E) :
      smoothDualSectionPairing E μ β u = 0 := by
    change (∫ x, (T α).val x (u.val x) - (T' α).val x (u.val x) ∂μ) = 0
    have hi : Integrable (fun x ↦ (T α).val x (u.val x)) μ :=
      integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T α)) u
    have hi' : Integrable (fun x ↦ (T' α).val x (u.val x)) μ :=
      integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T' α)) u
    rw [integral_sub hi hi', hT α u, hT' α u, sub_self]
  -- A smooth metric supplies the test section dual to this difference, without changing T.
  let w := h.dualSectionsEquiv.symm β
  have hwβ : h.dualSectionsEquiv w = β := h.dualSectionsEquiv.apply_symm_apply β
  have hnorm : h.sectionPairing μ w w = 0 := by
    rw [← h.dualSectionPairing_dualSectionsEquiv μ w w, hwβ]
    exact hzero w
  have hw : w = 0 := (h.sectionPairing_self_eq_zero_iff μ w).mp hnorm
  have hβ : β = 0 := by
    rw [← hwβ, hw, map_zero]
  apply (dualSectionsEquiv E).symm.injective
  exact sub_eq_zero.mp hβ

/-- The density-weighted local transpose gives a global PDO transpose for a single local piece. -/
theorem PseudodifferentialPiece.exists_formalTranspose {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) :
    ∃ T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
        smoothSections (n := n) (r := r) (DualBundle E),
      IsFormalTranspose μ L.toLinearMap T ∧
        IsPseudodifferentialOperator (DualBundle F) (DualBundle E) μ m T := by
  /- Stage 1: choose a compact plateau β equal to one near both original cutoff
  supports, inside their common chart/frame overlap. The operator β L.operator β
  has an exact order-m symbol and a compactly supported local bilinear transpose Q.
  Stage 2: write dμ=ρ dx in that same chart. Compact matrix multipliers construct
  W=(β/ρ) Q (βρ); exact matrix-amplitude reduction proves that W still has order m.
  Only local smoothness and positivity of ρ are used, with no global growth bound.
  Stage 3: use W in the induced dual frames with the two original cutoffs swapped.
  Transport both scalar pairings by the original density. On the original cutoff
  supports β=1, so its extra factors disappear and the density factors cancel.
  The local transpose identity therefore proves the global identity for this same
  actual piece, whose exact symbol already supplies its PDO order certificate. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let H (s : ℕ) := EuclideanSpace ℂ (Fin s)
  let c := L.chart
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  -- A common plateau lies strictly inside the original chart and both original frames.
  let K := tsupport L.input.cutoff ∪ tsupport L.output.cutoff
  let U := c.target ∩ c.symm ⁻¹' (L.input.frame.baseSet ∩ L.output.frame.baseSet)
  have hK : IsCompact K := L.input.compact_support.union L.output.compact_support
  have hU : IsOpen U := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    (L.input.frame.open_baseSet.inter L.output.frame.open_baseSet)
  have hKU : K ⊆ U := by
    rintro z (hz | hz)
    · exact ⟨(L.input.support_subset hz).1, (L.input.support_subset hz).2,
        L.input_support_in_output_frame hz⟩
    · exact ⟨(L.output.support_subset hz).1, L.output_support_in_input_frame hz,
        (L.output.support_subset hz).2⟩
  have hcutoff (S O : Set V) (hS : IsCompact S) (hO : IsOpen O) (hSO : S ⊆ O) :
      ∃ β : V → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ O ∧
        S ⊆ interior {z | β z = 1} := by
    obtain ⟨W, hW, hSW, hWO, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure hS hO hSO
    obtain ⟨D, hD, hWD, hDO, hDcompact⟩ :=
      exists_open_between_and_isCompact_closure hWcompact hO hWO
    obtain ⟨β, hβ, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hD isClosed_closure hWD
    have hts : tsupport β = closure D := congrArg closure hsupp
    refine ⟨β, hβ, ?_, ?_, ?_⟩
    · change IsCompact (tsupport β)
      rwa [hts]
    · rwa [hts]
    · apply hSW.trans
      apply interior_maximal ?_ hW
      intro z hz
      exact (hone z).mp (subset_closure hz)
  obtain ⟨β, hβ, hcβ, hsβ, honeβ⟩ := hcutoff K U hK hU hKU
  have hβK (z : V) (hz : z ∈ K) : β z = 1 :=
    (interior_subset (s := {z : V | β z = 1})) (honeβ hz)
  obtain ⟨χ, hχ, hcχ, _, honeχ⟩ :=
    hcutoff (tsupport β) Set.univ hcβ isOpen_univ (Set.subset_univ _)
  -- Compactify the original Schwartz operator before transposing it.
  let p₀ := cutoffSymbol β β L.symbol
  have hp₀ : IsSymbol Set.univ m p₀ :=
    isSymbol_cutoffSymbol m L.symbol L.isSymbol β β hβ hβ hcβ hcβ
  let P₀ := amplitudeOperator m (cutoffAmplitude β β L.symbol)
    (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ)
    (hasCompactSupport_cutoffAmplitude L.symbol β β hcβ hcβ)
  have hP₀ (v : 𝓢(V, H r)) (z : V) : P₀ v z = quantize p₀ v z := by
    rw [show P₀ v z = amplitudeApply (cutoffAmplitude β β L.symbol) v z from
      amplitudeOperator_apply m _ _ _ v z]
    exact (congrFun (quantize_amplitudeSymbol m _
      (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ)
      (hasCompactSupport_cutoffAmplitude L.symbol β β hcβ hcβ) v) z).symm
  have hP₀support : HasOperatorSupport (tsupport β) P₀ := by
    simpa only [Set.union_self] using
      hasOperatorSupport_cutoff m L.symbol L.isSymbol β β hβ hβ hcβ hcβ
  have hp₀compact : HasCompactSupport p₀ :=
    hcβ.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_symbol_subset_of_hasOperatorSupport m p₀ hp₀ P₀ hP₀
        (tsupport β) (isClosed_tsupport β) hP₀support)
  let Q := localFormalTranspose m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
  let q₀ := transposeSymbol χ p₀
  have hq₀ : IsSymbol Set.univ m q₀ :=
    isSymbol_transposeSymbol m p₀ hp₀ hp₀compact χ hχ hcχ
  have hQ (v : 𝓢(V, H q)) (z : V) : Q v z = quantize q₀ v z :=
    localFormalTranspose_apply m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
      χ hχ hcχ honeχ v z
  have hQpair : IsSchwartzFormalTranspose P₀ Q :=
    isSchwartzFormalTranspose_localFormalTranspose m p₀ hp₀ P₀ hP₀
      (tsupport β) hcβ hP₀support
  -- The density and its inverse need smoothness only on this chart target.
  obtain ⟨ρ, hρ, hρpos, hρmap⟩ := hμ.exists_smooth_density c L.chart_mem_atlas
  have hβtarget : tsupport β ⊆ c.target := fun z hz ↦ (hsβ hz).1
  let A : V → H r →L[ℂ] H r :=
    cutoffMatrix β (fun z ↦ (ρ z)⁻¹ • ContinuousLinearMap.id ℂ (H r))
  let B : V → H q →L[ℂ] H q :=
    cutoffMatrix β (fun z ↦ ρ z • ContinuousLinearMap.id ℂ (H q))
  have hA : ContDiff ℝ ∞ A := contDiff_cutoffMatrix c.target c.open_target _
    ((hρ.inv (fun z hz ↦ ne_of_gt (hρpos z hz))).smul contDiffOn_const)
    β hβ hβtarget
  have hB : ContDiff ℝ ∞ B := contDiff_cutoffMatrix c.target c.open_target _
    (hρ.smul contDiffOn_const) β hβ hβtarget
  have hcA : HasCompactSupport A := hasCompactSupport_cutoffMatrix β _ hcβ
  have hcB : HasCompactSupport B := hasCompactSupport_cutoffMatrix β _ hcβ
  let W := (matrixMultiplierCLM A hA hcA).comp
    (Q.comp (matrixMultiplierCLM B hB hcB))
  let w := amplitudeSymbol (matrixAmplitude A B q₀)
  have hw : IsSymbol Set.univ m w :=
    isSymbol_amplitudeSymbol m _ (isAmplitude_matrixAmplitude m q₀ hq₀ A B hA hB)
      (hasCompactSupport_matrixAmplitude A B q₀ hcA hcB)
  have hW (v : 𝓢(V, H q)) (z : V) : W v z = quantize w v z := by
    change matrixMultiplierCLM A hA hcA (Q (matrixMultiplierCLM B hB hcB v)) z = _
    rw [matrixMultiplierCLM_apply, hQ]
    exact (quantize_matrixAmplitude m q₀ hq₀ A B hA hcA hB hcB v z).symm
  -- Induced dual frames and the swapped original cutoffs retain exactly the original witnesses.
  let I : BundleChartCutoff (r := q) (DualBundle F) c :=
    { frame := dualFrame F L.output.frame
      frame_mem_atlas := inferInstance
      cutoff := L.output.cutoff
      smooth_cutoff := L.output.smooth_cutoff
      compact_support := L.output.compact_support
      support_subset := by simpa only [dualFrame_baseSet] using L.output.support_subset }
  let O : BundleChartCutoff (r := r) (DualBundle E) c :=
    { frame := dualFrame E L.input.frame
      frame_mem_atlas := inferInstance
      cutoff := L.input.cutoff
      smooth_cutoff := L.input.smooth_cutoff
      compact_support := L.input.compact_support
      support_subset := by simpa only [dualFrame_baseSet] using L.input.support_subset }
  let LT : PseudodifferentialPiece (n := n) (r := q) (q := r)
      (DualBundle F) (DualBundle E) m :=
    { chart := c
      chart_mem_atlas := L.chart_mem_atlas
      input := I
      output := O
      input_support_in_output_frame := by
        simpa only [I, O, dualFrame_baseSet] using L.output_support_in_input_frame
      output_support_in_input_frame := by
        simpa only [I, O, dualFrame_baseSet] using L.input_support_in_output_frame
      operator := W
      symbol := w
      isSymbol := hw
      operator_apply := hW }
  -- Scalar chart transport applies to both actual bundle evaluations.
  have hchartIntegral (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (μ : Measure M)
      (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContinuousOn w c.target)
      (hpos : ∀ z ∈ c.target, 0 ≤ w z)
      (hmap : Measure.map c (μ.restrict c.source) =
        (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
      (f : M → ℂ) (hf : Continuous f) (hsupp : Function.support f ⊆ c.source) :
      (∫ x, f x ∂μ) = ∫ z in c.target, w z • f (c.symm z) := by
    classical
    -- Extend the target test by zero outside the prescribed chart target.
    let g : EuclideanSpace ℝ (Fin n) → ℂ := c.target.piecewise (fun z ↦ f (c.symm z)) (fun _ ↦ 0)
    have hg : Measurable g :=
      (hf.comp_continuousOn c.continuousOn_symm).measurable_piecewise
        continuousOn_const c.open_target.measurableSet
    have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
      ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
        |>.aemeasurable c.open_target.measurableSet
    calc
      (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ Function.notMem_support.mp (fun h ↦ hx (hsupp h)))
      _ = ∫ x in c.source, g (c x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
        simp [g, Set.piecewise_eq_of_mem, c.map_source hx, c.left_inv hx]
      _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
        (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
          hg.aestronglyMeasurable).symm
      _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
        rw [hmap]
        exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
          (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
      _ = ∫ z in c.target, w z • f (c.symm z) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        simp [g, Set.piecewise_eq_of_mem, hz, ENNReal.toReal_ofReal (hpos z hz)]
  refine ⟨LT.toLinearMap, ?_, LT.isPseudodifferentialOperator m⟩
  intro α u
  let u₀ := L.input.localize L.chart_mem_atlas u
  let a₀ := I.localize L.chart_mem_atlas α
  let b := matrixMultiplierCLM B hB hcB a₀
  have hu₀zero (z : V) (hz : z ∉ tsupport L.input.cutoff) : u₀ z = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun hz' ↦ hz (L.input.tsupport_localizedFunction_subset u hz'))
  have ha₀zero (z : V) (hz : z ∉ tsupport L.output.cutoff) : a₀ z = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun hz' ↦ hz (I.tsupport_localizedFunction_subset α hz'))
  have hβgrowth : (fun z : V ↦ (β z : ℂ)).HasTemperateGrowth :=
    (hcβ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hβ)
  have hβu : SchwartzMap.smulLeftCLM (H r) (fun z ↦ (β z : ℂ)) u₀ = u₀ := by
    ext z : 1
    rw [SchwartzMap.smulLeftCLM_apply_apply hβgrowth]
    by_cases hz : z ∈ tsupport L.input.cutoff
    · rw [hβK z (Or.inl hz), Complex.ofReal_one, one_smul]
    · rw [hu₀zero z hz, smul_zero]
  have hP₀apply (z : V) : P₀ u₀ z = β z • L.operator u₀ z := by
    rw [show P₀ u₀ z = amplitudeApply (cutoffAmplitude β β L.symbol) u₀ z from
      amplitudeOperator_apply m _ _ _ u₀ z]
    rw [amplitudeApply_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ hcβ hcβ,
      hβu, ← L.operator_apply]
  have hb (z : V) : b z = ρ z • a₀ z := by
    rw [show b z = B z (a₀ z) from matrixMultiplierCLM_apply B hB hcB a₀ z]
    change β z • (ρ z • a₀ z) = _
    by_cases hz : z ∈ tsupport L.output.cutoff
    · rw [hβK z (Or.inr hz), one_smul]
    · rw [ha₀zero z hz, smul_zero, smul_zero]
  have hWapply (z : V) : W a₀ z = β z • ((ρ z)⁻¹ • Q b z) :=
    matrixMultiplierCLM_apply A hA hcA (Q b) z
  have hsmulDot {s : ℕ} (t : ℝ) (v w : H s) :
      (∑ i, (t • v) i * w i) = t • ∑ i, v i * w i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (t • v i) * w i = t • (v i * w i)
    exact smul_mul_assoc t (v i) (w i)
  -- Both global pairings are transported using the same chart density and induced dual frames.
  have hleftChart :
      (∫ y, (O.extend L.chart_mem_atlas (W a₀)).val y (u.val y) ∂μ) =
        ∫ z, ρ z • ∑ i, W a₀ z i * u₀ z i := by
    let A : BundleChartCutoff (r := r) E c := L.input
    let D := O
    let v := W a₀
    let := A.frame_mem_atlas
    let := D.frame_mem_atlas
    have hframe : D.frame = @dualFrame r M _ E _ _ _ _ _ A.frame A.frame_mem_atlas := rfl
    have hcut : D.cutoff = A.cutoff := rfl
    have hc := L.chart_mem_atlas
    have hρ := hρ.continuousOn
    have hρpos : ∀ z ∈ c.target, 0 ≤ ρ z := fun z hz ↦ (hρpos z hz).le
    have hmap := hρmap
    have hpair (x : M) (hx : x ∈ A.frame.baseSet) (α : DualBundle E x) (w : E x) :
        α w = ∑ i, (dualFrame E A.frame ⟨x, α⟩).2 i * (A.frame ⟨x, w⟩).2 i := by
      have hexpand : ∑ i : Fin r, (A.frame ⟨x, w⟩).2 i •
          A.frame.symmL ℂ x (EuclideanSpace.single i 1) = w := by
        have heq := congrArg (A.frame.symmL ℂ x)
          ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((A.frame ⟨x, w⟩).2))
        calc
          _ = A.frame.symmL ℂ x ((A.frame ⟨x, w⟩).2) := by
            simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
          _ = w := by
            rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ hx]
            exact A.frame.symmL_continuousLinearMapAt hx w
      have hd := dualFrame_apply_snd E A.frame
        (fun y ↦ if h : y = x then h.symm ▸ α else 0) x hx
      simp only [dite_true] at hd
      rw [hd]
      conv_lhs => rw [← hexpand, map_sum]
      simp only [map_smul, smul_eq_mul, dualSectionInFrame, dite_true]
      exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
    rw [hchartIntegral c μ ρ hρ hρpos hmap (fun x ↦ (D.extend hc v).val x (u.val x))
      (by simpa only [dualSectionsEquiv] using
        (contMDiff_dualSection_eval E ⟨(D.extend hc v).val,
          (isSmoothSection_dualBundle_iff E _).1 (D.extend hc v).property⟩ u).continuous)
      (by
        intro x hx
        by_contra hxc
        apply hx
        change (D.extendedFunction v x) (u.val x) = 0
        simp [BundleChartCutoff.extendedFunction, hxc])]
    calc
      _ = ∫ z in c.target, ρ z • ∑ i, v z i * (A.localize hc u) z i := by
        apply setIntegral_congr_fun c.open_target.measurableSet
        intro z hz
        apply congrArg (fun a : ℂ ↦ ρ z • a)
        change (D.extendedFunction v (c.symm z)) (u.val (c.symm z)) =
          ∑ i, v z i * A.localizedFunction u z i
        simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
          c.map_target hz, ite_true, c.right_inv hz, hz]
        by_cases hb : z ∈ tsupport A.cutoff
        · have he := (A.support_subset hb).2
          have hd : c.symm z ∈ D.frame.baseSet := by
            rw [hframe, dualFrame_baseSet]
            exact he
          change (D.cutoff z : ℂ) * (D.frame.symmL ℂ (c.symm z) (v z))
            (u.val (c.symm z)) = _
          rw [hpair _ he, ← hframe]
          rw [← D.frame.continuousLinearMapAt_apply_of_mem ℂ hd,
            D.frame.continuousLinearMapAt_symmL hd]
          simp only [hcut, sectionInChart, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ ↦ by ring)
        · simp [hcut, image_eq_zero_of_notMem_tsupport hb]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
        intro z hz
        change ρ z • ∑ i, v z i * A.localizedFunction u z i = 0
        simp [BundleChartCutoff.localizedFunction, hz])
  have hrightChart :
      (∫ y, α.val y ((L.output.extend L.chart_mem_atlas (L.operator u₀)).val y) ∂μ) =
        ∫ z, ρ z • ∑ j, a₀ z j * L.operator u₀ z j := by
    let A : BundleChartCutoff (r := q) F c := L.output
    let D := I
    let v := L.operator u₀
    let := A.frame_mem_atlas
    let := D.frame_mem_atlas
    have hframe : D.frame = @dualFrame q M _ F _ _ _ _ _ A.frame A.frame_mem_atlas := rfl
    have hcut : D.cutoff = A.cutoff := rfl
    have hc := L.chart_mem_atlas
    have hρ := hρ.continuousOn
    have hρpos : ∀ z ∈ c.target, 0 ≤ ρ z := fun z hz ↦ (hρpos z hz).le
    have hmap := hρmap
    have hpair (x : M) (hx : x ∈ A.frame.baseSet) (α : DualBundle F x) (w : F x) :
        α w = ∑ i, (dualFrame F A.frame ⟨x, α⟩).2 i * (A.frame ⟨x, w⟩).2 i := by
      have hexpand : ∑ i : Fin q, (A.frame ⟨x, w⟩).2 i •
          A.frame.symmL ℂ x (EuclideanSpace.single i 1) = w := by
        have heq := congrArg (A.frame.symmL ℂ x)
          ((EuclideanSpace.basisFun (Fin q) ℂ).sum_repr ((A.frame ⟨x, w⟩).2))
        calc
          _ = A.frame.symmL ℂ x ((A.frame ⟨x, w⟩).2) := by
            simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
          _ = w := by
            rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ hx]
            exact A.frame.symmL_continuousLinearMapAt hx w
      have hd := dualFrame_apply_snd F A.frame
        (fun y ↦ if h : y = x then h.symm ▸ α else 0) x hx
      simp only [dite_true] at hd
      rw [hd]
      conv_lhs => rw [← hexpand, map_sum]
      simp only [map_smul, smul_eq_mul, dualSectionInFrame, dite_true]
      exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
    rw [hchartIntegral c μ ρ hρ hρpos hmap (fun x ↦ α.val x ((A.extend hc v).val x))
      (by simpa only [dualSectionsEquiv] using
        (contMDiff_dualSection_eval F ⟨α.val, (isSmoothSection_dualBundle_iff F α.val).1 α.property⟩
          (A.extend hc v)).continuous)
      (by
        intro x hx
        by_contra hxc
        apply hx
        change α.val x (A.extendedFunction v x) = 0
        simp [BundleChartCutoff.extendedFunction, hxc])]
    calc
      _ = ∫ z in c.target, ρ z • ∑ i, (D.localize hc α) z i * v z i := by
        apply setIntegral_congr_fun c.open_target.measurableSet
        intro z hz
        apply congrArg (fun a : ℂ ↦ ρ z • a)
        change α.val (c.symm z) (A.extendedFunction v (c.symm z)) =
          ∑ i, D.localizedFunction α z i * v z i
        simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
          c.map_target hz, ite_true, c.right_inv hz, hz]
        by_cases hb : z ∈ tsupport A.cutoff
        · have he := (A.support_subset hb).2
          rw [map_smul, smul_eq_mul, hpair _ he]
          simp only [hframe, hcut, sectionInChart, PiLp.smul_apply, smul_eq_mul]
          rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
            A.frame.continuousLinearMapAt_symmL he]
          simp only [Finset.mul_sum, mul_assoc]
        · simp [hcut, image_eq_zero_of_notMem_tsupport hb]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
        intro z hz
        change ρ z • ∑ i, D.localizedFunction α z i * v z i = 0
        simp [BundleChartCutoff.localizedFunction, hz])
  have hleft (z : V) : (ρ z • ∑ i, W a₀ z i * u₀ z i) =
      ∑ i, Q b z i * u₀ z i := by
    by_cases hz : z ∈ tsupport L.input.cutoff
    · rw [hWapply, hβK z (Or.inl hz), one_smul, hsmulDot,
        smul_smul, mul_inv_cancel₀ (ne_of_gt (hρpos z (L.input.support_subset hz).1)),
        one_smul]
    · simp [hu₀zero z hz]
  have hright (z : V) : (∑ j, b z j * P₀ u₀ z j) =
      ρ z • ∑ j, a₀ z j * L.operator u₀ z j := by
    rw [hb, hP₀apply]
    by_cases hz : z ∈ tsupport L.output.cutoff
    · rw [hβK z (Or.inr hz), one_smul, hsmulDot]
    · simp [ha₀zero z hz]
  change (∫ y, (O.extend L.chart_mem_atlas (W a₀)).val y (u.val y) ∂μ) =
    ∫ y, α.val y ((L.output.extend L.chart_mem_atlas (L.operator u₀)).val y) ∂μ
  rw [hleftChart, hrightChart]
  simp_rw [hleft]
  exact (hQpair u₀ b).trans (integral_congr_ae (Filter.Eventually.of_forall hright))

/-- Transposing a finite representation gives a PDO of the same order on the actual dual bundles. -/
theorem IsPseudodifferentialOperator.exists_formalTranspose {m : ℝ}
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hP : IsPseudodifferentialOperator E F μ m P) :
    ∃ T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
        smoothSections (n := n) (r := r) (DualBundle E),
      IsFormalTranspose μ P T ∧
        IsPseudodifferentialOperator (DualBundle F) (DualBundle E) μ m T := by
  /- Extract P's actual finite local representation and smooth kernel remainder.
  Transpose each piece by the preceding local result and the remainder by the
  swapped dual kernel. Add the maps. Integral additivity gives the transpose
  identity, while finite PDO addition and the inclusion of smooth kernels in
  every real order give order m. No global transpose is assumed in this argument. -/
  classical
  obtain ⟨N, L, K, hK⟩ := hP
  choose T hT horder using fun j : Fin N ↦ (L j).exists_formalTranspose (μ := μ)
  -- Addition preserves the actual same-density identity because smooth evaluations are integrable.
  have hadd
      (P₁ P₂ : smoothSections (n := n) (r := r) E →ₗ[ℂ]
        smoothSections (n := n) (r := q) F)
      (T₁ T₂ : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
        smoothSections (n := n) (r := r) (DualBundle E))
      (h₁ : IsFormalTranspose μ P₁ T₁) (h₂ : IsFormalTranspose μ P₂ T₂) :
      IsFormalTranspose μ (P₁ + P₂) (T₁ + T₂) := by
    intro α u
    have hT₁ : Integrable (fun x ↦ (T₁ α).val x (u.val x)) μ :=
      integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T₁ α)) u
    have hT₂ : Integrable (fun x ↦ (T₂ α).val x (u.val x)) μ :=
      integrable_dualSection_eval E μ ((dualSectionsEquiv E).symm (T₂ α)) u
    have hP₁ : Integrable (fun x ↦ α.val x ((P₁ u).val x)) μ :=
      integrable_dualSection_eval F μ ((dualSectionsEquiv F).symm α) (P₁ u)
    have hP₂ : Integrable (fun x ↦ α.val x ((P₂ u).val x)) μ :=
      integrable_dualSection_eval F μ ((dualSectionsEquiv F).symm α) (P₂ u)
    change (∫ x, ((T₁ α).val x + (T₂ α).val x) (u.val x) ∂μ) =
      ∫ x, α.val x ((P₁ u).val x + (P₂ u).val x) ∂μ
    simp only [add_apply, map_add]
    rw [integral_add hT₁ hT₂, integral_add hP₁ hP₂, h₁ α u, h₂ α u]
  -- The same finite family carries both its order certificate and its transpose identity.
  have hsum (s : Finset (Fin N)) :
      IsFormalTranspose μ ((∑ j ∈ s, (L j).toLinearMap) + K.toLinearMap μ)
        ((∑ j ∈ s, T j) + K.transpose.toLinearMap μ) ∧
      IsPseudodifferentialOperator (DualBundle F) (DualBundle E) μ m
        ((∑ j ∈ s, T j) + K.transpose.toLinearMap μ) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty, zero_add] using
        And.intro K.isFormalTranspose_toLinearMap
          (IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨K.transpose, rfl⟩)
    | @insert j s hj ih =>
      simpa only [Finset.sum_insert hj, add_assoc] using
        And.intro (hadd _ _ _ _ (hT j) ih.1)
          (IsPseudodifferentialOperator.add m _ _ (horder j) ih.2)
  have hrepr : P = (∑ j, (L j).toLinearMap) + K.toLinearMap μ := by
    rw [hK]
    abel
  refine ⟨(∑ j, T j) + K.transpose.toLinearMap μ, ?_, (hsum Finset.univ).2⟩
  rw [hrepr]
  exact (hsum Finset.univ).1

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- The formal transpose is uniquely specified among all smooth-section linear maps. -/
theorem existsUnique_formalTranspose :
    ∃! T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
        smoothSections (n := n) (r := r) (DualBundle E),
      IsFormalTranspose μ P.toLinearMap T := by
  /- Existence is the map constructed from P's finite PDO representation.
  Uniqueness uses IsFormalTranspose.unique among all section maps, not only among
  the ones having a selected local representation. Thus the pairing specification
  is nonempty and identifies one actual map independently of the representation. -/
  obtain ⟨T, hT, _⟩ := P.isPseudodifferentialOperator.exists_formalTranspose P.toLinearMap
  refine ⟨T, hT, ?_⟩
  intro T' hT'
  exact IsFormalTranspose.unique P.toLinearMap T' T hT' hT

/-- The actual dual-section map selected by its unique bilinear transpose identity. -/
def formalTransposeLinearMap :
    smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E) :=
  P.existsUnique_formalTranspose.exists.choose

/-- The selected map satisfies the same-density bilinear pairing identity. -/
theorem isFormalTranspose_formalTransposeLinearMap :
    IsFormalTranspose μ P.toLinearMap P.formalTransposeLinearMap := by
  /- Apply the specifying property of the unique map chosen above. This is an
  identity of actual integrals on smooth vector and covector sections, using
  ordinary complex-linear evaluation; a Hermitian metric is not part of the data. -/
  exact P.existsUnique_formalTranspose.exists.choose_spec

/-- SG 3.17(iv): the specified transpose belongs to the original real PDO order. -/
theorem isPseudodifferentialOperator_formalTranspose :
    IsPseudodifferentialOperator (DualBundle F) (DualBundle E) μ m
      P.formalTransposeLinearMap := by
  /- The finite representation construction supplies a map T with both the
  transpose identity and order m. The identity just established and uniqueness
  identify the selected formalTransposeLinearMap with that same T. Transfer its
  order property, without adding PDO closure as a field of the transpose definition. -/
  obtain ⟨T, hT, horder⟩ := P.isPseudodifferentialOperator.exists_formalTranspose P.toLinearMap
  have heq : P.formalTransposeLinearMap = T :=
    IsFormalTranspose.unique P.toLinearMap P.formalTransposeLinearMap T
      P.isFormalTranspose_formalTransposeLinearMap hT
  exact heq.symm ▸ horder

/-- The actual transpose map packaged with the derived same-order PDO property. -/
def formalTranspose :
    PseudodifferentialOperator (n := n) (r := q) (q := r)
      (DualBundle F) (DualBundle E) μ m where
  toLinearMap := P.formalTransposeLinearMap
  isPseudodifferentialOperator := P.isPseudodifferentialOperator_formalTranspose

/-- The transpose of a smooth-kernel PDO is its actual swapped dual-kernel operator. -/
theorem formalTranspose_eq_kernelTranspose
    (K : SmoothKernel (n := n) (r := r) (q := q) E F)
    (hP : P.toLinearMap = K.toLinearMap μ) :
    P.formalTranspose.toLinearMap = K.transpose.toLinearMap μ := by
  /- The swapped kernel satisfies the formal transpose identity of K's map.
  Substitute hP and use uniqueness with P's transpose identity. This retains
  the exact kernel integral, rather than merely its principal symbol or order. -/
  apply IsFormalTranspose.unique P.toLinearMap P.formalTranspose.toLinearMap
    (K.transpose.toLinearMap μ) P.isFormalTranspose_formalTransposeLinearMap
  rw [hP]
  exact K.isFormalTranspose_toLinearMap

/-- Formal transposition preserves actual smooth-kernel operators. -/
theorem isSmoothingOperator_formalTranspose
    (hP : IsSmoothingOperator μ P.toLinearMap) :
    IsSmoothingOperator μ P.formalTranspose.toLinearMap := by
  /- Extract a smooth kernel K representing P. The preceding equality represents
  its transpose by K.transpose for the same density. This is the actual kernel
  characterization of smoothing, with no converse PDO order comparison required. -/
  obtain ⟨K, hK⟩ := hP
  exact ⟨K.transpose, (P.formalTranspose_eq_kernelTranspose K hK.symm).symm⟩

variable (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- Actual precomposition on continuous duals, transported to opposite-order Sobolev spaces. -/
def sobolevTranspose (s : ℝ) :
    B.DualSobolevSpace (-(s - m)) →L[ℂ] A.DualSobolevSpace (-s) :=
  (A.sobolevEvaluationDuality μ s).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL ℂ (A.SobolevSpace s) (B.SobolevSpace (s - m)) ℂ).flip
      (P.sobolevExtension A B s)).comp
        (B.sobolevEvaluationDuality μ (s - m)).toContinuousLinearMap)

/-- Geometric duality identifies the Sobolev transpose with precomposition by the original PDO. -/
theorem sobolevEvaluationDuality_transpose (s : ℝ)
    (α : B.DualSobolevSpace (-(s - m))) :
    A.sobolevEvaluationDuality μ s (P.sobolevTranspose A B s α) =
      (B.sobolevEvaluationDuality μ (s - m) α).comp (P.sobolevExtension A B s) := by
  /- Expand the composite defining sobolevTranspose and cancel the duality map
  with its inverse. The middle flipped composition map sends a functional to
  its actual precomposition with the order-m Sobolev extension of P. -/
  -- The two geometric duality equivalences cancel on this same precomposed functional.
  exact (A.sobolevEvaluationDuality μ s).apply_symm_apply _

/-- On smooth covectors the continuous transpose is the specified geometric transpose. -/
theorem sobolevTranspose_smooth (s : ℝ)
    (α : smoothDualSections (n := n) (r := q) F) :
    P.sobolevTranspose A B s (B.dualSmoothToSobolev (-(s - m)) α) =
      A.dualSmoothToSobolev (-s)
        ((dualSectionsEquiv E).symm (P.formalTranspose.toLinearMap (dualSectionsEquiv F α))) := by
  /- Test both sides by geometric duality on an arbitrary smooth primal section.
  The preceding precomposition formula and the PDO extension specification give
  the integral pairing with Pu. The formal transpose identity gives the same
  value on the right. Density of primal smooth sections identifies the continuous
  functionals, and injectivity of duality identifies the actual Sobolev elements. -/
  -- Test the two covectors using the original perfect evaluation pairing.
  apply (A.sobolevEvaluationDuality μ s).injective
  rw [P.sobolevEvaluationDuality_transpose]
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    (((B.sobolevEvaluationDuality μ (s - m))
      (B.dualSmoothToSobolev (-(s - m)) α)).comp
        (P.sobolevExtension A B s)).continuous
    ((A.sobolevEvaluationDuality μ s) _).continuous
  funext u
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.comp_apply, P.sobolevExtension_smoothToSobolev]
  change B.sobolevEvaluationPairing μ (s - m) _ _ =
    A.sobolevEvaluationPairing μ s _ _
  rw [B.sobolevEvaluationPairing_smooth, A.sobolevEvaluationPairing_smooth]
  -- The formal transpose uses the same smooth sections and same-point integral.
  exact (P.isFormalTranspose_formalTransposeLinearMap (dualSectionsEquiv F α) u).symm

/-- The common dual-bundle extension agrees with the independently constructed Sobolev transpose. -/
theorem dualSobolevEquiv_transpose (s : ℝ)
    (α : B.DualSobolevSpace (-(s - m))) :
    A.dualSobolevEquiv (-s) (P.sobolevTranspose A B s α) =
      A.dualPresentation.sobolevInclusion (-(s - m) - m) (-s)
        (by
          have h : -(s - m) - m = -s := by ring
          rw [h])
        (P.formalTranspose.sobolevExtension B.dualPresentation A.dualPresentation (-(s - m))
          (B.dualSobolevEquiv (-(s - m)) α)) := by
  /- Stage 1: the smooth-input formulas for both maps give the same actual
  transpose section. The model isometry is the identity on its Bessel coordinates;
  the natural inclusion changes only the equal target orders -(s-m)-m and -s.
  Stage 2: smooth covectors are dense and both sides are continuous. Extend their
  equality to every input, without identifying arbitrary Sobolev norms isometrically. -/
  -- Both continuous maps agree on the dense image of the actual smooth covectors.
  have heq := (B.denseRange_dualSmoothToSobolev (-(s - m))).equalizer
    ((A.dualSobolevEquiv (-s)).continuous.comp
      (P.sobolevTranspose A B s).continuous)
    ((A.dualPresentation.sobolevInclusion (-(s - m) - m) (-s)
      (by linarith)).continuous.comp
        ((P.formalTranspose.sobolevExtension B.dualPresentation
          A.dualPresentation (-(s - m))).continuous.comp
            (B.dualSobolevEquiv (-(s - m))).continuous)) (by
      funext β
      simp only [Function.comp_apply]
      -- The equal-order inclusion changes no smooth section or bundle identification.
      rw [P.sobolevTranspose_smooth, A.dualSobolevEquiv_smooth,
        B.dualSobolevEquiv_smooth, P.formalTranspose.sobolevExtension_smoothToSobolev,
        A.dualPresentation.sobolevInclusion_smoothToSobolev]
      simp only [LinearEquiv.apply_symm_apply])
  exact congrFun heq α

end PseudodifferentialOperator

/-- On a differential map the PDO transpose agrees with the existing differential transpose. -/
theorem DifferentialOperator.formalTranspose_eq_of_toLinearMap_eq {k : ℕ}
    (D : DifferentialOperator (n := n) (r := r) (q := q) E F k)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (k : ℝ))
    (h : P.toLinearMap = D.toLinearMap) :
    P.formalTranspose.toLinearMap = (D.formalTransposeOperator μ).toLinearMap := by
  /- The differential transpose's bilinear pairing formula transports through
  dualSectionsEquiv, which preserves every covector value. Thus it satisfies
  IsFormalTranspose for D and, by h, for P. Apply the full smooth-map uniqueness
  theorem. No comparison of principal symbols or elliptic regularity is used. -/
  apply IsFormalTranspose.unique P.toLinearMap P.formalTranspose.toLinearMap
    (D.formalTransposeOperator μ).toLinearMap P.isFormalTranspose_formalTransposeLinearMap
  intro α u
  rw [h]
  exact D.smoothDualSectionPairing_formalTranspose μ ((dualSectionsEquiv F).symm α) u

end AtiyahSinger
