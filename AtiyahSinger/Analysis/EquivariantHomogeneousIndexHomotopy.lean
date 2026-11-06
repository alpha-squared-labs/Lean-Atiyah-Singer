/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantMetricL2Average
public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbol
public import AtiyahSinger.Analysis.EquivariantOperatorAverage
public import AtiyahSinger.Analysis.GeometricEquivariantIndex
public import AtiyahSinger.Analysis.HomogeneousSymbolFamilies

/-!
# Equivariant index invariance along smooth-topology homogeneous-symbol paths

Public module ID: M0522.

An elliptic path in the original punctured C-infinity homogeneous-symbol
topology preserves the full representation-valued index of its actual
equivariant elliptic endpoint operators. The original smooth bundles,
actions, invariant metrics and positive invariant density stay fixed. The
endpoint operators need only have the specified principal classes; their
lower-order and smoothing terms can differ from a fixed quantization.

Sources: SG III.7 Theorem 7.10 and Remark 7.11, p.204, for continuous symbol
realization; SG III.9 Theorem 9.7, p.214, for representation-valued homotopy
invariance through averaging. The order-zero PDO formulation with the exact
punctured C-infinity topology is a project specialization and supplement.
The averaging comparison uses uniform lower-order estimates for conjugated symbols.

Operator averaging is a norm contraction on the original invariant-metric
L2 realizations. Its proof uses vector-valued strong integrals, without an
operator-norm-continuous group action or a Bochner integral in the operator
space. A continuous cosphere or compact-support K homotopy does not by itself
provide a path in the required smooth homogeneous-symbol topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

attribute [local instance] homogeneousSymbolTopology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [hGM : MeasurableSpace G] [hGB : BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

include hM hT2 hSC hC hBorel hE hF hμ hG hGC hGT hGM hGB hAction
  hInvariant kInvariant hμInvariant

set_option maxHeartbeats 1500000 in
-- One actual quantized path, its strong averages, and the original endpoint classes are compared.
/-- Equivariant elliptic homogeneous paths preserve the original full equivariant indices. -/
theorem equivariantAnalyticIndex_eq_of_continuous_homogeneous_principalSymbol
    (P Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
    (hQg : Q.IsEquivariant IG σE σF hσE hσF) (hQ : Q.IsElliptic)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : unitInterval → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (ha : Continuous a) (he : ∀ t, IsEllipticGlobalSymbol E F (a t).val)
    (hag : ∀ (t : unitInterval) (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      ξ ≠ 0 → equivariantGlobalSymbolLinearMap IG σE σF g (a t).val x ξ = (a t).val x ξ)
    (hPSymbol : P.principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 (a 0).val (a 0).property.1 (a 0).property.2))
    (hQSymbol : Q.principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 (a 1).val (a 1).property.1 (a 1).property.2)) :
    P.equivariantAnalyticIndex IG σE σF hσE hσF
        h k hInvariant kInvariant hμInvariant hPg hP =
      Q.equivariantAnalyticIndex IG σE σF hσE hσF
        h k hInvariant kInvariant hμInvariant hQg hQ := by
  classical
  obtain ⟨C⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q) (E := E) (F := F)
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  let L (t : unitInterval) := C.quantizeHomogeneous R μ 0 (a t).val
    (a t).property.1 (a t).property.2
  let Lbar (t : unitInterval) := (L t).average IG σE σF hσE hσF
  have hclass (t : unitInterval) : (L t).principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 (a t).val (a t).property.1 (a t).property.2) :=
    C.principalSymbol_quantizeHomogeneous R μ 0 (a t).val (a t).property.1 (a t).property.2
  -- Off-zero equivariance fixes the same original principal class before averaging.
  have hfixed (t : unitInterval) (g : G) :
      equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF 0 g (L t).principalSymbol =
        (L t).principalSymbol := by
    rw [hclass]
    exact (R.equivariant_regularizedSymbol_class_eq_iff IG σE σF hσE hσF R 0
      (a t) (a t) g).mpr (hag t g)
  have hbarclass (t : unitInterval) : (Lbar t).principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 (a t).val (a t).property.1 (a t).property.2) :=
    ((L t).principalSymbol_average_of_fixed IG σE σF hσE hσF (hfixed t)).trans (hclass t)
  have hbarEq (t : unitInterval) : (Lbar t).IsEquivariant IG σE σF hσE hσF :=
    (L t).isEquivariant_average IG σE σF hσE hσF
  have hbarEll (t : unitInterval) : (Lbar t).IsElliptic :=
    ⟨R.regularizedSymbol 0 (a t).val (a t).property.1 (a t).property.2, hbarclass t,
      (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 (a t).val
        (a t).property.1 (a t).property.2).mpr (he t)⟩
  -- The fixed Sobolev-zero comparisons identify the norm-continuous quantizations on metric L².
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  have hfExists : ∃ f : B.SobolevSpace (0 - 0) ≃L[ℂ] k.L2SectionSpace μ,
      ∀ v : smoothSections (n := n) (r := q) F,
        f (B.smoothToSobolev (0 - 0) v) = k.smoothToL2 μ v := by
    rw [sub_self]
    exact ⟨k.sobolevZeroEquivL2 (μ := μ) B, k.sobolevZeroEquivL2_smooth B⟩
  obtain ⟨f, hf⟩ := hfExists
  have hconj (T : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0) :
      T.metricL2Extension h k = f.toContinuousLinearMap.comp
        ((T.sobolevExtension A B 0).comp e.symm.toContinuousLinearMap) := by
    have hcomm : (T.metricL2Extension h k).comp e.toContinuousLinearMap =
        f.toContinuousLinearMap.comp (T.sobolevExtension A B 0) := by
      apply DFunLike.coe_injective
      apply (A.denseRange_smoothToSobolev 0).equalizer
        ((T.metricL2Extension h k).comp e.toContinuousLinearMap).continuous
        (f.toContinuousLinearMap.comp (T.sobolevExtension A B 0)).continuous
      funext v
      change T.metricL2Extension h k (e (A.smoothToSobolev 0 v)) =
        f (T.sobolevExtension A B 0 (A.smoothToSobolev 0 v))
      rw [T.sobolevExtension_smoothToSobolev, h.sobolevZeroEquivL2_smooth,
        T.metricL2Extension_smooth, hf]
    ext u
    exact (congrArg (T.metricL2Extension h k) (e.apply_symm_apply u)).symm.trans
      (DFunLike.congr_fun hcomm (e.symm u))
  have hquant : Continuous (fun t ↦ (L t).metricL2Extension h k) := by
    simp_rw [hconj]
    exact continuous_const.clm_comp
      ((R.continuous_sobolevQuantizeHomogeneous 0 μ C A B a ha 0).clm_comp continuous_const)
  -- Strong averaging is one bounded linear map of operators, hence preserves norm continuity.
  let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  let ρI := h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant
  let τI := k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant
  let W := unitaryOperatorAverage ν ρI τI
    (h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant)
    (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
  have hbarCont : Continuous (fun t ↦ (Lbar t).metricL2Extension h k) := by
    apply (W.continuous.comp hquant).congr
    intro t
    exact ((L t).metricL2Extension_average IG σE σF hσE hσF
      h k hInvariant kInvariant hμInvariant).symm
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  have hρ := h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  have hτ := k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  have hinter (t : unitInterval) (g : G) :
      ((Lbar t).metricL2Extension h k).comp (ρ g) =
        (τ g).comp ((Lbar t).metricL2Extension h k) :=
    ((Lbar t).isEquivariant_iff_metricL2Extension_intertwines IG σE σF hσE hσF
      h k hInvariant kInvariant hμInvariant).mp (hbarEq t) g
  have hFred (t : unitInterval) := (Lbar t).isFredholm_metricL2Extension h k (hbarEll t)
  let γ : Path ((Lbar 0).metricL2Extension h k) ((Lbar 1).metricL2Extension h k) := {
    toFun := fun t ↦ (Lbar t).metricL2Extension h k
    continuous_toFun := hbarCont
    source' := rfl
    target' := rfl }
  have hmiddle :
      (Lbar 0).equivariantAnalyticIndex IG σE σF hσE hσF
          h k hInvariant kInvariant hμInvariant (hbarEq 0) (hbarEll 0) =
        (Lbar 1).equivariantAnalyticIndex IG σE σF hσE hσF
          h k hInvariant kInvariant hμInvariant (hbarEq 1) (hbarEll 1) := by
    exact equivariantFredholmIndex_eq_of_path ρ τ hρ hτ
      (fun g ↦ (ρI g).isometry) (fun g ↦ (τI g).isometry)
      γ hinter hFred (hinter 0) (hinter 1) (hFred 0) (hFred 1)
  -- Original endpoint operators are compared to these exact averaged endpoint symbols.
  have hleft := P.equivariantAnalyticIndex_eq_of_principalSymbol_eq IG σE σF hσE hσF
    h k hInvariant kInvariant hμInvariant hPg hP (Lbar 0) (hbarEq 0) (hbarEll 0)
    (hPSymbol.trans (hbarclass 0).symm)
  have hright := Q.equivariantAnalyticIndex_eq_of_principalSymbol_eq IG σE σF hσE hσF
    h k hInvariant kInvariant hμInvariant hQg hQ (Lbar 1) (hbarEq 1) (hbarEll 1)
    (hQSymbol.trans (hbarclass 1).symm)
  exact hleft.trans (hmiddle.trans hright.symm)

end AtiyahSinger.PseudodifferentialOperator
