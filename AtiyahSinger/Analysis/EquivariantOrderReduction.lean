/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantQuantization
public import AtiyahSinger.Analysis.SelfAdjointEllipticCorrection

/-!
# Equivariant invertible representatives of real elliptic principal classes

Public module ID: M0550.

An invariant self-adjoint elliptic principal class has an actual equivariant
invertible representative on the original smooth sections. Equivariant
quantization and metric symmetrization retain the specified class. The
orthogonal projection onto the same smooth kernel commutes with the original
unitary action, so the usual finite-rank Fredholm correction remains equivariant.
Its actual Sobolev extensions are bijective at every order.

This is the equivariant form of the order-reduction existence argument in
SG III.13, p.247, with the invariant metric framework of III.9. It is a
standard supplement to the source and does not identify a prescribed
fractional spectral power. In particular, the scalar real principal classes
used for order shifts need no unproved functional-calculus premise.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σ.linearMap g x u) (σ.linearMap g x v) = h.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

set_option maxHeartbeats 2000000 in
-- Retain the original metric smooth space and all Sobolev realizations of one correction.
include hInvariant hμInvariant in
/-- An invariant self-adjoint elliptic class has an equivariant invertible representative. -/
theorem exists_equivariant_bijective_of_selfAdjoint_principalSymbol {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ m)
    (hP : P.IsElliptic)
    (hfixed : ∀ g : G,
      equivariantPrincipalSymbolRepresentation IG σ σ hσ hσ m g P.principalSymbol =
        P.principalSymbol)
    (hself : h.principalSymbolAdjoint h P.principalSymbol = P.principalSymbol) :
    ∃ J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ m,
      J.principalSymbol = P.principalSymbol ∧ J.IsEquivariant IG σ σ hσ hσ ∧
      J.IsElliptic ∧ Function.Bijective J.toLinearMap ∧
      ∀ (S : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ),
        Function.Bijective (J.sobolevExtension S S s) := by
  classical
  -- Average an actual realization, then symmetrize in the specified invariant metric.
  obtain ⟨Q, hQg, hQclass⟩ :=
    exists_equivariant_principalSymbol (μ := μ) IG σ σ hσ hσ m P.principalSymbol hfixed
  have hQadj := Q.isEquivariant_metricFormalAdjoint IG σ σ hσ hσ
    h h hInvariant hInvariant hμInvariant hQg
  have hQadjclass : (Q.metricFormalAdjoint h h).principalSymbol = P.principalSymbol := by
    rw [Q.principalSymbol_metricFormalAdjoint, hQclass, hself]
  let A := (Q.add (Q.metricFormalAdjoint h h)).smul (1 / 2)
  have hAclass : A.principalSymbol = P.principalSymbol := by
    rw [principalSymbol_smul, principalSymbol_add, hQclass, hQadjclass,
      ← two_smul ℂ _, smul_smul]
    norm_num
  have hA : A.IsElliptic :=
    (P.isElliptic_iff_of_principalSymbol_eq_operator A hAclass.symm).mp hP
  have hAself : IsMetricFormalAdjoint h h μ A.toLinearMap A.toLinearMap := by
    have hpair := Q.isMetricFormalAdjoint_metricFormalAdjoint h h
    have hsum : IsMetricFormalAdjoint h h μ
        (Q.toLinearMap + (Q.metricFormalAdjoint h h).toLinearMap)
        (Q.toLinearMap + (Q.metricFormalAdjoint h h).toLinearMap) := by
      convert hpair.add hpair.symm using 1
      exact add_comm _ _
    change IsMetricFormalAdjoint h h μ
      ((1 / 2 : ℂ) • (Q.toLinearMap + (Q.metricFormalAdjoint h h).toLinearMap))
      ((1 / 2 : ℂ) • (Q.toLinearMap + (Q.metricFormalAdjoint h h).toLinearMap))
    simpa only [map_div₀, map_one, map_ofNat] using hsum.smul (1 / 2 : ℂ)
  let R := σ.smoothSectionRepresentation IG hσ
  have hAg (g : G) (u : smoothSections (n := n) (r := r) E) :
      A.toLinearMap (R g u) = R g (A.toLinearMap u) := by
    change (1 / 2 : ℂ) •
      (Q.toLinearMap (R g u) + (Q.metricFormalAdjoint h h).toLinearMap (R g u)) =
        R g ((1 / 2 : ℂ) •
          (Q.toLinearMap u + (Q.metricFormalAdjoint h h).toLinearMap u))
    have hQ := LinearMap.congr_fun (hQg g) u
    have hQ' := LinearMap.congr_fun (hQadj g) u
    change Q.toLinearMap (R g u) = R g (Q.toLinearMap u) at hQ
    change (Q.metricFormalAdjoint h h).toLinearMap (R g u) =
      R g ((Q.metricFormalAdjoint h h).toLinearMap u) at hQ'
    rw [map_smul, map_add, hQ, hQ']
  -- The original smooth kernel is invariant, and its orthogonal projection is equivariant.
  obtain ⟨S₀⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) (E := E)
  obtain ⟨B, hB⟩ := A.exists_parametrix_of_isElliptic hA
  let W : Submodule ℂ (h.SmoothL2Section μ) := A.toLinearMap.ker
  let : FiniteDimensional ℂ W := A.finiteDimensional_ker_of_isParametrix S₀ S₀ B hB
  let K := smoothOrthogonalProjection μ h W
  have hW (g : G) (u : smoothSections (n := n) (r := r) E) (hu : u ∈ W) :
      R g u ∈ W := by
    change A.toLinearMap (R g u) = 0
    rw [hAg, show A.toLinearMap u = 0 from hu, map_zero]
  have hcancel (g : G) (u : smoothSections (n := n) (r := r) E) :
      R g (R g⁻¹ u) = u := by
    change (R g * R g⁻¹) u = u
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hpair (g : G) (u v : smoothSections (n := n) (r := r) E) :
      h.sectionPairing μ (R g u) (R g v) = h.sectionPairing μ u v := by
    rw [← h.inner_smoothToL2, ← h.inner_smoothToL2,
      ← h.l2IsometryRepresentation_smoothToL2 μ IG σ hσ hInvariant hμInvariant,
      ← h.l2IsometryRepresentation_smoothToL2 μ IG σ hσ hInvariant hμInvariant]
    exact (h.l2IsometryRepresentation μ IG σ hσ hInvariant hμInvariant g).inner_map_map _ _
  have hKg (g : G) (u : smoothSections (n := n) (r := r) E) :
      K (R g u) = R g (K u) := by
    apply W.eq_starProjection_of_mem_of_inner_eq_zero
      (hW g (K u) (W.starProjection_apply_mem u))
    intro v hv
    change smoothSections (n := n) (r := r) E at v
    change h.sectionPairing μ (R g u - R g (K u)) v = 0
    calc
      _ = h.sectionPairing μ (R g (u - K u)) (R g (R g⁻¹ v)) := by
        rw [map_sub, hcancel]
      _ = h.sectionPairing μ (u - K u) (R g⁻¹ v) := hpair g _ _
      _ = 0 := W.starProjection_inner_eq_zero u _ (hW g⁻¹ v hv)
  -- Add precisely that finite-rank projection, preserving the original principal class.
  have hK := isSmoothingOperator_smoothOrthogonalProjection μ h W
  let KP : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ m :=
    ⟨K, hK.isPseudodifferentialOperator m K⟩
  let J := A.add KP
  have hKclass : KP.principalSymbol = 0 :=
    KP.principalSymbol_eq_zero_iff.mpr (hK.isPseudodifferentialOperator (m - 1) K)
  have hclass : J.principalSymbol = P.principalSymbol := by
    rw [principalSymbol_add, hKclass, add_zero, hAclass]
  have hJ : J.IsElliptic :=
    (P.isElliptic_iff_of_principalSymbol_eq_operator J hclass.symm).mp hP
  have hJg : J.IsEquivariant IG σ σ hσ hσ := by
    intro g
    apply LinearMap.ext
    intro u
    change A.toLinearMap (R g u) + K (R g u) = R g (A.toLinearMap u + K u)
    rw [hAg, hKg, map_add]
  have hKself : IsMetricFormalAdjoint h h μ K K := by
    intro u v
    exact W.inner_starProjection_left_eq_right u v
  have hJself : IsMetricFormalAdjoint h h μ J.toLinearMap J.toLinearMap := hAself.add hKself
  have hJadj : J.metricFormalAdjoint h h = J := J.metricFormalAdjoint_eq h h J hJself
  -- Symmetry separates a corrected zero into its kernel and perpendicular components.
  have hinj : Function.Injective J.toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    have heq : A.toLinearMap u + K u = 0 := hu
    have hKu : A.toLinearMap (K u) = 0 := W.starProjection_apply_mem u
    have horth : h.sectionPairing μ (K u) (A.toLinearMap u) = 0 := by
      rw [← hAself, hKu]
      exact inner_zero_left (𝕜 := ℂ) (E := h.SmoothL2Section μ) u
    have hKzero : K u = 0 := by
      apply (h.sectionPairing_self_eq_zero_iff μ _).mp
      have hneg : A.toLinearMap u = -K u := eq_neg_of_add_eq_zero_left heq
      rw [hneg] at horth
      have hn : h.sectionPairing μ (K u) (-K u) = -h.sectionPairing μ (K u) (K u) :=
        inner_neg_right (𝕜 := ℂ) (E := h.SmoothL2Section μ) (K u) (K u)
      rw [hn] at horth
      exact neg_eq_zero.mp horth
    have hAu : A.toLinearMap u = 0 := by simpa only [hKzero, add_zero] using heq
    have hfix : K u = u := W.starProjection_eq_self_iff.mpr hAu
    exact hfix.symm.trans hKzero
  -- The actual smooth Fredholm alternative gives surjectivity for this same J.
  obtain ⟨C, hC⟩ := J.exists_parametrix_of_isElliptic hJ
  have hsurj : Function.Surjective J.toLinearMap := by
    intro v
    apply (J.mem_range_iff_pairing_metricFormalAdjoint_eq_zero h h S₀ S₀ C hC v).mpr
    intro w
    have hw : J.toLinearMap w.val = 0 := by
      exact (congrArg (fun L : PseudodifferentialOperator (n := n) (r := r) (q := r)
        E E μ m ↦ L.toLinearMap w.val) hJadj).symm.trans w.property
    have hwzero : w.val = 0 := hinj (by simpa using hw)
    rw [hwzero]
    exact inner_zero_left (𝕜 := ℂ) (E := h.SmoothL2Section μ) v
  refine ⟨J, hclass, hJg, hJ, ⟨hinj, hsurj⟩, ?_⟩
  intro S s
  -- Regularity identifies each original Sobolev kernel and quotient with the smooth ones.
  let T := J.sobolevExtension S S s
  have hTfred := J.isFredholm_sobolevExtension_of_isParametrix C S S hC s
  have hfinite := (isFredholm_iff_closed_range_finite T).mp hTfred
  let : FiniteDimensional ℂ T.ker := hfinite.2.1
  let : FiniteDimensional ℂ (S.SobolevSpace (s - m) ⧸ T.range) := hfinite.2.2
  have hker : Module.finrank ℂ T.ker = 0 := by
    rw [J.finrank_ker_sobolevExtension_of_isSmoothingOperator S S C hC.1 s,
      LinearMap.ker_eq_bot.mpr hinj]
    simp
  have hcoker : Module.finrank ℂ (S.SobolevSpace (s - m) ⧸ T.range) = 0 := by
    rw [J.finrank_coker_sobolevExtension_of_isParametrix S S C hC s]
    let : Subsingleton (smoothSections (n := n) (r := r) E ⧸ J.toLinearMap.range) :=
      Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hsurj)
    exact Module.finrank_zero_of_subsingleton
  let : Subsingleton T.ker := Module.finrank_zero_iff.mp hker
  exact ⟨LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton,
    LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp
      (Module.finrank_zero_iff.mp hcoker))⟩

end AtiyahSinger.PseudodifferentialOperator
