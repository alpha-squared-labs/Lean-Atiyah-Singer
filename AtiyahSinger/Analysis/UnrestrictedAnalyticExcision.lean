/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndexDimension
public import AtiyahSinger.Analysis.EquivariantIndexExcision
public import AtiyahSinger.Geometry.OrthogonalGroupManifold
public import AtiyahSinger.Topology.OpenCotangentKZero
public import AtiyahSinger.Topology.TrivialEquivariantKTheory

/-!
# Ordinary analytic excision for an arbitrary open source

Public module ID: M1046.

The arbitrary-source equivariant excision theorem specializes to the trivial
compact Lie group O(0). Forgetting that action retains the original support
class, both inverse-dual open embeddings and the two independent densities.
This form is used for the normal neighborhood in the compact embedding theorem.

Source: SG III.13, Excision Property 13.4; the removal of the finite-CW premise
uses the compact-control localization already present in equivariant excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 35

variable {n : ℕ} {O M N : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold (𝓡 n) ∞ O] [T2Space O] [SecondCountableTopology O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option maxHeartbeats 1000000 in
-- Use the same cotangent actions in excision and in both forgetful index comparisons.
/-- Two compact environments give the same analytic index on any common open source. -/
theorem analyticIndexOfComponents_excision_of_openSource
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]
    (U : Opens M) (V : Opens N)
    (f : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ U) (g : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ V) :
    (analyticIndexOfComponents μ).comp (cotangentKZeroOpenEmbedding U f) =
      (analyticIndexOfComponents ν).comp (cotangentKZeroOpenEmbedding V g) := by
  classical
  let G := Matrix.orthogonalGroup (Fin 0) ℝ
  let VG := OrthogonalGroupModel 0
  let := orthogonalGroupChartedSpace 0
  let := lieGroup_orthogonalGroup 0
  let := compactSpace_orthogonalGroup 0
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  -- The original base manifolds have the trivial action; their atlases are unchanged.
  let : MulAction G O :=
    { smul := fun _ x ↦ x
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl }
  let : MulAction G M :=
    { smul := fun _ x ↦ x
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl }
  let : MulAction G N :=
    { smul := fun _ x ↦ x
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl }
  let : ContinuousSMul G O := ⟨continuous_snd⟩
  let : ContinuousSMul G M := ⟨continuous_snd⟩
  let : ContinuousSMul G N := ⟨continuous_snd⟩
  let : ContMDiffSMul 𝓘(ℝ, VG) (𝓡 n) ∞ G O := ⟨contMDiff_snd⟩
  let : ContMDiffSMul 𝓘(ℝ, VG) (𝓡 n) ∞ G M := ⟨contMDiff_snd⟩
  let : ContMDiffSMul 𝓘(ℝ, VG) (𝓡 n) ∞ G N := ⟨contMDiff_snd⟩
  have hf (a : G) (x : O) : (f (a • x) : M) = a • (f x : M) := rfl
  have hg (a : G) (x : O) : (g (a • x) : N) = a • (g x : N) := rfl
  let := smoothCotangentMulAction (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := O)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  have hexc := equivariantAnalyticIndexMap_excision (VG := VG) U V f g hf hg
  have hdimM := representationDimension_equivariantAnalyticIndexMap
    (n := n) (M := M) (VG := VG) (G := G) μ
  have hdimN := representationDimension_equivariantAnalyticIndexMap
    (n := n) (M := N) (VG := VG) (G := G) ν
  -- Lift this same ordinary class before applying the full representation equality.
  apply AddMonoidHom.ext
  intro u
  obtain ⟨v, hv⟩ := supportTripleKZeroToCompactSupport_surjective u
  obtain ⟨a, ha⟩ :=
    (ComplexBundle.equivariantSupportTripleKZeroForget_bijective_of_subsingleton
      (G := G) (X := CotangentTotalSpace (n := n) (M := O))).surjective v
  have hforget : supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget a) = u := by rw [ha, hv]
  have hvalue := congrArg (representationDimension G) (DFunLike.congr_fun hexc a)
  have hM := DFunLike.congr_fun hdimM
    (equivariantCotangentKZeroOpenEmbedding (VG := VG) U f hf a)
  have hN := DFunLike.congr_fun hdimN
    (equivariantCotangentKZeroOpenEmbedding (VG := VG) V g hg a)
  simp only [AddMonoidHom.comp_apply] at hvalue hM hN
  rw [hM, hN] at hvalue
  change analyticIndexOfComponents μ (supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (equivariantSupportTripleKZeroOpenPushforward (cotangentOpenEmbeddingMap U f)
          (isOpenEmbedding_cotangentOpenEmbeddingMap U f)
          (cotangentOpenEmbeddingMap_equivariant (VG := VG) U f hf) a))) =
    analyticIndexOfComponents ν (supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (equivariantSupportTripleKZeroOpenPushforward (cotangentOpenEmbeddingMap V g)
          (isOpenEmbedding_cotangentOpenEmbeddingMap V g)
          (cotangentOpenEmbeddingMap_equivariant (VG := VG) V g hg) a))) at hvalue
  rw [equivariantSupportTripleKZeroOpenPushforward_forget,
    equivariantSupportTripleKZeroOpenPushforward_forget, hforget] at hvalue
  -- Compose the same inverse-dual homeomorphism and original open inclusion.
  have hpushM : compactSupportKZeroOpenPushforward (cotangentOpenEmbeddingMap U f)
      (isOpenEmbedding_cotangentOpenEmbeddingMap U f) = cotangentKZeroOpenEmbedding U f := by
    change _ = (compactSupportKZeroOpenPushforward (cotangentOpenInclusion U)
      (isOpenEmbedding_cotangentOpenInclusion U)).comp
        (compactSupportKZeroHomeomorph (cotangentDiffeomorph f))
    rw [← compactSupportKZeroOpenPushforward_homeomorph,
      ← compactSupportKZeroOpenPushforward_comp]
    rfl
  have hpushN : compactSupportKZeroOpenPushforward (cotangentOpenEmbeddingMap V g)
      (isOpenEmbedding_cotangentOpenEmbeddingMap V g) = cotangentKZeroOpenEmbedding V g := by
    change _ = (compactSupportKZeroOpenPushforward (cotangentOpenInclusion V)
      (isOpenEmbedding_cotangentOpenInclusion V)).comp
        (compactSupportKZeroHomeomorph (cotangentDiffeomorph g))
    rw [← compactSupportKZeroOpenPushforward_homeomorph,
      ← compactSupportKZeroOpenPushforward_comp]
    rfl
  simpa only [AddMonoidHom.comp_apply, hpushM, hpushN] using hvalue

end AtiyahSinger
