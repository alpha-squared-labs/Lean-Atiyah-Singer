/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialLocalAction
public import AtiyahSinger.Analysis.SchwartzKernelExistence

/-!
# The full original PDO as a local Schwartz operator

Public module ID: M0289.

Original input extension and presentation localization turn the whole PDO
into a continuous Schwartz operator. Every finite-order output jet is one
of the bounded derivative coordinates defining the same C^k section norm.
On the fixed original output support these jets control Schwartz continuity.
Finite coordinate reconstruction retains the original vector-valued output,
including zero rank. The smoothing remainder remains part of the operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set Topology
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E} {B : SmoothComplexBundleAtlas (n := n) F}

namespace AtlasPseudodifferentialOperator

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original cutoff extension and presentation localization give the full Schwartz action. -/
theorem exists_localActionSchwartz {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (D : AtlasChartCutoff A c) (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (j : Fin K.size) :
    ∃ T : 𝓢(EuclideanSpace ℝ (Fin n),
        EuclideanSpace ℂ (Fin (A.rank D.frameIndex))) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank (K.frameIndex j)))),
      ∀ v, T v = K.localize j (P.toLinearMap (D.extend hc v)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin (A.rank D.frameIndex))
  let W := EuclideanSpace ℂ (Fin (B.rank (K.frameIndex j)))
  let R : 𝓢(X, V) →ₗ[ℂ] 𝓢(X, W) :=
    (K.localizeLinearMap j).comp (P.toLinearMap.comp (D.extendLinearMap hc))
  let H : Set X := (K.chart j) '' tsupport (K.cutoff j)
  have hH : IsCompact H := (K.compact_support j).image_of_continuousOn
    ((K.chart j).continuousOn.mono (fun x hx ↦ (K.support_subset j hx).1))
  have hsupp (v : 𝓢(X, V)) : tsupport (R v) ⊆ H :=
    (K.localizedFunction_properties j (P.toLinearMap (D.extend hc v))).2.1
  -- The original C^k norm contains exactly the k-th localized output derivative.
  have hjets (k : ℕ) :
      Continuous (fun p : 𝓢(X, V) × X ↦ iteratedFDeriv ℝ k (R p.1) p.2) := by
    obtain ⟨T, hT⟩ := P.exists_localActionCk L K D hc k
    have hiso : Isometry (K.ckDerivativeCoordinates k) := by
      intro u v
      rfl
    have hcoord := (continuous_apply (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))).comp
      ((continuous_apply j).comp (hiso.continuous.comp T.continuous))
    have heval := (hcoord.comp continuous_fst).eval continuous_snd
    change Continuous (fun p : 𝓢(X, V) × X ↦
      iteratedFDeriv ℝ k (K.localizedCkFunction k j (T p.1)) p.2) at heval
    have heq (v : 𝓢(X, V)) : K.localizedCkFunction k j (T v) = R v := by
      rw [hT v]
      rfl
    simpa only [heq] using heval
  -- Scalar coordinate projections inherit all jets and the same compact support.
  let f (i : Fin (B.rank (K.frameIndex j))) (v : 𝓢(X, V)) : 𝓢(X, ℂ) :=
    SchwartzMap.postcompCLM (EuclideanSpace.proj (𝕜 := ℂ) i) (R v)
  have hf (i : Fin (B.rank (K.frameIndex j))) : Continuous (f i) := by
    apply continuous_schwartzMap_of_common_compact_support (f i) H hH
    · intro v
      exact (tsupport_comp_subset (g := EuclideanSpace.proj (𝕜 := ℂ) i)
        (map_zero _) (R v)).trans (hsupp v)
    · intro k
      let e := (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
      have hcont := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin k ↦ X) W ℂ e).continuous.comp (hjets k)
      convert hcont using 1
      funext p
      exact e.iteratedFDeriv_comp_left ((R p.1).smooth ⊤).contDiffAt (by simp)
  -- Reconstruct the actual vector output from its finite standard coordinates.
  let lift (i : Fin (B.rank (K.frameIndex j))) : 𝓢(X, ℂ) →L[ℂ] 𝓢(X, W) :=
    SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight
      (EuclideanSpace.single i 1))
  have hproj (i : Fin (B.rank (K.frameIndex j))) (w : W) :
      (EuclideanSpace.proj (𝕜 := ℂ) i) w = w i := rfl
  have hsum (v : 𝓢(X, V)) : R v = ∑ i, lift i (f i v) := by
    apply SchwartzMap.ext
    intro x
    simp only [sum_apply, lift, f, SchwartzMap.postcompCLM_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    symm
    simpa only [hproj, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin (B.rank (K.frameIndex j))) ℂ).toBasis.sum_repr (R v x)
  have hR : Continuous R := by
    have h : Continuous (fun v : 𝓢(X, V) ↦ ∑ i, lift i (f i v)) := by
      apply continuous_finsetSum
      intro i _
      exact (lift i).continuous.comp (hf i)
    simpa only [← hsum] using h
  exact ⟨{ R with cont := hR }, fun _ ↦ rfl⟩

end AtlasPseudodifferentialOperator

end AtiyahSinger
