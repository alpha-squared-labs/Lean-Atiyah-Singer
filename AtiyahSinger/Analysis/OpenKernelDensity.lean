/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenKernelTransport
public import AtiyahSinger.Analysis.SmoothKernelDensity
public import AtiyahSinger.Geometry.DensityDiffeomorph

/-!
# Actual integral transport of compact kernels through an open identification

Public module ID: M0825.

Transport the original positive measure on the open source, extend it near the
compact support of the transported kernel, and then change to the prescribed
target density. The resulting smooth-kernel operator retains the actual input
integral and both original fiber identifications. The source need not be compact.
This is the density and smoothing part of the open transport argument in SG III.13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace Set
open scoped ContDiff Manifold Topology

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [CompactSpace N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (a x).toLinearMap))
  (b : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hb : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (b x).toLinearMap))
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]

include ha hb in
/-- A compact source kernel has an exact smoothing integral transport for the target density. -/
theorem SmoothKernel.exists_openIntegralTransport
    (S : SmoothKernel (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (C : Set M) (hC : IsCompact C) (hCU : C ⊆ (U : Set M))
    (hS : ∀ x y, x ∉ C ∨ y ∉ C → S.toFun x y = 0) :
    ∃ R : smoothSections (n := n) (r := G.rank) G.Fiber →ₗ[ℂ]
        smoothSections (n := n) (r := H.rank) H.Fiber,
      IsSmoothingOperator ν R ∧
      (∀ (v : smoothSections (n := n) (r := G.rank) G.Fiber) y,
        y ∉ (V : Set N) → (R v).val y = 0) ∧
      ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
        (v : smoothSections (n := n) (r := G.rank) G.Fiber),
        (∀ x : U, x.val ∈ C → v.val (e x).val = a x (u.val x.val)) →
        ∀ x : U, (R v).val (e x).val = b x (S.apply μ u x.val) := by
  classical
  -- Keep one raw transported kernel, before assigning its integration density.
  obtain ⟨S', hS', C', hC', hC'V, hzero⟩ :=
    S.exists_openTransport E F G H U V e a ha b hb C hC hCU hS
  let μU := μ.comap (Subtype.val : U → M)
  have hμU : IsSmoothPositiveMeasure (n := n) μU :=
    isSmoothPositiveMeasure_comap_opens μ U
  let νV := Measure.map e μU
  have hνV : IsSmoothPositiveMeasure (n := n) νV :=
    IsSmoothPositiveMeasure.map_diffeomorph μU e
  -- Extend the actual pushed measure only near the compact kernel support.
  obtain ⟨ν', hν', W, hC'W, hWV, hmeasure⟩ :=
    exists_smoothPositiveMeasure_extension (n := n) V C' hC' hC'V νV
  let R := S'.toLinearMap ν'
  refine ⟨R, (isSmoothingOperator_measure_iff ν' ν R).mp ⟨S', rfl⟩, ?_, ?_⟩
  · intro v y hy
    let : NormedSpace ℝ (H.Fiber y) := NormedSpace.restrictScalars ℝ ℂ (H.Fiber y)
    change (∫ z, S'.toFun y z (v.val z) ∂ν') = 0
    have hz (z : N) : S'.toFun y z = 0 :=
      hzero y z (Or.inl (fun h ↦ hy (hC'V h)))
    simp only [hz, zero_apply, integral_zero]
  · intro u v hv x
    let : NormedSpace ℝ (H.Fiber (e x).val) :=
      NormedSpace.restrictScalars ℝ ℂ (H.Fiber (e x).val)
    let : NormedSpace ℝ (F.Fiber x.val) := NormedSpace.restrictScalars ℝ ℂ (F.Fiber x.val)
    let : FiniteDimensional ℂ (F.Fiber x.val) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x.val
    let : FiniteDimensional ℂ (H.Fiber (e x).val) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin H.rank)) H.Fiber (e x).val
    let B : F.Fiber x.val ≃L[ℂ] H.Fiber (e x).val :=
      (show F.Fiber x.val ≃ₗ[ℂ] H.Fiber (e x).val from b x).toContinuousLinearEquiv
    let f (y : N) := S'.toFun (e x).val y (v.val y)
    have hfzero (y : N) (hy : y ∉ C') : f y = 0 := by
      simp only [f, hzero _ _ (Or.inr hy), zero_apply]
    -- Inputs agreeing on C give identical integrands; outside C the raw kernel is zero.
    have hinput (y : U) : f (e y).val = B (S.toFun x.val y.val (u.val y.val)) := by
      by_cases hy : y.val ∈ C
      · change S'.toFun (e x).val (e y).val (v.val (e y).val) = _
        rw [hv y hy, hS']
        rfl
      · obtain ⟨w, hw⟩ := (a y).surjective (v.val (e y).val)
        change S'.toFun (e x).val (e y).val (v.val (e y).val) = _
        have heq := hS' x y w
        rw [hw] at heq
        rw [heq, hS x.val y.val (Or.inr hy)]
        simp only [zero_apply, map_zero]
        change B 0 = 0
        exact map_zero B
    have hlocal : (∫ y : V, f y.val ∂ν'.comap (Subtype.val : V → N)) =
        ∫ y : V, f y.val ∂νV := by
      let D : Set V := (Subtype.val : V → N) ⁻¹' (W : Set N)
      have hz (y : V) (hy : y ∉ D) : f y.val = 0 :=
        hfzero y.val (fun h ↦ hy (hC'W h))
      calc
        _ = ∫ y in D, f y.val ∂ν'.comap (Subtype.val : V → N) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
        _ = ∫ y in D, f y.val ∂νV := by rw [show
          (ν'.comap (Subtype.val : V → N)).restrict D = νV.restrict D from hmeasure]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hz
    -- All changes of variables use actual measures and the same fixed output fiber.
    change (∫ y, f y ∂ν') = B (∫ y, S.toFun x.val y (u.val y) ∂μ)
    calc
      _ = ∫ y in (V : Set N), f y ∂ν' :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy ↦ hfzero y (fun h ↦ hy (hC'V h)))).symm
      _ = ∫ y : V, f y.val ∂ν'.comap (Subtype.val : V → N) :=
        (integral_subtype_comap V.isOpen.measurableSet f).symm
      _ = ∫ y : V, f y.val ∂νV := hlocal
      _ = ∫ y : U, f (e y).val ∂μU :=
        e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map (fun y : V ↦ f y.val)
      _ = ∫ y : U, B (S.toFun x.val y.val (u.val y.val)) ∂μU :=
        integral_congr_ae (Filter.Eventually.of_forall hinput)
      _ = ∫ y in (U : Set M), B (S.toFun x.val y (u.val y)) ∂μ :=
        integral_subtype_comap (μ := μ) U.isOpen.measurableSet
          (fun y ↦ B (S.toFun x.val y (u.val y)))
      _ = ∫ y, B (S.toFun x.val y (u.val y)) ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by
          rw [hS x.val y (Or.inr (fun h ↦ hy (hCU h))), zero_apply,
            map_zero])
      _ = _ := B.integral_comp_comm _

end AtiyahSinger
