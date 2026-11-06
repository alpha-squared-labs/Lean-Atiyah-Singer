/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenSectionPairing
public import AtiyahSinger.Geometry.SmoothBundlePullback

/-!
# Supported sections under a specified open parametrization

Public module ID: M0917.

The actual smooth fiber comparison identifies supported source sections with
supported ambient sections. The same map preserves the integral pairing when
the given metrics and pushed-forward density agree on that support. The source
need not be compact. These are the precise common-source identifications used
to compare two relative elliptic realizations.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle TopologicalSpace MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n m : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [MeasurableSpace O] [BorelSpace O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact source fiber transport identifies supported sections and their original pairings. -/
theorem exists_pairingPreserving_supportedSectionOpenEmbeddingEquiv
    (E : SmoothFiniteComplexBundle (n := n) O)
    (G : SmoothFiniteComplexBundle (n := m) M) (U : Opens M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ U)
    (K : Set O) (L : Set M) (hL : IsClosed L) (hLU : L ⊆ U)
    (hKL : e ⁻¹' ((Subtype.val : U → M) ⁻¹' L) = K)
    (a : ∀ x : O, E.Fiber x ≃ₗ[ℂ] G.Fiber (e x).val)
    (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
      (E := E.Fiber)
      (F := ((⟨e, e.continuous⟩ : C(O, U)) : O → U) *ᵖ
        ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
      (fun x ↦ (a x).toLinearMap))
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (g : SmoothHermitianMetric (n := m) (r := G.rank) G.Fiber)
    (ν : Measure O) (μ : Measure M)
    (hpair : ∀ x : O, x ∈ K → ∀ v w : E.Fiber x,
      g.pairing (e x).val (a x v) (a x w) = h.pairing x v w)
    (hmeasure : Measure.map e (ν.restrict K) =
      (μ.comap (Subtype.val : U → M)).restrict ((Subtype.val : U → M) ⁻¹' L)) :
    ∃ A : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K ≃ₗ[ℂ]
        supportedSmoothSections (n := m) (r := G.rank) G.Fiber L,
      (∀ (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) (x : O),
        (A u).val.val (e x).val = a x (u.val.val x)) ∧
      ∀ u v, g.sectionPairing μ (A u).val (A v).val = h.sectionPairing ν u.val v.val := by
  let p : C(O, U) := ⟨e, e.continuous⟩
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  -- Apply the exact fiber map, undo base pullback, then extend the supported section by zero.
  let B := supportedSmoothSectionEquiv (n := n) (r := E.rank) (q := G.rank)
    (E := E.Fiber) (F := (p : O → U) *ᵖ ((i : U → M) *ᵖ G.Fiber)) K a ha
  let D := supportedSmoothSectionDiffeomorphEquiv (n := n) (m := m) (r := G.rank)
    ((i : U → M) *ᵖ G.Fiber) e ((Subtype.val : U → M) ⁻¹' L)
  let C := LinearEquiv.ofEq _ _
    (congrArg (supportedSmoothSections (n := n) (r := G.rank)
      ((p : O → U) *ᵖ ((i : U → M) *ᵖ G.Fiber))) hKL.symm)
  let S := supportedSmoothSectionRestrictionEquiv (n := m) (r := G.rank)
    G.Fiber U L hL hLU
  let A := (B.trans C).trans (D.symm.trans S.symm)
  have hvalue (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) (x : O) :
      (A u).val.val (e x).val = a x (u.val.val x) := by
    have hsame : D (S (A u)) = C (B u) := by
      change D (S (S.symm (D.symm (C (B u))))) = _
      exact (congrArg D (S.apply_symm_apply (D.symm (C (B u))))).trans
        (D.apply_symm_apply (C (B u)))
    have hx := congrArg (fun v ↦ v.val.val x) hsame
    change (A u).val.val (e x).val = (C (B u)).val.val x at hx
    have hc : (C (B u)).val = (B u).val := LinearEquiv.coe_ofEq_apply _ _
    exact hx.trans (congrArg (fun v ↦ v.val x) hc)
  refine ⟨A, hvalue, ?_⟩
  intro s t
  let f : O → ℂ := fun x ↦ h.pairing x (s.val.val x) (t.val.val x)
  let k : M → ℂ := fun y ↦ g.pairing y ((A s).val.val y) ((A t).val.val y)
  have hfzero (x : O) (hx : x ∉ K) : f x = 0 := by
    change h.pairing x (s.val.val x) (t.val.val x) = 0
    rw [s.property x hx]
    let := h.toCore x
    exact InnerProductSpace.Core.inner_zero_left _
  have hkzero (y : M) (hy : y ∉ L) : k y = 0 := by
    change g.pairing y ((A s).val.val y) ((A t).val.val y) = 0
    rw [(A s).property y hy]
    let := g.toCore y
    exact InnerProductSpace.Core.inner_zero_left _
  have hkf (x : O) : k (e x).val = f x := by
    by_cases hx : x ∈ K
    · change g.pairing (e x).val ((A s).val.val (e x).val)
        ((A t).val.val (e x).val) = _
      rw [hvalue s x, hvalue t x]
      exact hpair x hx _ _
    · have hy : (e x).val ∉ L := by
        intro hy
        apply hx
        change x ∈ e ⁻¹' ((Subtype.val : U → M) ⁻¹' L) at hy
        rwa [hKL] at hy
      exact (hkzero _ hy).trans (hfzero _ hx).symm
  -- The given equality of restricted measures compares the actual integrals, including Jacobians.
  change (∫ y, k y ∂μ) = ∫ x, f x ∂ν
  calc
    _ = ∫ y in (U : Set M), k y ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ hkzero y (fun hyL ↦ hy (hLU hyL)))).symm
    _ = ∫ y : U, k y.val ∂(μ.comap (Subtype.val : U → M)) :=
      (integral_subtype_comap U.isOpen.measurableSet k).symm
    _ = ∫ y in (Subtype.val : U → M) ⁻¹' L, k y.val
        ∂(μ.comap (Subtype.val : U → M)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ hkzero y.val hy)).symm
    _ = ∫ y : U, k y.val ∂Measure.map e (ν.restrict K) := by rw [hmeasure]
    _ = ∫ x in K, k (e x).val ∂ν :=
      e.toHomeomorph.measurableEmbedding.integral_map (fun y : U ↦ k y.val)
    _ = ∫ x in K, f x ∂ν := integral_congr_ae (Filter.Eventually.of_forall hkf)
    _ = ∫ x, f x ∂ν := setIntegral_eq_integral_of_forall_compl_eq_zero hfzero

end AtiyahSinger
