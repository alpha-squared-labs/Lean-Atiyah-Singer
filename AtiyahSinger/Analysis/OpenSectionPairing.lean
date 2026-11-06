/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SupportedSectionPairing
public import AtiyahSinger.Geometry.DensityDiffeomorph
public import AtiyahSinger.Geometry.OpenSectionIdentification

/-!
# Integral pairings under actual section transport

Public module ID: M0836.

D02/UL03/P02: compare the actual scalar integrals under diffeomorphism pullback
and under the section identification through two diffeomorphic open regions.
The metric and measure hypotheses refer to the same specified maps and only to
the support. These are standard change-of-variables supplements to the two-kernel
argument of SG III.13.4, pp.248--249, not a claim of PDO intertwining or excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

section Diffeomorph

variable {n r : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  {E : N → Type*} [∀ y, NormedAddCommGroup (E y)] [∀ y, NormedSpace ℂ (E y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

include hM hN hT hT' hSC hSC'


set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- The actual supported pullback preserves pairings with the pushed-forward density. -/
theorem SmoothHermitianMetric.sectionPairing_diffeomorph
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N)
    (k : SmoothHermitianMetric (n := n) (r := r)
      (((⟨e, e.continuous⟩ : C(M, N)) : M → N) *ᵖ E))
    (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
    (K : Set N) (hK : IsCompact K)
    (hk : ∀ x, e x ∈ K → ∀ v w : E (e x), k.pairing x v w = h.pairing (e x) v w)
    (s : supportedSmoothSections (n := n) (r := r) E K)
    (t : smoothSections (n := n) (r := r) E) :
    k.sectionPairing μ (supportedSmoothSectionDiffeomorphEquiv E e K s).val
        (smoothSectionDiffeomorphEquiv E e t) =
      h.sectionPairing (Measure.map e μ) s.val t := by
  /- The actual pullback maps have the values s(e x) and t(e x). On e⁻¹(K)
  use the supplied metric identity; outside it both integrands vanish. Apply
  the Borel embedding's total-integral identity to the same pushforward measure.
  No prior smooth-density transport or integrability theorem is needed for
  this equality. The retained compact-support hypotheses separately ensure
  finiteness when it is required downstream; the second section need not
  be compactly supported, and the metrics may differ off e⁻¹(K). -/
  -- The metric identities are needed only where the original supported section is nonzero.
  have hpoint (x : M) :
      k.pairing x (s.val.val (e x)) (t.val (e x)) =
        h.pairing (e x) (s.val.val (e x)) (t.val (e x)) := by
    by_cases hx : e x ∈ K
    · exact hk x hx _ _
    · rw [s.property (e x) hx]
      have hz₁ : k.pairing x 0 (t.val (e x)) = 0 := by
        let := k.toCore x
        exact InnerProductSpace.Core.inner_zero_left _
      have hz₂ : h.pairing (e x) 0 (t.val (e x)) = 0 := by
        let := h.toCore (e x)
        exact InnerProductSpace.Core.inner_zero_left _
      exact hz₁.trans hz₂.symm
  -- The same base diffeomorphism is a Borel embedding, so its total integrals agree.
  change (∫ x, k.pairing x (s.val.val (e x)) (t.val (e x)) ∂μ) = _
  calc
    _ = ∫ x, h.pairing (e x) (s.val.val (e x)) (t.val (e x)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = _ := (e.toHomeomorph.measurableEmbedding.integral_map
      (fun y ↦ h.pairing y (s.val.val y) (t.val y))).symm

end Diffeomorph

section OpenRegion

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

include hM hN hT hT' hSC hSC'


set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
-- Match the original supported sections and restricted measures through the same open map.
/-- The concrete open-region section identification preserves the supported integral pairing. -/
theorem SmoothHermitianMetric.sectionPairing_openEquiv
    (E : SmoothFiniteComplexBundle (n := n) M) (F : SmoothFiniteComplexBundle (n := m) N)
    (U : Opens M) (V : Opens N)
    (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ V)
    (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
    (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
    (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
    (a : ∀ x : U,
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
        (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
          ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber)) x)
    (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (a x).toLinearMap))
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := m) (r := F.rank) F.Fiber)
    (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [hν : IsSmoothPositiveMeasure (n := m) ν]
    (hk : ∀ (x : U), x.val ∈ K → ∀ v w : E.Fiber x.val,
      k.pairing (e x).val (a x v) (a x w) = h.pairing x.val v w)
    (hμν : Measure.map e ((μ.comap (Subtype.val : U → M)).restrict
        ((Subtype.val : U → M) ⁻¹' K)) =
      (ν.comap (Subtype.val : V → N)).restrict ((Subtype.val : V → N) ⁻¹' L))
    (s t : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) :
    let A := supportedSmoothSectionOpenEquiv E F U V e K L
      hK.isClosed hL.isClosed hKU hLV hKL a ha
    k.sectionPairing ν (A s).val (A t).val = h.sectionPairing μ s.val t.val := by
  /- Stage 1: cancel the exact restriction, fiber equivalence, inverse
  pullback and zero-extension maps to identify their value at corresponding
  points. The support-set transport changes no underlying section value.
  Stage 2: the original metrics agree on K; off K and L the supported
  integrands vanish. Restrict the total integrals to the actual open regions
  and then to these supports. Stage 3: apply the given equality of restricted
  comap measures and the Borel diffeomorphism's integral identity.
  No smooth-density transport theorem is used. This proves the conditional
  pairing identity, not PDO intertwining or the excision theorem. -/
  classical
  let A := supportedSmoothSectionOpenEquiv E F U V e K L
    hK.isClosed hL.isClosed hKU hLV hKL a ha
  change k.sectionPairing ν (A s).val (A t).val = h.sectionPairing μ s.val t.val
  -- Identify the original restriction/transport/inverse-pullback/extension at matching points.
  have hvalue (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) (x : U) :
      (A u).val.val (e x).val = a x (u.val.val x.val) := by
    let R := supportedSmoothSectionRestrictionEquiv (n := n) (r := E.rank)
      E.Fiber U K hK.isClosed hKU
    let B := supportedSmoothSectionEquiv (M := U) (n := n) (r := E.rank) (q := F.rank)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber))
      (F := (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber)))
      ((Subtype.val : U → M) ⁻¹' K) a ha
    let D := supportedSmoothSectionDiffeomorphEquiv (M := U) (N := V)
      (n := n) (m := m) (r := F.rank)
      ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber) e
      ((Subtype.val : V → N) ⁻¹' L)
    let C := LinearEquiv.ofEq _ _
      (congrArg (supportedSmoothSections (n := n) (r := F.rank)
        (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
          ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber))) hKL.symm)
    let S := supportedSmoothSectionRestrictionEquiv (n := m) (r := F.rank)
      F.Fiber V L hL.isClosed hLV
    have hsame : D (S (A u)) = C (B (R u)) := by
      change D (S (S.symm (D.symm (C (B (R u)))))) = _
      exact (congrArg D (S.apply_symm_apply (D.symm (C (B (R u)))))).trans
        (D.apply_symm_apply (C (B (R u))))
    have hx := congrArg (fun v ↦ v.val.val x) hsame
    change (A u).val.val (e x).val = (C (B (R u))).val.val x at hx
    have hc : (C (B (R u))).val = (B (R u)).val := LinearEquiv.coe_ofEq_apply _ _
    exact hx.trans (congrArg (fun v ↦ v.val x) hc)
  let f : M → ℂ := fun x ↦ h.pairing x (s.val.val x) (t.val.val x)
  let g : N → ℂ := fun y ↦ k.pairing y ((A s).val.val y) ((A t).val.val y)
  have hfzero (x : M) (hx : x ∉ K) : f x = 0 := by
    change h.pairing x (s.val.val x) (t.val.val x) = 0
    rw [s.property x hx]
    let := h.toCore x
    exact InnerProductSpace.Core.inner_zero_left _
  have hgzero (y : N) (hy : y ∉ L) : g y = 0 := by
    change k.pairing y ((A s).val.val y) ((A t).val.val y) = 0
    rw [(A s).property y hy]
    let := k.toCore y
    exact InnerProductSpace.Core.inner_zero_left _
  have hfg (x : U) : g (e x).val = f x.val := by
    by_cases hx : x.val ∈ K
    · change k.pairing (e x).val ((A s).val.val (e x).val)
        ((A t).val.val (e x).val) = _
      rw [hvalue s x, hvalue t x]
      exact hk x hx _ _
    · have hy : (e x).val ∉ L := by
        intro hy
        apply hx
        have : x ∈ e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) := hy
        rw [hKL] at this
        exact this
      exact (hgzero _ hy).trans (hfzero _ hx).symm
  -- Restrict to the actual open regions and supports, then transport the given measure.
  change (∫ y, g y ∂ν) = ∫ x, f x ∂μ
  calc
    _ = ∫ y in (V : Set N), g y ∂ν :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ hgzero y (fun hyL ↦ hy (hLV hyL)))).symm
    _ = ∫ y : V, g y.val ∂(ν.comap (Subtype.val : V → N)) :=
      (integral_subtype_comap V.isOpen.measurableSet g).symm
    _ = ∫ y in (Subtype.val : V → N) ⁻¹' L, g y.val
        ∂(ν.comap (Subtype.val : V → N)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ hgzero y.val hy)).symm
    _ = ∫ y : V, g y.val ∂Measure.map e
        ((μ.comap (Subtype.val : U → M)).restrict ((Subtype.val : U → M) ⁻¹' K)) := by
      rw [hμν]
    _ = ∫ x in (Subtype.val : U → M) ⁻¹' K, g (e x).val
        ∂(μ.comap (Subtype.val : U → M)) :=
      e.toHomeomorph.measurableEmbedding.integral_map (fun y : V ↦ g y.val)
    _ = ∫ x in (Subtype.val : U → M) ⁻¹' K, f x.val
        ∂(μ.comap (Subtype.val : U → M)) :=
      integral_congr_ae (Filter.Eventually.of_forall hfg)
    _ = ∫ x : U, f x.val ∂(μ.comap (Subtype.val : U → M)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hfzero x.val hx)
    _ = ∫ x in (U : Set M), f x ∂μ := integral_subtype_comap U.isOpen.measurableSet f
    _ = ∫ x, f x ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ hfzero x (fun hxK ↦ hx (hKU hxK)))

end OpenRegion

end AtiyahSinger
