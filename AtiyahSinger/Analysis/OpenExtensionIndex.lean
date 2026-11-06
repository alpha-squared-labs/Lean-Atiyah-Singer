/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialSupport
public import AtiyahSinger.Analysis.EllipticOpenExtension
public import AtiyahSinger.Analysis.OpenSectionPairing
public import AtiyahSinger.Analysis.SupportedOperatorComparison
public import AtiyahSinger.Geometry.SmoothSectionEvaluation

import all AtiyahSinger.Analysis.ExcisionLocalization

/-!
# Index comparison for exact supported open extensions

Public module ID: M0819.

UL03/P02: both full kernel supports and the required adjoint support control
follow from an exterior invertible bundle map plus a two-sided supported PDO.
The correction's exact extension law supplies the original intertwining, and
specified metric/density matching on the controls supplies the pairings. No kernel-support or
adjoint-intertwining hypothesis is assumed separately. This is the conditional
analytic comparison in SG III.13.4 under explicit geometric data. Full K-theory
excision additionally uses relative representatives and identification of the
corresponding symbol-extension class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace Filter
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

section SupportedPerturbation

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hB : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT hSC hC hB hE hF hμ

set_option maxHeartbeats 1200000 in
-- Compare the same supported perturbation with its exact metric adjoint.
/-- A supported perturbation of an exterior bundle isomorphism controls both full kernels.
This standard support argument is used in each of the two ambient environments below. -/
private theorem support_and_kernel_of_supported_perturbation
    (P R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (c : ∀ x, E x →ₗ[ℂ] F x) (hc : IsSmoothBundleMap (n := n) (r := r) (q := q) c)
    (hP : P.toLinearMap = smoothSectionMap c hc + R.toLinearMap)
    (K : Set M) (hK : IsClosed K) (hR : HasSectionOperatorSupport K R.toLinearMap)
    (hext : ∀ x, x ∉ K → Function.Bijective (c x))
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F) :
    (∀ u : supportedSmoothSections (n := n) (r := r) E K,
      P.toLinearMap u.val ∈ supportedSmoothSections (n := n) (r := q) F K) ∧
    (∀ v : supportedSmoothSections (n := n) (r := q) F K,
      (P.metricFormalAdjoint h k).toLinearMap v.val ∈
        supportedSmoothSections (n := n) (r := r) E K) ∧
    P.toLinearMap.ker ≤ supportedSmoothSections (n := n) (r := r) E K ∧
    (P.metricFormalAdjoint h k).toLinearMap.ker ≤
      supportedSmoothSections (n := n) (r := q) F K := by
  classical
  let B : DifferentialOperator (n := n) (r := r) (q := q) E F 0 :=
    ⟨smoothSectionMap c hc, isDifferentialOperator_smoothSectionMap c hc⟩
  let Bd := B.metricFormalAdjoint (μ := μ) h k
  let Rd := R.metricFormalAdjoint h k
  have hRd : HasSectionOperatorSupport K Rd.toLinearMap :=
    IsMetricFormalAdjoint.hasSectionOperatorSupport h k μ R.toLinearMap Rd.toLinearMap
      (R.isMetricFormalAdjoint_metricFormalAdjoint h k) K hK hR
  -- The exact adjoint retains the differential part and the same supported residual.
  have hsum := (B.isMetricFormalAdjoint_metricFormalAdjoint h k).add
    (R.isMetricFormalAdjoint_metricFormalAdjoint h k)
  have hsumP : IsMetricFormalAdjoint h k μ P.toLinearMap
      (Bd.toLinearMap + Rd.toLinearMap) := by
    rw [hP]
    exact hsum
  have hPadj := (P.isMetricFormalAdjoint_metricFormalAdjoint h k).unique hsumP
  have hRzero (u : smoothSections (n := n) (r := r) E) (x : M) (hx : x ∉ K) :
      (R.toLinearMap u).val x = 0 := by
    by_contra hne
    exact hx (hR.1 u (subset_closure hne))
  have hRdZero (v : smoothSections (n := n) (r := q) F) (x : M) (hx : x ∉ K) :
      (Rd.toLinearMap v).val x = 0 := by
    by_contra hne
    exact hx (hRd.1 v (subset_closure hne))
  have hsymbol (x : M) (w : E x) : B.principalSymbol x 0 w = c x w := by
    obtain ⟨u, hu⟩ := exists_smoothSection_apply_eq (n := n) (r := r) x w
    have hv := zeroOrder_apply_eq_principalSymbol B u x 0
    change c x (u.val x) = B.principalSymbol x 0 (u.val x) at hv
    simpa only [hu] using hv.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u x hx
    rw [hP]
    change c x (u.val.val x) + (R.toLinearMap u.val).val x = 0
    rw [u.property x hx, map_zero, hRzero u.val x hx, add_zero]
  · intro v x hx
    have hb := Bd.map_mem_supportedSmoothSections K hK v
    rw [hPadj]
    change (Bd.toLinearMap v.val).val x + (Rd.toLinearMap v.val).val x = 0
    rw [hb x hx, hRdZero v.val x hx, add_zero]
  · intro u hu x hx
    have hz := congrArg (fun v : smoothSections (n := n) (r := q) F ↦ v.val x) hu
    rw [hP] at hz
    change c x (u.val x) + (R.toLinearMap u).val x = 0 at hz
    rw [hRzero u x hx, add_zero] at hz
    exact (hext x hx).1 (hz.trans (map_zero _).symm)
  · intro v hv x hx
    have hz := congrArg (fun u : smoothSections (n := n) (r := r) E ↦ u.val x) hv
    rw [hPadj] at hz
    change (Bd.toLinearMap v).val x + (Rd.toLinearMap v).val x = 0 at hz
    rw [hRdZero v x hx, add_zero] at hz
    have hb := zeroOrder_apply_eq_principalSymbol Bd v x 0
    have hbd : Bd.principalSymbol x 0 (v.val x) = 0 := hb.symm.trans hz
    -- Exterior surjectivity and the original positive metric annihilate the adjoint kernel.
    obtain ⟨w, hw⟩ := (hext x hx).2 (v.val x)
    have hpair := B.principalSymbol_metricFormalAdjoint_pairing (μ := μ) h k x 0 w (v.val x)
    rw [hsymbol, hw] at hpair
    change k.pairing x (v.val x) (v.val x) =
      h.pairing x w (Bd.principalSymbol x 0 (v.val x)) at hpair
    rw [hbd] at hpair
    apply (k.toCore x).definite
    apply hpair.trans
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact InnerProductSpace.Core.inner_zero_right w

end SupportedPerturbation

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
  (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
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
  [hC' : CompactSpace N] [MeasurableSpace N] [hB' : BorelSpace N]
  (ν : Measure N) [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hN hT hT' hSC hSC' hC' hB' hν hK hL hKU hLV hKL ha hb

variable [hC : CompactSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (c : ∀ x, E.Fiber x →ₗ[ℂ] F.Fiber x)
  (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank) c)
  (d : ∀ y, G.Fiber y →ₗ[ℂ] H.Fiber y)
  (hd : IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank) d)
  (hcd : ∀ (x : U) (v : E.Fiber x.val), d (e x).val (a x v) = b x (c x.val v))

include hC hB hμ hcd

set_option maxHeartbeats 2000000 in
-- The two supported transports use the prescribed fiber maps and pairing data.
/-- Exact extension of supported corrections, with matching geometry, preserves the full index. -/
theorem PseudodifferentialOperator.index_eq_of_openExtension
    (P R : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0)
    (Q S : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber ν 0)
    (hP : P.toLinearMap = smoothSectionMap c hc + R.toLinearMap)
    (hQ : Q.toLinearMap = smoothSectionMap d hd + S.toLinearMap)
    (hR : HasSectionOperatorSupport K R.toLinearMap)
    (hS : HasSectionOperatorSupport L S.toLinearMap)
    (hPe : P.IsElliptic) (hQe : Q.IsElliptic)
    (hcext : ∀ x, x ∉ K → Function.Bijective (c x))
    (hdext : ∀ y, y ∉ L → Function.Bijective (d y))
    (hRS : ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := G.rank) G.Fiber),
      (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) →
      ∀ x : U, (S.toLinearMap v).val (e x).val = b x ((R.toLinearMap u).val x.val))
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (h' : SmoothHermitianMetric (n := n) (r := G.rank) G.Fiber)
    (k' : SmoothHermitianMetric (n := n) (r := H.rank) H.Fiber)
    (hha : ∀ (x : U), x.val ∈ K → ∀ v w : E.Fiber x.val,
      h'.pairing (e x).val (a x v) (a x w) = h.pairing x.val v w)
    (hkb : ∀ (x : U), x.val ∈ K → ∀ v w : F.Fiber x.val,
      k'.pairing (e x).val (b x v) (b x w) = k.pairing x.val v w)
    (hμν : Measure.map e ((μ.comap (Subtype.val : U → M)).restrict
        ((Subtype.val : U → M) ⁻¹' K)) =
      (ν.comap (Subtype.val : V → N)).restrict ((Subtype.val : V → N) ⁻¹' L)) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  /- Stage 1: adjunction and HasSectionOperatorSupport transfer two-sided
  support from R and S to their actual metric adjoints. The adjoints of the
  zero-order bundle maps are their pointwise fiber adjoints. Consequently P,Q
  and both adjoints preserve the controlled section spaces. Outside K or L,
  each kernel equation reduces to an invertible fiber map or its invertible
  adjoint. Thus all four full kernels have the required support; none of these
  inclusions is an input hypothesis. Exterior invertibility is kept even in
  dimension zero, where off-zero ellipticity alone is vacuous.
  Stage 2: form the concrete supported open equivalences A and B. Their value
  formulas supply the germ hypothesis for hRS; add the zero-order identity hcd
  to obtain the exact original intertwining. The preceding open-region pairing
  theorem, with hha, hkb and hμν, supplies both integral pairing identities.
  Stage 3: apply index_eq_of_supported_intertwining. Its adjoint comparison is
  derived from adjunction and support, and ellipticity supplies the finite
  two-kernel index formula. The output is the index of the actual section maps.
  This conditional analytic comparison uses the given relative geometric data;
  the symbol K-class extension is a separate identification. -/
  classical
  -- Both full kernels and the supported actions follow from the exterior isomorphisms.
  obtain ⟨hPP, hPR, hkerP, hkerR⟩ := support_and_kernel_of_supported_perturbation
    P R c hc hP K hK.isClosed hR hcext h k
  obtain ⟨hQQ, hQS, hkerQ, hkerS⟩ := support_and_kernel_of_supported_perturbation
    Q S d hd hQ L hL.isClosed hS hdext h' k'
  let A := supportedSmoothSectionOpenEquiv E G U V e K L
    hK.isClosed hL.isClosed hKU hLV hKL a ha
  let B := supportedSmoothSectionOpenEquiv F H U V e K L
    hK.isClosed hL.isClosed hKU hLV hKL b hb
  -- Cancel the original restriction, bundle map, inverse pullback and zero extension.
  have hvalue (E₀ : SmoothFiniteComplexBundle (n := n) M)
      (G₀ : SmoothFiniteComplexBundle (n := n) N)
      (a : ∀ x : U,
        ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E₀.Fiber) x ≃ₗ[ℂ]
          (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
            ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G₀.Fiber)) x)
      (ha : IsSmoothBundleMap (n := n) (r := E₀.rank) (q := G₀.rank)
        (fun x ↦ (a x).toLinearMap))
      (u : supportedSmoothSections (n := n) (r := E₀.rank) E₀.Fiber K) (x : U) :
      let T := supportedSmoothSectionOpenEquiv E₀ G₀ U V e K L
        hK.isClosed hL.isClosed hKU hLV hKL a ha
      (T u).val.val (e x).val = a x (u.val.val x.val) := by
    let T := supportedSmoothSectionOpenEquiv E₀ G₀ U V e K L
      hK.isClosed hL.isClosed hKU hLV hKL a ha
    let R := supportedSmoothSectionRestrictionEquiv (n := n) (r := E₀.rank)
      E₀.Fiber U K hK.isClosed hKU
    let B := supportedSmoothSectionEquiv (M := U) (n := n) (r := E₀.rank) (q := G₀.rank)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E₀.Fiber))
      (F := (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G₀.Fiber)))
      ((Subtype.val : U → M) ⁻¹' K) a ha
    let D := supportedSmoothSectionDiffeomorphEquiv (M := U) (N := V)
      (n := n) (m := n) (r := G₀.rank)
      ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G₀.Fiber) e
      ((Subtype.val : V → N) ⁻¹' L)
    let C := LinearEquiv.ofEq _ _
      (congrArg (supportedSmoothSections (n := n) (r := G₀.rank)
        (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
          ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G₀.Fiber))) hKL.symm)
    let S := supportedSmoothSectionRestrictionEquiv (n := n) (r := G₀.rank)
      G₀.Fiber V L hL.isClosed hLV
    have hsame : D (S (T u)) = C (B (R u)) := by
      change D (S (S.symm (D.symm (C (B (R u)))))) = _
      exact (congrArg D (S.apply_symm_apply (D.symm (C (B (R u)))))).trans
        (D.apply_symm_apply (C (B (R u))))
    have hx := congrArg (fun v ↦ v.val.val x) hsame
    change (T u).val.val (e x).val = (C (B (R u))).val.val x at hx
    have hc : (C (B (R u))).val = (B (R u)).val := LinearEquiv.coe_ofEq_apply _ _
    exact hx.trans (congrArg (fun v ↦ v.val x) hc)
  have hA (u v : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) :
      h'.sectionPairing ν (A u).val (A v).val = h.sectionPairing μ u.val v.val :=
    SmoothHermitianMetric.sectionPairing_openEquiv E G U V e K L hK hL hKU hLV hKL
      a ha h h' μ ν hha hμν u v
  have hB (u v : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K) :
      k'.sectionPairing ν (B u).val (B v).val = k.sectionPairing μ u.val v.val :=
    SmoothHermitianMetric.sectionPairing_openEquiv F H U V e K L hK hL hKU hLV hKL
      b hb k k' μ ν hkb hμν u v
  -- The prescribed germ equation identifies the same supported operator outputs.
  have hPQ (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) :
      Q.toLinearMap (A u).val = (B ⟨P.toLinearMap u.val, hPP u⟩).val := by
    have hgerm : ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        (A u).val.val (e x).val = a x (u.val.val x.val) :=
      Filter.Eventually.of_forall (hvalue E G a ha u)
    have hs := hRS u.val (A u).val hgerm
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ V
    · let x : U := e.symm ⟨y, hy⟩
      have he : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
      have hactual : (Q.toLinearMap (A u).val).val (e x).val =
          (B ⟨P.toLinearMap u.val, hPP u⟩).val.val (e x).val := by
        have hQvalue : (Q.toLinearMap (A u).val).val (e x).val =
            d (e x).val ((A u).val.val (e x).val) +
              (S.toLinearMap (A u).val).val (e x).val :=
          congrArg (fun T ↦ (T (A u).val).val (e x).val) hQ
        have hPvalue : (P.toLinearMap u.val).val x.val =
            c x.val (u.val.val x.val) + (R.toLinearMap u.val).val x.val :=
          congrArg (fun T ↦ (T u.val).val x.val) hP
        rw [hQvalue, hvalue F H b hb ⟨P.toLinearMap u.val, hPP u⟩ x]
        rw [hPvalue, hvalue E G a ha u x, hcd, hs]
        exact ((b x).map_add (c x.val (u.val.val x.val))
          ((R.toLinearMap u.val).val x.val)).symm
      exact (congrArg (fun z ↦ (Q.toLinearMap (A u).val).val z =
        (B ⟨P.toLinearMap u.val, hPP u⟩).val.val z) he).mp hactual
    · have hyL : y ∉ L := fun h ↦ hy (hLV h)
      exact (hQQ (A u) y hyL).trans ((B ⟨P.toLinearMap u.val, hPP u⟩).property y hyL).symm
  exact PseudodifferentialOperator.index_eq_of_supported_intertwining
    E F G H h k h' k' μ ν P Q hPe hQe K L hK hL hPP hPR hQS
    hkerP hkerQ hkerR hkerS A B hA hB hPQ

end AtiyahSinger
