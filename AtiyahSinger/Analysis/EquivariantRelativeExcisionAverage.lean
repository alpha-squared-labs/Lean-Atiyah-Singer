/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantOpenExtensionIndex
public import AtiyahSinger.Analysis.EquivariantRelativeOperatorAverage
public import AtiyahSinger.Analysis.EquivariantSupportedOpenSectionTransport

/-!
# Relative equivariant index comparison after actual averaging

Public module ID: M0561.

A prescribed pair of relative operators need not initially be equivariant.
Their fixed principal classes and equivariant exterior multipliers allow Haar
averaging while retaining the exact supported germ transport. The resulting
full representation-valued indices agree by the original open comparison.
All four operators, both supports, bundle maps, pairings and measures remain
those supplied in the statement; symbol realization is a separate input.

This is the averaged relative comparison used in SG III.13.4 and the
Atiyah--Singer excision argument, retaining complete kernel and cokernel actions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace Filter
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (E' F' : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
  (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ E'.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := E'.rank)
    (fun x ↦ (a x).toLinearMap))
  (b : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F'.Fiber)) x)
  (hb : IsSmoothBundleMap (n := n) (r := F.rank) (q := F'.rank)
    (fun x ↦ (b x).toLinearMap))
  [hC' : CompactSpace N] [MeasurableSpace N] [hB' : BorelSpace N]
  (ν : Measure N) [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hN hT hT' hSC hSC' hC' hB' hν hK hL hKU hLV hKL ha hb

variable [hC : CompactSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (c : ∀ x, E.Fiber x →ₗ[ℂ] F.Fiber x)
  (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank) c)
  (d : ∀ y, E'.Fiber y →ₗ[ℂ] F'.Fiber y)
  (hd : IsSmoothBundleMap (n := n) (r := E'.rank) (q := F'.rank) d)
  (hcd : ∀ (x : U) (v : E.Fiber x.val), d (e x).val (a x v) = b x (c x.val v))

include hC hB hμ hcd

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (τE : letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
    EquivariantStructure G E'.Fiber)
  (τF : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    EquivariantStructure G F'.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  (hτE : τE.IsSmooth (n := n) (r := E'.rank) IG)
  (hτF : τF.IsSmooth (n := n) (r := F'.rank) IG)

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

set_option maxHeartbeats 1800000 in
-- Retain four dependent section operators, the original open maps and both full index types.
/-- The specified relative open extension gives equal full indices for the averaged operators. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_of_averaged_openExtension
    [MulAction G U] [ContinuousSMul G U]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (he : ∀ (g : G) (x : U), (e (g • x)).val = g • (e x).val)
    (P R : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0)
    (Q S : PseudodifferentialOperator (n := n) (r := E'.rank) (q := F'.rank)
      E'.Fiber F'.Fiber ν 0)
    (hPfixed : ∀ g : G,
      equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF 0 g
        P.principalSymbol = P.principalSymbol)
    (hQfixed : ∀ g : G,
      equivariantPrincipalSymbolRepresentation IG τE τF hτE hτF 0 g
        Q.principalSymbol = Q.principalSymbol)
    (hcg : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (x : M) (v : E.Fiber x),
        c (g • x) (σE.linearMap g x v) = σF.linearMap g x (c x v))
    (hdg : letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      ∀ (g : G) (y : N) (v : E'.Fiber y),
        d (g • y) (τE.linearMap g y v) = τF.linearMap g y (d y v))
    (hag : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      ∀ (g : G) (x : U) (v : E.Fiber x.val),
        (⟨(e (g • x)).val, a (g • x)
          (cast (congrArg E.Fiber (hU g x).symm) (σE.linearMap g x.val v))⟩ :
            TotalSpace Unit E'.Fiber) =
          ⟨g • (e x).val, τE.linearMap g (e x).val (a x v)⟩)
    (hbg : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      ∀ (g : G) (x : U) (v : F.Fiber x.val),
        (⟨(e (g • x)).val, b (g • x)
          (cast (congrArg F.Fiber (hU g x).symm) (σF.linearMap g x.val v))⟩ :
            TotalSpace Unit F'.Fiber) =
          ⟨g • (e x).val, τF.linearMap g (e x).val (b x v)⟩)
    (hP : P.toLinearMap = smoothSectionMap c hc + R.toLinearMap)
    (hQ : Q.toLinearMap = smoothSectionMap d hd + S.toLinearMap)
    (hR : HasSectionOperatorSupport K R.toLinearMap)
    (hS : HasSectionOperatorSupport L S.toLinearMap)
    (hPe : P.IsElliptic) (hQe : Q.IsElliptic)
    (hcext : ∀ x, x ∉ K → Function.Bijective (c x))
    (hdext : ∀ y, y ∉ L → Function.Bijective (d y))
    (hRS : ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := E'.rank) E'.Fiber),
      (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) →
      ∀ x : U, (S.toLinearMap v).val (e x).val = b x ((R.toLinearMap u).val x.val))
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (h' : SmoothHermitianMetric (n := n) (r := E'.rank) E'.Fiber)
    (k' : SmoothHermitianMetric (n := n) (r := F'.rank) F'.Fiber)
    (hha : ∀ (x : U), x.val ∈ K → ∀ v w : E.Fiber x.val,
      h'.pairing (e x).val (a x v) (a x w) = h.pairing x.val v w)
    (hkb : ∀ (x : U), x.val ∈ K → ∀ v w : F.Fiber x.val,
      k'.pairing (e x).val (b x v) (b x w) = k.pairing x.val v w)
    (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      ∀ (g : G) (x : M) (u v : E.Fiber x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
    (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (x : M) (u v : F.Fiber x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
    (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
    (hKInvariant : ∀ (g : G) (x : M), g • x ∈ K ↔ x ∈ K)
    (hμν : Measure.map e ((μ.comap (Subtype.val : U → M)).restrict
        ((Subtype.val : U → M) ⁻¹' K)) =
      (ν.comap (Subtype.val : V → N)).restrict ((Subtype.val : V → N) ⁻¹' L)) :
    ∃ (hPbar : (P.average IG σE σF hσE hσF).IsElliptic)
      (hQbar : (Q.average IG τE τF hτE hτF).IsElliptic),
      (P.average IG σE σF hσE hσF).smoothEquivariantAnalyticIndex IG σE σF hσE hσF
        (P.isEquivariant_average IG σE σF hσE hσF) hPbar =
      (Q.average IG τE τF hτE hτF).smoothEquivariantAnalyticIndex IG τE τF hτE hτF
        (Q.isEquivariant_average IG τE τF hτE hτF) hQbar := by
  classical
  let Pbar := P.average IG σE σF hσE hσF
  let Rbar := R.average IG σE σF hσE hσF
  let Qbar := Q.average IG τE τF hτE hτF
  let Sbar := S.average IG τE τF hτE hτF
  -- The specified fixed principal classes preserve actual ellipticity after averaging.
  have hPbarClass : Pbar.principalSymbol = P.principalSymbol :=
    P.principalSymbol_average_of_fixed IG σE σF hσE hσF hPfixed
  have hQbarClass : Qbar.principalSymbol = Q.principalSymbol :=
    Q.principalSymbol_average_of_fixed IG τE τF hτE hτF hQfixed
  have hPbar : Pbar.IsElliptic :=
    (Pbar.isElliptic_iff_of_principalSymbol_eq_operator P hPbarClass).mpr hPe
  have hQbar : Qbar.IsElliptic :=
    (Qbar.isElliptic_iff_of_principalSymbol_eq_operator Q hQbarClass).mpr hQe
  -- The same compact target control is invariant under the transported base action.
  have hLimage (g : G) : (fun y : N ↦ g • y) '' L ⊆ L := by
    rintro _ ⟨y, hy, rfl⟩
    let x : U := e.symm ⟨y, hLV hy⟩
    have hxvalue : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hLV hy⟩)
    have hxK : x.val ∈ K := by
      have hx : x ∈ e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) := by
        change (e x).val ∈ L
        rw [hxvalue]
        exact hy
      rw [hKL] at hx
      exact hx
    have hgxK : (g • x : U).val ∈ K := by
      rw [hU]
      exact (hKInvariant g x.val).mpr hxK
    have hgx : g • x ∈ e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) := by
      rw [hKL]
      exact hgxK
    change (e (g • x)).val ∈ L at hgx
    rw [he, hxvalue] at hgx
    exact hgx
  have hKimage (g : G) : (fun x : M ↦ g • x) '' K ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hKInvariant g x).mpr hx
  have hRbar : HasSectionOperatorSupport K Rbar.toLinearMap :=
    R.hasSectionOperatorSupport_average IG σE σF hσE hσF K hK hKimage hR
  have hSbar : HasSectionOperatorSupport L Sbar.toLinearMap :=
    S.hasSectionOperatorSupport_average IG τE τF hτE hτF L hL hLimage hS
  -- Both decompositions retain the same exterior maps, with precisely the averaged corrections.
  have hPdecomp : Pbar.toLinearMap = smoothSectionMap c hc + Rbar.toLinearMap :=
    P.average_toLinearMap_of_equivariant_multiplier IG σE σF hσE hσF R c hc hcg hP
  have hQdecomp : Qbar.toLinearMap = smoothSectionMap d hd + Sbar.toLinearMap :=
    Q.average_toLinearMap_of_equivariant_multiplier IG τE τF hτE hτF S d hd hdg hQ
  have hKUi (g : G) (x : U) (hx : x.val ∈ K) : (g • x : U).val ∈ K := by
    rw [hU]
    exact (hKInvariant g x.val).mpr hx
  have hRSbar (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := E'.rank) E'.Fiber)
      (huv : ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) :
      ∀ x : U, (Sbar.toLinearMap v).val (e x).val =
        b x ((Rbar.toLinearMap u).val x.val) :=
    PseudodifferentialOperator.average_intertwines_of_germ IG
      (Subtype.val : U → M) (fun x : U ↦ (e x).val) hU he
      ((Subtype.val : U → M) ⁻¹' K) hKUi E F E' F' σE σF τE τF
      hσE hσF hτE hτF a b hag hbg R S hRS u v huv
  -- The geometric squares determine both actual supported section action comparisons.
  have hAg := supportedSmoothSectionOpenEquiv_intertwines IG E E' U V e hU he
    K L hK hL hKU hLV hKL hKInvariant a ha σE τE hσE hτE hag
  have hBg := supportedSmoothSectionOpenEquiv_intertwines IG F F' U V e hU he
    K L hK hL hKU hLV hKL hKInvariant b hb σF τF hσF hτF hbg
  -- Apply the original full kernel/cokernel comparison with these exact averaged operators.
  refine ⟨hPbar, hQbar, ?_⟩
  exact PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_of_openExtension
    E F E' F' U V e K L hK hL hKU hLV hKL a ha b hb ν μ c hc d hd hcd
    IG σE σF τE τF hσE hσF hτE hτF Pbar Rbar Qbar Sbar
    (P.isEquivariant_average IG σE σF hσE hσF)
    (Q.isEquivariant_average IG τE τF hτE hτF)
    hPdecomp hQdecomp hRbar hSbar hPbar hQbar hcext hdext hRSbar
    h k h' k' hha hkb hInvariant kInvariant hμInvariant hKInvariant hAg hBg hμν

end AtiyahSinger
