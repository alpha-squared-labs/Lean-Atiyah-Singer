/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClopenPseudodifferential
public import AtiyahSinger.Analysis.EquivariantOpenSymbolRestriction
public import AtiyahSinger.Analysis.EquivariantOpenSymbolTransport
public import AtiyahSinger.Analysis.EquivariantRelativeExcisionAverage
public import AtiyahSinger.Analysis.EquivariantSmoothSymbolIndex
public import AtiyahSinger.Analysis.RelativeCompactRealization
public import AtiyahSinger.Analysis.SmoothBundleMapOperator

/-!
# Full relative analytic comparison for one prescribed finite quantization

Public module ID: M0560.

The same source correction is realized on the two compact environments.
Its original cotangent and fiber squares fix both principal classes.
Averaging retains the exterior multipliers and the supported germ comparison;
the actual kernels and adjoint kernels therefore give equal full indices.
The transported raw symbol keeps the smaller specified zero-section control.
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
  (c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
  (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank) (fun x ↦ (c x).toLinearMap))
  (d : ∀ y, E'.Fiber y →L[ℂ] F'.Fiber y)
  (hd : IsSmoothBundleMap (n := n) (r := E'.rank) (q := F'.rank) (fun y ↦ (d y).toLinearMap))
  (hcd : ∀ (x : U) (v : E.Fiber x.val), d (e x).val (a x v) = b x (c x.val v))

include hC hB hμ hc hd hcd

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- Actual source and target operators, their averages and smaller symbol controls share witnesses.
/-- Relative realization and averaging compare the full indices of the original symbols. -/
theorem exists_equivariant_relative_analytic_comparison
    [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (he : ∀ (g : G) (x : U), (e (g • x)).val = g • (e x).val)
    (hCot : letI := smoothCotangentMulAction (n := n) (G := G) (M := U) IG
      letI := smoothCotangentMulAction (n := n) (G := G) (M := N) IG
      ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := U)),
        cotangentOpenInclusion V (cotangentDiffeomorph e (g • z)) =
          g • cotangentOpenInclusion V (cotangentDiffeomorph e z))
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
    (s : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (hs : IsEllipticGlobalSymbol E.Fiber F.Fiber s.val)
    (hsg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
    (hsext : ∀ x ∉ K, ∀ ξ v, s.val x ξ v = c x v)
    (hcext : ∀ x ∉ K, Function.Bijective (c x))
    (hdext : ∀ y ∉ L, Function.Bijective (d y))
    (g₀ : SmoothCotangentMetric (n := n) (M := M)) (k₀ : ℕ)
    (T : Fin k₀ → PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (hpieces : ∀ j, (T j).chart.symm ''
      (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ K)
    (hprincipal : ∀ x ξ, 1 ≤ g₀.length x ξ →
      (∑ j, (T j).globalSymbol).val x ξ + c x = s.val x ξ)
    (hcorrection : HasSectionOperatorSupport K (∑ j, (T j).toLinearMap))
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
    ∃ t : homogeneousGlobalSymbolSpace (n := n) (r := E'.rank) (q := F'.rank)
        E'.Fiber F'.Fiber 0,
      ∃ ht : IsEllipticGlobalSymbol E'.Fiber F'.Fiber t.val,
        ∃ htg : ∀ (g : G) (y : N) (η : CotangentFiber (n := n) y), η ≠ 0 →
            equivariantGlobalSymbolLinearMap IG τE τF g t.val y η = t.val y η,
          equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hs hsg =
            equivariantHomogeneousAnalyticIndex IG τE τF hτE hτF t ht htg ∧
          (∀ (x : U) (ξ : CotangentFiber (n := n) x.val) (v : E.Fiber x.val),
            t.val (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (a x v) =
              b x (s.val x.val ξ v)) ∧
          (∀ y ∉ L, ∀ η v, t.val y η v = d y v) ∧
          letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
          letI := smoothCotangentMulAction (n := n) (G := G) (M := N) IG
          letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) IG
          letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
            ContMDiffSMul.continuousSMul (I := IG)
              (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
          ∃ B : CompactSupportTriple
              ((cotangentProjection (n := n) (M := N) : _ → N) *ᵖ E'.Fiber)
              ((cotangentProjection (n := n) (M := N) : _ → N) *ᵖ F'.Fiber),
            B.control = cotangentZeroSection '' L ∧
            (∀ (z : (B.controlᶜ : Set (CotangentTotalSpace (n := n) (M := N))))
              (v : E'.Fiber z.val.proj),
              B.boundary.linearEquiv z v = t.val z.val.proj z.val.snd v) ∧
            B.IsEquivariant (τE.pullback cotangentProjection (fun _ _ ↦ rfl))
              (τF.pullback cotangentProjection (fun _ _ ↦ rfl)) := by
  classical
  obtain ⟨A⟩ := nonempty_quantizationPresentation
    (n := n) (r := E.rank) (q := F.rank) (E := E.Fiber) (F := F.Fiber)
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := E'.rank) (q := F'.rank) (E := E'.Fiber) (F := F'.Fiber)
  -- The compact source realization contains exactly the specified finite correction.
  obtain ⟨P, hPe, hPact, hPclass⟩ := exists_relative_compact_realization_of_pieces E F μ
    s hs c hc g₀ k₀ T hprincipal A
  obtain ⟨Q, t, ht, hQe, hQclass, hQsupport, hQact, hst, htext,
      B, hBcontrol, hBboundary, _hBclass⟩ :=
    exists_relative_elliptic_openExtension_of_pieces E F E' F' U V e K L
      hK hL hKU hLV hKL a ha b hb ν s hs c hc
      (fun x hx ξ ↦ ContinuousLinearMap.ext (hsext x hx ξ))
      d hd hcd hdext g₀ k₀ T hpieces hprincipal R
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) ((i : U → M) *ᵖ E.Fiber)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((i : U → M) *ᵖ F.Fiber)
  let σEU := σE.modelPullback i hU
  let σFU := σF.modelPullback i hU
  -- Model pullback transports precisely the original vectors through the supplied base equality.
  have hpull (C : SmoothFiniteComplexBundle (n := n) M)
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin C.rank)) C.Fiber
        EquivariantStructure G C.Fiber)
      (g : G) (x : U) (v : C.Fiber x.val) :
      letI := modelTopology (EuclideanSpace ℂ (Fin C.rank)) C.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin C.rank)) ((i : U → M) *ᵖ C.Fiber)
      (σ.modelPullback i hU).linearMap g x v =
        cast (congrArg C.Fiber (hU g x).symm) (σ.linearMap g x.val v) := by
    let := modelTopology (EuclideanSpace ℂ (Fin C.rank)) C.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin C.rank)) ((i : U → M) *ᵖ C.Fiber)
    have hcast {y z : M} (hyz : y = z) (w : C.Fiber z) :
        (⟨y, cast (congrArg C.Fiber hyz.symm) w⟩ : TotalSpace Unit C.Fiber) = ⟨z, w⟩ := by
      subst z
      rfl
    exact TotalSpace.mk_injective (i (g • x))
      ((σ.modelPullback_lift i hU g x v).trans (hcast (hU g x) _).symm)
  have haU (g : G) (x : U) (v : E.Fiber x.val) :
      (⟨(e (g • x)).val, a (g • x) (σEU.linearMap g x v)⟩ : TotalSpace Unit E'.Fiber) =
        ⟨g • (e x).val, τE.linearMap g (e x).val (a x v)⟩ := by
    rw [hpull]
    exact hag g x v
  have hbU (g : G) (x : U) (v : F.Fiber x.val) :
      (⟨(e (g • x)).val, b (g • x) (σFU.linearMap g x v)⟩ : TotalSpace Unit F'.Fiber) =
        ⟨g • (e x).val, τF.linearMap g (e x).val (b x v)⟩ := by
    rw [hpull]
    exact hbg g x v
  have hsU := equivariantGlobalSymbolLinearMap_eq_restrictOpen IG E F σE σF U hU s.val hsg
  have htg := equivariantGlobalSymbolLinearMap_eq_of_openTransport IG
    (E.restrictOpen U) (F.restrictOpen U) E' F' σEU σFU τE τF V e he hCot a b haU hbU
    (fun x ξ ↦ s.val x.val ξ) t.val hsU hst (fun y ↦ (d y).toLinearMap) hdg
    (fun y hy η v ↦ congrArg (fun C ↦ C v) (htext y (fun hyL ↦ hy (hLV hyL)) η))
  have hPfixed (g : G) : equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF 0 g
      P.principalSymbol = P.principalSymbol := by
    rw [hPclass]
    exact (A.equivariant_regularizedSymbol_class_eq_iff IG σE σF hσE hσF A 0 s s g).mpr
      (hsg g)
  have hQfixed (g : G) : equivariantPrincipalSymbolRepresentation IG τE τF hτE hτF 0 g
      Q.principalSymbol = Q.principalSymbol := by
    rw [hQclass]
    exact (R.equivariant_regularizedSymbol_class_eq_iff IG τE τF hτE hτF R 0 t t g).mpr
      (htg g)
  -- Both actual correction operators keep the specified support and matching germ.
  let RP : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0 :=
    ⟨P.toLinearMap - smoothSectionMap (fun x ↦ (c x).toLinearMap) hc,
      (pseudodifferentialSpace E.Fiber F.Fiber μ 0).sub_mem P.isPseudodifferentialOperator
        (isPseudodifferentialOperator_smoothSectionMap (fun x ↦ (c x).toLinearMap) hc)⟩
  let RQ : PseudodifferentialOperator (n := n) (r := E'.rank) (q := F'.rank)
      E'.Fiber F'.Fiber ν 0 :=
    ⟨Q.toLinearMap - smoothSectionMap (fun y ↦ (d y).toLinearMap) hd,
      (pseudodifferentialSpace E'.Fiber F'.Fiber ν 0).sub_mem Q.isPseudodifferentialOperator
        (isPseudodifferentialOperator_smoothSectionMap (fun y ↦ (d y).toLinearMap) hd)⟩
  have hRP : RP.toLinearMap = ∑ j, (T j).toLinearMap := by
    change P.toLinearMap - smoothSectionMap (fun x ↦ (c x).toLinearMap) hc = _
    rw [hPact, add_sub_cancel_left]
  obtain ⟨hPbar, hQbar, hindex⟩ :=
    PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_of_averaged_openExtension
      E F E' F' U V e K L hK hL hKU hLV hKL a ha b hb ν μ
      (fun x ↦ (c x).toLinearMap) hc (fun y ↦ (d y).toLinearMap) hd hcd
      IG σE σF τE τF hσE hσF hτE hτF hU he P RP Q RQ hPfixed hQfixed hcg hdg hag hbg
      (by change _ = _ + (_ - _); abel) (by change _ = _ + (_ - _); abel)
      (by rw [hRP]; exact hcorrection) hQsupport hPe hQe hcext hdext
      (by intro u v huv x; rw [hRP]; exact hQact u v huv x)
      h k h' k' hha hkb hInvariant kInvariant hμInvariant hKInvariant hμν
  have hindexSymbols : equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hs hsg =
      equivariantHomogeneousAnalyticIndex IG τE τF hτE hτF t ht htg := by
    calc
      _ = (P.average IG σE σF hσE hσF).smoothEquivariantAnalyticIndex
          IG σE σF hσE hσF (P.isEquivariant_average IG σE σF hσE hσF) hPbar :=
        equivariantHomogeneousAnalyticIndex_eq_smooth IG σE σF hσE hσF s hs hsg μ A
          (P.average IG σE σF hσE hσF) (P.isEquivariant_average IG σE σF hσE hσF) hPbar
          ((P.principalSymbol_average_of_fixed IG σE σF hσE hσF hPfixed).trans hPclass)
      _ = _ := hindex
      _ = _ := (equivariantHomogeneousAnalyticIndex_eq_smooth IG τE τF hτE hτF t ht htg ν R
        (Q.average IG τE τF hτE hτF) (Q.isEquivariant_average IG τE τF hτE hτF) hQbar
        ((Q.principalSymbol_average_of_fixed IG τE τF hτE hτF hQfixed).trans hQclass)).symm
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := smoothCotangentMulAction (n := n) (G := G) (M := N) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let Y := CotangentTotalSpace (n := n) (M := N)
  -- The exact target control is invariant because the specified diffeomorphism matches K and L.
  have hLforward (g : G) (y : N) (hy : y ∈ L) : g • y ∈ L := by
    let x := e.symm ⟨y, hLV hy⟩
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
    rwa [he, hxvalue] at hgx
  have hLi (g : G) (y : N) : g • y ∈ L ↔ y ∈ L :=
    ⟨fun hy ↦ by simpa only [inv_smul_smul] using hLforward g⁻¹ (g • y) hy,
      hLforward g y⟩
  have hcontrol (g : G) (z : Y) : g • z ∈ B.control ↔ z ∈ B.control := by
    have hforward (g : G) (z : Y) : z ∈ B.control → g • z ∈ B.control := by
      rw [hBcontrol]
      rintro ⟨x, hx, rfl⟩
      refine ⟨g • x, (hLi g x).mpr hx, ?_⟩
      change (⟨g • x, 0⟩ : Y) = ⟨g • x, (0 : CotangentFiber (n := n) x).comp _⟩
      rw [ContinuousLinearMap.zero_comp]
    constructor
    · intro hz
      simpa only [inv_smul_smul] using hforward g⁻¹ (g • z) hz
    · exact hforward g z
  have hBeq : B.IsEquivariant (τE.pullback cotangentProjection (fun _ _ ↦ rfl))
      (τF.pullback cotangentProjection (fun _ _ ↦ rfl)) := by
    refine ⟨hcontrol, ?_⟩
    intro g z v
    let gz : (B.controlᶜ : Set Y) :=
      ⟨g • z.val, fun hz ↦ z.property ((hcontrol g z.val).mp hz)⟩
    change B.boundary.linearEquiv gz (τE.linearMap g z.val.proj v) =
      τF.linearMap g z.val.proj (B.boundary.linearEquiv z v)
    rw [hBboundary, hBboundary]
    by_cases hz0 : z.val.snd = 0
    · have hzL : z.val.proj ∉ L := by
        intro hzL
        have hzmem : z.val ∈ cotangentZeroSection '' L :=
          ⟨z.val.proj, hzL, TotalSpace.ext rfl (heq_of_eq hz0.symm)⟩
        exact z.property (by simpa only [hBcontrol] using hzmem)
      have hgzL : (g • z.val).proj ∉ L := (hLi g z.val.proj).not.mpr hzL
      rw [htext _ hgzL, htext _ hzL]
      exact hdg g z.val.proj v
    · exact (equivariantGlobalSymbolLinearMap_eq_iff IG τE τF t.val).mp htg
        g z.val.proj z.val.snd hz0 v
  exact ⟨t, ht, htg, hindexSymbols, hst,
    (fun y hy η v ↦ congrArg (fun C ↦ C v) (htext y hy η)),
    B, hBcontrol, hBboundary, hBeq⟩

end AtiyahSinger
