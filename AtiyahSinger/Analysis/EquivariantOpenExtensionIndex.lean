/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Analysis.EquivariantSupportedOperatorComparison
public import AtiyahSinger.Analysis.OpenExtensionIndex

import all AtiyahSinger.Analysis.OpenExtensionIndex

/-!
# Full equivariant index of exact open extensions

Public module ID: M0543.

An exterior invertible bundle map plus a two-sided supported correction gives
support bounds for both entire kernels. The prescribed open section maps and
matching pairings then identify the full equivariant smooth indices. The actual
adjoint action is obtained from the original invariant metrics and density.
This is the analytic open-extension comparison; construction of a common relative
symbol representative remains a separate part of equivariant K-theory excision.

Source: Atiyah--Singer I, section 4, and SG III.13.4. All equalities concern the
original full representation ring, including the original quotient cokernels.
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

set_option maxHeartbeats 2200000 in
-- Preserve the actual open maps, both supported transports and all four bundle actions.
/-- An equivariant exact open extension preserves the full representation-valued index. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_of_openExtension
    (P R : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0)
    (Q S : PseudodifferentialOperator (n := n) (r := E'.rank) (q := F'.rank)
      E'.Fiber F'.Fiber ν 0)
    (hPg : P.IsEquivariant IG σE σF hσE hσF)
    (hQg : Q.IsEquivariant IG τE τF hτE hτF)
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
    (hAg :
      let A := supportedSmoothSectionOpenEquiv E E' U V e K L
        hK.isClosed hL.isClosed hKU hLV hKL a ha
      ∀ (g : G) (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
        (hu : σE.smoothSectionRepresentation IG hσE g u.val ∈
          supportedSmoothSections (n := n) (r := E.rank) E.Fiber K),
        (A ⟨σE.smoothSectionRepresentation IG hσE g u.val, hu⟩).val =
          τE.smoothSectionRepresentation IG hτE g (A u).val)
    (hBg :
      let B := supportedSmoothSectionOpenEquiv F F' U V e K L
        hK.isClosed hL.isClosed hKU hLV hKL b hb
      ∀ (g : G) (u : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K)
        (hu : σF.smoothSectionRepresentation IG hσF g u.val ∈
          supportedSmoothSections (n := n) (r := F.rank) F.Fiber K),
        (B ⟨σF.smoothSectionRepresentation IG hσF g u.val, hu⟩).val =
          τF.smoothSectionRepresentation IG hτF g (B u).val)
    (hμν : Measure.map e ((μ.comap (Subtype.val : U → M)).restrict
        ((Subtype.val : U → M) ⁻¹' K)) =
      (ν.comap (Subtype.val : V → N)).restrict ((Subtype.val : V → N) ⁻¹' L)) :
    P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hPe =
      Q.smoothEquivariantAnalyticIndex IG τE τF hτE hτF hQg hQe := by
  classical
  -- Both full kernels and the supported actions follow from the exterior isomorphisms.
  obtain ⟨hPP, hPR, hkerP, hkerR⟩ := support_and_kernel_of_supported_perturbation
    P R c hc hP K hK.isClosed hR hcext h k
  obtain ⟨hQQ, hQS, hkerQ, hkerS⟩ := support_and_kernel_of_supported_perturbation
    Q S d hd hQ L hL.isClosed hS hdext h' k'
  let A := supportedSmoothSectionOpenEquiv E E' U V e K L
    hK.isClosed hL.isClosed hKU hLV hKL a ha
  let B := supportedSmoothSectionOpenEquiv F F' U V e K L
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
    SmoothHermitianMetric.sectionPairing_openEquiv E E' U V e K L hK hL hKU hLV hKL
      a ha h h' μ ν hha hμν u v
  have hB (u v : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K) :
      k'.sectionPairing ν (B u).val (B v).val = k.sectionPairing μ u.val v.val :=
    SmoothHermitianMetric.sectionPairing_openEquiv F F' U V e K L hK hL hKU hLV hKL
      b hb k k' μ ν hkb hμν u v
  -- The prescribed germ equation identifies the same supported operator outputs.
  have hPQ (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) :
      Q.toLinearMap (A u).val = (B ⟨P.toLinearMap u.val, hPP u⟩).val := by
    have hgerm : ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        (A u).val.val (e x).val = a x (u.val.val x.val) :=
      Filter.Eventually.of_forall (hvalue E E' a ha u)
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
        rw [hQvalue, hvalue F F' b hb ⟨P.toLinearMap u.val, hPP u⟩ x]
        rw [hPvalue, hvalue E E' a ha u x, hcd, hs]
        exact ((b x).map_add (c x.val (u.val.val x.val))
          ((R.toLinearMap u.val).val x.val)).symm
      exact (congrArg (fun z ↦ (Q.toLinearMap (A u).val).val z =
        (B ⟨P.toLinearMap u.val, hPP u⟩).val.val z) he).mp hactual
    · have hyL : y ∉ L := fun h ↦ hy (hLV h)
      exact (hQQ (A u) y hyL).trans ((B ⟨P.toLinearMap u.val, hPP u⟩).property y hyL).symm
  -- Invariant control preserves each actual supported section space.
  have action_support (D : SmoothFiniteComplexBundle (n := n) M)
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
        EquivariantStructure G D.Fiber)
      (hσ : σ.IsSmooth (n := n) (r := D.rank) IG)
      (g : G) (u : supportedSmoothSections (n := n) (r := D.rank) D.Fiber K) :
      σ.smoothSectionRepresentation IG hσ g u.val ∈
        supportedSmoothSections (n := n) (r := D.rank) D.Fiber K := by
    have hu : closure {x : M | u.val.val x ≠ 0} ⊆ K := by
      apply closure_minimal ?_ hK.isClosed
      intro x hx
      by_contra hxK
      exact hx (u.property x hxK)
    have haction : closure {x : M | σ.sectionLinearMap g u.val.val x ≠ 0} ⊆ K := by
      rw [σ.closure_support_sectionLinearMap]
      rintro _ ⟨x, hx, rfl⟩
      exact (hKInvariant g x).mpr (hu hx)
    intro x hx
    by_contra hne
    exact hx (haction (subset_closure hne))
  -- The given invariant source geometry makes its actual adjoint equivariant.
  have hRg (g : G) (v : (P.metricFormalAdjoint h k).toLinearMap.ker) :
      σF.smoothSectionRepresentation IG hσF g v.val ∈
        (P.metricFormalAdjoint h k).toLinearMap.ker := by
    have hadj := P.isEquivariant_metricFormalAdjoint IG σE σF hσE hσF
      h k hInvariant kInvariant hμInvariant hPg
    have heq := congrArg (fun T ↦ T v.val) (hadj g)
    change (P.metricFormalAdjoint h k).toLinearMap
      (σF.smoothSectionRepresentation IG hσF g v.val) = 0
    change (P.metricFormalAdjoint h k).toLinearMap
      (σF.smoothSectionRepresentation IG hσF g v.val) =
        σE.smoothSectionRepresentation IG hσE g
          ((P.metricFormalAdjoint h k).toLinearMap v.val) at heq
    rw [heq, v.property, map_zero]
  -- Use the same supports, pairings and actual open maps in the full index comparison.
  exact PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_of_supported_intertwining
    E F E' F' h k h' k' μ ν IG σE σF τE τF hσE hσF hτE hτF
    P Q hPe hQe hPg hQg hRg K L hK hL hPP hPR hQS hkerP hkerQ hkerR hkerS
    A B hA hB (action_support E σE hσE) (action_support F σF hσF)
    (fun g u ↦ hAg g u _) (fun g u ↦ hBg g u _) hPQ

end AtiyahSinger
