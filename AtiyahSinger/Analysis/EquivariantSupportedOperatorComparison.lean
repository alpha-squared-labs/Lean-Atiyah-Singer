/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothEquivariantIndex
public import AtiyahSinger.Analysis.SupportedOperatorComparison

/-!
# Equivariant comparison of supported elliptic operators

Public module ID: M0584.

The same pairing-preserving supported section maps identify the full kernels
and, through the actual metric-adjoint kernels, the original quotient cokernels.
If these maps intertwine the original actions, their indices agree in the full
representation ring. The compact environments, bundle ranks and operator orders
may differ. This conditional comparison is the analytic step of equivariant
excision; support localization is assumed, and relative representatives are
not constructed by this theorem.

Source: Atiyah--Singer I, the excision axiom B1, and SG III.13.4. The passage
through the actual quotient cokernels keeps the representation action instead
of applying the dimension homomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  [MeasurableSpace M] [MeasurableSpace N] [BorelSpace M] [BorelSpace N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (E' F' : SmoothFiniteComplexBundle (n := m) N)
  (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
  (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
  (h' : SmoothHermitianMetric (n := m) (r := E'.rank) E'.Fiber)
  (k' : SmoothHermitianMetric (n := m) (r := F'.rank) F'.Fiber)
  (μ : Measure M) (ν : Measure N)
  [hμ : IsSmoothPositiveMeasure (n := n) μ] [hν : IsSmoothPositiveMeasure (n := m) ν]

include hM hN hT hT' hSC hSC' hμ hν

variable [CompactSpace M] [CompactSpace N]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G N]
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
  (hτE : τE.IsSmooth (n := m) (r := E'.rank) IG)
  (hτF : τF.IsSmooth (n := m) (r := F'.rank) IG)

set_option maxHeartbeats 2000000 in
-- Retain the exact supported maps and all original quotient actions.
/-- Equivariant supported identifications preserve the full smooth analytic index. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_of_supported_intertwining
    {a b : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ a)
    (Q : PseudodifferentialOperator (n := m) (r := E'.rank) (q := F'.rank)
      E'.Fiber F'.Fiber ν b)
    (hPe : P.IsElliptic) (hQe : Q.IsElliptic)
    (hPg : P.IsEquivariant IG σE σF hσE hσF)
    (hQg : Q.IsEquivariant IG τE τF hτE hτF)
    (hRg : ∀ (g : G) (v : (P.metricFormalAdjoint h k).toLinearMap.ker),
      σF.smoothSectionRepresentation IG hσF g v.val ∈
        (P.metricFormalAdjoint h k).toLinearMap.ker)
    (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
    (hP : ∀ u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K, P.toLinearMap u.val ∈
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber K)
    (hR : ∀ v : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K,
      (P.metricFormalAdjoint h k).toLinearMap v.val ∈
        supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
    (hS : ∀ v : supportedSmoothSections (n := m) (r := F'.rank) F'.Fiber L,
      (Q.metricFormalAdjoint h' k').toLinearMap v.val ∈
        supportedSmoothSections (n := m) (r := E'.rank) E'.Fiber L)
    (hkerP : P.toLinearMap.ker ≤ supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
    (hkerQ : Q.toLinearMap.ker ≤ supportedSmoothSections (n := m) (r := E'.rank) E'.Fiber L)
    (hkerR : (P.metricFormalAdjoint h k).toLinearMap.ker ≤
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber K)
    (hkerS : (Q.metricFormalAdjoint h' k').toLinearMap.ker ≤
      supportedSmoothSections (n := m) (r := F'.rank) F'.Fiber L)
    (A : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K ≃ₗ[ℂ]
      supportedSmoothSections (n := m) (r := E'.rank) E'.Fiber L)
    (B : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K ≃ₗ[ℂ]
      supportedSmoothSections (n := m) (r := F'.rank) F'.Fiber L)
    (hA : ∀ u v, h'.sectionPairing ν (A u).val (A v).val =
      h.sectionPairing μ u.val v.val)
    (hB : ∀ u v, k'.sectionPairing ν (B u).val (B v).val =
      k.sectionPairing μ u.val v.val)
    (hEK : ∀ (g : G) (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K),
      σE.smoothSectionRepresentation IG hσE g u.val ∈
        supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
    (hFK : ∀ (g : G) (u : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K),
      σF.smoothSectionRepresentation IG hσF g u.val ∈
        supportedSmoothSections (n := n) (r := F.rank) F.Fiber K)
    (hAg : ∀ (g : G) (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K),
      (A ⟨σE.smoothSectionRepresentation IG hσE g u.val, hEK g u⟩).val =
        τE.smoothSectionRepresentation IG hτE g (A u).val)
    (hBg : ∀ (g : G) (u : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K),
      (B ⟨σF.smoothSectionRepresentation IG hσF g u.val, hFK g u⟩).val =
        τF.smoothSectionRepresentation IG hτF g (B u).val)
    (hPQ : ∀ u, Q.toLinearMap (A u).val = (B ⟨P.toLinearMap u.val, hP u⟩).val) :
    P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hPe =
      Q.smoothEquivariantAnalyticIndex IG τE τF hτE hτF hQg hQe := by
  classical
  -- Restrict the actual supported maps, keeping their value formulas.
  have kerEquiv (X₁ : Type _) (Y₁ : Type _) (X₂ : Type _) (Y₂ : Type _)
      [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup Y₁] [Module ℂ Y₁]
      [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup Y₂] [Module ℂ Y₂]
      (p : X₁ →ₗ[ℂ] Y₁) (q : X₂ →ₗ[ℂ] Y₂)
      (s₁ : Submodule ℂ X₁) (t₁ : Submodule ℂ Y₁)
      (s₂ : Submodule ℂ X₂) (t₂ : Submodule ℂ Y₂)
      (hp : ∀ u : s₁, p u.val ∈ t₁) (hkp : p.ker ≤ s₁) (hkq : q.ker ≤ s₂)
      (a : s₁ ≃ₗ[ℂ] s₂) (b : t₁ ≃ₗ[ℂ] t₂)
      (hpq : ∀ u : s₁, q (a u).val = (b ⟨p u.val, hp u⟩).val) :
      ∃ e : p.ker ≃ₗ[ℂ] q.ker, ∀ u,
        (e u).val = (a ⟨u.val, hkp u.property⟩).val := by
    let f : p.ker →ₗ[ℂ] q.ker :=
      { toFun := fun u ↦ ⟨(a ⟨u.val, hkp u.property⟩).val, by
          rw [LinearMap.mem_ker, hpq]
          have hz : (⟨p u.val, hp ⟨u.val, hkp u.property⟩⟩ : t₁) = 0 :=
            Subtype.ext u.property
          rw [hz, map_zero]
          rfl⟩
        map_add' := by
          intro u v
          apply Subtype.ext
          exact congrArg (fun w : s₂ ↦ (w : X₂)) (a.map_add ⟨u.val, hkp u.property⟩
            ⟨v.val, hkp v.property⟩)
        map_smul' := by
          intro c u
          apply Subtype.ext
          exact congrArg (fun w : s₂ ↦ (w : X₂)) (a.map_smul c ⟨u.val, hkp u.property⟩) }
    have hf : Function.Bijective f := by
      constructor
      · intro u v huv
        apply Subtype.ext
        have he : a ⟨u.val, hkp u.property⟩ = a ⟨v.val, hkp v.property⟩ :=
          Subtype.ext (congrArg (fun w : q.ker ↦ (w : X₂)) huv)
        exact congrArg (fun w : s₁ ↦ (w : X₁)) (a.injective he)
      · intro v
        let u : s₁ := a.symm ⟨v.val, hkq v.property⟩
        have hau : a u = ⟨v.val, hkq v.property⟩ := a.apply_symm_apply _
        have hpu : p u.val = 0 := by
          have hz : b ⟨p u.val, hp u⟩ = 0 := by
            apply Subtype.ext
            exact (hpq u).symm.trans
              ((congrArg (fun w : s₂ ↦ q w.val) hau).trans v.property)
          exact congrArg (fun w : t₁ ↦ (w : Y₁))
            (b.injective (hz.trans b.map_zero.symm))
        refine ⟨⟨u.val, hpu⟩, ?_⟩
        apply Subtype.ext
        exact congrArg (fun w : s₂ ↦ (w : X₂)) hau
    exact ⟨LinearEquiv.ofBijective f hf, fun _ ↦ rfl⟩
  obtain ⟨e, he⟩ := kerEquiv _ _ _ _ P.toLinearMap Q.toLinearMap _ _ _ _
    hP hkerP hkerQ A B hPQ
  -- Derive adjoint intertwining from the exact same pairings and supported maps.
  have hRS := IsMetricFormalAdjoint.intertwining_of_supported E F E' F' h k h' k' μ ν
    K L hK hL P.toLinearMap (P.metricFormalAdjoint h k).toLinearMap
    Q.toLinearMap (Q.metricFormalAdjoint h' k').toLinearMap
    (P.isMetricFormalAdjoint_metricFormalAdjoint h k)
    (Q.isMetricFormalAdjoint_metricFormalAdjoint h' k') hP hR hS A B hA hB hPQ
  obtain ⟨f, hf⟩ := kerEquiv _ _ _ _ (P.metricFormalAdjoint h k).toLinearMap
    (Q.metricFormalAdjoint h' k').toLinearMap _ _ _ _ hR hkerR hkerS B A hRS
  -- Ellipticity identifies each original smooth cokernel with its actual adjoint kernel.
  obtain ⟨AE⟩ := nonempty_smoothBundlePresentation (n := n) (r := E.rank) E.Fiber
  obtain ⟨AF⟩ := nonempty_smoothBundlePresentation (n := n) (r := F.rank) F.Fiber
  obtain ⟨AG⟩ := nonempty_smoothBundlePresentation (n := m) (r := E'.rank) E'.Fiber
  obtain ⟨AH⟩ := nonempty_smoothBundlePresentation (n := m) (r := F'.rank) F'.Fiber
  obtain ⟨P', hP'⟩ := P.exists_parametrix_of_isElliptic hPe
  obtain ⟨Q', hQ'⟩ := Q.exists_parametrix_of_isElliptic hQe
  let CP := P.kerMetricFormalAdjointEquivCoker h k AE AF P' hP'
  let CQ := Q.kerMetricFormalAdjointEquivCoker h' k' AG AH Q' hQ'
  let C := CP.symm.trans (f.trans CQ)
  let RE := σE.smoothSectionRepresentation IG hσE
  let RF := σF.smoothSectionRepresentation IG hσF
  let SE := τE.smoothSectionRepresentation IG hτE
  let SF := τF.smoothSectionRepresentation IG hτF
  -- Equivariance preserves the original ranges and gives their quotient actions.
  have hrangeP (g : G) : P.toLinearMap.range ≤ P.toLinearMap.range.comap (RF g) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨RE g u, congrArg (fun T ↦ T u) (hPg g)⟩
  have hrangeQ (g : G) : Q.toLinearMap.range ≤ Q.toLinearMap.range.comap (SF g) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨SE g u, congrArg (fun T ↦ T u) (hQg g)⟩
  let RP := RF.quotient P.toLinearMap.range hrangeP
  let RQ := SF.quotient Q.toLinearMap.range hrangeQ
  have hCP (v : (P.metricFormalAdjoint h k).toLinearMap.ker) :
      CP v = P.toLinearMap.range.mkQ v.val := rfl
  have hCQ (v : (Q.metricFormalAdjoint h' k').toLinearMap.ker) :
      CQ v = Q.toLinearMap.range.mkQ v.val := rfl
  -- The supported target map intertwines on adjoint zeros; their inclusions give
  -- the original cokernel classes, so no new quotient representation is chosen.
  have hC (g : G) (z : smoothSections (n := n) (r := F.rank) F.Fiber ⧸
      P.toLinearMap.range) : C (RP g z) = RQ g (C z) := by
    obtain ⟨v, rfl⟩ := CP.surjective z
    let gv : (P.metricFormalAdjoint h k).toLinearMap.ker :=
      ⟨RF g v.val, hRg g v⟩
    have hgv : RP g (CP v) = CP gv := rfl
    have hfv : (f gv).val = SF g (f v).val := by
      rw [hf, hf]
      exact hBg g ⟨v.val, hkerR v.property⟩
    rw [hgv]
    change CQ (f (CP.symm (CP gv))) = RQ g (CQ (f (CP.symm (CP v))))
    rw [CP.symm_apply_apply, CP.symm_apply_apply, hCQ, hCQ]
    change Q.toLinearMap.range.mkQ (f gv).val =
      Q.toLinearMap.range.mkQ (SF g (f v).val)
    exact congrArg Q.toLinearMap.range.mkQ hfv
  obtain ⟨ρ, τ, a, b, ha, hb⟩ :=
    P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hPe
  have hkernel (g : G) (v : Fin ρ.dimension → ℂ) :
      ((a.trans e) (ρ.representation g v)).val = SE g ((a.trans e) v).val := by
    change (e (a (ρ.representation g v))).val = SE g (e (a v)).val
    rw [he, he]
    have hu := ha g v
    change (a (ρ.representation g v)).val = RE g (a v).val at hu
    have hsub : (⟨(a (ρ.representation g v)).val,
        hkerP (a (ρ.representation g v)).property⟩ :
        supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) =
      ⟨RE g (a v).val, hEK g ⟨(a v).val, hkerP (a v).property⟩⟩ := Subtype.ext hu
    rw [hsub]
    exact hAg g ⟨(a v).val, hkerP (a v).property⟩
  have hτ (g : G) (z : smoothSections (n := n) (r := F.rank) F.Fiber ⧸
      P.toLinearMap.range) : b (τ.representation g (b.symm z)) = RP g z := by
    obtain ⟨v, rfl⟩ := P.toLinearMap.range.mkQ_surjective z
    exact hb g v
  have hcoker (g : G) (v : smoothSections (n := m) (r := F'.rank) F'.Fiber) :
      (b.trans C) (τ.representation g ((b.trans C).symm (Q.toLinearMap.range.mkQ v))) =
        Q.toLinearMap.range.mkQ (SF g v) := by
    change C (b (τ.representation g (b.symm (C.symm (Q.toLinearMap.range.mkQ v))))) = _
    rw [hτ, hC, C.apply_symm_apply]
    rfl
  -- Evaluate both indices using exactly the same finite continuous coordinates.
  rw [P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hPe ρ τ a b ha hb]
  exact (Q.smoothEquivariantAnalyticIndex_eq IG τE τF hτE hτF hQg hQe
    ρ τ (a.trans e) (b.trans C) hkernel hcoker).symm

end AtiyahSinger
