/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.HermitianMetricAdjointKernel
public import AtiyahSinger.Analysis.SupportedSectionPairing
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Comparing adjoints and indices through supported section identifications

Public module ID: M1015.

UL03/P02: the analytic comparison used after relative geometries and actual
localized operators have been identified. The hypotheses retain the two integral
pairings, the prescribed supported section equivalences, and the exact operator
action. Adjoint intertwining is a conclusion, not an input.

SG III.13.4, pp.248--249, compares both kernels across ambient extensions. These
statements make its conditional analytic comparison explicit. They do not produce
an arbitrary noncompact K representative, compatible geometric identifications,
or the symbol-class extension equation. Thus they are not full excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  [MeasurableSpace M] [MeasurableSpace N] [BorelSpace M] [BorelSpace N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := m) N)
  (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
  (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
  (h' : SmoothHermitianMetric (n := m) (r := G.rank) G.Fiber)
  (k' : SmoothHermitianMetric (n := m) (r := H.rank) H.Fiber)
  (μ : Measure M) (ν : Measure N)
  [hμ : IsSmoothPositiveMeasure (n := n) μ] [hν : IsSmoothPositiveMeasure (n := m) ν]

include hM hN hT hT' hSC hSC' hμ hν

/-- Prescribed pairing-preserving identifications intertwine the actual supported adjoints. -/
theorem IsMetricFormalAdjoint.intertwining_of_supported
    (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
    (P : smoothSections (n := n) (r := E.rank) E.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := F.rank) F.Fiber)
    (R : smoothSections (n := n) (r := F.rank) F.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := E.rank) E.Fiber)
    (Q : smoothSections (n := m) (r := G.rank) G.Fiber →ₗ[ℂ]
      smoothSections (n := m) (r := H.rank) H.Fiber)
    (S : smoothSections (n := m) (r := H.rank) H.Fiber →ₗ[ℂ]
      smoothSections (n := m) (r := G.rank) G.Fiber)
    (hPR : IsMetricFormalAdjoint h k μ P R)
    (hQS : IsMetricFormalAdjoint h' k' ν Q S)
    (hP : ∀ u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K, P u.val ∈
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber K)
    (hR : ∀ v : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K, R v.val ∈
      supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
    (hS : ∀ v : supportedSmoothSections (n := m) (r := H.rank) H.Fiber L, S v.val ∈
      supportedSmoothSections (n := m) (r := G.rank) G.Fiber L)
    (A : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K ≃ₗ[ℂ]
      supportedSmoothSections (n := m) (r := G.rank) G.Fiber L)
    (B : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K ≃ₗ[ℂ]
      supportedSmoothSections (n := m) (r := H.rank) H.Fiber L)
    (hA : ∀ u v, h'.sectionPairing ν (A u).val (A v).val =
      h.sectionPairing μ u.val v.val)
    (hB : ∀ u v, k'.sectionPairing ν (B u).val (B v).val =
      k.sectionPairing μ u.val v.val)
    (hPQ : ∀ u, Q (A u).val = (B ⟨P u.val, hP u⟩).val) :
    ∀ v, S (B v).val = (A ⟨R v.val, hR v⟩).val := by
  /- Stage 1: test the difference of the two proposed outputs against A u.
  Use the two ambient adjunction identities, exact original intertwining hPQ,
  and preservation of both integral pairings. The resulting integral is zero
  for every supported u. No ellipticity or kernel-finiteness assertion is used.
  Stage 2: hS and hR place both outputs in the target supported space. Since A
  is onto, test with a preimage of their difference. Compact support makes this
  scalar quadratic form integrable and definite, hence the difference vanishes.
  The result concerns the actual adjoint actions on supported inputs. It does
  not claim existence of formal adjoints on arbitrary noncompact section spaces;
  the supplied hPR and hQS are explicit hypotheses. -/
  /- The same prescribed A and B identify all supported test pairings of the
  two adjoint outputs. Test their supported difference, then transport its zero
  quadratic pairing back through A and use definiteness on the original K. -/
  intro v
  let rv : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K :=
    ⟨R v.val, hR v⟩
  let sv : supportedSmoothSections (n := m) (r := G.rank) G.Fiber L :=
    ⟨S (B v).val, hS (B v)⟩
  -- Both adjunction identities use the exact original intertwining and pairings.
  have hpair (w : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) :
      h'.sectionPairing ν (A w).val sv.val =
        h'.sectionPairing ν (A w).val (A rv).val := by
    calc
      _ = k'.sectionPairing ν (Q (A w).val) (B v).val := (hQS _ _).symm
      _ = k'.sectionPairing ν (B ⟨P w.val, hP w⟩).val (B v).val := by
        rw [hPQ w]
      _ = k.sectionPairing μ (P w.val) v.val := hB _ v
      _ = h.sectionPairing μ w.val (R v.val) := hPR _ _
      _ = h'.sectionPairing ν (A w).val (A rv).val := (hA w rv).symm
  -- The actual outputs share L, so their difference supplies an integrable test.
  let d : supportedSmoothSections (n := m) (r := G.rank) G.Fiber L := sv - A rv
  let u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K := A.symm d
  have hAu : A u = d := A.apply_symm_apply d
  have hdiff : h'.sectionPairing ν d.val d.val =
      h'.sectionPairing ν d.val sv.val - h'.sectionPairing ν d.val (A rv).val := by
    unfold SmoothHermitianMetric.sectionPairing
    have heval (x : N) : h'.pairing x (d.val.val x) (d.val.val x) =
        h'.pairing x (d.val.val x) (sv.val.val x) -
          h'.pairing x (d.val.val x) ((A rv).val.val x) := by
      change (h'.toCore x).inner (d.val.val x)
        (sv.val.val x - (A rv).val.val x) = _
      let : InnerProductSpace.Core ℂ (G.Fiber x) := h'.toCore x
      exact InnerProductSpace.Core.inner_sub_right _ _ _
    simp_rw [heval]
    exact integral_sub (h'.integrable_pairing_of_supported ν L hL d sv.val)
      (h'.integrable_pairing_of_supported ν L hL d (A rv).val)
  have hdself : h'.sectionPairing ν d.val d.val = 0 := by
    rw [hdiff]
    have htest := hpair u
    rw [hAu] at htest
    exact sub_eq_zero.mpr htest
  -- A preserves the same quadratic pairing, so source definiteness annihilates its preimage.
  have huself : h.sectionPairing μ u.val u.val = 0 := by
    rw [← hA u u, hAu]
    exact hdself
  have hu : u = 0 :=
    (h.sectionPairing_self_eq_zero_iff_of_supported μ K hK u).mp huself
  have hd : d = 0 := by
    calc
      d = A u := hAu.symm
      _ = A 0 := congrArg A hu
      _ = 0 := A.map_zero
  exact congrArg Subtype.val (sub_eq_zero.mp hd)

variable [hC : CompactSpace M] [hC' : CompactSpace N]

include hC hC'

set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the specified supported actions, pairings and both kernel
-- comparisons.
/-- Matching supported actions and pairings give equal indices when they capture both kernels. -/
theorem PseudodifferentialOperator.index_eq_of_supported_intertwining
    {a b : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ a)
    (Q : PseudodifferentialOperator (n := m) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber ν b)
    (hPe : P.IsElliptic) (hQe : Q.IsElliptic)
    (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
    (hP : ∀ u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K, P.toLinearMap u.val ∈
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber K)
    (hR : ∀ v : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K,
      (P.metricFormalAdjoint h k).toLinearMap v.val ∈
        supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
    (hS : ∀ v : supportedSmoothSections (n := m) (r := H.rank) H.Fiber L,
      (Q.metricFormalAdjoint h' k').toLinearMap v.val ∈
        supportedSmoothSections (n := m) (r := G.rank) G.Fiber L)
    (hkerP : P.toLinearMap.ker ≤ supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
    (hkerQ : Q.toLinearMap.ker ≤ supportedSmoothSections (n := m) (r := G.rank) G.Fiber L)
    (hkerR : (P.metricFormalAdjoint h k).toLinearMap.ker ≤
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber K)
    (hkerS : (Q.metricFormalAdjoint h' k').toLinearMap.ker ≤
      supportedSmoothSections (n := m) (r := H.rank) H.Fiber L)
    (A : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K ≃ₗ[ℂ]
      supportedSmoothSections (n := m) (r := G.rank) G.Fiber L)
    (B : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K ≃ₗ[ℂ]
      supportedSmoothSections (n := m) (r := H.rank) H.Fiber L)
    (hA : ∀ u v, h'.sectionPairing ν (A u).val (A v).val =
      h.sectionPairing μ u.val v.val)
    (hB : ∀ u v, k'.sectionPairing ν (B u).val (B v).val =
      k.sectionPairing μ u.val v.val)
    (hPQ : ∀ u, Q.toLinearMap (A u).val = (B ⟨P.toLinearMap u.val, hP u⟩).val) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  /- Stage 1: use the preceding supported-adjoint comparison with the actual
  metricFormalAdjoint maps and their existing integral identities. This derives
  the second intertwining relation; it is not an extra premise of the theorem.
  Stage 2: the four kernel-support inclusions let A and B restrict to the
  original and adjoint kernels respectively. The original and derived adjoint
  intertwining, and the inverse supported equivalences, give two actual kernel
  equivalences. Construct these inside this proof, retaining the specified maps.
  Stage 3: ellipticity supplies two-sided parametrices and finite smooth bundle
  presentations on each compact base. Apply the existing metric-adjoint kernel
  formula for each index and replace both finranks using those equivalences.
  No common rank, order, base dimension, unitarity outside K/L, or connectedness
  is imposed. These are conditional analytic comparisons: compatible A, B and
  actual hPQ, the initial relative K representative, and the symbol K extension
  equation must still be obtained before deducing SG's full excision property. -/
  classical
  -- Restrict the supplied intertwiner to the full kernels, using the support inclusions.
  have kerEquiv (X₁ : Type _) (Y₁ : Type _) (X₂ : Type _) (Y₂ : Type _)
      [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup Y₁] [Module ℂ Y₁]
      [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup Y₂] [Module ℂ Y₂]
      (p : X₁ →ₗ[ℂ] Y₁) (q : X₂ →ₗ[ℂ] Y₂)
      (s₁ : Submodule ℂ X₁) (t₁ : Submodule ℂ Y₁)
      (s₂ : Submodule ℂ X₂) (t₂ : Submodule ℂ Y₂)
      (hp : ∀ u : s₁, p u.val ∈ t₁) (hkp : p.ker ≤ s₁) (hkq : q.ker ≤ s₂)
      (a : s₁ ≃ₗ[ℂ] s₂) (b : t₁ ≃ₗ[ℂ] t₂)
      (hpq : ∀ u : s₁, q (a u).val = (b ⟨p u.val, hp u⟩).val) :
      Nonempty (p.ker ≃ₗ[ℂ] q.ker) := by
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
    exact ⟨LinearEquiv.ofBijective f hf⟩
  obtain ⟨e⟩ := kerEquiv _ _ _ _ P.toLinearMap Q.toLinearMap _ _ _ _
    hP hkerP hkerQ A B hPQ
  -- Derive adjoint intertwining from the exact same pairings and supported maps.
  have hRS := IsMetricFormalAdjoint.intertwining_of_supported E F G H h k h' k' μ ν
    K L hK hL P.toLinearMap (P.metricFormalAdjoint h k).toLinearMap
    Q.toLinearMap (Q.metricFormalAdjoint h' k').toLinearMap
    (P.isMetricFormalAdjoint_metricFormalAdjoint h k)
    (Q.isMetricFormalAdjoint_metricFormalAdjoint h' k') hP hR hS A B hA hB hPQ
  obtain ⟨f⟩ := kerEquiv _ _ _ _ (P.metricFormalAdjoint h k).toLinearMap
    (Q.metricFormalAdjoint h' k').toLinearMap _ _ _ _ hR hkerR hkerS B A hRS
  -- Ellipticity supplies actual parametrices and the two smooth-kernel index formulas.
  obtain ⟨AE⟩ := nonempty_smoothBundlePresentation (n := n) (r := E.rank) E.Fiber
  obtain ⟨AF⟩ := nonempty_smoothBundlePresentation (n := n) (r := F.rank) F.Fiber
  obtain ⟨AG⟩ := nonempty_smoothBundlePresentation (n := m) (r := G.rank) G.Fiber
  obtain ⟨AH⟩ := nonempty_smoothBundlePresentation (n := m) (r := H.rank) H.Fiber
  obtain ⟨P', hP'⟩ := P.exists_parametrix_of_isElliptic hPe
  obtain ⟨Q', hQ'⟩ := Q.exists_parametrix_of_isElliptic hQe
  rw [P.index_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint h k AE AF P' hP',
    Q.index_eq_finrank_ker_sub_finrank_ker_metricFormalAdjoint h' k' AG AH Q' hQ',
    e.finrank_eq, f.finrank_eq]

end AtiyahSinger
