/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.RelativeEllipticRealization
public import AtiyahSinger.Analysis.FullSymbolParametrix

/-!
# Elliptic representatives under a whole-base diffeomorphism

Public module ID: M0429.

A10/P02: quantize one degree-zero symbol by a specified finite family, transport
that same family, and identify the actual section maps. The source and target
principal representatives retain the inverse-dual cotangent square. Whole-base
section equivalences identify kernels and quotient cokernels, so no density or
Hermitian pairing compatibility is needed for their algebraic indices.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace Filter Set
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback
attribute [local instance 2000] FiberBundle.pullback VectorBundle.pullback

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
  (hU : U = ⊤) (hV : V = ⊤)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (α : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (hα : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (α x).toLinearMap))
  (β : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hβ : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (β x).toLinearMap))
  [hC' : CompactSpace N] [MeasurableSpace N] [hB' : BorelSpace N]
  (ν : Measure N) [hν : IsSmoothPositiveMeasure (n := n) ν]


variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

include hU hV hα hβ

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in

/-- Elliptic representatives retain the prescribed cotangent square and have equal index. -/
theorem exists_elliptic_representatives_of_diffeomorph
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (A : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (R : QuantizationPresentation (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber) :
    ∃ (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber μ 0)
      (Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber ν 0)
      (b : homogeneousGlobalSymbolSpace (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber 0),
      P.IsElliptic ∧ Q.IsElliptic ∧ IsEllipticGlobalSymbol G.Fiber H.Fiber b.val ∧
      P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
        (A.regularizedSymbol 0 a.val a.property.1 a.property.2) ∧
      Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber 0
        (R.regularizedSymbol 0 b.val b.property.1 b.property.2) ∧
      (∀ (x : U) (ξ : CotangentFiber (n := n) x.val) (v : E.Fiber x.val),
        b.val (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (α x v) =
          β x (a.val x.val ξ v)) ∧ P.toLinearMap.index = Q.toLinearMap.index := by
  classical
  have hKU : (univ : Set M) ⊆ (U : Set M) := by simp [hU]
  have hLV : (univ : Set N) ⊆ (V : Set N) := by simp [hV]
  have hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' (univ : Set N)) =
      (Subtype.val : U → M) ⁻¹' (univ : Set M) := by simp
  have hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (0 : E.Fiber x →L[ℂ] F.Fiber x).toLinearMap) := by
    intro i _ j _ k
    apply (contMDiffOn_const (c := (0 : EuclideanSpace ℂ (Fin F.rank)))).congr
    intro x hx
    change (j ⟨x, 0⟩).2 = 0
    simpa only [j.coe_linearMapAt_of_mem hx.2] using (j.linearMapAt ℂ x).map_zero
  have hd : IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank)
      (fun x ↦ (0 : G.Fiber x →L[ℂ] H.Fiber x).toLinearMap) := by
    intro i _ j _ k
    apply (contMDiffOn_const (c := (0 : EuclideanSpace ℂ (Fin H.rank)))).congr
    intro x hx
    change (j ⟨x, 0⟩).2 = 0
    simpa only [j.coe_linearMapAt_of_mem hx.2] using (j.linearMapAt ℂ x).map_zero
  obtain ⟨g⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
  -- Quantize once. The finite source sum retains every lower-order cutoff term.
  obtain ⟨p, _, hhigh, k, T, hsum, L, _, _, _, _, _, _⟩ :=
    exists_relative_quantization_pieces E F a (fun _ ↦ 0) hc univ isCompact_univ
      (by simp) univ isOpen_univ (Subset.refl _) g
  have hzero : IsSmoothingOperator μ
      (0 : smoothSections (n := n) (r := E.rank) E.Fiber →ₗ[ℂ]
        smoothSections (n := n) (r := F.rank) F.Fiber) := by
    let K : SmoothKernel (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber :=
      { toFun := fun _ _ ↦ 0
        isSmooth := by
          intro i j _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames E.Fiber F.Fiber (fun _ _ ↦ 0) i j z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
            ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
    refine ⟨K, ?_⟩
    ext u x
    change K.apply μ u x = 0
    simp [SmoothKernel.apply, K]
  let P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0 :=
    ⟨∑ j, (T j).toLinearMap, ⟨k, T, by simpa using hzero⟩⟩
  have hPp : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0 p := by
    rw [P.principalSymbol_eq_of_representation k T (by simpa [P] using hzero), hsum]
  -- Compare the actual full source representative with the requested regularization.
  have hPa : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
      (A.regularizedSymbol 0 a.val a.property.1 a.property.2) := by
    rw [hPp, globalPrincipalSymbolClass_eq_iff]
    apply isGlobalSymbol_sub_of_high_frequency p
      (A.regularizedSymbol 0 a.val a.property.1 a.property.2)
    intro c hcat i j _ _ C hC hCV
    let X := EuclideanSpace ℝ (Fin n)
    let ℓ (z η : X) := g.length (c.symm z) (covectorFromChart c (c.symm z) η)
    have hne (z η : X) (hz : z ∈ C) (hη : η ≠ 0) :
        covectorFromChart c (c.symm z) η ≠ 0 := by
      intro heq
      have h := covectorInChart_covectorFromChart c hcat (c.symm z)
        (c.map_target (hCV hz).1.1) η
      rw [heq] at h
      apply hη
      rw [← h]
      ext v
      rfl
    have hcont : ContinuousOn (Function.uncurry ℓ) (C ×ˢ Metric.sphere (0 : X) 1) :=
      (g.contDiffOn_length_covectorFromChart c hcat).continuousOn.mono (by
        intro z hz
        exact ⟨(hCV hz.1).1.1, by intro heq; simpa [heq] using hz.2⟩)
    obtain ⟨δ, hδ, hlow⟩ := (hC.prod (isCompact_sphere (0 : X) 1)).exists_forall_le'
      hcont (a := 0) (by
        intro z hz
        exact g.length_pos _ _ (hne z.1 z.2 hz.1 (by
          intro heq
          simpa [heq] using hz.2)))
    obtain ⟨r, _, hr⟩ := A.regularizedSymbolFunction_eq_inChart_at_high_frequency
      a.val c hcat i j C hC hCV
    refine ⟨max δ⁻¹ r, ?_⟩
    intro z hz η hη
    have hl : δ⁻¹ ≤ ‖η‖ := (le_max_left _ _).trans hη
    have hn : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hδ) hl
    let u := ‖η‖⁻¹ • η
    have hu : u ∈ Metric.sphere (0 : X) 1 := by
      simpa [u, mem_sphere_zero_iff_norm] using
        norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.mp hn)
    have hscale : ℓ z η = ‖η‖ * ℓ z u := by
      have hηeq : ‖η‖ • u = η := by simp [u, smul_smul, hn.ne']
      conv_lhs => rw [← hηeq]
      change g.length _ (covectorFromChart c _ (‖η‖ • u)) = _
      have hcov : covectorFromChart c (c.symm z) (‖η‖ • u) =
          ‖η‖ • covectorFromChart c (c.symm z) u := by
        ext v
        change inner ℝ (‖η‖ • u) _ = ‖η‖ * inner ℝ u _
        exact real_inner_smul_left _ _ _
      rw [hcov, g.length_smul, abs_of_nonneg (norm_nonneg _)]
    have hone : 1 ≤ ℓ z η := by
      rw [hscale]
      calc
        1 = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
        _ ≤ ‖η‖ * δ := mul_le_mul_of_nonneg_right hl hδ.le
        _ ≤ ‖η‖ * ℓ z u := mul_le_mul_of_nonneg_left (hlow (z, u) ⟨hz, hu⟩) hn.le
    change globalSymbolInChart E.Fiber F.Fiber p.val c i j z η =
      globalSymbolInChart E.Fiber F.Fiber (A.regularizedSymbolFunction a.val) c i j z η
    rw [hr z hz η ((le_max_right _ _).trans hη)]
    have hp : p.val (c.symm z) (covectorFromChart c (c.symm z) η) =
        a.val (c.symm z) (covectorFromChart c (c.symm z) η) := by
      simpa using hhigh (c.symm z) (covectorFromChart c (c.symm z) η) hone
    simp only [globalSymbolInChart, hp]
  have hPe : P.IsElliptic :=
    (P.isElliptic_iff_homogeneous A a hPa).mpr ha
  -- The same finite family is transported with its exact section action and cotangent square.
  obtain ⟨Q, b, hb, hQ, hQb, _, hact, hsymbol, _, _⟩ :=
    exists_relative_elliptic_openExtension_of_pieces E F G H U V e
      univ univ isCompact_univ isCompact_univ hKU hLV hKL α hα β hβ ν
      a ha (fun _ ↦ 0) hc (by simp) (fun _ ↦ 0) hd
      (by intro x v; exact (map_zero (β x)).symm) (by simp)
      g k T (fun _ ↦ subset_univ _) (by simpa [hsum] using hhigh) R
  refine ⟨P, Q, b, hPe, hQ, hb, hPa, hQb, hsymbol, ?_⟩
  -- Whole-base supports identify all smooth sections, with the specified fiber action.
  let total (B : SmoothFiniteComplexBundle (n := n) M) :
      smoothSections (n := n) (r := B.rank) B.Fiber ≃ₗ[ℂ]
        supportedSmoothSections (n := n) (r := B.rank) B.Fiber univ :=
    { toFun := fun u ↦ ⟨u, by intro x hx; exact (hx (mem_univ x)).elim⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let total' (B : SmoothFiniteComplexBundle (n := n) N) :
      smoothSections (n := n) (r := B.rank) B.Fiber ≃ₗ[ℂ]
        supportedSmoothSections (n := n) (r := B.rank) B.Fiber univ :=
    { toFun := fun u ↦ ⟨u, by intro x hx; exact (hx (mem_univ x)).elim⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let S := ((total E).trans (supportedSmoothSectionOpenEquiv E G U V e univ univ
    isClosed_univ isClosed_univ hKU hLV hKL α hα)).trans (total' G).symm
  let T₀ := ((total F).trans (supportedSmoothSectionOpenEquiv F H U V e univ univ
    isClosed_univ isClosed_univ hKU hLV hKL β hβ)).trans (total' H).symm
  have hS (u : smoothSections (n := n) (r := E.rank) E.Fiber) (x : U) :
      (S u).val (e x).val = α x (u.val x.val) :=
    supportedSmoothSectionOpenEquiv_apply E G U V e univ univ isCompact_univ isCompact_univ
      hKU hLV hKL α hα (total E u) x
  have hT (u : smoothSections (n := n) (r := F.rank) F.Fiber) (x : U) :
      (T₀ u).val (e x).val = β x (u.val x.val) :=
    supportedSmoothSectionOpenEquiv_apply F H U V e univ univ isCompact_univ isCompact_univ
      hKU hLV hKL β hβ (total F u) x
  have hinter (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      Q.toLinearMap (S u) = T₀ (P.toLinearMap u) := by
    apply Subtype.ext
    funext y
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hLV (mem_univ y)⟩
    have heq : (e x).val = y := congrArg Subtype.val hx
    rw [← heq, hT]
    have hv := hact u (S u) (Eventually.of_forall (hS u)) x
    simpa [smoothSectionMap, P] using hv
  -- The exact intertwining identifies both algebraic defects, including quotient cokernels.
  let kerEquiv : LinearMap.ker P.toLinearMap ≃ₗ[ℂ] LinearMap.ker Q.toLinearMap :=
    { toFun := fun u ↦ ⟨S u.val, by rw [LinearMap.mem_ker, hinter, u.property, map_zero]⟩
      invFun := fun u ↦ ⟨S.symm u.val, by
        apply T₀.injective
        rw [map_zero, ← hinter, S.apply_symm_apply]
        exact u.property⟩
      left_inv := fun u ↦ Subtype.ext (S.symm_apply_apply u.val)
      right_inv := fun u ↦ Subtype.ext (S.apply_symm_apply u.val)
      map_add' := fun u v ↦ Subtype.ext (S.map_add u.val v.val)
      map_smul' := fun t u ↦ Subtype.ext (S.map_smul t u.val) }
  have hrange : (LinearMap.range P.toLinearMap).map T₀.toLinearMap =
      LinearMap.range Q.toLinearMap := by
    ext v
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨S u, hinter u⟩
    · rintro ⟨u, rfl⟩
      exact ⟨P.toLinearMap (S.symm u), ⟨S.symm u, rfl⟩,
        (hinter (S.symm u)).symm.trans (congrArg Q.toLinearMap (S.apply_symm_apply u))⟩
  let cokerEquiv := Submodule.Quotient.equiv (LinearMap.range P.toLinearMap)
    (LinearMap.range Q.toLinearMap) T₀ hrange
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    kerEquiv.finrank_eq, cokerEquiv.finrank_eq]

end AtiyahSinger
