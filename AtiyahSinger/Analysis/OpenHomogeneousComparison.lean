/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereRegularity
public import AtiyahSinger.Analysis.OpenSymbolCoordinates

/-!
# The principal class of relative homogeneous open transport

Public module ID: M0823.

High-frequency agreement in the original source metric is preserved locally by
the specified open transport. Compact coordinate subsets admit uniform bounds,
so the target full symbol and the specified regularization have the same class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set TopologicalSpace
open scoped ContDiff Manifold Topology

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
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



include hα hβ in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
-- Compact source-frequency bounds and the two original coordinate formulas share every witness.
/-- The transported full symbol has the principal class of the specified homogeneous data. -/
theorem globalPrincipalSymbolClass_openTransport_eq_regularizedSymbol [T2Space N]
    (L : Set N) (hL : IsCompact L) (hLV : L ⊆ (V : Set N))
    (ℓ : SmoothCotangentMetric (n := n) (M := M))
    (p a : GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
    (hhigh : ∀ x ξ, 1 ≤ ℓ.length x ξ → p x ξ = a x ξ)
    (q : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber 0)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber 0)
    (hq : ∀ (x : U) η (v : E.Fiber x.val),
      q.val (e x).val η (α x v) = β x
        (p x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v))
    (hb : ∀ (x : U) η (v : E.Fiber x.val),
      b.val (e x).val η (α x v) = β x
        (a x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v))
    (hexterior : ∀ y, y ∉ L → ∀ η, q.val y η = b.val y η)
    (R : QuantizationPresentation (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber) :
    globalPrincipalSymbolClass G.Fiber H.Fiber 0 q =
      globalPrincipalSymbolClass G.Fiber H.Fiber 0
        (R.regularizedSymbol 0 b.val b.property.1 b.property.2) := by
  classical
  apply (globalPrincipalSymbolClass_eq_iff G.Fiber H.Fiber 0 _ _).mpr
  change IsGlobalSymbol (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber (0 - 1)
    (q.val - R.regularizedSymbolFunction b.val)
  intro C hC f g _ _
  let X := EuclideanSpace ℝ (Fin n)
  let Ω := symbolChartDomain G.Fiber H.Fiber C f g
  have hΩ : IsOpen Ω := isOpen_symbolChartDomain G.Fiber H.Fiber C f g
  let Q := globalSymbolInChart G.Fiber H.Fiber q.val C f g
  let B₀ := globalSymbolInChart G.Fiber H.Fiber b.val C f g
  let S := globalSymbolInChart G.Fiber H.Fiber (R.regularizedSymbolFunction b.val) C f g
  have hsub : globalSymbolInChart G.Fiber H.Fiber
      (q.val - R.regularizedSymbolFunction b.val) C f g = Q - S := by
    ext z η v
    simp [globalSymbolInChart, Q, S]
  rw [hsub]
  have hreg : ContDiffOn ℝ ∞ (Function.uncurry (Q - S)) (Ω ×ˢ univ) :=
    (q.property C hC f g).1.sub
      (R.isGlobalSymbol_regularizedSymbolFunction 0 b.val b.property.1 b.property.2 C hC f g).1
  -- Local uniform high-frequency agreement makes the difference lower order.
  have hcriterion (Z : Set X) (hZ : IsOpen Z) (hZΩ : Z ⊆ Ω)
      (hZhigh : ∀ K : Set X, K ⊆ Z → IsCompact K →
        ∃ r : ℝ, ∀ y ∈ K, ∀ η, r ≤ ‖η‖ → Q y η = B₀ y η) :
      IsSymbol Z (0 - 1) (Q - S) := by
    refine ⟨hreg.mono (Set.prod_mono hZΩ subset_rfl), ?_⟩
    intro K hKZ hK i j
    obtain ⟨K', hK', hKK', hK'Z⟩ := exists_compact_between hK hZ hKZ
    obtain ⟨r₁, hr₁⟩ := hZhigh K' hK'Z hK'
    obtain ⟨r₂, _, hr₂⟩ := R.regularizedSymbolFunction_eq_inChart_at_high_frequency
      b.val C hC f g K' hK' (hK'Z.trans hZΩ)
    have hsupp : ∀ y ∈ interior K', ∀ η, max r₁ r₂ ≤ ‖η‖ → (Q - S) y η = 0 := by
      intro y hy η hη
      change Q y η - S y η = 0
      rw [hr₁ y (interior_subset hy) η ((le_max_left _ _).trans hη)]
      dsimp only [S, B₀]
      rw [hr₂ y (interior_subset hy) η ((le_max_right _ _).trans hη), sub_self]
    have hlocal := isSmoothingSymbol_of_frequency_support isOpen_interior (Q - S)
      (max r₁ r₂) (hreg.mono (Set.prod_mono
        (interior_subset.trans (hK'Z.trans hZΩ)) subset_rfl)) hsupp (0 - 1)
    exact hlocal.2 K hKK' hK i j
  apply IsSymbol.of_locally hΩ
  intro z hz
  by_cases hzL : C.symm z ∈ L
  · obtain ⟨C₀, f₀, g₀, hf₀, hg₀, hC₀, Z, t, A, B, hZ, hzZ, hZΩ, hZt, htS,
      ht, hts, _, _, _, hformula⟩ :=
      exists_local_openSymbolInChart E F G H U V e α hα β hβ C hC f g z hz (hLV hzL)
    let := hf₀
    let := hg₀
    refine ⟨Z, hZ, hzZ, hZΩ, hcriterion Z hZ hZΩ ?_⟩
    intro K hKZ hK
    let D (y : X) := fderiv ℝ t (t.symm y)
    let adjointMap : (X →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) :=
      ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
    have hD (y : X) (hy : y ∈ Z) : ContDiffAt ℝ ∞ D y :=
      (((ht.contDiffAt (t.open_source.mem_nhds (t.map_target (hZt hy)))).fderiv_right
        (m := ∞) (by simp)).comp y
          (hts.contDiffAt (t.open_target.mem_nhds (hZt hy))))
    have hν (y η : X) (hy : y ∈ Z) :
        ContDiffAt ℝ ∞ (fun w : X × X ↦ (D w.1).adjoint w.2) (y, η) :=
      (adjointMap.contDiff.contDiffAt.comp (y, η)
        ((hD y hy).comp (y, η) contDiffAt_fst)).clm_apply contDiffAt_snd
    have hνne (y η : X) (hy : y ∈ Z) (hη : η ≠ 0) : (D y).adjoint η ≠ 0 := by
      have hf := (ht.contDiffAt (t.open_source.mem_nhds
        (t.map_target (hZt hy)))).differentiableAt (by simp)
      have hb' := (hts.contDiffAt (t.open_target.mem_nhds (hZt hy))).differentiableAt (by simp)
      have hright : (D y).comp (fderiv ℝ t.symm y) = ContinuousLinearMap.id ℝ X := by
        apply (hf.hasFDerivAt.comp y hb'.hasFDerivAt).unique
        apply (hasFDerivAt_id y).congr_of_eventuallyEq
        filter_upwards [t.open_target.mem_nhds (hZt hy)] with w hw
        exact t.right_inv hw
      have hdual := congrArg ContinuousLinearMap.adjoint hright
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hdual
      intro hzero
      have h := congrArg (fun T ↦ T η) hdual
      change (fderiv ℝ t.symm y).adjoint ((D y).adjoint η) = η at h
      rw [hzero, map_zero] at h
      exact hη h.symm
    have htarget (y : X) (hy : y ∈ Z) : t.symm y ∈ C₀.target :=
      (htS (t.map_target (hZt hy))).1.1
    have hcovne (y η : X) (hy : y ∈ Z) (hη : η ≠ 0) :
        covectorFromChart C₀ (C₀.symm (t.symm y)) ((D y).adjoint η) ≠ 0 := by
      intro hzero
      have h := covectorInChart_covectorFromChart C₀ hC₀ (C₀.symm (t.symm y))
        (C₀.map_target (htarget y hy)) ((D y).adjoint η)
      rw [hzero] at h
      have hzero' : covectorInChart C₀ (C₀.symm (t.symm y)) 0 = 0 := by ext; rfl
      exact hνne y η hy hη (h.symm.trans hzero')
    let Λ (y η : X) := ℓ.length (C₀.symm (t.symm y))
      (covectorFromChart C₀ (C₀.symm (t.symm y)) ((D y).adjoint η))
    have hΛ (y η : X) (hy : y ∈ Z) (hη : η ≠ 0) :
        ContDiffAt ℝ ∞ (Function.uncurry Λ) (y, η) := by
      have hsource : ContDiffAt ℝ ∞
          (fun w : X × X ↦ ℓ.length (C₀.symm w.1) (covectorFromChart C₀ (C₀.symm w.1) w.2))
          (t.symm y, (D y).adjoint η) :=
        (ℓ.contDiffOn_length_covectorFromChart C₀ hC₀).contDiffAt
          ((C₀.open_target.prod isOpen_ne).mem_nhds ⟨htarget y hy, hνne y η hy hη⟩)
      exact ContDiffAt.comp
        (f := fun w : X × X ↦ (t.symm w.1, (D w.1).adjoint w.2))
        (g := fun w : X × X ↦
          ℓ.length (C₀.symm w.1) (covectorFromChart C₀ (C₀.symm w.1) w.2)) (y, η)
        hsource (((hts.contDiffAt (t.open_target.mem_nhds (hZt hy))).comp
          (y, η) contDiffAt_fst).prodMk (hν y η hy))
    have hscale (y η : X) (r : ℝ) : Λ y (r • η) = |r| * Λ y η := by
      dsimp only [Λ]
      rw [map_smul]
      have hcov : covectorFromChart C₀ (C₀.symm (t.symm y)) (r • (D y).adjoint η) =
          r • covectorFromChart C₀ (C₀.symm (t.symm y)) ((D y).adjoint η) := by
        ext v
        change inner ℝ (r • (D y).adjoint η)
          ((mfderiv _ _ C₀ (C₀.symm (t.symm y))) v) =
            r * inner ℝ ((D y).adjoint η) ((mfderiv _ _ C₀ (C₀.symm (t.symm y))) v)
        exact real_inner_smul_left _ _ r
      rw [hcov, ℓ.length_smul]
    let T := K ×ˢ Metric.sphere (0 : X) 1
    have hT : IsCompact T := hK.prod (isCompact_sphere _ _)
    have hunit (η : X) (hη : η ∈ Metric.sphere (0 : X) 1) : η ≠ 0 := by
      intro hzero
      simp only [hzero, Metric.mem_sphere, dist_self, zero_ne_one] at hη
    have hcont : ContinuousOn (Function.uncurry Λ) T := by
      intro w hw
      exact (hΛ w.1 w.2 (hKZ hw.1) (hunit w.2 hw.2)).continuousAt.continuousWithinAt
    obtain ⟨d, hdpos, hlow⟩ := hT.exists_forall_le' hcont (a := 0) (by
      intro w hw
      exact ℓ.length_pos _ _ (hcovne w.1 w.2 (hKZ hw.1) (hunit w.2 hw.2)))
    refine ⟨d⁻¹, ?_⟩
    intro y hy η hη
    have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hdpos) hη
    have hηne := norm_pos_iff.mp hηpos
    let v := ‖η‖⁻¹ • η
    have hv : v ∈ Metric.sphere (0 : X) 1 := by
      simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
    have hvscale : ‖η‖ • v = η := by
      simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
    have hlen : Λ y η = ‖η‖ * Λ y v := by
      calc
        Λ y η = Λ y (‖η‖ • v) := congrArg (Λ y) hvscale.symm
        _ = ‖η‖ * Λ y v := by rw [hscale, abs_of_nonneg (norm_nonneg η)]
    have hlength : 1 ≤ Λ y η := by
      rw [hlen]
      have h := mul_le_mul_of_nonneg_left hη hdpos.le
      rw [mul_inv_cancel₀ hdpos.ne'] at h
      have hl := mul_le_mul_of_nonneg_left (hlow (y, v) ⟨hy, hv⟩) (norm_nonneg η)
      exact h.trans (by simpa only [Function.uncurry, mul_comm] using hl)
    have hsource : globalSymbolInChart E.Fiber F.Fiber p C₀ f₀ g₀
        (t.symm y) ((D y).adjoint η) = globalSymbolInChart E.Fiber F.Fiber a C₀ f₀ g₀
          (t.symm y) ((D y).adjoint η) := by
      dsimp only [globalSymbolInChart]
      rw [hhigh _ _ hlength]
    dsimp only [Q, B₀]
    rw [hformula p q.val hq y (hKZ hy) η, hformula a b.val hb y (hKZ hy) η]
    dsimp only [matrixSymbol, cotangentSymbol]
    rw [hsource]
  · -- Outside the compact exceptional set, full-frequency equality holds on an open neighborhood.
    let Z := Ω ∩ C.symm ⁻¹' Lᶜ
    have hc : ContinuousOn C.symm Ω := C.continuousOn_symm.mono (fun _ hy ↦ hy.1.1)
    have hZ : IsOpen Z := hc.isOpen_inter_preimage hΩ hL.isClosed.isOpen_compl
    refine ⟨Z, hZ, ⟨hz, hzL⟩, Set.inter_subset_left,
      hcriterion Z hZ Set.inter_subset_left ?_⟩
    intro K hKZ _
    refine ⟨0, ?_⟩
    intro y hy η _
    dsimp only [Q, B₀, globalSymbolInChart]
    rw [hexterior (C.symm y) (hKZ hy).2]

end AtiyahSinger
