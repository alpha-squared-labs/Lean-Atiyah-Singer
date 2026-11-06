/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.FrameChange
public import AtiyahSinger.Analysis.GlobalFullSymbolEllipticity
public import AtiyahSinger.Analysis.OpenSymbolCoordinates

/-!
# Full-symbol ellipticity in open transport

Public module ID: M0821.

Quantitative ellipticity is local on the base. At order zero its inverse bounds
are preserved by smooth changes of cotangent coordinates and invertible frame
matrices. These statements concern general full symbols; no homogeneous leading
term or regularization is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped ContDiff Manifold Topology

variable {n r q k l : ℕ}

/-- Compact-local ellipticity can be checked on open neighborhoods of the base. -/
theorem IsEllipticFullSymbol.of_locally {U : Set (EuclideanSpace ℝ (Fin n))}
    {m : ℝ} {p : SymbolFunction n r q}
    (hlocal : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsEllipticFullSymbol V m p) :
    IsEllipticFullSymbol U m p := by
  classical
  choose V hV hxV _hVU hpV using fun x : U ↦ hlocal x.val x.property
  intro K hKU hK
  -- Shrink the neighborhoods before using their compact-local inverse bounds.
  choose L hL hxL hLV using fun x : U ↦ exists_compact_subset (hV x) (hxV x)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : U ↦ interior (L x))
    (fun _ ↦ isOpen_interior) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hxL ⟨x, hKU hx⟩⟩)
  choose R C hR hC hbound using fun x : U ↦ hpV x (L x) (hLV x) (hL x)
  refine ⟨1 + ∑ x ∈ t, R x, ∑ x ∈ t, C x, ?_,
    Finset.sum_nonneg (fun x _ ↦ hC x), ?_⟩
  · have hsum : 0 ≤ ∑ x ∈ t, R x := Finset.sum_nonneg (fun x _ ↦ (hR x).le)
    linarith
  intro x hx ξ hξ
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  -- One radius dominates the finite cover, and summing constants preserves the order.
  have hRy : R y ≤ 1 + ∑ x ∈ t, R x := by
    have hsum := Finset.single_le_sum (fun x _ ↦ (hR x).le) hyt
    linarith
  obtain ⟨hinv, hnorm⟩ := hbound y x (interior_subset hxy) ξ (hRy.trans hξ)
  refine ⟨hinv, hnorm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun x _ ↦ hC x) hyt)
    (Real.rpow_nonneg (by positivity) _)

/-- At order zero, invertible frame changes and smooth cotangent changes preserve ellipticity. -/
theorem isEllipticFullSymbol_matrixSymbol_cotangentSymbol
    (t : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (ht : ContDiffOn ℝ ∞ t t.source) (hts : ContDiffOn ℝ ∞ t.symm t.target)
    (p : SymbolFunction n r q) (hp : IsEllipticFullSymbol t.source 0 p)
    (Z : Set (EuclideanSpace ℝ (Fin n))) (hZ : Z ⊆ t.target)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin l))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (hA : ContinuousOn A Z) (hB : ContinuousOn B Z)
    (hAi : ∀ x ∈ Z, Function.Bijective (A x))
    (hBi : ∀ x ∈ Z, Function.Bijective (B x)) :
    IsEllipticFullSymbol Z 0 (matrixSymbol A B (cotangentSymbol t p)) := by
  intro K hKZ hK
  -- Bound the two inverse frame matrices on this same compact target set.
  have hAinv (x) (hx : x ∈ Z) : (A x).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (A x).toLinearMap (hAi x hx)).toContinuousLinearEquiv, rfl⟩
  have hBinv (x) (hx : x ∈ Z) : (B x).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (B x).toLinearMap (hBi x hx)).toContinuousLinearEquiv, rfl⟩
  have hAc : ContinuousOn (fun x ↦ (A x).inverse) Z := by
    intro x hx
    exact ((hAinv x hx).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
      (hA x hx)
  have hBc : ContinuousOn (fun x ↦ (B x).inverse) Z := by
    intro x hx
    exact ((hBinv x hx).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
      (hB x hx)
  obtain ⟨CA, hCA⟩ := hK.exists_bound_of_continuousOn (hAc.mono hKZ)
  obtain ⟨CB, hCB⟩ := hK.exists_bound_of_continuousOn (hBc.mono hKZ)
  -- The inverse coordinate map sends K to a compact set where the source estimate applies.
  have hKt : K ⊆ t.target := hKZ.trans hZ
  obtain ⟨R, C, hR, hC, hbound⟩ := hp (t.symm '' K)
    (by rintro _ ⟨x, hx, rfl⟩; exact t.map_target (hKt hx))
    (hK.image_of_continuousOn (t.continuousOn_symm.mono hKt))
  have hG : ContinuousOn (fun x ↦ fderiv ℝ t.symm x) t.target :=
    hts.continuousOn_fderiv_of_isOpen t.open_target (by simp)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hG.mono hKt)
  let M : ℝ := max D 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨R * M, max CB 0 * C * max CA 0, mul_pos hR hM, by positivity, ?_⟩
  intro x hx ξ hξ
  let F := fderiv ℝ t (t.symm x)
  let G := fderiv ℝ t.symm x
  -- Differentiating the inverse identity gives a uniform lower bound for the new frequency.
  have hforward := (ht.contDiffAt
    (t.open_source.mem_nhds (t.map_target (hKt hx)))).differentiableAt (by simp)
  have hbackward := (hts.contDiffAt (t.open_target.mem_nhds (hKt hx))).differentiableAt
    (by simp)
  have hright : F.comp G = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply (hforward.hasFDerivAt.comp x hbackward.hasFDerivAt).unique
    apply (hasFDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [t.open_target.mem_nhds (hKt hx)] with y hy
    exact t.right_inv hy
  have hdual : G.adjoint.comp F.adjoint =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg ContinuousLinearMap.adjoint hright
  have hfrequency : ‖ξ‖ ≤ M * ‖F.adjoint ξ‖ := by
    calc
      ‖ξ‖ = ‖G.adjoint (F.adjoint ξ)‖ := by
        rw [← ContinuousLinearMap.comp_apply, hdual, ContinuousLinearMap.id_apply]
      _ ≤ ‖G.adjoint‖ * ‖F.adjoint ξ‖ := G.adjoint.le_opNorm _
      _ ≤ M * ‖F.adjoint ξ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [ContinuousLinearMap.adjoint.norm_map] using
          (hD x hx).trans (le_max_left D 1)
  have hsourceFrequency : R ≤ ‖F.adjoint ξ‖ := by
    nlinarith
  obtain ⟨hpinv, hpnorm⟩ := hbound (t.symm x) ⟨x, hx, rfl⟩ (F.adjoint ξ) hsourceFrequency
  simp only [neg_zero, Real.rpow_zero, mul_one] at hpnorm ⊢
  change (A x |>.comp ((p (t.symm x) (F.adjoint ξ)).comp (B x))).IsInvertible ∧ _
  refine ⟨(hAinv x (hKZ hx)).comp (hpinv.comp (hBinv x (hKZ hx))), ?_⟩
  -- Reverse the actual three matrix factors in the inverse and multiply the compact bounds.
  change ‖((A x).comp ((p (t.symm x) (F.adjoint ξ)).comp (B x))).inverse‖ ≤ _
  rw [(hAinv x (hKZ hx)).inverse_comp_of_left, hpinv.inverse_comp_of_left]
  calc
    ‖((B x).inverse.comp (p (t.symm x) (F.adjoint ξ)).inverse).comp (A x).inverse‖ ≤
        (‖(B x).inverse‖ * ‖(p (t.symm x) (F.adjoint ξ)).inverse‖) * ‖(A x).inverse‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (max CB 0 * C) * max CA 0 :=
      mul_le_mul
        (mul_le_mul ((hCB x hx).trans (le_max_left _ _)) hpnorm (norm_nonneg _) (by positivity))
        ((hCA x hx).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N] [T2Space N]
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

set_option maxHeartbeats 2000000 in

include hα hβ in
/-- Exact open transport and an invertible exterior bundle map preserve full order-zero ellipticity.
The target is a genuine full symbol; the exterior map is only assumed invertible
off the control set. -/
theorem IsEllipticFullGlobalSymbol.of_openTransport
    (p : GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
    (hp : IsEllipticFullGlobalSymbol (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 p)
    (J : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber 0)
    (htransport : ∀ (x : U) η (v : E.Fiber x.val),
      J.val (e x).val η (α x v) = β x
        (p x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v))
    (L : Set N) (hL : IsCompact L) (hLV : L ⊆ (V : Set N))
    (d : ∀ y, G.Fiber y →ₗ[ℂ] H.Fiber y)
    (hd : ∀ y, y ∉ L → Function.Bijective (d y))
    (houtside : ∀ y, y ∉ L → ∀ η v, J.val y η v = d y v) :
    IsEllipticFullGlobalSymbol (r := G.rank) (q := H.rank) G.Fiber H.Fiber 0 J.val := by
  classical
  intro C hC f g _ _
  apply IsEllipticFullSymbol.of_locally
  intro z hz
  by_cases hzV : C.symm z ∈ V
  · -- On the common open region, use the same actual charts and fiber equivalences.
    obtain ⟨C₀, f₀, g₀, hf₀, hg₀, hC₀, Z, t, A, B, hZ, hzZ, hZU, hZt, htS,
      ht, hts, hA, hB, hbijective, hformula⟩ :=
      exists_local_openSymbolInChart E F G H U V e α hα β hβ C hC f g z hz hzV
    let := hf₀
    let := hg₀
    have hsource : IsEllipticFullSymbol t.source 0
        (globalSymbolInChart E.Fiber F.Fiber p C₀ f₀ g₀) := by
      intro K hKt hK
      exact hp C₀ hC₀ f₀ g₀ K (hKt.trans htS) hK
    have hlocal := isEllipticFullSymbol_matrixSymbol_cotangentSymbol t ht hts
      (globalSymbolInChart E.Fiber F.Fiber p C₀ f₀ g₀) hsource Z hZt A B
      hA.continuousOn hB.continuousOn
      (fun y hy ↦ (hbijective y hy).1) (fun y hy ↦ (hbijective y hy).2)
    refine ⟨Z, hZ, hzZ, hZU, ?_⟩
    intro K hKZ hK
    obtain ⟨R, D, hR, hD, hbound⟩ := hlocal K hKZ hK
    refine ⟨R, D, hR, hD, ?_⟩
    intro y hy η hη
    rw [hformula p J.val htransport y (hKZ hy) η]
    exact hbound y hy η hη
  · -- Outside the compact control set, the same symbol is frequency independent and invertible.
    let Z := symbolChartDomain G.Fiber H.Fiber C f g ∩ C.symm ⁻¹' Lᶜ
    have hZ : IsOpen Z := by
      have h := C.isOpen_inter_preimage_symm
        ((f.open_baseSet.inter g.open_baseSet).inter hL.isClosed.isOpen_compl)
      simpa only [Z, symbolChartDomain, Set.preimage_inter, Set.inter_assoc] using h
    have hzZ : z ∈ Z := ⟨hz, fun h ↦ hzV (hLV h)⟩
    let A := fun y ↦ globalSymbolInChart G.Fiber H.Fiber J.val C f g y 0
    have hA : ContinuousOn A Z :=
      (J.property C hC f g).1.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun _ hy ↦ ⟨hy.1, Set.mem_univ _⟩)
    have hAi (y) (hy : y ∈ Z) : (A y).IsInvertible := by
      have heq : ⇑(A y) = fun v ↦
          (g.continuousLinearEquivAt ℂ (C.symm y) hy.1.2)
            (d (C.symm y) ((f.continuousLinearEquivAt ℂ (C.symm y) hy.1.1.2).symm v)) := by
        funext v
        change g.continuousLinearMapAt ℂ (C.symm y)
          (J.val (C.symm y) _ (f.symmL ℂ (C.symm y) v)) = _
        rw [houtside (C.symm y) hy.2]
        rw [← g.coe_continuousLinearEquivAt_eq' (R := ℂ) hy.1.2,
          ← f.symm_continuousLinearEquivAt_eq' (R := ℂ) hy.1.1.2]
        rfl
      have hbij : Function.Bijective (A y) := by
        rw [heq]
        exact (g.continuousLinearEquivAt ℂ (C.symm y) hy.1.2).bijective.comp
          ((hd (C.symm y) hy.2).comp
            (f.continuousLinearEquivAt ℂ (C.symm y) hy.1.1.2).symm.bijective)
      exact ⟨(LinearEquiv.ofBijective (A y).toLinearMap hbij).toContinuousLinearEquiv, rfl⟩
    have hAc : ContinuousOn (fun y ↦ (A y).inverse) Z := by
      intro y hy
      exact ((hAi y hy).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
        (hA y hy)
    have hconst (y) (hy : y ∈ Z) (η) :
        globalSymbolInChart G.Fiber H.Fiber J.val C f g y η = A y := by
      apply ContinuousLinearMap.ext
      intro v
      change g.continuousLinearMapAt ℂ (C.symm y)
        (J.val (C.symm y) _ (f.symmL ℂ (C.symm y) v)) =
        g.continuousLinearMapAt ℂ (C.symm y)
          (J.val (C.symm y) _ (f.symmL ℂ (C.symm y) v))
      rw [houtside (C.symm y) hy.2, houtside (C.symm y) hy.2]
    refine ⟨Z, hZ, hzZ, Set.inter_subset_left, ?_⟩
    intro K hKZ hK
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hAc.mono hKZ)
    refine ⟨1, max D 0, zero_lt_one, le_max_right _ _, ?_⟩
    intro y hy η _hη
    rw [hconst y (hKZ hy) η]
    refine ⟨hAi y (hKZ hy), ?_⟩
    simpa only [neg_zero, Real.rpow_zero, mul_one] using
      (hD y hy).trans (le_max_left D 0)

end AtiyahSinger
