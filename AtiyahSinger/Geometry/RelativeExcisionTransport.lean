/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DensityDiffeomorph
public import AtiyahSinger.Geometry.MetricTransport
public import AtiyahSinger.Geometry.RelativeExcisionData
public import AtiyahSinger.Geometry.RelativeFramePullback
public import AtiyahSinger.Geometry.SmoothBundleMapContinuity
public import AtiyahSinger.Geometry.SmoothBundleMapPullback

/-!
# Relative excision data along a specified open parametrization

Public module ID: M1352.

Transport the original source bundles, exterior frames, fiber pairings and density
through the prescribed diffeomorphism onto an open submanifold. Applying relative
extension there and composing back retains the exact original fiber maps and local
pairings. The density is the actual pushforward, including its Jacobian. These are
the same-witness geometric data used to realize one correction in two environments.
The source and ambient manifolds are Hausdorff and second-countable.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle TopologicalSpace MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

section PullbackComparison

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inversePullback_smooth
    (E : SmoothFiniteComplexBundle (n := n) M)
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N) :
    let G := E.pullback ⟨e.symm, e.symm.continuous⟩ e.symm.contMDiff
    IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
      (E := E.Fiber) (F := (⟨e, e.continuous⟩ : C(M, N)) *ᵖ G.Fiber)
      (fun x ↦ (LinearEquiv.cast (R := ℂ) (M := E.Fiber)
        (e.symm_apply_apply x).symm).toLinearMap) := by
  dsimp only
  rintro d hd _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ j
  let := hd
  let := ht
  have hcolumn := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin E.rank))
    (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ).contMDiff.comp_contMDiffOn
      (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := E.Fiber) d t)
  have hs := hcolumn.mono (fun x
    (hx : x ∈ d.baseSet ∩ (e ⁻¹' (e.symm ⁻¹' t.baseSet))) ↦ by
      change x ∈ d.baseSet ∧ e.symm (e x) ∈ t.baseSet at hx
      exact ⟨hx.1, by simpa only [Diffeomorph.symm_apply_apply] using hx.2⟩)
  apply hs.congr
  intro x hx
  change (t ⟨e.symm (e x),
    cast (congrArg E.Fiber (e.symm_apply_apply x).symm)
      (d.symmL ℂ x (EuclideanSpace.single j 1))⟩).2 =
    (d.coordChangeL ℂ t x) (EuclideanSpace.single j 1)
  rw [show (⟨e.symm (e x),
      cast (congrArg E.Fiber (e.symm_apply_apply x).symm)
        (d.symmL ℂ x (EuclideanSpace.single j 1))⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin E.rank)) E.Fiber) =
      ⟨x, d.symmL ℂ x (EuclideanSpace.single j 1)⟩ from
    TotalSpace.mk_cast (F := EuclideanSpace ℂ (Fin E.rank))
      (E := E.Fiber) (e.symm_apply_apply x).symm _]
  have hxt : x ∈ t.baseSet := by
    simpa only [Set.mem_preimage, Diffeomorph.symm_apply_apply] using hx.2
  rw [d.symmL_apply hx.1]
  exact (d.coordChangeL_apply t ⟨hx.1, hxt⟩ _).symm


end PullbackComparison

variable {n : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
-- Keep both original fiber comparisons and all native pullback geometries in one construction.
/-- Relative excision geometry retains a specified source under its actual open embedding. -/
theorem exists_relative_excision_data_of_diffeomorph
    (E F : SmoothFiniteComplexBundle (n := n) O) (hEF : E.rank = F.rank)
    (U : Opens M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (K L : Set O) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (ν : Measure O) [IsSmoothPositiveMeasure (n := n) ν]
    (c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
    (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (c x).toLinearMap)) :
    let W : Opens O := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
    ∀ (τE : ∀ x : W, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
      (τF : ∀ x : W, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank)),
      IsSmoothBundleMap (n := n) (r := E.rank) (q := E.rank) (M := W)
        (E := ((ContinuousMap.subtypeVal (W : Set O) : W → O) *ᵖ E.Fiber))
        (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τE x).toLinearMap) →
      IsSmoothBundleMap (n := n) (r := F.rank) (q := E.rank) (M := W)
        (E := ((ContinuousMap.subtypeVal (W : Set O) : W → O) *ᵖ F.Fiber))
        (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τF x).toLinearMap) →
      (∀ (x : W) (v : E.Fiber x.val), τF x (c x.val v) = τE x v) →
      ∃ G H : SmoothFiniteComplexBundle (n := n) M,
        G.rank = E.rank ∧ H.rank = F.rank ∧
        ∃ (α : ∀ x : O, E.Fiber x ≃ₗ[ℂ] G.Fiber (e x).val)
          (β : ∀ x : O, F.Fiber x ≃ₗ[ℂ] H.Fiber (e x).val),
          IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank) (M := O)
            (E := E.Fiber)
            (F := ((⟨e, e.continuous⟩ : C(O, U)) : O → U) *ᵖ
              ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
            (fun x ↦ (α x).toLinearMap) ∧
          IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank) (M := O)
            (E := F.Fiber)
            (F := ((⟨e, e.continuous⟩ : C(O, U)) : O → U) *ᵖ
              ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ H.Fiber))
            (fun x ↦ (β x).toLinearMap) ∧
          ∃ d : ∀ x : M, G.Fiber x →L[ℂ] H.Fiber x,
            IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank)
              (fun x ↦ (d x).toLinearMap) ∧
            (∀ (x : O) (v : E.Fiber x), d (e x).val (α x v) = β x (c x v)) ∧
            (∀ x : M, x ∉ (fun x : O ↦ (e x).val) '' K → Function.Bijective (d x)) ∧
            ∃ (g : SmoothHermitianMetric (n := n) (r := G.rank) G.Fiber)
              (l : SmoothHermitianMetric (n := n) (r := H.rank) H.Fiber)
              (μ : Measure M), IsSmoothPositiveMeasure (n := n) μ ∧
              ∃ A : Opens M, (fun x : O ↦ (e x).val) '' L ⊆ (A : Set M) ∧ A ≤ U ∧
                (∀ (x : O), (e x).val ∈ A → ∀ v w : E.Fiber x,
                  g.pairing (e x).val (α x v) (α x w) = h.pairing x v w) ∧
                (∀ (x : O), (e x).val ∈ A → ∀ v w : F.Fiber x,
                  l.pairing (e x).val (β x v) (β x w) = k.pairing x v w) ∧
                (μ.comap (Subtype.val : U → M)).restrict
                    ((Subtype.val : U → M) ⁻¹' (A : Set M)) =
                  (Measure.map e ν).restrict ((Subtype.val : U → M) ⁻¹' (A : Set M)) := by
  classical
  dsimp only
  intro τE τF hτE hτF hτ
  let W : Opens O := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  let f : C(U, O) := ⟨e.symm, e.symm.continuous⟩
  let p : C(O, U) := ⟨e, e.continuous⟩
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let φ : C(O, M) := i.comp p
  let EU := E.pullback f e.symm.contMDiff
  let FU := F.pullback f e.symm.contMDiff
  let K' : Set M := φ '' K
  let L' : Set M := φ '' L
  have hK' : IsCompact K' := hK.image φ.continuous
  have hL' : IsCompact L' := hL.image φ.continuous
  have hL'U : L' ⊆ (U : Set M) := by
    rintro _ ⟨x, _, rfl⟩
    exact (e x).property
  -- Pull back the actual fiber pairings and push forward the actual source density.
  obtain ⟨hU, hhU, _⟩ := h.existsUnique_pullback f e.symm.contMDiff
  obtain ⟨kU, hkU, _⟩ := k.existsUnique_pullback f e.symm.contMDiff
  let νU := Measure.map e ν
  let : IsSmoothPositiveMeasure (n := n) νU := IsSmoothPositiveMeasure.map_diffeomorph ν e
  let cU : ∀ x : U, EU.Fiber x →L[ℂ] FU.Fiber x := fun x ↦ c (f x)
  have hcU : IsSmoothBundleMap (n := n) (r := EU.rank) (q := FU.rank)
      (fun x ↦ (cU x).toLinearMap) := hc.pullback f e.symm.contMDiff
  let V : Opens U := ⟨(Subtype.val : U → M) ⁻¹' K'ᶜ,
    hK'.isClosed.isOpen_compl.preimage continuous_subtype_val⟩
  have hVW (x : V) : f x.val ∈ W := by
    intro hxK
    apply x.property
    refine ⟨e.symm x.val, hxK, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply x.val)
  let σE (x : V) : EU.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank) :=
    τE ⟨f x.val, hVW x⟩
  let σF (x : V) : FU.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank) :=
    τF ⟨f x.val, hVW x⟩
  have hσE := isSmoothBundleMap_exteriorFrame_pullback E W V f
    e.symm.contMDiff hVW τE hτE
  have hσF := isSmoothBundleMap_exteriorFrame_pullback F W V f
    e.symm.contMDiff hVW τF hτF
  -- The existing relative construction extends these precise transported data.
  obtain ⟨G, H, hGr, hHs, a, b, ha, hb, _, _, _, _, _, _, d, hd, hcd, _, hdext,
      g, l, μ, hμ, A, hLA, hAU, hg, hl, hμν⟩ :=
    exists_relative_excision_data U K' L' hK' hL' (Set.image_mono hKL) hL'U
      EU FU hEF hU kU νU cU hcU σE σF hσE hσF
        (fun x v ↦ hτ ⟨f x.val, hVW x⟩ v)
  let a₀ (x : O) : E.Fiber x ≃ₗ[ℂ] EU.Fiber (e x) :=
    LinearEquiv.cast (R := ℂ) (M := E.Fiber) (e.symm_apply_apply x).symm
  let b₀ (x : O) : F.Fiber x ≃ₗ[ℂ] FU.Fiber (e x) :=
    LinearEquiv.cast (R := ℂ) (M := F.Fiber) (e.symm_apply_apply x).symm
  let α (x : O) : E.Fiber x ≃ₗ[ℂ] G.Fiber (e x).val := (a₀ x).trans (a (e x))
  let β (x : O) : F.Fiber x ≃ₗ[ℂ] H.Fiber (e x).val := (b₀ x).trans (b (e x))
  have hα : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
      (E := E.Fiber) (F := (p : O → U) *ᵖ ((i : U → M) *ᵖ G.Fiber))
      (fun x ↦ (α x).toLinearMap) := by
    let GU := (i : U → M) *ᵖ G.Fiber
    let : IsSmoothComplexBundle (n := n) (r := G.rank) GU :=
      isSmoothComplexBundle_pullback G.Fiber i contMDiff_subtype_val
    let : IsSmoothComplexBundle (n := n) (r := EU.rank) ((p : O → U) *ᵖ EU.Fiber) :=
      isSmoothComplexBundle_pullback EU.Fiber p e.contMDiff
    let : IsSmoothComplexBundle (n := n) (r := G.rank) ((p : O → U) *ᵖ GU) :=
      isSmoothComplexBundle_pullback GU p e.contMDiff
    exact IsSmoothBundleMap.comp (E := E.Fiber) (F := (p : O → U) *ᵖ EU.Fiber)
      (H := (p : O → U) *ᵖ GU) (ha.pullback p e.contMDiff)
        (inversePullback_smooth E e)
  have hβ : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
      (E := F.Fiber) (F := (p : O → U) *ᵖ ((i : U → M) *ᵖ H.Fiber))
      (fun x ↦ (β x).toLinearMap) := by
    let HU := (i : U → M) *ᵖ H.Fiber
    let : IsSmoothComplexBundle (n := n) (r := H.rank) HU :=
      isSmoothComplexBundle_pullback H.Fiber i contMDiff_subtype_val
    let : IsSmoothComplexBundle (n := n) (r := FU.rank) ((p : O → U) *ᵖ FU.Fiber) :=
      isSmoothComplexBundle_pullback FU.Fiber p e.contMDiff
    let : IsSmoothComplexBundle (n := n) (r := H.rank) ((p : O → U) *ᵖ HU) :=
      isSmoothComplexBundle_pullback HU p e.contMDiff
    exact IsSmoothBundleMap.comp (E := F.Fiber) (F := (p : O → U) *ᵖ FU.Fiber)
      (H := (p : O → U) *ᵖ HU) (hb.pullback p e.contMDiff)
        (inversePullback_smooth F e)
  refine ⟨G, H, hGr, hHs, α, β, hα, hβ, d, hd, ?_, hdext,
    g, l, μ, hμ, A, hLA, hAU, ?_, ?_, hμν⟩
  · intro x v
    have hcast (y x : O) (hy : y = x) (v : E.Fiber x) :
        c y ((LinearEquiv.cast (R := ℂ) (M := E.Fiber) hy.symm) v) =
          (LinearEquiv.cast (R := ℂ) (M := F.Fiber) hy.symm) (c x v) := by
      subst y
      rfl
    exact (hcd (e x) (a₀ x v)).trans
      (congrArg (b (e x)) (hcast (e.symm (e x)) x (e.symm_apply_apply x) v))
  · intro x hx v w
    have hcast (y x : O) (hy : y = x) (v w : E.Fiber x) :
        h.pairing y ((LinearEquiv.cast (R := ℂ) (M := E.Fiber) hy.symm) v)
          ((LinearEquiv.cast (R := ℂ) (M := E.Fiber) hy.symm) w) = h.pairing x v w := by
      subst y
      rfl
    exact (hg (e x) hx (a₀ x v) (a₀ x w)).trans
      ((hhU (e x) (a₀ x v) (a₀ x w)).trans
        (hcast (e.symm (e x)) x (e.symm_apply_apply x) v w))
  · intro x hx v w
    have hcast (y x : O) (hy : y = x) (v w : F.Fiber x) :
        k.pairing y ((LinearEquiv.cast (R := ℂ) (M := F.Fiber) hy.symm) v)
          ((LinearEquiv.cast (R := ℂ) (M := F.Fiber) hy.symm) w) = k.pairing x v w := by
      subst y
      rfl
    exact (hl (e x) hx (b₀ x v) (b₀ x w)).trans
      ((hkU (e x) (b₀ x v) (b₀ x w)).trans
        (hcast (e.symm (e x)) x (e.symm_apply_apply x) v w))

end AtiyahSinger
