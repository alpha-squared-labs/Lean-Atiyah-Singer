/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantRelativeExcisionData
public import AtiyahSinger.Geometry.RelativeExcisionTransport
public import AtiyahSinger.Geometry.SmoothEquivariantPullback

import all AtiyahSinger.Geometry.RelativeExcisionTransport

/-!
# Equivariant transport of the same relative excision data

Public module ID: M1204.

Inverse pullback along the specified diffeomorphism retains each original
vector and action. The resulting moving-fiber squares are used to transport
the relative geometric construction without changing its chosen witnesses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  {n : ℕ} {O X : Type*} [TopologicalSpace O] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ X]
  [MulAction G O] [ContinuousSMul G O]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G O]
  [MulAction G X] [ContinuousSMul G X]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G X]

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ X] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical inverse-diffeomorphism pullback map retains the original moving-fiber action.
This native comparison is used for both bundles in relative excision transport. -/
theorem ComplexBundle.EquivariantStructure.inverseDiffeomorphPullback_intertwines
    (E : SmoothFiniteComplexBundle (n := n) O)
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ X)
    (hf : ∀ (g : G) (y : X), e.symm (g • y) = g • e.symm y) :
    let f : C(X, O) := ⟨e.symm, e.symm.continuous⟩
    let E' := (f : X → O) *ᵖ E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E'
    let τ := σ.modelPullback f hf
    let a (x : O) := LinearEquiv.cast (R := ℂ) (M := E.Fiber) (e.symm_apply_apply x).symm
    ∀ (g : G) (x : O) (v : E.Fiber x),
      (⟨e (g • x), a (g • x) (σ.linearMap g x v)⟩ : TotalSpace Unit E') =
        ⟨g • e x, τ.linearMap g (e x) (a x v)⟩ := by
  dsimp only
  let f : C(X, O) := ⟨e.symm, e.symm.continuous⟩
  let E' := (f : X → O) *ᵖ E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E'
  let τ := σ.modelPullback f hf
  let a (x : O) := LinearEquiv.cast (R := ℂ) (M := E.Fiber) (e.symm_apply_apply x).symm
  let lift : TotalSpace Unit E' → TotalSpace Unit E.Fiber :=
    fun z ↦ ⟨f z.proj, z.snd⟩
  have hlift : Function.Injective lift := by
    rintro ⟨y, v⟩ ⟨z, w⟩ h
    have hyz : y = z := e.symm.injective (congrArg TotalSpace.proj h)
    subst z
    exact congrArg (TotalSpace.mk y) (TotalSpace.mk_injective (f y) h)
  have hcast (x : O) (v : E.Fiber x) :
      (⟨f (e x), a x v⟩ : TotalSpace Unit E.Fiber) = ⟨x, v⟩ :=
    TotalSpace.mk_cast (F := Unit) (E := E.Fiber) (e.symm_apply_apply x).symm v
  let act (g : G) (z : TotalSpace Unit E.Fiber) : TotalSpace Unit E.Fiber :=
    ⟨g • z.proj, σ.linearMap g z.proj z.snd⟩
  intro g x v
  apply hlift
  change (⟨f (e (g • x)), a (g • x) (σ.linearMap g x v)⟩ : TotalSpace Unit E.Fiber) =
    ⟨f (g • e x), τ.linearMap g (e x) (a x v)⟩
  calc
    (⟨f (e (g • x)), a (g • x) (σ.linearMap g x v)⟩ : TotalSpace Unit E.Fiber) =
        ⟨g • x, σ.linearMap g x v⟩ := hcast (g • x) _
    _ = ⟨g • f (e x), σ.linearMap g (f (e x)) (a x v)⟩ :=
      (congrArg (act g) (hcast x v)).symm
    _ = ⟨f (g • e x), τ.linearMap g (e x) (a x v)⟩ :=
      (σ.modelPullback_lift f hf g (e x) (a x v)).symm

variable [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
  {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

set_option maxHeartbeats 3000000 in
-- Compose the actual inverse-pullback fiber maps with C's original witness tuple.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same equivariant relative data extend through the specified open diffeomorphism. -/
theorem exists_equivariant_relative_excision_data_of_diffeomorph
    (E F : SmoothFiniteComplexBundle (n := n) O) (hEF : E.rank = F.rank)
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
    (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
    (U : Opens M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (hfeq : ∀ (g : G) (y : U), e.symm (g • y) = g • e.symm y)
    (K L : Set O) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L)
    (hKi : ∀ (g : G) (x : O), g • x ∈ K ↔ x ∈ K)
    (W' : Opens M) (hWset : (W' : Set M) = ((fun x : O ↦ (e x).val) '' K)ᶜ)
    [MulAction G W'] [ContinuousSMul G W']
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G W']
    (hW : ∀ (g : G) (x : W'), ((g • x : W') : M) = g • x.val)
    (κ : letI := (modelTopology (EuclideanSpace ℂ (Fin E.rank))
        (Bundle.Trivial W' (EuclideanSpace ℂ (Fin E.rank))))
      EquivariantStructure G (Bundle.Trivial W' (EuclideanSpace ℂ (Fin E.rank))))
    (hκ : κ.IsSmooth (n := n) (r := E.rank) IG)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (ν : Measure O) [IsSmoothPositiveMeasure (n := n) ν]
    (c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
    (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (c x).toLinearMap))
    (hcEq : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (x : O) (v : E.Fiber x),
        c (g • x) (σE.linearMap g x v) = σF.linearMap g x (c x v)) :
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
      (letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
       letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
         (Bundle.Trivial W' (EuclideanSpace ℂ (Fin E.rank)))
       ∀ (g : G) (x : W) (hx : (e x.val).val ∈ W') (v : E.Fiber x.val),
         τE ⟨g • x.val, (hKi g x.val).not.mpr x.property⟩ (σE.linearMap g x.val v) =
           κ.linearMap g ⟨(e x.val).val, hx⟩ (τE x v)) →
      (letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
       letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
         (Bundle.Trivial W' (EuclideanSpace ℂ (Fin E.rank)))
       ∀ (g : G) (x : W) (hx : (e x.val).val ∈ W') (v : F.Fiber x.val),
         τF ⟨g • x.val, (hKi g x.val).not.mpr x.property⟩ (σF.linearMap g x.val v) =
           κ.linearMap g ⟨(e x.val).val, hx⟩ (τF x v)) →
      ∃ E' F' : SmoothFiniteComplexBundle (n := n) M,
        E'.rank = E.rank ∧ F'.rank = F.rank ∧
        ∃ (α : ∀ x : O, E.Fiber x ≃ₗ[ℂ] E'.Fiber (e x).val)
          (β : ∀ x : O, F.Fiber x ≃ₗ[ℂ] F'.Fiber (e x).val),
          IsSmoothBundleMap (n := n) (r := E.rank) (q := E'.rank) (M := O)
            (E := E.Fiber)
            (F := ((⟨e, e.continuous⟩ : C(O, U)) : O → U) *ᵖ
              ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E'.Fiber))
            (fun x ↦ (α x).toLinearMap) ∧
          IsSmoothBundleMap (n := n) (r := F.rank) (q := F'.rank) (M := O)
            (E := F.Fiber)
            (F := ((⟨e, e.continuous⟩ : C(O, U)) : O → U) *ᵖ
              ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F'.Fiber))
            (fun x ↦ (β x).toLinearMap) ∧
          ∃ d : ∀ x : M, E'.Fiber x →L[ℂ] F'.Fiber x,
            IsSmoothBundleMap (n := n) (r := E'.rank) (q := F'.rank)
              (fun x ↦ (d x).toLinearMap) ∧
            (∀ (x : O) (v : E.Fiber x), d (e x).val (α x v) = β x (c x v)) ∧
            (∀ x : M, x ∉ (fun x : O ↦ (e x).val) '' K → Function.Bijective (d x)) ∧
            ∃ (g : SmoothHermitianMetric (n := n) (r := E'.rank) E'.Fiber)
              (l : SmoothHermitianMetric (n := n) (r := F'.rank) F'.Fiber)
              (μ : Measure M), IsSmoothPositiveMeasure (n := n) μ ∧
              ∃ A : Opens M, (fun x : O ↦ (e x).val) '' L ⊆ (A : Set M) ∧ A ≤ U ∧
                (∀ (x : O), (e x).val ∈ A → ∀ v w : E.Fiber x,
                  g.pairing (e x).val (α x v) (α x w) = h.pairing x v w) ∧
                (∀ (x : O), (e x).val ∈ A → ∀ v w : F.Fiber x,
                  l.pairing (e x).val (β x v) (β x w) = k.pairing x v w) ∧
                (μ.comap (Subtype.val : U → M)).restrict
                    ((Subtype.val : U → M) ⁻¹' (A : Set M)) =
                  (Measure.map e ν).restrict ((Subtype.val : U → M) ⁻¹' (A : Set M)) ∧
                letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
                letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
                letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
                letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
                ∃ (ρE : EquivariantStructure G E'.Fiber)
                  (ρF : EquivariantStructure G F'.Fiber),
                  ρE.IsSmooth (n := n) (r := E'.rank) IG ∧
                  ρF.IsSmooth (n := n) (r := F'.rank) IG ∧
                  (∀ (g : G) (x : O) (v : E.Fiber x),
                    (⟨(e (g • x)).val, α (g • x) (σE.linearMap g x v)⟩ :
                        TotalSpace Unit E'.Fiber) =
                      ⟨g • (e x).val, ρE.linearMap g (e x).val (α x v)⟩) ∧
                  (∀ (g : G) (x : O) (v : F.Fiber x),
                    (⟨(e (g • x)).val, β (g • x) (σF.linearMap g x v)⟩ :
                        TotalSpace Unit F'.Fiber) =
                      ⟨g • (e x).val, ρF.linearMap g (e x).val (β x v)⟩) ∧
                  ∀ (g : G) (x : M) (v : E'.Fiber x),
                    d (g • x) (ρE.linearMap g x v) = ρF.linearMap g x (d x v) := by
  classical
  dsimp only
  intro τE τF hτE hτF hτ hτEeq hτFeq
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
  obtain ⟨hmetricU, hhU, _⟩ := h.existsUnique_pullback f e.symm.contMDiff
  obtain ⟨kU, hkU, _⟩ := k.existsUnique_pullback f e.symm.contMDiff
  let νU := Measure.map e ν
  let : IsSmoothPositiveMeasure (n := n) νU := IsSmoothPositiveMeasure.map_diffeomorph ν e
  let cU : ∀ x : U, EU.Fiber x →L[ℂ] FU.Fiber x := fun x ↦ c (f x)
  have hcU : IsSmoothBundleMap (n := n) (r := EU.rank) (q := FU.rank)
      (fun x ↦ (cU x).toLinearMap) := hc.pullback f e.symm.contMDiff
  have hWident : W' = ⟨K'ᶜ, hK'.isClosed.isOpen_compl⟩ := SetLike.coe_injective hWset
  subst W'
  let W' : Opens M := ⟨K'ᶜ, hK'.isClosed.isOpen_compl⟩
  let V := openRefinementPiece U W'
  have hVW (x : V) : f x.val ∈ W := by
    intro hxK
    apply x.property
    refine ⟨e.symm x.val, hxK, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply x.val)
  let frameE (x : V) : EU.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank) :=
    τE ⟨f x.val, hVW x⟩
  let frameF (x : V) : FU.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank) :=
    τF ⟨f x.val, hVW x⟩
  have hframeE := isSmoothBundleMap_exteriorFrame_pullback E W V f
    e.symm.contMDiff hVW τE hτE
  have hframeF := isSmoothBundleMap_exteriorFrame_pullback F W V f
    e.symm.contMDiff hVW τF hτF
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank))
    (Bundle.Trivial W' (EuclideanSpace ℂ (Fin E.rank)))
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) ((f : U → O) *ᵖ E.Fiber)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((f : U → O) *ᵖ F.Fiber)
  let ρEU := σE.modelPullback f hfeq
  let ρFU := σF.modelPullback f hfeq
  have hρEU := σE.modelPullback_isSmooth IG hσE f hfeq e.symm.contMDiff
  have hρFU := σF.modelPullback_isSmooth IG hσF f hfeq e.symm.contMDiff
  -- Pulling the original multiplier back preserves its actual moving-fiber square.
  have hcUEq (g : G) (x : U) (v : EU.Fiber x) :
      cU (g • x) (ρEU.linearMap g x v) = ρFU.linearMap g x (cU x v) := by
    let D : TotalSpace Unit E.Fiber → TotalSpace Unit F.Fiber :=
      fun z ↦ ⟨z.proj, c z.proj z.snd⟩
    apply TotalSpace.mk_injective (F := Unit) (f (g • x))
    exact (congrArg D (σE.modelPullback_lift f hfeq g x v)).trans
      ((congrArg (TotalSpace.mk (g • f x)) (hcEq g (f x) v)).trans
        (σF.modelPullback_lift f hfeq g x (c (f x) v)).symm)
  let := openRefinementMulAction U W' hU hW
  -- The supplied exterior frames intertwine the identical target exterior action κ.
  have frame_intertwines (D : SmoothFiniteComplexBundle (n := n) O)
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
        EquivariantStructure G D.Fiber)
      (τ : ∀ x : W, D.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
      (hτeq : letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
        ∀ (g : G) (x : W) (hx : (e x.val).val ∈ W') (v : D.Fiber x.val),
          τ ⟨g • x.val, (hKi g x.val).not.mpr x.property⟩ (σ.linearMap g x.val v) =
            κ.linearMap g ⟨(e x.val).val, hx⟩ (τ x v)) :
      letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) ((f : U → O) *ᵖ D.Fiber)
      ∀ (g : G) (x : V) (v : D.Fiber (f x.val)),
        τ ⟨f (g • x).val, hVW (g • x)⟩ ((σ.modelPullback f hfeq).linearMap g x.val v) =
          κ.linearMap g ⟨x.val.val, x.property⟩ (τ ⟨f x.val, hVW x⟩ v) := by
    let := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin D.rank)) ((f : U → O) *ᵖ D.Fiber)
    intro g x v
    let evalFrame (z : TotalSpace Unit D.Fiber) : EuclideanSpace ℂ (Fin E.rank) :=
      if hz : z.proj ∈ W then τ ⟨z.proj, hz⟩ z.snd else 0
    have hmove := congrArg evalFrame (σ.modelPullback_lift f hfeq g x.val v)
    have hgo : g • f x.val ∈ W := (hKi g (f x.val)).not.mpr (hVW x)
    change (if hz : f (g • x).val ∈ W then
        τ ⟨f (g • x).val, hz⟩ ((σ.modelPullback f hfeq).linearMap g x.val v) else 0) =
      (if hz : g • f x.val ∈ W then τ ⟨g • f x.val, hz⟩
        (σ.linearMap g (f x.val) v) else 0) at hmove
    rw [dite_eq_left (hVW (g • x)), dite_eq_left hgo] at hmove
    have hx : (e (f x.val)).val ∈ W' := by
      change (e (e.symm x.val)).val ∈ W'
      rw [e.apply_symm_apply]
      exact x.property
    have hw : (⟨(e (f x.val)).val, hx⟩ : W') = ⟨x.val.val, x.property⟩ := by
      apply Subtype.ext
      change (e (e.symm x.val)).val = x.val.val
      exact congrArg Subtype.val (e.apply_symm_apply x.val)
    have hτ := hτeq g ⟨f x.val, hVW x⟩ hx v
    rw [hw] at hτ
    exact hmove.trans hτ
  -- Choose C's relative tuple once, now with its exact interior and exterior actions.
  obtain ⟨E', F', hGr, hHs, a, b, ha, hb, _, _, _, _, _, _, d, hd, hcd, _, hdext,
      g, l, μ, hμ, A, hLA, hAU, hg, hl, hμν,
      ρE, ρF, hρE, hρF, hρEUeq, hρFUeq, _hρEW, _hρFW, hdEq⟩ :=
    exists_equivariant_relative_excision_data IG U K' L' hK' hL'
      (Set.image_mono hKL) hL'U W' rfl hU hW EU FU hEF ρEU ρFU hρEU hρFU κ hκ
      hmetricU kU νU cU hcU hcUEq frameE frameF hframeE hframeF
      (fun x v ↦ hτ ⟨f x.val, hVW x⟩ v)
      (frame_intertwines E σE τE hτEeq) (frame_intertwines F σF τF hτFeq)
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let a₀ (x : O) : E.Fiber x ≃ₗ[ℂ] EU.Fiber (e x) :=
    LinearEquiv.cast (R := ℂ) (M := E.Fiber) (e.symm_apply_apply x).symm
  let b₀ (x : O) : F.Fiber x ≃ₗ[ℂ] FU.Fiber (e x) :=
    LinearEquiv.cast (R := ℂ) (M := F.Fiber) (e.symm_apply_apply x).symm
  let α (x : O) : E.Fiber x ≃ₗ[ℂ] E'.Fiber (e x).val := (a₀ x).trans (a (e x))
  let β (x : O) : F.Fiber x ≃ₗ[ℂ] F'.Fiber (e x).val := (b₀ x).trans (b (e x))
  have hα : IsSmoothBundleMap (n := n) (r := E.rank) (q := E'.rank)
      (E := E.Fiber) (F := (p : O → U) *ᵖ ((i : U → M) *ᵖ E'.Fiber))
      (fun x ↦ (α x).toLinearMap) := by
    let GU := (i : U → M) *ᵖ E'.Fiber
    let : IsSmoothComplexBundle (n := n) (r := E'.rank) GU :=
      isSmoothComplexBundle_pullback E'.Fiber i contMDiff_subtype_val
    let : IsSmoothComplexBundle (n := n) (r := EU.rank) ((p : O → U) *ᵖ EU.Fiber) :=
      isSmoothComplexBundle_pullback EU.Fiber p e.contMDiff
    let : IsSmoothComplexBundle (n := n) (r := E'.rank) ((p : O → U) *ᵖ GU) :=
      isSmoothComplexBundle_pullback GU p e.contMDiff
    exact IsSmoothBundleMap.comp (E := E.Fiber) (F := (p : O → U) *ᵖ EU.Fiber)
      (H := (p : O → U) *ᵖ GU) (ha.pullback p e.contMDiff)
        (inversePullback_smooth E e)
  have hβ : IsSmoothBundleMap (n := n) (r := F.rank) (q := F'.rank)
      (E := F.Fiber) (F := (p : O → U) *ᵖ ((i : U → M) *ᵖ F'.Fiber))
      (fun x ↦ (β x).toLinearMap) := by
    let HU := (i : U → M) *ᵖ F'.Fiber
    let : IsSmoothComplexBundle (n := n) (r := F'.rank) HU :=
      isSmoothComplexBundle_pullback F'.Fiber i contMDiff_subtype_val
    let : IsSmoothComplexBundle (n := n) (r := FU.rank) ((p : O → U) *ᵖ FU.Fiber) :=
      isSmoothComplexBundle_pullback FU.Fiber p e.contMDiff
    let : IsSmoothComplexBundle (n := n) (r := F'.rank) ((p : O → U) *ᵖ HU) :=
      isSmoothComplexBundle_pullback HU p e.contMDiff
    exact IsSmoothBundleMap.comp (E := F.Fiber) (F := (p : O → U) *ᵖ FU.Fiber)
      (H := (p : O → U) *ᵖ HU) (hb.pullback p e.contMDiff)
        (inversePullback_smooth F e)
  refine ⟨E', F', hGr, hHs, α, β, hα, hβ, d, hd, ?_, hdext,
    g, l, μ, hμ, A, hLA, hAU, ?_, ?_, hμν, ρE, ρF, hρE, hρF, ?_, ?_, hdEq⟩
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
  · intro g x v
    let T : TotalSpace Unit ((f : U → O) *ᵖ E.Fiber) → TotalSpace Unit E'.Fiber :=
      fun z ↦ ⟨z.proj.val, a z.proj z.snd⟩
    have h := ComplexBundle.EquivariantStructure.inverseDiffeomorphPullback_intertwines
      E σE e hfeq g x v
    exact (congrArg T h).trans (hρEUeq g (e x) (a₀ x v)).symm
  · intro g x v
    let T : TotalSpace Unit ((f : U → O) *ᵖ F.Fiber) → TotalSpace Unit F'.Fiber :=
      fun z ↦ ⟨z.proj.val, b z.proj z.snd⟩
    have h := ComplexBundle.EquivariantStructure.inverseDiffeomorphPullback_intertwines
      F σF e hfeq g x v
    exact (congrArg T h).trans (hρFUeq g (e x) (b₀ x v)).symm

end AtiyahSinger
