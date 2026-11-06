/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantNativeExteriorFrames
public import AtiyahSinger.Geometry.EquivariantRelativeExcisionTransport
public import AtiyahSinger.Geometry.InvariantOpenAction

/-!
# Relative extension from the original native finite-representation source

Public module ID: M1195.

The same source multiplier determines both exterior frames. Restriction to
an invariant open submanifold and the specified diffeomorphism then feed the
actual relative extension construction. The returned fiber maps, pairings,
density and smooth actions retain the original source data near the full
finite-piece support, while the exterior uses the same finite representation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G]
  {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [T2Space N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]

attribute [local instance] isSmoothPositiveMeasure_comap_opens trivialTopology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- The original source frames and pairings feed C through the same specified diffeomorphism.
/-- A native relative symbol source supplies all actual equivariant extension geometry. -/
theorem exists_equivariant_native_relative_excision_data
    (ρ : FiniteContinuousRepresentation G)
    (hT : IsSmoothComplexBundle (n := n) (r := ρ.dimension)
      (Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))))
    (F : SmoothFiniteComplexBundle (n := n) M) (hF : F.rank = ρ.dimension)
    (U : Opens M) (V : Opens N)
    [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    [MulAction G V] [ContinuousSMul G V]
    [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G V]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (hV : ∀ (g : G) (x : V), ((g • x : V) : N) = g • x.val)
    (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
    (he : ∀ (g : G) (x : U), (e (g • x)).val = g • (e x).val)
    (K L : Set M) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L)
    (hLU : L ⊆ U) (hKi : ∀ (g : G) (x : M), g • x ∈ K ↔ x ∈ K)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] :
    letI := hT
    let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
    letI := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) T
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (σT : EquivariantStructure G T) (σF : EquivariantStructure G F.Fiber)
      (_hσT : σT.IsSmooth (n := n) (r := ρ.dimension) 𝓘(ℝ, VG))
      (_hσF : σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG))
      (_hσTvalue : ∀ (g : G) (x : M) (v : T x), σT.linearMap g x v =
        (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
          (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)))
      (c : Hom T F.Fiber)
      (_hc : IsSmoothBundleMap (n := n) (r := ρ.dimension) (q := F.rank) c.linearMap)
      (_hcg : c.IsEquivariant σT σF)
      (_hcext : ∀ x ∉ K, Function.Bijective (c.linearMap x))
      (h : SmoothHermitianMetric (n := n) (r := ρ.dimension) T)
      (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber),
      ∃ E' F' : SmoothFiniteComplexBundle (n := n) N,
        E'.rank = ρ.dimension ∧ F'.rank = F.rank ∧
        ∃ (α : ∀ x : U, T x.val ≃ₗ[ℂ] E'.Fiber (e x).val)
          (β : ∀ x : U, F.Fiber x.val ≃ₗ[ℂ] F'.Fiber (e x).val),
          IsSmoothBundleMap (M := U) (n := n) (r := ρ.dimension) (q := E'.rank)
            (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ T))
            (F := ((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
              ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ E'.Fiber))
            (fun x ↦ (α x).toLinearMap) ∧
          IsSmoothBundleMap (M := U) (n := n) (r := F.rank) (q := F'.rank)
            (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber))
            (F := ((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
              ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F'.Fiber))
            (fun x ↦ (β x).toLinearMap) ∧
          ∃ d : ∀ y : N, E'.Fiber y →L[ℂ] F'.Fiber y,
            IsSmoothBundleMap (M := N) (n := n) (r := E'.rank) (q := F'.rank)
              (fun y ↦ (d y).toLinearMap) ∧
            (∀ (x : U) (v : T x.val), d (e x).val (α x v) = β x (c.linearMap x.val v)) ∧
            (∀ y ∉ (fun x : U ↦ (e x).val) '' ((Subtype.val : U → M) ⁻¹' K),
              Function.Bijective (d y)) ∧
            ∃ (h' : SmoothHermitianMetric (n := n) (r := E'.rank) E'.Fiber)
              (k' : SmoothHermitianMetric (n := n) (r := F'.rank) F'.Fiber)
              (ν : Measure N), IsSmoothPositiveMeasure (n := n) ν ∧
              ∃ A : Opens N,
                (fun x : U ↦ (e x).val) '' ((Subtype.val : U → M) ⁻¹' L) ⊆ A ∧
                A ≤ V ∧
                (∀ (x : U), (e x).val ∈ A → ∀ v w : T x.val,
                  h'.pairing (e x).val (α x v) (α x w) = h.pairing x.val v w) ∧
                (∀ (x : U), (e x).val ∈ A → ∀ v w : F.Fiber x.val,
                  k'.pairing (e x).val (β x v) (β x w) = k.pairing x.val v w) ∧
                (ν.comap (Subtype.val : V → N)).restrict
                    ((Subtype.val : V → N) ⁻¹' (A : Set N)) =
                  (Measure.map e (μ.comap (Subtype.val : U → M))).restrict
                    ((Subtype.val : V → N) ⁻¹' (A : Set N)) ∧
                letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
                letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
                ∃ (τE : EquivariantStructure G E'.Fiber)
                  (τF : EquivariantStructure G F'.Fiber),
                  τE.IsSmooth (n := n) (r := E'.rank) 𝓘(ℝ, VG) ∧
                  τF.IsSmooth (n := n) (r := F'.rank) 𝓘(ℝ, VG) ∧
                  (∀ (g : G) (x : U) (v : T x.val),
                    (⟨(e (g • x)).val, α (g • x)
                      (cast (congrArg T (hU g x).symm) (σT.linearMap g x.val v))⟩ :
                        TotalSpace Unit E'.Fiber) =
                      ⟨g • (e x).val, τE.linearMap g (e x).val (α x v)⟩) ∧
                  (∀ (g : G) (x : U) (v : F.Fiber x.val),
                    (⟨(e (g • x)).val, β (g • x)
                      (cast (congrArg F.Fiber (hU g x).symm) (σF.linearMap g x.val v))⟩ :
                        TotalSpace Unit F'.Fiber) =
                      ⟨g • (e x).val, τF.linearMap g (e x).val (β x v)⟩) ∧
                  ∀ (g : G) (y : N) (v : E'.Fiber y),
                    d (g • y) (τE.linearMap g y v) = τF.linearMap g y (d y v) := by
  classical
  dsimp only
  let := hT
  let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
  let E : SmoothFiniteComplexBundle (n := n) M := { rank := ρ.dimension, Fiber := T }
  let := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) T
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  intro σT σF hσT hσF hσTvalue c hc hcg hcext h k
  let IG := 𝓘(ℝ, VG)
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let EU := E.pullback i contMDiff_subtype_val
  let FU := F.pullback i contMDiff_subtype_val
  let KU : Set U := i ⁻¹' K
  let LU : Set U := i ⁻¹' L
  have hKU : K ⊆ U := hKL.trans hLU
  have hKr : K ⊆ Set.range i := fun x hx ↦ ⟨⟨x, hKU hx⟩, rfl⟩
  have hLr : L ⊆ Set.range i := fun x hx ↦ ⟨⟨x, hLU hx⟩, rfl⟩
  have hKUc : IsCompact KU :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKr
  have hLUc : IsCompact LU :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hL hLr
  have hKUi (g : G) (x : U) : g • x ∈ KU ↔ x ∈ KU := by
    change (g • x : U).val ∈ K ↔ x.val ∈ K
    rw [hU]
    exact hKi g x.val
  let j : C(U, N) := ⟨fun x ↦ (e x).val, continuous_subtype_val.comp e.continuous⟩
  let KN : Set N := j '' KU
  have hKN : IsCompact KN := hKUc.image j.continuous
  have hKNi (g : G) (y : N) : g • y ∈ KN ↔ y ∈ KN := by
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨g⁻¹ • x, (hKUi g⁻¹ x).mpr hx, ?_⟩
      change (e (g⁻¹ • x)).val = y
      change (e x).val = g • y at hxy
      rw [he, hxy, inv_smul_smul]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g • x, (hKUi g x).mpr hx, he g x⟩
  let WN : Opens N := ⟨KNᶜ, hKN.isClosed.isOpen_compl⟩
  have hWNi (g : G) (y : N) : g • y ∈ WN ↔ y ∈ WN := (hKNi g y).not
  let := invariantOpenMulAction WN hWNi
  let := continuousSMul_invariantOpen WN hWNi
  let := contMDiffSMul_invariantOpen (n := n) IG WN hWNi
  have hWN (g : G) (y : WN) : ((g • y : WN) : N) = g • y.val := rfl
  -- The target exterior carries the actual original finite representation in its native model.
  obtain ⟨hTN, κ, hκ, eκ, heκ, hκvalue, _hκframe⟩ :=
    exists_smooth_finiteRepresentation_bundle (VG := VG) (n := n) (M := WN) ρ
  let := hTN
  let := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension))
    (Bundle.Trivial WN (EuclideanSpace ℂ (Fin ρ.dimension)))
  have hκformula (g : G) (y : WN) (v : EuclideanSpace ℂ (Fin ρ.dimension)) :
      κ.linearMap g y v = (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
        (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)) := by
    have hh := heκ g y ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)
    change eκ.linearEquiv (g • y)
        (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)) =
      κ.linearMap g y (eκ.linearEquiv y ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v)) at hh
    rw [hκvalue, hκvalue] at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh.symm
  let := modelTopology (EuclideanSpace ℂ (Fin EU.rank)) EU.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin FU.rank)) FU.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) ((i : U → M) *ᵖ T)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((i : U → M) *ᵖ F.Fiber)
  let σEU : EquivariantStructure G EU.Fiber := σT.modelPullback i hU
  let σFU : EquivariantStructure G FU.Fiber := σF.modelPullback i hU
  have hσEU := σT.modelPullback_isSmooth IG hσT i hU contMDiff_subtype_val
  have hσFU := σF.modelPullback_isSmooth IG hσF i hU contMDiff_subtype_val
  let cU (x : U) : EU.Fiber x →L[ℂ] FU.Fiber x :=
    (c.linearMap x.val).toContinuousLinearMap
  have hcU : IsSmoothBundleMap (n := n) (r := EU.rank) (q := FU.rank)
      (fun x ↦ (cU x).toLinearMap) := hc.pullback i contMDiff_subtype_val
  have hcUg (g : G) (x : U) (v : EU.Fiber x) :
      cU (g • x) (σEU.linearMap g x v) = σFU.linearMap g x (cU x v) := by
    let D : TotalSpace Unit T → TotalSpace Unit F.Fiber :=
      fun z ↦ ⟨z.proj, c.linearMap z.proj z.snd⟩
    apply TotalSpace.mk_injective (F := Unit) (i (g • x))
    exact (congrArg D (σT.modelPullback_lift i hU g x v)).trans
      ((congrArg (TotalSpace.mk (g • i x)) (hcg g (i x) v)).trans
        (σF.modelPullback_lift i hU g x (cU x v)).symm)
  obtain ⟨hUmetric, hhU, _⟩ := h.existsUnique_pullback i contMDiff_subtype_val
  obtain ⟨kUmetric, hkU, _⟩ := k.existsUnique_pullback i contMDiff_subtype_val
  let μU := μ.comap (Subtype.val : U → M)
  -- Pull back the actual exterior frames determined by c, retaining their canonical trivial target.
  obtain ⟨τT, τF, hτT, hτF, hτc, hτTg, hτFg⟩ :=
    exists_equivariant_native_exterior_frames ρ hT F σT σF hσTvalue K hK.isClosed hKi
      c hc hcg hcext
  let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  let WU : Opens U := ⟨KUᶜ, hKUc.isClosed.isOpen_compl⟩
  have hWU (x : WU) : i x.val ∈ W := x.property
  let τEU (x : WU) := τT ⟨i x.val, hWU x⟩
  let τFU (x : WU) := τF ⟨i x.val, hWU x⟩
  have hτEU := isSmoothBundleMap_exteriorFrame_pullback E W WU i
    contMDiff_subtype_val hWU τT hτT
  have hτFU := isSmoothBundleMap_exteriorFrame_pullback F W WU i
    contMDiff_subtype_val hWU τF hτF
  have hWUi (g : G) (x : WU) : i (g • x.val) ∈ W := by
    change (g • x.val : U).val ∉ K
    rw [hU]
    exact (hKi g x.val.val).not.mpr (hWU x)
  have frame_intertwines (D : SmoothFiniteComplexBundle (n := n) M)
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
        EquivariantStructure G D.Fiber)
      (τ : ∀ x : W, D.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin ρ.dimension))
      (hτg : letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
        ∀ (g : G) (x : W) (v : D.Fiber x.val),
          τ ⟨g • x.val, (hKi g x.val).not.mpr x.property⟩ (σ.linearMap g x.val v) =
            (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
              (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) (τ x v)))) :
      letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) ((i : U → M) *ᵖ D.Fiber)
      ∀ (g : G) (x : WU) (hx : (e x.val).val ∈ WN) (v : D.Fiber x.val.val),
        τ ⟨i (g • x.val), hWUi g x⟩
            ((σ.modelPullback i hU).linearMap g x.val v) =
          κ.linearMap g ⟨(e x.val).val, hx⟩ (τ ⟨i x.val, hWU x⟩ v) := by
    let := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin D.rank)) ((i : U → M) *ᵖ D.Fiber)
    intro g x hx v
    let evalFrame (z : TotalSpace Unit D.Fiber) : EuclideanSpace ℂ (Fin ρ.dimension) :=
      if hz : z.proj ∈ W then τ ⟨z.proj, hz⟩ z.snd else 0
    have hmove := congrArg evalFrame (σ.modelPullback_lift i hU g x.val v)
    have hgo : g • i x.val ∈ W := (hKi g (i x.val)).not.mpr (hWU x)
    have hgi : i (g • x.val) ∈ W := by
      change (g • x.val : U).val ∉ K
      rw [hU]
      exact hgo
    change (if hz : i (g • x.val) ∈ W then
        τ ⟨i (g • x.val), hz⟩ ((σ.modelPullback i hU).linearMap g x.val v) else 0) =
      (if hz : g • i x.val ∈ W then
        τ ⟨g • i x.val, hz⟩ (σ.linearMap g (i x.val) v) else 0) at hmove
    rw [dite_eq_left hgi, dite_eq_left hgo] at hmove
    exact hmove.trans ((hτg g ⟨i x.val, hWU x⟩ v).trans (hκformula g _ _).symm)
  have hfeq (g : G) (y : V) : e.symm (g • y) = g • e.symm y := by
    apply e.injective
    apply Subtype.ext
    change (e (e.symm (g • y))).val = (e (g • e.symm y)).val
    rw [e.apply_symm_apply, he, e.apply_symm_apply, hV]
  obtain ⟨E', F', hE', hF', α, β, hα, hβ, d, hd, hcd, hdext,
      h', k', ν, hν, A, hLA, hAV, hαmetric, hβmetric, hmeasure,
      τE, τF', hτE, hτF', hαg, hβg, hdg⟩ :=
    exists_equivariant_relative_excision_data_of_diffeomorph IG EU FU hF.symm
      σEU σFU hσEU hσFU V e hV hfeq KU LU hKUc hLUc (fun _ hx ↦ hKL hx) hKUi WN rfl hWN
      κ hκ hUmetric kUmetric μU cU hcU hcUg τEU τFU hτEU hτFU
      (fun x v ↦ hτc ⟨i x.val, hWU x⟩ v)
      (frame_intertwines E σT τT hτTg) (frame_intertwines F σF τF hτFg)
  refine ⟨E', F', hE', hF', α, β, hα, hβ, d, hd, hcd, hdext,
    h', k', ν, hν, A, hLA, hAV, ?_, ?_, hmeasure, τE, τF', hτE, hτF', ?_, ?_, hdg⟩
  · intro x hx v w
    exact (hαmetric x hx v w).trans (hhU x v w)
  · intro x hx v w
    exact (hβmetric x hx v w).trans (hkU x v w)
  · intro g x v
    have hcast : σEU.linearMap g x v =
        cast (congrArg T (hU g x).symm) (σT.linearMap g x.val v) := by
      have hmove := σT.modelPullback_lift i hU g x v
      have heq {y z : M} (hyz : y = z) (w : T z) :
          (⟨y, cast (congrArg T hyz.symm) w⟩ : TotalSpace Unit T) = ⟨z, w⟩ := by
        subst z
        rfl
      exact TotalSpace.mk_injective (i (g • x)) (hmove.trans (heq (hU g x) _).symm)
    rw [← hcast]
    exact hαg g x v
  · intro g x v
    have hcast : σFU.linearMap g x v =
        cast (congrArg F.Fiber (hU g x).symm) (σF.linearMap g x.val v) := by
      have hmove := σF.modelPullback_lift i hU g x v
      have heq {y z : M} (hyz : y = z) (w : F.Fiber z) :
          (⟨y, cast (congrArg F.Fiber hyz.symm) w⟩ : TotalSpace Unit F.Fiber) = ⟨z, w⟩ := by
        subst z
        rfl
      exact TotalSpace.mk_injective (i (g • x)) (hmove.trans (heq (hU g x) _).symm)
    rw [← hcast]
    exact hβg g x v

end AtiyahSinger
