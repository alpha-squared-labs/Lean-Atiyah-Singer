/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantExteriorBundleExtension
public import AtiyahSinger.Geometry.RelativeExcisionData

/-!
# Equivariant actions on the same relative excision data

Public module ID: M1203.

The original relative construction fixes the extended bundles, interior and
exterior frames, operator, metrics and measure at once. We put smooth actions
on those same bundles by conjugating the supplied actions in those frames.
Their overlap identity then makes the original extended operator equivariant.
No new geometric witnesses replace the metric and density comparisons.

Source: the relative equivariant refinement of SG III.13.4. The metrics and
ambient density need not be invariant; only the given bundle actions are glued.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

set_option maxHeartbeats 2400000 in
-- Compare the two moving-fiber actions on the original specified frames.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [T2Space M] in
private theorem exists_action_on_relative_bundle
    {s : ℕ} (U W : Opens M) (hcover : (U : Set M) ∪ (W : Set M) = Set.univ)
    [MulAction G U] [ContinuousSMul G U] [ContMDiffSMul IG I ∞ G U]
    [MulAction G W] [ContinuousSMul G W] [ContMDiffSMul IG I ∞ G W]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hW : ∀ (g : G) (x : W), ((g • x : W) : M) = g • (x : M))
    (E : SmoothFiniteComplexBundle (n := n) U)
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (hσ : σ.IsSmooth (n := n) (r := E.rank) IG)
    (κ :
      letI := modelTopology (EuclideanSpace ℂ (Fin s))
        (Bundle.Trivial W (EuclideanSpace ℂ (Fin s)))
      EquivariantStructure G (Bundle.Trivial W (EuclideanSpace ℂ (Fin s))))
    (hκ : κ.IsSmooth (M := W) (n := n) (r := s) IG)
    (a : ∀ x : openRefinementPiece U W,
      E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin s))
    (haeq :
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin s))
        (Bundle.Trivial W (EuclideanSpace ℂ (Fin s)))
      letI := openRefinementMulAction U W hU hW
      ∀ (g : G) (x : openRefinementPiece U W) (v : E.Fiber x.val),
        a (g • x) (σ.linearMap g x.val v) =
          κ.linearMap g ⟨x.val.val, x.property⟩ (a x v))
    (F : SmoothFiniteComplexBundle (n := n) M)
    (e : ∀ x : U, E.Fiber x ≃ₗ[ℂ] F.Fiber x.val)
    (he : IsSmoothBundleMap (M := U) (n := n) (r := E.rank) (q := F.rank)
      (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber))
      (fun x ↦ (e x).toLinearMap))
    (b : ∀ x : W, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin s))
    (hb : IsSmoothBundleMap (M := W) (n := n) (r := F.rank) (q := s)
      (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ F.Fiber))
      (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin s)))
      (fun x ↦ (b x).toLinearMap))
    (hab : ∀ (x : openRefinementPiece U W) (v : E.Fiber x.val),
      b ⟨x.val.val, x.property⟩ (e x.val v) = a x v) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin s))
      (Bundle.Trivial W (EuclideanSpace ℂ (Fin s)))
    ∃ ρ : EquivariantStructure G F.Fiber, ρ.IsSmooth (n := n) (r := F.rank) IG ∧
      (∀ (g : G) (x : U) (v : E.Fiber x),
        (⟨g • x.val, ρ.linearMap g x.val (e x v)⟩ : TotalSpace Unit F.Fiber) =
          ⟨((g • x : U) : M), e (g • x) (σ.linearMap g x v)⟩) ∧
      ∀ (g : G) (x : W) (v : F.Fiber x.val),
        (⟨g • x.val, ρ.linearMap g x.val v⟩ : TotalSpace Unit F.Fiber) =
          ⟨((g • x : W) : M), (b (g • x)).symm (κ.linearMap g x (b x v))⟩ := by
  classical
  let V := openRefinementPiece U W
  let Model := EuclideanSpace ℂ (Fin s)
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology Model (Bundle.Trivial W Model)
  let p : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let q : C(W, M) := ContinuousMap.subtypeVal (W : Set M)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((p : U → M) *ᵖ F.Fiber)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((q : W → M) *ᵖ F.Fiber)
  obtain ⟨e₀, he₀⟩ := IsSmoothBundleMap.exists_iso (M := U) (n := n) (r := E.rank) (q := F.rank)
    (E := E.Fiber) (F := ((p : U → M) *ᵖ F.Fiber)) e he
  obtain ⟨ρU, hρU⟩ := σ.exists_conjugate e₀
  have hρUs : ρU.IsSmooth (M := U) (n := n) (r := F.rank) IG :=
    EquivariantStructure.IsSmooth.of_iso IG σ ρU hσ e he (by
      intro g x v
      simpa only [Iso.toHom, LinearEquiv.coe_coe, he₀] using hρU g x v)
  have hbs : IsSmoothBundleMap (M := W) (n := n) (r := s) (q := F.rank)
      (E := Bundle.Trivial W Model) (F := ((q : W → M) *ᵖ F.Fiber))
      (fun x ↦ ((b x).symm).toLinearMap) :=
    hb.symm (E := ((q : W → M) *ᵖ F.Fiber)) (F := Bundle.Trivial W Model) b
  obtain ⟨b₀, hb₀⟩ := IsSmoothBundleMap.exists_iso (M := W) (n := n) (r := s) (q := F.rank)
    (E := Bundle.Trivial W Model) (F := ((q : W → M) *ᵖ F.Fiber))
    (fun x ↦ (b x).symm) hbs
  obtain ⟨ρW, hρW⟩ := κ.exists_conjugate b₀
  have hρWs : ρW.IsSmooth (M := W) (n := n) (r := F.rank) IG :=
    EquivariantStructure.IsSmooth.of_iso IG κ ρW hκ (fun x ↦ (b x).symm)
      hbs (by
        intro g x v
        have h := hρW g x v
        change b₀.linearEquiv (g • x) (κ.linearMap g x v) =
          ρW.linearMap g x (b₀.linearEquiv x v) at h
        erw [hb₀, hb₀] at h
        exact h)
  have hUvalue (g : G) (x : U) (v : F.Fiber x.val) :
      ρU.linearMap g x v = e (g • x) (σ.linearMap g x ((e x).symm v)) := by
    have h := hρU g x ((e x).symm v)
    change e₀.linearEquiv (g • x) (σ.linearMap g x ((e x).symm v)) =
      ρU.linearMap g x (e₀.linearEquiv x ((e x).symm v)) at h
    erw [he₀, he₀, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hWvalue (g : G) (x : W) (v : F.Fiber x.val) :
      ρW.linearMap g x v = (b (g • x)).symm (κ.linearMap g x (b x v)) := by
    have h := hρW g x (b x v)
    change b₀.linearEquiv (g • x) (κ.linearMap g x (b x v)) =
      ρW.linearMap g x (b₀.linearEquiv x (b x v)) at h
    erw [hb₀, hb₀, LinearEquiv.symm_apply_apply] at h
    exact h.symm
  -- The supplied equivariance of the transition identifies both moving-fiber actions.
  have hagree (g : G) (x : M) (hx : x ∈ U) (hy : x ∈ W) (v : F.Fiber x) :
      (⟨((g • (⟨x, hx⟩ : U) : U) : M), ρU.linearMap g ⟨x, hx⟩ v⟩ :
        TotalSpace Unit F.Fiber) =
        ⟨((g • (⟨x, hy⟩ : W) : W) : M), ρW.linearMap g ⟨x, hy⟩ v⟩ := by
    let := openRefinementMulAction U W hU hW
    let z : V := ⟨⟨x, hx⟩, hy⟩
    have hbase : (⟨(g • z).val.val, (g • z).property⟩ : W) = g • (⟨x, hy⟩ : W) := by
      apply Subtype.ext
      exact (hU g z.val).trans (hW g ⟨x, hy⟩).symm
    rw [hUvalue, hWvalue, ← hbase]
    apply congrArg (fun w : F.Fiber (g • z).val.val ↦
      (⟨(g • z).val.val, w⟩ : TotalSpace Unit F.Fiber))
    apply (b ⟨(g • z).val.val, (g • z).property⟩).injective
    rw [LinearEquiv.apply_symm_apply]
    have hleft := hab (g • z) (σ.linearMap g z.val ((e z.val).symm v))
    have hright := hab z ((e z.val).symm v)
    rw [LinearEquiv.apply_symm_apply] at hright
    exact hleft.trans ((haeq g z ((e z.val).symm v)).trans
      (congrArg (κ.linearMap g ⟨x, hy⟩) hright.symm))
  obtain ⟨ρ, hρ, hρUeq, hρWeq⟩ := EquivariantStructure.exists_smooth_gluing
    (E := F.Fiber) IG U W hcover hU hW ρU ρW hρUs hρWs hagree
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro g x v
    erw [hρUeq, hUvalue, LinearEquiv.symm_apply_apply]
  · intro g x v
    erw [hρWeq, hWvalue]


variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

set_option maxHeartbeats 3200000 in
-- Retain the full relative tuple before constructing either equivariant action.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original relative excision data admit smooth actions with the prescribed local maps. -/
theorem exists_equivariant_relative_excision_data
    (U : Opens M) (K L : Set M) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hLU : L ⊆ (U : Set M))
    (W : Opens M) (hWset : (W : Set M) = Kᶜ)
    [MulAction G U] [ContinuousSMul G U] [ContMDiffSMul IG I ∞ G U]
    [MulAction G W] [ContinuousSMul G W] [ContMDiffSMul IG I ∞ G W]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hW : ∀ (g : G) (x : W), ((g • x : W) : M) = g • (x : M))
    (E F : SmoothFiniteComplexBundle (n := n) U) (hEF : E.rank = F.rank)
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
    (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
    (κ :
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
        (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
      EquivariantStructure G (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank))))
    (hκ : κ.IsSmooth (M := W) (n := n) (r := E.rank) IG)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (ν : Measure U) [hν : IsSmoothPositiveMeasure (n := n) ν]
    (c : ∀ x : U, E.Fiber x →L[ℂ] F.Fiber x)
    (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (c x).toLinearMap))
    (hcEq : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (x : U) (v : E.Fiber x),
        c (g • x) (σE.linearMap g x v) = σF.linearMap g x (c x v)) :
    let V := openRefinementPiece U W
    ∀ (τE : ∀ x : V, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
      (τF : ∀ x : V, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank)),
      IsSmoothBundleMap (n := n) (r := E.rank) (q := E.rank) (M := V)
        (E := ((ContinuousMap.subtypeVal (V : Set U) : V → U) *ᵖ E.Fiber))
        (F := Bundle.Trivial V (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τE x).toLinearMap) →
      IsSmoothBundleMap (n := n) (r := F.rank) (q := E.rank) (M := V)
        (E := ((ContinuousMap.subtypeVal (V : Set U) : V → U) *ᵖ F.Fiber))
        (F := Bundle.Trivial V (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τF x).toLinearMap) →
      (∀ (x : V) (v : E.Fiber x.val), τF x (c x.val v) = τE x v) →
      (letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
       letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
         (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
       letI := openRefinementMulAction U W hU hW
       ∀ (g : G) (x : V) (v : E.Fiber x.val),
         τE (g • x) (σE.linearMap g x.val v) =
           κ.linearMap g ⟨x.val.val, x.property⟩ (τE x v)) →
      (letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
       letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
         (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
       letI := openRefinementMulAction U W hU hW
       ∀ (g : G) (x : V) (v : F.Fiber x.val),
         τF (g • x) (σF.linearMap g x.val v) =
           κ.linearMap g ⟨x.val.val, x.property⟩ (τF x v)) →
      ∃ E' F' : SmoothFiniteComplexBundle (n := n) M,
        E'.rank = E.rank ∧ F'.rank = F.rank ∧
        ∃ (eE : ∀ x : U, E.Fiber x ≃ₗ[ℂ] E'.Fiber x.val)
          (eF : ∀ x : U, F.Fiber x ≃ₗ[ℂ] F'.Fiber x.val),
          IsSmoothBundleMap (n := n) (r := E.rank) (q := E'.rank) (M := U)
            (E := E.Fiber)
            (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E'.Fiber))
            (fun x ↦ (eE x).toLinearMap) ∧
          IsSmoothBundleMap (n := n) (r := F.rank) (q := F'.rank) (M := U)
            (E := F.Fiber)
            (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F'.Fiber))
            (fun x ↦ (eF x).toLinearMap) ∧
          ∃ (bE : ∀ x : W, E'.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
            (bF : ∀ x : W, F'.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank)),
            IsSmoothBundleMap (n := n) (r := E'.rank) (q := E.rank) (M := W)
              (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E'.Fiber))
              (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
              (fun x ↦ (bE x).toLinearMap) ∧
            IsSmoothBundleMap (n := n) (r := F'.rank) (q := E.rank) (M := W)
              (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ F'.Fiber))
              (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
              (fun x ↦ (bF x).toLinearMap) ∧
            (∀ (x : V) (v : E.Fiber x.val),
              bE ⟨x.val.val, x.property⟩ (eE x.val v) = τE x v) ∧
            (∀ (x : V) (v : F.Fiber x.val),
              bF ⟨x.val.val, x.property⟩ (eF x.val v) = τF x v) ∧
            ∃ d : ∀ x : M, E'.Fiber x →L[ℂ] F'.Fiber x,
              IsSmoothBundleMap (n := n) (r := E'.rank) (q := F'.rank)
                (fun x ↦ (d x).toLinearMap) ∧
              (∀ (x : U) (v : E.Fiber x), d x.val (eE x v) = eF x (c x v)) ∧
              (∀ (x : W) (v : E'.Fiber x.val), bF x (d x.val v) = bE x v) ∧
              (∀ x : M, x ∉ K → Function.Bijective (d x)) ∧
              ∃ (g : SmoothHermitianMetric (n := n) (r := E'.rank) E'.Fiber)
                (l : SmoothHermitianMetric (n := n) (r := F'.rank) F'.Fiber)
                (μ : Measure M),
                IsSmoothPositiveMeasure (n := n) μ ∧
                ∃ O : Opens M, L ⊆ (O : Set M) ∧ O ≤ U ∧
                  (∀ (x : U), x.val ∈ O → ∀ v w : E.Fiber x,
                    g.pairing x.val (eE x v) (eE x w) = h.pairing x v w) ∧
                  (∀ (x : U), x.val ∈ O → ∀ v w : F.Fiber x,
                    l.pairing x.val (eF x v) (eF x w) = k.pairing x v w) ∧
                  (μ.comap (Subtype.val : U → M)).restrict
                      ((Subtype.val : U → M) ⁻¹' (O : Set M)) =
                    ν.restrict ((Subtype.val : U → M) ⁻¹' (O : Set M)) ∧
                  letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
                  letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
                  letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
                  letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
                  letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
                    (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
                  ∃ (ρE : EquivariantStructure G E'.Fiber)
                    (ρF : EquivariantStructure G F'.Fiber),
                    ρE.IsSmooth (n := n) (r := E'.rank) IG ∧
                    ρF.IsSmooth (n := n) (r := F'.rank) IG ∧
                    (∀ (g : G) (x : U) (v : E.Fiber x),
                      (⟨g • x.val, ρE.linearMap g x.val (eE x v)⟩ :
                          TotalSpace Unit E'.Fiber) =
                        ⟨((g • x : U) : M), eE (g • x) (σE.linearMap g x v)⟩) ∧
                    (∀ (g : G) (x : U) (v : F.Fiber x),
                      (⟨g • x.val, ρF.linearMap g x.val (eF x v)⟩ :
                          TotalSpace Unit F'.Fiber) =
                        ⟨((g • x : U) : M), eF (g • x) (σF.linearMap g x v)⟩) ∧
                    (∀ (g : G) (x : W) (v : E'.Fiber x.val),
                      (⟨g • x.val, ρE.linearMap g x.val v⟩ : TotalSpace Unit E'.Fiber) =
                        ⟨((g • x : W) : M), (bE (g • x)).symm
                          (κ.linearMap g x (bE x v))⟩) ∧
                    (∀ (g : G) (x : W) (v : F'.Fiber x.val),
                      (⟨g • x.val, ρF.linearMap g x.val v⟩ : TotalSpace Unit F'.Fiber) =
                        ⟨((g • x : W) : M), (bF (g • x)).symm
                          (κ.linearMap g x (bF x v))⟩) ∧
                    ∀ (g : G) (x : M) (v : E'.Fiber x),
                      d (g • x) (ρE.linearMap g x v) = ρF.linearMap g x (d x v) := by
  classical
  have hWident : W = ⟨Kᶜ, hK.isClosed.isOpen_compl⟩ := SetLike.coe_injective hWset
  subst W
  let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  dsimp only
  intro τE τF hτE hτF hidentity hτEeq hτFeq
  -- Choose the original geometric witnesses once, including both metric comparisons.
  obtain ⟨E', F', hE', hF', eE, eF, heE, heF, bE, bF, hbE, hbF,
      hbEeq, hbFeq, d, hd, hdU, hdW, hdInv, h', k', μ, hμ, O,
      hLO, hOU, hh', hk', hμν⟩ :=
    exists_relative_excision_data U K L hK hL hKL hLU E F hEF h k ν c hc
      τE τF hτE hτF hidentity
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank))
    (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
  have hcover : (U : Set M) ∪ (W : Set M) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx : x ∈ K
    · exact Or.inl (hLU (hKL hx))
    · exact Or.inr hx
  -- Glue on precisely E' and F'; both exterior frames use the same action κ.
  obtain ⟨ρE, hρE, hρEU, hρEW⟩ := exists_action_on_relative_bundle
    IG U W hcover hU hW E σE hσE κ hκ τE hτEeq E' eE heE bE hbE hbEeq
  obtain ⟨ρF, hρF, hρFU, hρFW⟩ := exists_action_on_relative_bundle
    IG U W hcover hU hW F σF hσF κ hκ τF hτFeq F' eF heF bF hbF hbFeq
  refine ⟨E', F', hE', hF', eE, eF, heE, heF, bE, bF, hbE, hbF,
    hbEeq, hbFeq, d, hd, hdU, hdW, hdInv, h', k', μ, hμ, O,
    hLO, hOU, hh', hk', hμν, ρE, ρF, hρE, hρF, hρEU, hρFU, hρEW, hρFW, ?_⟩
  -- Check the original operator in each invariant part of the same cover.
  let D : TotalSpace Unit E'.Fiber → TotalSpace Unit F'.Fiber :=
    fun z ↦ ⟨z.proj, d z.proj z.snd⟩
  intro g x v
  apply TotalSpace.mk_injective (F := Unit) (g • x)
  by_cases hx : x ∈ U
  · let y : U := ⟨x, hx⟩
    obtain ⟨w, hw⟩ := (eE y).surjective v
    subst v
    calc
      (⟨g • x, d (g • x) (ρE.linearMap g x (eE y w))⟩ : TotalSpace Unit F'.Fiber) =
          ⟨((g • y : U) : M), d ((g • y : U) : M)
            (eE (g • y) (σE.linearMap g y w))⟩ := congrArg D (hρEU g y w)
      _ = ⟨((g • y : U) : M), eF (g • y) (σF.linearMap g y (c y w))⟩ := by
        rw [hdU, hcEq]
      _ = ⟨g • x, ρF.linearMap g x (eF y (c y w))⟩ := (hρFU g y (c y w)).symm
      _ = _ := by rw [hdU y w]
  · have hxW : x ∈ W := by
      have hxcover : x ∈ (U : Set M) ∪ W := by rw [hcover]; trivial
      exact hxcover.resolve_left hx
    let y : W := ⟨x, hxW⟩
    have hdW' (z : W) (w : E'.Fiber z.val) :
        d z.val w = (bF z).symm (bE z w) := by
      apply (bF z).injective
      rw [hdW, LinearEquiv.apply_symm_apply]
    calc
      (⟨g • x, d (g • x) (ρE.linearMap g x v)⟩ : TotalSpace Unit F'.Fiber) =
          ⟨((g • y : W) : M), d ((g • y : W) : M)
            ((bE (g • y)).symm (κ.linearMap g y (bE y v)))⟩ :=
        congrArg D (hρEW g y v)
      _ = ⟨((g • y : W) : M), (bF (g • y)).symm
          (κ.linearMap g y (bE y v))⟩ := by
        rw [hdW', LinearEquiv.apply_symm_apply]
      _ = ⟨g • x, ρF.linearMap g x (d x v)⟩ := by
        have hh := hρFW g y (d x v)
        rw [hdW] at hh
        exact hh.symm

end AtiyahSinger
