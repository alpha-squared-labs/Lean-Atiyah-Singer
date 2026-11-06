/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantClopenRefinement
public import AtiyahSinger.Geometry.ExteriorBundleExtension
public import AtiyahSinger.Geometry.SmoothBundleMapContinuity
public import AtiyahSinger.Geometry.SmoothEquivariantBundleGluing
public import AtiyahSinger.Geometry.SmoothEquivariantBundleIso
public import AtiyahSinger.Topology.EquivariantBundleTransport

/-!
# Extending a smooth equivariant bundle with its prescribed exterior action

Public module ID: M1187.

The ordinary exterior-frame extension admits a jointly smooth group action
which retains both the original interior action and the specified exterior
action. Compatibility is imposed on the actual supplied frame, so this
construction preserves the identifications used in relative analytic excision.
This is the equivariant form of the bundle gluing in SG III.13.4; no finite
CW model or compactness of the ambient manifold is needed here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
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
-- Retain the three actual restricted atlases and all moving-fiber identifications.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exterior-frame gluing retains the original interior action and specified exterior action. -/
theorem exists_smoothEquivariantBundle_extension_of_exterior_trivialization
    (U W : Opens M) (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    (hWset : (W : Set M) = Kᶜ)
    [MulAction G U] [ContinuousSMul G U] [ContMDiffSMul IG I ∞ G U]
    [MulAction G W] [ContinuousSMul G W] [ContMDiffSMul IG I ∞ G W]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hW : ∀ (g : G) (x : W), ((g • x : W) : M) = g • (x : M))
    (E : SmoothFiniteComplexBundle (n := n) U)
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (hσ : σ.IsSmooth (n := n) (r := E.rank) IG)
    (κ :
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
        (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
      EquivariantStructure G (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank))))
    (hκ : κ.IsSmooth (M := W) (n := n) (r := E.rank) IG)
    (a : ∀ x : openRefinementPiece U W,
      E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
    (ha : IsSmoothBundleMap (M := openRefinementPiece U W) (n := n)
      (r := E.rank) (q := E.rank)
      (E := ((ContinuousMap.subtypeVal (openRefinementPiece U W : Set U) :
        openRefinementPiece U W → U) *ᵖ E.Fiber))
      (F := Bundle.Trivial (openRefinementPiece U W) (EuclideanSpace ℂ (Fin E.rank)))
      (fun x ↦ (a x).toLinearMap))
    (haeq :
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
        (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
      letI := openRefinementMulAction U W hU hW
      ∀ (g : G) (x : openRefinementPiece U W) (v : E.Fiber x.val),
        a (g • x) (σ.linearMap g x.val v) =
          κ.linearMap g ⟨x.val.val, x.property⟩ (a x v)) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = E.rank ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank))
        (Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
      ∃ e : ∀ x : U, E.Fiber x ≃ₗ[ℂ] F.Fiber x.val,
        IsSmoothBundleMap (M := U) (n := n) (r := E.rank) (q := F.rank)
          (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber))
          (fun x ↦ (e x).toLinearMap) ∧
        ∃ b : ∀ x : W, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank),
          IsSmoothBundleMap (M := W) (n := n) (r := F.rank) (q := E.rank)
            (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ F.Fiber))
            (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
            (fun x ↦ (b x).toLinearMap) ∧
          (∀ (x : openRefinementPiece U W) (v : E.Fiber x.val),
            b ⟨x.val.val, x.property⟩ (e x.val v) = a x v) ∧
          ∃ ρ : EquivariantStructure G F.Fiber, ρ.IsSmooth (n := n) (r := F.rank) IG ∧
            (∀ (g : G) (x : U) (v : E.Fiber x),
              (⟨g • x.val, ρ.linearMap g x.val (e x v)⟩ : TotalSpace Unit F.Fiber) =
                ⟨((g • x : U) : M), e (g • x) (σ.linearMap g x v)⟩) ∧
            ∀ (g : G) (x : W) (v : F.Fiber x.val),
              (⟨g • x.val, ρ.linearMap g x.val v⟩ : TotalSpace Unit F.Fiber) =
                ⟨((g • x : W) : M), (b (g • x)).symm (κ.linearMap g x (b x v))⟩ := by
  classical
  have hWident : W = ⟨Kᶜ, hK.isClosed.isOpen_compl⟩ := SetLike.coe_injective hWset
  subst W
  let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  let V := openRefinementPiece U W
  let Model := EuclideanSpace ℂ (Fin E.rank)
  -- First build the actual smooth bundle and retain its prescribed transition frame.
  obtain ⟨F, hF, e, he, b, hb, hab⟩ :=
    exists_smoothBundle_extension_of_exterior_trivialization U K hK hKU E a ha
  let := modelTopology Model E.Fiber
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
  have hbs : IsSmoothBundleMap (M := W) (n := n) (r := E.rank) (q := F.rank)
      (E := Bundle.Trivial W Model) (F := ((q : W → M) *ᵖ F.Fiber))
      (fun x ↦ ((b x).symm).toLinearMap) :=
    hb.symm (E := ((q : W → M) *ᵖ F.Fiber)) (F := Bundle.Trivial W Model) b
  obtain ⟨b₀, hb₀⟩ := IsSmoothBundleMap.exists_iso (M := W) (n := n) (r := E.rank) (q := F.rank)
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
  have hcover : (U : Set M) ∪ (W : Set M) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  obtain ⟨ρ, hρ, hρUeq, hρWeq⟩ := EquivariantStructure.exists_smooth_gluing
    (E := F.Fiber) IG U W hcover hU hW ρU ρW hρUs hρWs hagree
  refine ⟨F, hF, e, he, b, hb, hab, ρ, hρ, ?_, ?_⟩
  · intro g x v
    erw [hρUeq, hUvalue, LinearEquiv.symm_apply_apply]
  · intro g x v
    erw [hρWeq, hWvalue]

end AtiyahSinger
