/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantRelativeOperatorAverage
public import AtiyahSinger.Analysis.OpenOperatorTransport

import all AtiyahSinger.Analysis.EquivariantRelativeOperatorAverage

/-!
# Equivariance of the original supported open section equivalence

Public module ID: M0583.

The prescribed open diffeomorphism and fiber equivalence determine the original
restriction, transport and zero-extension map. Its moving-fiber square implies
equivariance of that exact map on supported smooth sections. The compact controls
and the ambient bundle actions remain fixed. This supplies both section action
comparisons required by relative equivariant analytic excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N] [T2Space M] [T2Space N]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]

set_option maxHeartbeats 1000000 in
-- Compare the same dependent section values on the original open image and its complement.
/-- The specified open section equivalence intertwines the original smooth bundle actions. -/
theorem supportedSmoothSectionOpenEquiv_intertwines
    (E : SmoothFiniteComplexBundle (n := n) M)
    (F : SmoothFiniteComplexBundle (n := n) N)
    (U : Opens M) (V : Opens N)
    (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
    [MulAction G U] [ContinuousSMul G U]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (he : ∀ (g : G) (x : U), (e (g • x)).val = g • (e x).val)
    (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
    (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
    (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
    (hKi : ∀ (g : G) (x : M), g • x ∈ K ↔ x ∈ K)
    (a : ∀ x : U,
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
        (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
          ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F.Fiber)) x)
    (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (a x).toLinearMap))
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (τ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (hσ : σ.IsSmooth (n := n) (r := E.rank) IG)
    (hτ : τ.IsSmooth (n := n) (r := F.rank) IG)
    (hag : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (x : U) (v : E.Fiber x.val),
        (⟨(e (g • x)).val, a (g • x)
          (cast (congrArg E.Fiber (hU g x).symm) (σ.linearMap g x.val v))⟩ :
            TotalSpace Unit F.Fiber) =
          ⟨g • (e x).val, τ.linearMap g (e x).val (a x v)⟩)
    (g : G) (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
    (hu : σ.smoothSectionRepresentation IG hσ g u.val ∈
      supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) :
    let A := supportedSmoothSectionOpenEquiv E F U V e K L
      hK.isClosed hL.isClosed hKU hLV hKL a ha
    (A ⟨σ.smoothSectionRepresentation IG hσ g u.val, hu⟩).val =
      τ.smoothSectionRepresentation IG hτ g (A u).val := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let A := supportedSmoothSectionOpenEquiv E F U V e K L
    hK.isClosed hL.isClosed hKU hLV hKL a ha
  let gu : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K :=
    ⟨σ.smoothSectionRepresentation IG hσ g u.val, hu⟩
  have hvalue (v : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) (x : U) :
      (A v).val.val (e x).val = a x (v.val.val x.val) :=
    supportedSmoothSectionOpenEquiv_apply E F U V e K L hK hL hKU hLV hKL a ha v x
  -- The target control is the image of the same source control under this equivariant map.
  have hLforward (k : G) (y : N) (hy : y ∈ L) : k • y ∈ L := by
    let x : U := e.symm ⟨y, hLV hy⟩
    have hxvalue : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hLV hy⟩)
    have hxK : x.val ∈ K := by
      have hx : x ∈ e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) := by
        change (e x).val ∈ L
        rw [hxvalue]
        exact hy
      rw [hKL] at hx
      exact hx
    have hkxK : (k • x : U).val ∈ K := by
      rw [hU]
      exact (hKi k x.val).mpr hxK
    have hkx : k • x ∈ e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) := by
      rw [hKL]
      exact hkxK
    change (e (k • x)).val ∈ L at hkx
    rwa [he, hxvalue] at hkx
  apply Subtype.ext
  funext y
  by_cases hy : y ∈ L
  · -- On the original image, transport the actual section square from the inverse point.
    let x : U := e.symm ⟨y, hLV hy⟩
    have hxvalue : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hLV hy⟩)
    have h := section_transport_action IG (Subtype.val : U → M)
      (fun z : U ↦ (e z).val) hU he E F σ τ hσ hτ a hag
      g u.val (A u).val (g⁻¹ • x) (hvalue u (g⁻¹ • x))
    have haction : (τ.smoothSectionRepresentation IG hτ g (A u).val).val (e x).val =
        a x ((σ.smoothSectionRepresentation IG hσ g u.val).val x.val) :=
      (congrArg (fun z : U ↦
        (τ.smoothSectionRepresentation IG hτ g (A u).val).val (e z).val =
          a z ((σ.smoothSectionRepresentation IG hσ g u.val).val z.val))
        (smul_inv_smul g x)).mp h
    have hactual := (hvalue gu x).trans haction.symm
    exact (congrArg (fun z : N ↦ (A gu).val.val z =
      (τ.smoothSectionRepresentation IG hτ g (A u).val).val z) hxvalue).mp hactual
  · -- Off the same target control the original zero extension and its translate both vanish.
    have hs : closure {z : N | (A u).val.val z ≠ 0} ⊆ L := by
      apply closure_minimal ?_ hL.isClosed
      intro z hz
      by_contra hzL
      exact hz ((A u).property z hzL)
    have hsaction : closure {z : N | τ.sectionLinearMap g (A u).val.val z ≠ 0} ⊆ L := by
      rw [τ.closure_support_sectionLinearMap]
      rintro _ ⟨z, hz, rfl⟩
      exact hLforward g z (hs hz)
    have hzero : τ.sectionLinearMap g (A u).val.val y = 0 := by
      by_contra hne
      exact hy (hsaction (subset_closure hne))
    exact ((A gu).property y hy).trans hzero.symm

end AtiyahSinger
