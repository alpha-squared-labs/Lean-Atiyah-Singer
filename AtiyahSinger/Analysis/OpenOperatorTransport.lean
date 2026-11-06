/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SectionOperatorSupport
public import AtiyahSinger.Geometry.OpenSectionIdentification

import AtiyahSinger.Analysis.CoordinateChange
import AtiyahSinger.Analysis.SmoothSectionMultiplication

/-!
# Exact supported transport through an open identification

Public module ID: M0831.

The supplied base diffeomorphism and fiber equivalences transport actual
section germs and supported outputs. Cutoff pullback realizes every target
input germ in the original source section space. The construction requires
neither a compact source nor a measure on that source.

These reusable transport statements provide the actual maps used in SG III.13.4.
They do not identify operators merely by their principal symbol.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace Filter Set
open scoped Manifold ContDiff Topology

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
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
  (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (a x).toLinearMap))
  (b : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hb : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (b x).toLinearMap))

include hK hKU ha in
omit hT' hSC' in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 600000 in
-- Use the prescribed fiber transport in the cutoff pullback and its zero extension.
/-- A compact cutoff realizes every target germ as an actual smooth source section. -/
theorem exists_openSectionGermPullback :
    ∃ (χ : M → ℝ)
      (_hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
      (T : smoothSections (n := n) (r := G.rank) G.Fiber →ₗ[ℂ]
        smoothSections (n := n) (r := E.rank) E.Fiber),
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧
      ∀ (v : smoothSections (n := n) (r := G.rank) G.Fiber) (x : U),
        (T v).val x.val = (χ x.val : ℂ) • (a x).symm (v.val (e x).val) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨W, hW, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK U.isOpen hKU
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := I) (n := ⊤) hK.isClosed (hKW.trans hW.subset_interior_closure)
  have hχW : tsupport χ ⊆ closure W := by
    apply closure_minimal _ hWc.isClosed
    intro x hx
    by_contra hxW
    exact hx (hχzero x hxW)
  let E₀ : U → Type := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber)
  let G₀ : V → Type := ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)
  let G₁ : U → Type := (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ G₀)
  let R := smoothSectionRestriction (n := n) (r := G.rank) G.Fiber V
  let D := smoothSectionPullback (M := U) (N := V) (n := n) (m := n) (r := G.rank)
    G₀ (⟨e, e.continuous⟩ : C(U, V)) e.contMDiff
  let A := smoothSectionEquiv (M := U) (n := n) (r := E.rank) (q := G.rank)
    (E := E₀) (F := G₁) a ha
  have hχU : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun x : U ↦ (χ x.val : ℂ)) :=
    Complex.ofRealCLM.contMDiff.comp (χ.contMDiff.comp contMDiff_subtype_val)
  let S := (smoothSectionMul (M := U) (n := n) (r := E.rank) E₀
    (fun x : U ↦ (χ x.val : ℂ)) hχU).comp (A.symm.toLinearMap.comp (D.comp R))
  let S₀ : smoothSections (n := n) (r := G.rank) G.Fiber →ₗ[ℂ]
      supportedSmoothSections (M := U) (n := n) (r := E.rank) E₀
        ((Subtype.val : U → M) ⁻¹' closure W) :=
    S.codRestrict _ (fun v x hx ↦ by
      change (χ x.val : ℂ) • (a x).symm (v.val (e x).val) = 0
      rw [hχzero x.val hx]
      simp)
  let T := (smoothSectionZeroExtension (n := n) (r := E.rank) E.Fiber U
    (closure W) hWc.isClosed hWU).comp S₀
  refine ⟨χ, χ.contMDiff, T,
    hWc.of_isClosed_subset isClosed_closure hχW, hχW.trans hWU, hχone, ?_⟩
  intro v x
  change (if hx : x.val ∈ U then (S₀ v).val.val ⟨x.val, hx⟩ else (0 : E.Fiber x.val)) = _
  rw [dite_eq_left x.property]
  rfl

omit hSC hSC' in
set_option maxSynthPendingDepth 40 in
/-- The specified open section equivalence evaluates by the original fiber identification. -/
theorem supportedSmoothSectionOpenEquiv_apply
    (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) (x : U) :
    (supportedSmoothSectionOpenEquiv E G U V e K L
      hK.isClosed hL.isClosed hKU hLV hKL a ha u).val.val (e x).val =
        a x (u.val.val x.val) := by
  let T := supportedSmoothSectionOpenEquiv E G U V e K L
    hK.isClosed hL.isClosed hKU hLV hKL a ha
  let R := supportedSmoothSectionRestrictionEquiv (n := n) (r := E.rank)
    E.Fiber U K hK.isClosed hKU
  let B := supportedSmoothSectionEquiv (M := U) (n := n) (r := E.rank) (q := G.rank)
    (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber))
    (F := (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
      ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)))
    ((Subtype.val : U → M) ⁻¹' K) a ha
  let D := supportedSmoothSectionDiffeomorphEquiv (M := U) (N := V)
    (n := n) (m := n) (r := G.rank)
    ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber) e
    ((Subtype.val : V → N) ⁻¹' L)
  let C := LinearEquiv.ofEq _ _
    (congrArg (supportedSmoothSections (n := n) (r := G.rank)
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber))) hKL.symm)
  let S := supportedSmoothSectionRestrictionEquiv (n := n) (r := G.rank)
    G.Fiber V L hL.isClosed hLV
  have hsame : D (S (T u)) = C (B (R u)) := by
    change D (S (S.symm (D.symm (C (B (R u)))))) = _
    exact (congrArg D (S.apply_symm_apply (D.symm (C (B (R u)))))).trans
      (D.apply_symm_apply (C (B (R u))))
  have hx := congrArg (fun v ↦ v.val.val x) hsame
  change (T u).val.val (e x).val = (C (B (R u))).val.val x at hx
  have hc : (C (B (R u))).val = (B (R u)).val := LinearEquiv.coe_ofEq_apply _ _
  exact hx.trans (congrArg (fun v ↦ v.val x) hc)

omit hM hT hSC in
/-- A supported section operator depends only on the input germ near its support. -/
theorem HasSectionOperatorSupport.eq_of_eventuallyEq
    (R : smoothSections (n := n) (r := E.rank) E.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := F.rank) F.Fiber)
    (hR : HasSectionOperatorSupport K R)
    (u v : smoothSections (n := n) (r := E.rank) E.Fiber)
    (huv : ∀ᶠ x in 𝓝ˢ K, u.val x = v.val x) : R u = R v := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hR.2
  apply Set.disjoint_left.mpr
  intro x hx hxK
  have hn := eventually_nhdsSet_iff_forall.mp huv x hxK
  obtain ⟨y, hy, hne⟩ := mem_closure_iff_nhds.mp hx {y | u.val y = v.val y} hn
  exact hne (sub_eq_zero.mpr hy)

include hK hL hKU hLV hKL ha hb in
omit hSC' in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1000000 in
-- The same input cutoff and output equivalence determine existence, support and uniqueness.
/-- Exact supported operators extend uniquely through a specified open fiber identification. -/
theorem existsUnique_supported_openExtension
    (R : smoothSections (n := n) (r := E.rank) E.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := F.rank) F.Fiber)
    (hR : HasSectionOperatorSupport K R) :
    ∃! Q : smoothSections (n := n) (r := G.rank) G.Fiber →ₗ[ℂ]
        smoothSections (n := n) (r := H.rank) H.Fiber,
      HasSectionOperatorSupport L Q ∧
        ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
          (v : smoothSections (n := n) (r := G.rank) G.Fiber),
          (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
            v.val (e x).val = a x (u.val x.val)) →
          ∀ x : U, (Q v).val (e x).val = b x ((R u).val x.val) := by
  classical
  obtain ⟨χ, hχ, Tin, _, _, hχone, hTin⟩ :=
    exists_openSectionGermPullback E G U V e K hK hKU a ha
  let Bout := supportedSmoothSectionOpenEquiv F H U V e K L
    hK.isClosed hL.isClosed hKU hLV hKL b hb
  let Rs : smoothSections (n := n) (r := E.rank) E.Fiber →ₗ[ℂ]
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber K :=
    R.codRestrict _ (fun u x hx ↦ by
      by_contra hne
      exact hx (hR.1 u (subset_closure hne)))
  let Q : smoothSections (n := n) (r := G.rank) G.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := H.rank) H.Fiber :=
    (supportedSmoothSections (n := n) (r := H.rank) H.Fiber L).subtype.comp
      (Bout.toLinearMap.comp (Rs.comp Tin))
  -- Relative neighborhoods in the common open set are ambient neighborhoods at K.
  have hRgerm (u v : smoothSections (n := n) (r := E.rank) E.Fiber)
      (huv : ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K), u.val x.val = v.val x.val) :
      R u = R v := by
    apply hR.eq_of_eventuallyEq
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hxK
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hKU hxK⟩]
    exact eventually_nhdsSet_iff_forall.mp huv ⟨x, hKU hxK⟩ hxK
  have hχUone : ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K), χ x.val = 1 := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hxK
    have hn : ∀ᶠ y in 𝓝 x.val, χ y = 1 :=
      eventually_nhdsSet_iff_forall.mp hχone x.val hxK
    exact (continuous_subtype_val.tendsto x).eventually hn
  have hTinmatch (v : smoothSections (n := n) (r := G.rank) G.Fiber) :
      ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x ((Tin v).val x.val) := by
    filter_upwards [hχUone] with x hx
    rw [hTin, hx, Complex.ofReal_one, one_smul, LinearEquiv.apply_symm_apply]
  have hformula (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := G.rank) G.Fiber)
      (huv : ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) (x : U) :
      (Q v).val (e x).val = b x ((R u).val x.val) := by
    have hRu : R (Tin v) = R u := hRgerm _ _ (by
      filter_upwards [hTinmatch v, huv] with y hy hv
      exact (a y).injective (hy.symm.trans hv))
    change (Bout (Rs (Tin v))).val.val (e x).val = _
    rw [supportedSmoothSectionOpenEquiv_apply F H U V e K L hK hL hKU hLV hKL b hb]
    change b x ((R (Tin v)).val x.val) = _
    rw [hRu]
  have hout (v : smoothSections (n := n) (r := G.rank) G.Fiber) :
      closure {x | (Q v).val x ≠ 0} ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hxL
    exact hx ((Bout (Rs (Tin v))).property x hxL)
  have hsupp : HasSectionOperatorSupport L Q := by
    refine ⟨hout, ?_⟩
    intro v hv
    have hvgerm : ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = 0 := by
      apply eventually_nhdsSet_iff_forall.mpr
      intro x hxK
      have hxL : (e x).val ∈ L := by
        change x ∈ e ⁻¹' ((Subtype.val : V → N) ⁻¹' L)
        rw [hKL]
        exact hxK
      have hxnot : (e x).val ∉ closure {y | v.val y ≠ 0} :=
        fun h ↦ Set.disjoint_left.mp hv h hxL
      have hecont : Continuous (fun x : U ↦ (e x).val) := continuous_subtype_val.comp e.continuous
      have hn : (closure {y | v.val y ≠ 0})ᶜ ∈ 𝓝 (e x).val :=
        isClosed_closure.isOpen_compl.mem_nhds hxnot
      filter_upwards [hecont.continuousAt.preimage_mem_nhds hn] with y hy
      by_contra hne
      exact hy (subset_closure hne)
    have hRu : R (Tin v) = R 0 := hRgerm _ _ (by
      filter_upwards [hTinmatch v, hvgerm] with x hx hz
      apply (a x).injective
      change (a x) ((Tin v).val x.val) = (a x) (0 : E.Fiber x.val)
      rw [map_zero]
      exact hx.symm.trans hz)
    have hRzero : Rs (Tin v) = 0 := by
      apply Subtype.ext
      exact hRu.trans (map_zero R)
    change (Bout (Rs (Tin v))).val = 0
    rw [hRzero, map_zero]
    rfl
  refine ⟨Q, ⟨hsupp, hformula⟩, ?_⟩
  intro Q' hQ'
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext y
  by_cases hy : y ∈ V
  · let x : U := e.symm ⟨y, hy⟩
    have hleft := hQ'.2 (Tin v) v (hTinmatch v) x
    have hright := hformula (Tin v) v (hTinmatch v) x
    have he : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    exact (congrArg (fun z ↦ (Q' v).val z = (Q v).val z) he).mp (hleft.trans hright.symm)
  · have hyL : y ∉ L := fun h ↦ hy (hLV h)
    have hleft : (Q' v).val y = 0 := by
      by_contra hne
      exact hyL (hQ'.1.1 v (subset_closure hne))
    have hright : (Q v).val y = 0 := by
      by_contra hne
      exact hyL (hout v (subset_closure hne))
    exact hleft.trans hright.symm

end AtiyahSinger
