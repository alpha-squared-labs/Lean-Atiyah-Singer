/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EuclideanRelativeHomology
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compact convex controls in local singular homology

Public module ID: M1635.

For a compact convex set and a point in it, the inclusion of complements is a
homotopy equivalence: expand radially to or beyond a fixed bounding sphere. Convexity
ensures that every outward ray starting outside the set stays outside it. The
long exact sequences of the actual pairs then identify their relative homology
through the original inclusion map. This is the convex case of Hatcher, Lemma 3.27.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits
open scoped unitInterval

universe u

/-- Restriction from a compact convex control to any one of its points is an isomorphism. -/
theorem relativeSingularHomologyInclusion_compactConvex_bijective
    (R : Type) [CommRing R] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K) (x : E) (hx : x ∈ K)
    (k : ℕ) :
    Function.Bijective (relativeSingularHomologyInclusion R Kᶜ ({x}ᶜ)
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) k) := by
  let A := Kᶜ
  let B := ({x}ᶜ : Set E)
  have hAB : A ⊆ B := Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)
  let f : C(A, B) := ⟨fun y ↦ ⟨y.val, hAB y.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  -- A common radius bounds all translated vectors in the compact control.
  obtain ⟨ρ, hρ, hbound⟩ :=
    (hK.image (continuous_id.sub continuous_const)).isBounded.exists_pos_norm_lt
  have hbound' (y : E) (hy : y ∈ K) : ‖y - x‖ < ρ := hbound _ ⟨y, hy, rfl⟩
  have hne (y : B) : y.val - x ≠ 0 := sub_ne_zero.mpr y.property
  let q (y : B) : ℝ := max 1 (ρ / ‖y.val - x‖)
  have hq (y : B) : 1 ≤ q y := le_max_left _ _
  have hqCont : Continuous q := continuous_const.max
    (continuous_const.div ((continuous_subtype_val.sub continuous_const).norm)
      (fun y ↦ norm_ne_zero_iff.mpr (hne y)))
  have hout (y : E) (hy : y ∉ K) (t : ℝ) (ht : 1 ≤ t) :
      x + t • (y - x) ∉ K := by
    -- If an outward point belonged to the convex control, its segment to x
    -- would contain the original point, contradicting that it lies outside.
    intro h
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hmem := (hconv.starConvex hx).add_smul_sub_mem h
      (inv_nonneg.mpr htpos.le) (inv_le_one_of_one_le₀ ht)
    have heq : x + t⁻¹ • (x + t • (y - x) - x) = y := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
      abel
    exact hy (heq ▸ hmem)
  have hfar (y : B) : x + q y • (y.val - x) ∉ K := by
    intro hy
    have hnorm : ‖x + q y • (y.val - x) - x‖ = q y * ‖y.val - x‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_trans zero_le_one (hq y))]
    have hlarge : ρ ≤ q y * ‖y.val - x‖ :=
      (div_le_iff₀ (norm_pos_iff.mpr (hne y))).mp (le_max_right _ _)
    have hsmall := hbound' _ hy
    rw [hnorm] at hsmall
    exact (not_lt_of_ge hlarge) hsmall
  let g : C(B, A) := ⟨fun y ↦ ⟨x + q y • (y.val - x), hfar y⟩,
    (continuous_const.add (hqCont.smul (continuous_subtype_val.sub continuous_const))).subtype_mk _⟩
  -- Both composites are connected to the identity by the same outward radial homotopy.
  let scale (t : unitInterval) (y : B) : ℝ :=
    1 + (1 - (t : ℝ)) * (q y - 1)
  have hscale (t : unitInterval) (y : B) : 1 ≤ scale t y := by
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr t.property.2)
      (sub_nonneg.mpr (hq y)))
  have hgf : (g.comp f).Homotopic (ContinuousMap.id A) := by
    refine ⟨{ toFun p := ⟨x + scale p.1 (f p.2) • (p.2.val - x),
                hout p.2.val p.2.property _ (hscale p.1 (f p.2))⟩
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · dsimp only [scale]
      fun_prop
    · intro y
      apply Subtype.ext
      simp [scale, g, f]
    · intro y
      apply Subtype.ext
      simp [scale]
  have hfg : (f.comp g).Homotopic (ContinuousMap.id B) := by
    refine ⟨{ toFun p := ⟨x + scale p.1 p.2 • (p.2.val - x), ?_⟩
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · change x + scale p.1 p.2 • (p.2.val - x) ≠ x
      intro h
      have hz : scale p.1 p.2 • (p.2.val - x) = 0 :=
        add_left_cancel (h.trans (add_zero x).symm)
      exact smul_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one (hscale p.1 p.2)))
        (hne p.2) hz
    · dsimp only [scale]
      fun_prop
    · intro y
      apply Subtype.ext
      simp [scale, f, g]
    · intro y
      apply Subtype.ext
      simp [scale]
  -- Homotopy invariance gives inverse maps on each absolute homology group.
  have hmap {U V : Type u} [TopologicalSpace U] [TopologicalSpace V]
      (a : C(U, V)) (b : C(V, U))
      (h : (b.comp a).Homotopic (ContinuousMap.id U)) (j : ℕ) :
      singularHomologyMap R a j ≫ singularHomologyMap R b j = 𝟙 _ := by
    change HomologicalComplex.homologyMap ((singularChainsFunctor R).map (TopCat.ofHom a)) j ≫
      HomologicalComplex.homologyMap ((singularChainsFunctor R).map (TopCat.ofHom b)) j = _
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    exact (singularHomologyMap_eq_of_homotopic R h j).trans (by simp [singularHomologyMap])
  have hIso (j : ℕ) : IsIso (singularHomologyMap R f j) :=
    ⟨⟨singularHomologyMap R g j, hmap f g hgf j, hmap g f hfg j⟩⟩
  -- Compare the two original pair sequences. The middle vertical map is the identity;
  -- the left vertical maps are the isomorphisms just proved, so the right map is too.
  let S (C : Set E) := ShortComplex.mk (singularSubspaceChains R C)
    (relativeSingularChainsProjection R C) (cokernel.condition _)
  let φ : S A ⟶ S B :=
    { τ₁ := (singularChainsFunctor R).map (TopCat.ofHom f)
      τ₂ := 𝟙 (singularChains R E)
      τ₃ := relativeSingularChainsMap R (ContinuousMap.id E) (fun _ hy ↦ hAB hy)
      comm₁₂ := by
        dsimp [S]
        rw [Category.comp_id]
        simp only [singularSubspaceChains, ← Functor.map_comp]
        rfl
      comm₂₃ := by
        dsimp [S]
        simp [relativeSingularChainsMap] }
  have h₁ : QuasiIso φ.τ₁ := by
    rw [quasiIso_iff]
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hIso j
  have h₂ : QuasiIso φ.τ₂ := by dsimp [φ]; infer_instance
  have : QuasiIso φ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
      (shortExact_singularSubspaceChains R A) (shortExact_singularSubspaceChains R B) h₁ h₂
  exact (ConcreteCategory.isIso_iff_bijective
    (HomologicalComplex.homologyMap φ.τ₃ k)).mp inferInstance

end AtiyahSinger
