/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasDifferentialPseudodifferential

import AtiyahSinger.Geometry.AtlasFrameTransition

/-!
# The identity in the atlas pseudodifferential calculus

Public module ID: M0286.

The actual identity section map is an order-zero differential operator, including
between different frames of the same locally varying-rank atlas. Its intrinsic
symbol is the fiber identity, hence its PDO principal class is the identity class.
This supplies the zero-th power for the parametrix geometric series without any
constant-rank reduction or replacement of the original section space.
Source: SG III.1 and III.3, applied to the order-zero identity differential operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- The original identity map has the usual order-zero expressions in every frame pair. -/
def atlasIdentityDifferentialOperator : AtlasDifferentialOperator A A 0 where
  toLinearMap := LinearMap.id
  isAtlasDifferentialOperator := by
    classical
    intro c hc i j x hx
    let U := c.source ∩ (A.chart i).baseSet ∩ (A.chart j).baseSet
    have hU : IsOpen U := (c.open_source.inter (A.chart i).open_baseSet).inter
      (A.chart j).open_baseSet
    have hcU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ c.symm (c '' U) := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact (contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) hc) (c.map_source hy.1.1)).contMDiffWithinAt
    have hcover : Set.MapsTo c.symm (c '' U)
        ((A.chart i).baseSet ∩ (A.chart j).baseSet) := by
      rintro z ⟨y, hy, rfl⟩
      rw [c.left_inv hy.1.1]
      exact ⟨hy.1.2, hy.2⟩
    let Q : CoordinateDifferentialOperator n (A.rank i) (A.rank j) 0 (c '' U) :=
      { coefficient := fun _ _ z ↦ A.coordChangeL i j (c.symm z)
        smooth_coefficient := fun _ _ ↦ A.contDiffOn_coordChangeL_comp i j _ _ hcU hcover }
    refine ⟨U, hU, hx, Q, Set.Subset.rfl, ?_⟩
    intro u y hy
    -- At order zero the only coefficient is the actual old-to-new frame transition.
    simp only [LinearMap.id_coe, id_eq, PiLp.continuousLinearEquiv_symm_apply,
      CoordinateDifferentialOperator.apply, Nat.reduceAdd, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero, pow_zero, one_smul,
      Finset.sum_singleton, Fin.coe_ofNat_eq_mod, Nat.zero_mod, iteratedFDeriv_zero_apply,
      atlasSectionInChart, Finset.sum_const, Finset.card_singleton, Q]
    rw [c.left_inv hy.1.1]
    exact A.coordChangeL_apply i j y ⟨hy.1.2, hy.2⟩ (u.val y)

/-- The leading polynomial of the order-zero identity is the fiber identity at every covector. -/
private theorem principalSymbol_atlasIdentityDifferentialOperator :
    (atlasIdentityDifferentialOperator A).principalSymbol = fun _ _ ↦ LinearMap.id := by
  classical
  have exists_section_value (x : M) (v : E x) :
      ∃ s : A.smoothSections, s.val x = v := by
    classical
    let H := EuclideanSpace ℝ (Fin n)
    let c := chartAt H x
    obtain ⟨i, hxi⟩ := A.covers x
    have hcx : c x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet := by
      exact ⟨c.map_source (mem_chart_source H x), by simpa [c] using hxi⟩
    have hU : IsOpen (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :=
      c.isOpen_inter_preimage_symm (A.chart i).open_baseSet
    obtain ⟨b, _, hb⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, H)) (c x)).mem_iff.mp
        (hU.mem_nhds hcx)
    let L : AtlasChartCutoff A c := {
      frameIndex := i
      cutoff := b
      smooth_cutoff := b.contMDiff.contDiff
      compact_support := b.hasCompactSupport
      support_subset := hb }
    let e := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
    let a := e.symm (A.frameLinearEquiv i x hxi v)
    have hcompact : HasCompactSupport (fun z : H ↦ b z • a) :=
      b.hasCompactSupport.smul_right
    have hsmooth : ContDiff ℝ ∞ (fun z : H ↦ b z • a) :=
      b.contMDiff.contDiff.smul contDiff_const
    let f : 𝓢(H, EuclideanSpace ℂ (Fin (A.rank i))) := hcompact.toSchwartzMap hsmooth
    refine ⟨L.extend (chart_mem_atlas H x) f, ?_⟩
    -- Both original cutoffs have value one, so the specified frame inverse recovers v.
    have hvalid : x ∈ c.source ∩ (A.chart i).baseSet := ⟨mem_chart_source H x, hxi⟩
    change L.extendedFunction f x = v
    simp only [AtlasChartCutoff.extendedFunction, L, dite_eq_left hvalid]
    change (b (c x) : ℂ) • (A.frameLinearEquiv i x hxi).symm (e (b (c x) • a)) = v
    rw [b.eq_one, Complex.ofReal_one, one_smul, one_smul]
    rw [show e a = A.frameLinearEquiv i x hxi v from e.apply_symm_apply _]
    exact (A.frameLinearEquiv i x hxi).symm_apply_apply v
  funext x ξ
  apply LinearMap.ext
  intro v
  obtain ⟨s, hs⟩ := exists_section_value x v
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨i, hxi⟩ := A.covers x
  obtain ⟨U, hU, hxU, Q, hQ⟩ :=
    (atlasIdentityDifferentialOperator A).isAtlasDifferentialOperator c
      (chart_mem_atlas _ x) i i x ⟨⟨mem_chart_source _ x, hxi⟩, hxi⟩
  have hsymbol := (atlasIdentityDifferentialOperator A).hasAtlasPrincipalSymbol c
    (chart_mem_atlas _ x) i i U hU Q hQ x hxU ξ v
  have hvalue := hQ.2 s x hxU
  have hformula : Q.apply (atlasSectionInChart A c i s.val) (c x) =
      Q.principalSymbol (c x) (covectorInChart c x ξ)
        ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm ((A.chart i ⟨x, v⟩).2)) := by
    simp only [CoordinateDifferentialOperator.apply, Nat.reduceAdd, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero, pow_zero, one_smul,
      Finset.sum_singleton, Fin.coe_ofNat_eq_mod, Nat.zero_mod, iteratedFDeriv_zero_apply,
      atlasSectionInChart, PiLp.continuousLinearEquiv_symm_apply,
      CoordinateDifferentialOperator.principalSymbol, Finset.univ_eq_empty,
      Finset.prod_empty, Fin.zero_eta]
    rw [c.left_inv (mem_chart_source _ x), hs]
  rw [hformula] at hvalue
  change (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
    ((A.chart i ⟨x, s.val x⟩).2) = _ at hvalue
  rw [hs] at hvalue
  apply (A.frameLinearEquiv i x hxi).injective
  apply (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.injective
  exact hsymbol.trans hvalue.symm

/-- The standard order-zero identity symbol on the original atlas fibers. -/
def atlasGlobalIdentitySymbol : atlasGlobalSymbolSpace A A 0 :=
  ⟨fun _ _ ↦ LinearMap.id, by
    change IsAtlasGlobalSymbol A A 0 (fun _ _ ↦ LinearMap.id)
    rw [← principalSymbol_atlasIdentityDifferentialOperator A]
    simpa only [Nat.cast_zero] using
      (atlasIdentityDifferentialOperator A).isAtlasGlobalSymbol_principalSymbol⟩

namespace AtlasPseudodifferentialOperator

variable [CompactSpace M]

/-- The actual identity on the original smooth sections as an order-zero PDO. -/
def id : AtlasPseudodifferentialOperator A A 0 where
  toLinearMap := LinearMap.id
  isPseudodifferentialOperator := by
    simpa only [Nat.cast_zero, atlasIdentityDifferentialOperator] using
      (atlasIdentityDifferentialOperator A).isAtlasPseudodifferentialOperator

set_option backward.isDefEq.respectTransparency false in
/-- Its principal class is the class of the same full fiber-identity symbol. -/
theorem principalSymbol_id :
    (id A).principalSymbol = atlasGlobalPrincipalSymbolClass A A 0
      (atlasGlobalIdentitySymbol A) := by
  -- Transport the entire operator-symbol comparison at once, preserving both witnesses.
  have transfer (t : ℝ) (ht : t = 0)
      (hT : IsAtlasPseudodifferentialOperator A A t LinearMap.id)
      (ha : IsAtlasGlobalSymbol A A t (fun _ _ ↦ LinearMap.id))
      (hpr : (show AtlasPseudodifferentialOperator A A t from
          ⟨LinearMap.id, hT⟩).principalSymbol =
        atlasGlobalPrincipalSymbolClass A A t ⟨fun _ _ ↦ LinearMap.id, ha⟩) :
      (id A).principalSymbol = atlasGlobalPrincipalSymbolClass A A 0
        (atlasGlobalIdentitySymbol A) := by
    subst t
    exact hpr
  have ha : IsAtlasGlobalSymbol A A ((0 : ℕ) : ℝ) (fun _ _ ↦ LinearMap.id) := by
    rw [← principalSymbol_atlasIdentityDifferentialOperator A]
    exact (atlasIdentityDifferentialOperator A).isAtlasGlobalSymbol_principalSymbol
  have hT : IsAtlasPseudodifferentialOperator A A ((0 : ℕ) : ℝ) LinearMap.id :=
    (atlasIdentityDifferentialOperator A).isAtlasPseudodifferentialOperator
  apply transfer ((0 : ℕ) : ℝ) (Nat.cast_zero) hT ha
  have h := (atlasIdentityDifferentialOperator A).principalSymbol_toAtlasPseudodifferentialOperator
  simp only [AtlasDifferentialOperator.principalGlobalSymbol,
    principalSymbol_atlasIdentityDifferentialOperator] at h
  exact h


end AtlasPseudodifferentialOperator

end AtiyahSinger
