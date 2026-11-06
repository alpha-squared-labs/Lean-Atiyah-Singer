/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleMapPseudodifferential
public import AtiyahSinger.Analysis.AtlasPseudodifferentialComposition
public import AtiyahSinger.Geometry.AtlasSectionEquiv
public import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Conjugating an atlas PDO by the specified smooth bundle isomorphisms

Public module ID: M0228.

The two multiplication PDOs transport the given operator to the target atlas
section spaces. Its full principal representative is the original fiberwise
conjugate. The same section equivalences identify the actual kernel and quotient
cokernel, hence preserve the index. No globally constant rank, ellipticity or
new smooth atlas is imposed. This is the change-of-bundle form of SG III.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F E' F' : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
  [TopologicalSpace (TotalSpace Unit E')]
  [∀ x, AddCommGroup (F' x)] [∀ x, Module ℂ (F' x)]
  [TopologicalSpace (TotalSpace Unit F')]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {A' : SmoothComplexBundleAtlas (n := n) E'}
  {B' : SmoothComplexBundleAtlas (n := n) F'}

set_option maxSynthPendingDepth 30 in
/-- Smooth bundle conjugation retains the operator, its principal representative and index. -/
theorem AtlasPseudodifferentialOperator.exists_bundleIso_conjugate {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m)
    (e : Iso E E') (f : Iso F F')
    (he : IsSmoothAtlasBundleMap A A' e.toHom.linearMap)
    (hei : IsSmoothAtlasBundleMap A' A e.symm.toHom.linearMap)
    (hf : IsSmoothAtlasBundleMap B B' f.toHom.linearMap)
    (hfi : IsSmoothAtlasBundleMap B' B f.symm.toHom.linearMap)
    (p : atlasGlobalSymbolSpace A B m)
    (hp : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m p) :
    ∃ hq : IsAtlasGlobalSymbol A' B' m
        (fun x ξ ↦ (f.toHom.linearMap x).comp
          ((p.val x ξ).comp (e.symm.toHom.linearMap x))),
      ∃ Q : AtlasPseudodifferentialOperator A' B' m,
        Q.toLinearMap = (atlasSmoothSectionEquiv B B' f hf hfi).toLinearMap.comp
          (P.toLinearMap.comp (atlasSmoothSectionEquiv A A' e he hei).symm.toLinearMap) ∧
        Q.principalSymbol = atlasGlobalPrincipalSymbolClass A' B' m
          ⟨(fun x ξ ↦ (f.toHom.linearMap x).comp
            ((p.val x ξ).comp (e.symm.toHom.linearMap x))), hq⟩ ∧
        Q.toLinearMap.index = P.toLinearMap.index := by
  classical
  let S := atlasSmoothSectionEquiv A A' e he hei
  let T := atlasSmoothSectionEquiv B B' f hf hfi
  -- Both outer operators are multiplication by the specified original fiber maps.
  obtain ⟨hu, U, hU, hUsymbol⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap A' A e.symm.toHom.linearMap hei
  obtain ⟨hv, V, hV, hVsymbol⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap B B' f.toHom.linearMap hf
  let q : AtlasSymbolFunction (n := n) E' F' := fun x ξ ↦
    (f.toHom.linearMap x).comp ((p.val x ξ).comp (e.symm.toHom.linearMap x))
  have hq : IsAtlasGlobalSymbol A' B' (0 + (m + 0)) q :=
    hv.atlasSymbolComp (p.property.atlasSymbolComp hu)
  let Q := V.comp (P.comp U)
  have haction : Q.toLinearMap = T.toLinearMap.comp (P.toLinearMap.comp S.symm.toLinearMap) := by
    change V.toLinearMap.comp (P.toLinearMap.comp U.toLinearMap) = _
    rw [hU, hV]
    rfl
  have hsymbol : Q.principalSymbol =
      atlasGlobalPrincipalSymbolClass A' B' (0 + (m + 0)) ⟨q, hq⟩ := by
    rw [AtlasPseudodifferentialOperator.principalSymbol_comp,
      AtlasPseudodifferentialOperator.principalSymbol_comp, hUsymbol, hVsymbol, hp,
      atlasGlobalPrincipalSymbolComp_class, atlasGlobalPrincipalSymbolComp_class]
    rfl
  -- Intertwining by these same equivalences transports the two actual defects.
  have hinter (u : A.smoothSections) : Q.toLinearMap (S u) = T (P.toLinearMap u) := by
    rw [haction]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, S.symm_apply_apply]
  let kerEquiv : P.toLinearMap.ker ≃ₗ[ℂ] Q.toLinearMap.ker := {
    toFun u := ⟨S u.val, by rw [LinearMap.mem_ker, hinter, u.property, map_zero]⟩
    invFun u := ⟨S.symm u.val, by
      apply T.injective
      rw [map_zero, ← hinter, S.apply_symm_apply]
      exact u.property⟩
    left_inv u := Subtype.ext (S.symm_apply_apply u.val)
    right_inv u := Subtype.ext (S.apply_symm_apply u.val)
    map_add' u v := Subtype.ext (S.map_add u.val v.val)
    map_smul' z u := Subtype.ext (S.map_smul z u.val) }
  have hrange : P.toLinearMap.range.map T.toLinearMap = Q.toLinearMap.range := by
    ext v
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨S u, hinter u⟩
    · rintro ⟨u, rfl⟩
      exact ⟨P.toLinearMap (S.symm u), ⟨S.symm u, rfl⟩,
        (hinter (S.symm u)).symm.trans (congrArg Q.toLinearMap (S.apply_symm_apply u))⟩
  let cokerEquiv := Submodule.Quotient.equiv P.toLinearMap.range Q.toLinearMap.range T hrange
  have hindex : Q.toLinearMap.index = P.toLinearMap.index := by
    rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
      kerEquiv.finrank_eq, cokerEquiv.finrank_eq]
  -- Transport the entire package across the real-order identity, keeping all witnesses together.
  have htransfer (l : ℝ) (hl : l = m)
      (h : ∃ hq : IsAtlasGlobalSymbol A' B' l q,
        ∃ Q : AtlasPseudodifferentialOperator A' B' l,
          Q.toLinearMap = T.toLinearMap.comp (P.toLinearMap.comp S.symm.toLinearMap) ∧
          Q.principalSymbol = atlasGlobalPrincipalSymbolClass A' B' l ⟨q, hq⟩ ∧
          Q.toLinearMap.index = P.toLinearMap.index) :
      ∃ hq : IsAtlasGlobalSymbol A' B' m q,
        ∃ Q : AtlasPseudodifferentialOperator A' B' m,
          Q.toLinearMap = T.toLinearMap.comp (P.toLinearMap.comp S.symm.toLinearMap) ∧
          Q.principalSymbol = atlasGlobalPrincipalSymbolClass A' B' m ⟨q, hq⟩ ∧
          Q.toLinearMap.index = P.toLinearMap.index := by
    subst l
    exact h
  exact htransfer _ (by simp only [zero_add, add_zero]) ⟨hq, Q, haction, hsymbol, hindex⟩

end AtiyahSinger
