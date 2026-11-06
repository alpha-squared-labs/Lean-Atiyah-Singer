/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCochainCup
public import AtiyahSinger.Topology.RelativeSingularFunctoriality
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Exactness of the original relative cochains

Public module ID: M2062.

For every subspace, restriction of ordinary cochains is surjective degree by
degree: extend a coefficient function from its embedded singular simplices.
The original relative cochains are the kernel. Thus the original complexes
form the usual short exact sequence over every commutative coefficient ring.

This is the singular cochain proof of the pair long exact sequence in Hatcher,
Algebraic Topology, section 3.1. It does not assume dualization is exact on
arbitrary modules, and does not replace the original singular chain model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The canonical relative-to-ordinary-to-subspace sequence of the original cochain complexes. -/
def singularSubspaceCochainsSequence (A : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) where
  X₁ := relativeSingularCochains R A
  X₂ := singularCochains R X
  X₃ := singularCochains R A
  f := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  g := (singularCochainDualFunctor R).map (singularSubspaceChains R A).op
  zero := by
    have : (singularCochainDualFunctor.{u} R).Additive := by
      change (((((linearYoneda R (ModuleCat.{u} R)).obj
        (singularCoefficient R)).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).op) ⋙
          HomologicalComplex.unopFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)).Additive
      infer_instance
    rw [← Functor.map_comp, ← op_comp, cokernel.condition, op_zero, Functor.map_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Original relative and ordinary cochains form a short exact sequence for every subspace. -/
theorem shortExact_singularSubspaceCochains (A : Set X) :
    (singularSubspaceCochainsSequence R A).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
  intro n
  let S := (singularSubspaceCochainsSequence R A).map
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n)
  have hmono : Mono S.f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro φ ψ h
    change (relativeSingularChains R A).X n ⟶ singularCoefficient R at φ ψ
    apply (cancel_epi ((relativeSingularChainsProjection R A).f n)).mp
    exact h
  have hepi : Epi S.g := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro φ
    let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let g := TopCat.toSSet.map (TopCat.ofHom i)
    let j := g.app (op ⦋n⦌)
    have hj : Function.Injective j := by
      intro σ τ h
      apply ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).injective
      ext t
      exact congrArg (fun σ ↦ (TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ t) h
    let ψ := (singularCochainEquiv R X n).symm
      (Function.extend j (singularCochainEquiv R A n φ) 0)
    refine ⟨ψ, ?_⟩
    apply (singularCochainEquiv R A n).injective
    funext σ
    change (show (singularChains R X).X n ⟶ singularCoefficient R from ψ)
      (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex σ ≫
        (SSet.chainComplexMap g (singularCoefficient R)).f n) (ULift.up 1)) = _
    rw [SSet.ι_chainComplexMap_f]
    change singularCochainEquiv R X n ψ (j σ) = _
    rw [LinearEquiv.apply_symm_apply, Function.Injective.extend_apply hj]
  refine { mono_f := hmono, epi_g := hepi, exact := ?_ }
  -- The original quotient universal property identifies the kernel with relative cochains.
  apply (ShortComplex.moduleCat_exact_iff S).mpr
  intro φ hφ
  let a := (relativeSingularCochainEquiv R A n).symm ⟨φ, hφ⟩
  refine ⟨a, ?_⟩
  exact congrArg Subtype.val ((relativeSingularCochainEquiv R A n).apply_symm_apply ⟨φ, hφ⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A contractible relative neighborhood can be replaced by one of its points.
The map is the original restriction of the relative cochain condition. -/
theorem isIso_relativeSingularCohomologyRestriction_singleton
    (B : Set X) (x : X) (hx : x ∈ B) [ContractibleSpace B] (n : ℕ) :
    IsIso (relativeSingularCohomologyRestriction R ({x} : Set X) B
      (Set.singleton_subset_iff.mpr hx) n) := by
  let A : Set X := {x}
  let hAB : A ⊆ B := Set.singleton_subset_iff.mpr hx
  let i : C(A, B) := ⟨fun a ↦ ⟨a.val, hAB a.property⟩, continuous_subtype_val.subtype_mk _⟩
  let r : C(B, A) := ContinuousMap.const _ ⟨x, Set.mem_singleton x⟩
  have hri : r.comp i = ContinuousMap.id A := by
    ext a
    exact (Set.mem_singleton_iff.mp a.property).symm
  have hir : (i.comp r).Homotopic (ContinuousMap.id B) := by
    obtain ⟨y, h⟩ := id_nullhomotopic B
    have h' := ContinuousMap.Homotopic.comp h (.refl (i.comp r))
    change (i.comp r).Homotopic (ContinuousMap.const B y) at h'
    exact h'.trans h.symm
  have hi (k : ℕ) : IsIso (singularCohomologyPullback R i k) := by
    let H := singularCohomologyFunctor R k
    have h₁ : singularCohomologyPullback R i k ≫ singularCohomologyPullback R r k = 𝟙 _ := by
      change H.map (TopCat.ofHom i).op ≫ H.map (TopCat.ofHom r).op = _
      rw [← H.map_comp, ← op_comp]
      change singularCohomologyPullback R (i.comp r) k = _
      obtain ⟨h⟩ := hir
      rw [singularCohomologyPullback_homotopic R h]
      exact H.map_id _
    have h₂ : singularCohomologyPullback R r k ≫ singularCohomologyPullback R i k = 𝟙 _ := by
      change H.map (TopCat.ofHom r).op ≫ H.map (TopCat.ofHom i).op = _
      rw [← H.map_comp, ← op_comp]
      change singularCohomologyPullback R (r.comp i) k = _
      rw [hri]
      exact H.map_id _
    exact ⟨singularCohomologyPullback R r k, h₁, h₂⟩
  let D := singularCochainDualFunctor R
  let I := (relativeSingularChainsFunctor R X).map (homOfLE hAB)
  let J := (singularChainsFunctor R).map (TopCat.ofHom i)
  let φ : singularSubspaceCochainsSequence R B ⟶ singularSubspaceCochainsSequence R A :=
    { τ₁ := D.map I.op
      τ₂ := 𝟙 (singularCochains R X)
      τ₃ := D.map J.op
      comm₁₂ := by
        change D.map I.op ≫ D.map (relativeSingularChainsProjection R A).op = _
        rw [← D.map_comp, ← op_comp]
        have hq : relativeSingularChainsProjection R A ≫ I =
            relativeSingularChainsProjection R B := by
          simp [I, relativeSingularChainsFunctor, relativeSingularChainsMap]
        rw [hq]
        exact (Category.comp_id _).symm
      comm₂₃ := by
        change 𝟙 _ ≫ D.map (singularSubspaceChains R A).op =
          D.map (singularSubspaceChains R B).op ≫ D.map J.op
        rw [Category.id_comp, ← D.map_comp, ← op_comp]
        congr 1
        apply congrArg Quiver.Hom.op
        change singularSubspaceChains R A = J ≫ singularSubspaceChains R B
        simp only [J, singularSubspaceChains, ← Functor.map_comp]
        rfl }
  have hB := shortExact_singularSubspaceCochains R B
  have hA := shortExact_singularSubspaceCochains R A
  have h₂ (k : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₂ k) := by
    change IsIso (HomologicalComplex.homologyMap (𝟙 _) k)
    infer_instance
  have h₃ (k : ℕ) : IsIso (HomologicalComplex.homologyMap φ.τ₃ k) := hi k
  change IsIso (HomologicalComplex.homologyMap φ.τ₁ n)
  -- The pair long exact sequences compare the same relative restriction maps.
  open HomologicalComplex HomologySequence ComposableArrows CategoryTheory.Abelian in
  cases n with
  | zero =>
    apply isIso_of_isIso_of_mono (mapComposableArrows₂ φ 0)
      (composableArrows₂_exact hB 0) (composableArrows₂_exact hA 0)
    · have := hB.mono_f
      apply mono_homologyMap_of_mono_of_not_rel
      simp
    · have := hA.mono_f
      apply mono_homologyMap_of_mono_of_not_rel
      simp
    · exact h₂ 0
    · change Mono (HomologicalComplex.homologyMap φ.τ₃ 0)
      have := h₃ 0
      infer_instance
  | succ k =>
    apply isIso_of_epi_of_isIso_of_isIso_of_mono
      (composableArrows₅_exact hB k (k + 1) rfl).δ₀
      (composableArrows₅_exact hA k (k + 1) rfl).δ₀
      (δ₀Functor.map (mapComposableArrows₅ φ hB hA k (k + 1) rfl))
    · exact (h₂ k).epi_of_iso
    · exact h₃ k
    · exact h₂ (k + 1)
    · exact (h₃ (k + 1)).mono_of_iso

end AtiyahSinger
