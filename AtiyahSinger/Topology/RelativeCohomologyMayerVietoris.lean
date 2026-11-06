/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologySequence

/-!
# Mayer–Vietoris for the original relative singular cochains

Public module ID: M2065.

The diagonal-and-difference sequence of relative chains is split in each
individual degree: delete exactly the simplices lying in either subspace.
Dualizing those splittings gives the cochain Mayer–Vietoris sequence over
any commutative coefficient ring. The splitting is not asserted to commute
with the differential. The existing open-union excision comparison identifies
its first cohomology term with the cohomology of the actual union pair.

This is the ordinary singular-chain proof of relative Mayer–Vietoris,
Hatcher, Algebraic Topology, sections 2.1 and 3.1. It supplies the native
connecting morphisms needed for compact-support gluing.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- Dual of the actual relative diagonal-and-difference chain sequence. -/
def relativeSingularCochainMayerVietorisSequence (A B : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  (relativeSingularMayerVietorisShortComplex R A B).op.map (singularCochainDualFunctor R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The relative cochain Mayer–Vietoris sequence is short exact
over every commutative coefficient ring. -/
theorem shortExact_relativeSingularCochainMayerVietorisSequence (A B : Set X) :
    (relativeSingularCochainMayerVietorisSequence R A B).ShortExact := by
  classical
  let S := relativeSingularMayerVietorisShortComplex R A B
  apply shortExact_singularCochainDual_of_degreewiseSplit R S
  intro n
  let ev := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let D := S.map ev
  have hD : D.ShortExact :=
    (shortExact_relativeSingularMayerVietorisShortComplex R A B).map_of_exact ev
  let C := singularChains R X
  let Q := relativeUnionSingularChainsProjection R A B
  let inc (U : Set X) := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
  let J (U : Set X) := Set.range ((inc U).app (op ⦋n⦌))
  -- On the free simplex generators, retain just the complement of both subspace images.
  let P : C.X n ⟶ C.X n := Sigma.desc fun σ ↦
    if σ ∈ J A ∪ J B then 0 else (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ
  have hP (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) :
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫ P =
        if σ ∈ J A ∪ J B then 0 else
          (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ := Sigma.ι_comp_desc _ _
  have hkill (U : Set X) (hU : J U ⊆ J A ∪ J B) :
      (singularSubspaceChains R U).f n ≫ P = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    change (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex σ ≫
      (SSet.chainComplexMap (inc U) (singularCoefficient R)).f n ≫ P = _
    rw [← Category.assoc, SSet.ι_chainComplexMap_f, hP]
    simp only [hU ⟨σ, rfl⟩, ↓reduceIte, comp_zero]
  have hkillA := hkill A Set.subset_union_left
  have hkillB := hkill B Set.subset_union_right
  have hkillSum : (singularSubspaceSumChains R A B).f n ≫ P = 0 := by
    have hsum := congrArg (fun f ↦ f.f n)
      (biprod.desc_eq (f := singularSubspaceChains R A) (g := singularSubspaceChains R B))
    change (singularSubspaceSumChains R A B).f n = _ at hsum
    rw [hsum]
    change ((biprod.fst : singularChains R A ⊞ singularChains R B ⟶
      singularChains R A).f n ≫ (singularSubspaceChains R A).f n +
      (biprod.snd : singularChains R A ⊞ singularChains R B ⟶
      singularChains R B).f n ≫ (singularSubspaceChains R B).f n) ≫ P = 0
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, hkillA, hkillB]
    simp
  have hquot (U : Set X) (hU : U = A ∨ U = B) :
      (singularSubspaceChains R U).f n ≫ Q.f n = 0 := by
    rcases hU with hU | hU
    · subst U
      have h := congrArg (fun f ↦
        (biprod.inl : singularChains R A ⟶ singularChains R A ⊞ singularChains R B) ≫ f)
        (show singularSubspaceSumChains R A B ≫ Q = 0 from cokernel.condition _)
      rw [← Category.assoc] at h
      change (biprod.inl ≫ biprod.desc (singularSubspaceChains R A)
        (singularSubspaceChains R B)) ≫ Q = _ at h
      rw [biprod.inl_desc, comp_zero] at h
      exact congrArg (fun f ↦ f.f n) h
    · subst U
      have h := congrArg (fun f ↦
        (biprod.inr : singularChains R B ⟶ singularChains R A ⊞ singularChains R B) ≫ f)
        (show singularSubspaceSumChains R A B ≫ Q = 0 from cokernel.condition _)
      rw [← Category.assoc] at h
      change (biprod.inr ≫ biprod.desc (singularSubspaceChains R A)
        (singularSubspaceChains R B)) ≫ Q = _ at h
      rw [biprod.inr_desc, comp_zero] at h
      exact congrArg (fun f ↦ f.f n) h
  have hfix : P ≫ Q.f n = Q.f n := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, hP]
    by_cases hσ : σ ∈ J A ∪ J B
    · rw [ite_eq_left hσ, zero_comp]
      rcases hσ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · have h := congrArg (fun f ↦
          (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫ f) (hquot A (Or.inl rfl))
        change (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
          (SSet.chainComplexMap (inc A) (singularCoefficient R)).f n ≫ Q.f n = _ at h
        rw [← Category.assoc, SSet.ι_chainComplexMap_f, comp_zero] at h
        exact h.symm
      · have h := congrArg (fun f ↦
          (TopCat.toSSet.obj (TopCat.of B)).ιChainComplex τ ≫ f) (hquot B (Or.inr rfl))
        change (TopCat.toSSet.obj (TopCat.of B)).ιChainComplex τ ≫
          (SSet.chainComplexMap (inc B) (singularCoefficient R)).f n ≫ Q.f n = _ at h
        rw [← Category.assoc, SSet.ι_chainComplexMap_f, comp_zero] at h
        exact h.symm
    · rw [ite_eq_right hσ]
  -- Descend that degreewise projection through precisely the original sum quotient.
  let colim := isColimitOfHasCokernelOfPreservesColimit ev (singularSubspaceSumChains R A B)
  let sectionQ := CokernelCofork.IsColimit.desc' colim P hkillSum
  have hsectionQ : Q.f n ≫ sectionQ.val = P := sectionQ.property
  have hleft : relativeSingularChainsProjection R A ≫
      (biprod.inl : relativeSingularChains R A ⟶
        relativeSingularChains R A ⊞ relativeSingularChains R B) ≫ S.g = Q := by
    simp [S, Q, relativeSingularMayerVietorisShortComplex, relativeSingularChainsProjection]
  let s : D.X₃ ⟶ D.X₂ := sectionQ.val ≫ (relativeSingularChainsProjection R A).f n ≫
    (biprod.inl : relativeSingularChains R A ⟶
      relativeSingularChains R A ⊞ relativeSingularChains R B).f n
  have hs : s ≫ D.g = 𝟙 _ := by
    apply (cancel_epi (Q.f n)).mp
    change Q.f n ≫ (sectionQ.val ≫ (relativeSingularChainsProjection R A).f n ≫
      (biprod.inl : relativeSingularChains R A ⟶
        relativeSingularChains R A ⊞ relativeSingularChains R B).f n) ≫ S.g.f n = _
    have hleftn := congrArg (fun f ↦ f.f n) hleft
    simp only [HomologicalComplex.comp_f] at hleftn
    rw [Category.assoc, Category.assoc, hleftn, ← Category.assoc, hsectionQ, hfix]
    exact (Category.comp_id (Q.f n)).symm
  -- The split chain sequence dualizes in reverse order; no exactness of arbitrary duals is used.
  exact ShortComplex.Splitting.ofExactOfSection D hD.exact s hs hD.mono_f

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual map of two subspace pairs gives a map of their original Mayer–Vietoris sequences.
Dualizing this map supplies naturality of the connecting maps, including support enlargement. -/
def relativeSingularMayerVietorisMap {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) {A B : Set X} {A' B' : Set Y}
    (hfA : Set.MapsTo f A A') (hfB : Set.MapsTo f B B') :
    relativeSingularMayerVietorisShortComplex R A B ⟶
      relativeSingularMayerVietorisShortComplex R A' B' := by
  let S := relativeSingularMayerVietorisShortComplex R A B
  let T := relativeSingularMayerVietorisShortComplex R A' B'
  let F := (singularChainsFunctor R).map (TopCat.ofHom f)
  let fA : C(A, A') := ⟨fun x ↦ ⟨f x.val, hfA x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let fB : C(B, B') := ⟨fun x ↦ ⟨f x.val, hfB x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let FA := (singularChainsFunctor R).map (TopCat.ofHom fA)
  let FB := (singularChainsFunctor R).map (TopCat.ofHom fB)
  have hA : singularSubspaceChains R A ≫ F = FA ≫ singularSubspaceChains R A' := by
    simp only [F, FA, singularSubspaceChains, ← Functor.map_comp]
    rfl
  have hB : singularSubspaceChains R B ≫ F = FB ≫ singularSubspaceChains R B' := by
    simp only [F, FB, singularSubspaceChains, ← Functor.map_comp]
    rfl
  -- Both quotient maps come from the same ambient chain map, before any dualization.
  let C := cokernel.map (singularSubspaceSumChains R A B)
    (singularSubspaceSumChains R A' B') (biprod.map FA FB) F (by
      apply biprod.hom_ext'
      · simpa only [singularSubspaceSumChains, biprod.inl_desc_assoc,
          biprod.inl_map_assoc, biprod.inl_desc, Category.assoc] using hA
      · simpa only [singularSubspaceSumChains, biprod.inr_desc_assoc,
          biprod.inr_map_assoc, biprod.inr_desc, Category.assoc] using hB)
  let a := relativeSingularChainsMap R f hfA
  let b := relativeSingularChainsMap R f hfB
  let c := relativeSingularChainsMap R f
    (A := A ∩ B) (B := A' ∩ B') (fun _ hx ↦ ⟨hfA hx.1, hfB hx.2⟩)
  have hqa : relativeSingularChainsProjection R A ≫ a =
      F ≫ relativeSingularChainsProjection R A' := by
    simp [a, F, relativeSingularChainsMap, relativeSingularChainsProjection]
  have hqb : relativeSingularChainsProjection R B ≫ b =
      F ≫ relativeSingularChainsProjection R B' := by
    simp [b, F, relativeSingularChainsMap, relativeSingularChainsProjection]
  have hqc : relativeSingularChainsProjection R (A ∩ B) ≫ c =
      F ≫ relativeSingularChainsProjection R (A' ∩ B') := by
    simp [c, F, relativeSingularChainsMap, relativeSingularChainsProjection]
  have hqC : relativeUnionSingularChainsProjection R A B ≫ C =
      F ≫ relativeUnionSingularChainsProjection R A' B' := by
    simp [C]
  have hdiag₁ {Z : Type u} [TopologicalSpace Z] (U V : Set Z) :
      relativeSingularChainsProjection R (U ∩ V) ≫
        (relativeSingularMayerVietorisShortComplex R U V).f ≫ biprod.fst =
          relativeSingularChainsProjection R U := by
    simp [relativeSingularMayerVietorisShortComplex, relativeSingularChainsFunctor,
      relativeSingularChainsMap, relativeSingularChainsProjection]
  have hdiag₂ {Z : Type u} [TopologicalSpace Z] (U V : Set Z) :
      relativeSingularChainsProjection R (U ∩ V) ≫
        (relativeSingularMayerVietorisShortComplex R U V).f ≫ biprod.snd =
          relativeSingularChainsProjection R V := by
    simp [relativeSingularMayerVietorisShortComplex, relativeSingularChainsFunctor,
      relativeSingularChainsMap, relativeSingularChainsProjection]
  have hdiff₁ {Z : Type u} [TopologicalSpace Z] (U V : Set Z) :
      relativeSingularChainsProjection R U ≫ biprod.inl ≫
        (relativeSingularMayerVietorisShortComplex R U V).g =
          relativeUnionSingularChainsProjection R U V := by
    simp [relativeSingularMayerVietorisShortComplex, relativeSingularChainsProjection]
  have hdiff₂ {Z : Type u} [TopologicalSpace Z] (U V : Set Z) :
      relativeSingularChainsProjection R V ≫ biprod.inr ≫
        (relativeSingularMayerVietorisShortComplex R U V).g =
          -relativeUnionSingularChainsProjection R U V := by
    simp [relativeSingularMayerVietorisShortComplex, relativeSingularChainsProjection]
  refine { τ₁ := c, τ₂ := biprod.map a b, τ₃ := C, comm₁₂ := ?_, comm₂₃ := ?_ }
  · -- Check the two diagonal components on ambient simplex representatives.
    apply biprod.hom_ext
    · apply (cancel_epi (relativeSingularChainsProjection R (A ∩ B))).mp
      change _ ≫ (c ≫ T.f) ≫ biprod.fst = _ ≫ (S.f ≫ biprod.map a b) ≫ biprod.fst
      rw [Category.assoc, ← Category.assoc _ c, hqc, Category.assoc, hdiag₁,
        Category.assoc, biprod.map_fst]
      simpa only [Category.assoc] using
        (congrArg (fun k ↦ k ≫ a) (hdiag₁ A B)).trans hqa |>.symm
    · apply (cancel_epi (relativeSingularChainsProjection R (A ∩ B))).mp
      change _ ≫ (c ≫ T.f) ≫ biprod.snd = _ ≫ (S.f ≫ biprod.map a b) ≫ biprod.snd
      rw [Category.assoc, ← Category.assoc _ c, hqc, Category.assoc, hdiag₂,
        Category.assoc, biprod.map_snd]
      simpa only [Category.assoc] using
        (congrArg (fun k ↦ k ≫ b) (hdiag₂ A B)).trans hqb |>.symm
  · -- The difference signs on both sides are inherited from the same original sequence.
    apply biprod.hom_ext'
    · apply (cancel_epi (relativeSingularChainsProjection R A)).mp
      change _ ≫ biprod.inl ≫ biprod.map a b ≫ T.g = _ ≫ biprod.inl ≫ S.g ≫ C
      rw [biprod.inl_map_assoc, ← Category.assoc, hqa, Category.assoc, hdiff₁]
      simpa only [Category.assoc] using
        (congrArg (fun k ↦ k ≫ C) (hdiff₁ A B)).trans hqC |>.symm
    · apply (cancel_epi (relativeSingularChainsProjection R B)).mp
      change _ ≫ biprod.inr ≫ biprod.map a b ≫ T.g = _ ≫ biprod.inr ≫ S.g ≫ C
      rw [biprod.inr_map_assoc, ← Category.assoc, hqb, Category.assoc, hdiff₂,
        Preadditive.comp_neg]
      have h := congrArg (fun k ↦ k ≫ C) (hdiff₂ A B)
      rw [Preadditive.neg_comp, hqC] at h
      simpa only [Category.assoc] using h.symm

end AtiyahSinger
