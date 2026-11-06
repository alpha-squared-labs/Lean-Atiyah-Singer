/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantSupportTripleKZero

/-!
# Forgetting the action of a trivial group

Public module ID: M2263.

For a subsingleton group every action on the original bundle is forced by the
identity law. Ordinary bundle maps and support-triple relations consequently
retain their full equivariant meaning. The forgetful map is an isomorphism of
the existing presentations, without changing the specified base action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Subsingleton G] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E F : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- The unique action over the specified base action of a subsingleton group. -/
def EquivariantStructure.ofSubsingleton (E : X → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] : EquivariantStructure G E := by
  have hbase (g : G) (x : X) : x = g • x := by
    rw [Subsingleton.elim g 1, one_smul]
  let L (g : G) (x : X) : E x →ₗ[ℂ] E (g • x) :=
    (LinearEquiv.cast (R := ℂ) (M := E) (hbase g x)).toLinearMap
  have hcast (x y : X) (h : x = y) (v : E x) :
      (⟨y, LinearEquiv.cast (R := ℂ) (M := E) h v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
    subst y
    rfl
  have hL (g : G) (x : X) (v : E x) :
      (⟨g • x, L g x v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := hcast x _ (hbase g x) v
  exact {
    linearMap := L
    one_map := hL 1
    mul_map := fun g h x v ↦ (hL (g * h) x v).trans
      ((hL g (h • x) (L h x v)).trans (hL h x v)).symm
    continuous_action := continuous_snd.congr (fun p ↦ (hL p.1 p.2.proj p.2.snd).symm) }

/-- The identity action law determines every fiber map for a subsingleton group. -/
theorem EquivariantStructure.eq_of_subsingleton (σ τ : EquivariantStructure G E) : σ = τ := by
  have hmap : σ.linearMap = τ.linearMap := by
    funext g x
    apply LinearMap.ext
    intro v
    have hg : g = 1 := Subsingleton.elim g 1
    subst g
    exact TotalSpace.mk_injective _ ((σ.one_map x v).trans (τ.one_map x v).symm)
  cases σ
  cases τ
  cases hmap
  rfl

/-- Every bundle map intertwines the original actions of a subsingleton group. -/
theorem Hom.isEquivariant_of_subsingleton (f : Hom E F)
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) :
    f.IsEquivariant σ τ := by
  intro g x v
  have hg : g = 1 := Subsingleton.elim g 1
  subst g
  apply TotalSpace.mk_injective ((1 : G) • x)
  exact (congrArg (fun z : TotalSpace Unit E ↦
    (⟨z.proj, f.linearMap z.proj z.snd⟩ : TotalSpace Unit F))
      (σ.one_map x v)).trans (τ.one_map x (f.linearMap x v)).symm

/-- Every original support triple is equivariant for the unique bundle actions. -/
theorem CompactSupportTriple.isEquivariant_of_subsingleton (a : CompactSupportTriple E F)
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) :
    a.IsEquivariant σ τ := by
  classical
  have hInv (g : G) (x : X) : g • x ∈ a.control ↔ x ∈ a.control := by
    rw [Subsingleton.elim g 1, one_smul]
  refine ⟨hInv, ?_⟩
  intro g x v
  have hg : g = 1 := Subsingleton.elim g 1
  subst g
  let B (z : TotalSpace Unit E) : TotalSpace Unit F :=
    if h : z.proj ∈ a.control then ⟨z.proj, 0⟩ else
      ⟨z.proj, a.boundary.linearEquiv ⟨z.proj, h⟩ z.snd⟩
  have hx : x.val ∉ a.control := x.property
  have hnot : (1 : G) • x.val ∉ a.control := by simpa only [one_smul] using hx
  have htotal := congrArg B (σ.one_map x.val v)
  simp only [B, hnot, hx, dite_false] at htotal
  apply TotalSpace.mk_injective ((1 : G) • x.val)
  exact htotal.trans (τ.one_map x.val (a.boundary.linearEquiv x v)).symm

/-- Forgetting a subsingleton action is bijective on the original support-triple group. -/
theorem equivariantSupportTripleKZeroForget_bijective_of_subsingleton :
    Function.Bijective (equivariantSupportTripleKZeroForget (G := G) (X := X)) := by
  -- Equip every original triple with the forced action, retaining its compact control.
  let B (a : SupportBundleTriple X) : EquivariantSupportBundleTriple G X :=
    ⟨a, { sourceAction := EquivariantStructure.ofSubsingleton a.source.Fiber
          targetAction := EquivariantStructure.ofSubsingleton a.target.Fiber
          isEquivariant := a.datum.isEquivariant_of_subsingleton _ _ }⟩
  have hlift (a b : EquivariantSupportBundleTriple G X) (h : a.1.IsIsomorphic b.1) :
      a.IsIsomorphic b := by
    obtain ⟨K, hK, ha, hb, u, v, hsquare⟩ := h
    refine ⟨K, hK, ?_, ha, hb, u, v,
      u.toHom.isEquivariant_of_subsingleton _ _,
      v.toHom.isEquivariant_of_subsingleton _ _, hsquare⟩
    intro g x
    rw [Subsingleton.elim g 1, one_smul]
  obtain ⟨hi, hs, hz⟩ :=
    equivariantSupportTripleKZero_generator_relations (G := G) (X := X)
  have hBi (a b : SupportBundleTriple X) (h : a.IsIsomorphic b) :
      (B a).kZeroClass = (B b).kZeroClass := hi _ _ (hlift _ _ h)
  have hBs (a b : SupportBundleTriple X) :
      (B (a.sum b)).kZeroClass = (B a).kZeroClass + (B b).kZeroClass := by
    exact (hi _ _ (hlift _ _ (a.sum b).isIsomorphic_refl)).trans (hs (B a) (B b))
  have hBz (E : FiniteBundle X) : (B (SupportBundleTriple.identity E)).kZeroClass = 0 := by
    exact (hi _ _ (hlift _ _ (SupportBundleTriple.identity E).isIsomorphic_refl)).trans
      (hz E (EquivariantStructure.ofSubsingleton E.Fiber))
  -- All three ordinary relations lift, so the inverse descends through the same presentation.
  obtain ⟨L, hL, _⟩ := supportTripleKZero_universal_property X
    (fun a ↦ (B a).kZeroClass) hBi hBs hBz
  let F := equivariantSupportTripleKZeroForget (G := G) (X := X)
  have hsame (a : EquivariantSupportBundleTriple G X) :
      (B a.1).kZeroClass = a.kZeroClass := hi _ _ (hlift _ _ a.1.isIsomorphic_refl)
  -- The identity comparison uses the original generators, including their supplied actions.
  obtain ⟨J, _hJ, hJu⟩ := equivariantSupportTripleKZero_universal_property
    (fun a : EquivariantSupportBundleTriple G X ↦ a.kZeroClass) hi hs hz
  have hLF : L.comp F = AddMonoidHom.id _ := by
    apply (hJu _ ?_).trans (hJu _ (fun _ ↦ rfl)).symm
    intro a
    change L (equivariantSupportTripleKZeroForget a.kZeroClass) = a.kZeroClass
    rw [equivariantSupportTripleKZeroForget_apply, hL, hsame]
  obtain ⟨J', _hJ', hJu'⟩ := supportTripleKZero_universal_property X
    (fun a ↦ a.kZeroClass)
    (fun a b h ↦ a.kZeroClass_eq_of_isIsomorphic b h)
    SupportBundleTriple.kZeroClass_sum SupportBundleTriple.kZeroClass_identity
  have hFL : F.comp L = AddMonoidHom.id _ := by
    apply (hJu' _ ?_).trans (hJu' _ (fun _ ↦ rfl)).symm
    intro a
    change equivariantSupportTripleKZeroForget (L a.kZeroClass) = a.kZeroClass
    rw [hL, equivariantSupportTripleKZeroForget_apply]
  refine ⟨?_, ?_⟩
  · intro x y h
    have hx := DFunLike.congr_fun hLF x
    have hy := DFunLike.congr_fun hLF y
    exact hx.symm.trans ((congrArg L h).trans hy)
  · intro x
    exact ⟨L x, DFunLike.congr_fun hFL x⟩

/-- Equality after forgetting a subsingleton action already holds in the equivariant group. -/
theorem equivariantSupportTripleKZeroForget_injective_of_subsingleton :
    Function.Injective (equivariantSupportTripleKZeroForget (G := G) (X := X)) :=
  equivariantSupportTripleKZeroForget_bijective_of_subsingleton.injective

end AtiyahSinger.ComplexBundle
