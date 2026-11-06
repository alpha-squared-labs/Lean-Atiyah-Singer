/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteDimensionalProductThom
public import AtiyahSinger.Topology.RelativeSupportedCohomologyThom

/-!
# Relative product Thom multiplication on an original open pair

Public module ID: M2085.

The same specified fiber generator gives the two-relative external cup
bijection for any pair consisting of a space and an open subspace. The
proof compares the actual cochain right-cup maps on the product and its
open restriction. It preserves the original supports and factor order.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex
open scoped unitInterval

universe u

variable (R : Type) [CommRing R]

private theorem isIso_productProjection (X : Type u) [TopologicalSpace X]
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :
    IsIso (singularCohomologyPullback R (ContinuousMap.fst : C(X × V, X)) k) := by
  let s : C(X, X × V) := ⟨fun x ↦ (x, 0), continuous_id.prodMk continuous_const⟩
  have hscale : (s.comp (ContinuousMap.fst : C(X × V, X))).Homotopic
      (ContinuousMap.id (X × V)) := by
    refine ⟨{ toFun := fun z ↦ (z.2.1, (z.1 : ℝ) • z.2.2)
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · exact continuous_snd.fst.prodMk (continuous_fst.subtype_val.smul continuous_snd.snd)
    · intro z
      exact Prod.ext rfl (zero_smul ℝ z.2)
    · intro z
      exact Prod.ext rfl (one_smul ℝ z.2)
  exact isIso_singularCohomologyPullback_of_homotopyInverse R ContinuousMap.fst s
    hscale ⟨ContinuousMap.Homotopy.refl _⟩ k

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem cupMap_bijective_of_productModel
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin r))
    (A : Set Y) (f : C(X × V, Y)) (g : C(Y, X × V))
    (hf : Set.MapsTo f {z | z.2 ≠ 0} A) (hg : Set.MapsTo g A {z | z.2 ≠ 0})
    (hgf : g.comp f = ContinuousMap.id _) (hfg : f.comp g = ContinuousMap.id _)
    (c : relativeSingularCocycles R A r)
    (hgen : ∀ x : X, Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R
        (⟨fun v : V ↦ (x, v), continuous_const.prodMk continuous_id⟩ : C(V, X × V))
        (A := {v | v ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hv ↦ hv) r
        (relativeSingularCohomologyPullback R f hf r
          (relativeSingularCocycleClass R A r c)))) (n : ℕ) :
    Function.Bijective (homologyMap (relativeSingularCochainCupMap R A r c) n) := by
  let B : Set (X × V) := {z | z.2 ≠ 0}
  let T := relativeSingularCocycleClass R A r c
  let J (k : ℕ) := relativeSingularCohomologyPullback R f hf k
  have hJ (k : ℕ) : IsIso (J k) :=
    isIso_relativeSingularCohomologyPullback_of_inverse R f g hf hg hgf hfg k
  have hF (k : ℕ) : IsIso (singularCohomologyPullback R f k) := by
    apply isIso_singularCohomologyPullback_of_homotopyInverse R f g
    · rw [hgf]
    · rw [hfg]
  let d : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  by_cases hn : r ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    have hprod := relativeSingularCohomologyAction_prod_bijective_of_linearEquiv
      R X r e (J r T) hgen p
    have := isIso_productProjection R X V p
    have haction : Function.Bijective (fun a : singularCohomology R (X × V) p ↦
        relativeSingularCohomologyAction R B p r a (J r T)) :=
      (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso
        (singularCohomologyPullback R (ContinuousMap.fst : C(X × V, X)) p))).mp hprod
    have := hF p
    have hcomp := haction.comp
      (ConcreteCategory.bijective_of_isIso (singularCohomologyPullback R f p))
    have hformula : (fun a : singularCohomology R Y p ↦
        relativeSingularCohomologyAction R B p r
          (singularCohomologyPullback R f p a) (J r T)) =
        J (p + r) ∘ (fun a ↦ relativeSingularCohomologyAction R A p r a T) := by
      funext a
      exact (relativeSingularCohomologyPullback_action R f hf p r a T).symm
    change Function.Bijective (fun a : singularCohomology R Y p ↦
      relativeSingularCohomologyAction R B p r
        (singularCohomologyPullback R f p a) (J r T)) at hcomp
    rw [hformula] at hcomp
    have := hJ (p + r)
    have hright := ((ConcreteCategory.bijective_of_isIso (J (p + r))).of_comp_iff' _).mp hcomp
    -- At or above the rank, the cochain map has exactly the original ordered cup action.
    let shiftIso := (singularCochains R Y).extendHomologyIso d (j := p) rfl
    apply (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso shiftIso.inv)).mp
    have hcup : homologyMap (relativeSingularCochainCupMap R A r c) (p + r) ∘ shiftIso.inv =
        (fun a : singularCohomology R Y p ↦ relativeSingularCohomologyAction R A p r a T) :=
      funext fun a ↦ homologyMap_relativeSingularCochainCupMap R A r c p a
    rw [hcup]
    exact hright
  · -- Below the rank, both the full target and the extended source have zero homology.
    have hnr : n < r := Nat.lt_of_not_ge hn
    let := subsingleton_relativeSingularCohomology_prod_below_of_linearEquiv R X r e n hnr
    have := hJ n
    have htarget : Subsingleton (relativeSingularCohomology R A n) :=
      (ConcreteCategory.bijective_of_isIso (J n)).injective.subsingleton
    have hsource : Subsingleton (((singularCochains R Y).extend d).homology n) := by
      apply ModuleCat.isZero_iff_subsingleton.mp
      apply (exactAt_iff_isZero_homology _ _).mp
      exact extend_exactAt _ d n (by
        intro p hp
        change p + r = n at hp
        omega)
    exact ⟨fun _ _ _ ↦ hsource.elim _ _, fun a ↦ ⟨0, htarget.elim _ a⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified fiber generator gives the actual two-relative external Thom cup bijection. -/
theorem relativeSingularCohomologyUnionCup_prod_bijective
    (X : Type u) [TopologicalSpace X]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (S : Set X) (hS : IsOpen S)
    (τ : relativeSingularCohomology R {v : V | v ≠ 0} r)
    (hτ : Function.Bijective (fun a : R ↦ a • τ)) (p : ℕ) :
    Function.Bijective (fun a : relativeSingularCohomology R S p ↦
      relativeSingularCohomologyUnionCup R {z : X × V | z.1 ∈ S} {z : X × V | z.2 ≠ 0}
        (hS.preimage continuous_fst) (isOpen_ne_fun continuous_snd continuous_const) p r
        (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(X × V, X))
          (A := {z | z.1 ∈ S}) (B := S) (fun _ hz ↦ hz) p a)
        (relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × V, V))
          (A := {z | z.2 ≠ 0}) (B := {v | v ≠ 0}) (fun _ hz ↦ hz) r τ)) := by
  let A : Set (X × V) := {z | z.2 ≠ 0}
  let B : Set (X × V) := {z | z.1 ∈ S}
  let t := relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × V, V))
    (A := A) (B := {v | v ≠ 0}) (fun _ hz ↦ hz) r τ
  let T := relativeUnionSingularCochainSequence R A B
  -- Choose a cocycle for the specified pullback class and restrict that very cocycle to B.
  obtain ⟨c, hc⟩ := (relativeSingularCoboundaries R A r).mkQ_surjective
    (((relativeSingularCochains R A).sc r).moduleCatHomologyIso.hom t)
  have hct : relativeSingularCocycleClass R A r c = t := by
    change ((relativeSingularCochains R A).sc r).moduleCatHomologyIso.inv
      ((relativeSingularCoboundaries R A r).mkQ c) = t
    rw [hc]
    exact congrArg (fun f ↦ f t)
      ((relativeSingularCochains R A).sc r).moduleCatHomologyIso.hom_inv_id
  let cB : relativeSingularCocycles R ((Subtype.val : B → X × V) ⁻¹' A) r :=
    ⟨T.g.f r c.val, by
      change T.X₃.dFrom r (T.g.f r c.val) = 0
      have h := congrArg (fun f ↦ f c.val) (T.g.comm_from r)
      change T.X₃.dFrom r (T.g.f r c.val) = T.g.next r (T.X₂.dFrom r c.val) at h
      have hclosed : T.X₂.dFrom r c.val = 0 := c.property
      rw [h, hclosed, map_zero]⟩
  have hcB : relativeSingularCocycleClass R ((Subtype.val : B → X × V) ⁻¹' A) r cB =
      relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
        (A := (Subtype.val : B → X × V) ⁻¹' A) (B := A) (fun _ hz ↦ hz) r t := by
    have h := homologyMap_cycleClass R T.X₂ T.X₃ T.g r c cB rfl
    change relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
      (A := (Subtype.val : B → X × V) ⁻¹' A) (B := A) (fun _ hz ↦ hz) r
        (relativeSingularCocycleClass R A r c) =
      relativeSingularCocycleClass R ((Subtype.val : B → X × V) ⁻¹' A) r cB at h
    rw [hct] at h
    exact h.symm
  have hglobal : ∀ n, Function.Bijective
      (homologyMap (relativeSingularCochainCupMap R A r c) n) := by
    apply cupMap_bijective_of_productModel R X (X × V) r e A
      (ContinuousMap.id _) (ContinuousMap.id _) (fun _ hz ↦ hz) (fun _ hz ↦ hz) rfl rfl c
    intro x
    have hpoint : relativeSingularCohomologyPullback R
        (⟨fun v : V ↦ (x, v), continuous_const.prodMk continuous_id⟩ : C(V, X × V))
        (A := {v | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r
        (relativeSingularCohomologyPullback R (ContinuousMap.id (X × V))
          (A := A) (B := A) (fun _ hz ↦ hz) r
          (relativeSingularCocycleClass R A r c)) = τ := by
      rw [hct]
      dsimp only [t]
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp,
        ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      change relativeSingularCohomologyPullback R (ContinuousMap.id V)
        (A := {v | v ≠ 0}) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) r τ = τ
      simp [relativeSingularCohomologyPullback, relativeSingularChainsMap,
        CategoryTheory.Limits.cokernel.map]
    exact (congrArg Function.Bijective (funext
      (fun a : R ↦ congrArg (fun z ↦ a • z) hpoint))).mpr hτ
  -- The original restricted product is identified with S × V by its literal two coordinates.
  let f : C(S × V, B) :=
    ⟨fun z ↦ ⟨(z.1.val, z.2), z.1.property⟩,
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _⟩
  let g : C(B, S × V) :=
    ⟨fun z ↦ (⟨z.val.1, z.property⟩, z.val.2),
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)⟩
  have hgf : g.comp f = ContinuousMap.id _ := by ext z <;> rfl
  have hfg : f.comp g = ContinuousMap.id _ := by ext z <;> rfl
  have hf : Set.MapsTo f {z : S × V | z.2 ≠ 0} ((Subtype.val : B → X × V) ⁻¹' A) :=
    fun _ hz ↦ hz
  have hg : Set.MapsTo g ((Subtype.val : B → X × V) ⁻¹' A) {z : S × V | z.2 ≠ 0} :=
    fun _ hz ↦ hz
  have hrestricted : ∀ n, Function.Bijective (homologyMap
      (relativeSingularCochainCupMap R ((Subtype.val : B → X × V) ⁻¹' A) r cB) n) := by
    apply cupMap_bijective_of_productModel R S B r e _ f g hf hg hgf hfg cB
    intro x
    have hpoint : relativeSingularCohomologyPullback R
        (⟨fun v : V ↦ (x, v), continuous_const.prodMk continuous_id⟩ : C(V, S × V))
        (A := {v | v ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hv ↦ hv) r
        (relativeSingularCohomologyPullback R f hf r
          (relativeSingularCocycleClass R ((Subtype.val : B → X × V) ⁻¹' A) r cB)) = τ := by
      rw [hcB]
      dsimp only [t]
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp,
        ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp,
        ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      change relativeSingularCohomologyPullback R (ContinuousMap.id V)
        (A := {v | v ≠ 0}) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) r τ = τ
      simp [relativeSingularCohomologyPullback, relativeSingularChainsMap,
        CategoryTheory.Limits.cokernel.map]
    exact (congrArg Function.Bijective (funext
      (fun a : R ↦ congrArg (fun z ↦ a • z) hpoint))).mpr hτ
  have hcup := relativeSingularCohomologyUnionCup_bijective_of_cupMap R A B
    (isOpen_ne_fun continuous_snd continuous_const) (hS.preimage continuous_fst)
    r c cB rfl hglobal hrestricted p
  rw [hct] at hcup
  -- Projection is a pair equivalence: scaling the vector preserves S at every time.
  have hproj (k : ℕ) : IsIso
      (singularCohomologyPullback R (ContinuousMap.fst : C(X × V, X)) k) :=
    isIso_productProjection R X V k
  let prB : C(B, S) := ⟨fun z ↦ ⟨z.val.1, z.property⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩
  let zeroB : C(S, B) := ⟨fun x ↦ ⟨(x.val, 0), x.property⟩,
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩
  have hscale : (zeroB.comp prB).Homotopic (ContinuousMap.id B) := by
    refine ⟨{ toFun := fun z ↦ ⟨(z.2.val.1, (z.1 : ℝ) • z.2.val.2), z.2.property⟩
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · exact ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
        (continuous_fst.subtype_val.smul
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
    · intro z
      exact Subtype.ext (Prod.ext rfl (zero_smul ℝ z.val.2))
    · intro z
      exact Subtype.ext (Prod.ext rfl (one_smul ℝ z.val.2))
  have hprojB (k : ℕ) : IsIso (singularCohomologyPullback R prB k) :=
    isIso_singularCohomologyPullback_of_homotopyInverse R prB zeroB hscale
      ⟨ContinuousMap.Homotopy.refl _⟩ k
  have := isIso_relativeSingularCohomologyPullback_of_absolute R
    (ContinuousMap.fst : C(X × V, X)) (A := B) (B := S) (fun _ hz ↦ hz) hproj hprojB p
  exact hcup.comp (ConcreteCategory.bijective_of_isIso
    (relativeSingularCohomologyPullback R (ContinuousMap.fst : C(X × V, X))
      (A := B) (B := S) (fun _ hz ↦ hz) p))

end AtiyahSinger
