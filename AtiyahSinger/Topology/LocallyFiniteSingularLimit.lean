/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocallyFiniteSingularHomology
public import AtiyahSinger.Topology.RelativeSingularChainCoordinates
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Locally finite chains and compact exhaustions

Public module ID: M1954.

The original compact-relative restriction retains precisely the coefficients
of simplices that meet the compact control. Compatible relative chains over
a compact exhaustion therefore determine an actual locally finite coefficient
function, and these same restrictions detect equality. These comparisons are
at chain level; no interchange of homology and an inverse limit is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The compact restriction preserves each coefficient of a simplex meeting the control. -/
theorem locallyFiniteSingularChainRestriction_coordinates
    (K : Compacts X) (n : ℕ) (c : locallyFiniteSingularChainModule R X n)
    (σ : {σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) //
      ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ (K : Set X)ᶜ}) :
    relativeSingularChainCoordinates R ((K : Set X)ᶜ) n
      (locallyFiniteSingularChainRestriction R X K n c) σ = c.val σ.val := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  let meet (τ : S.obj (op ⦋n⦌)) :=
    (Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) ∩ (K : Set X)).Nonempty
  have hmeet (τ : S.obj (op ⦋n⦌)) :
      meet τ ↔ ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) ⊆ (K : Set X)ᶜ := by
    constructor
    · rintro ⟨x, hx, hxK⟩ h
      exact h hx hxK
    · intro h
      by_contra h'
      apply h
      intro x hx hxK
      exact h' ⟨x, hx, hxK⟩
  let term (τ : S.obj (op ⦋n⦌)) : (relativeSingularChains R ((K : Set X)ᶜ)).X n :=
    if meet τ then (relativeSingularChainsProjection R ((K : Set X)ᶜ)).f n
      (S.ιChainComplex (R := singularCoefficient R) τ (ULift.up (c.val τ))) else 0
  have hfinite : (Function.support term).Finite := by
    apply (locallyFiniteSingularChainModule_finite_meeting R X K n c).subset
    intro τ hτ
    change term τ ≠ 0 at hτ
    simp only [term] at hτ
    split_ifs at hτ with hm
    · refine ⟨?_, hm⟩
      intro hc
      apply hτ
      rw [hc]
      change (relativeSingularChainsProjection R ((K : Set X)ᶜ)).f n
        (S.ιChainComplex (R := singularCoefficient R) τ (0 : ULift.{u} R)) = 0
      rw [map_zero]
      exact map_zero _
    · exact (hτ rfl).elim
  let ev : (relativeSingularChains R ((K : Set X)ᶜ)).X n →ₗ[R] R :=
    (Finsupp.lapply σ).comp (relativeSingularChainCoordinates R ((K : Set X)ᶜ) n).toLinearMap
  change ev (∑ᶠ τ, term τ) = c.val σ.val
  rw [map_finsum _ hfinite]
  have hterm (τ : S.obj (op ⦋n⦌)) :
      ev (term τ) = if τ = σ.val then c.val τ else 0 := by
    by_cases hm : meet τ
    · simp only [term, hm, ↓reduceIte]
      change (relativeSingularChainCoordinates R ((K : Set X)ᶜ) n
        ((relativeSingularChainsProjection R ((K : Set X)ᶜ)).f n
          (S.ιChainComplex (R := singularCoefficient R) τ (ULift.up (c.val τ))))) σ = _
      rw [relativeSingularChainCoordinates_apply_generator]
      simp [(hmeet τ).mp hm, Finsupp.single_apply, Subtype.ext_iff]
    · have hne : τ ≠ σ.val := by
        intro h
        exact hm (h ▸ (hmeet σ.val).mpr σ.property)
      simp [term, hm, hne]
  simp_rw [hterm]
  rw [finsum_eq_single _ σ.val (fun τ hτ ↦ by simp [hτ])]
  simp

/-- A compatible family over a compact exhaustion is one actual locally finite chain. -/
theorem existsUnique_locallyFiniteSingularChain_of_exhaustion
    (K : CompactExhaustion X) (n : ℕ)
    (c : ∀ i : ℕ, (relativeSingularChains R (K i)ᶜ).X n)
    (hc : ∀ i : ℕ,
      (relativeSingularChainsMap R (ContinuousMap.id X)
        (fun _ hx ↦ (Set.compl_subset_compl.mpr (K.subset_succ i)) hx)).f n (c (i + 1)) = c i) :
    ∃! a : locallyFiniteSingularChainModule R X n, ∀ i : ℕ,
      locallyFiniteSingularChainRestriction R X ⟨K i, K.isCompact i⟩ n a = c i := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  let P (i : ℕ) (σ : S.obj (op ⦋n⦌)) :=
    ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ (K i)ᶜ
  have hP (i : ℕ) (σ : S.obj (op ⦋n⦌)) :
      P i σ ↔ (Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ∩ K i).Nonempty := by
    constructor
    · intro h
      by_contra h'
      apply h
      intro x hx hxK
      exact h' ⟨x, hx, hxK⟩
    · rintro ⟨x, hx, hxK⟩ h
      exact h hx hxK
  have hmono {i j : ℕ} (hij : i ≤ j) {σ : S.obj (op ⦋n⦌)} (hσ : P i σ) : P j σ :=
    fun h ↦ hσ (h.trans (Set.compl_subset_compl.mpr (K.subset hij)))
  let coord (i : ℕ) (σ : S.obj (op ⦋n⦌)) (hσ : P i σ) : R :=
    relativeSingularChainCoordinates R (K i)ᶜ n (c i) ⟨σ, hσ⟩
  -- The original pair transition preserves the coefficient of every surviving simplex.
  have hstep (i : ℕ) (σ : S.obj (op ⦋n⦌)) (hσ : P i σ) :
      coord (i + 1) σ (hmono (Nat.le_succ i) hσ) = coord i σ hσ := by
    have h := relativeSingularChainCoordinates_inclusion_apply R
      (K (i + 1))ᶜ (K i)ᶜ (Set.compl_subset_compl.mpr (K.subset_succ i)) n
      (c (i + 1)) ⟨σ, hσ⟩
    rw [hc i] at h
    exact h.symm
  have hstable {i j : ℕ} (hij : i ≤ j) (σ : S.obj (op ⦋n⦌)) (hσ : P i σ) :
      coord j σ (hmono hij hσ) = coord i σ hσ := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hij ih => exact (hstep j σ (hmono hij hσ)).trans ih
  -- A fixed vertex makes each original simplex meet some stage of the exhaustion.
  let point (σ : S.obj (op ⦋n⦌)) : X :=
    ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) (Convexity.StdSimplex.single 0)
  let stage (σ : S.obj (op ⦋n⦌)) : ℕ := K.find (point σ)
  have hstage (σ : S.obj (op ⦋n⦌)) : P (stage σ) σ :=
    (hP _ _).mpr ⟨point σ, ⟨Convexity.StdSimplex.single 0, rfl⟩, K.mem_find (point σ)⟩
  let a (σ : S.obj (op ⦋n⦌)) : R := coord (stage σ) σ (hstage σ)
  have ha (i : ℕ) (σ : S.obj (op ⦋n⦌)) (hσ : P i σ) : a σ = coord i σ hσ := by
    let j := max i (stage σ)
    exact (hstable (show stage σ ≤ j from le_max_right _ _) σ (hstage σ)).symm.trans
      (hstable (show i ≤ j from le_max_left _ _) σ hσ)
  have hloc : IsLocallyFiniteSingularChain R X n a := by
    -- A compact stage is a neighborhood of each given point. Its finite coordinate
    -- support controls every nonzero global simplex meeting this neighborhood.
    intro x
    obtain ⟨i, hi⟩ := K.exists_mem_nhds x
    let v := relativeSingularChainCoordinates R (K i)ᶜ n (c i)
    have hfin := v.support.finite_toSet.image Subtype.val
    refine ⟨K i, hi, (hfin.preimage Subtype.val_injective.injOn).subset ?_⟩
    intro σ hσ
    have hp : P i σ.val := (hP i σ.val).mpr hσ
    refine ⟨⟨σ.val, hp⟩, ?_, rfl⟩
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact σ.property ((ha i σ.val hp).trans hz)
  let chain : locallyFiniteSingularChainModule R X n := ⟨a, hloc⟩
  have hrestrict (i : ℕ) :
      locallyFiniteSingularChainRestriction R X ⟨K i, K.isCompact i⟩ n chain = c i := by
    apply (relativeSingularChainCoordinates R (K i)ᶜ n).injective
    ext σ
    exact (locallyFiniteSingularChainRestriction_coordinates R
      ⟨K i, K.isCompact i⟩ n chain σ).trans (ha i σ.val σ.property)
  refine ⟨chain, hrestrict, ?_⟩
  -- Every simplex is detected at its chosen stage, so the actual restrictions separate chains.
  intro b hb
  apply Subtype.ext
  funext σ
  have h := congrArg (fun d ↦ relativeSingularChainCoordinates R (K (stage σ))ᶜ n d
    ⟨σ, hstage σ⟩) (hb (stage σ))
  exact (locallyFiniteSingularChainRestriction_coordinates R
    ⟨K (stage σ), K.isCompact (stage σ)⟩ n b ⟨σ, hstage σ⟩).symm.trans h

/-- Restrictions along a compact exhaustion detect equality of actual locally finite chains. -/
theorem locallyFiniteSingularChainRestriction_exhaustion_injective
    (K : CompactExhaustion X) (n : ℕ) :
    Function.Injective (fun a : locallyFiniteSingularChainModule R X n ↦
      fun i : ℕ ↦ locallyFiniteSingularChainRestriction R X ⟨K i, K.isCompact i⟩ n a) := by
  intro a b hab
  apply Subtype.ext
  funext σ
  let x := ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) (Convexity.StdSimplex.single 0)
  obtain ⟨i, hi⟩ := K.exists_mem x
  have hσ : ¬ Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ (K i)ᶜ :=
    fun h ↦ h ⟨Convexity.StdSimplex.single 0, rfl⟩ hi
  have h := congrArg (fun d ↦ relativeSingularChainCoordinates R (K i)ᶜ n d ⟨σ, hσ⟩)
    (congrFun hab i)
  exact (locallyFiniteSingularChainRestriction_coordinates R
    ⟨K i, K.isCompact i⟩ n a ⟨σ, hσ⟩).symm.trans
      (h.trans (locallyFiniteSingularChainRestriction_coordinates R
        ⟨K i, K.isCompact i⟩ n b ⟨σ, hσ⟩))

end AtiyahSinger
