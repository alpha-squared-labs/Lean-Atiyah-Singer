/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CountableHomologyLifting
public import AtiyahSinger.Topology.LocallyFiniteSingularLimit

/-!
# Realization of compatible compact-relative homology

Public module ID: M1951.

A compact exhaustion identifies the actual locally finite chain groups with
compatible families in the original relative chain quotients. These quotients
have surjective transition maps. Vanishing in the next homology degree makes
preceding cycles lift as well, so the countable chain-lifting argument gives a
unique actual locally finite homology class with the prescribed restrictions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits TopologicalSpace

universe u

/-- Compatible compact-relative classes have one locally finite realization
when the next compact-relative homology groups vanish. -/
theorem existsUnique_locallyFiniteSingularHomology_of_exhaustion
    (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
    (K : CompactExhaustion X) (n : ℕ)
    (hvan : ∀ i : ℕ, Subsingleton (relativeSingularHomology R (K i)ᶜ (n + 1)))
    (z : ∀ i : ℕ, relativeSingularHomology R (K i)ᶜ n)
    (hz : ∀ i : ℕ, relativeSingularHomologyInclusion R (K (i + 1))ᶜ (K i)ᶜ
      (Set.compl_subset_compl.mpr (K.subset_succ i)) n (z (i + 1)) = z i) :
    ∃! a : locallyFiniteSingularHomology R X n, ∀ i : ℕ,
      locallyFiniteSingularHomologyRestriction R ⟨K i, K.isCompact i⟩ n a = z i := by
  let C (i : ℕ) := relativeSingularChains R (K i)ᶜ
  let t (i : ℕ) : C (i + 1) ⟶ C i :=
    relativeSingularChainsMap R (ContinuousMap.id X)
      (fun _ hx ↦ (Set.compl_subset_compl.mpr (K.subset_succ i)) hx)
  let L := locallyFiniteSingularChains R X
  let q (i : ℕ) : L ⟶ C i :=
    locallyFiniteSingularChainsRestriction R X ⟨K i, K.isCompact i⟩
  have hq (i : ℕ) : q (i + 1) ≫ t i = q i :=
    locallyFiniteSingularChainsRestriction_inclusion R X
      (K := ⟨K i, K.isCompact i⟩) (L := ⟨K (i + 1), K.isCompact (i + 1)⟩)
      (K.subset_succ i)
  have ht (i j : ℕ) : Function.Surjective ((t i).f j) := by
    -- Every transition is the quotient map on the same ambient chains.
    have hp : relativeSingularChainsProjection R (K (i + 1))ᶜ ≫ t i =
        relativeSingularChainsProjection R (K i)ᶜ := by
      simp [t, relativeSingularChainsMap, relativeSingularChainsProjection]
    have hpj := congrArg (fun f ↦ f.f j) hp
    have : Epi ((t i).f j) := epi_of_epi_fac hpj
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  let F := HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  have hcycles (i : ℕ) : ∀ a : (F.obj (C i)).X₁, (F.obj (C i)).f a = 0 →
      ∃ b : (F.obj (C (i + 1))).X₁,
        (F.obj (C (i + 1))).f b = 0 ∧ (F.map (t i)).τ₁ b = a := by
    -- A preceding cycle bounds by the next-degree vanishing. Lift that bounding
    -- chain through the surjective transition, then take its boundary upstairs.
    change ∀ a : (C i).X ((ComplexShape.down ℕ).prev n),
      (C i).d ((ComplexShape.down ℕ).prev n) n a = 0 →
        ∃ b : (C (i + 1)).X ((ComplexShape.down ℕ).prev n),
          (C (i + 1)).d ((ComplexShape.down ℕ).prev n) n b = 0 ∧
            (t i).f ((ComplexShape.down ℕ).prev n) b = a
    rw [ChainComplex.prev]
    intro a ha
    let := hvan i
    have hexact : (C i).ExactAt (n + 1) :=
      ((C i).exactAt_iff_isZero_homology (n + 1)).mpr
        (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
    have hshort : ((C i).sc' (n + 2) (n + 1) n).Exact :=
      ((C i).exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).mp hexact
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp hshort a ha
    obtain ⟨b', hb'⟩ := ht i (n + 2) b
    refine ⟨(C (i + 1)).d (n + 2) (n + 1) b', ?_, ?_⟩
    · change ((C (i + 1)).d (n + 2) (n + 1) ≫ (C (i + 1)).d (n + 1) n) b' = 0
      rw [HomologicalComplex.d_comp_d]
      rfl
    · have h := congrArg (fun f ↦ f b') ((t i).comm (n + 2) (n + 1))
      exact h.symm.trans (by rw [ModuleCat.comp_apply, hb']; exact hb)
  -- Apply the countable lifting result to the original three-term complexes.
  change ∃! a : (F.obj L).homology,
    ∀ i : ℕ, ShortComplex.homologyMap (F.map (q i)) a = z i
  refine existsUnique_homology_of_surjective_tower R
    (fun i ↦ F.obj (C i)) (fun i ↦ F.map (t i)) (F.obj L) (fun i ↦ F.map (q i))
    (fun i ↦ by rw [← F.map_comp, hq]) ?_ ?_ ?_ ?_ ?_ hcycles z hz
  · intro c hc
    exact (existsUnique_locallyFiniteSingularChain_of_exhaustion R K
      ((ComplexShape.down ℕ).prev n) c hc).exists
  · intro c hc
    exact (existsUnique_locallyFiniteSingularChain_of_exhaustion R K n c hc).exists
  · intro x y h
    exact locallyFiniteSingularChainRestriction_exhaustion_injective R K n (funext h)
  · intro x y h
    exact locallyFiniteSingularChainRestriction_exhaustion_injective R K
      ((ComplexShape.down ℕ).next n) (funext h)
  · intro i
    exact ht i ((ComplexShape.down ℕ).prev n)

end AtiyahSinger
