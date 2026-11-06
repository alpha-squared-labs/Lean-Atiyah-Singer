/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCapProduct
public import AtiyahSinger.Topology.RelativeSingularMayerVietoris
public import AtiyahSinger.Topology.SingularCechCochains
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Small representatives for the original relative singular homology

Public module ID: M2159.

The absolute small-chain comparisons on both spaces of a pair induce an
isomorphism on the actual relative chain cokernels. Consequently every
relative homology class has a representative small for any specified open
cover. This allows supported cap arguments to use one common representative.

Source: Hatcher, Algebraic Topology, section 2.1, subdivision and excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Inclusion of the actual small relative chain quotient induces homology isomorphisms. -/
theorem isIso_homologyMap_smallRelativeSingularChainsInclusion
    (𝒰 : Set (Set X)) (A : Set X) (hOpen : ∀ U ∈ 𝒰, IsOpen U)
    (hCover : ⋃₀ 𝒰 = Set.univ) (n : ℕ) :
    IsIso (homologyMap (smallRelativeSingularChainsInclusion R 𝒰 A) n) := by
  let 𝒱 := smallSingularSubspaceCover 𝒰 A
  have hVOpen : ∀ V ∈ 𝒱, IsOpen V := by
    rintro _ ⟨U, hU, rfl⟩
    exact (hOpen U hU).preimage continuous_subtype_val
  have hVCover : ⋃₀ 𝒱 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨U, hU, hx⟩ := Set.mem_sUnion.mp (hCover.symm ▸ Set.mem_univ x.val)
    exact Set.mem_sUnion.mpr ⟨_, ⟨U, hU, rfl⟩, hx⟩
  let S := ShortComplex.cokernelSequence (smallSingularSubspaceChains R 𝒰 A)
  let T := ShortComplex.cokernelSequence (singularSubspaceChains R A)
  have hmono (k : ℕ) : Mono ((smallSingularSubspaceChains R 𝒰 A).f k) := by
    let := isSplitMono_smallSingularSubspaceChains R 𝒰 A k
    infer_instance
  let : Mono (smallSingularSubspaceChains R 𝒰 A) := mono_of_mono_f _ hmono
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := by change Mono (smallSingularSubspaceChains R 𝒰 A); infer_instance }
  have hT : T.ShortExact := shortExact_singularSubspaceChains R A
  -- Both rows are the original subspace inclusion followed by its categorical cokernel.
  let F : S ⟶ T :=
    { τ₁ := smallSingularChainsInclusion R 𝒱
      τ₂ := smallSingularChainsInclusion R 𝒰
      τ₃ := smallRelativeSingularChainsInclusion R 𝒰 A
      comm₁₂ := by
        change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ =
          SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
        simp only [SSet.chainComplexMap, ← Functor.map_comp]
        rfl
      comm₂₃ := by
        change smallSingularChainsInclusion R 𝒰 ≫ relativeSingularChainsProjection R A =
          cokernel.π (smallSingularSubspaceChains R 𝒰 A) ≫
            smallRelativeSingularChainsInclusion R 𝒰 A
        simp [smallRelativeSingularChainsInclusion, relativeSingularChainsProjection] }
  have h₁ (k : ℕ) : IsIso (homologyMap F.τ₁ k) := by
    obtain ⟨e, he⟩ := homotopyEquivalences_smallSingularChainsInclusion R 𝒱 hVOpen hVCover
    change IsIso (homologyMap (smallSingularChainsInclusion R 𝒱) k)
    rw [← he]
    exact (e.toHomologyIso k).isIso_hom
  have h₂ (k : ℕ) : IsIso (homologyMap F.τ₂ k) := by
    obtain ⟨e, he⟩ := homotopyEquivalences_smallSingularChainsInclusion R 𝒰 hOpen hCover
    change IsIso (homologyMap (smallSingularChainsInclusion R 𝒰) k)
    rw [← he]
    exact (e.toHomologyIso k).isIso_hom
  -- The pair comparison theorem handles both positive degrees and the degree-zero endpoint.
  exact HomologySequence.isIso_homologyMap_τ₃ F hS hT n (h₁ n).epi_of_iso (h₂ n)
    (fun k _ ↦ h₁ k) (fun k _ ↦ (h₂ k).mono_of_iso)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every original relative class has a cycle representative small for the specified open cover. -/
theorem exists_small_relativeSingularCycle_representative
    (𝒰 : Set (Set X)) (A : Set X) (hOpen : ∀ U ∈ 𝒰, IsOpen U)
    (hCover : ⋃₀ 𝒰 = Set.univ) (n : ℕ) (z : relativeSingularHomology R A n) :
    ∃ (c : (singularChains R X).X n),
      c ∈ ((smallSingularChainsInclusion R 𝒰).f n).hom.range ∧
      ∃ a : relativeSingularCycles R A n,
        a.val = (relativeSingularChainsProjection R A).f n c ∧
          relativeSingularCycleClass R A n a = z := by
  let C := smallRelativeSingularChains R 𝒰 A
  let D := relativeSingularChains R A
  let P : C ⟶ D := smallRelativeSingularChainsInclusion R 𝒰 A
  let : IsIso (homologyMap P n) :=
    isIso_homologyMap_smallRelativeSingularChainsInclusion R 𝒰 A hOpen hCover n
  -- Choose a small relative cycle mapping to the given class, then lift its chain quotient.
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (homologyMap P n)).mp inferInstance z
  obtain ⟨gc, hgc⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance y
  let π := cokernel.π (smallSingularSubspaceChains R 𝒰 A)
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (π.f n)).mp inferInstance (C.iCycles n gc)
  let c := (smallSingularChainsInclusion R 𝒰).f n b
  let a : relativeSingularCycles R A n :=
    (D.sc n).moduleCatCyclesIso.hom (cyclesMap P n gc)
  have ha : a.val = (relativeSingularChainsProjection R A).f n c := by
    have hi := congrArg (fun f ↦ f (cyclesMap P n gc))
      (D.sc n).moduleCatCyclesIso_hom_i
    change a.val = D.iCycles n (cyclesMap P n gc) at hi
    have hmap := congrArg (fun f ↦ f gc) (cyclesMap_i P n)
    change D.iCycles n (cyclesMap P n gc) = P.f n (C.iCycles n gc) at hmap
    rw [hi, hmap, ← hb]
    have hπ : π ≫ P = smallSingularChainsInclusion R 𝒰 ≫
        relativeSingularChainsProjection R A := by
      simp [π, P, smallRelativeSingularChainsInclusion, relativeSingularChainsProjection]
    exact congrArg (fun f ↦ f.f n b) hπ
  refine ⟨c, ⟨b, rfl⟩, a, ha, ?_⟩
  -- Naturality of the canonical cycle quotient identifies the class, without changing models.
  have hclass : relativeSingularCycleClass R A n a =
      D.homologyπ n (cyclesMap P n gc) := by
    have h := congrArg (fun f ↦ f a) (D.sc n).moduleCatCyclesIso_inv_π
    change D.homologyπ n ((D.sc n).moduleCatCyclesIso.inv a) =
      relativeSingularCycleClass R A n a at h
    have hc : (D.sc n).moduleCatCyclesIso.inv a = cyclesMap P n gc :=
      congrArg (fun f ↦ f (cyclesMap P n gc)) (D.sc n).moduleCatCyclesIso.hom_inv_id
    rw [hc] at h
    exact h.symm
  have hnat := congrArg (fun f ↦ f gc) (homologyπ_naturality P n)
  change homologyMap P n (C.homologyπ n gc) = D.homologyπ n (cyclesMap P n gc) at hnat
  rw [hclass, ← hnat, hgc, hy]

end AtiyahSinger
