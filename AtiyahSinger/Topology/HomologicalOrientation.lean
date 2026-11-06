/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactRelativeLocalHomology
public import AtiyahSinger.Topology.SingularHomology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Sets.Compacts

/-!
# Integral homological orientations and compact-relative fundamental classes

Public module ID: M1907.

Hatcher, Algebraic Topology, section 3.3, pp.233--238, especially
Lemma 3.27. An integral homological orientation is a locally compatible
choice of a generator of H_n(M,M \ {x};ℤ) at every point. A linear
equivalence from ℤ records that generator without allowing rational-unit
rescaling. Local compatibility uses only classes over neighborhoods; it
does not assume a global fundamental class or Poincaré duality.

For a Hausdorff second-countable manifold charted on all of Euclidean
n-space, each compact subset K has a unique relative fundamental class
restricting to those prescribed local generators. Compactness belongs
to K, not to M. Connectedness, nonemptiness and positive dimension are
not assumed. The empty compact set gives the zero relative class;
in dimension zero the statement is the usual finite signed sum of points.

Rational classes are the images of these exact integer classes under the
actual coefficient homomorphism. Their normalization and support-change
laws refer to the original pair inclusions. This file does not identify
homological orientation with a tangent-frame orientation, supply the
canonical orientation on a tangent total space, or assert a locally
finite-chain realization. Those are distinct geometric comparisons.
The compact classes below are constructed from the prescribed local witnesses by
relative Mayer–Vietoris and compact-relative point detection.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace

universe u

/-- Standard integral local-homology orientation, with locally compatible generators. -/
structure HomologicalOrientation (n : ℕ) (M : Type u) [TopologicalSpace M] where
  /-- The chosen integral generator at x is the image of 1 under this equivalence. -/
  localGenerator : ∀ x : M,
    ℤ ≃ₗ[ℤ] relativeSingularHomology ℤ ({x}ᶜ : Set M) n
  /-- Near each point the specified local generators are restrictions of one local class. -/
  locally_compatible : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∃ c : relativeSingularHomology ℤ Uᶜ n, ∀ (y : M) (hy : y ∈ U),
      relativeSingularHomologyInclusion ℤ Uᶜ ({y}ᶜ)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) n c =
          localGenerator y 1

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [SecondCountableTopology M]

-- Retain the original second-countability assumption, although compact gluing needs less.
set_option linter.unusedSectionVars false in
/-- Hatcher Lemma 3.27: the specified local orientation has a unique compact-relative class. -/
theorem existsUnique_compactRelativeFundamentalClass
    (O : HomologicalOrientation n M) (K : Compacts M) :
    ∃! c : relativeSingularHomology ℤ ((K : Set M)ᶜ) n,
      ∀ (x : M) (hx : x ∈ K),
        relativeSingularHomologyInclusion ℤ ((K : Set M)ᶜ) ({x}ᶜ)
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n c =
            O.localGenerator x 1 := by
  classical
  -- Work with the relative subspace itself, so Mayer–Vietoris uses literal intersections.
  let P (A : Set M) : Prop := ∃ c : relativeSingularHomology ℤ A n,
    ∀ (x : M) (hx : x ∉ A), relativeSingularHomologyInclusion ℤ A ({x}ᶜ)
      (fun _y hy h ↦ hx (h ▸ hy)) n c = O.localGenerator x 1
  have hglue (A B : Set M) (hA : IsOpen A) (hB : IsOpen B)
      (hAc : IsCompact Aᶜ) (hBc : IsCompact Bᶜ) (hPA : P A) (hPB : P B) : P (A ∩ B) := by
    obtain ⟨a, ha⟩ := hPA
    obtain ⟨b, hb⟩ := hPB
    -- On the compact overlap, the two classes have the same prescribed point restrictions.
    have hmatch : relativeSingularHomologyInclusion ℤ A (A ∪ B) Set.subset_union_left n a =
        relativeSingularHomologyInclusion ℤ B (A ∪ B) Set.subset_union_right n b := by
      apply sub_eq_zero.mp
      apply relativeSingularHomology_eq_zero_of_point_restrictions ℤ n (A ∪ B)
        (by simpa only [Set.compl_union] using hAc.inter hBc)
      intro x hx
      have hxA : x ∉ A := fun h ↦ hx (Or.inl h)
      have hxB : x ∉ B := fun h ↦ hx (Or.inr h)
      have h₁ := congrArg (fun f ↦ f a)
        (relativeSingularHomologyInclusion_comp ℤ A (A ∪ B) ({x}ᶜ)
          Set.subset_union_left (fun _y hy h ↦ hx (h ▸ hy)) n)
      have h₂ := congrArg (fun f ↦ f b)
        (relativeSingularHomologyInclusion_comp ℤ B (A ∪ B) ({x}ᶜ)
          Set.subset_union_right (fun _y hy h ↦ hx (h ▸ hy)) n)
      rw [map_sub]
      exact sub_eq_zero.mpr ((h₁.trans (ha x hxA)).trans (h₂.trans (hb x hxB)).symm)
    obtain ⟨c, hca, hcb⟩ :=
      exists_relativeSingularHomology_inter_of_compatible ℤ A B hA hB n a b hmatch
    refine ⟨c, ?_⟩
    intro x hx
    by_cases hxA : x ∈ A
    · have hxB : x ∉ B := fun h ↦ hx ⟨hxA, h⟩
      have hcomp := congrArg (fun f ↦ f c)
        (relativeSingularHomologyInclusion_comp ℤ (A ∩ B) B ({x}ᶜ)
          Set.inter_subset_right (fun _y hy h ↦ hxB (h ▸ hy)) n)
      have hvalue := congrArg
        (fun z ↦ relativeSingularHomologyInclusion ℤ B ({x}ᶜ)
          (fun _y hy h ↦ hxB (h ▸ hy)) n z) hcb
      exact hcomp.symm.trans (hvalue.trans (hb x hxB))
    · have hcomp := congrArg (fun f ↦ f c)
        (relativeSingularHomologyInclusion_comp ℤ (A ∩ B) A ({x}ᶜ)
          Set.inter_subset_left (fun _y hy h ↦ hxA (h ▸ hy)) n)
      have hvalue := congrArg
        (fun z ↦ relativeSingularHomologyInclusion ℤ A ({x}ᶜ)
          (fun _y hy h ↦ hxA (h ▸ hy)) n z) hca
      exact hcomp.symm.trans (hvalue.trans (ha x hxA))
  have hfinite (s : Finset M) (L : M → Set M)
      (hL : ∀ i ∈ s, IsCompact (L i)) (hP : ∀ i ∈ s, P (L i)ᶜ) :
      P (⋃ i ∈ s, L i)ᶜ := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.compl_empty]
      exact ⟨0, fun x hx ↦ False.elim (hx (Set.mem_univ x))⟩
    | @insert i s hi ih =>
      have hrest := ih (fun j hj ↦ hL j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))
      have hcompact : IsCompact (⋃ j ∈ s, L j) :=
        s.isCompact_biUnion fun j hj ↦ hL j (Finset.mem_insert_of_mem hj)
      have hpiece := hL i (Finset.mem_insert_self _ _)
      simpa only [Finset.set_biUnion_insert, Set.compl_union] using
        hglue (L i)ᶜ (⋃ j ∈ s, L j)ᶜ hpiece.isClosed.isOpen_compl
          hcompact.isClosed.isOpen_compl (by simpa using hpiece) (by simpa using hcompact)
          (hP i (Finset.mem_insert_self _ _)) hrest
  -- Shrink finitely many of the orientation's own compatibility neighborhoods to compact pieces.
  choose U hU hxU c hc using O.locally_compatible
  obtain ⟨s, hs⟩ := K.isCompact.elim_finite_subcover U hU (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  obtain ⟨L, hL, hLU, hcover⟩ :=
    K.isCompact.finite_compact_cover s U (fun x _ ↦ hU x) hs
  have hpiece (i : M) : P (L i)ᶜ := by
    refine ⟨relativeSingularHomologyInclusion ℤ (U i)ᶜ (L i)ᶜ
      (Set.compl_subset_compl.mpr (hLU i)) n (c i), ?_⟩
    intro x hx
    have hxL : x ∈ L i := not_not.mp hx
    have hcomp := congrArg (fun f ↦ f (c i))
      (relativeSingularHomologyInclusion_comp ℤ (U i)ᶜ (L i)ᶜ ({x}ᶜ)
        (Set.compl_subset_compl.mpr (hLU i)) (fun _y hy h ↦ hx (h ▸ hy)) n)
    exact hcomp.trans (hc i x (hLU i hxL))
  have hPK : P ((K : Set M)ᶜ) := by
    have hfinitePieces : P (⋃ i ∈ s, L i)ᶜ :=
      hfinite s L (fun i _ ↦ hL i) (fun i _ ↦ hpiece i)
    exact (congrArg (fun T : Set M ↦ P Tᶜ) hcover).mpr hfinitePieces
  obtain ⟨z, hz⟩ := hPK
  have hnormalized : ∀ (x : M) (hx : x ∈ K),
      relativeSingularHomologyInclusion ℤ ((K : Set M)ᶜ) ({x}ᶜ)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n z =
          O.localGenerator x 1 := fun x hx ↦ hz x (not_not.mpr hx)
  refine ⟨z, hnormalized, ?_⟩
  -- Point detection identifies any other normalized class with this same glued witness.
  intro w hw
  apply sub_eq_zero.mp
  apply relativeSingularHomology_eq_zero_of_point_restrictions ℤ n ((K : Set M)ᶜ)
    (by simpa using K.isCompact)
  intro x hx
  rw [map_sub, hw x (not_not.mp hx), hz x hx, sub_self]

/-- The unique integral relative fundamental class with the prescribed local normalization. -/
def compactRelativeFundamentalClass (O : HomologicalOrientation n M) (K : Compacts M) :
    relativeSingularHomology ℤ ((K : Set M)ᶜ) n :=
  Classical.choose (existsUnique_compactRelativeFundamentalClass O K).exists

/-- The selected fundamental class restricts to the exact chosen local integral generator. -/
theorem compactRelativeFundamentalClass_restriction
    (O : HomologicalOrientation n M) (K : Compacts M) (x : M) (hx : x ∈ K) :
    relativeSingularHomologyInclusion ℤ ((K : Set M)ᶜ) ({x}ᶜ)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n
        (compactRelativeFundamentalClass O K) = O.localGenerator x 1 := by
  exact (Classical.choose_spec
    (existsUnique_compactRelativeFundamentalClass O K).exists) x hx

/-- Compact-relative fundamental classes agree under the original inclusion of complements. -/
theorem compactRelativeFundamentalClass_inclusion
    (O : HomologicalOrientation n M) {K L : Compacts M} (h : K ≤ L) :
    relativeSingularHomologyInclusion ℤ ((L : Set M)ᶜ) ((K : Set M)ᶜ)
        (Set.compl_subset_compl.mpr h) n (compactRelativeFundamentalClass O L) =
      compactRelativeFundamentalClass O K := by
  -- Compare the prescribed point restrictions of the two classes over K.
  apply (existsUnique_compactRelativeFundamentalClass O K).unique
  · intro x hx
    have hcomp := congrArg (fun f ↦ f (compactRelativeFundamentalClass O L))
      (relativeSingularHomologyInclusion_comp ℤ ((L : Set M)ᶜ) ((K : Set M)ᶜ) ({x}ᶜ)
        (Set.compl_subset_compl.mpr h)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n)
    exact hcomp.trans (compactRelativeFundamentalClass_restriction O L x (h hx))
  · exact compactRelativeFundamentalClass_restriction O K

/-- The rational fundamental class is the coefficient image of the normalized integer class. -/
def rationalCompactRelativeFundamentalClass
    (O : HomologicalOrientation n M) (K : Compacts M) :
    relativeSingularHomology ℚ ((K : Set M)ᶜ) n :=
  relativeSingularHomologyRationalization ((K : Set M)ᶜ) n
    (compactRelativeFundamentalClass O K)

/-- Rational normalization retains the chosen integral local generator and its sign. -/
theorem rationalCompactRelativeFundamentalClass_restriction
    (O : HomologicalOrientation n M) (K : Compacts M) (x : M) (hx : x ∈ K) :
    relativeSingularHomologyInclusion ℚ ((K : Set M)ᶜ) ({x}ᶜ)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n
        (rationalCompactRelativeFundamentalClass O K) =
      relativeSingularHomologyRationalization ({x}ᶜ : Set M) n (O.localGenerator x 1) := by
  -- Coefficient change commutes with this very pair inclusion.
  have hnat := relativeSingularHomologyRationalization_naturality (ContinuousMap.id M)
    (fun _ hx' ↦ (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) hx') n
    (compactRelativeFundamentalClass O K)
  change relativeSingularHomologyRationalization ({x}ᶜ : Set M) n
    (relativeSingularHomologyInclusion ℤ ((K : Set M)ᶜ) ({x}ᶜ)
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n
      (compactRelativeFundamentalClass O K)) = _ at hnat
  rw [compactRelativeFundamentalClass_restriction O K x hx] at hnat
  exact hnat.symm

/-- The normalized rational classes form the compatible family used by compact-support cap. -/
theorem rationalCompactRelativeFundamentalClass_inclusion
    (O : HomologicalOrientation n M) {K L : Compacts M} (h : K ≤ L) :
    relativeSingularHomologyInclusion ℚ ((L : Set M)ᶜ) ((K : Set M)ᶜ)
        (Set.compl_subset_compl.mpr h) n (rationalCompactRelativeFundamentalClass O L) =
      rationalCompactRelativeFundamentalClass O K := by
  -- Rationalize the integral compatibility of the specified chosen classes.
  have hnat := relativeSingularHomologyRationalization_naturality (ContinuousMap.id M)
    (fun _ hx ↦ (Set.compl_subset_compl.mpr h) hx) n (compactRelativeFundamentalClass O L)
  change relativeSingularHomologyRationalization ((K : Set M)ᶜ) n
    (relativeSingularHomologyInclusion ℤ ((L : Set M)ᶜ) ((K : Set M)ᶜ)
      (Set.compl_subset_compl.mpr h) n (compactRelativeFundamentalClass O L)) = _ at hnat
  rw [compactRelativeFundamentalClass_inclusion O h] at hnat
  exact hnat.symm

end AtiyahSinger
