/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactRelativeLocalHomology
public import AtiyahSinger.Topology.HomologicalOrientation
public import AtiyahSinger.Topology.LocallyFiniteHomologyRealization
public import AtiyahSinger.Topology.LocallyFiniteSingularHomology

/-!
# The locally finite fundamental class with the original integral normalization

Public module ID: M1950.

The class belongs to the homology of the actual locally finite singular
chain complex. It is characterized by its images in the original relative
homology over every compact support, with the same HomologicalOrientation.
Rationalization is the actual coefficient map of that complex.

Sources: Hatcher, Algebraic Topology, section 3.3, Lemma 3.27, and section 3.F
for the inverse-limit obstruction; Atiyah--Singer III, p.552, for the
fundamental class with arbitrary supports. The chain realization below is a
supplementary argument, not an assertion that homology commutes with inverse
limits. It uses a compact exhaustion and vanishing above the manifold
dimension. It does not assume a triangulation of a topological manifold.

The manifold is Hausdorff, second countable and charted on all of Euclidean
space. It may be noncompact, disconnected, empty or zero dimensional. The
geometric comparison with a tangent-frame orientation, including the
canonical orientation of a tangent total space, requires a separate geometric comparison.
The chain realization uses compatible original cycles and primitives.
The compact-relative dimension bound follows from the same original local homology model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [SecondCountableTopology M]

-- The dimension bound follows from compact chart controls and local homology.
set_option linter.unusedSectionVars false in
/-- Hatcher Lemma 3.27(b): compact-relative homology vanishes above the manifold dimension. -/
theorem relativeSingularHomology_subsingleton_above_dim (R : Type) [CommRing R]
    (K : Compacts M) (k : ℕ) (h : n < k) :
    Subsingleton (relativeSingularHomology R ((K : Set M)ᶜ) k) := by
  -- Compact chart controls glue through the original relative Mayer–Vietoris sequence.
  exact relativeSingularHomology_subsingleton_compact_manifold
    R n (K : Set M) K.isCompact k h

/-- The prescribed compact-relative generators determine one actual locally finite class. -/
theorem existsUnique_locallyFiniteFundamentalClass (O : HomologicalOrientation n M) :
    ∃! z : locallyFiniteSingularHomology ℤ M n,
      ∀ K : Compacts M,
        locallyFiniteSingularHomologyRestriction ℤ K n z =
          compactRelativeFundamentalClass O K := by
  -- A countable compact exhaustion detects the actual local finiteness condition.
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let K := CompactExhaustion.choice M
  let C (i : ℕ) : Compacts M := ⟨K i, K.isCompact i⟩
  let family (i : ℕ) := compactRelativeFundamentalClass O (C i)
  have hvan (i : ℕ) : Subsingleton (relativeSingularHomology ℤ (K i)ᶜ (n + 1)) :=
    relativeSingularHomology_subsingleton_above_dim (n := n) ℤ (C i) (n + 1) (by omega)
  have hfamily (i : ℕ) :
      relativeSingularHomologyInclusion ℤ (K (i + 1))ᶜ (K i)ᶜ
        (Set.compl_subset_compl.mpr (K.subset_succ i)) n (family (i + 1)) = family i :=
    compactRelativeFundamentalClass_inclusion O (K := C i) (L := C (i + 1))
      (K.subset_succ i)
  -- Lift representatives recursively, correcting by lifted boundaries at each stage.
  -- Next-degree vanishing likewise makes the bounding chains compatible and gives uniqueness.
  obtain ⟨z, hz, huniq⟩ := existsUnique_locallyFiniteSingularHomology_of_exhaustion
    ℤ K n hvan family hfamily
  refine ⟨z, ?_, ?_⟩
  · intro L
    -- Cofinality and the original inclusion square extend the equality to every compact set.
    obtain ⟨i, hi⟩ := K.exists_superset_of_isCompact L.isCompact
    have hrest := locallyFiniteSingularHomologyRestriction_inclusion ℤ
      (K := L) (L := C i) hi n
    have hrestz := congrArg (fun f ↦ f z) hrest
    change relativeSingularHomologyInclusion ℤ ((C i : Set M)ᶜ) ((L : Set M)ᶜ)
      (Set.compl_subset_compl.mpr hi) n
      (locallyFiniteSingularHomologyRestriction ℤ (C i) n z) =
        locallyFiniteSingularHomologyRestriction ℤ L n z at hrestz
    rw [← hrestz, hz i]
    exact compactRelativeFundamentalClass_inclusion O (K := L) (L := C i) hi
  · intro w hw
    exact huniq w (fun i ↦ hw (C i))

/-- The actual integral locally finite class with the specified local orientation. -/
def locallyFiniteFundamentalClass (O : HomologicalOrientation n M) :
    locallyFiniteSingularHomology ℤ M n :=
  Classical.choose (existsUnique_locallyFiniteFundamentalClass O).exists

/-- The chosen locally finite class has the original relative class over every compact set. -/
theorem locallyFiniteFundamentalClass_restriction (O : HomologicalOrientation n M)
    (K : Compacts M) :
    locallyFiniteSingularHomologyRestriction ℤ K n (locallyFiniteFundamentalClass O) =
      compactRelativeFundamentalClass O K := by
  -- The selected class is the very witness whose compact restrictions were prescribed.
  exact (Classical.choose_spec (existsUnique_locallyFiniteFundamentalClass O).exists) K

/-- The rational fundamental class is the actual image of the same integral LF class. -/
def rationalLocallyFiniteFundamentalClass (O : HomologicalOrientation n M) :
    locallyFiniteSingularHomology ℚ M n :=
  locallyFiniteSingularHomologyRationalization M n (locallyFiniteFundamentalClass O)

/-- Rational restriction agrees with the already normalized compact-relative fundamental class. -/
theorem rationalLocallyFiniteFundamentalClass_restriction
    (O : HomologicalOrientation n M) (K : Compacts M) :
    locallyFiniteSingularHomologyRestriction ℚ K n
        (rationalLocallyFiniteFundamentalClass O) =
      rationalCompactRelativeFundamentalClass O K := by
  -- Coefficient change commutes with the actual same-simplex restriction map.
  change locallyFiniteSingularHomologyRestriction ℚ K n
    (locallyFiniteSingularHomologyRationalization M n (locallyFiniteFundamentalClass O)) = _
  rw [← locallyFiniteSingularHomologyRationalization_restriction,
    locallyFiniteFundamentalClass_restriction]
  rfl

end AtiyahSinger
