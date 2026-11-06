/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteRealizationHomology
public import AtiyahSinger.Topology.FiniteSimplicialRealizationHausdorff
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality

/-!
# Compact Hausdorff test sources for singular homology and cohomology

Public module ID: M1640.

Every singular homology class of an arbitrary space comes from a compact
Hausdorff space. The source is the original realization of a finite subcomplex
of the singular simplicial set, and its map is the original adjunction counit
after the realized inclusion. The finite-realization lifting theorem retains
the same cycle and coefficients under this map.

Over a field, equality after pullback to every compact Hausdorff test source
therefore detects equality of ordinary cohomology classes. The proof uses the
existing Kronecker evaluation bijection and its naturality for the same chain
map. No compactness or separation assumption is imposed on the original space.

This is the standard finite-support realization argument followed by the
universal coefficient theorem over a field. It supplies the test-source step
needed to extend the compact-base half-spinor formula in SR05.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory
open scoped Simplicial

universe u

/-- Every singular homology class comes from a compact Hausdorff test space. -/
theorem exists_compactHausdorff_singularHomology_preimage
    (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
    (n : ℕ) (c : singularHomology R X n) :
    ∃ Y : TopCat.{u}, CompactSpace Y ∧ T2Space Y ∧
      ∃ (f : C(Y, X)) (d : singularHomology R Y n), singularHomologyMap R f n d = c := by
  -- Retain the finite subcomplex and the exact lifted class from the original counit map.
  obtain ⟨A, hA, d, hd⟩ := exists_finiteRealization_singularHomology_preimage R n c
  let := hA
  let f : C(SSet.toTop.obj (A : SSet.{u}), X) :=
    ((sSetTopAdj.homEquiv (A : SSet) (TopCat.of X)).symm A.ι).hom
  -- The two separately proved topological properties apply to this same realization.
  exact ⟨SSet.toTop.obj (A : SSet.{u}), SSet.compactSpace_toTop_of_finite (A : SSet),
    SSet.t2Space_toTop_of_finite (A : SSet), f, d, hd⟩

/-- Over a field, pullback to compact Hausdorff test spaces detects ordinary cohomology. -/
theorem singularCohomology_eq_of_compactHausdorff_pullback
    (K : Type) [Field K] {X : Type u} [TopologicalSpace X]
    (n : ℕ) (a b : singularCohomology K X n)
    (h : ∀ (Y : TopCat.{u}) [CompactSpace Y] [T2Space Y] (f : C(Y, X)),
      singularCohomologyPullback K f n a = singularCohomologyPullback K f n b) :
    a = b := by
  -- The field evaluation theorem reduces equality to pairing with every original homology class.
  apply (singularCochainHomologyEvaluation_bijective K (singularChains K X) n).injective
  apply LinearMap.ext
  intro c
  obtain ⟨Y, hCompact, hHausdorff, f, d, hd⟩ :=
    exists_compactHausdorff_singularHomology_preimage K n c
  let := hCompact
  let := hHausdorff
  -- Naturality uses the same test map and its actual chain map on both sides of the pairing.
  have hnatural (t : singularCohomology K X n) :
      singularCochainHomologyEvaluation K (singularChains K X) n t
          (singularHomologyMap K f n d) =
        singularCochainHomologyEvaluation K (singularChains K Y) n
          (singularCohomologyPullback K f n t) d := by
    exact singularCochainHomologyEvaluation_naturality K
      (singularChains K Y) (singularChains K X)
      ((singularChainsFunctor K).map (TopCat.ofHom f)) n t d
  rw [← hd, hnatural a, hnatural b, h Y f]

end AtiyahSinger
