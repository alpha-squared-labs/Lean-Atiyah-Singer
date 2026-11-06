/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectivePuncture
public import AtiyahSinger.Topology.RelativeSingularOpenExcision

/-!
# Projective affine excision with an arbitrary parameter

Public module ID: M1898.

The inverse affine chart is an open embedding into the original projector
space. It identifies the zero vector with the specified projective point.
Taking its product with the identity retains every point of an arbitrary
parameter space. Excision therefore identifies the corresponding relative
cohomology pairs over any commutative coefficient ring.

Only the projective point is required to be closed; no separation condition
is imposed on the parameter space. The isomorphism is the actual pullback
of the product chart, so relative cup and Thom comparisons can use the same
map, support and reference vector.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open CategoryTheory Topology

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The inverse affine chart as an actual map into the original projective space. -/
def chartEmbedding (e : V) (he : ‖e‖ = 1) :
    C((innerSL ℂ e).ker, HermitianProjectiveSpace V InnerProductSpace.toCore) :=
  (ContinuousMap.subtypeVal _).comp ⟨(chart e he).symm, (chart e he).symm.continuous⟩

/-- The actual inverse affine chart has open image in the projector topology. -/
theorem isOpenEmbedding_chartEmbedding (e : V) (he : ‖e‖ = 1) :
    IsOpenEmbedding (chartEmbedding e he) :=
  (isOpen_affineChart_source e).isOpenEmbedding_subtypeVal.comp (chart e he).symm.isOpenEmbedding

/-- The same affine embedding sends only zero to its specified projective center. -/
theorem chartEmbedding_eq_ofVector_iff (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0)
    (v : (innerSL ℂ e).ker) : chartEmbedding e he v = ofVector e hne ↔ v = 0 := by
  change ((chart e he).symm v).val = ofVector e hne ↔ v = 0
  have h := (chart_apply_eq_zero_iff e he hne ((chart e he).symm v)).symm
  simpa only [Homeomorph.apply_symm_apply] using h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Affine excision of a projective point preserves an arbitrary parameter space and ring. -/
def puncturedProdCohomologyIso (R : Type) [CommRing R]
    (X : Type u) [TopologicalSpace X] (e : V) (he : ‖e‖ = 1) (hne : e ≠ 0) (k : ℕ) :
    relativeSingularCohomology R
        {z : X × HermitianProjectiveSpace V InnerProductSpace.toCore | z.2 ≠ ofVector e hne} k ≅
      relativeSingularCohomology R {z : X × (innerSL ℂ e).ker | z.2 ≠ 0} k := by
  let Q := ofVector e hne
  let f := (ContinuousMap.id X).prodMap (chartEmbedding e he)
  let K : Set (X × HermitianProjectiveSpace V InnerProductSpace.toCore) := {z | z.2 = Q}
  let A : Set (X × (innerSL ℂ e).ker) := {z | z.2 ≠ 0}
  have hf : IsOpenEmbedding f :=
    IsOpenEmbedding.id.prodMap (isOpenEmbedding_chartEmbedding e he)
  have hK : IsClosed K := isClosed_eq continuous_snd continuous_const
  have hcenter : chartEmbedding e he 0 = Q :=
    (chartEmbedding_eq_ofVector_iff e he hne 0).mpr rfl
  have hKr : K ⊆ Set.range f := by
    intro z hz
    refine ⟨(z.1, 0), ?_⟩
    exact Prod.ext rfl (hcenter.trans hz.symm)
  have hpre : A = (f ⁻¹' K)ᶜ := by
    ext z
    exact not_congr (chartEmbedding_eq_ofVector_iff e he hne z.2).symm
  have hmap : Set.MapsTo f A Kᶜ := by
    intro z hz heq
    exact hz ((chartEmbedding_eq_ofVector_iff e he hne z.2).mp heq)
  -- Excision is a chain homotopy equivalence before taking the algebraic dual.
  have hexc {B : Set (X × (innerSL ℂ e).ker)} (hB : B = (f ⁻¹' K)ᶜ)
      (h : Set.MapsTo f B Kᶜ) :
      HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
        (relativeSingularChainsMap R f h) := by
    subst B
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R f hf K hK hKr
  let P := relativeSingularCohomologyPullback R f hmap k
  have : IsIso P := isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences
    R _ (hexc hpre hmap) k
  exact asIso P

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
