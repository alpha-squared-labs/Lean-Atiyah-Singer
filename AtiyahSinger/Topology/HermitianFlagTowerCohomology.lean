/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFlagTower
public import AtiyahSinger.Topology.SingularCohomology

/-!
# Cohomological induction through the actual flag tower

Public module ID: M1886.

Injectivity for positive-rank projective bundles implies injectivity for the
original complete flag projection. The zero-rank flag has an actual section
given by the empty projection family. At each successor rank, the literal
orthogonal complement and the actual assembly map give the required square.
No injectivity statement about the empty rank-zero projective bundle is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory Opposite

universe u

attribute [local instance] hermitianFlagTopology hermitianProjectiveTopology
  hermitianProjectiveComplementModelTopology hermitianProjectiveComplementFiberBundle
  hermitianProjectiveComplementVectorBundle

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Positive-rank projective injectivity gives injectivity of the original complete flag tower. -/
theorem hermitianFlagProjection_cohomology_injective_of_projective
    (R : Type) [CommRing R] (n : ℕ)
    (hprojective : ∀ (s : ℕ) {Y : Type u} [TopologicalSpace Y]
      (F : Y → Type u) [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin (s + 1))) F)]
      [FiberBundle (EuclideanSpace ℂ (Fin (s + 1))) F]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin (s + 1))) F]
      (hF : letI := modelTopology (EuclideanSpace ℂ (Fin (s + 1))) F
        ContinuousHermitianMetric F),
      Function.Injective (singularCohomologyPullback R
        (hermitianProjectiveProjection (s + 1) F hF) n)) :
    ∀ (r : ℕ) {X : Type u} [TopologicalSpace X]
      (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
      [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
      (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
        ContinuousHermitianMetric E),
      Function.Injective (singularCohomologyPullback R (hermitianFlagProjection r E h) n) := by
  intro r
  induction r with
  | zero =>
    intro X tX E hnorm hspace tE fb vb h
    let V := EuclideanSpace ℂ (Fin 0)
    let := modelTopology V E
    -- Every original rank-zero fiber is zero; its empty projector tuple sums to its identity.
    let empty (x : X) : HermitianFlagSpace 0 (E x) (h.toCore x) := by
      have : Subsingleton (E x) :=
        ((trivializationAt V E x).linearEquivAt ℂ x
          (mem_baseSet_trivializationAt V E x)).injective.subsingleton
      refine ⟨Fin.elim0, (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i),
        (fun i ↦ Fin.elim0 i), ?_, (fun i ↦ Fin.elim0 i)⟩
      ext v
      exact Subsingleton.elim _ _
    let sectionMap : C(X, HermitianFlagBundle 0 E h) :=
      { toFun := fun x ↦ ⟨x, empty x⟩
        continuous_toFun := by
          apply continuous_induced_rng.mpr
          exact continuous_id.prodMk (continuous_pi fun i ↦ Fin.elim0 i) }
    -- The retained base coordinate makes the section/projection composite exactly the identity.
    let H := singularCohomologyFunctor R n
    have hcomp : singularCohomologyPullback R (hermitianFlagProjection 0 E h) n ≫
        singularCohomologyPullback R sectionMap n = 𝟙 _ := by
      change H.map (TopCat.ofHom (hermitianFlagProjection 0 E h)).op ≫
        H.map (TopCat.ofHom sectionMap).op = _
      rw [← H.map_comp, ← op_comp]
      exact H.map_id _
    apply Function.LeftInverse.injective (g := singularCohomologyPullback R sectionMap n)
    intro a
    exact congrArg (fun f ↦ f a) hcomp
  | succ r ih =>
    intro X tX E hnorm hspace tE fb vb h
    let K := HermitianProjectiveComplement r E h
    let hK := hermitianProjectiveComplementMetric r E h
    let first := hermitianProjectiveProjection (r + 1) E h
    let next := hermitianFlagProjection r K hK
    let assembly := hermitianFlagTowerAssembly r E h
    let original := hermitianFlagProjection (r + 1) E h
    -- Both lower projections are injective using the same literal complementary bundle.
    have hfirst := hprojective r E h
    have hnext := ih K hK
    intro a b hab
    apply hfirst
    apply hnext
    -- Contravariance turns the actual projection square into this same composite pullback.
    have hsquare := congrArg
      (fun f ↦ singularCohomologyPullback R f n)
      (hermitianFlagProjection_comp_towerAssembly r E h)
    let H := singularCohomologyFunctor R n
    change H.map (TopCat.ofHom assembly ≫ TopCat.ofHom original).op =
      H.map (TopCat.ofHom next ≫ TopCat.ofHom first).op at hsquare
    rw [op_comp, H.map_comp, op_comp, H.map_comp] at hsquare
    have ha := congrArg (fun f ↦ f a) hsquare
    have hb := congrArg (fun f ↦ f b) hsquare
    change singularCohomologyPullback R assembly n
      (singularCohomologyPullback R original n a) =
      singularCohomologyPullback R next n (singularCohomologyPullback R first n a) at ha
    change singularCohomologyPullback R assembly n
      (singularCohomologyPullback R original n b) =
      singularCohomologyPullback R next n (singularCohomologyPullback R first n b) at hb
    exact ha.symm.trans ((congrArg (singularCohomologyPullback R assembly n) hab).trans hb)

end AtiyahSinger.ComplexBundle
