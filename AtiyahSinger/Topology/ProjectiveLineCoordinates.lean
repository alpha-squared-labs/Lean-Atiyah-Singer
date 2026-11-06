/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleRestriction
public import AtiyahSinger.Topology.HermitianProjectiveBundle

import all AtiyahSinger.Topology.BundleHomotopyType

/-!
# Line coordinates on the actual Hermitian projective bundle

Public module ID: M2014.

A continuous linear map to a line bundle gives an open projective coordinate
domain: the points where it is nonzero on the tautological line. On this domain
the same map is an isomorphism to the pulled-back target line. Thus the two
normalized first Chern classes have the same restriction.

The construction does not require that a coordinate map be orthogonal for the
Hermitian form defining the projective carrier. This permits a fixed splitting
to compare characteristic classes constructed with two different metrics.
The openness proof reuses the existing finite-bundle invertibility argument.

Source: Hatcher, Vector Bundles and K-Theory, proof of Theorem 3.2, pp.79–81.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)
  {F : X → Type u} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

attribute [local instance] hermitianProjectiveTopology hermitianProjectiveLineTopology
  isFiniteRank_hermitianProjectiveLine isFiniteRank_pullback isFiniteRank_restrict

/-- Restrict an actual linear coordinate map to the original tautological line. -/
def hermitianProjectiveCoordinateHom
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Hom E F) :
    Hom (HermitianProjectiveLine r E h)
      ((hermitianProjectiveProjection r E h : HermitianProjectiveBundle r E h → X) *ᵖ F) := by
  let V := EuclideanSpace ℂ (Fin r)
  let := modelTopology V E
  let := isFiniteRank_model V E
  let p := hermitianProjectiveProjection r E h
  refine
    { linearMap := fun q ↦ (a.linearMap q.1).comp (LinearMap.range q.2.val.toLinearMap).subtype
      continuous_total := ?_ }
  -- Both induced total topologies retain the same projective point and actual fiber vector.
  have hinc : Continuous (fun z : TotalSpace Unit (HermitianProjectiveLine r E h) ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit ((p : _ → X) *ᵖ E))) :=
    continuous_induced_dom
  rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
  exact ((Pullback.continuous_proj Unit E p).comp hinc).prodMk
    (a.continuous_total.comp ((Pullback.continuous_lift Unit E p).comp hinc))

/-- The coordinate domain where the actual map is invertible on the tautological line. -/
def hermitianProjectiveCoordinateDomain
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Hom E F) : Set (HermitianProjectiveBundle r E h) :=
  {q | Function.Bijective ((hermitianProjectiveCoordinateHom r E h a).linearMap q)}

/-- Projective coordinate domains are open in the original native projector topology. -/
theorem isOpen_hermitianProjectiveCoordinateDomain
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Hom E F) :
    IsOpen (hermitianProjectiveCoordinateDomain r E h a) := by
  -- This is the existing local finite-dimensional invertibility theorem, with no base separation.
  exact Hom.isOpen_setOf_bijective (HermitianProjectiveLine r E h)
    (hermitianProjectiveCoordinateHom r E h a)

/-- For a line target, the coordinate domain is exactly the locus of nonzero restriction. -/
theorem mem_hermitianProjectiveCoordinateDomain_iff
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Hom E F) (hF : ∀ x : X, Module.finrank ℂ (F x) = 1)
    (q : HermitianProjectiveBundle r E h) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    q ∈ hermitianProjectiveCoordinateDomain r E h a ↔
      ∃ v : HermitianProjectiveLine r E h q, a.linearMap q.1 v.val ≠ 0 := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let f := (hermitianProjectiveCoordinateHom r E h a).linearMap q
  let := finite_fiber (E := HermitianProjectiveLine r E h) q
  let := finite_fiber (E := F) q.1
  constructor
  · intro hq
    let : Nontrivial (F q.1) := Module.nontrivial_of_finrank_pos (by rw [hF]; decide)
    obtain ⟨w, hw⟩ := exists_ne (0 : F q.1)
    obtain ⟨v, hv⟩ := hq.surjective w
    exact ⟨v, fun hz ↦ hw (hv.symm.trans hz)⟩
  · rintro ⟨v, hv⟩
    -- A nonzero linear map between these two one-dimensional fibers is bijective.
    have hs : Function.Surjective f := by
      intro w
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (hF q.1) hv w
      exact ⟨c • v, (f.map_smul c v).trans hc⟩
    have hr : Module.finrank ℂ (HermitianProjectiveLine r E h q) =
        Module.finrank ℂ (F q.1) := q.2.property.2.1.trans (hF q.1).symm
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mpr hs, hs⟩

/-- Line coordinates jointly detecting vectors cover the whole original projective bundle. -/
theorem iUnion_hermitianProjectiveCoordinateDomain {ι : Type*}
    (L : ι → X → Type u) [∀ i x, NormedAddCommGroup (L i x)]
    [∀ i x, NormedSpace ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] [∀ i, IsFiniteRank (L i)]
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ i : ι, Hom E (L i)) (hL : ∀ i x, Module.finrank ℂ (L i x) = 1)
    (hdetect : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (x : X) (v : E x), (∀ i, (a i).linearMap x v = 0) → v = 0) :
    (⋃ i : ι, hermitianProjectiveCoordinateDomain r E h (a i)) = Set.univ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  apply Set.eq_univ_of_forall
  intro q
  let : Nontrivial (HermitianProjectiveLine r E h q) :=
    Module.nontrivial_of_finrank_pos (by rw [q.2.property.2.1]; decide)
  obtain ⟨v, hv⟩ := exists_ne (0 : HermitianProjectiveLine r E h q)
  -- A nonzero tautological vector cannot vanish in all of the given line coordinates.
  by_contra hn
  have hz (i : ι) : (a i).linearMap q.1 v.val = 0 := by
    by_contra hi
    exact hn (Set.mem_iUnion.mpr ⟨i,
      (mem_hermitianProjectiveCoordinateDomain_iff r E h (a i) (hL i) q).mpr ⟨v, hi⟩⟩)
  exact hv (Subtype.ext (hdetect q.1 v.val hz))

/-- On its coordinate domain the same fiber map is an actual line-bundle isomorphism. -/
def hermitianProjectiveCoordinateIso
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Hom E F) :
    Iso (Restrict (HermitianProjectiveLine r E h) (hermitianProjectiveCoordinateDomain r E h a))
      (Restrict
        ((hermitianProjectiveProjection r E h : HermitianProjectiveBundle r E h → X) *ᵖ F)
        (hermitianProjectiveCoordinateDomain r E h a)) := by
  let U := hermitianProjectiveCoordinateDomain r E h a
  let f := (hermitianProjectiveCoordinateHom r E h a).restrict U
  have hf (q : U) : Function.Bijective (f.linearMap q) := q.property
  exact
    { linearEquiv q := LinearEquiv.ofBijective (f.linearMap q) (hf q)
      continuous_total := f.continuous_total
      continuous_symm := f.continuous_inverse hf }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The tautological root and target line class agree on the actual coordinate domain. -/
theorem hermitianProjectiveChernRoot_restrict_coordinate
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Hom E F) (hF : ∀ x : X, Module.finrank ℂ (F x) = 1) :
    singularCohomologyPullback ℤ
        (ContinuousMap.subtypeVal (hermitianProjectiveCoordinateDomain r E h a)) 2
        (hermitianProjectiveChernRoot r E h) =
      singularCohomologyPullback ℤ
        (ContinuousMap.subtypeVal (hermitianProjectiveCoordinateDomain r E h a)) 2
        (singularCohomologyPullback ℤ (hermitianProjectiveProjection r E h) 2
          (firstChernClass F hF)) := by
  let p := hermitianProjectiveProjection r E h
  let U := hermitianProjectiveCoordinateDomain r E h a
  let j := ContinuousMap.subtypeVal U
  let L := HermitianProjectiveLine r E h
  let G := (p : HermitianProjectiveBundle r E h → X) *ᵖ F
  let : ∀ q, NormedAddCommGroup (G q) :=
    fun q ↦ (inferInstance : ∀ x, NormedAddCommGroup (F x)) (p q)
  let : ∀ q, NormedSpace ℂ (G q) :=
    fun q ↦ (inferInstance : ∀ x, NormedSpace ℂ (F x)) (p q)
  let : ∀ q : U, NormedAddCommGroup (Restrict L U q) :=
    fun q ↦ (inferInstance : NormedAddCommGroup (L q.val))
  let : ∀ q : U, NormedSpace ℂ (Restrict L U q) :=
    fun q ↦ (inferInstance : NormedSpace ℂ (L q.val))
  let : ∀ q : U, NormedAddCommGroup (Restrict G U q) :=
    fun q ↦ (inferInstance : ∀ x, NormedAddCommGroup (F x)) (p q.val)
  let : ∀ q : U, NormedSpace ℂ (Restrict G U q) :=
    fun q ↦ (inferInstance : ∀ x, NormedSpace ℂ (F x)) (p q.val)
  let hL (q : HermitianProjectiveBundle r E h) : Module.finrank ℂ (L q) = 1 :=
    q.2.property.2.1
  -- The coordinate isomorphism acts on the actual pulled-back line bundles over U.
  have heq := firstChernClass_eq_of_iso (F := Restrict G U) (Restrict L U) (fun q ↦ hL q.val)
    (fun q ↦ hF (p q.val)) (hermitianProjectiveCoordinateIso r E h a)
  -- Pullback naturality uses the same inclusions and projection on both sides.
  calc
    singularCohomologyPullback ℤ j 2 (hermitianProjectiveChernRoot r E h) =
        firstChernClass (Restrict L U) (fun q ↦ hL q.val) :=
      (firstChernClass_pullback L hL j).symm
    _ = firstChernClass (Restrict G U) (fun q ↦ hF (p q.val)) := heq
    _ = singularCohomologyPullback ℤ j 2 (firstChernClass G (fun q ↦ hF (p q))) :=
      firstChernClass_pullback G (fun q ↦ hF (p q)) j
    _ = singularCohomologyPullback ℤ j 2
        (singularCohomologyPullback ℤ p 2 (firstChernClass F hF)) :=
      congrArg (singularCohomologyPullback ℤ j 2) (firstChernClass_pullback F hF p)

end AtiyahSinger.ComplexBundle
