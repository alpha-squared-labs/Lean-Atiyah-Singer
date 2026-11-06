/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMapComposition
public import AtiyahSinger.Geometry.EquivariantFixedRankModel
public import AtiyahSinger.Geometry.SmoothAtlasSum
public import AtiyahSinger.Topology.EquivariantBundleEmbedding

/-!
# A specified smooth equivariant atlas as a native bundle summand

Public module ID: M1362.

For a smooth action of a compact Lie group on a compact Hausdorff
second-countable smooth base, adjoin a continuous equivariant complement,
smooth only that complement,
and use the resulting constant rank to build a compatible native model.
The prescribed atlas is a smooth equivariant retract of this fixed-rank
model by the actual first inclusion and projection. No continuous
complement isomorphism is assumed smooth. The intermediate representation
bundle already has small fibers; its
atlas is transported through the same original complement isomorphism.

This is a standard consequence of equivariant bundle complementation and
smooth direct sums (SG III.1 and III.9), used to realize a prescribed
variable-rank symbol by rectangular native quantization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G]
  [CompactSpace G] [T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology

/-- The prescribed equivariant smooth bundle is a smooth retract of a fixed-rank native bundle. -/
theorem exists_equivariant_native_retract (A : SmoothComplexBundleAtlas (n := n) E)
    (σ : EquivariantStructure G E) (hσ : σ.IsSmoothAtlas 𝓘(ℝ, VG) A) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M,
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ τ : EquivariantStructure G F.Fiber, τ.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
        ∃ i : Hom E F.Fiber, ∃ p : Hom F.Fiber E,
          IsSmoothAtlasBundleMap A
            (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) i.linearMap ∧
          IsSmoothAtlasBundleMap
            (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) A p.linearMap ∧
          i.IsEquivariant σ τ ∧ p.IsEquivariant τ σ ∧
          ∀ x : M, (p.linearMap x).comp (i.linearMap x) = LinearMap.id :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let : IsFiniteRank E := A.isFiniteRank
  -- Only the added complement receives a newly selected smooth structure.
  obtain ⟨C, ρC, V, eV, heV⟩ := σ.exists_finiteRepresentation_complement
  obtain ⟨AC, hAC⟩ : ∃ AC : SmoothComplexBundleAtlas.{0} (n := n) C.Fiber,
      ρC.IsSmoothAtlas 𝓘(ℝ, VG) AC := ρC.exists_smoothAtlas (VG := VG) (n := n)
  let D := E ×ᵇ C.Fiber
  let AD := A.sum AC
  let ρD := σ.sum ρC
  have hD : ρD.IsSmoothAtlas 𝓘(ℝ, VG) AD := A.isSmoothAtlas_sum AC 𝓘(ℝ, VG) σ ρC hσ hAC
  -- The complement already supplies a small representation bundle and its same action.
  -- Transport only its atlas; its continuous comparison need not be smooth in other frames.
  let S := Bundle.Trivial M (Fin V.dimension → ℂ)
  let e : Iso D S := eV
  let AS := e.symm.smoothAtlas AD
  let ρS : EquivariantStructure G S := EquivariantStructure.ofFiniteRepresentation V
  have he : e.IsEquivariant ρD ρS := heV
  have hinverse (g : G) (x : M) (v : S x) :
      (e.linearEquiv (g • x)).symm (ρS.linearMap g x v) =
        ρD.linearMap g x ((e.linearEquiv x).symm v) := by
    apply (e.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    have h := he g x ((e.linearEquiv x).symm v)
    change e.linearEquiv (g • x) (ρD.linearMap g x ((e.linearEquiv x).symm v)) =
      ρS.linearMap g x (e.linearEquiv x ((e.linearEquiv x).symm v)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hS : ρS.IsSmoothAtlas 𝓘(ℝ, VG) AS := by
    intro i j k
    apply (hD i j k).congr
    intro z hz
    have hx : z.2 ∈ (AS.chart i).baseSet := hz.1
    have hd : z.2 ∈ (AD.chart i).baseSet := hz.1
    have hframe : (e.linearEquiv z.2).symm
        ((AS.frameLinearEquiv i z.2 hx).symm (Pi.single k 1)) =
          (AD.frameLinearEquiv i z.2 hd).symm (Pi.single k 1) := by
      apply (AD.frameLinearEquiv i z.2 hd).injective
      rw [LinearEquiv.apply_symm_apply]
      change AS.frameLinearEquiv i z.2 hx
        ((AS.frameLinearEquiv i z.2 hx).symm _) = _
      exact LinearEquiv.apply_symm_apply _ _
    simp only [dite_eq_left hx, dite_eq_left hd]
    change (AD.chart j ⟨z.1 • z.2, (e.linearEquiv (z.1 • z.2)).symm
      (ρS.linearMap z.1 z.2 ((AS.frameLinearEquiv i z.2 hx).symm (Pi.single k 1)))⟩).2 = _
    rw [hinverse, hframe]
  have hrS (x : M) : Module.finrank ℂ (S x) = V.dimension := by
    simp [S]
  obtain ⟨F, _, τ, hτ, f, hf, hforward, hbackward⟩ :=
    AS.exists_equivariant_smooth_model_of_rank_with_atlasMaps 𝓘(ℝ, VG) ρS V.dimension hrS hS
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let q : Iso D F.Fiber := e.trans f
  have hq : q.IsEquivariant ρD τ := by
    intro g x v
    exact (congrArg (f.linearEquiv (g • x)) (he g x v)).trans
      (hf g x (e.linearEquiv x v))
  have hqf : IsSmoothAtlasBundleMap AD
      (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) q.toHom.linearMap :=
    hforward.comp (e.symm.isSmoothAtlasBundleMap_symm_smoothAtlas AD)
  have hqb : IsSmoothAtlasBundleMap
      (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) AD
      (fun x ↦ (e.symm.toHom.linearMap x).comp (f.symm.toHom.linearMap x)) :=
    (e.symm.isSmoothAtlasBundleMap_smoothAtlas AD).comp hbackward
  -- The first inclusion and projection retain the original summand and its action.
  let i : Hom E F.Fiber := q.toHom.comp (sumInl (E := E) (F := C.Fiber))
  let p : Hom F.Fiber E := (sumFst (E := E) (F := C.Fiber)).comp
    (e.symm.toHom.comp f.symm.toHom)
  refine ⟨F, τ, hτ, i, p, hqf.comp (A.isSmoothAtlasBundleMap_inl AC),
    (A.isSmoothAtlasBundleMap_fst AC).comp hqb, ?_, ?_, ?_⟩
  · intro g x v
    have h := hq g x (v, 0)
    change q.linearEquiv (g • x) (σ.linearMap g x v, ρC.linearMap g x 0) =
      τ.linearMap g x (q.linearEquiv x (v, 0)) at h
    rw [map_zero] at h
    exact h
  · intro g x v
    have h := hf g x ((f.linearEquiv x).symm v)
    have hh : (f.linearEquiv (g • x)).symm (τ.linearMap g x v) =
        ρS.linearMap g x ((f.linearEquiv x).symm v) := by
      apply (f.linearEquiv (g • x)).injective
      rw [LinearEquiv.apply_symm_apply]
      change f.linearEquiv (g • x) (ρS.linearMap g x ((f.linearEquiv x).symm v)) =
        τ.linearMap g x (f.linearEquiv x ((f.linearEquiv x).symm v)) at h
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
    change ((e.linearEquiv (g • x)).symm
      ((f.linearEquiv (g • x)).symm (τ.linearMap g x v))).1 =
        σ.linearMap g x (((e.linearEquiv x).symm ((f.linearEquiv x).symm v)).1)
    rw [hh, hinverse]
    rfl
  · intro x
    apply LinearMap.ext
    intro v
    change ((e.linearEquiv x).symm ((f.linearEquiv x).symm
      (f.linearEquiv x (e.linearEquiv x (v, 0))))).1 = v
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end AtiyahSinger.SmoothComplexBundleAtlas
