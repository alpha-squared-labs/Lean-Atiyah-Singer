/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereTubularComparison
public import AtiyahSinger.Geometry.SmoothRiemannianMetric
public import AtiyahSinger.Geometry.SmoothSectionEmbedding
public import AtiyahSinger.Geometry.TubularNeighborhood
public import AtiyahSinger.Topology.AssociatedCompactControl

/-!
# A compact embedding and its actual normal frame sphere

Public module ID: M1171.

The original quotient normal bundle receives a smooth metric on its original
topology. A normalized whole-bundle tube and the original frame stereographic
map identify the embedding with the south section inside two open subsets.
An explicit linear model equivalence puts both open subsets in the ambient
model. Both sections are smooth proper embeddings, ready for common-open
analytic excision. No normal fibers, tangent quotient maps or stereographic
normalization are replaced.

Source: the normal-neighborhood reduction in SG III.13, Property 2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold TopologicalSpace
open scoped Manifold ContDiff

attribute [local instance] normalBundleTopology orthogonalFrameTopology
  continuousSMul_orthogonalSphere

variable {En Em : Type*} [NormedAddCommGroup En] [NormedSpace ℝ En]
  [FiniteDimensional ℝ En] [NormedAddCommGroup Em] [NormedSpace ℝ Em]
  [FiniteDimensional ℝ Em]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace En M]
  [IsManifold 𝓘(ℝ, En) ∞ M] [CompactSpace M] [T2Space M]
  [SecondCountableTopology M] [Nonempty M]
  [TopologicalSpace N] [ChartedSpace Em N] [IsManifold 𝓘(ℝ, Em) ∞ N]
  [T2Space N] [SecondCountableTopology N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1200000 in
-- The normal metric, quotient atlas and the two specified total manifold models coexist here.
/-- The given embedding and its actual normal sphere section have one common open neighborhood. -/
theorem exists_normal_frameSphere_neighborhood
    (f : ContMDiffMap 𝓘(ℝ, En) 𝓘(ℝ, Em) M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, En) 𝓘(ℝ, Em) ∞ f) (hp : IsProperMap f) :
    let r := Module.finrank ℝ Em - Module.finrank ℝ En
    let V := NormalBundle 𝓘(ℝ, En) 𝓘(ℝ, Em) f
    letI := normalBundleFiberBundle f hf.isImmersion
    letI := normalBundleVectorBundle f hf.isImmersion
    letI := normalBundleContMDiffVectorBundle f hf.isImmersion
    letI : ∀ x, TopologicalSpace (V x) := fun _ ↦ inferInstance
    letI : ∀ x, AddCommGroup (V x) := fun _ ↦ inferInstance
    letI : ∀ x, Module ℝ (V x) := fun _ ↦ inferInstance
    letI : ∀ x, IsTopologicalAddGroup (V x) := fun _ ↦ inferInstance
    letI : ∀ x, ContinuousConstSMul ℝ (V x) := fun _ ↦ inferInstance
    let g := smoothRiemannianMetric (EB := En) (NormalModel En Em) V
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, NormedAddCommGroup (V x) :=
      instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    letI : ∀ x, InnerProductSpace ℝ (V x) := instInnerProductSpaceReal
    letI : IsContMDiffRiemannianBundle 𝓘(ℝ, En) ∞ (NormalModel En Em) V :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, En)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, En)
    let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ)
      (OrthogonalFrameBundle r V) (OrthogonalSphere r)
    letI := associatedSphereChartedSpace S
    let a := frameSphereStereographic (EB := En) r V
    let W : Opens Z := ⟨a.source, a.open_source⟩
    ∃ l : (En × NormalModel En Em) ≃L[ℝ] Em,
      letI := linearModelChartedSpace l Z
      ∃ j : ContMDiffMap 𝓘(ℝ, En) 𝓘(ℝ, Em) M Z ∞,
        IsSmoothEmbedding 𝓘(ℝ, En) 𝓘(ℝ, Em) ∞ j ∧ IsProperMap j ∧
          (∀ x : M, j x = a.symm ⟨x, 0⟩) ∧
          ∃ (U : Opens N) (s : ContMDiffMap 𝓘(ℝ, En) 𝓘(ℝ, Em) M U ∞),
            IsSmoothEmbedding 𝓘(ℝ, En) 𝓘(ℝ, Em) ∞ s ∧ IsProperMap s ∧
              (∀ x : M, (s x : N) = f x) ∧
              ∃ d : U ≃ₘ⟮𝓘(ℝ, Em), 𝓘(ℝ, Em)⟯ W,
                ∀ x : M, (d (s x) : Z) = j x := by
  classical
  let r := Module.finrank ℝ Em - Module.finrank ℝ En
  let V := NormalBundle 𝓘(ℝ, En) 𝓘(ℝ, Em) f
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let T : TubularNeighborhood f hf.isImmersion :=
    Classical.choice (nonempty_tubularNeighborhood f hf.isImmersion hf.isEmbedding hp)
  let tubeMap := T.diffeomorph
  -- The normalized tube uses this same quotient normal bundle and its original zero section.
  let s : ContMDiffMap 𝓘(ℝ, En) 𝓘(ℝ, Em) M T.target ∞ :=
    ⟨fun x ↦ tubeMap ⟨x, 0⟩,
      tubeMap.contMDiff.comp (contMDiff_zeroSection ℝ V)⟩
  let q : ContMDiffMap 𝓘(ℝ, Em) 𝓘(ℝ, En) T.target M ∞ :=
    ⟨fun z ↦ (tubeMap.symm z).proj,
      (contMDiff_proj V).comp tubeMap.symm.contMDiff⟩
  have hs : IsSmoothEmbedding 𝓘(ℝ, En) 𝓘(ℝ, Em) ∞ s := by
    apply isSmoothEmbedding_of_leftInverse s q
    intro x
    change (tubeMap.symm (tubeMap ⟨x, 0⟩)).proj = x
    rw [tubeMap.symm_apply_apply]
  let : ∀ x, TopologicalSpace (V x) := fun _ ↦ inferInstance
  let : ∀ x, AddCommGroup (V x) := fun _ ↦ inferInstance
  let : ∀ x, Module ℝ (V x) := fun _ ↦ inferInstance
  let : ∀ x, IsTopologicalAddGroup (V x) := fun _ ↦ inferInstance
  let : ∀ x, ContinuousConstSMul ℝ (V x) := fun _ ↦ inferInstance
  let g := smoothRiemannianMetric (EB := En) (NormalModel En Em) V
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, NormedAddCommGroup (V x) :=
    instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
  let : ∀ x, InnerProductSpace ℝ (V x) := instInnerProductSpaceReal
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, En) ∞ (NormalModel En Em) V :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, En)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, En)
  let Z := AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ)
    (OrthogonalFrameBundle r V) (OrthogonalSphere r)
  let := associatedSphereChartedSpace S
  let : T2Space Z := associatedBundle_t2Space S.toIsPrincipalBundle
  let a := frameSphereStereographic (EB := En) r V
  let W : Opens Z := ⟨a.source, a.open_source⟩
  -- A point of the nonempty source gives the actual codimension identity.
  have hle : Module.finrank ℝ En ≤ Module.finrank ℝ Em :=
    LinearMap.finrank_le_finrank_of_injective
      (hf.isImmersion.mfderiv_injective (by simp) (Classical.choice inferInstance))
  have hdim : Module.finrank ℝ (En × NormalModel En Em) = Module.finrank ℝ Em := by
    rw [Module.finrank_prod]
    simp only [NormalModel, finrank_euclideanSpace_fin]
    omega
  let l := (LinearEquiv.ofFinrankEq (En × NormalModel En Em) Em hdim).toContinuousLinearEquiv
  let dModel := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  let := isManifold_linearModelChartedSpace l Z
  -- The same stereographic map has a smooth left inverse given by the original projection.
  let c := frameSphereHomeomorph (EB := En) r V
  have ha := frameSphereStereographic_spec (EB := En) r V
  have hc := (frameSphereHomeomorph_spec (EB := En) r V).2
  let j : ContMDiffMap 𝓘(ℝ, En) 𝓘(ℝ, Em) M Z ∞ :=
    ⟨fun x ↦ a.symm ⟨x, 0⟩,
      dModel.contMDiff.comp (ha.2.2.2.2.2.comp (contMDiff_zeroSection ℝ V))⟩
  let p : ContMDiffMap 𝓘(ℝ, Em) 𝓘(ℝ, En) Z M ∞ :=
    ⟨fun z ↦ (c z).val.1.proj,
      ((contMDiff_proj V).comp (contMDiff_fst.comp hc.contMDiff)).comp
        dModel.symm.contMDiff⟩
  have hj : IsSmoothEmbedding 𝓘(ℝ, En) 𝓘(ℝ, Em) ∞ j := by
    apply isSmoothEmbedding_of_leftInverse j p
    intro x
    change (c (a.symm ⟨x, 0⟩)).val.1.proj = x
    rw [ha.2.2.2.1]
  have hcomparison := exists_frameSphere_tubular_diffeomorph r V l T.target tubeMap
  let d := hcomparison.choose
  have hd := hcomparison.choose_spec
  refine ⟨l, j, hj, j.contMDiff.continuous.isProperMap, (fun _ ↦ rfl),
    T.target, s, hs, s.contMDiff.continuous.isProperMap, T.map_zero, d, ?_⟩
  intro x
  exact hd ⟨x, 0⟩

end AtiyahSinger
