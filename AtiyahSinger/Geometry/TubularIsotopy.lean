/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleRescalingCylinder
public import AtiyahSinger.Geometry.NormalizedTubeTransition
public import AtiyahSinger.Geometry.TubularNeighborhood
public import AtiyahSinger.Topology.BundleRescalingIsotopy
public import AtiyahSinger.Topology.OpenEmbeddingHomotopyOperations
public import AtiyahSinger.Topology.OpenEmbeddingIsotopy

/-!
# Isotopy and open-extension independence of normalized tubular neighborhoods

Public module ID: M1504.

K05. Two given normalized tubular neighborhoods on the same quotient normal
bundle are joined by an open isotopy fixing the original zero section. Its
domain is the whole normal bundle, and its endpoints are the two original
total maps. The parameter-preserving cylinder is an open embedding, so the
existing compact-support open extensions agree.

Source: Karoubi, *K-Theory*, IV.5.21, printed p. 230, states independence of
tubular-neighborhood choice and refers to Lang for the comparison construction.
The whole-total, fixed-zero-section and open-cylinder formulation below is an
explicit project supplement: the Lean proof constructs this stronger
cylinder formulation from normalized tube transitions and rescaling.

The comparison starts with two actual tubes. Hausdorff paracompactness of the
source supplies a bundle metric and a varying radius; properness of the original
map and second countability are not comparison hypotheses. The K-theory conclusion
also requires a Hausdorff ambient manifold. Neither the geometric embedding
pushforward nor its complex-orientation choice comparison is defined here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.TubularNeighborhood

open Bundle Manifold Topology
open scoped ContDiff unitInterval

attribute [local instance] normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  [hMT : T2Space M] [hMP : ParacompactSpace M]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

include hMT hMP

/-- Given normalized tubes admit a whole-total open isotopy fixing their zero section. -/
theorem exists_openIsotopy (T₀ T₁ : TubularNeighborhood f hf) :
    ∃ H : ContinuousMap.Homotopy (T₀.totalMap f hf) (T₁.totalMap f hf),
      IsOpenEmbedding (fun p : I ×
        TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) ↦
          (p.1, H p)) ∧
        ∀ (t : I) (x : M), H (t, ⟨x, 0⟩) = f x := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let G := NormalModel E F
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let NB := TotalSpace G V
  -- The actual overlap has identity normal derivative in both directions.
  obtain ⟨e, _, _, hezero, hefix, hemap, henormal, heinormal⟩ :=
    exists_normalized_tubeTransition f hf T₀ T₁
  let m := smoothRiemannianMetric (EB := E) G V
  let : RiemannianBundle V := ⟨m.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle G V :=
    ⟨⟨m.inner, m.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ G V :=
    ⟨m.inner, m.contMDiff, fun _ _ _ ↦ rfl⟩
  obtain ⟨ε, hεpos, hεsub⟩ :=
    exists_contMDiff_radius_subset (EB := E) e.open_source hezero
  let q (z : NB) : ℝ := inner ℝ z.snd z.snd / (ε z.proj) ^ 2
  have hq : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ) ∞ q := by
    have hi : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ) ∞
        (fun z : NB ↦ inner ℝ z.snd z.snd) := contMDiff_id.inner_bundle contMDiff_id
    exact hi.mul (((ε.contMDiff.comp (contMDiff_proj V)).pow 2).inv₀
      (fun z ↦ pow_ne_zero 2 (hεpos z.proj).ne'))
  have hqnonneg (z : NB) : 0 ≤ q z := div_nonneg real_inner_self_nonneg (sq_nonneg _)
  have hquad (a : ℝ) (z : NB) : q ⟨z.proj, a • z.snd⟩ = a ^ 2 * q z := by
    simp only [q, real_inner_smul_left, real_inner_smul_right]
    ring
  have hqsub (z : NB) (hz : q z < 1) : z ∈ e.source := by
    apply hεsub z.proj z.snd
    have h := (div_lt_one (sq_pos_of_pos (hεpos z.proj))).mp hz
    rw [real_inner_self_eq_norm_sq] at h
    exact (sq_lt_sq₀ (norm_nonneg z.snd) (hεpos z.proj).le).mp h
  -- The common topological construction keeps the actual overlap and both tube maps.
  have hTopen (T : TubularNeighborhood f hf) : IsOpenEmbedding (T.totalMap f hf) :=
    T.target.isOpen.isOpenEmbedding_subtypeVal.comp T.diffeomorph.toHomeomorph.isOpenEmbedding
  have hefixi (x : M) : e.symm ⟨x, 0⟩ = ⟨x, 0⟩ := by
    simpa only [hefix x] using! e.left_inv (hezero x)
  obtain ⟨H, hH, hzero⟩ := exists_openIsotopy_of_rescaling
    (T₀.totalMap f hf) (T₁.totalMap f hf) (hTopen T₀) (hTopen T₁)
    e.toOpenPartialHomeomorph hezero hefix hemap
    (continuousOn_rescaleBundleMap e e.contMDiffOn e.open_source hefix henormal)
    (continuousOn_rescaleBundleMap e.symm e.contMDiffOn_invFun e.open_target hefixi heinormal)
    q hq.continuous hqnonneg hquad hqsub
  exact ⟨H, hH, fun t x ↦ (hzero t x).trans (T₀.map_zero x)⟩

/-- The original compact-support open extension is independent of the normalized tube. -/
theorem openPushforward_eq [T2Space N] (T₀ T₁ : TubularNeighborhood f hf) :
    letI := normalBundleFiberBundle f hf
    let h₀ : IsOpenEmbedding (T₀.totalMap f hf) :=
      T₀.target.isOpen.isOpenEmbedding_subtypeVal.comp
        T₀.diffeomorph.toHomeomorph.isOpenEmbedding
    let h₁ : IsOpenEmbedding (T₁.totalMap f hf) :=
      T₁.target.isOpen.isOpenEmbedding_subtypeVal.comp
        T₁.diffeomorph.toHomeomorph.isOpenEmbedding
    letI : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace F N
    letI := h₀.isEmbedding.t2Space
    letI := h₀.locallyCompactSpace
    compactSupportKZeroOpenPushforward (T₀.totalMap f hf) h₀ =
      compactSupportKZeroOpenPushforward (T₁.totalMap f hf) h₁ := by
  -- Use the original whole-total tube maps and the open cylinder just constructed.
  let := normalBundleFiberBundle f hf
  let h₀ : IsOpenEmbedding (TubularNeighborhood.totalMap f hf T₀) :=
    T₀.target.isOpen.isOpenEmbedding_subtypeVal.comp T₀.diffeomorph.toHomeomorph.isOpenEmbedding
  let h₁ : IsOpenEmbedding (TubularNeighborhood.totalMap f hf T₁) :=
    T₁.target.isOpen.isOpenEmbedding_subtypeVal.comp T₁.diffeomorph.toHomeomorph.isOpenEmbedding
  let : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace F N
  let := h₀.isEmbedding.t2Space
  let := h₀.locallyCompactSpace
  obtain ⟨H, hH, _⟩ := exists_openIsotopy f hf T₀ T₁
  exact compactSupportKZeroOpenPushforward_eq_of_isotopy h₀ h₁ H hH

end AtiyahSinger.TubularNeighborhood
