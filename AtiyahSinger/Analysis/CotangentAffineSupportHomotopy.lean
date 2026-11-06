/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereRegularity
public import AtiyahSinger.Topology.BundleIsoAffineHomotopy

/-!
# A common compact exterior from finite cotangent chart estimates

A finite family of compact coordinate windows covers the original base.
If an affine path of the two original bundle maps is invertible at large
coordinate frequency on every window, the path is invertible outside one
compact subset of the actual cotangent bundle. This gives a supported
homotopy of the original triples on their original bundles.

The charts may belong to the maximal smooth atlas. Their actual inverse
cotangent maps, including zero frequency, produce the compact control;
there is no need to replace the specified charts or choose a global norm.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle IsManifold Set
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {ι : Type*} [Finite ι]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Cot" => CotangentTotalSpace (n := n) (M := M)

variable {E F : CotangentTotalSpace (n := n) (M := M) → Type*}
  [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ z, AddCommGroup (F z)] [∀ z, Module ℂ (F z)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

/-- Uniform affine invertibility in a finite compact chart cover gives supported homotopy. -/
theorem CompactSupportTriple.homotopic_of_affine_cotangent_charts
    (a b : CompactSupportTriple E F) (A B : Hom E F)
    (ha : ∀ z : (a.controlᶜ : Set Cot),
      (a.boundary.linearEquiv z).toLinearMap = A.linearMap z.val)
    (hb : ∀ z : (b.controlᶜ : Set Cot),
      (b.boundary.linearEquiv z).toLinearMap = B.linearMap z.val)
    (c : ι → OpenPartialHomeomorph M X)
    (hc : ∀ i, c i ∈ maximalAtlas 𝓘(ℝ, X) ∞ M)
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hKc : ∀ i, K i ⊆ (c i).target)
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source ∧ c i x ∈ K i)
    (R : ι → ℝ)
    (hinvertible : ∀ (i : ι) (t : unitInterval), ∀ x ∈ K i, ∀ ξ : X,
      R i ≤ ‖ξ‖ →
        let z : Cot := ⟨(c i).symm x, covectorFromChart (c i) ((c i).symm x) ξ⟩
        Function.Bijective ((1 - (t : ℂ)) • A.linearMap z + (t : ℂ) • B.linearMap z)) :
    a.Homotopic b := by
  classical
  let inverse (i : ι) (p : X × X) : Cot :=
    ⟨(c i).symm p.1, covectorFromChart (c i) ((c i).symm p.1) p.2⟩
  -- The actual inverse cotangent chart is continuous even at the zero covector.
  have hcontinuous (i : ι) : ContinuousOn (inverse i) ((c i).target ×ˢ Set.univ) := by
    intro p hp
    have hbase : ContMDiffAt 𝓘(ℝ, X × X) 𝓘(ℝ, X) ∞
        (fun p ↦ (c i).symm p.1) p :=
      (contMDiffAt_symm_of_mem_maximalAtlas (hc i) hp.1).comp p
        contDiffAt_fst.contMDiffAt
    have hd := ((contMDiffAt_of_mem_maximalAtlas (hc i)
      ((c i).map_target hp.1)).mfderiv_const
        (m := (∞ : WithTop ℕ∞)) (by simp)).comp p hbase
    have hinner : ContMDiffAt 𝓘(ℝ, X × X) 𝓘(ℝ, CotangentModel n) ∞
        (fun p ↦ innerSL ℝ p.2) p :=
      (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp p contDiffAt_snd.contMDiffAt
    have hmap : ContMDiffAt 𝓘(ℝ, X × X)
        (𝓘(ℝ, X).prod 𝓘(ℝ, CotangentModel n)) ∞ (inverse i) p := by
      apply (contMDiffAt_hom_bundle _).mpr
      refine ⟨hbase, ?_⟩
      apply (hinner.clm_comp hd).congr_of_eventuallyEq
      filter_upwards with z
      ext v
      simp [inverse, covectorFromChart, inTangentCoordinates,
        ContinuousLinearMap.inCoordinates, Function.id_def, ContinuousLinearMap.comp_apply]
      rfl
    exact hmap.continuousAt.continuousWithinAt
  let bad (i : ι) : Set Cot := inverse i '' (K i ×ˢ Metric.closedBall (0 : X) (R i))
  have hbad (i : ι) : IsCompact (bad i) :=
    ((hK i).prod (isCompact_closedBall (0 : X) (R i))).image_of_continuousOn
      ((hcontinuous i).mono (by intro p hp; exact ⟨hKc i hp.1, Set.mem_univ _⟩))
  let L : Set Cot := (a.control ∪ b.control) ∪ ⋃ i, bad i
  have hL : IsCompact L :=
    (a.isCompact_control.union b.isCompact_control).union (isCompact_iUnion hbad)
  have haL : a.control ⊆ L := fun _ h ↦ Or.inl (Or.inl h)
  have hbL : b.control ⊆ L := fun _ h ↦ Or.inl (Or.inr h)
  apply a.homotopic_of_affine b L hL haL hbL
  intro t z
  obtain ⟨i, hsource, hwindow⟩ := hcover z.val.proj
  let ξ := covectorInChart (c i) z.val.proj z.val.snd
  -- Differentiating the same chart inverse recovers the original total covector.
  have hback : covectorFromChart (c i) z.val.proj ξ = z.val.snd := by
    have hcoord : innerSL ℝ ξ = z.val.snd.comp
        (mfderiv 𝓘(ℝ, X) 𝓘(ℝ, X) (c i).symm (c i z.val.proj)) := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro j
      simp [ξ, covectorInChart, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right]
      rfl
    have hdiff : (c i).MDifferentiable 𝓘(ℝ, X) 𝓘(ℝ, X) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas (hc i)).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas (hc i)).mdifferentiableOn (by simp)⟩
    ext v
    have h := congrArg (fun T : TangentSpace 𝓘(ℝ, X) z.val.proj →L[ℝ]
      TangentSpace 𝓘(ℝ, X) z.val.proj ↦ T v) (hdiff.symm_comp_deriv hsource)
    change (mfderiv _ _ (c i).symm (c i z.val.proj))
      ((mfderiv _ _ (c i) z.val.proj) v) = v at h
    calc
      covectorFromChart (c i) z.val.proj ξ v =
          z.val.snd ((mfderiv _ _ (c i).symm (c i z.val.proj))
            ((mfderiv _ _ (c i) z.val.proj) v)) :=
        DFunLike.congr_fun hcoord ((mfderiv _ _ (c i) z.val.proj) v)
      _ = z.val.snd v := congrArg z.val.snd h
  have htotal : inverse i (c i z.val.proj, ξ) = z.val := by
    dsimp only [inverse]
    rw [(c i).left_inv hsource, hback]
  have hlarge : R i ≤ ‖ξ‖ := by
    by_contra! hsmall
    apply z.property
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨(c i z.val.proj, ξ),
      ⟨hwindow, by simpa only [Metric.mem_closedBall, dist_zero_right] using hsmall.le⟩,
        htotal⟩⟩)
  have ha' : ((a.enlarge L hL haL).boundary.linearEquiv z).toLinearMap =
      A.linearMap z.val := by
    ext v
    exact (a.enlarge_apply L hL haL z v).trans
      (LinearMap.congr_fun (ha ⟨z.val, fun h ↦ z.property (haL h)⟩) v)
  have hb' : ((b.enlarge L hL hbL).boundary.linearEquiv z).toLinearMap =
      B.linearMap z.val := by
    ext v
    exact (b.enlarge_apply L hL hbL z v).trans
      (LinearMap.congr_fun (hb ⟨z.val, fun h ↦ z.property (hbL h)⟩) v)
  rw [ha', hb']
  have h := hinvertible i t (c i z.val.proj) hwindow ξ hlarge
  change Function.Bijective
    ((1 - (t : ℂ)) • A.linearMap (inverse i (c i z.val.proj, ξ)) +
      (t : ℂ) • B.linearMap (inverse i (c i z.val.proj, ξ))) at h
  rwa [htotal] at h

end AtiyahSinger
