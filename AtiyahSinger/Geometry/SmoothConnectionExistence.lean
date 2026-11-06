/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Smooth connections on the original vector bundle

Public module ID: M1387.

A finite-rank smooth real vector bundle on a Hausdorff second-countable smooth
manifold admits a smooth covariant derivative. Local frame differentiation is
glued by a locally finite smooth partition of unity. All maps use the given
bundle fibers, topology and smooth atlas.

This standard connection-existence construction is the shared foundation for
tangent connections and the real restriction of complex connections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set ContinuousLinearMap
open scoped Manifold ContDiff Topology

/-- A smooth finite-rank real vector bundle admits a smooth covariant derivative. -/
theorem exists_smooth_covariantDerivative {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (V : M → Type*)
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul ℝ (V x)]
    [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EuclideanSpace ℝ (Fin n))] :
    ∃ cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F V,
      CovariantDerivative.ContMDiffCovariantDerivative cov ∞ := by
  classical
  -- Differentiate section coordinates in each original local frame.
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let e (b : M) := trivializationAt F V b
  let coordinates (b : M) (σ : ∀ x, V x) (x : M) : F :=
    (e b).continuousLinearMapAt ℝ x (σ x)
  let localCov (b : M) (σ : ∀ x, V x) (x : M) : TangentSpace I x →L[ℝ] V x :=
    ((e b).symmL ℝ x).comp (mvfderiv I (coordinates b σ) x)
  have hcoord (b : M) (σ : ∀ x, V x) (x : M) (hx : x ∈ (e b).baseSet) :
      coordinates b σ =ᶠ[𝓝 x] (fun y ↦ (e b ⟨y, σ y⟩).2) := by
    filter_upwards [(e b).open_baseSet.mem_nhds hx] with y hy
    exact (e b).continuousLinearMapAt_apply_of_mem ℝ hy (σ y)
  -- Coordinate differentiation obeys additivity and the real Leibniz rule.
  have hlocal (b : M) : IsCovariantDerivativeOn F (localCov b) (e b).baseSet := by
    constructor
    · intro σ σ' x hσ hσ' hx
      have hσc := ((e b).mdifferentiableAt_section_iff I σ hx).mp hσ
      have hσc' := ((e b).mdifferentiableAt_section_iff I σ' hx).mp hσ'
      have hσd := hσc.congr_of_eventuallyEq (hcoord b σ x hx)
      have hσd' := hσc'.congr_of_eventuallyEq (hcoord b σ' x hx)
      have hsum : coordinates b (σ + σ') = coordinates b σ + coordinates b σ' := by
        funext y
        exact map_add ((e b).continuousLinearMapAt ℝ y) (σ y) (σ' y)
      dsimp only [localCov]
      rw [hsum, mvfderiv_add hσd hσd', ContinuousLinearMap.comp_add]
    · intro σ g x hσ hg hx
      have hσc := ((e b).mdifferentiableAt_section_iff I σ hx).mp hσ
      have hσd := hσc.congr_of_eventuallyEq (hcoord b σ x hx)
      have hsmul : coordinates b (g • σ) = g • coordinates b σ := by
        funext y
        exact map_smul ((e b).continuousLinearMapAt ℝ y) (g y) (σ y)
      dsimp only [localCov]
      rw [hsmul, mvfderiv_smul hg hσd]
      ext v
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        smul_apply, ContinuousLinearMap.smulRight_apply,
        map_add, map_smul]
      rw [(e b).symmL_continuousLinearMapAt hx]
  -- Smoothness is checked in the native Hom-bundle coordinates.
  have hsmooth (b : M) : ContMDiffCovariantDerivativeOn F ∞ (localCov b) (e b).baseSet := by
    constructor
    intro σ hσ x hx
    simp only [show (∞ : WithTop ℕ∞) + 1 = ∞ by simp] at hσ
    have hσc := ((e b).contMDiffAt_section_iff hx).mp
      ((hσ x hx).contMDiffAt ((e b).open_baseSet.mem_nhds hx))
    have hσd := hσc.congr_of_eventuallyEq (hcoord b σ x hx)
    have hd := hσd.mfderiv_const (m := ∞) (by simp)
    have hc := contMDiffAt_coordChangeL (IB := I) (n := ∞)
      hx (mem_baseSet_trivializationAt F V x)
    have hh := hc.clm_comp hd
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply hh.congr_of_eventuallyEq
    filter_upwards [(e b).open_baseSet.mem_nhds hx,
      (trivializationAt F V x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F V x)] with y hy hy'
    ext v
    simp [localCov, inTangentCoordinates, inCoordinates,
      TangentBundle.continuousLinearMapAt_model_space,
      Trivialization.coordChangeL_apply' (e b) (trivializationAt F V x) ⟨hy, hy'⟩,
      Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy',
      Trivialization.symmL_apply _ hy, mvfderiv, NormedSpace.fromTangentSpace,
      Trivialization.mk_symm _ hy, tangentSpaceCastModel]
    rfl
  -- A subordinate locally finite partition makes the local derivatives global.
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity M I M univ,
      ρ.IsSubordinate (fun b ↦ (e b).baseSet) := by
    apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
      (fun b ↦ (e b).baseSet) (fun b ↦ (e b).open_baseSet)
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_baseSet_trivializationAt F V x⟩
  let cov (σ : ∀ x, V x) (x : M) : TangentSpace I x →L[ℝ] V x :=
    ∑ᶠ b, ρ b x • localCov b σ x
  have hsum (σ : ∀ x, V x) (x : M) :
      cov σ x = ∑ b ∈ ρ.finsupport x, ρ b x • localCov b σ x :=
    (ρ.sum_finsupport_smul_eq_finsum x (fun b _ ↦ localCov b σ x)).symm
  have hdomain (x b : M) (hb : b ∈ ρ.finsupport x) : x ∈ (e b).baseSet := by
    apply hρ b
    exact subset_closure ((ρ.mem_finsupport x).mp hb)
  -- At a point only finitely many weights occur, and their sum is one.
  have hcov : IsCovariantDerivativeOn F cov univ := by
    constructor
    · intro σ σ' x hσ hσ' _
      rw [hsum, hsum, hsum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      rw [(hlocal b).add hσ hσ' (hdomain x b hb), smul_add]
    · intro σ g x hσ hg _
      rw [hsum, hsum]
      calc
        _ = ∑ b ∈ ρ.finsupport x,
            ρ b x • (g x • localCov b σ x + (mvfderiv I g x).smulRight (σ x)) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [(hlocal b).leibniz hσ hg (hdomain x b hb)]
        _ = g x • (∑ b ∈ ρ.finsupport x, ρ b x • localCov b σ x) +
            (∑ b ∈ ρ.finsupport x, ρ b x) • (mvfderiv I g x).smulRight (σ x) := by
          simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum,
            Finset.sum_smul, smul_comm (ρ _ _) (g x)]
        _ = _ := by rw [ρ.sum_finsupport x (mem_univ x), one_smul]
  -- Weighted local Hom sections extend smoothly by zero before summation.
  refine ⟨⟨cov, hcov⟩, ⟨⟨?_⟩⟩⟩
  intro σ hσ
  have hterm (b : M) : ContMDiff I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] F) x
        (ρ b x • localCov b σ x)) := by
    apply ContMDiffOn.smul_section_of_tsupport (ρ b).contMDiff.contMDiffOn
      (e b).open_baseSet (hρ b)
    exact (hsmooth b).contMDiff (hσ.mono (subset_univ _))
  apply ContMDiff.contMDiffOn
  apply ContMDiff.finsum_section_of_locallyFinite ?_ hterm
  apply ρ.locallyFinite.subset
  intro b x hx
  exact left_ne_zero_of_smul hx

end AtiyahSinger
