/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedHodgeEllipticRealization
public import AtiyahSinger.Analysis.SmoothBundleMapOperator
public import AtiyahSinger.Geometry.SmoothBundleMapFromSections

/-!
# Finite matrices of the original smooth-section operators

Public module ID: M0699.

The specified native finite-sum coordinates and section equivalences determine
smooth coordinate projections and inclusions. A finite matrix of actual PDOs
therefore gives an actual PDO on those same bundles. The construction retains
its block operators as arguments and its exact action on the original sections.
It is the finite-sum assembly used for the even-to-odd Hodge operator.

Source: finite matrices of differential and pseudodifferential operators,
Lawson--Michelsohn, Spin Geometry, III.1 and III.3. The exact native-section
transport is an implementation supplement to the standard finite direct sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {ι κ : Type} [Fintype ι] [Fintype κ]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A : ι → SmoothFiniteComplexBundle (n := n) M)
  (B : κ → SmoothFiniteComplexBundle (n := n) M)
  (e : ∀ x, ((i : ι) → (A i).Fiber x) ≃ₗ[ℂ] E.Fiber x)
  (f : ∀ x, ((j : κ) → (B j).Fiber x) ≃ₗ[ℂ] F.Fiber x)
  (Φ : ((i : ι) → smoothSections (n := n) (r := (A i).rank) (A i).Fiber) ≃ₗ[ℂ]
    smoothSections (n := n) (r := E.rank) E.Fiber)
  (Ψ : ((j : κ) → smoothSections (n := n) (r := (B j).rank) (B j).Fiber) ≃ₗ[ℂ]
    smoothSections (n := n) (r := F.rank) F.Fiber)
  (hΦ : ∀ u x, (Φ u).val x = e x (fun i ↦ (u i).val x))
  (hΨ : ∀ u x, (Ψ u).val x = f x (fun j ↦ (u j).val x))
  {m : ℝ}
  (P : (j : κ) → (i : ι) → PseudodifferentialOperator (n := n)
    (r := (A i).rank) (q := (B j).rank) (A i).Fiber (B j).Fiber μ m)

set_option maxHeartbeats 800000 in
-- The extended limit accommodates elaboration of the finite matrix on the specified direct-sum
-- bundles.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- A finite matrix of actual PDOs on the specified original native direct-sum bundles. -/
def finiteMatrixPseudodifferentialOperator :
    PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ m := by
  classical
  let L : ((i : ι) → smoothSections (n := n) (r := (A i).rank) (A i).Fiber) →ₗ[ℂ]
      ((j : κ) → smoothSections (n := n) (r := (B j).rank) (B j).Fiber) :=
    { toFun := fun u j ↦ ∑ i, (P j i).toLinearMap (u i)
      map_add' := by
        intro u v
        funext j
        change (∑ i, (P j i).toLinearMap (u i + v i)) =
          (∑ i, (P j i).toLinearMap (u i)) + ∑ i, (P j i).toLinearMap (v i)
        simp only [map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c u
        funext j
        change (∑ i, (P j i).toLinearMap (c • u i)) =
          c • ∑ i, (P j i).toLinearMap (u i)
        simp only [map_smul, Finset.smul_sum] }
  let projection (i : ι) (x : M) : E.Fiber x →ₗ[ℂ] (A i).Fiber x :=
    (LinearMap.proj i).comp (e x).symm.toLinearMap
  let inclusion (j : κ) (x : M) : (B j).Fiber x →ₗ[ℂ] F.Fiber x :=
    (f x).toLinearMap.comp (LinearMap.single ℂ (fun j ↦ (B j).Fiber x) j)
  -- The stated section equivalences prove smoothness of these very coordinate maps.
  have hprojection (i : ι) : IsSmoothBundleMap (n := n) (r := E.rank)
      (q := (A i).rank) (projection i) := by
    apply (isSmoothBundleMap_iff_map_smoothSections _).mpr
    intro u
    have heval (x : M) : projection i x (u.val x) = (Φ.symm u i).val x := by
      have h := hΦ (Φ.symm u) x
      rw [Φ.apply_symm_apply] at h
      change (e x).symm (u.val x) i = _
      rw [h, LinearEquiv.symm_apply_apply]
    have hs := (Φ.symm u i).property
    change IsSmoothSection (n := n) (r := (A i).rank) (A i).Fiber
      (fun x ↦ (Φ.symm u i).val x) at hs
    simpa only [heval] using hs
  have hinclusion (j : κ) : IsSmoothBundleMap (n := n) (r := (B j).rank)
      (q := F.rank) (inclusion j) := by
    apply (isSmoothBundleMap_iff_map_smoothSections _).mpr
    intro u
    have heval (x : M) : inclusion j x (u.val x) = (Ψ (Pi.single j u)).val x := by
      rw [hΨ]
      apply congrArg (f x)
      funext k
      by_cases hk : k = j
      · subst k
        simp
      · simp [Pi.single_eq_of_ne hk]
    have hs := (Ψ (Pi.single j u)).property
    change IsSmoothSection (n := n) (r := F.rank) F.Fiber
      (fun x ↦ (Ψ (Pi.single j u)).val x) at hs
    simpa only [heval] using hs
  let R (i : ι) := smoothBundleMapOperator (μ := μ) (projection i) (hprojection i)
  let J (j : κ) := smoothBundleMapOperator (μ := μ) (inclusion j) (hinclusion j)
  have hR (i : ι) (u : (i : ι) →
      smoothSections (n := n) (r := (A i).rank) (A i).Fiber) :
      (R i).toLinearMap (Φ u) = u i := by
    apply Subtype.ext
    funext x
    change (e x).symm ((Φ u).val x) i = (u i).val x
    rw [hΦ, LinearEquiv.symm_apply_apply]
  have hJ (j : κ) (u : smoothSections (n := n) (r := (B j).rank) (B j).Fiber) :
      (J j).toLinearMap u = Ψ (Pi.single j u) := by
    apply Subtype.ext
    funext x
    rw [hΨ]
    change f x (Pi.single j (u.val x)) = f x (fun k ↦
      ((Pi.single j u : (k : κ) → smoothSections (n := n)
        (r := (B k).rank) (B k).Fiber) k).val x)
    apply congrArg (f x)
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hk]
  let Q := Ψ.toLinearMap.comp (L.comp Φ.symm.toLinearMap)
  -- Each block is an actual zero-order inclusion, original PDO and zero-order projection.
  have hblock (j : κ) (i : ι) :
      IsPseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber μ m
        ((J j).toLinearMap.comp ((P j i).toLinearMap.comp (R i).toLinearMap)) := by
    have h := (J j).isPseudodifferentialOperator.comp (J j).toLinearMap
      ((P j i).toLinearMap.comp (R i).toLinearMap)
      ((P j i).isPseudodifferentialOperator.comp (P j i).toLinearMap
        (R i).toLinearMap (R i).isPseudodifferentialOperator)
    simpa only [zero_add, add_zero] using h
  have hQ : Q = ∑ j : κ, ∑ i : ι,
      (J j).toLinearMap.comp ((P j i).toLinearMap.comp (R i).toLinearMap) := by
    apply LinearMap.ext
    intro s
    obtain ⟨u, rfl⟩ := Φ.surjective s
    change Ψ (L (Φ.symm (Φ u))) = _
    rw [Φ.symm_apply_apply]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, hR, hJ]
    simp_rw [← map_sum]
    apply congrArg Ψ
    funext j
    simp only [Finset.sum_apply]
    change (∑ i, (P j i).toLinearMap (u i)) =
      ∑ k, ∑ i, Pi.single k ((P k i).toLinearMap (u i)) j
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    symm
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      exact Pi.single_eq_of_ne (Ne.symm hk) _
    · simp
  refine ⟨Q, ?_⟩
  rw [hQ]
  exact (pseudodifferentialSpace E.Fiber F.Fiber μ m).sum_mem fun j _ ↦
    (pseudodifferentialSpace E.Fiber F.Fiber μ m).sum_mem fun i _ ↦ hblock j i

/-- The finite native matrix acts on exactly the supplied family of original smooth sections. -/
theorem finiteMatrixPseudodifferentialOperator_apply
    (u : (i : ι) → smoothSections (n := n) (r := (A i).rank) (A i).Fiber) :
    (finiteMatrixPseudodifferentialOperator E F A B e f Φ Ψ hΦ hΨ P).toLinearMap (Φ u) =
      Ψ (fun j ↦ ∑ i, (P j i).toLinearMap (u i)) := by
  change Ψ ((fun v j ↦ ∑ i, (P j i).toLinearMap (v i)) (Φ.symm (Φ u))) = _
  rw [Φ.symm_apply_apply]

end AtiyahSinger
