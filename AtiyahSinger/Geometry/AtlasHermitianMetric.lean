/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.SmoothAtlasSections
public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth Hermitian metrics in the original varying-rank atlas

Public module ID: M1097.

A01/D02: smoothness is a property of the existing continuous Hermitian metric,
tested in the original atlas frames. The metric remains an explicit family of
positive forms on the original fibers and total-space topology. No fiber norm
instance, replacement metric structure, or globally constant rank is introduced.

The inverse-frame formula below is zero outside the frame domain, but smoothness
is required only on that open domain. No smooth zero extension of a frame is
asserted. Sources: Spin Geometry III.2, pp.170, 176-177; Husemoller III.9.5
for metric existence, with the usual smooth partition-of-unity refinement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle
open scoped Manifold ContDiff ComplexConjugate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] (A : SmoothComplexBundleAtlas (n := n) E)

open Classical in
/-- The existing positive forms have smooth Gram entries in every original atlas frame. -/
def IsSmoothHermitianMetric (h : ComplexBundle.ContinuousHermitianMetric E) : Prop :=
  ∀ (i : A.Index) (a b : Fin (A.rank i)),
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x : M ↦ if hx : x ∈ (A.chart i).baseSet then
        (h.toCore x).inner
          (cast (congrArg E ((A.chart i).proj_symm_apply' hx))
            ((A.chart i).toPartialEquiv.symm (x, Pi.single a 1)).snd)
          (cast (congrArg E ((A.chart i).proj_symm_apply' hx))
            ((A.chart i).toPartialEquiv.symm (x, Pi.single b 1)).snd)
        else 0) (A.chart i).baseSet

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

include hM hT hSC

/-- A locally finite-rank smooth bundle admits a smooth metric on its original fibers. -/
theorem exists_smoothHermitianMetric :
    ∃ h : ComplexBundle.ContinuousHermitianMetric E, A.IsSmoothHermitianMetric h := by
  /- Stage 1: choose a locally finite smooth partition subordinate to the
  given bundle charts. Pull back each standard finite-dimensional Hermitian
  form through that original chart, multiply by its partition weight, and
  extend the supported term by zero. These are forms on the same E x.
  Stage 2: the locally finite sum is jointly continuous on the original
  same-base double bundle. Nonnegative weights summing to one make the
  form positive definite. Package it as ContinuousHermitianMetric E.
  Stage 3: in any original frame the other frame changes are smooth on
  overlaps. The weighted finite Gram sums are therefore smooth there.
  Local finiteness gives smoothness on noncompact bases as well. Different
  components may have different ranks; empty overlaps impose no equality
  of those ranks. Zero-rank fibers and the empty base are included. -/
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : ComplexBundle.IsFiniteRank E := A.isFiniteRank
  let : TopologicalSpace (TotalSpace Unit (E ×ᵇ E)) := ComplexBundle.sumTopology
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ
    (fun i : A.Index ↦ (A.chart i).baseSet) (fun i ↦ (A.chart i).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr (A.covers x))
  let ρc := ρ.toPartitionOfUnity
  let coord (i : A.Index) (x : M) (v : E x) : EuclideanSpace ℂ (Fin (A.rank i)) :=
    WithLp.toLp 2 (A.chart i ⟨x, v⟩).2
  let q (i : A.Index) (x : M) (u v : E x) : ℂ :=
    inner ℂ (coord i x u) (coord i x v)
  let H (x : M) (u v : E x) : ℂ :=
    ∑ i ∈ ρc.finsupport x, ((ρ i x : ℝ) : ℂ) * q i x u v
  have hactive {i : A.Index} {x : M} (hi : i ∈ ρc.finsupport x) :
      x ∈ (A.chart i).baseSet :=
    hρ i (subset_closure ((ρc.mem_finsupport x).mp hi))
  have hnonneg (i : A.Index) (x : M) (v : E x) : 0 ≤ (q i x v v).re :=
    inner_self_nonneg (𝕜 := ℂ) (x := coord i x v)
  have hre (x : M) (v : E x) :
      (H x v v).re = ∑ i ∈ ρc.finsupport x, ρ i x * (q i x v v).re := by
    simp [H, Complex.mul_re]
  -- Joint continuity is tested on the original same-base double-bundle topology.
  have hfst : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace Unit E)) := ComplexBundle.continuous_sum_fst
  have hsnd : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace Unit E)) := ComplexBundle.continuous_sum_snd
  have hbase : Continuous (π Unit (E ×ᵇ E)) :=
    (ComplexBundle.continuous_proj (E := E)).comp hfst
  let ρD : PartitionOfUnity A.Index (TotalSpace Unit (E ×ᵇ E)) Set.univ := {
    toFun i := (ρc i).comp ⟨π Unit (E ×ᵇ E), hbase⟩
    locallyFinite' := ρc.locallyFinite.preimage_continuous hbase
    nonneg' i z := ρ.nonneg i z.proj
    sum_eq_one' z _ := ρc.sum_eq_one (Set.mem_univ z.proj)
    sum_le_one' z := ρc.sum_le_one z.proj }
  have hρD : ρD.IsSubordinate (fun i ↦ π Unit (E ×ᵇ E) ⁻¹' (A.chart i).baseSet) := by
    intro i z hz
    exact hρ i ((tsupport_comp_subset_preimage (ρc i) hbase) hz)
  have hcontinuous : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      H z.proj z.snd.1 z.snd.2) := by
    have hlocal (i : A.Index) : ContinuousOn
        (fun z : TotalSpace Unit (E ×ᵇ E) ↦ q i z.proj z.snd.1 z.snd.2)
        (π Unit (E ×ᵇ E) ⁻¹' (A.chart i).baseSet) := by
      have hu : ContinuousOn (fun z : TotalSpace Unit (E ×ᵇ E) ↦ coord i z.proj z.snd.1)
          (π Unit (E ×ᵇ E) ⁻¹' (A.chart i).baseSet) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin (A.rank i) ↦ ℂ)).comp_continuousOn
          (continuous_snd.comp_continuousOn
            ((A.chart i).toOpenPartialHomeomorph.continuousOn.comp hfst.continuousOn
              (fun z hz ↦ (A.chart i).mem_source.mpr hz)))
      have hv : ContinuousOn (fun z : TotalSpace Unit (E ×ᵇ E) ↦ coord i z.proj z.snd.2)
          (π Unit (E ×ᵇ E) ⁻¹' (A.chart i).baseSet) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin (A.rank i) ↦ ℂ)).comp_continuousOn
          (continuous_snd.comp_continuousOn
            ((A.chart i).toOpenPartialHomeomorph.continuousOn.comp hsnd.continuousOn
              (fun z hz ↦ (A.chart i).mem_source.mpr hz)))
      exact hu.inner hv
    have hsum := hρD.continuous_finsum_smul
      (fun i ↦ (A.chart i).open_baseSet.preimage hbase) hlocal
    apply hsum.congr
    intro z
    have hfinite := ρc.sum_finsupport_smul_eq_finsum
      (x₀ := z.proj) (fun i _ ↦ q i z.proj z.snd.1 z.snd.2)
    change (∑ᶠ i, ρ i z.proj • q i z.proj z.snd.1 z.snd.2) = H z.proj z.snd.1 z.snd.2
    simpa [H, ρc, Algebra.smul_def] using hfinite.symm
  -- Each nonzero vector has a positive diagonal in a chart with positive partition weight.
  let core (x : M) : InnerProductSpace.Core ℂ (E x) := {
    inner := H x
    conj_inner_symm := by
      intro u v
      simp only [H, map_sum, map_mul, Complex.conj_ofReal]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [q]
      rw [inner_conj_symm]
    re_inner_nonneg := by
      intro v
      change 0 ≤ (H x v v).re
      rw [hre]
      exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (ρ.nonneg i x) (hnonneg i x v))
    add_left := by
      intro u v w
      simp only [H, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [q, coord]
      rw [(A.linear i x (hactive hi)).map_add, WithLp.toLp_add, inner_add_left, mul_add]
    smul_left := by
      intro u v c
      simp only [H, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [q, coord]
      rw [(A.linear i x (hactive hi)).map_smul, WithLp.toLp_smul, inner_smul_left]
      ring
    definite := by
      intro v hv
      obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
      have himem : i ∈ ρc.finsupport x := (ρc.mem_finsupport x).mpr (ne_of_gt hi)
      have hx := hactive himem
      have hsumzero : ∑ j ∈ ρc.finsupport x, ρ j x * (q j x v v).re = 0 := by
        rw [← hre, hv, Complex.zero_re]
      have hterm : ρ i x * (q i x v v).re ≤ 0 := by
        rw [← hsumzero]
        exact Finset.single_le_sum
          (fun j _ ↦ mul_nonneg (ρ.nonneg j x) (hnonneg j x v)) himem
      have hqzero : (q i x v v).re = 0 := by
        nlinarith [hnonneg i x v]
      have hcoordzero : coord i x v = 0 := by
        by_contra hvcoord
        exact (ne_of_gt ((re_inner_self_pos (𝕜 := ℂ)).mpr hvcoord)) hqzero
      apply (A.frameLinearEquiv i x hx).injective
      have hvzero := congrArg WithLp.ofLp hcoordzero
      simpa [frameLinearEquiv, coord, (A.linear i x hx).map_zero] using hvzero }
  refine ⟨{
    toCore := core
    continuous_pairing := hcontinuous
    isFiniteRank := A.isFiniteRank }, ?_⟩
  intro j a b x hx
  let inv (v : Fin (A.rank j) → ℂ) (y : M) : E y :=
    if hy : y ∈ (A.chart j).baseSet then (A.frameLinearEquiv j y hy).symm v else 0
  have hpoint (v : Fin (A.rank j) → ℂ) (y : M) (hy : y ∈ (A.chart j).baseSet) :
      (⟨y, inv v y⟩ : TotalSpace Unit E) = (A.chart j).toPartialEquiv.symm (y, v) := by
    dsimp only [inv]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := Unit) (E := E) ((A.chart j).proj_symm_apply' hy) _
  let g (i : A.Index) (y : M) : ℂ := q i y (inv (Pi.single a 1) y) (inv (Pi.single b 1) y)
  -- Smoothness uses the actual transition columns, including the original fiber transport.
  have hsmooth : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun y ↦ ∑ᶠ i, ρ i y • g i y) x := by
    apply ρ.contMDiffAt_finsum
    intro i hi
    have hxi : x ∈ (A.chart i).baseSet := hρ i hi
    have hvec (c : Fin (A.rank j)) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i))) ∞
          (fun y ↦ coord i y (inv (Pi.single c 1) y))
          ((A.chart j).baseSet ∩ (A.chart i).baseSet) := by
      let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (A.rank i) ↦ ℂ)).symm
      have hcol := (L.toContinuousLinearMap.restrictScalars ℝ).contDiff.contMDiff.comp_contMDiffOn
        (A.contMDiffOn_coordChange j i c)
      apply hcol.congr
      intro y hy
      dsimp only [coord]
      rw [hpoint (Pi.single c 1) y hy.1]
      rfl
    have hpair := (contDiff_inner (𝕜 := ℂ)).contMDiff.comp_contMDiffOn
      ((hvec a).prodMk_space (hvec b))
    exact hpair.contMDiffAt
      (((A.chart j).open_baseSet.inter (A.chart i).open_baseSet).mem_nhds ⟨hx, hxi⟩)
  have heq (y : M) : H y (inv (Pi.single a 1) y) (inv (Pi.single b 1) y) =
      ∑ᶠ i, ρ i y • g i y := by
    simpa [H, g, ρc, Algebra.smul_def] using
      ρc.sum_finsupport_smul_eq_finsum (x₀ := y) (fun i _ ↦ g i y)
  have hmetric : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun y ↦ H y (inv (Pi.single a 1) y) (inv (Pi.single b 1) y)) x := by
    simp_rw [heq]
    exact hsmooth
  apply hmetric.contMDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [dite_eq_left hy, inv, frameLinearEquiv]
    rfl
  · simp only [dite_eq_left hx, inv, frameLinearEquiv]
    rfl

/- Retain the original standing manifold context for compatibility with existing callers. -/
set_option linter.unusedSectionVars false in
/-- The specified smooth metric pairs original smooth sections to a smooth scalar function. -/
theorem contMDiff_pairing (h : ComplexBundle.ContinuousHermitianMetric E)
    (hh : A.IsSmoothHermitianMetric h) (u v : A.smoothSections) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x : M ↦ (h.toCore x).inner (u.val x) (v.val x)) := by
  /- Stage 1: around each point choose a covering original frame. Expand
  both section values using its actual inverse basis vectors. Sesquilinearity
  writes the pairing as a finite sum of conjugated coordinates, Gram entries
  and coordinates. All these functions are real-smooth on the frame domain.
  Stage 2: the frame inverse identities recover the same original fiber
  pairing on that neighborhood. Smoothness is local, so the cover gives
  global smoothness. No global rank or fiber inner-product instance is used. -/
  classical
  intro x
  obtain ⟨i, hx⟩ := A.covers x
  let G (y : M) (a b : Fin (A.rank i)) : ℂ :=
    if hy : y ∈ (A.chart i).baseSet then
      (h.toCore y).inner ((A.frameLinearEquiv i y hy).symm (Pi.single a 1))
        ((A.frameLinearEquiv i y hy).symm (Pi.single b 1))
    else 0
  have hgram (a b : Fin (A.rank i)) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun y ↦ G y a b) (A.chart i).baseSet := hh i a b
  -- Smoothness is established only on the chosen original frame domain.
  have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun y ↦ ∑ a, ∑ b, conj ((A.chart i ⟨y, u.val y⟩).2 a) *
        G y a b * (A.chart i ⟨y, v.val y⟩).2 b) (A.chart i).baseSet := by
    apply contMDiffOn_finsetSum
    intro a _
    apply contMDiffOn_finsetSum
    intro b _
    have hconj := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn
      ((contMDiffOn_pi_space.mp (u.property i)) a)
    have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2) := contDiff_mul
    exact hmul.contMDiff.comp_contMDiffOn
      ((hmul.contMDiff.comp_contMDiffOn
        (hconj.prodMk_space (hgram a b))).prodMk_space
          ((contMDiffOn_pi_space.mp (v.property i)) b))
  -- Algebraic expansion uses the actual inverse frame, including its original fiber transport.
  have hlocal := hsum.congr
    (f₁ := fun y ↦ (h.toCore y).inner (u.val y) (v.val y)) ?_
  · exact hlocal.contMDiffAt ((A.chart i).open_baseSet.mem_nhds hx)
  · intro y hy
    let : InnerProductSpace.Core ℂ (E y) := h.toCore y
    let B : E y →ₗ⋆[ℂ] E y →ₗ[ℂ] ℂ :=
      LinearMap.mk₂'ₛₗ _ _ (h.toCore y).inner
        (fun a b c ↦ (h.toCore y).add_left a b c)
        (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
        (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
        (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
    have hexpand (w : E y) :
        ∑ a : Fin (A.rank i), (A.chart i ⟨y, w⟩).2 a •
          (A.frameLinearEquiv i y hy).symm (Pi.single a 1) = w := by
      have heq := congrArg (A.frameLinearEquiv i y hy).symm
        ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr ((A.frameLinearEquiv i y hy) w))
      simp only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply,
        LinearEquiv.symm_apply_apply] at heq
      simpa [frameLinearEquiv] using heq
    change B (u.val y) (v.val y) = _
    conv_lhs => rw [← hexpand (u.val y), map_sum]
    simp only [LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro a _
    conv_lhs => rw [← hexpand (v.val y), map_sum]
    simp only [map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [G]
    rw [dite_eq_left hy]
    change conj ((A.chart i ⟨y, u.val y⟩).2 a) *
        ((A.chart i ⟨y, v.val y⟩).2 b *
          (h.toCore y).inner ((A.frameLinearEquiv i y hy).symm (Pi.single a 1))
            ((A.frameLinearEquiv i y hy).symm (Pi.single b 1))) = _
    ring

end AtiyahSinger.SmoothComplexBundleAtlas
