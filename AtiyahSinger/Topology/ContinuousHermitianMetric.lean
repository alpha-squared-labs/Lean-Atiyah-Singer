/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleSum
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.PartitionOfUnity

/-!
# Continuous Hermitian metrics on the original complex bundle

Public module ID: M1743.

A metric includes local finite-rank linear triviality of the original complex bundle
and explicit positive definite Hermitian-form data, expressed by
mathlib's `InnerProductSpace.Core`, with joint continuity on the existing
same-base double bundle. The original fibers, complex module structures and
total-space topology remain fixed. No norm or inner-product instance is installed
by this construction, and no metric-dependent topology is used on an exterior
bundle or a compact-support K group.

Husemoller III.9.2 and III.9.5, together with III.5.5, give this standard notion
and existence over a paracompact Hausdorff base. Karoubi I.8.5--8.7, pp.41--42,
supplies the same existence input to the exterior Thom construction in IV.1.4.
Both books use a first-linear convention; here the first slot is conjugate-linear
as in mathlib, obtained from that convention by exchanging the two arguments.
Convex interpolation
is the standard positive-form argument: it has the original metrics as endpoints
and is jointly continuous in time and the two fiber vectors. This supports later
metric independence; it does not itself assert equality of Thom classes.

The actual convex combination, its joint homotopy certificate and metric existence
are proved below. Existence uses a locally finite partition of unity subordinate
to the original variable-rank charts. No compactness, constant rank, positive
rank or nonempty fibers beyond the original vector-space structures are assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval ComplexConjugate

attribute [local instance] sumTopology

section General

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- A continuous positive definite Hermitian metric on the original finite-rank bundle. -/
structure ContinuousHermitianMetric where
  /-- The specified Hermitian form, conjugate-linear in its first argument. -/
  toCore : ∀ x, InnerProductSpace.Core ℂ (E x)
  /-- Joint continuity for the original same-base double-bundle topology. -/
  continuous_pairing : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
    (toCore z.proj).inner z.snd.1 z.snd.2)
  /-- Local finite-rank linear triviality of the original complex bundle. -/
  isFiniteRank : IsFiniteRank E

namespace ContinuousHermitianMetric

variable {E} (h₀ h₁ : ContinuousHermitianMetric E)

/-- The actual convex combination of the two forms on precisely the same original fibers. -/
def convexCombination (t : I) : ContinuousHermitianMetric E where
  toCore x :=
    { inner := fun u v ↦
        ((1 - (t : ℝ) : ℝ) : ℂ) * (h₀.toCore x).inner u v +
          ((t : ℝ) : ℂ) * (h₁.toCore x).inner u v
      conj_inner_symm u v := by
        -- Real coefficients retain the original Hermitian symmetry.
        simp only [map_add, map_mul, Complex.conj_ofReal,
          (h₀.toCore x).conj_inner_symm, (h₁.toCore x).conj_inner_symm]
      re_inner_nonneg v := by
        -- Both weights and both diagonal values are nonnegative.
        change 0 ≤ (((1 - (t : ℝ) : ℝ) : ℂ) * (h₀.toCore x).inner v v +
          ((t : ℝ) : ℂ) * (h₁.toCore x).inner v v).re
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr t.property.2) ((h₀.toCore x).re_inner_nonneg v))
          (mul_nonneg t.property.1 ((h₁.toCore x).re_inner_nonneg v))
      add_left u v w := by
        rw [(h₀.toCore x).add_left, (h₁.toCore x).add_left]
        ring
      smul_left u v c := by
        rw [(h₀.toCore x).smul_left, (h₁.toCore x).smul_left]
        ring
      definite v hv := by
        -- A vanishing weighted diagonal forces one positive-weight metric to vanish.
        have hreal := congrArg Complex.re hv
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hreal
        have h₀nonneg := (h₀.toCore x).re_inner_nonneg v
        have h₁nonneg := (h₁.toCore x).re_inner_nonneg v
        change 0 ≤ ((h₀.toCore x).inner v v).re at h₀nonneg
        change 0 ≤ ((h₁.toCore x).inner v v).re at h₁nonneg
        by_cases ht : (t : ℝ) < 1
        · apply (h₀.toCore x).definite v
          apply Complex.ext
          · have hterm := mul_nonneg t.property.1 h₁nonneg
            change ((h₀.toCore x).inner v v).re = 0
            nlinarith
          · have him := congrArg Complex.im ((h₀.toCore x).conj_inner_symm v v)
            change -((h₀.toCore x).inner v v).im = ((h₀.toCore x).inner v v).im at him
            change ((h₀.toCore x).inner v v).im = 0
            linarith
        · have ht₁ : (t : ℝ) = 1 := le_antisymm t.property.2 (le_of_not_gt ht)
          apply (h₁.toCore x).definite v
          apply Complex.ext
          · change ((h₁.toCore x).inner v v).re = 0
            simpa only [ht₁, sub_self, zero_mul, one_mul, zero_add] using hreal
          · have him := congrArg Complex.im ((h₁.toCore x).conj_inner_symm v v)
            change -((h₁.toCore x).inner v v).im = ((h₁.toCore x).inner v v).im at him
            change ((h₁.toCore x).inner v v).im = 0
            linarith }
  continuous_pairing :=
    (continuous_const.mul h₀.continuous_pairing).add
      (continuous_const.mul h₁.continuous_pairing)
  isFiniteRank := h₀.isFiniteRank

/-- Convex interpolation is a joint metric homotopy with the two original endpoints. -/
theorem convexCombination_properties :
    Continuous (fun p : I × TotalSpace Unit (E ×ᵇ E) ↦
      ((h₀.convexCombination h₁ p.1).toCore p.2.proj).inner p.2.snd.1 p.2.snd.2) ∧
      h₀.convexCombination h₁ 0 = h₀ ∧ h₀.convexCombination h₁ 1 = h₁ := by
  /- Stage 1: both original pairings are continuous on the same double bundle.
  Their composites with the second projection remain continuous. The real time
  coordinate and its complement are continuous on I, and complex scalar
  multiplication and addition give the displayed joint continuity. No choice of
  fiber norm or identification of different bundle topologies enters this step.
  Stage 2: at time zero the coefficients are one and zero, and at time one they
  are zero and one. Thus the complete fiberwise Hermitian forms are the original
  endpoint forms. Function extensionality identifies their inner fields, and
  proof irrelevance identifies the algebraic and continuity certificates. -/
  have hcore_ext (x : X) (a b : InnerProductSpace.Core ℂ (E x))
      (hab : a.inner = b.inner) : a = b := by
    rcases a with ⟨⟨⟨f⟩, hs, hp, ha, hm⟩, hd⟩
    rcases b with ⟨⟨⟨g⟩, hs', hp', ha', hm'⟩, hd'⟩
    change f = g at hab
    cases hab
    rfl
  have hext (a b : ContinuousHermitianMetric E)
      (hab : ∀ x (u v : E x), (a.toCore x).inner u v = (b.toCore x).inner u v) : a = b := by
    cases a with
    | mk ca ha _ =>
      cases b with
      | mk cb hb _ =>
        congr 1
        funext x
        exact hcore_ext x (ca x) (cb x) (funext fun u ↦ funext fun v ↦ hab x u v)
  refine ⟨?_, ?_, ?_⟩
  · -- The time coefficients and original pairings vary continuously together.
    change Continuous (fun p : I × TotalSpace Unit (E ×ᵇ E) ↦
      ((1 - (p.1 : ℝ) : ℝ) : ℂ) * (h₀.toCore p.2.proj).inner p.2.snd.1 p.2.snd.2 +
        ((p.1 : ℝ) : ℂ) * (h₁.toCore p.2.proj).inner p.2.snd.1 p.2.snd.2)
    exact ((Complex.continuous_ofReal.comp
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).mul
        (h₀.continuous_pairing.comp continuous_snd)).add
      ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
        (h₁.continuous_pairing.comp continuous_snd))
  · -- Endpoint equality retains the complete original form and its certificates.
    apply hext
    intro x u v
    change ((1 - ((0 : I) : ℝ) : ℝ) : ℂ) * (h₀.toCore x).inner u v +
      (((0 : I) : ℝ) : ℂ) * (h₁.toCore x).inner u v = (h₀.toCore x).inner u v
    simp
  · apply hext
    intro x u v
    change ((1 - ((1 : I) : ℝ) : ℝ) : ℂ) * (h₀.toCore x).inner u v +
      (((1 : I) : ℝ) : ℂ) * (h₁.toCore x).inner u v = (h₁.toCore x).inner u v
    simp

end ContinuousHermitianMetric

variable [hT : T2Space X] [hP : ParacompactSpace X] [hE : IsFiniteRank E]

include hT hP hE in
/-- Every locally finite-rank complex bundle over a paracompact Hausdorff base has a metric. -/
theorem nonempty_continuousHermitianMetric : Nonempty (ContinuousHermitianMetric E) := by
  /- Stage 1: choose the original finite linear trivializations around every
  base point. Paracompact Hausdorff spaces are normal, so choose a locally finite
  partition of unity subordinate to this open cover. Pull the ordinary Euclidean
  Hermitian form back through each chart, retaining its original fiber vectors.
  Stage 2: multiply each chart form by its partition weight, extend by zero off
  its supported chart and take the locally finite sum. Local finiteness proves
  joint continuity on the original same-base double bundle; it is stronger than
  continuity on individual fibers. Every summand is positive semidefinite and
  their weights sum to one. A nonzero vector has a strictly positive diagonal
  in each active chart, giving positive definiteness of the resulting form.
  Stage 3: the original chart ranks may vary locally. Each weighted form uses
  its own chart rank, with no uniform rank bound or rank-stratum choice. Zero-rank fibers
  satisfy definiteness trivially, and an empty base gives an empty metric family.
  This is HU III.9.5 with III.5.5, or KA I.8.7. Local compactness alone does not
  imply the paracompactness used here and is not substituted for it. -/
  classical
  -- Choose only original local charts; their ranks remain indexed by base points.
  choose r e he hlinear using (IsFiniteRank.exists_linear_trivialization (E := E))
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : X ↦ (e i).baseSet) (fun i ↦ (e i).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, he x⟩)
  let coord (i x : X) (v : E x) : EuclideanSpace ℂ (Fin (r i)) :=
    WithLp.toLp 2 ((e i) ⟨x, v⟩).2
  let q (i x : X) (u v : E x) : ℂ := inner ℂ (coord i x u) (coord i x v)
  let H (x : X) (u v : E x) : ℂ :=
    ∑ i ∈ ρ.finsupport x, ((ρ i x : ℝ) : ℂ) * q i x u v
  have hactive {i x : X} (hi : i ∈ ρ.finsupport x) : x ∈ (e i).baseSet := by
    apply hρ i
    apply subset_closure
    exact (ρ.mem_finsupport x).mp hi
  have hnonneg (i x : X) (v : E x) : 0 ≤ (q i x v v).re :=
    inner_self_nonneg (𝕜 := ℂ) (x := coord i x v)
  have hre (x : X) (v : E x) :
      (H x v v).re = ∑ i ∈ ρ.finsupport x, ρ i x * (q i x v v).re := by
    simp [H, Complex.mul_re]
  -- Pull the weights back to the original double bundle, retaining its induced topology.
  have hfst : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace Unit E)) := continuous_sum_fst
  have hsnd : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace Unit E)) := continuous_sum_snd
  have hbase : Continuous (π Unit (E ×ᵇ E)) := (continuous_proj (E := E)).comp hfst
  let ρD : PartitionOfUnity X (TotalSpace Unit (E ×ᵇ E)) Set.univ := {
    toFun i := (ρ i).comp ⟨π Unit (E ×ᵇ E), hbase⟩
    locallyFinite' := ρ.locallyFinite.preimage_continuous hbase
    nonneg' i z := ρ.nonneg i z.proj
    sum_eq_one' z _ := ρ.sum_eq_one (Set.mem_univ z.proj)
    sum_le_one' z := ρ.sum_le_one z.proj }
  have hρD : ρD.IsSubordinate (fun i ↦ π Unit (E ×ᵇ E) ⁻¹' (e i).baseSet) := by
    intro i z hz
    exact hρ i ((tsupport_comp_subset_preimage (ρ i) hbase) hz)
  have hcontinuous : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      H z.proj z.snd.1 z.snd.2) := by
    have hlocal (i : X) : ContinuousOn
        (fun z : TotalSpace Unit (E ×ᵇ E) ↦ q i z.proj z.snd.1 z.snd.2)
        (π Unit (E ×ᵇ E) ⁻¹' (e i).baseSet) := by
      have hu : ContinuousOn (fun z : TotalSpace Unit (E ×ᵇ E) ↦ coord i z.proj z.snd.1)
          (π Unit (E ×ᵇ E) ⁻¹' (e i).baseSet) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin (r i) ↦ ℂ)).comp_continuousOn
          (continuous_snd.comp_continuousOn
            ((e i).toOpenPartialHomeomorph.continuousOn.comp hfst.continuousOn
              (fun z hz ↦ (e i).mem_source.mpr hz)))
      have hv : ContinuousOn (fun z : TotalSpace Unit (E ×ᵇ E) ↦ coord i z.proj z.snd.2)
          (π Unit (E ×ᵇ E) ⁻¹' (e i).baseSet) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin (r i) ↦ ℂ)).comp_continuousOn
          (continuous_snd.comp_continuousOn
            ((e i).toOpenPartialHomeomorph.continuousOn.comp hsnd.continuousOn
              (fun z hz ↦ (e i).mem_source.mpr hz)))
      exact hu.inner hv
    have hsum := hρD.continuous_finsum_smul
      (fun i ↦ (e i).open_baseSet.preimage hbase) hlocal
    apply hsum.congr
    intro z
    have hfinite := ρ.sum_finsupport_smul_eq_finsum
      (x₀ := z.proj) (fun i _ ↦ q i z.proj z.snd.1 z.snd.2)
    change (∑ᶠ i, ρ i z.proj • q i z.proj z.snd.1 z.snd.2) = H z.proj z.snd.1 z.snd.2
    simpa [H, Algebra.smul_def] using hfinite.symm
  refine ⟨{
    toCore := fun x ↦ {
      inner := H x
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_
      definite := ?_ }
    continuous_pairing := hcontinuous
    isFiniteRank := hE }⟩
  · rename_i x
    intro u v
    simp only [H, map_sum, map_mul, Complex.conj_ofReal]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [q]
    rw [inner_conj_symm]
  · rename_i x
    intro v
    change 0 ≤ (H x v v).re
    rw [hre]
    exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (ρ.nonneg i x) (hnonneg i x v))
  · rename_i x
    intro u v w
    simp only [H, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [q, coord]
    rw [(hlinear i x (hactive hi)).map_add, WithLp.toLp_add, inner_add_left, mul_add]
  · rename_i x
    intro u v c
    simp only [H, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [q, coord]
    rw [(hlinear i x (hactive hi)).map_smul, WithLp.toLp_smul, inner_smul_left]
    ring
  · rename_i x
    intro v hv
    -- One positive partition weight witnesses definiteness in an actual chart at x.
    obtain ⟨i, hi⟩ := ρ.exists_pos (Set.mem_univ x)
    have himem : i ∈ ρ.finsupport x := (ρ.mem_finsupport x).mpr (ne_of_gt hi)
    have hx := hactive himem
    have hsumzero : ∑ j ∈ ρ.finsupport x, ρ j x * (q j x v v).re = 0 := by
      rw [← hre, hv, Complex.zero_re]
    have hterm : ρ i x * (q i x v v).re ≤ 0 := by
      rw [← hsumzero]
      exact Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (ρ.nonneg j x) (hnonneg j x v)) himem
    have hqzero : (q i x v v).re = 0 := by
      nlinarith [hnonneg i x v]
    have hcoordzero : coord i x v = 0 := by
      by_contra hvcoord
      have hpos := (re_inner_self_pos (𝕜 := ℂ)).mpr hvcoord
      exact (ne_of_gt hpos) hqzero
    have hcoord : ((e i) ⟨x, v⟩).2 = ((e i) ⟨x, (0 : E x)⟩).2 := by
      have hvzero := congrArg WithLp.ofLp hcoordzero
      simpa [coord, (hlinear i x hx).map_zero] using hvzero
    have htotal : (⟨x, v⟩ : TotalSpace Unit E) = ⟨x, (0 : E x)⟩ := by
      apply (e i).injOn ((e i).mem_source.mpr hx) ((e i).mem_source.mpr hx)
      apply Prod.ext
      · exact ((e i).proj_toFun (⟨x, v⟩ : TotalSpace Unit E)
          ((e i).mem_source.mpr hx)).trans
          ((e i).proj_toFun (⟨x, (0 : E x)⟩ : TotalSpace Unit E)
            ((e i).mem_source.mpr hx)).symm
      · exact hcoord
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd) htotal)

end General

namespace ContinuousHermitianMetric

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- The installed inner products, retained as explicit forms with the same joint continuity. -/
def ofInnerProduct [IsFiniteRank E]
    (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2)) :
    ContinuousHermitianMetric E where
  toCore := fun _ ↦ InnerProductSpace.toCore
  continuous_pairing := hinner
  isFiniteRank := inferInstance

end ContinuousHermitianMetric

end AtiyahSinger.ComplexBundle
