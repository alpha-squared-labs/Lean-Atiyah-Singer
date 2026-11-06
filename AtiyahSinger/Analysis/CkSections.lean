/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasCkSections
public import AtiyahSinger.Analysis.SobolevMaps

/-!
# Finite-order section spaces and global Sobolev embedding

Public module ID: M0328.

D01/A01. C^k sections are actual sections whose expressions in every smooth bundle
frame are C^k over the real base. The norm is the supremum of the norms of all localized
Fréchet derivatives through order k. On the compact base forced by the presentation,
this is the usual C^k norm up to equivalence. It gives a Banach space of actual sections.

The Sobolev embedding is the unique bounded extension of the actual inclusion of smooth
sections. Its distribution identity ensures that it returns the representative of the
input, not an unrelated C^k section. The exponent is strictly s > n/2+k. Compactness
factors through a strictly intermediate Sobolev order. Sources: Spin Geometry III.2.5,
2.7, 2.15(1); (2.9) uses an equivalent finite sum of coordinate partial derivatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*)
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- The standard C^k regularity condition in all smooth complex bundle frames. -/
def IsContMDiffSection (k : ℕ) (u : ∀ x, E x) : Prop :=
  ∀ e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E),
    MemTrivializationAtlas e →
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin r)) k
        (fun x ↦ (e ⟨x, u x⟩).2) e.baseSet

/-- The zero section is C^k in every linear frame. -/
theorem isContMDiffSection_zero (k : ℕ) :
    IsContMDiffSection (n := n) (r := r) E k (fun _ ↦ 0) := by
  /- Fiberwise linearity makes the local coordinate function identically zero.
  A constant function is C^k on the entire base, hence on each frame domain. -/
  intro e he
  let := he
  -- The prescribed linear frame takes the zero section to the constant zero map.
  apply (contMDiffOn_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr
  intro x hx
  exact (e.linearEquivAt ℂ x hx).map_zero

/-- Addition preserves C^k section regularity. -/
theorem isContMDiffSection_add (k : ℕ) (u v : ∀ x, E x)
    (hu : IsContMDiffSection (n := n) (r := r) E k u)
    (hv : IsContMDiffSection (n := n) (r := r) E k v) :
    IsContMDiffSection (n := n) (r := r) E k (u + v) := by
  /- In a linear frame the coordinate expression is the sum of the coordinate
  expressions of u and v. Addition preserves C^k regularity over the real base. -/
  intro e he
  let := he
  -- Addition is checked in the same frame and on its original base set.
  apply ((hu e he).add (hv e he)).congr
  intro x hx
  exact (e.linearEquivAt ℂ x hx).map_add (u x) (v x)

/-- Complex scalar multiplication preserves real C^k regularity. -/
theorem isContMDiffSection_smul (k : ℕ) (c : ℂ) (u : ∀ x, E x)
    (hu : IsContMDiffSection (n := n) (r := r) E k u) :
    IsContMDiffSection (n := n) (r := r) E k (c • u) := by
  /- In each complex-linear frame multiplication by c is a fixed real-linear map
  of the model fiber. Composing with it preserves C^k regularity. -/
  intro e he
  let := he
  -- A fixed complex scalar acts by a bounded real-linear map on the model fiber.
  have hscale := ((c • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))).restrictScalars
    ℝ).contMDiff (n := k)
  apply (hscale.comp_contMDiffOn (hu e he)).congr
  intro x hx
  exact (e.linearEquivAt ℂ x hx).map_smul c (u x)

/-- Finite-order sections as a concrete complex submodule of all sections. -/
def contMDiffSections (k : ℕ) : Submodule ℂ (∀ x, E x) where
  carrier := {u | IsContMDiffSection (n := n) (r := r) E k u}
  zero_mem' := isContMDiffSection_zero E k
  add_mem' := fun hu hv ↦ isContMDiffSection_add E k _ _ hu hv
  smul_mem' := fun c _ hu ↦ isContMDiffSection_smul E k c _ hu

set_option linter.unusedSectionVars false in
/-- Smooth sections have every finite order of regularity. -/
theorem isContMDiffSection_of_isSmoothSection (k : ℕ) (u : ∀ x, E x)
    (hu : IsSmoothSection (n := n) (r := r) E u) :
    IsContMDiffSection (n := n) (r := r) E k u := by
  /- In each frame lower the regularity index of the smooth coordinate expression
  from infinity to k. This retains the same underlying section and frame domains. -/
  intro e he
  -- Lower the regularity index without changing either coordinates or domains.
  exact (hu e he).of_le (by simp)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable {E} (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- C^k sections tagged by the finite presentation defining their norm. -/
def CkSectionSpace (_A : SmoothBundlePresentation (n := n) (r := r) E) (k : ℕ) : Type _ :=
  contMDiffSections (n := n) (r := r) E k

/-- The usual addition of C^k sections on the tagged type. -/
@[instance_reducible]
def ckSectionAddCommGroup (k : ℕ) : AddCommGroup (A.CkSectionSpace k) :=
  inferInstanceAs (AddCommGroup (contMDiffSections (n := n) (r := r) E k))

attribute [instance] ckSectionAddCommGroup

/-- The usual complex scalar action on C^k sections. -/
@[instance_reducible]
def ckSectionModule (k : ℕ) : Module ℂ (A.CkSectionSpace k) :=
  inferInstanceAs (Module ℂ (contMDiffSections (n := n) (r := r) E k))

attribute [instance] ckSectionModule

/-- Actual C^k localization, multiplied by the cutoff and extended by zero. -/
def localizedCkFunction (k : ℕ) (j : Fin A.size) (u : A.CkSectionSpace k)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin r) := by
  classical
  exact if z ∈ (A.chart j).target then
    (A.cutoff j ((A.chart j).symm z) : ℂ) •
      sectionInChart E (A.chart j) (A.frame j) u.val z
  else 0

set_option linter.unusedSectionVars false in
/-- The cutoff localizations are C^k on the entire Euclidean chart space. -/
theorem contDiff_localizedCkFunction (k : ℕ) (j : Fin A.size) (u : A.CkSectionSpace k) :
    ContDiff ℝ k (A.localizedCkFunction k j u) := by
  /- On the chart/frame overlap the expression is a product of a smooth cutoff and
  a C^k function. Its support is compactly contained in that overlap. The zero
  extension vanishes in a neighborhood of each point outside this compact image,
  so the local C^k assertions cover all of Euclidean space. -/
  classical
  let c := A.chart j
  let K := c '' tsupport (A.cutoff j)
  have hcompact : IsCompact K :=
    (A.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ K
  · -- On the fixed compact support, compose the finite-order coordinates with the chart.
    obtain ⟨x, hx, rfl⟩ := hz
    have hxsource := (A.support_subset j hx).1
    have htarget : c x ∈ c.target := c.map_source hxsource
    have hframe : c.symm (c x) ∈ (A.frame j).baseSet := by
      rw [c.left_inv hxsource]
      exact (A.support_subset j hx).2
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) (A.chart_mem_atlas j)) htarget
    have hsection := (u.property (A.frame j) (A.frame_mem_atlas j)).contMDiffAt
      ((A.frame j).open_baseSet.mem_nhds hframe)
    have hcoords := hsection.comp (c x) (hchart.of_le (by simp))
    have hcut := (A.smooth_cutoff j).contMDiffAt.comp (c x) hchart
    have hscalar := Complex.ofRealCLM.contDiff.comp_contMDiffAt hcut
    have hlocal := (hscalar.contDiffAt.of_le (by simp)).smul hcoords.contDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds htarget] with y hy
    change y ∈ (A.chart j).target at hy
    simp [localizedCkFunction, sectionInChart, hy, c]
  · -- Off that closed support image the prescribed extension is locally zero.
    apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
    filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hz] with y hy
    by_cases htarget : y ∈ c.target
    · have hcut : c.symm y ∉ tsupport (A.cutoff j) := by
        intro hmem
        exact hy ⟨c.symm y, hmem, c.right_inv htarget⟩
      simp [localizedCkFunction, image_eq_zero_of_notMem_tsupport hcut, c]
    · simp [localizedCkFunction, show y ∉ (A.chart j).target from htarget]

set_option linter.unusedSectionVars false in
/-- Each C^k localization has compact support, independently of its section values. -/
theorem hasCompactSupport_localizedCkFunction
    (k : ℕ) (j : Fin A.size) (u : A.CkSectionSpace k) :
    HasCompactSupport (A.localizedCkFunction k j u) := by
  /- Its topological support lies in the chart image of the fixed compact cutoff
  support. That image is compact; the support is closed in Euclidean space and
  therefore a compact subset of it. -/
  classical
  -- The fixed cutoff support controls every section, independently of its values.
  have hcompact : IsCompact ((A.chart j) '' tsupport (A.cutoff j)) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  apply hcompact.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ hcompact.isClosed)
  intro z hz
  have htarget : z ∈ (A.chart j).target := by
    by_contra houtside
    exact hz (by simp [localizedCkFunction, houtside])
  have hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j) := by
    by_contra houtside
    have hzero := image_eq_zero_of_notMem_tsupport houtside
    exact hz (by simp [localizedCkFunction, hzero])
  exact ⟨(A.chart j).symm z, hcut, (A.chart j).right_inv htarget⟩

/-- The usual finite-atlas C^k norm: a supremum over local derivatives through order k. -/
def ckNorm (k : ℕ) (u : A.CkSectionSpace k) : ℝ :=
  sSup {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k ∧
    ∃ x : EuclideanSpace ℝ (Fin n), a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j u) x‖}

/-- The derivative values used in the C^k norm are bounded above. -/
theorem bddAbove_ckNorm_values (k : ℕ) (u : A.CkSectionSpace k) :
    BddAbove {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k ∧
      ∃ x : EuclideanSpace ℝ (Fin n),
        a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j u) x‖} := by
  /- Each derivative through order k is continuous and supported in the
  same fixed compact set, so it is bounded. A finite nonnegative sum of
  these bounds controls every chart and derivative order, including an
  empty presentation. -/
  classical
  -- Every allowed derivative is continuous and compactly supported, hence bounded.
  have hbound (j : Fin A.size) (i : Fin (k + 1)) :
      ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i.val (A.localizedCkFunction k j u) x‖ ≤ C := by
    have hi : (i.val : ℕ∞ω) ≤ k := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    exact ((A.contDiff_localizedCkFunction k j u).continuous_iteratedFDeriv hi)
      |>.bounded_above_of_compact_support
        ((A.hasCompactSupport_localizedCkFunction k j u).iteratedFDeriv i.val)
  choose B hB using hbound
  -- A finite nonnegative sum bounds every chart and derivative order, including an empty atlas.
  refine ⟨∑ j, ∑ i, max 0 (B j i), ?_⟩
  rintro a ⟨j, i, hi, x, rfl⟩
  let i' : Fin (k + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  calc
    ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j u) x‖ ≤ B j i' := hB j i' x
    _ ≤ max 0 (B j i') := le_max_right _ _
    _ ≤ ∑ l, max 0 (B j l) :=
      Finset.single_le_sum (fun l _ ↦ le_max_left 0 (B j l)) (Finset.mem_univ i')
    _ ≤ ∑ l, ∑ i, max 0 (B l i) :=
      Finset.single_le_sum (fun l _ ↦ Finset.sum_nonneg (fun i _ ↦ le_max_left 0 (B l i)))
        (Finset.mem_univ j)

set_option linter.unusedSectionVars false in
/-- The zero section has zero C^k norm. -/
theorem ckNorm_zero (k : ℕ) : A.ckNorm k 0 = 0 := by
  /- Every derivative of each zero localization vanishes, so the supremum is zero.
  If the presentation is empty the defining set is empty, whose real supremum is zero. -/
  classical
  have hlocal (j : Fin A.size) : A.localizedCkFunction k j 0 = 0 := by
    let := A.frame_mem_atlas j
    funext z
    by_cases hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j)
    · have hframe := (A.support_subset j hcut).2
      have hz : (A.frame j ⟨(A.chart j).symm z, 0⟩).2 = 0 :=
        ((A.frame j).linearEquivAt ℂ _ hframe).map_zero
      simp only [localizedCkFunction, sectionInChart, Pi.zero_apply]
      change (if z ∈ (A.chart j).target then
        (A.cutoff j ((A.chart j).symm z) : ℂ) •
          (A.frame j ⟨(A.chart j).symm z, 0⟩).2 else 0) = 0
      rw [hz]
      simp
    · simp [localizedCkFunction, image_eq_zero_of_notMem_tsupport hcut]
  -- The norm set is either the singleton zero or empty; both have real supremum zero.
  have hderiv (j : Fin A.size) (i : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j 0) x‖ = 0 := by
    rw [hlocal]
    cases i with
    | zero => simp
    | succ i => simp
  simp only [ckNorm, hderiv]
  by_cases hsize : A.size = 0
  · have : IsEmpty (Fin A.size) := Fin.isEmpty_iff.mpr hsize
    simp
  · have : Nonempty (Fin A.size) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hsize)
    have hex : ∃ i : ℕ, i ≤ k := ⟨0, Nat.zero_le k⟩
    simp [hex]

set_option linter.unusedSectionVars false in
/-- Negating a section leaves its C^k norm unchanged. -/
theorem ckNorm_neg (k : ℕ) (u : A.CkSectionSpace k) : A.ckNorm k (-u) = A.ckNorm k u := by
  /- Localization and derivatives through order k commute with negation. The norms
  of the resulting multilinear maps agree pointwise, so their suprema agree. -/
  classical
  have hlocal (j : Fin A.size) : A.localizedCkFunction k j (-u) = -A.localizedCkFunction k j u := by
    let := A.frame_mem_atlas j
    funext z
    by_cases hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j)
    · have hframe := (A.support_subset j hcut).2
      have hneg : (A.frame j ⟨(A.chart j).symm z, -u.val ((A.chart j).symm z)⟩).2 =
          -(A.frame j ⟨(A.chart j).symm z, u.val ((A.chart j).symm z)⟩).2 :=
        ((A.frame j).linearEquivAt ℂ _ hframe).map_neg (u.val _)
      by_cases htarget : z ∈ (A.chart j).target
      · simp only [localizedCkFunction, ite_eq_left htarget, sectionInChart, Pi.neg_apply]
        change (A.cutoff j ((A.chart j).symm z) : ℂ) •
          (A.frame j ⟨(A.chart j).symm z, -u.val ((A.chart j).symm z)⟩).2 = _
        rw [hneg, smul_neg]
      · simp [localizedCkFunction, htarget]
    · simp [localizedCkFunction, image_eq_zero_of_notMem_tsupport hcut]
  -- Negation commutes with every iterated derivative, preserving each norm value.
  simp only [ckNorm, hlocal, iteratedFDeriv_neg, Pi.neg_apply, norm_neg]

/-- The C^k norm satisfies the triangle inequality. -/
theorem ckNorm_add_le (k : ℕ) (u v : A.CkSectionSpace k) :
    A.ckNorm k (u + v) ≤ A.ckNorm k u + A.ckNorm k v := by
  /- On C^k functions each derivative through order k respects addition. The
  operator-norm triangle inequality bounds every value by the sum of the two suprema.
  Boundedness justifies taking suprema; the empty-presentation case is zero. -/
  classical
  have hlocal (j : Fin A.size) : A.localizedCkFunction k j (u + v) =
      A.localizedCkFunction k j u + A.localizedCkFunction k j v := by
    let := A.frame_mem_atlas j
    funext z
    by_cases hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j)
    · have hframe := (A.support_subset j hcut).2
      have hadd : (A.frame j ⟨(A.chart j).symm z,
          u.val ((A.chart j).symm z) + v.val ((A.chart j).symm z)⟩).2 =
            (A.frame j ⟨(A.chart j).symm z, u.val ((A.chart j).symm z)⟩).2 +
              (A.frame j ⟨(A.chart j).symm z, v.val ((A.chart j).symm z)⟩).2 :=
        ((A.frame j).linearEquivAt ℂ _ hframe).map_add _ _
      by_cases htarget : z ∈ (A.chart j).target
      · simp only [localizedCkFunction, ite_eq_left htarget, sectionInChart, Pi.add_apply]
        change (A.cutoff j ((A.chart j).symm z) : ℂ) •
          (A.frame j ⟨(A.chart j).symm z,
            u.val ((A.chart j).symm z) + v.val ((A.chart j).symm z)⟩).2 = _
        rw [hadd, smul_add]
      · simp [localizedCkFunction, htarget]
    · simp [localizedCkFunction, image_eq_zero_of_notMem_tsupport hcut]
  by_cases hsize : A.size = 0
  · have : IsEmpty (Fin A.size) := Fin.isEmpty_iff.mpr hsize
    simp [ckNorm]
  · -- A genuine chart supplies nonemptiness; every derivative is bounded by its own supremum.
    let j₀ : Fin A.size := ⟨0, Nat.pos_of_ne_zero hsize⟩
    change sSup _ ≤ _
    refine csSup_le ?_ ?_
    · exact ⟨‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j₀ (u + v)) 0‖,
        j₀, 0, Nat.zero_le k, 0, rfl⟩
    rintro a ⟨j, i, hi, x, rfl⟩
    have hi' : (i : ℕ∞ω) ≤ k := by exact_mod_cast hi
    rw [hlocal, iteratedFDeriv_add_apply
      ((A.contDiff_localizedCkFunction k j u).of_le hi').contDiffAt
      ((A.contDiff_localizedCkFunction k j v).of_le hi').contDiffAt]
    apply (norm_add_le _ _).trans
    exact add_le_add
      (le_csSup (A.bddAbove_ckNorm_values k u) ⟨j, i, hi, x, rfl⟩)
      (le_csSup (A.bddAbove_ckNorm_values k v) ⟨j, i, hi, x, rfl⟩)

/-- The order-zero terms and the partition identity make the C^k norm nondegenerate. -/
theorem ckNorm_eq_zero_iff (k : ℕ) (u : A.CkSectionSpace k) : A.ckNorm k u = 0 ↔ u = 0 := by
  /- A zero supremum forces every order-zero localized value to vanish. Pull these
  zero values back through the linear frames and sum using Σχ_j=1 to recover u=0.
  The reverse direction is ckNorm_zero; an empty presentation forces an empty base. -/
  classical
  constructor
  · intro hzero
    -- Order zero detects every localized value, using the established bounded supremum.
    have hlocal (j : Fin A.size) (z : EuclideanSpace ℝ (Fin n)) :
        A.localizedCkFunction k j u z = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      have hle := le_csSup (A.bddAbove_ckNorm_values k u)
        (show ‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j u) z‖ ∈
          {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k ∧
            ∃ x : EuclideanSpace ℝ (Fin n),
              a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j u) x‖} from
          ⟨j, 0, Nat.zero_le k, z, rfl⟩)
      change ‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j u) z‖ ≤ A.ckNorm k u at hle
      simpa only [norm_iteratedFDeriv_zero, hzero] using hle
    apply Subtype.ext
    funext x
    -- Pull zero coordinates back through the original frames, then sum the partition.
    have hcut (j : Fin A.size) : (A.cutoff j x : ℂ) • u.val x = 0 := by
      by_cases hx : x ∈ tsupport (A.cutoff j)
      · let := A.frame_mem_atlas j
        have hsource := (A.support_subset j hx).1
        have hframe := (A.support_subset j hx).2
        have hcoords := hlocal j ((A.chart j) x)
        simp only [localizedCkFunction, ite_eq_left ((A.chart j).map_source hsource),
          sectionInChart, (A.chart j).left_inv hsource] at hcoords
        apply ((A.frame j).linearEquivAt ℂ x hframe).injective
        rw [map_smul, map_zero]
        have hpoint : (⟨(A.chart j).symm ((A.chart j) x),
            u.val ((A.chart j).symm ((A.chart j) x))⟩ :
              TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, u.val x⟩ :=
          congrArg (fun y ↦ (⟨y, u.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
            ((A.chart j).left_inv hsource)
        rw [hpoint] at hcoords
        exact hcoords
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have hsum : ∑ j, (A.cutoff j x : ℂ) = 1 := by exact_mod_cast A.sum_cutoff x
    change u.val x = 0
    calc
      u.val x = (1 : ℂ) • u.val x := (one_smul ℂ (u.val x)).symm
      _ = (∑ j, (A.cutoff j x : ℂ)) • u.val x := by rw [hsum]
      _ = ∑ j, (A.cutoff j x : ℂ) • u.val x := Finset.sum_smul
      _ = 0 := Finset.sum_eq_zero (fun j _ ↦ hcut j)
  · rintro rfl
    exact A.ckNorm_zero k

/-- The C^k norm is absolutely homogeneous for complex scalars. -/
theorem ckNorm_smul (k : ℕ) (c : ℂ) (u : A.CkSectionSpace k) :
    A.ckNorm k (c • u) = ‖c‖ * A.ckNorm k u := by
  /- Localization commutes with complex scalars. Real Fréchet derivatives also
  commute with their fixed complex-linear action on the output. Each operator norm
  scales by |c|, and bounded suprema respect this nonnegative factor, including c=0. -/
  classical
  have hlocal (j : Fin A.size) : A.localizedCkFunction k j (c • u) =
      c • A.localizedCkFunction k j u := by
    let := A.frame_mem_atlas j
    funext z
    by_cases hcut : (A.chart j).symm z ∈ tsupport (A.cutoff j)
    · have hframe := (A.support_subset j hcut).2
      have hsmul : (A.frame j ⟨(A.chart j).symm z,
          c • u.val ((A.chart j).symm z)⟩).2 =
            c • (A.frame j ⟨(A.chart j).symm z, u.val ((A.chart j).symm z)⟩).2 :=
        ((A.frame j).linearEquivAt ℂ _ hframe).map_smul _ _
      by_cases htarget : z ∈ (A.chart j).target
      · simp only [localizedCkFunction, ite_eq_left htarget, sectionInChart, Pi.smul_apply]
        change (A.cutoff j ((A.chart j).symm z) : ℂ) •
          (A.frame j ⟨(A.chart j).symm z,
            c • u.val ((A.chart j).symm z)⟩).2 = _
        rw [hsmul, smul_comm]
      · simp [localizedCkFunction, htarget]
    · simp [localizedCkFunction, image_eq_zero_of_notMem_tsupport hcut]
  -- Real derivatives commute with the fixed complex scalar action on the output.
  have hderiv (j : Fin A.size) (i : ℕ) (hi : i ≤ k)
      (x : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j (c • u)) x‖ =
        ‖c‖ * ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j u) x‖ := by
    have hi' : (i : ℕ∞ω) ≤ k := by exact_mod_cast hi
    rw [hlocal, iteratedFDeriv_const_smul_apply
      ((A.contDiff_localizedCkFunction k j u).of_le hi').contDiffAt, norm_smul]
  by_cases hsize : A.size = 0
  · have : IsEmpty (Fin A.size) := Fin.isEmpty_iff.mpr hsize
    simp [ckNorm]
  · let j₀ : Fin A.size := ⟨0, Nat.pos_of_ne_zero hsize⟩
    let S : Set ℝ := {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k ∧
      ∃ x : EuclideanSpace ℝ (Fin n),
        a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j u) x‖}
    have hnonempty : S.Nonempty :=
      ⟨‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j₀ u) 0‖,
        j₀, 0, Nat.zero_le k, 0, rfl⟩
    -- The entire defining set is the nonnegative scalar image of the original one.
    have hset : {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k ∧
        ∃ x : EuclideanSpace ℝ (Fin n),
          a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j (c • u)) x‖} =
        (fun a : ℝ ↦ ‖c‖ * a) '' S := by
      ext a
      constructor
      · rintro ⟨j, i, hi, x, rfl⟩
        exact ⟨‖iteratedFDeriv ℝ i (A.localizedCkFunction k j u) x‖,
          ⟨j, i, hi, x, rfl⟩, (hderiv j i hi x).symm⟩
      · rintro ⟨b, ⟨j, i, hi, x, rfl⟩, rfl⟩
        exact ⟨j, i, hi, x, (hderiv j i hi x).symm⟩
    change sSup _ = ‖c‖ * sSup S
    rw [hset]
    exact ((isLUB_csSup hnonempty (A.bddAbove_ckNorm_values k u)).mul_left
      (norm_nonneg c)).csSup_eq (hnonempty.image _)

/-- The explicit supremum norm packaged as an additive group norm. -/
def ckAddGroupNorm (k : ℕ) : AddGroupNorm (A.CkSectionSpace k) where
  toFun := A.ckNorm k
  map_zero' := A.ckNorm_zero k
  add_le' := A.ckNorm_add_le k
  neg' := A.ckNorm_neg k
  eq_zero_of_map_eq_zero' := fun u h ↦ (A.ckNorm_eq_zero_iff k u).mp h

/-- The norm topology of the actual C^k section space. -/
@[instance_reducible]
def ckSectionNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (A.CkSectionSpace k) :=
  (A.ckAddGroupNorm k).toNormedAddCommGroup

attribute [instance] ckSectionNormedAddCommGroup

/-- Compatibility of the C^k norm with the complex vector-space structure. -/
@[instance_reducible]
def ckSectionNormedSpace (k : ℕ) : NormedSpace ℂ (A.CkSectionSpace k) where
  norm_smul_le c u := le_of_eq (A.ckNorm_smul k c u)

attribute [instance] ckSectionNormedSpace

/-- The finite-order section space is complete in its actual supremum norm. -/
theorem completeSpace_ckSectionSpace (k : ℕ) : CompleteSpace (A.CkSectionSpace k) := by
  /- Use the established variable-rank Banach section construction.
  The following identity-on-values comparison preserves each designated
  native chart and proves equality of the localized derivative norms.
  Its linear isometry transports completeness to the original C^k norm. -/
  classical
  /- Transport the already proved variable-rank Banach construction without giving
  the original fibers any norm. The proof-local atlas retains every designated
  native chart and the original total-space topology. Only the finite-dimensional
  model coordinates are changed; their two conversions cancel before differentiation. -/
  -- Retype the phantom total-space model, preserving every actual point and fiber value.
  let eTotal : TotalSpace Unit E ≃ TotalSpace (EuclideanSpace ℂ (Fin r)) E :=
    { toFun := fun z ↦ ⟨z.proj, z.snd⟩
      invFun := fun z ↦ ⟨z.proj, z.snd⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let tUnit : TopologicalSpace (TotalSpace Unit E) :=
    TopologicalSpace.induced eTotal inferInstance
  let := tUnit
  let hTotal : TotalSpace Unit E ≃ₜ TotalSpace (EuclideanSpace ℂ (Fin r)) E :=
    { toEquiv := eTotal
      continuous_toFun := continuous_induced_dom
      continuous_invFun := by
        apply continuous_induced_rng.mpr
        exact continuous_id }
  let e₀ := EuclideanSpace.equiv (Fin r) ℂ
  let finiteChart (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) :
      Trivialization (Fin r → ℂ) (π Unit E) :=
    (e.compHomeomorph hTotal).transFiberHomeomorph e₀.toHomeomorph
  -- The local atlas has exactly the original linear frames and their original transitions.
  let S : SmoothComplexBundleAtlas (n := n) E := by
    refine
      { Index := {e : Trivialization (EuclideanSpace ℂ (Fin r))
            (π (EuclideanSpace ℂ (Fin r)) E) // MemTrivializationAtlas e}
        rank := fun _ ↦ r
        chart := fun i ↦ finiteChart i.val
        covers := ?_
        linear := ?_
        contMDiffOn_coordChange := ?_ }
    · intro x
      exact ⟨⟨trivializationAt (EuclideanSpace ℂ (Fin r)) E x, inferInstance⟩,
        mem_baseSet_trivializationAt (EuclideanSpace ℂ (Fin r)) E x⟩
    · intro i x hx
      let := i.property
      change IsLinearMap ℂ (fun z : E x ↦ e₀ (i.val ⟨x, z⟩).2)
      exact (e₀.toLinearMap.comp ((i.val.linear ℂ hx).mk' _)).isLinear
    · intro i j a
      let := i.property
      let := j.property
      have ht := IsSmoothComplexBundle.contMDiffOn_coordChange
        (n := n) (E := E) i.val j.val
      have heval : ContDiff ℝ ∞
          (fun T : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) ↦
            T (e₀.symm (Pi.single a 1))) :=
        (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
      have hv := heval.contMDiff.comp_contMDiffOn ht
      have hmodel := (e₀.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
      apply (hmodel.comp_contMDiffOn hv).congr
      intro x hx
      change e₀ (j.val (i.val.toOpenPartialHomeomorph.symm
        (x, e₀.symm (Pi.single a 1)))).2 = _
      exact congrArg e₀ (i.val.coordChangeL_apply' j.val hx _).symm
  have hregularity (u : ∀ x : M, E x) :
      S.IsContMDiffSection k u ↔ IsContMDiffSection (n := n) (r := r) E k u := by
    constructor
    · intro hu e he
      have hc := hu ⟨e, he⟩
      have hmodel := (e₀.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := k)
      apply (hmodel.comp_contMDiffOn hc).congr
      intro x hx
      change (e ⟨x, u x⟩).2 = e₀.symm (e₀ (e ⟨x, u x⟩).2)
      exact (e₀.symm_apply_apply _).symm
    · intro hu i
      have hc := hu i.val i.property
      have hmodel := (e₀.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := k)
      exact hmodel.comp_contMDiffOn hc
  -- Retain the specified finite chart/frame indices, partition and support certificates.
  let P : AtlasBundlePresentation S :=
    { size := A.size
      chart := A.chart
      chart_mem_atlas := A.chart_mem_atlas
      frameIndex := fun j ↦ ⟨A.frame j, A.frame_mem_atlas j⟩
      cutoff := A.cutoff
      smooth_cutoff := A.smooth_cutoff
      cutoff_nonneg := A.cutoff_nonneg
      compact_support := A.compact_support
      support_subset := A.support_subset
      sum_cutoff := A.sum_cutoff }
  let T : A.CkSectionSpace k ≃ₗ[ℂ] P.CkSectionSpace k :=
    { toFun := fun u ↦ ⟨u.val, (hregularity u.val).mpr u.property⟩
      invFun := fun u ↦ ⟨u.val, (hregularity u.val).mp u.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hlocal (j : Fin A.size) (u : A.CkSectionSpace k) :
      P.localizedCkFunction k j (T u) = A.localizedCkFunction k j u := by
    funext z
    change (if z ∈ (A.chart j).target then
      (A.cutoff j ((A.chart j).symm z) : ℂ) •
        e₀.symm (e₀ (A.frame j ⟨(A.chart j).symm z, u.val ((A.chart j).symm z)⟩).2)
      else 0) = _
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  -- The induced finite Pi norm is exactly the original supremum of derivative norms.
  have hnorm (u : A.CkSectionSpace k) : ‖T u‖ = ‖u‖ := by
    change ‖P.ckDerivativeCoordinates k (T u)‖ = A.ckNorm k u
    have hvalue (j : Fin A.size) (i : Fin (k + 1)) (x : EuclideanSpace ℝ (Fin n)) :
        P.ckDerivativeCoordinates k (T u) j i x =
          iteratedFDeriv ℝ i.val (A.localizedCkFunction k j u) x := by
      change iteratedFDeriv ℝ i.val (P.localizedCkFunction k j (T u)) x = _
      rw [hlocal]
    have hnonneg : 0 ≤ A.ckNorm k u := norm_nonneg u
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
      intro j
      apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
      intro i
      apply (BoundedContinuousFunction.norm_le hnonneg).mpr
      intro x
      apply (congrArg norm (hvalue j i x)).le.trans
      exact le_csSup (A.bddAbove_ckNorm_values k u)
        ⟨j, i.val, Nat.le_of_lt_succ i.isLt, x, rfl⟩
    · by_cases hsize : A.size = 0
      · have : IsEmpty (Fin A.size) := Fin.isEmpty_iff.mpr hsize
        simp [ckNorm]
      · apply csSup_le
        · obtain ⟨j⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hsize)
          exact ⟨_, j, 0, Nat.zero_le k, 0, rfl⟩
        · rintro a ⟨j, i, hi, x, rfl⟩
          let i' : Fin (k + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
          rw [← hvalue j i' x]
          exact ((P.ckDerivativeCoordinates k (T u) j i').norm_coe_le_norm x).trans
            ((norm_le_pi_norm _ i').trans (norm_le_pi_norm _ j))
  -- Transport completeness through this identity-on-values linear isometry.
  let e : A.CkSectionSpace k ≃ₗᵢ[ℂ] P.CkSectionSpace k :=
    { toLinearEquiv := T
      norm_map' := hnorm }
  exact e.toIsometryEquiv.completeSpace

attribute [instance] completeSpace_ckSectionSpace

/-- The usual inclusion of a smooth section as a C^k section. -/
def smoothToCk (k : ℕ) : smoothSections (n := n) (r := r) E →ₗ[ℂ] A.CkSectionSpace k where
  toFun u := ⟨u.val, isContMDiffSection_of_isSmoothSection E k u.val u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Different finite presentations define equivalent C^k norms on the same sections. -/
theorem exists_ck_norm_comparison (B : SmoothBundlePresentation (n := n) (r := r) E) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : A.CkSectionSpace k,
      ‖(show B.CkSectionSpace k from u)‖ ≤ C * ‖u‖ := by
  classical
  /- Project supplementary route: use the closed graph theorem on the identity
  between the two actual Banach section spaces. Order-zero localization controls
  original frame evaluations, which identifies any two graph limits pointwise.
  This proves the original bound without replacing either presentation or norm. -/
  -- Convergence in one presentation preserves evaluation in every original frame.
  have hpoint (P : SmoothBundlePresentation (n := n) (r := r) E)
      (a : ℕ → P.CkSectionSpace k) (u : P.CkSectionSpace k)
      (ha : Filter.Tendsto a Filter.atTop (nhds u))
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
      (x : M) (hxe : x ∈ e.baseSet) :
      Filter.Tendsto (fun b ↦ (e ⟨x, (a b).val x⟩).2) Filter.atTop
        (nhds ((e ⟨x, u.val x⟩).2)) := by
    have hchoose : ∃ j : Fin P.size, P.cutoff j x ≠ 0 := by
      by_contra! h
      have hsum := P.sum_cutoff x
      simp only [h, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨j, hj⟩ := hchoose
    have hx := P.support_subset j (subset_tsupport _ hj)
    let := P.frame_mem_atlas j
    let ev : P.CkSectionSpace k →ₗ[ℂ] EuclideanSpace ℂ (Fin r) :=
      { toFun := fun w ↦ (P.cutoff j x : ℂ) •
          ((P.frame j).linearEquivAt ℂ x hx.2) (w.val x)
        map_add' := by
          intro v w
          change (P.cutoff j x : ℂ) •
            ((P.frame j).linearEquivAt ℂ x hx.2) (v.val x + w.val x) = _
          rw [map_add, smul_add]
        map_smul' := by
          intro c w
          change (P.cutoff j x : ℂ) •
            ((P.frame j).linearEquivAt ℂ x hx.2) (c • w.val x) = _
          rw [map_smul, smul_comm]
          rfl }
    have heval (w : P.CkSectionSpace k) :
        ev w = P.localizedCkFunction k j w (P.chart j x) := by
      have hpair : (⟨(P.chart j).symm (P.chart j x),
          w.val ((P.chart j).symm (P.chart j x))⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, w.val x⟩ :=
        congrArg (fun y ↦ (⟨y, w.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
          ((P.chart j).left_inv hx.1)
      simp only [localizedCkFunction, ite_eq_left ((P.chart j).map_source hx.1),
        sectionInChart, hpair, (P.chart j).left_inv hx.1]
      rfl
    have hbound (w : P.CkSectionSpace k) : ‖ev w‖ ≤ 1 * ‖w‖ := by
      rw [one_mul, heval]
      change ‖P.localizedCkFunction k j w (P.chart j x)‖ ≤ P.ckNorm k w
      have h := le_csSup (P.bddAbove_ckNorm_values k w)
        (show ‖iteratedFDeriv ℝ 0 (P.localizedCkFunction k j w) (P.chart j x)‖ ∈
          {a : ℝ | ∃ (j : Fin P.size) (i : ℕ), i ≤ k ∧
            ∃ z : EuclideanSpace ℝ (Fin n),
              a = ‖iteratedFDeriv ℝ i (P.localizedCkFunction k j w) z‖} from
          ⟨j, 0, Nat.zero_le k, P.chart j x, rfl⟩)
      change ‖iteratedFDeriv ℝ 0 (P.localizedCkFunction k j w) (P.chart j x)‖ ≤
        P.ckNorm k w at h
      simpa only [norm_iteratedFDeriv_zero] using h
    have hvalues := ((ev.mkContinuous 1 hbound).continuous.tendsto u).comp ha
    -- Divide the nonzero original cutoff and use the finite-dimensional frame transition.
    let T := ((e.linearEquivAt ℂ x hxe).toLinearMap.comp
      ((P.frame j).linearEquivAt ℂ x hx.2).symm.toLinearMap).toContinuousLinearMap
    let ψ : EuclideanSpace ℂ (Fin r) → EuclideanSpace ℂ (Fin r) :=
      fun z ↦ T ((P.cutoff j x : ℂ)⁻¹ • z)
    have hψ : Continuous ψ := by
      change Continuous (fun z : EuclideanSpace ℂ (Fin r) ↦ T ((P.cutoff j x : ℂ)⁻¹ • z))
      have hscale : Continuous (fun z : EuclideanSpace ℂ (Fin r) ↦
          (P.cutoff j x : ℂ)⁻¹ • z) :=
        ((P.cutoff j x : ℂ)⁻¹ • ContinuousLinearMap.id ℂ
          (EuclideanSpace ℂ (Fin r))).continuous
      exact T.continuous.comp hscale
    have hχ : (P.cutoff j x : ℂ) ≠ 0 := by exact_mod_cast hj
    have hrecover (w : P.CkSectionSpace k) : ψ (ev w) = (e ⟨x, w.val x⟩).2 := by
      change (e.linearEquivAt ℂ x hxe)
        (((P.frame j).linearEquivAt ℂ x hx.2).symm
          ((P.cutoff j x : ℂ)⁻¹ •
            ((P.cutoff j x : ℂ) • ((P.frame j).linearEquivAt ℂ x hx.2) (w.val x)))) = _
      rw [smul_smul, inv_mul_cancel₀ hχ, one_smul, LinearEquiv.symm_apply_apply]
      rfl
    have hh := (hψ.tendsto _).comp hvalues
    change Filter.Tendsto (fun b ↦ ψ (ev (a b))) Filter.atTop (nhds (ψ (ev u))) at hh
    simpa only [hrecover] using hh
  -- Equality in each original frame makes the graph closed on the actual section values.
  let I : A.CkSectionSpace k →ₗ[ℂ] B.CkSectionSpace k :=
    { toFun := fun u ↦ u
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hcont : Continuous I := I.continuous_of_seq_closed_graph (by
    intro a u v hau hav
    apply Subtype.ext
    funext x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx := mem_baseSet_trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    apply (e.linearEquivAt ℂ x hx).injective
    exact tendsto_nhds_unique (hpoint B (I ∘ a) v hav e x hx)
      (hpoint A a u hau e x hx))
  let T : A.CkSectionSpace k →L[ℂ] B.CkSectionSpace k :=
    { toLinearMap := I, cont := hcont }
  -- A positive enlargement also covers the zero section space and an empty base.
  refine ⟨‖T‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg T) zero_lt_one, ?_⟩
  intro u
  calc
    ‖(show B.CkSectionSpace k from u)‖ = ‖T u‖ := rfl
    _ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
    _ ≤ (‖T‖ + 1) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg u)

/-- The global Sobolev estimate for the actual C^k norm of smooth sections. -/
theorem exists_sobolev_ck_bound (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      ‖A.smoothToCk k u‖ ≤ C * ‖A.smoothToSobolev s u‖ := by
  /- Apply the Euclidean real-order Sobolev embedding to each actual compactly
  supported localization. It bounds all derivatives through k by the local H^s
  norm under the strict exponent inequality. Each coordinate norm is bounded by
  the finite Hilbert norm; take the supremum over the finitely many localizations. -/
  classical
  obtain ⟨C, hC, hembed⟩ := sobolev_embedding n r k s hs
  refine ⟨C, hC, ?_⟩
  intro u
  -- Identify the Euclidean embedding representative with the original localization.
  have hlocal (j : Fin A.size) (i : ℕ) (hi : i ≤ k)
      (x : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ i (A.localize j u) x‖ ≤
        C * ‖schwartzSobolevCoordinate s (A.localize j u)‖ := by
    obtain ⟨v, hv, hpair, hbound⟩ :=
      hembed (schwartzSobolevCoordinate s (A.localize j u))
    have hveq_ae : v =ᵐ[volume] A.localize j u := by
      apply ae_eq_of_integral_contDiff_smul_eq hv.continuous.locallyIntegrable
        (A.localize j u).continuous.locallyIntegrable
      intro φ hφ hcφ
      let ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
        (hcφ.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
          (Complex.ofRealCLM.contDiff.comp hφ)
      have h := hpair ψ
      rw [besselRealization_schwartzSobolevCoordinate, SchwartzMap.coe_apply] at h
      simpa [ψ, Function.comp_def] using h.symm
    have hveq : v = A.localize j u :=
      MeasureTheory.Measure.eq_of_ae_eq hveq_ae hv.continuous (A.localize j u).continuous
    rw [hveq] at hbound
    exact hbound i hi x
  -- The fixed Hilbert tuple bounds each of its actual local Bessel coordinates.
  have hcoordinate (j : Fin A.size) :
      ‖schwartzSobolevCoordinate s (A.localize j u)‖ ≤ ‖A.smoothToSobolev s u‖ :=
    PiLp.norm_apply_le (A.sobolevCoordinates s u) j
  change A.ckNorm k (A.smoothToCk k u) ≤ C * ‖A.smoothToSobolev s u‖
  by_cases hsize : A.size = 0
  · have : IsEmpty (Fin A.size) := Fin.isEmpty_iff.mpr hsize
    simpa [ckNorm] using mul_nonneg hC (norm_nonneg (A.smoothToSobolev s u))
  · -- Every derivative defining the supremum has the same global bound.
    apply csSup_le
    · let j : Fin A.size := ⟨0, Nat.pos_of_ne_zero hsize⟩
      exact ⟨_, j, 0, Nat.zero_le k, 0, rfl⟩
    · rintro a ⟨j, i, hi, x, rfl⟩
      change ‖iteratedFDeriv ℝ i (A.localize j u) x‖ ≤ _
      exact (hlocal j i hi x).trans (mul_le_mul_of_nonneg_left (hcoordinate j) hC)

/-- SG III.2.15(1): the smooth inclusion extends uniquely from H^s to actual C^k sections. -/
theorem existsUnique_sobolevToCk (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    ∃! T : A.SobolevSpace s →L[ℂ] A.CkSectionSpace k,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev s u) = A.smoothToCk k u := by
  /- The Sobolev estimate bounds the actual smooth inclusion. The target C^k normed
  space is complete, so the map extends to the Sobolev completion. The source smooth
  image is dense and injective, giving a well-defined extension and its uniqueness. -/
  obtain ⟨C, _, hbound⟩ := A.exists_sobolev_ck_bound k s hs
  -- Extend the actual smooth inclusion into the proved complete C^k section space.
  let T := (A.smoothToCk k).extendOfNorm (A.smoothToSobolev s)
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev s u) = A.smoothToCk k u :=
    LinearMap.extendOfNorm_eq (A.denseRange_smoothToSobolev s) ⟨C, hbound⟩ u
  refine ⟨T, hT, ?_⟩
  -- Two bounded extensions agree on the same dense family of smooth sections.
  intro S hS
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer S.continuous T.continuous
  funext u
  exact (hS u).trans (hT u).symm

/-- The canonical Sobolev-to-C^k map, determined by the original smooth section. -/
def sobolevToCk (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    A.SobolevSpace s →L[ℂ] A.CkSectionSpace k :=
  Classical.choose (A.existsUnique_sobolevToCk k s hs).exists

/-- The global embedding preserves each actual smooth section. -/
theorem sobolevToCk_smoothToSobolev (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s)
    (u : smoothSections (n := n) (r := r) E) :
    A.sobolevToCk k s hs (A.smoothToSobolev s u) = A.smoothToCk k u := by
  /- Apply the specification of existsUnique_sobolevToCk to the chosen extension.
  Both embeddings in this equality use the identical underlying smooth section. -/
  exact (Classical.choose_spec (A.existsUnique_sobolevToCk k s hs).exists) u

/-- The output section represents the actual localized Sobolev distributions. -/
theorem localDistribution_sobolevToCk (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s)
    (j : Fin A.size) (u : A.SobolevSpace s)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    A.localDistribution s j u φ =
      ∫ x, φ x • A.localizedCkFunction k j (A.sobolevToCk k s hs u) x := by
  /- Order-zero localization is bounded by the original C^k norm.
  Schwartz L1 decay therefore makes integration against the fixed test
  a bounded linear map on these actual sections. Its composite with the
  Sobolev embedding and the Bessel test evaluation are continuous maps
  on H^s. Their equality on dense original smooth sections extends the
  exact localization formula to every Sobolev vector. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let := A.frame_mem_atlas j
  -- The actual localization is linear, including where the total frame is outside its domain.
  let loc : A.CkSectionSpace k →ₗ[ℂ] (X → V) :=
    { toFun := fun w x ↦ if x ∈ (A.chart j).target then
        (A.cutoff j ((A.chart j).symm x) : ℂ) •
          (A.frame j).linearMapAt ℂ ((A.chart j).symm x) (w.val ((A.chart j).symm x))
      else 0
      map_add' := by
        intro w z
        funext x
        by_cases hx : x ∈ (A.chart j).target
        · simp only [Pi.add_apply, ite_eq_left hx]
          change (A.cutoff j ((A.chart j).symm x) : ℂ) •
              (A.frame j).linearMapAt ℂ ((A.chart j).symm x)
                (w.val ((A.chart j).symm x) + z.val ((A.chart j).symm x)) =
            (A.cutoff j ((A.chart j).symm x) : ℂ) •
                (A.frame j).linearMapAt ℂ ((A.chart j).symm x) (w.val ((A.chart j).symm x)) +
              (A.cutoff j ((A.chart j).symm x) : ℂ) •
                (A.frame j).linearMapAt ℂ ((A.chart j).symm x) (z.val ((A.chart j).symm x))
          rw [map_add, smul_add]
        · simp [hx]
      map_smul' := by
        intro c w
        funext x
        by_cases hx : x ∈ (A.chart j).target
        · simp only [Pi.smul_apply, RingHom.id_apply, ite_eq_left hx]
          change (A.cutoff j ((A.chart j).symm x) : ℂ) •
              (A.frame j).linearMapAt ℂ ((A.chart j).symm x)
                (c • w.val ((A.chart j).symm x)) =
            c • ((A.cutoff j ((A.chart j).symm x) : ℂ) •
              (A.frame j).linearMapAt ℂ ((A.chart j).symm x) (w.val ((A.chart j).symm x)))
          rw [map_smul, smul_comm]
        · simp [hx] }
  have hloc (w : A.CkSectionSpace k) : loc w = A.localizedCkFunction k j w := by
    funext x
    change (if x ∈ (A.chart j).target then
      (A.cutoff j ((A.chart j).symm x) : ℂ) •
        (A.frame j).linearMapAt ℂ ((A.chart j).symm x) (w.val ((A.chart j).symm x))
      else 0) = _
    by_cases hx : x ∈ (A.chart j).target
    · simp only [localizedCkFunction, ite_eq_left hx, sectionInChart]
      by_cases hcut : (A.chart j).symm x ∈ tsupport (A.cutoff j)
      · rw [Trivialization.linearMapAt_apply, ite_eq_left (A.support_subset j hcut).2]
      · simp [image_eq_zero_of_notMem_tsupport hcut]
    · simp [localizedCkFunction, hx]
  -- Its order-zero values are bounded by the original C^k norm.
  have hloc_bound (w : A.CkSectionSpace k) (x : X) : ‖loc w x‖ ≤ ‖w‖ := by
    rw [hloc w]
    change ‖A.localizedCkFunction k j w x‖ ≤ A.ckNorm k w
    have h := le_csSup (A.bddAbove_ckNorm_values k w)
      (show ‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j w) x‖ ∈
        {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k ∧
          ∃ y : X, a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction k j w) y‖} from
        ⟨j, 0, Nat.zero_le k, x, rfl⟩)
    change ‖iteratedFDeriv ℝ 0 (A.localizedCkFunction k j w) x‖ ≤ A.ckNorm k w at h
    simpa only [norm_iteratedFDeriv_zero] using h
  have hbound (w : A.CkSectionSpace k) (x : X) :
      ‖φ x • loc w x‖ ≤ ‖φ x‖ * ‖w‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hloc_bound w x) (norm_nonneg _)
  have hint (w : A.CkSectionSpace k) : Integrable (fun x : X ↦ φ x • loc w x) := by
    apply (φ.integrable.norm.mul_const ‖w‖).mono'
    · rw [hloc w]
      exact (φ.continuous.smul
        (A.contDiff_localizedCkFunction k j w).continuous).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hbound w)
  -- The test integral is a bounded linear functional of the same actual C^k section.
  let I : A.CkSectionSpace k →ₗ[ℂ] V :=
    { toFun := fun w ↦ ∫ x : X, φ x • loc w x
      map_add' := by
        intro w z
        simp only [map_add, Pi.add_apply, smul_add]
        exact integral_add (hint w) (hint z)
      map_smul' := by
        intro c w
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with x
        exact smul_comm (φ x) c (loc w x) }
  have hI (w : A.CkSectionSpace k) : ‖I w‖ ≤ (∫ x : X, ‖φ x‖) * ‖w‖ := by
    change ‖∫ x : X, φ x • loc w x‖ ≤ _
    calc
      _ ≤ ∫ x : X, ‖φ x‖ * ‖w‖ := norm_integral_le_of_norm_le
        (φ.integrable.norm.mul_const ‖w‖) (Filter.Eventually.of_forall (hbound w))
      _ = _ := integral_mul_const _ _
  let T : A.SobolevCoordinates →L[ℂ] V :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) _ φ).comp
      ((besselRealization n r s).comp (PiLp.proj 2 _ j))
  have hleft : Continuous (fun w : A.SobolevSpace s ↦ A.localDistribution s j w φ) :=
    T.continuous.comp continuous_subtype_val
  have hright : Continuous (fun w : A.SobolevSpace s ↦ I (A.sobolevToCk k s hs w)) :=
    (I.mkContinuous (∫ x : X, ‖φ x‖) hI).continuous.comp
      (A.sobolevToCk k s hs).continuous
  -- Extend the exact smooth-input identity by density in the original Sobolev completion.
  have heq : A.localDistribution s j u φ = I (A.sobolevToCk k s hs u) := by
    refine (A.denseRange_smoothToSobolev s).induction_on u (isClosed_eq hleft hright) ?_
    intro v
    rw [A.localDistribution_smoothToSobolev, A.sobolevToCk_smoothToSobolev]
    change (∫ x, φ x • A.localizedFunction j v x) =
      ∫ x, φ x • loc (A.smoothToCk k v) x
    rw [hloc]
    rfl
  change A.localDistribution s j u φ = ∫ x, φ x • loc (A.sobolevToCk k s hs u) x at heq
  simpa only [hloc] using heq

/-- The Sobolev-to-C^k map is injective on represented sections. -/
theorem sobolevToCk_injective (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    Function.Injective (A.sobolevToCk k s hs) := by
  /- Equal output sections give equal test integrals in every chart. The distribution
  identity gives equality of the localized Sobolev distributions. Injectivity of
  each Bessel realization then recovers all Hilbert coordinates of the input vector. -/
  intro u v huv
  apply Subtype.ext
  apply (WithLp.ext_iff 2).mpr
  funext j
  -- Equal actual output sections represent equal distributions in every original chart.
  apply besselRealization_injective n r s
  apply ContinuousLinearMap.ext
  intro φ
  change A.localDistribution s j u φ = A.localDistribution s j v φ
  rw [A.localDistribution_sobolevToCk k s hs j u φ,
    A.localDistribution_sobolevToCk k s hs j v φ, huv]

/-- The same strict exponent gives compactness of the global Sobolev-to-C^k map. -/
theorem isCompactOperator_sobolevToCk (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + k < s) :
    IsCompactOperator (A.sobolevToCk k s hs) := by
  /- Choose t strictly between n/2+k and s. Rellich gives compact H^s→H^t, followed
  by bounded H^t→C^k. Their composite agrees with the displayed map on dense smooth
  sections, hence everywhere. A bounded map after a compact map is compact. -/
  obtain ⟨t, ht, hts⟩ := exists_between hs
  have hcompact := (A.isCompactOperator_sobolevInclusion s t hts).clm_comp
    (A.sobolevToCk k t ht)
  have heq : (A.sobolevToCk k t ht).comp (A.sobolevInclusion s t hts.le) =
      A.sobolevToCk k s hs := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer
      ((A.sobolevToCk k t ht).comp (A.sobolevInclusion s t hts.le)).continuous
      (A.sobolevToCk k s hs).continuous
    funext u
    change A.sobolevToCk k t ht (A.sobolevInclusion s t hts.le (A.smoothToSobolev s u)) =
      A.sobolevToCk k s hs (A.smoothToSobolev s u)
    rw [A.sobolevInclusion_smoothToSobolev, A.sobolevToCk_smoothToSobolev,
      A.sobolevToCk_smoothToSobolev]
  change IsCompactOperator ((A.sobolevToCk k t ht).comp
    (A.sobolevInclusion s t hts.le)) at hcompact
  rwa [heq] at hcompact

end SmoothBundlePresentation

end AtiyahSinger
