/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSobolevMaps
public import AtiyahSinger.Geometry.AtlasFrame
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Finite-order sections of a locally finite-rank smooth bundle

Public module ID: M0232.

A01: C^k sections are dependent functions tested in the specified bundle atlas.
A finite presentation gives the norm as the maximum of the suprema of local
real Fréchet derivatives through order k. Bounded continuous derivative
coordinates form an injective linear map, with the rank of each selected
chart used separately. The resulting section space is complete, and different
finite presentations give equivalent norms.

Sources: Spin Geometry III.2.5, (2.9), and III.2.15(1). The book uses a finite
sum of coordinate partial derivatives; this construction uses the maximum
of operator norms and does not assert equality with that finite sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff BoundedContinuousFunction

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

namespace SmoothComplexBundleAtlas

variable (A : SmoothComplexBundleAtlas (n := n) E)

/-- Finite real regularity of the original section in every original bundle chart. -/
def IsContMDiffSection (k : ℕ) (u : ∀ x : M, E x) : Prop :=
  ∀ i : A.Index,
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (A.rank i) → ℂ) k
      (fun x : M ↦ (A.chart i ⟨x, u x⟩).2) (A.chart i).baseSet

/-- The grouped algebraic closure certificate for finite-order original sections. -/
theorem isContMDiffSection_closure (k : ℕ) :
    A.IsContMDiffSection k 0 ∧
      (∀ u v : ∀ x : M, E x,
        A.IsContMDiffSection k u → A.IsContMDiffSection k v →
          A.IsContMDiffSection k (u + v)) ∧
      (∀ (c : ℂ) (u : ∀ x : M, E x),
        A.IsContMDiffSection k u → A.IsContMDiffSection k (c • u)) := by
  /- In each chart, use its original fiberwise linearity to identify coordinates
  of zero, addition and complex scalar multiplication. The corresponding finite
  real regularity rules apply on that same open base set. Ranks are chartwise. -/
  constructor
  · intro i
    -- Each original linear frame takes the zero section to the zero coordinate map.
    apply (contMDiffOn_const (c := (0 : Fin (A.rank i) → ℂ))).congr
    intro x hx
    exact (A.linear i x hx).map_zero
  constructor
  · intro u v hu hv i
    apply ((hu i).add (hv i)).congr
    intro x hx
    exact (A.linear i x hx).map_add (u x) (v x)
  · intro c u hu i
    -- The model rank is local to this frame; complex scaling is a real-smooth map.
    have hscale := ((c • ContinuousLinearMap.id ℂ (Fin (A.rank i) → ℂ)).restrictScalars
      ℝ).contMDiff (n := k)
    apply (hscale.comp_contMDiffOn (hu i)).congr
    intro x hx
    exact (A.linear i x hx).map_smul c (u x)

/-- The standard complex submodule of actual C^k sections of the original bundle. -/
def contMDiffSections (k : ℕ) : Submodule ℂ (∀ x : M, E x) where
  carrier := {u | A.IsContMDiffSection k u}
  zero_mem' := (A.isContMDiffSection_closure k).1
  add_mem' := fun hu hv ↦ (A.isContMDiffSection_closure k).2.1 _ _ hu hv
  smul_mem' := fun c _ hu ↦ (A.isContMDiffSection_closure k).2.2 c _ hu

/-- An original smooth section has every finite order of real regularity. -/
theorem isContMDiffSection_of_isSmoothSection (k : ℕ) (u : ∀ x : M, E x)
    (hu : A.IsSmoothSection u) : A.IsContMDiffSection k u := by
  /- In each original chart lower the regularity index from infinity to k.
  Neither the section values nor the original chart domains change. -/
  intro i

  exact (hu i).of_le (by simp)

end SmoothComplexBundleAtlas

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  {A : SmoothComplexBundleAtlas (n := n) E}

include hM hT2 hSC

namespace AtlasBundlePresentation

variable (L : AtlasBundlePresentation A)

/-- Actual C^k sections tagged by the presentation that specifies their norm. -/
def CkSectionSpace (_L : AtlasBundlePresentation A) (k : ℕ) : Type _ :=
  A.contMDiffSections k

/-- The inherited additive structure on the actual finite-order sections. -/
@[instance_reducible]
def ckSectionAddCommGroup (k : ℕ) : AddCommGroup (L.CkSectionSpace k) :=
  inferInstanceAs (AddCommGroup (A.contMDiffSections k))

attribute [instance] ckSectionAddCommGroup

/-- The inherited complex scalar action on the original finite-order sections. -/
@[instance_reducible]
def ckSectionModule (k : ℕ) : Module ℂ (L.CkSectionSpace k) :=
  inferInstanceAs (Module ℂ (A.contMDiffSections k))

attribute [instance] ckSectionModule

/-- The actual cutoff coordinate function, extended by zero outside the manifold chart. -/
def localizedCkFunction (k : ℕ) (j : Fin L.size) (u : L.CkSectionSpace k)
    (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j))) := by
  classical
  exact if z ∈ (L.chart j).target then
    (L.cutoff j ((L.chart j).symm z) : ℂ) •
      atlasSectionInChart A (L.chart j) (L.frameIndex j) u.val z
  else 0

set_option linter.unusedSectionVars false in
/-- Continuity and boundedness certificates for every localized derivative through order k. -/
theorem localizedCkFunction_derivative_properties (k : ℕ) (j : Fin L.size)
    (u : L.CkSectionSpace k) (i : Fin (k + 1)) :
    Continuous (iteratedFDeriv ℝ i.val (L.localizedCkFunction k j u)) ∧
      ∃ C : ℝ, ∀ x y : EuclideanSpace ℝ (Fin n),
        dist (iteratedFDeriv ℝ i.val (L.localizedCkFunction k j u) x)
          (iteratedFDeriv ℝ i.val (L.localizedCkFunction k j u) y) ≤ C := by
  /- Stage 1: the cutoff support is compactly contained in the manifold/frame
  overlap. There the actual section coordinates are C^k; multiplication by the
  smooth cutoff and zero extension give a globally C^k Euclidean function.
  Stage 2: every derivative through order k is continuous and supported in the
  same fixed compact coordinate image. Its norm is bounded there and vanishes
  outside. Twice this norm bound gives the displayed pairwise distance bound. -/
  have hlocal_properties (j : Fin L.size) (u : L.CkSectionSpace k) :
      ContDiff ℝ k (L.localizedCkFunction k j u) ∧
        HasCompactSupport (L.localizedCkFunction k j u) := by
    classical
    let c := L.chart j
    let K := c '' tsupport (L.cutoff j)
    have hcompact : IsCompact K :=
      (L.compact_support j).image_of_continuousOn
        (c.continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
    -- Every actual coordinate value is supported in the same compact cutoff image.
    have hsupport : tsupport (L.localizedCkFunction k j u) ⊆ K := by
      apply closure_minimal ?_ hcompact.isClosed
      intro z hz
      have htarget : z ∈ c.target := by
        by_contra houtside
        change z ∉ (L.chart j).target at houtside
        exact hz (by simp [localizedCkFunction, houtside])
      have hcut : c.symm z ∈ tsupport (L.cutoff j) := by
        by_contra houtside
        have hzero := image_eq_zero_of_notMem_tsupport houtside
        change L.cutoff j ((L.chart j).symm z) = 0 at hzero
        exact hz (by simp [localizedCkFunction, hzero])
      exact ⟨c.symm z, hcut, c.right_inv htarget⟩
    refine ⟨?_, hcompact.of_isClosed_subset (isClosed_tsupport _) hsupport⟩
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ K
    · obtain ⟨x, hx, rfl⟩ := hz
      have hxsource := (L.support_subset j hx).1
      have htarget : c x ∈ c.target := c.map_source hxsource
      have hframe : c.symm (c x) ∈ (A.chart (L.frameIndex j)).baseSet := by
        rw [c.left_inv hxsource]
        exact (L.support_subset j hx).2
      -- Retain this frame's own rank and its original finite-order section coordinates.
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (L.chart_mem_atlas j)) htarget
      have hsection := (u.property (L.frameIndex j)).contMDiffAt
        ((A.chart (L.frameIndex j)).open_baseSet.mem_nhds hframe)
      let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
      have hcoords := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp (c x)
        (hsection.comp (c x) (hchart.of_le (by simp)))
      have hcut := (L.smooth_cutoff j).contMDiffAt.comp (c x) hchart
      have hscalar := Complex.ofRealCLM.contDiff.comp_contMDiffAt hcut
      have hlocal := (hscalar.contDiffAt.of_le (by simp)).smul hcoords.contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [c.open_target.mem_nhds htarget] with y hy
      change y ∈ (L.chart j).target at hy
      simp [localizedCkFunction, atlasSectionInChart, hy, c, e]
    · -- The fixed compact support leaves an open zero region across the chart boundary.
      apply (contDiffAt_const
        (c := (0 : EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))))).congr_of_eventuallyEq
      filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun hmem ↦ hy (hsupport hmem))
  -- Finite-order derivatives are continuous and retain the same compact support.
  have hi : (i.val : ℕ∞ω) ≤ k := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hcont := (hlocal_properties j u).1.continuous_iteratedFDeriv hi
  refine ⟨hcont, ?_⟩
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
    ((hlocal_properties j u).2.iteratedFDeriv i.val)
  exact ⟨C + C, fun x y ↦ (dist_le_norm_add_norm _ _).trans (add_le_add (hC x) (hC y))⟩

/-- Finite bounded derivative coordinates, using the rank of each original selected chart. -/
abbrev CkCoordinates (k : ℕ) : Type :=
  ∀ j : Fin L.size, ∀ i : Fin (k + 1),
    EuclideanSpace ℝ (Fin n) →ᵇ
      ContinuousMultilinearMap ℝ (fun _ : Fin i.val ↦ EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j))))

/-- The actual local derivatives of a section, packaged as bounded continuous functions. -/
def ckDerivativeCoordinates (k : ℕ) (u : L.CkSectionSpace k) : L.CkCoordinates k :=
  fun j i ↦
    { toFun := iteratedFDeriv ℝ i.val (L.localizedCkFunction k j u)
      continuous_toFun := (L.localizedCkFunction_derivative_properties k j u i).1
      map_bounded' := (L.localizedCkFunction_derivative_properties k j u i).2 }

/-- The derivative coordinate map is complex linear and separates actual sections. -/
theorem ckDerivativeCoordinates_properties (k : ℕ) :
    IsLinearMap ℂ (L.ckDerivativeCoordinates k) ∧
      Function.Injective (L.ckDerivativeCoordinates k) := by
  /- Stage 1: localization is complex linear by the original frame linearity.
  The real derivatives through k commute with addition and fixed complex scalar
  multiplication on C^k functions, so the bounded derivative coordinates are linear.
  Stage 2: equality of the order-zero derivative coordinates gives equality of
  the cutoff section values in each original frame. Pull back through those
  frames and sum the partition identity to recover every original section value.
  An empty presentation forces an empty base, so injectivity also holds there. -/
  classical
  have hlocal_properties (j : Fin L.size) (u : L.CkSectionSpace k) :
      ContDiff ℝ k (L.localizedCkFunction k j u) ∧
        HasCompactSupport (L.localizedCkFunction k j u) := by
    classical
    let c := L.chart j
    let K := c '' tsupport (L.cutoff j)
    have hcompact : IsCompact K :=
      (L.compact_support j).image_of_continuousOn
        (c.continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
    -- Every actual coordinate value is supported in the same compact cutoff image.
    have hsupport : tsupport (L.localizedCkFunction k j u) ⊆ K := by
      apply closure_minimal ?_ hcompact.isClosed
      intro z hz
      have htarget : z ∈ c.target := by
        by_contra houtside
        change z ∉ (L.chart j).target at houtside
        exact hz (by simp [localizedCkFunction, houtside])
      have hcut : c.symm z ∈ tsupport (L.cutoff j) := by
        by_contra houtside
        have hzero := image_eq_zero_of_notMem_tsupport houtside
        change L.cutoff j ((L.chart j).symm z) = 0 at hzero
        exact hz (by simp [localizedCkFunction, hzero])
      exact ⟨c.symm z, hcut, c.right_inv htarget⟩
    refine ⟨?_, hcompact.of_isClosed_subset (isClosed_tsupport _) hsupport⟩
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ K
    · obtain ⟨x, hx, rfl⟩ := hz
      have hxsource := (L.support_subset j hx).1
      have htarget : c x ∈ c.target := c.map_source hxsource
      have hframe : c.symm (c x) ∈ (A.chart (L.frameIndex j)).baseSet := by
        rw [c.left_inv hxsource]
        exact (L.support_subset j hx).2
      -- Retain this frame's own rank and its original finite-order section coordinates.
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (L.chart_mem_atlas j)) htarget
      have hsection := (u.property (L.frameIndex j)).contMDiffAt
        ((A.chart (L.frameIndex j)).open_baseSet.mem_nhds hframe)
      let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
      have hcoords := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp (c x)
        (hsection.comp (c x) (hchart.of_le (by simp)))
      have hcut := (L.smooth_cutoff j).contMDiffAt.comp (c x) hchart
      have hscalar := Complex.ofRealCLM.contDiff.comp_contMDiffAt hcut
      have hlocal := (hscalar.contDiffAt.of_le (by simp)).smul hcoords.contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [c.open_target.mem_nhds htarget] with y hy
      change y ∈ (L.chart j).target at hy
      simp [localizedCkFunction, atlasSectionInChart, hy, c, e]
    · -- The fixed compact support leaves an open zero region across the chart boundary.
      apply (contDiffAt_const
        (c := (0 : EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))))).congr_of_eventuallyEq
      filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun hmem ↦ hy (hsupport hmem))
  -- Localization is linear on the original dependent fibers, wherever a cutoff is nonzero.
  have hadd (j : Fin L.size) (u v : L.CkSectionSpace k) :
      L.localizedCkFunction k j (u + v) =
        L.localizedCkFunction k j u + L.localizedCkFunction k j v := by
    funext z
    by_cases hz : z ∈ (L.chart j).target
    · by_cases hcut : (L.chart j).symm z ∈ tsupport (L.cutoff j)
      · have hframe := (L.support_subset j hcut).2
        simp only [localizedCkFunction, ite_eq_left hz, atlasSectionInChart, Pi.add_apply]
        change (L.cutoff j ((L.chart j).symm z) : ℂ) •
          (EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ).symm
            ((A.chart (L.frameIndex j) ⟨(L.chart j).symm z,
              u.val ((L.chart j).symm z) + v.val ((L.chart j).symm z)⟩).2) = _
        rw [(A.linear (L.frameIndex j) ((L.chart j).symm z) hframe).map_add]
        simp only [map_add, smul_add]
      · simp [localizedCkFunction, image_eq_zero_of_notMem_tsupport hcut]
    · simp [localizedCkFunction, hz]
  have hsmul (j : Fin L.size) (a : ℂ) (u : L.CkSectionSpace k) :
      L.localizedCkFunction k j (a • u) = a • L.localizedCkFunction k j u := by
    funext z
    by_cases hz : z ∈ (L.chart j).target
    · by_cases hcut : (L.chart j).symm z ∈ tsupport (L.cutoff j)
      · have hframe := (L.support_subset j hcut).2
        simp only [localizedCkFunction, ite_eq_left hz, atlasSectionInChart, Pi.smul_apply]
        change (L.cutoff j ((L.chart j).symm z) : ℂ) •
          (EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ).symm
            ((A.chart (L.frameIndex j) ⟨(L.chart j).symm z,
              a • u.val ((L.chart j).symm z)⟩).2) = _
        rw [(A.linear (L.frameIndex j) ((L.chart j).symm z) hframe).map_smul]
        simp only [map_smul, smul_comm (L.cutoff j ((L.chart j).symm z) : ℂ) a]
      · simp [localizedCkFunction, image_eq_zero_of_notMem_tsupport hcut]
    · simp [localizedCkFunction, hz]
  constructor
  · constructor
    · intro u v
      funext j i
      apply DFunLike.ext
      intro z
      change iteratedFDeriv ℝ i.val (L.localizedCkFunction k j (u + v)) z =
        iteratedFDeriv ℝ i.val (L.localizedCkFunction k j u) z +
          iteratedFDeriv ℝ i.val (L.localizedCkFunction k j v) z
      have hi : (i.val : ℕ∞ω) ≤ k := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      rw [hadd, iteratedFDeriv_add_apply
        ((hlocal_properties j u).1.of_le hi).contDiffAt
        ((hlocal_properties j v).1.of_le hi).contDiffAt]
    · intro a u
      funext j i
      apply DFunLike.ext
      intro z
      change iteratedFDeriv ℝ i.val (L.localizedCkFunction k j (a • u)) z =
        a • iteratedFDeriv ℝ i.val (L.localizedCkFunction k j u) z
      have hi : (i.val : ℕ∞ω) ≤ k := by exact_mod_cast Nat.le_of_lt_succ i.isLt
      rw [hsmul, iteratedFDeriv_const_smul_apply
        ((hlocal_properties j u).1.of_le hi).contDiffAt]
  · intro u v h
    -- Order-zero coordinates retain the original localized values, not only derivative data.
    have hlocal (j : Fin L.size) (z : EuclideanSpace ℝ (Fin n)) :
        L.localizedCkFunction k j u z = L.localizedCkFunction k j v z := by
      have hzero := congrArg
        (fun f : L.CkCoordinates k ↦ f j ⟨0, Nat.zero_lt_succ k⟩ z
          (fun a : Fin 0 ↦ Fin.elim0 a)) h
      simpa only [ckDerivativeCoordinates, BoundedContinuousFunction.coe_mk,
        iteratedFDeriv_zero_apply] using hzero
    apply Subtype.ext
    funext x
    have hcut (j : Fin L.size) :
        (L.cutoff j x : ℂ) • u.val x = (L.cutoff j x : ℂ) • v.val x := by
      by_cases hx : x ∈ tsupport (L.cutoff j)
      · have hsource := (L.support_subset j hx).1
        have hframe := (L.support_subset j hx).2
        have htarget := (L.chart j).map_source hsource
        have hpointu :
            (⟨(L.chart j).symm (L.chart j x),
              u.val ((L.chart j).symm (L.chart j x))⟩ : TotalSpace Unit E) = ⟨x, u.val x⟩ :=
          congrArg (fun y ↦ (⟨y, u.val y⟩ : TotalSpace Unit E)) ((L.chart j).left_inv hsource)
        have hpointv :
            (⟨(L.chart j).symm (L.chart j x),
              v.val ((L.chart j).symm (L.chart j x))⟩ : TotalSpace Unit E) = ⟨x, v.val x⟩ :=
          congrArg (fun y ↦ (⟨y, v.val y⟩ : TotalSpace Unit E)) ((L.chart j).left_inv hsource)
        have hcoords := hlocal j (L.chart j x)
        simp only [localizedCkFunction, ite_eq_left htarget, atlasSectionInChart,
          hpointu, hpointv, (L.chart j).left_inv hsource] at hcoords
        -- Undo exactly the selected chart's Euclidean coordinates and original linear frame.
        apply (A.frameLinearEquiv (L.frameIndex j) x hframe).injective
        simp only [map_smul]
        apply (EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ).symm.injective
        simpa only [map_smul, SmoothComplexBundleAtlas.frameLinearEquiv,
          LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] using hcoords
      · simp [image_eq_zero_of_notMem_tsupport hx]
    -- The same partition of unity reconstructs both original fiber values.
    have hsum : ∑ j, (L.cutoff j x : ℂ) = 1 := by exact_mod_cast L.sum_cutoff x
    calc
      u.val x = (∑ j, (L.cutoff j x : ℂ)) • u.val x := by rw [hsum, one_smul]
      _ = ∑ j, (L.cutoff j x : ℂ) • u.val x := Finset.sum_smul
      _ = ∑ j, (L.cutoff j x : ℂ) • v.val x := Finset.sum_congr rfl (fun j _ ↦ hcut j)
      _ = (∑ j, (L.cutoff j x : ℂ)) • v.val x := Finset.sum_smul.symm
      _ = v.val x := by rw [hsum, one_smul]

/-- The injective linear derivative map used to specify the standard finite-order norm. -/
def ckDerivativeCoordinatesLinearMap (k : ℕ) :
    L.CkSectionSpace k →ₗ[ℂ] L.CkCoordinates k :=
  IsLinearMap.mk' (L.ckDerivativeCoordinates k) (L.ckDerivativeCoordinates_properties k).1

/-- The norm is the maximum of all localized derivative suprema through order k. -/
@[instance_reducible]
def ckSectionNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (L.CkSectionSpace k) :=
  NormedAddCommGroup.induced _ _ (L.ckDerivativeCoordinatesLinearMap k)
    (L.ckDerivativeCoordinates_properties k).2

attribute [instance] ckSectionNormedAddCommGroup

/-- The induced derivative norm is compatible with the original complex scalar action. -/
@[instance_reducible]
def ckSectionNormedSpace (k : ℕ) : NormedSpace ℂ (L.CkSectionSpace k) :=
  NormedSpace.induced ℂ _ _ (L.ckDerivativeCoordinatesLinearMap k)

attribute [instance] ckSectionNormedSpace

/-- The original C^k section space is complete in the finite localized derivative norm. -/
theorem completeSpace_ckSectionSpace (k : ℕ) : CompleteSpace (L.CkSectionSpace k) := by
  classical
  /- Work in the original bounded-jet coordinates. Their uniform limits reconstruct
  actual fiber values using nonzero partition weights. Compatibility in every original
  frame then gives a C^k section and convergence in precisely the original norm. -/
  -- A compatible uniform limit of the original jets remains the jet of a C^k function.
  have hjet (r : ℕ)
      (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (g : ∀ i : Fin (k + 1), EuclideanSpace ℝ (Fin n) →
        ContinuousMultilinearMap ℝ (fun _ : Fin i.val ↦ EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℂ (Fin r)))
      (hf : ∀ a, ContDiff ℝ k (f a))
      (hg : ∀ i, Continuous (g i))
      (hlim : ∀ i, TendstoUniformly (fun a ↦ iteratedFDeriv ℝ i.val (f a)) (g i)
        Filter.atTop) :
      let f₀ := fun z ↦ (g ⟨0, Nat.zero_lt_succ k⟩ z) (fun a ↦ Fin.elim0 a)
      ContDiff ℝ k f₀ ∧
        (∀ i : Fin (k + 1), iteratedFDeriv ℝ i.val f₀ = g i) ∧
        ∀ z, Filter.Tendsto (fun a ↦ f a z) Filter.atTop (nhds (f₀ z)) := by
    dsimp only
    let f₀ := fun z ↦ (g ⟨0, Nat.zero_lt_succ k⟩ z) (fun a ↦ Fin.elim0 a)
    have hderiv (m : ℕ) (hm : m < k) (x : EuclideanSpace ℝ (Fin n)) :
        HasFDerivAt (g ⟨m, by omega⟩)
          (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (m + 1) ↦ EuclideanSpace ℝ (Fin n))
              (EuclideanSpace ℂ (Fin r)) (g ⟨m + 1, by omega⟩ x)) x := by
      let e := continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) ↦ EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℂ (Fin r))
      apply hasFDerivAt_of_tendstoUniformly
        (e.isometry.uniformContinuous.comp_tendstoUniformly (hlim ⟨m + 1, by omega⟩))
        (fun a y ↦ ?_) (fun y ↦ (hlim ⟨m, by omega⟩).tendsto_at y) x
      have hmk : (m : ℕ∞ω) < k := by exact_mod_cast hm
      simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using
        ((hf a).differentiable_iteratedFDeriv hmk y).hasFDerivAt
    have heq (m : ℕ) (hm : m ≤ k) :
        iteratedFDeriv ℝ m f₀ = g ⟨m, by omega⟩ := by
      induction m with
      | zero =>
          funext x
          apply ContinuousMultilinearMap.ext
          intro a
          simp only [iteratedFDeriv_zero_apply, f₀]
          congr 1
          exact Subsingleton.elim _ _
      | succ m ih =>
          have hm' : m < k := by omega
          funext x
          rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih (by omega),
            (hderiv m hm' x).fderiv]
          exact LinearIsometryEquiv.symm_apply_apply _ _
    refine ⟨?_, fun i ↦ heq i.val (by omega), ?_⟩
    · apply contDiff_nat_iff_continuous_differentiable.mpr
      constructor
      · intro m hm
        rw [heq m hm]
        exact hg _
      · intro m hm
        rw [heq m hm.le]
        exact fun x ↦ (hderiv m hm x).differentiableAt
    · intro z
      let e := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℂ (Fin r))
      have hz := e.continuous.tendsto (g ⟨0, Nat.zero_lt_succ k⟩ z) |>.comp
        ((hlim ⟨0, Nat.zero_lt_succ k⟩).tendsto_at z)
      have hnil : (0 : Fin 0 → EuclideanSpace ℝ (Fin n)) = (fun a ↦ Fin.elim0 a) :=
        Subsingleton.elim _ _
      simpa only [Function.comp_def, e, continuousMultilinearCurryFin0_apply,
        iteratedFDeriv_zero_apply, hnil, f₀] using hz
  have hlocal_properties (j : Fin L.size) (u : L.CkSectionSpace k) :
      ContDiff ℝ k (L.localizedCkFunction k j u) ∧
        HasCompactSupport (L.localizedCkFunction k j u) := by
    classical
    let c := L.chart j
    let K := c '' tsupport (L.cutoff j)
    have hcompact : IsCompact K :=
      (L.compact_support j).image_of_continuousOn
        (c.continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
    -- Every actual coordinate value is supported in the same compact cutoff image.
    have hsupport : tsupport (L.localizedCkFunction k j u) ⊆ K := by
      apply closure_minimal ?_ hcompact.isClosed
      intro z hz
      have htarget : z ∈ c.target := by
        by_contra houtside
        change z ∉ (L.chart j).target at houtside
        exact hz (by simp [localizedCkFunction, houtside])
      have hcut : c.symm z ∈ tsupport (L.cutoff j) := by
        by_contra houtside
        have hzero := image_eq_zero_of_notMem_tsupport houtside
        change L.cutoff j ((L.chart j).symm z) = 0 at hzero
        exact hz (by simp [localizedCkFunction, hzero])
      exact ⟨c.symm z, hcut, c.right_inv htarget⟩
    refine ⟨?_, hcompact.of_isClosed_subset (isClosed_tsupport _) hsupport⟩
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ K
    · obtain ⟨x, hx, rfl⟩ := hz
      have hxsource := (L.support_subset j hx).1
      have htarget : c x ∈ c.target := c.map_source hxsource
      have hframe : c.symm (c x) ∈ (A.chart (L.frameIndex j)).baseSet := by
        rw [c.left_inv hxsource]
        exact (L.support_subset j hx).2
      -- Retain this frame's own rank and its original finite-order section coordinates.
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (L.chart_mem_atlas j)) htarget
      have hsection := (u.property (L.frameIndex j)).contMDiffAt
        ((A.chart (L.frameIndex j)).open_baseSet.mem_nhds hframe)
      let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
      have hcoords := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp (c x)
        (hsection.comp (c x) (hchart.of_le (by simp)))
      have hcut := (L.smooth_cutoff j).contMDiffAt.comp (c x) hchart
      have hscalar := Complex.ofRealCLM.contDiff.comp_contMDiffAt hcut
      have hlocal := (hscalar.contDiffAt.of_le (by simp)).smul hcoords.contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [c.open_target.mem_nhds htarget] with y hy
      change y ∈ (L.chart j).target at hy
      simp [localizedCkFunction, atlasSectionInChart, hy, c, e]
    · -- The fixed compact support leaves an open zero region across the chart boundary.
      apply (contDiffAt_const
        (c := (0 : EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))))).congr_of_eventuallyEq
      filter_upwards [hcompact.isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun hmem ↦ hy (hsupport hmem))
  -- Pass the Cauchy sequence into the fixed complete space of bounded jets.
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hiso : Isometry (L.ckDerivativeCoordinates k) := by
    intro v w
    rfl
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete (hiso.uniformContinuous.comp_cauchySeq hu)
  have hlim (j : Fin L.size) (i : Fin (k + 1)) :
      TendstoUniformly (fun a ↦ iteratedFDeriv ℝ i.val (L.localizedCkFunction k j (u a)))
        (F j i) Filter.atTop := by
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hF j)) i)
  let v (j : Fin L.size) (z : EuclideanSpace ℝ (Fin n)) :=
    (F j ⟨0, Nat.zero_lt_succ k⟩ z) (fun a ↦ Fin.elim0 a)
  have hv (j : Fin L.size) : ContDiff ℝ k (v j) ∧
      (∀ i : Fin (k + 1), iteratedFDeriv ℝ i.val (v j) = F j i) ∧
      ∀ z, Filter.Tendsto (fun a ↦ L.localizedCkFunction k j (u a) z)
        Filter.atTop (nhds (v j z)) := by
    exact hjet (A.rank (L.frameIndex j)) (fun a ↦ L.localizedCkFunction k j (u a))
      (fun i ↦ F j i) (fun a ↦ (hlocal_properties j (u a)).1)
      (fun i ↦ (F j i).continuous) (hlim j)
  -- The original partition always supplies a nonzero weight at any original base point.
  have hchoose (x : M) : ∃ j : Fin L.size, L.cutoff j x ≠ 0 := by
    by_contra! h
    have hsum := L.sum_cutoff x
    simp only [h, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  choose pick hpick using hchoose
  have hpick_valid (x : M) :
      x ∈ (L.chart (pick x)).source ∩ (A.chart (L.frameIndex (pick x))).baseSet := by
    exact L.support_subset (pick x) (subset_tsupport _ (hpick x))
  let s (x : M) : E x :=
    (A.frameLinearEquiv (L.frameIndex (pick x)) x (hpick_valid x).2).symm
      ((L.cutoff (pick x) x : ℂ)⁻¹ •
        (EuclideanSpace.equiv (Fin (A.rank (L.frameIndex (pick x)))) ℂ)
          (v (pick x) (L.chart (pick x) x)))
  have hvalue (j : Fin L.size) (x : M) (hxs : x ∈ (L.chart j).source)
      (hxf : x ∈ (A.chart (L.frameIndex j)).baseSet) (w : L.CkSectionSpace k) :
      L.localizedCkFunction k j w (L.chart j x) = (L.cutoff j x : ℂ) •
        (EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ).symm
          ((A.frameLinearEquiv (L.frameIndex j) x hxf) (w.val x)) := by
    have hpoint : (⟨(L.chart j).symm (L.chart j x),
        w.val ((L.chart j).symm (L.chart j x))⟩ : TotalSpace Unit E) = ⟨x, w.val x⟩ :=
      congrArg (fun y ↦ (⟨y, w.val y⟩ : TotalSpace Unit E)) ((L.chart j).left_inv hxs)
    simp only [localizedCkFunction, ite_eq_left ((L.chart j).map_source hxs),
      atlasSectionInChart, hpoint, (L.chart j).left_inv hxs]
    rfl
  -- Every original frame sees the same pointwise limit; no fiber topology is replaced.
  have hpoint (i : A.Index) (x : M) (hxi : x ∈ (A.chart i).baseSet) :
      Filter.Tendsto (fun a ↦ (A.chart i ⟨x, (u a).val x⟩).2) Filter.atTop
        (nhds ((A.chart i ⟨x, s x⟩).2)) := by
    let j := pick x
    have hx := hpick_valid x
    let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
    let T := ((A.frameLinearEquiv i x hxi).toLinearMap.comp
      (A.frameLinearEquiv (L.frameIndex j) x hx.2).symm.toLinearMap).toContinuousLinearMap
    let ψ : EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j))) → Fin (A.rank i) → ℂ :=
      fun z ↦ T ((L.cutoff j x : ℂ)⁻¹ • e z)
    have hψ : Continuous ψ := T.continuous.comp (e.continuous.const_smul (L.cutoff j x : ℂ)⁻¹)
    have hh := (hψ.tendsto _).comp ((hv j).2.2 (L.chart j x))
    have hχ : (L.cutoff j x : ℂ) ≠ 0 := by exact_mod_cast hpick x
    have heval (a : ℕ) : ψ (L.localizedCkFunction k j (u a) (L.chart j x)) =
        (A.chart i ⟨x, (u a).val x⟩).2 := by
      dsimp only [ψ]
      rw [hvalue j x hx.1 hx.2, e.map_smul, e.apply_symm_apply, smul_smul,
        inv_mul_cancel₀ hχ, one_smul]
      change (A.frameLinearEquiv i x hxi)
        ((A.frameLinearEquiv (L.frameIndex j) x hx.2).symm
          ((A.frameLinearEquiv (L.frameIndex j) x hx.2) ((u a).val x))) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    have ht : ψ (v j (L.chart j x)) = (A.chart i ⟨x, s x⟩).2 := rfl
    rw [ht] at hh
    convert hh using 1
    funext a
    exact (heval a).symm
  have hrecover (j : Fin L.size) (x : M) (hxs : x ∈ (L.chart j).source)
      (hxf : x ∈ (A.chart (L.frameIndex j)).baseSet) (hχ : L.cutoff j x ≠ 0) :
      (A.frameLinearEquiv (L.frameIndex j) x hxf) (s x) =
        (L.cutoff j x : ℂ)⁻¹ •
          (EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ) (v j (L.chart j x)) := by
    let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
    have hcoord := (e.symm.continuous.tendsto _).comp (hpoint (L.frameIndex j) x hxf)
    have hscaled := hcoord.const_smul (L.cutoff j x : ℂ)
    have hlocal : Filter.Tendsto
        (fun a ↦ L.localizedCkFunction k j (u a) (L.chart j x)) Filter.atTop
        (nhds ((L.cutoff j x : ℂ) •
          e.symm ((A.frameLinearEquiv (L.frameIndex j) x hxf) (s x)))) := by
      convert hscaled using 1
      · funext a
        exact hvalue j x hxs hxf (u a)
      · rfl
    have heq := tendsto_nhds_unique ((hv j).2.2 (L.chart j x)) hlocal
    have hχ' : (L.cutoff j x : ℂ) ≠ 0 := by exact_mod_cast hχ
    rw [heq, map_smul, e.apply_symm_apply, smul_smul, inv_mul_cancel₀ hχ', one_smul]
  -- On a nonzero-weight neighborhood, the limit is expressed in one fixed original frame.
  have hs : A.IsContMDiffSection k s := by
    intro i x hxi
    let j := pick x
    have hj := hpick x
    have hx := L.support_subset j (subset_tsupport _ hj)
    have hchart := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) (L.chart_mem_atlas j)) hx.1
    let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
    have hvector := (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contMDiffAt
      ((hv j).1.comp_contMDiffAt (hchart.of_le (by simp)))
    have hscalar : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) k
        (fun y ↦ (L.cutoff j y : ℂ)) x :=
      (Complex.ofRealCLM.contDiff (n := k)).comp_contMDiffAt
        ((L.smooth_cutoff j).contMDiffAt.of_le (by simp))
    have hχ : (L.cutoff j x : ℂ) ≠ 0 := by exact_mod_cast hj
    have hinv := (contDiffAt_inv ℝ hχ).comp_contMDiffAt
      (f := fun y : M ↦ (L.cutoff j y : ℂ)) (x := x) hscalar
    have hsum : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, Fin (A.rank i) → ℂ) k
        (fun y ↦ ∑ a : Fin (A.rank (L.frameIndex j)),
          (e (v j (L.chart j y))) a •
            (A.chart i ((A.chart (L.frameIndex j)).toPartialEquiv.symm
              (y, Pi.single a 1))).2) x := by
      apply contMDiffAt_finsetSum
      intro a _
      have hcoeff := contMDiffAt_pi_space.mp hvector a
      have hcolumn := (A.contMDiffOn_coordChange (L.frameIndex j) i a).contMDiffAt
        (((A.chart (L.frameIndex j)).open_baseSet.inter
          (A.chart i).open_baseSet).mem_nhds ⟨hx.2, hxi⟩)
      exact (contDiff_smul (𝕜 := ℝ) (n := k)).comp_contMDiffAt
        (hcoeff.prodMk_space (hcolumn.of_le (by simp)))
    have hlocal := (contDiff_smul (𝕜 := ℝ) (n := k)).comp_contMDiffAt
      (hinv.prodMk_space hsum)
    apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
    have hopen : IsOpen {y : M | L.cutoff j y ≠ 0} :=
      isOpen_ne_fun (L.smooth_cutoff j).continuous continuous_const
    filter_upwards [(L.chart j).open_source.mem_nhds hx.1,
      (A.chart (L.frameIndex j)).open_baseSet.mem_nhds hx.2,
      (A.chart i).open_baseSet.mem_nhds hxi, hopen.mem_nhds hj] with y hyc hyj hyi hyχ
    let T := (A.frameLinearEquiv i y hyi).toLinearMap.comp
      (A.frameLinearEquiv (L.frameIndex j) y hyj).symm.toLinearMap
    have hexpand := congrArg T ((Pi.basisFun ℂ (Fin (A.rank (L.frameIndex j)))).sum_repr
      (e (v j (L.chart j y))))
    simp [T, map_sum, map_smul] at hexpand
    have hcolumn (a : Fin (A.rank (L.frameIndex j))) :
        (A.frameLinearEquiv i y hyi)
            ((A.frameLinearEquiv (L.frameIndex j) y hyj).symm (Pi.single a 1)) =
          (A.chart i ((A.chart (L.frameIndex j)).toPartialEquiv.symm (y, Pi.single a 1))).2 := by
      change (A.chart i ⟨y, cast (congrArg E
        ((A.chart (L.frameIndex j)).proj_symm_apply' hyj))
          ((A.chart (L.frameIndex j)).toOpenPartialHomeomorph.symm (y, Pi.single a 1)).2⟩).2 = _
      have hpoint' := TotalSpace.mk_cast (F := Unit) (E := E)
        ((A.chart (L.frameIndex j)).proj_symm_apply' (x := Pi.single a 1) hyj)
        ((A.chart (L.frameIndex j)).toOpenPartialHomeomorph.symm (y, Pi.single a 1)).2
      exact congrArg (fun p : TotalSpace Unit E ↦ (A.chart i p).2) hpoint'
    simp only [hcolumn] at hexpand
    change (A.frameLinearEquiv i y hyi) (s y) = _
    rw [← (A.frameLinearEquiv (L.frameIndex j) y hyj).symm_apply_apply (s y),
      hrecover j y hyc hyj hyχ, map_smul, map_smul]
    congr 1
    exact hexpand.symm
  let w : L.CkSectionSpace k := ⟨s, hs⟩
  -- Identify the same localized functions, then all their original derivative coordinates.
  have hloc (j : Fin L.size) : L.localizedCkFunction k j w = v j := by
    funext z
    by_cases hz : z ∈ (L.chart j).target
    · by_cases hχ : L.cutoff j ((L.chart j).symm z) = 0
      · have hzero (a : ℕ) : L.localizedCkFunction k j (u a) z = 0 := by
          simp [localizedCkFunction, hz, hχ]
        have hzero_lim : v j z = 0 := tendsto_nhds_unique ((hv j).2.2 z)
          (by simpa only [hzero] using (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ ↦ (0 : EuclideanSpace ℂ
              (Fin (A.rank (L.frameIndex j)))) ) Filter.atTop (nhds 0)))
        simp [localizedCkFunction, hz, hχ, hzero_lim]
      · have hxf := (L.support_subset j (subset_tsupport _ hχ)).2
        have heq := hvalue j ((L.chart j).symm z) ((L.chart j).map_target hz) hxf w
        have hχ' : (L.cutoff j ((L.chart j).symm z) : ℂ) ≠ 0 := by exact_mod_cast hχ
        rw [hrecover j _ ((L.chart j).map_target hz) hxf hχ, map_smul,
          ContinuousLinearEquiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ hχ', one_smul] at heq
        simpa only [(L.chart j).right_inv hz] using heq
    · have hzero (a : ℕ) : L.localizedCkFunction k j (u a) z = 0 := by
        simp [localizedCkFunction, hz]
      have hzero_lim : v j z = 0 := tendsto_nhds_unique ((hv j).2.2 z)
        (by simpa only [hzero] using (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ ↦ (0 : EuclideanSpace ℂ
            (Fin (A.rank (L.frameIndex j))))) Filter.atTop (nhds 0)))
      simp [localizedCkFunction, hz, hzero_lim]
  have hF_eq : L.ckDerivativeCoordinates k w = F := by
    funext j i
    apply DFunLike.ext
    intro z
    change iteratedFDeriv ℝ i.val (L.localizedCkFunction k j w) z = F j i z
    rw [hloc j]
    exact congrFun ((hv j).2.1 i) z
  refine ⟨w, hiso.tendsto_nhds_iff.mpr ?_⟩
  rwa [hF_eq]

attribute [instance] completeSpace_ckSectionSpace

/-- The actual smooth section included as a finite-order section, with unchanged values. -/
def smoothToCk (k : ℕ) : A.smoothSections →ₗ[ℂ] L.CkSectionSpace k where
  toFun u := ⟨u.val, A.isContMDiffSection_of_isSmoothSection k u.val u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Two finite presentations give equivalent C^k norms on the same actual section space.
Swapping the two presentations supplies the reverse inequality. -/
theorem exists_ck_norm_comparison (K : AtlasBundlePresentation A) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : L.CkSectionSpace k,
      ‖(show K.CkSectionSpace k from u)‖ ≤ C * ‖u‖ := by
  classical
  -- Each specified norm controls point evaluation in every original finite-dimensional frame.
  have hpoint (P : AtlasBundlePresentation A) (a : ℕ → P.CkSectionSpace k)
      (u : P.CkSectionSpace k) (ha : Filter.Tendsto a Filter.atTop (nhds u))
      (i : A.Index) (x : M) (hxi : x ∈ (A.chart i).baseSet) :
      Filter.Tendsto (fun b ↦ (A.chart i ⟨x, (a b).val x⟩).2) Filter.atTop
        (nhds ((A.chart i ⟨x, u.val x⟩).2)) := by
    have hchoose : ∃ j : Fin P.size, P.cutoff j x ≠ 0 := by
      by_contra! h
      have hsum := P.sum_cutoff x
      simp only [h, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨j, hj⟩ := hchoose
    have hx := P.support_subset j (subset_tsupport _ hj)
    have hiso : Isometry (P.ckDerivativeCoordinates k) := by
      intro v w
      rfl
    have hcoords := (hiso.continuous.tendsto u).comp ha
    have hbounded := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hcoords j))
      ⟨0, Nat.zero_lt_succ k⟩
    have hjet := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hbounded
    let e₀ := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℂ (Fin (A.rank (P.frameIndex j))))
    have hvalues : Filter.Tendsto
        (fun b ↦ P.localizedCkFunction k j (a b) (P.chart j x)) Filter.atTop
        (nhds (P.localizedCkFunction k j u (P.chart j x))) := by
      have h := (e₀.continuous.tendsto _).comp (hjet.tendsto_at (P.chart j x))
      simpa only [Function.comp_def, e₀, ckDerivativeCoordinates,
        BoundedContinuousFunction.coe_mk, continuousMultilinearCurryFin0_apply,
        iteratedFDeriv_zero_apply] using h
    let e := EuclideanSpace.equiv (Fin (A.rank (P.frameIndex j))) ℂ
    let T := ((A.frameLinearEquiv i x hxi).toLinearMap.comp
      (A.frameLinearEquiv (P.frameIndex j) x hx.2).symm.toLinearMap).toContinuousLinearMap
    let ψ : EuclideanSpace ℂ (Fin (A.rank (P.frameIndex j))) → Fin (A.rank i) → ℂ :=
      fun z ↦ T ((P.cutoff j x : ℂ)⁻¹ • e z)
    have hψ : Continuous ψ :=
      T.continuous.comp (e.continuous.const_smul (P.cutoff j x : ℂ)⁻¹)
    have hχ : (P.cutoff j x : ℂ) ≠ 0 := by exact_mod_cast hj
    have heval (w : P.CkSectionSpace k) : ψ (P.localizedCkFunction k j w (P.chart j x)) =
        (A.chart i ⟨x, w.val x⟩).2 := by
      have hpoint' : (⟨(P.chart j).symm (P.chart j x),
          w.val ((P.chart j).symm (P.chart j x))⟩ : TotalSpace Unit E) = ⟨x, w.val x⟩ :=
        congrArg (fun y ↦ (⟨y, w.val y⟩ : TotalSpace Unit E)) ((P.chart j).left_inv hx.1)
      simp only [ψ, localizedCkFunction, ite_eq_left ((P.chart j).map_source hx.1),
        atlasSectionInChart, hpoint', (P.chart j).left_inv hx.1]
      rw [e.map_smul, e.apply_symm_apply, smul_smul, inv_mul_cancel₀ hχ, one_smul]
      change (A.frameLinearEquiv i x hxi)
        ((A.frameLinearEquiv (P.frameIndex j) x hx.2).symm
          ((A.frameLinearEquiv (P.frameIndex j) x hx.2) (w.val x))) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    have hh := (hψ.tendsto _).comp hvalues
    simpa only [Function.comp_def, heval] using hh
  -- The graph is closed because convergence in either norm preserves those same fiber values.
  let I : L.CkSectionSpace k →ₗ[ℂ] K.CkSectionSpace k :=
    { toFun := fun u ↦ u
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hcont : Continuous I := I.continuous_of_seq_closed_graph (by
    intro a u v hau hav
    apply Subtype.ext
    funext x
    obtain ⟨i, hi⟩ := A.covers x
    apply (A.frameLinearEquiv i x hi).injective
    exact tendsto_nhds_unique (hpoint K (I ∘ a) v hav i x hi) (hpoint L a u hau i x hi))
  let T : L.CkSectionSpace k →L[ℂ] K.CkSectionSpace k :=
    { toLinearMap := I, cont := hcont }
  -- A positive enlargement of the operator norm also covers zero section spaces.
  refine ⟨‖T‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg T) zero_lt_one, ?_⟩
  intro u
  calc
    ‖(show K.CkSectionSpace k from u)‖ = ‖T u‖ := rfl
    _ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
    _ ≤ (‖T‖ + 1) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg u)

end AtlasBundlePresentation

end AtiyahSinger
