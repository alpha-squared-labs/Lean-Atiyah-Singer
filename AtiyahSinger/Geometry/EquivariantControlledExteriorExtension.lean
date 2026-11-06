/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantExteriorSmoothBundleMap

/-!
# Equivariant exterior extension inside a prescribed support window

Public module ID: M1181.

A specified invariant smooth cutoff extends an exterior bundle map by zero on
its original smooth bundles. The exact cutoff formula retains the chosen window;
no new compact exception is chosen by the extension. This relative supplement
to SG III.13.4 is needed when both compact environments must retain one common
open source throughout smoothing and quantization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G M] [ContinuousSMul G M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A prescribed invariant cutoff extends the same exterior map equivariantly by zero. -/
theorem exists_smooth_equivariant_extension_of_exterior_with_cutoff
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      EquivariantStructure G F)
    (U : Opens M) (hUi : ∀ (g : G) (x : M), g • x ∈ U ↔ x ∈ U)
    (a : ∀ x : U, E x.val →L[ℂ] F x.val)
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) (M := U)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E))
      (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F))
      (fun x ↦ (a x).toLinearMap))
    (haEq : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (g : G) (x : U) (v : E x.val),
        a ⟨g • x.val, (hUi g x.val).mpr x.property⟩ (σE.linearMap g x.val v) =
          σF.linearMap g x.val (a x v))
    (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (U : Set M))
    (hχinv : ∀ (g : G) (x : M), χ (g • x) = χ x) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ c : Hom E F,
      IsSmoothBundleMap (n := n) (r := r) (q := q) c.linearMap ∧
      c.IsEquivariant σE σF ∧
      (∀ (x : U) (v : E x.val), c.linearMap x.val v = (χ x.val : ℂ) • a x v) ∧
      ∀ x ∉ U, c.linearMap x = 0 := by
  classical
  let H := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let Z := EuclideanSpace ℂ (Fin q)
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let c (x : M) : E x →L[ℂ] F x :=
    if hx : x ∈ U then (χ x : ℂ) • a ⟨x, hx⟩ else 0
  -- Descend native pullback columns through the open-submanifold inclusion.
  have haLocal (e : Trivialization V (π V E)) [MemTrivializationAtlas e]
      (f : Trivialization Z (π Z F)) [MemTrivializationAtlas f]
      (j : Fin r) (x : M) (hx : x ∈ e.baseSet ∩ f.baseSet) (hxU : x ∈ U) :
      ContMDiffAt 𝓘(ℝ, H) 𝓘(ℝ, Z) ∞
        (fun y ↦ if hy : y ∈ U then
          (f ⟨y, a ⟨y, hy⟩ (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 else 0) x := by
    let x' : U := ⟨x, hxU⟩
    let : MemTrivializationAtlas (e.pullback i) := ⟨e, inferInstance, rfl⟩
    let : MemTrivializationAtlas (f.pullback i) := ⟨f, inferInstance, rfl⟩
    have hx' : x' ∈ (e.pullback i).baseSet ∩ (f.pullback i).baseSet := hx
    have hlocal := (ha (e.pullback i) (f.pullback i) j).contMDiffAt
      (((e.pullback i).open_baseSet.inter (f.pullback i).open_baseSet).mem_nhds hx')
    apply (contMDiffAt_subtype_iff (U := U) (x := x')).mp
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [((e.pullback i).open_baseSet.inter
      (f.pullback i).open_baseSet).mem_nhds hx'] with y hy
    have heq : (e.pullback i).symmL ℂ y (EuclideanSpace.single j 1) =
        e.symmL ℂ y.val (EuclideanSpace.single j 1) := by
      rw [(e.pullback i).symmL_apply (R := ℂ) hy.1]
      change (e.pullback i).symm y (EuclideanSpace.single j 1) =
        e.symmL ℂ (i y) (EuclideanSpace.single j 1)
      rw [e.symmL_apply (R := ℂ) hy.1, (e.pullback i).symm_apply hy.1]
      rfl
    erw [dite_eq_left y.property]
    change (f ⟨y.val, a y (e.symmL ℂ y.val (EuclideanSpace.single j 1))⟩).2 =
      (f ⟨y.val, a y ((e.pullback i).symmL ℂ y (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  have hc : IsSmoothBundleMap (n := n) (r := r) (q := q)
      (fun x ↦ (c x).toLinearMap) := by
    intro e he f hf j x hx
    let := he
    let := hf
    by_cases hxU : x ∈ U
    · -- Elsewhere the original columns are smooth, multiplied by the smooth scalar cutoff.
      have hscalar : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, ℂ) ∞
          (fun y ↦ (χ y : ℂ)) :=
        Complex.ofRealCLM.contMDiff.comp hχ
      have hmul : ContDiff ℝ ∞ (fun t : ℂ × Z ↦ t.1 • t.2) := contDiff_smul
      have hs := hmul.contMDiff.contMDiffAt.comp x
        (hscalar.contMDiffAt.prodMk_space (haLocal e f j x hx hxU))
      apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [U.isOpen.mem_nhds hxU, f.open_baseSet.mem_nhds hx.2] with y hyU hyf
      change (f ⟨y, c y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 =
        (χ y : ℂ) • (if hy : y ∈ U then
          (f ⟨y, a ⟨y, hy⟩ (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 else 0)
      have hcy : c y = ((χ y : ℂ) • a ⟨y, hyU⟩) := dite_eq_left hyU
      rw [hcy]
      erw [dite_eq_left hyU]
      exact (f.linearEquivAt ℂ y hyf).map_smul _ _
    · -- The cutoff kills the map on a neighborhood, including the boundary of its domain.
      have hxχ : x ∉ tsupport χ := fun hx ↦ hxU (hχsupport hx)
      have hχx : ∀ᶠ y in 𝓝 x, χ y = 0 := notMem_tsupport_iff_eventuallyEq.mp hxχ
      apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : Z))).congr_of_eventuallyEq
      filter_upwards [hχx, f.open_baseSet.mem_nhds hx.2] with y hχy hyf
      have hcy : c y = 0 := by
        dsimp only [c]
        split_ifs
        · rw [hχy, Complex.ofReal_zero, zero_smul]
        · rfl
      change (f ⟨y, c y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 = 0
      rw [hcy, zero_apply]
      exact (f.linearEquivAt ℂ y hyf).map_zero
  -- The original fiber formula gives equivariance without changing the support window.
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let d : Hom E F := ⟨fun x ↦ (c x).toLinearMap, hc.continuous_total⟩
  refine ⟨d, hc, ?_, ?_, ?_⟩
  · intro g x v
    by_cases hx : x ∈ U
    · have hgx : g • x ∈ U := (hUi g x).mpr hx
      change c (g • x) (σE.linearMap g x v) = σF.linearMap g x (c x v)
      simp only [c, dite_eq_left hx, dite_eq_left hgx, smul_apply,
        hχinv, map_smul]
      exact congrArg ((χ x : ℂ) • ·) (haEq g ⟨x, hx⟩ v)
    · have hgx : g • x ∉ U := fun h ↦ hx ((hUi g x).mp h)
      change c (g • x) (σE.linearMap g x v) = σF.linearMap g x (c x v)
      simp only [c, dite_eq_right hx, dite_eq_right hgx, zero_apply,
        map_zero]
  · intro x v
    change c x.val v = _
    rw [show c x.val = (χ x.val : ℂ) • a x from dite_eq_left x.property]
    rfl
  · intro x hx
    change (c x).toLinearMap = 0
    rw [show c x = 0 from dite_eq_right hx]
    rfl

end AtiyahSinger
