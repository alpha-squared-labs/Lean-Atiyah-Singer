/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DualBundle

import AtiyahSinger.Geometry.CompactParameterIntegral
import AtiyahSinger.Geometry.HermitianMetricDual

/-!
# Smooth bundle kernels and their actual integral operators

Public module ID: M1406.

D05/A05. A kernel is an actual family K(x,y): E_y -> F_x, smooth over the real
product manifold in every pair of complex bundle frames. A positive smooth measure
trivializes the density factor in the integration variable y. No Hermitian metric
is required as input. The integral-operator conclusions assume a compact
Hausdorff second-countable smooth base and smooth source and target bundles;
the integral then acts on their actual smooth sections.

Sources: Taylor, Pseudodifferential Operators II.2, pp.39–40, kernel formula (2.6);
Spin Geometry III.3.6 and III.5, p.192. This module only treats everywhere smooth
kernels. It does not assert the Schwartz kernel theorem or construct general PDOs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- The kernel matrix in the output frame f at x and the input frame e at y. -/
def kernelInFrames
    (K : ∀ x y : M, E y →L[ℂ] F x)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] (z : M × M) :
    EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
  (f.continuousLinearMapAt ℂ z.1).comp ((K z.1 z.2).comp (e.symmL ℂ z.2))

/-- Joint real smoothness of the actual kernel in all pairs of bundle frames. -/
def IsSmoothKernel (K : ∀ x y : M, E y →L[ℂ] F x) : Prop :=
  ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f],
    ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
      (kernelInFrames E F K e f) (f.baseSet ×ˢ e.baseSet)

/-- A fiber-map family with joint real smoothness in the supplied bundle frames. -/
structure SmoothKernel where
  /-- The genuine fiber map, with the output at x and input at y. -/
  toFun : ∀ x y : M, E y →L[ℂ] F x
  /-- Joint smoothness on the product base, checked in complex-linear frames. -/
  isSmooth : IsSmoothKernel (n := n) (r := r) (q := q) E F toFun

namespace SmoothKernel

variable {E F} (K : SmoothKernel (n := n) (r := r) (q := q) E F)

/-- Evaluating the output against a covector leaves a smooth dual section in the input variable. -/
theorem isSmoothDualSection_row (x : M) (α : DualBundle F x) :
    IsSmoothDualSection (n := n) (r := r) E (fun y ↦ α.comp (K.toFun x y)) := by
  /- Fix an output frame whose base contains x and an arbitrary input frame.
  Joint smoothness restricts to the slice with first coordinate x. Evaluating the
  smooth kernel matrix against the fixed covector in that output frame is a fixed
  complex-linear functional, hence real-smooth. These are exactly the dual coefficients. -/
  classical
  intro e he
  let := he
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have hx : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
  -- Restrict the original joint matrix to this fixed output point.
  have hslice : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
      (fun y ↦ kernelInFrames E F K.toFun e f (x, y)) e.baseSet :=
    (K.isSmooth e f).comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun y hy ↦ ⟨hx, hy⟩)
  -- Compose with the same inverse output frame and take the original dual coefficients.
  let a := α.comp (f.symmL ℂ x)
  let L := (dualModelEquiv r).toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace ℂ (Fin q)) ℂ) a)
  have hs := (L.restrictScalars ℝ).contMDiff.comp_contMDiffOn hslice
  apply hs.congr
  intro y hy
  ext i
  change α (K.toFun x y (e.symmL ℂ y (EuclideanSpace.single i 1))) =
    dualModelEquiv r (a.comp (kernelInFrames E F K.toFun e f (x, y))) i
  rw [dualModelEquiv_apply]
  change α (K.toFun x y (e.symmL ℂ y (EuclideanSpace.single i 1))) =
    α (f.symmL ℂ x (f.continuousLinearMapAt ℂ x
      (K.toFun x y (e.symmL ℂ y (EuclideanSpace.single i 1)))))
  rw [f.symmL_continuousLinearMapAt hx]

/-- The actual smooth covector row y ↦ α ∘ K(x,y), without a metric identification. -/
def dualRow (x : M) (α : DualBundle F x) : smoothDualSections (n := n) (r := r) E :=
  ⟨fun y ↦ α.comp (K.toFun x y), K.isSmoothDualSection_row x α⟩

/-- A covector row evaluates by applying the kernel and then the output covector. -/
theorem dualRow_apply (x y : M) (α : DualBundle F x) (v : E y) :
    (K.dualRow x α).val y v = α (K.toFun x y v) := by
  /- Unfold the row section and continuous-linear-map composition. The equality
  is at the actual fiber values, with no frame choice or conjugation involved. -/
  rfl

variable [MeasurableSpace M] (μ : Measure M)

/-- Integrate in the input variable in the fixed output fiber.
Real scalars are restricted from the specified complex action. -/
def apply (u : smoothSections (n := n) (r := r) E) (x : M) : F x := by
  letI : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
  exact ∫ y, K.toFun x y (u.val y) ∂μ

variable [BorelSpace M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothPositiveMeasure (n := n) μ]

set_option linter.unusedSectionVars false in
/-- Each kernel integrand is integrable in its fixed, finite-dimensional output fiber. -/
theorem integrable_apply (u : smoothSections (n := n) (r := r) E) (x : M) :
    Integrable (fun y ↦ K.toFun x y (u.val y)) μ := by
  /- In one fixed original frame at x, each output coordinate is evaluation of
  a smooth covector row on u. These evaluations are smooth, hence continuous.
  Reconstruct through that same finite-dimensional frame to obtain continuity
  in the original output fiber. Compactness and finite total measure then give
  Bochner integrability; no partition or new output-fiber norm is required. -/
  -- Test against the coordinates of one fixed original output frame.
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have hx : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
  let c := f.continuousLinearEquivAt ℂ x hx
  have hcoord : Continuous (fun y ↦
      ((EuclideanSpace.equiv (Fin q) ℂ) (c (K.toFun x y (u.val y))))) := by
    apply continuous_pi
    intro i
    let α := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).comp
      c.toContinuousLinearMap
    exact (contMDiff_dualSection_eval E (K.dualRow x α) u).continuous
  -- The same continuous inverse frame reconstructs the genuine fixed-fiber integrand.
  have hcont : Continuous (fun y ↦ K.toFun x y (u.val y)) := by
    have h := c.symm.continuous.comp
      ((EuclideanSpace.equiv (Fin q) ℂ).symm.continuous.comp hcoord)
    apply h.congr
    intro y
    exact c.symm_apply_apply (K.toFun x y (u.val y))
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral of a jointly smooth kernel against a smooth section is a smooth section. -/
theorem isSmoothSection_apply (u : smoothSections (n := n) (r := r) E) :
    IsSmoothSection (n := n) (r := q) F (K.apply μ u) := by
  /- In one output frame, evaluate the joint kernel matrix on the smooth input
  coordinates. Input frames are needed only locally to establish this joint
  smoothness. Compact-parameter differentiation then integrates over the whole
  original input manifold, and the same output frame commutes with the integral. -/
  classical
  intro f hf
  let := hf
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let Φ (p : M × M) : EuclideanSpace ℂ (Fin q) :=
    f.continuousLinearMapAt ℂ p.2 (K.toFun p.2 p.1 (u.val p.1))
  have hΦ : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞ Φ (Set.univ ×ˢ f.baseSet) := by
    intro p hp
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E p.1
    have he : p.1 ∈ e.baseSet := mem_baseSet_trivializationAt _ _ p.1
    -- Locally the genuine integrand is the kernel matrix applied to input coordinates.
    have hmatrix := (K.isSmooth e f).comp
      (contMDiffOn_snd.prodMk contMDiffOn_fst)
      (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ ⟨hz.2, hz.1⟩)
    have hu := (u.property e inferInstance).comp
      (contMDiffOn_fst (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
      (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ hz.1)
    have heval : ContDiff ℝ ∞ (fun z :
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
          EuclideanSpace ℂ (Fin r) ↦ z.1 z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
    have hlocal := heval.contMDiff.comp_contMDiffOn (hmatrix.prodMk_space hu)
    have hactual := hlocal.congr (f₁ := Φ) (by
      intro z hz
      change f.continuousLinearMapAt ℂ z.2 (K.toFun z.2 z.1 (u.val z.1)) =
        f.continuousLinearMapAt ℂ z.2 (K.toFun z.2 z.1
          (e.symmL ℂ z.1 ((e ⟨z.1, u.val z.1⟩).2)))
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.1,
        e.symmL_continuousLinearMapAt hz.1])
    exact (hactual.contMDiffAt ((e.open_baseSet.prod f.open_baseSet).mem_nhds
      ⟨he, hp.2⟩)).contMDiffWithinAt
  -- Move only the output variable into a finite-dimensional open coordinate domain.
  intro x hx
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  let s := c.target ∩ c.symm ⁻¹' f.baseSet
  have hs : IsOpen s := c.isOpen_inter_preimage_symm f.open_baseSet
  have hcx : c x ∈ s := ⟨c.map_source (mem_chart_source _ x), by
    simpa only [Set.mem_preimage, c, OpenPartialHomeomorph.left_inv _ (mem_chart_source _ x)]
      using hx⟩
  have hchart : ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
      (fun p : M × EuclideanSpace ℝ (Fin n) ↦ Φ (p.1, c.symm p.2)) (Set.univ ×ˢ s) := by
    apply hΦ.comp
      (contMDiffOn_fst.prodMk ((contMDiffOn_chart_symm
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (x := x)).comp contMDiffOn_snd
          (fun _ hp ↦ hp.2.1)))
    intro p hp
    exact ⟨Set.mem_univ _, hp.2.2⟩
  have hint : ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) ↦ ∫ y, Φ (y, c.symm z) ∂μ) s :=
    contDiffOn_integral_of_compact_manifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) μ hs hchart
  have hlocal := (hint.contMDiffOn.contMDiffAt (hs.mem_nhds hcx)).comp x
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x) (mem_chart_source _ x))
  -- The same original output frame commutes with the fixed-fiber Bochner integral.
  apply ContMDiffAt.contMDiffWithinAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x),
    f.open_baseSet.mem_nhds hx] with z hzc hzf
  change (f ⟨z, K.apply μ u z⟩).2 = ∫ y, Φ (y, c.symm (c z)) ∂μ
  rw [c.left_inv hzc]
  rw [← f.continuousLinearMapAt_apply_of_mem ℂ hzf]
  let : NormedSpace ℝ (F z) := NormedSpace.restrictScalars ℝ ℂ (F z)
  let : CompleteSpace (F z) := VectorBundle.completeSpace ℂ
    (EuclideanSpace ℂ (Fin q)) F z
  exact ((f.continuousLinearMapAt ℂ z).integral_comp_comm (K.integrable_apply μ u z)).symm

/-- Kernel integration is additive on the original smooth sections. -/
theorem apply_add (u v : smoothSections (n := n) (r := r) E) :
    K.apply μ (u + v) = K.apply μ u + K.apply μ v := by
  /- Each fiber map is additive. For every output point, split the Bochner integral
  using the integrability of both summands. Equality at all output points gives the result. -/
  funext x
  let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
  -- Integrability is established for these same original summands before splitting.
  change (∫ y, K.toFun x y (u.val y + v.val y) ∂μ) =
    (∫ y, K.toFun x y (u.val y) ∂μ) + ∫ y, K.toFun x y (v.val y) ∂μ
  simp_rw [map_add]
  exact integral_add (K.integrable_apply μ u x) (K.integrable_apply μ v x)

set_option linter.unusedSectionVars false in
/-- Kernel integration is complex-linear, even though smoothness is over the real base. -/
theorem apply_smul (c : ℂ) (u : smoothSections (n := n) (r := r) E) :
    K.apply μ (c • u) = c • K.apply μ u := by
  /- Complex scalar multiplication commutes with each original fiber map and
  with the totalized Bochner integral. The restricted real scalar structure
  used to define that integral is compatible with the complex action. -/
  funext x
  let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
  -- The complex scalar acts through the original continuous linear fiber map.
  change (∫ y, K.toFun x y (c • u.val y) ∂μ) =
    c • ∫ y, K.toFun x y (u.val y) ∂μ
  simp_rw [map_smul]
  exact integral_smul c _

/-- The actual integral operator on smooth sections, with its smoothness and linearity packaged. -/
def toLinearMap :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F where
  toFun u := ⟨K.apply μ u, K.isSmoothSection_apply μ u⟩
  map_add' u v := Subtype.ext (K.apply_add μ u v)
  map_smul' c u := Subtype.ext (K.apply_smul μ c u)

/-- The packaged section operator retains the pointwise integral formula. -/
theorem toLinearMap_apply (u : smoothSections (n := n) (r := r) E) (x : M) :
    (K.toLinearMap μ u).val x = K.apply μ u x := by
  /- The section-valued linear map was packaged with this exact integral as its
  underlying section. The smoothness and linearity fields do not alter its values. -/
  rfl

/-- Smooth test sections determine every smooth kernel uniquely for the fixed positive density. -/
theorem toLinearMap_injective :
    Function.Injective
      (fun L : SmoothKernel (n := n) (r := r) (q := q) E F ↦ L.toLinearMap μ) := by
  /- At a fixed output point, equal operators give equal integral pairings for
  every covector row. Use an auxiliary smooth Hermitian metric only to select the
  smooth section dual to the difference row. Positivity of the original density
  forces that section, hence the row, to vanish. Original frame covectors then
  separate the output vectors; the kernel itself never acquires a new metric. -/
  classical
  intro A B hAB
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) E
  have hrow (x : M) (α : DualBundle F x) (y : M) (v : E y) :
      α (A.toFun x y v) = α (B.toFun x y v) := by
    let β := A.dualRow x α - B.dualRow x α
    -- Move the very same covector through each original fixed-fiber integral.
    have hpair (L : SmoothKernel (n := n) (r := r) (q := q) E F)
        (u : smoothSections (n := n) (r := r) E) :
        α (L.apply μ u x) = smoothDualSectionPairing E μ (L.dualRow x α) u := by
      let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
      let : CompleteSpace (F x) := VectorBundle.completeSpace ℂ
        (EuclideanSpace ℂ (Fin q)) F x
      exact (α.integral_comp_comm (L.integrable_apply μ u x)).symm
    have hzero (u : smoothSections (n := n) (r := r) E) :
        smoothDualSectionPairing E μ β u = 0 := by
      change (∫ z, (A.dualRow x α).val z (u.val z) -
        (B.dualRow x α).val z (u.val z) ∂μ) = 0
      rw [integral_sub (integrable_dualSection_eval E μ (A.dualRow x α) u)
        (integrable_dualSection_eval E μ (B.dualRow x α) u)]
      change smoothDualSectionPairing E μ (A.dualRow x α) u -
        smoothDualSectionPairing E μ (B.dualRow x α) u = 0
      rw [← hpair A u, ← hpair B u]
      apply sub_eq_zero.mpr
      exact congrArg α (congrArg
        (fun T : smoothSections (n := n) (r := r) E →ₗ[ℂ]
          smoothSections (n := n) (r := q) F ↦ (T u).val x) hAB)
    -- The dual metric chooses a legitimate smooth test section for this difference row.
    let w := h.dualSectionsEquiv.symm β
    have hwβ : h.dualSectionsEquiv w = β := h.dualSectionsEquiv.apply_symm_apply β
    have hnorm : h.sectionPairing μ w w = 0 := by
      rw [← h.dualSectionPairing_dualSectionsEquiv μ w w, hwβ]
      exact hzero w
    have hw : w = 0 := (h.sectionPairing_self_eq_zero_iff μ w).mp hnorm
    have hβ : β = 0 := by
      rw [← hwβ, hw, map_zero]
    have heval := congrArg
      (fun γ : smoothDualSections (n := n) (r := r) E ↦ γ.val y v) hβ
    change α (A.toFun x y v) - α (B.toFun x y v) = 0 at heval
    exact sub_eq_zero.mp heval
  -- Coordinates of one original output frame separate the actual output fiber.
  have hfun : A.toFun = B.toFun := by
    funext x y
    apply ContinuousLinearMap.ext
    intro v
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hx : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
    let c := f.continuousLinearEquivAt ℂ x hx
    apply c.injective
    apply PiLp.ext
    intro i
    exact hrow x ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).comp
      c.toContinuousLinearMap) y v
  cases A
  cases B
  cases hfun
  rfl

/-- A kernel integral paired with an output covector is the existing metric-free section pairing. -/
theorem dual_apply (u : smoothSections (n := n) (r := r) E)
    (x : M) (α : DualBundle F x) :
    α (K.apply μ u x) = smoothDualSectionPairing E μ (K.dualRow x α) u := by
  /- Move the fixed continuous linear functional α through the integrable
  fiber-valued Bochner integral. The resulting scalar integrand is the evaluation
  of the actual covector row on u. This is the previously defined bilinear pairing. -/
  let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
  let : CompleteSpace (F x) := VectorBundle.completeSpace ℂ
    (EuclideanSpace ℂ (Fin q)) F x
  -- Move this output covector through the integral of the same actual kernel section.
  exact (α.integral_comp_comm (K.integrable_apply μ u x)).symm

end SmoothKernel

end AtiyahSinger
