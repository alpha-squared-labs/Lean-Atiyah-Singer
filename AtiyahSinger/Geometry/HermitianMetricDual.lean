/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Geometry.DualSections
public import AtiyahSinger.Geometry.HermitianMetricComparison

/-!
# Metric duality with explicit Hermitian forms

Public module ID: M1273.

D02/A07: the complex-linear dual is unchanged. A chosen metric identifies vectors
with covectors conjugate-linearly, using the original fiber topology. Smoothness
and bijectivity are separate statements; no norm instance is replaced.
Sources: SG III.5 (5.1), pp.194–195; HU Ch.3 §9. The explicit-metric comparisons
are project deductions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

namespace SmoothHermitianMetric

variable (h : SmoothHermitianMetric (n := n) (r := r) E)

/-- The second slot of the metric is a unique continuous complex-linear functional. -/
theorem existsUnique_dual (x : M) (u : E x) :
    ∃! α : DualBundle E x, ∀ v : E x, α v = h.pairing x u v := by
  /- Sesquilinearity makes the second slot linear. Its continuity for the
  original fiber topology follows from continuous_pairing. These properties
  construct the functional, and its values on all v determine it uniquely. -/
  -- Keep the original fiber topology when bundling the linear second slot.
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  let L : E x →ₗ[ℂ] ℂ := {
    toFun := h.pairing x u
    map_add' v w := InnerProductSpace.Core.inner_add_right u v w
    map_smul' c v := InnerProductSpace.Core.inner_smul_right u v (r := c) }
  let α : DualBundle E x :=
    { L with cont := (h.continuous_pairing x).comp (continuous_const.prodMk continuous_id) }
  refine ⟨α, fun _ ↦ rfl, ?_⟩
  intro β hβ
  ext v
  exact hβ v

/-- The actual covector v ↦ h(u,v), with the original operator-norm topology. -/
def dual (x : M) (u : E x) : DualBundle E x :=
  Classical.choose (h.existsUnique_dual x u).exists

/-- Metric dual evaluation is exactly the chosen fiber form. -/
theorem dual_apply (x : M) (u v : E x) : h.dual x u v = h.pairing x u v := by
  /- Use the specified evaluation of the chosen unique functional. This fixes
  the conjugate-linear first slot and leaves the target dual complex-linear. -/
  exact (Classical.choose_spec (h.existsUnique_dual x u).exists) v

/-- The metric dual map is additive. -/
theorem dual_add (x : M) (u v : E x) : h.dual x (u + v) = h.dual x u + h.dual x v := by
  /- Evaluate both covectors on an arbitrary vector and use additivity of
  the first slot. Extensionality of continuous linear maps gives equality. -/
  -- The same pairing values determine the original continuous covector.
  ext w
  rw [add_apply, h.dual_apply, h.dual_apply, h.dual_apply]
  exact (h.toCore x).add_left u v w

/-- Scalar multiplication in the source is conjugated. -/
theorem dual_smul (x : M) (c : ℂ) (u : E x) :
    h.dual x (c • u) = conj c • h.dual x u := by
  /- Evaluate on a test vector and apply conjugate-linearity in the first
  slot. This is an antilinear Riesz map, not a complex-linear identification. -/
  ext v
  rw [smul_apply, h.dual_apply, h.dual_apply]
  exact (h.toCore x).smul_left u v c

/-- Finite rank and positivity make fiber metric duality bijective. -/
theorem bijective_dual (x : M) : Function.Bijective (h.dual x) := by
  /- Positivity gives injectivity. For surjectivity, apply finite-dimensional
  Riesz representation with the norm of the specified positive form locally.
  Rebundle only the given functional's algebraic map for that temporary norm,
  then identify its values with the original continuous dual. The statement
  and the selected dual map retain the original norm and topology. -/
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    constructor
    · -- Positivity separates vectors without changing the given norm.
      intro u v huv
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      have he (w : E x) : h.pairing x u w = h.pairing x v w := by
        exact (h.dual_apply x u w).symm.trans
          ((congrArg (fun α : DualBundle E x ↦ α w) huv).trans (h.dual_apply x v w))
      have hz : (h.toCore x).inner (u - v) (u - v) = 0 := by
        rw [InnerProductSpace.Core.inner_sub_left]
        exact sub_eq_zero.mpr (he (u - v))
      exact sub_eq_zero.mp ((h.toCore x).definite _ hz)
    · intro α
      -- Use Riesz in a local metric norm, retaining α's algebraic map and the original dual.
      let core := h.toCore x
      let D := h.dual x
      have hD (u v : E x) : D u v = core.inner u v := h.dual_apply x u v
      let αlin : E x →ₗ[ℂ] ℂ := α.toLinearMap
      let moduleE : Module ℂ (E x) := inferInstance
      let : NormedAddCommGroup (E x) := core.toNormedAddCommGroup
      let : Module ℂ (E x) := moduleE
      let : InnerProductSpace ℂ (E x) := InnerProductSpace.ofCore core.toCore
      let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
      let β : StrongDual ℂ (E x) := αlin.toContinuousLinearMap
      let u := (InnerProductSpace.toDual ℂ (E x)).symm β
      refine ⟨u, ?_⟩
      change D u = α
      apply DFunLike.ext
      intro v
      exact (hD u v).trans (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ))

/-- The conjugate-linear fiber identification with the actual continuous dual. -/
def dualEquiv (x : M) : E x ≃ₗ⋆[ℂ] DualBundle E x :=
  LinearEquiv.ofBijective
    { toFun := h.dual x
      map_add' := h.dual_add x
      map_smul' := h.dual_smul x }
    (h.bijective_dual x)

/-- The packaged fiber equivalence keeps the given covector values. -/
theorem dualEquiv_apply (x : M) (u v : E x) :
    h.dualEquiv x u v = h.pairing x u v := by
  /- The forward map of LinearEquiv.ofBijective is the specified dual map.
  Its evaluation is the metric pairing by the preceding construction formula. -/
  exact h.dual_apply x u v

/-- The inverse metric identification represents a covector by its exact pairing. -/
theorem pairing_dualEquiv_symm (x : M) (α : DualBundle E x) (v : E x) :
    h.pairing x ((h.dualEquiv x).symm α) v = α v := by
  /- Apply the forward evaluation formula to the inverse image of α, then
  cancel the equivalence and its inverse. No chosen basis remains in the result. -/
  -- Evaluate the inverse law on the same test vector.
  exact (h.dualEquiv_apply x ((h.dualEquiv x).symm α) v).symm.trans
    (congrArg (fun β : DualBundle E x ↦ β v) ((h.dualEquiv x).apply_symm_apply α))

/-- Changing the metric composes duality with the positive change in the first slot. -/
theorem dual_change (k : SmoothHermitianMetric (n := n) (r := r) E) (x : M) (u : E x) :
    k.dual x u = h.dual x (h.change k x u) := by
  /- Evaluate at v. The change operator is self-adjoint relative to h,
  so h(Bu,v)=k(u,v). Covector extensionality identifies the two functionals. -/
  ext v
  rw [k.dual_apply, h.dual_apply]
  exact (h.pairing_change_left k x u v).symm

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

set_option linter.unusedSectionVars false in
-- Retain the original manifold parameter of the public metric-dual interface.
/-- The metric dual of a smooth section is a smooth covector section. -/
theorem isSmoothDualSection_dual (u : smoothSections (n := n) (r := r) E) :
    IsSmoothDualSection (n := n) (r := r) E (fun x ↦ h.dual x (u.val x)) := by
  /- In a frame, each dual coefficient is a finite sum of conjugated
  section coordinates times smooth Gram entries. This is real-smooth and
  satisfies exactly the existing metric-free dual-section predicate. -/
  classical
  intro e he
  let := he
  let P := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  -- Each coefficient is a finite sum of conjugate primal coordinates and Gram entries.
  have hcoord (i : Fin r) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ (e ⟨x, u.val x⟩).2 i) e.baseSet :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ).contDiff.contMDiff
      |>.comp_contMDiffOn (u.property e he)
  have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, Fin r → ℂ) ∞
      (fun x j ↦ ∑ i, conj ((e ⟨x, u.val x⟩).2 i) * h.gramMatrix e x i j) e.baseSet := by
    apply contMDiffOn_pi_space.mpr
    intro j
    apply contMDiffOn_finsetSum
    intro i _
    have hconj := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn (hcoord i)
    have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) := contDiff_mul
    exact hmul.contMDiff.comp_contMDiffOn
      (hconj.prodMk_space (h.contMDiffOn_gram e i j))
  have hsmooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
      (fun x ↦ P.symm (fun j ↦ ∑ i, conj ((e ⟨x, u.val x⟩).2 i) *
        h.gramMatrix e x i j)) e.baseSet :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.contDiff.contMDiff
      |>.comp_contMDiffOn hsum
  -- The original pairing expansion identifies those coordinates with the actual dual map.
  apply hsmooth.congr
  intro x hx
  apply PiLp.ext
  intro j
  change h.dual x (u.val x) (e.symmL ℂ x (EuclideanSpace.single j 1)) = _
  rw [h.dual_apply, h.pairing_eq_gramMatrix e x hx]
  have hb : (e ⟨x, e.symmL ℂ x (EuclideanSpace.single j 1)⟩).2 =
      EuclideanSpace.single j 1 := by
    rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
    exact e.continuousLinearMapAt_symmL hx _
  simp [hb, P]

/-- Pointwise metric duality on actual smooth sections, conjugate-linear over ℂ. -/
def dualSections :
    smoothSections (n := n) (r := r) E →ₗ⋆[ℂ] smoothDualSections (n := n) (r := r) E where
  toFun := fun u ↦ ⟨fun x ↦ h.dual x (u.val x), h.isSmoothDualSection_dual u⟩
  map_add' := fun u v ↦ Subtype.ext (funext (fun x ↦ h.dual_add x (u.val x) (v.val x)))
  map_smul' := fun c u ↦ Subtype.ext (funext (fun x ↦ h.dual_smul x c (u.val x)))

/-- Smooth metric duality is bijective without a compactness assumption. -/
theorem bijective_dualSections : Function.Bijective h.dualSections := by
  open scoped Matrix.Norms.Elementwise in
  /- Invert the Gram matrix in each smooth frame and conjugate the dual
  coefficient vector. Matrix inversion is smooth on the invertible locus.
  Pointwise uniqueness glues these inverse sections and also gives injectivity. -/
  classical
  constructor
  · -- The original fiber metric duality separates values of the sections.
    intro u v huv
    apply Subtype.ext
    funext x
    apply (h.bijective_dual x).1
    exact congrArg (fun α : smoothDualSections (n := n) (r := r) E ↦ α.val x) huv
  · intro α
    let s (x : M) : E x := (h.dualEquiv x).symm (α.val x)
    have hs : IsSmoothSection (n := n) (r := r) E s := by
      intro e he
      let := he
      let V := EuclideanSpace ℂ (Fin r)
      let P := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
      -- Realize the original positive Gram matrix as an operator on the fixed frame model.
      let toOp : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] (V →L[ℂ] V) :=
        LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
      let toOpC : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (V →L[ℂ] V) :=
        LinearMap.toContinuousLinearMap (toOp.restrictScalars ℝ)
      let A (x : M) : V →L[ℂ] V := toOpC (h.gramMatrix e x)
      have hA : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞
          A e.baseSet := by
        apply toOpC.contDiff.contMDiff.comp_contMDiffOn
        apply contMDiffOn_pi_space.mpr
        intro i
        apply contMDiffOn_pi_space.mpr
        intro j
        exact h.contMDiffOn_gram e i j
      have hequiv (x : M) (hx : x ∈ e.baseSet) :
          ∃ H : V ≃L[ℂ] V, H.toContinuousLinearMap = A x := by
        have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr (h.isUnit_det_gramMatrix e x hx)
        let L := (LinearEquiv.ofBijective (h.gramMatrix e x).mulVecLin
          ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
            Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
        refine ⟨P.trans (L.trans P.symm), ?_⟩
        ext v i
        rfl
      -- Inversion is smooth on the invertible locus; no global norm bound is needed.
      have hinverse : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞
          (fun x ↦ (A x).inverse) e.baseSet := by
        intro x hx
        obtain ⟨H, hH⟩ := hequiv x hx
        have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (A x) := by
          rw [← hH]
          exact (contDiffAt_map_inverse H).restrict_scalars ℝ
        exact hi.contMDiffAt.comp_contMDiffWithinAt x (hA x hx)
      let b (x : M) : V := WithLp.toLp 2
        (fun i ↦ conj (dualSectionInFrame E e α.val x i))
      have hb : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ b e.baseSet := by
        apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.contDiff.contMDiff
          |>.comp_contMDiffOn
        apply contMDiffOn_pi_space.mpr
        intro i
        have hc := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ)
          |>.contDiff.contMDiff.comp_contMDiffOn (α.property e he)
        exact Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn hc
      have heval : ContDiff ℝ ∞ (fun z : (V →L[ℂ] V) × V ↦ z.1 z.2) :=
        (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
      have hcoordSmooth := heval.contMDiff.comp_contMDiffOn (hinverse.prodMk_space hb)
      -- Test the exact inverse pairing on each basis vector to recover H s = conjugate α.
      have hcoord (x : M) (hx : x ∈ e.baseSet) : A x (e ⟨x, s x⟩).2 = b x := by
        apply PiLp.ext
        intro i
        have htest := congrArg (starRingEnd ℂ)
          (h.pairing_dualEquiv_symm x (α.val x)
            (e.symmL ℂ x (EuclideanSpace.single i 1)))
        simp only [pairing, (h.toCore x).conj_inner_symm] at htest
        change h.pairing x (e.symmL ℂ x (EuclideanSpace.single i 1)) (s x) = _ at htest
        rw [h.pairing_eq_gramMatrix e x hx] at htest
        have hbase : (e ⟨x, e.symmL ℂ x (EuclideanSpace.single i 1)⟩).2 =
            EuclideanSpace.single i 1 := by
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact e.continuousLinearMapAt_symmL hx _
        change (∑ j, h.gramMatrix e x i j * (e ⟨x, s x⟩).2 j) =
          conj (α.val x (e.symmL ℂ x (EuclideanSpace.single i 1)))
        simpa [hbase] using htest
      apply hcoordSmooth.congr
      intro x hx
      obtain ⟨H, hH⟩ := hequiv x hx
      change (e ⟨x, s x⟩).2 = (A x).inverse (b x)
      rw [← hH, ContinuousLinearMap.inverse_equiv]
      apply H.injective
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
        ← hH] using hcoord x hx
    -- The fiber inverse gives the prescribed original covector section at every point.
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    funext x
    exact (h.dualEquiv x).apply_symm_apply (α.val x)

/-- The metric identification of the two actual smooth-section spaces. -/
def dualSectionsEquiv :
    smoothSections (n := n) (r := r) E ≃ₗ⋆[ℂ] smoothDualSections (n := n) (r := r) E :=
  LinearEquiv.ofBijective h.dualSections h.bijective_dualSections

/-- The section equivalence evaluates to the fiber form. -/
theorem dualSectionsEquiv_apply (u : smoothSections (n := n) (r := r) E) (x : M) (v : E x) :
    (h.dualSectionsEquiv u).val x v = h.pairing x (u.val x) v := by
  /- The section equivalence keeps the explicitly defined pointwise dual
  map. Apply dual_apply in the fiber to recover its exact metric value. -/
  exact h.dual_apply x (u.val x) v

/-- The inverse section equivalence solves the actual covector pairing equation. -/
theorem pairing_dualSectionsEquiv_symm (α : smoothDualSections (n := n) (r := r) E)
    (x : M) (v : E x) :
    h.pairing x ((h.dualSectionsEquiv.symm α).val x) v = α.val x v := by
  /- Evaluate the equivalence inverse law at x and v, then replace its
  forward evaluation by the metric pairing. Smoothness of the inverse is
  already part of the separately stated bijectivity argument. -/
  exact (h.dualSectionsEquiv_apply (h.dualSectionsEquiv.symm α) x v).symm.trans
    (congrArg (fun β : smoothDualSections (n := n) (r := r) E ↦ β.val x v)
      (h.dualSectionsEquiv.apply_symm_apply α))

/-- Section metric duality transforms by the specified positive multiplier. -/
theorem dualSectionsEquiv_change (k : SmoothHermitianMetric (n := n) (r := r) E)
    (u : smoothSections (n := n) (r := r) E) :
    k.dualSectionsEquiv u = h.dualSectionsEquiv (h.changeSections k u) := by
  /- Evaluate both smooth covector sections on every fiber vector. The
  fiber dual_change identity gives equality, and subtype extensionality
  retains the same underlying covector section, not just its dimension. -/
  apply Subtype.ext
  funext x
  exact h.dual_change k x (u.val x)

/-- The bilinear dual integral becomes the explicit Hermitian integral. -/
theorem dualSectionPairing_dualSectionsEquiv [MeasurableSpace M] (μ : Measure M)
    (u v : smoothSections (n := n) (r := r) E) :
    smoothDualSectionPairing E μ (h.dualSectionsEquiv u) v = h.sectionPairing μ u v := by
  /- Both integrands agree pointwise by dualSectionsEquiv_apply. Integral
  congruence proves this identity even before imposing integrability; separate
  compact-base theorems justify the later nondegeneracy arguments. -/
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ h.dualSectionsEquiv_apply u x (v.val x))

end SmoothHermitianMetric

end AtiyahSinger
