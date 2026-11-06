/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CkSections
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic

/-!
# Smooth evaluation of uniformly bounded derivative families

Public module ID: M0840.

Uniform bounds on the derivatives of a linear family turn pointwise regularity into
regularity for the operator norm. One additional derivative supplies continuity of
the highest operator-valued derivative. The application to Sobolev kernel reconstruction
uses this result for the two actual localized evaluation families, with all bounds
obtained from the original Sobolev embeddings. The finite-order localized Sobolev
evaluation theorem is used for the output bundle and the original induced input-dual
presentation. This is the standard derivative evaluation argument underlying the
smooth-kernel characterization; it does not assume a kernel representation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff

set_option maxHeartbeats 1200000 in
-- The induction changes the derivative target while retaining the same scalar structures.
/-- A linear family with uniform derivative bounds has a bounded C^k evaluation family. -/
theorem exists_contDiff_evaluation_of_uniform_derivative_bounds
    {X E F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F]
    (k : ℕ) (J : E →ₗ[ℂ] (X → F))
    (hJ : ∀ u, ContDiff ℝ (k + 1) (J u))
    (hbound : ∀ j : ℕ, j ≤ k + 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u x, ‖iteratedFDeriv ℝ j (J u) x‖ ≤ C * ‖u‖) :
    ∃ T : X → E →L[ℂ] F, (∀ x u, T x u = J u x) ∧ ContDiff ℝ k T := by
  /- Bound the evaluation maps first. Induct on the desired regularity, applying
  the same argument to the pointwise derivative family. A continuous operator-valued
  derivative gives a uniform first-order remainder by the mean value inequality;
  taking the supremum over unit inputs proves actual Fréchet differentiability. -/
  classical
  have regularity (k : ℕ) :
      ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
        [IsScalarTower ℝ ℂ F] (f : X → E →L[ℂ] F),
        (∀ u, ContDiff ℝ (k + 1) (fun x ↦ f x u)) →
        (∀ j : ℕ, j ≤ k + 1 → ∃ C : ℝ, 0 ≤ C ∧
          ∀ u x, ‖iteratedFDeriv ℝ j (fun y ↦ f y u) x‖ ≤ C * ‖u‖) →
        ContDiff ℝ k f := by
    induction k with
    | zero =>
      intro F _ _ _ _ f hf hb
      obtain ⟨C, hC, hCbound⟩ := hb 1 (by omega)
      have hnorm (x y : X) : ‖f y - f x‖ ≤ C * ‖y - x‖ := by
        apply (f y - f x).opNorm_le_bound (mul_nonneg hC (norm_nonneg _))
        intro u
        have h := Convex.norm_image_sub_le_of_norm_fderiv_le
          (s := Set.univ) (f := fun z ↦ f z u)
          (fun z _ ↦ (hf u).differentiable (by simp) z)
          (fun z _ ↦ by simpa only [norm_iteratedFDeriv_one] using hCbound u z)
          convex_univ (Set.mem_univ x) (Set.mem_univ y)
        change ‖f y u - f x u‖ ≤ _
        exact h.trans_eq (by ring)
      have hlip : LipschitzWith (Real.toNNReal C) f :=
        LipschitzWith.of_dist_le_mul (fun x y ↦ by
          rw [Real.coe_toNNReal C hC, dist_eq_norm, dist_eq_norm]
          exact hnorm y x)
      exact contDiff_zero.mpr hlip.continuous
    | succ k ih =>
      intro F _ _ _ _ f hf hb
      obtain ⟨C, hC, hCbound⟩ := hb 1 (by omega)
      -- Pointwise differentiation preserves complex linearity in the input.
      let d (x : X) : E →ₗ[ℂ] (X →L[ℝ] F) :=
        { toFun := fun u ↦ fderiv ℝ (fun y ↦ f y u) x
          map_add' := by
            intro u v
            simp only [map_add]
            exact fderiv_add ((hf u).differentiable (by simp) x)
              ((hf v).differentiable (by simp) x)
          map_smul' := by
            intro c u
            simp only [map_smul]
            exact fderiv_const_smul ((hf u).differentiable (by simp) x) c }
      have hdBound (x : X) (u : E) : ‖d x u‖ ≤ C * ‖u‖ := by
        change ‖fderiv ℝ (fun y ↦ f y u) x‖ ≤ C * ‖u‖
        simpa only [norm_iteratedFDeriv_one] using hCbound u x
      let D (x : X) : E →L[ℂ] (X →L[ℝ] F) := (d x).mkContinuous C (hdBound x)
      have hD : ContDiff ℝ k D := by
        apply ih
        · intro u
          change ContDiff ℝ (k + 1) (fderiv ℝ (fun x ↦ f x u))
          exact (contDiff_succ_iff_fderiv.mp (hf u)).2.2
        · intro j hj
          obtain ⟨Cj, hCj, hCjbound⟩ := hb (j + 1) (by omega)
          refine ⟨Cj, hCj, ?_⟩
          intro u x
          change ‖iteratedFDeriv ℝ j (fderiv ℝ (fun y ↦ f y u)) x‖ ≤ _
          rw [norm_iteratedFDeriv_fderiv]
          exact hCjbound u x
      -- Flip the real direction and complex input while preserving both linear structures.
      let flip (L : E →L[ℂ] (X →L[ℝ] F)) : X →L[ℝ] (E →L[ℂ] F) :=
        LinearMap.mkContinuous
          { toFun := fun v ↦ LinearMap.mkContinuous
              { toFun := fun u ↦ L u v
                map_add' := by intros; simp
                map_smul' := by intros; simp }
              (‖L‖ * ‖v‖) (by
                intro u
                exact ((L u).le_opNorm v).trans
                  ((mul_le_mul_of_nonneg_right (L.le_opNorm u) (norm_nonneg v)).trans_eq
                    (by ring)))
            map_add' := by intros; ext; simp
            map_smul' := by intros; ext; simp }
          ‖L‖ (by
            intro v
            apply ContinuousLinearMap.opNorm_le_bound _
              (mul_nonneg (norm_nonneg L) (norm_nonneg v))
            intro u
            exact ((L u).le_opNorm v).trans
              ((mul_le_mul_of_nonneg_right (L.le_opNorm u) (norm_nonneg v)).trans_eq
                (by ring)))
      have hflipNorm (L : E →L[ℂ] (X →L[ℝ] F)) : ‖flip L‖ ≤ ‖L‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
        intro v
        apply ContinuousLinearMap.opNorm_le_bound _
          (mul_nonneg (norm_nonneg L) (norm_nonneg v))
        intro u
        exact ((L u).le_opNorm v).trans
          ((mul_le_mul_of_nonneg_right (L.le_opNorm u) (norm_nonneg v)).trans_eq
            (by ring))
      let flipMap : (E →L[ℂ] (X →L[ℝ] F)) →L[ℝ] (X →L[ℝ] (E →L[ℂ] F)) :=
        LinearMap.mkContinuous
          { toFun := flip
            map_add' := by intros; ext; simp [flip]
            map_smul' := by intros; ext; simp [flip] }
          1 (fun L ↦ by
            change ‖flip L‖ ≤ 1 * ‖L‖
            simpa only [one_mul] using hflipNorm L)
      let S : X → X →L[ℝ] (E →L[ℂ] F) := fun x ↦ flipMap (D x)
      have hS : ContDiff ℝ k S := flipMap.contDiff.comp hD
      have hvalue (x v : X) (u : E) : S x v u = fderiv ℝ (fun y ↦ f y u) x v := rfl
      clear_value d D flip flipMap S
      refine contDiff_succ_iff_hasFDerivAt.mpr ⟨S, hS, ?_⟩
      intro x
      -- One operator-norm neighborhood controls the remainders for every input vector.
      rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
      intro ε hε
      have hclose : ∀ᶠ z in nhds x, ‖S z - S x‖ < ε :=
        (hS.continuous.continuousAt.sub continuousAt_const).norm.eventually
          (gt_mem_nhds (by simpa only [Pi.sub_apply, sub_self, norm_zero] using hε))
      obtain ⟨δ, hδ, hδclose⟩ := Metric.eventually_nhds_iff.mp hclose
      filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
      apply (f y - f x - S x (y - x)).opNorm_le_bound
        (mul_nonneg hε.le (norm_nonneg _))
      intro u
      let g : X → F := fun z ↦ f z u - fderiv ℝ (fun w ↦ f w u) x z
      have hg (z : X) : HasFDerivAt g
          (fderiv ℝ (fun w ↦ f w u) z - fderiv ℝ (fun w ↦ f w u) x) z :=
        ((hf u).differentiable (by simp) z).hasFDerivAt.sub
          (fderiv ℝ (fun w ↦ f w u) x).hasFDerivAt
      have hgBound (z : X) (hz : z ∈ Metric.ball x δ) :
          ‖fderiv ℝ (fun w ↦ f w u) z - fderiv ℝ (fun w ↦ f w u) x‖ ≤ ε * ‖u‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε.le (norm_nonneg _))
        intro v
        change ‖fderiv ℝ (fun w ↦ f w u) z v - fderiv ℝ (fun w ↦ f w u) x v‖ ≤ _
        rw [← hvalue z v u, ← hvalue x v u]
        calc
          _ ≤ ‖S z - S x‖ * ‖v‖ * ‖u‖ := by
            exact (((S z - S x) v).le_opNorm u).trans
              (mul_le_mul_of_nonneg_right ((S z - S x).le_opNorm v) (norm_nonneg u))
          _ ≤ ε * ‖u‖ * ‖v‖ := by
            have hz' := (hδclose hz).le
            exact (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hz' (norm_nonneg v)) (norm_nonneg u)).trans_eq
                (by ring)
      have hmean := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z _ ↦ (hg z).hasFDerivWithinAt) hgBound
        (Metric.mem_ball_self hδ) hy
      change ‖(f y - f x - S x (y - x)) u‖ ≤ _
      have heq : (f y - f x - S x (y - x)) u = g y - g x := by
        simp only [sub_apply, hvalue, g, map_sub]
        abel
      rw [heq]
      exact hmean.trans_eq (by ring)
  -- The zeroth derivative bound bundles the original pointwise evaluations.
  obtain ⟨C, hC, hCbound⟩ := hbound 0 (by omega)
  let ev (x : X) : E →ₗ[ℂ] F :=
    { toFun := fun u ↦ J u x
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have hev (x : X) (u : E) : ‖ev x u‖ ≤ C * ‖u‖ := by
    change ‖J u x‖ ≤ C * ‖u‖
    simpa only [norm_iteratedFDeriv_zero] using hCbound u x
  let T (x : X) : E →L[ℂ] F := (ev x).mkContinuous C (hev x)
  exact ⟨T, fun _ _ ↦ rfl, regularity k T hJ hbound⟩

open Bundle
open scoped Manifold SchwartzMap

namespace SmoothBundlePresentation

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- The actual localized Sobolev evaluation has operator-norm C^k regularity.
One extra derivative and the original C^(k+1) embedding give uniform bounds.
The kernel reconstruction applies this to the output and to the induced input-dual bundle. -/
theorem exists_contDiff_localizedCkFunction_sobolevToCk
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (k : ℕ) (s : ℝ) (hs : (n : ℝ) / 2 + ((k + 1 : ℕ) : ℝ) < s) (j : Fin A.size) :
    ∃ T : EuclideanSpace ℝ (Fin n) → A.SobolevSpace s →L[ℂ]
        EuclideanSpace ℂ (Fin r),
      (∀ x u, T x u = A.localizedCkFunction (k + 1) j
        (A.sobolevToCk (k + 1) s hs u) x) ∧ ContDiff ℝ k T := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let := A.frame_mem_atlas j
  let loc : A.CkSectionSpace (k + 1) →ₗ[ℂ] (X → V) :=
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
  have hloc (w : A.CkSectionSpace (k + 1)) : loc w = A.localizedCkFunction (k + 1) j w := by
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
  let J : A.SobolevSpace s →ₗ[ℂ] (X → V) :=
    loc.comp (A.sobolevToCk (k + 1) s hs).toLinearMap
  have hJ (u : A.SobolevSpace s) : J u =
      A.localizedCkFunction (k + 1) j (A.sobolevToCk (k + 1) s hs u) := hloc _
  obtain ⟨T, hT, hdiff⟩ := exists_contDiff_evaluation_of_uniform_derivative_bounds k J
    (fun u ↦ by rw [hJ]; exact A.contDiff_localizedCkFunction _ _ _) (by
      intro i hi
      refine ⟨‖A.sobolevToCk (k + 1) s hs‖, norm_nonneg _, ?_⟩
      intro u x
      rw [hJ]
      have hbound := le_csSup
        (A.bddAbove_ckNorm_values (k + 1) (A.sobolevToCk (k + 1) s hs u))
        (show ‖iteratedFDeriv ℝ i (A.localizedCkFunction (k + 1) j
          (A.sobolevToCk (k + 1) s hs u)) x‖ ∈
          {a : ℝ | ∃ (j : Fin A.size) (i : ℕ), i ≤ k + 1 ∧
            ∃ y : X, a = ‖iteratedFDeriv ℝ i (A.localizedCkFunction (k + 1) j
              (A.sobolevToCk (k + 1) s hs u)) y‖} from ⟨j, i, hi, x, rfl⟩)
      exact hbound.trans ((A.sobolevToCk (k + 1) s hs).le_opNorm u))
  exact ⟨T, fun x u ↦ (hT x u).trans (congrFun (hJ u) x), hdiff⟩

end SmoothBundlePresentation

end AtiyahSinger
