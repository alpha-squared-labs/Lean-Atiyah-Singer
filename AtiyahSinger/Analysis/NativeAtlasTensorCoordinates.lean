/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasCovariantSobolev
public import AtiyahSinger.Analysis.CovariantTensorCoordinates
public import AtiyahSinger.Geometry.CovariantTensorMultilinear
public import AtiyahSinger.Geometry.NativeAtlasLocalConnection
public import AtiyahSinger.Geometry.SmoothInvariantMetric

/-!
# Actual atlas coordinates of native iterated covariant tensors

Public module ID: M0807.

The original recursive Hom derivative has exactly the components of the original
atlas tensor recursion. The proof uses local connection agreement and the full
old-slot Leibniz formula with the actual tangent coordinate fields. No substitute
connection, tensor model, or Fourier norm is introduced. Source: SG III.2 (2.1).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 40

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

local notation "MI" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "TM" => TangentSpace MI (M := M)
local notation "VF" => EuclideanSpace ℂ (Fin r)

set_option backward.isDefEq.respectTransparency false in
/-- In each actual chart frame, native covariant tensors have the original atlas components. -/
theorem iteratedCovariantDerivative_eq_atlasComponents
    (covT : CovariantDerivative MI (EuclideanSpace ℝ (Fin n)) TM)
    (covE : CovariantDerivative MI VF E)
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞) :
    letI := ComplexBundle.modelTopology VF E
    let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
    ∀ covA : AtlasComplexConnection A,
      (∀ (u : smoothSections (n := n) (r := r) E) (x : M) (v : TM x),
        covA.covariantDerivative
          ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) x v =
            covE u.val x v) →
      ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index)
        (u : smoothSections (n := n) (r := r) E) (k : ℕ) (indices : Fin k → Fin n)
        (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet),
        covariantTensorEvaluation E k x
          (fun a ↦ ((tangentBundleCore MI M).localTriv ⟨c, hc⟩).symmL ℝ x
            (EuclideanSpace.single (indices a) 1))
          (iteratedCovariantDerivative covT covE k u.val x) =
        (A.frameLinearEquiv i x hx.2).symm ((EuclideanSpace.equiv (Fin r) ℂ)
          (covA.localIteratedCovariantDerivative covT c hc i
            ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) k indices (c x))) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let H := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℂ (Fin r)
  let := ComplexBundle.modelTopology F E
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  change ∀ covA : AtlasComplexConnection A, _
  intro covA hA c hc i u k
  change A.Index at i
  let e : Trivialization H (TotalSpace.proj : TangentBundle I M → M) :=
    (tangentBundleCore I M).localTriv ⟨c, hc⟩
  let : MemTrivializationAtlas e := ⟨⟨⟨c, hc⟩, rfl⟩⟩
  let Y (a : Fin n) (y : M) : TangentSpace I y := e.symmL ℝ y (EuclideanSpace.single a 1)
  let D (j : ℕ) := iteratedCovariantDerivative covT covE j u.val
  let ua := (nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u
  let components (j : ℕ) := covA.localIteratedCovariantDerivative covT c hc i ua j
  have hY (a : Fin n) (x : M) (hx : x ∈ c.source) :
      MDifferentiableAt I (I).tangent (fun y ↦ (⟨y, Y a y⟩ : TangentBundle I M)) x := by
    apply (e.mdifferentiableAt_section_iff I (Y a) hx).mpr
    have heq : (fun y ↦ (e ⟨y, Y a y⟩).2) =ᶠ[nhds x]
        (fun _ ↦ EuclideanSpace.single a 1) := by
      filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
      change (e ⟨y, e.symmL ℝ y (EuclideanSpace.single a 1)⟩).2 = _
      rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy, e.continuousLinearMapAt_symmL hy]
    exact mdifferentiableAt_const.congr_of_eventuallyEq heq
  have hD (j : ℕ) (x : M) :=
    (contMDiff_iteratedCovariantDerivative_of_t2Space covT covE hcovT hcovE j u).contMDiffAt
      (x := x) |>.mdifferentiableAt (by simp)
  have hchart (x : M) (hx : x ∈ c.source) (a : Fin n) :
      mfderiv I I c x (Y a x) = EuclideanSpace.single a 1 := by
    have hderiv : mfderiv I I c x = e.continuousLinearMapAt ℝ x := by
      rw [(tangentBundleCore I M).localTriv_continuousLinearMapAt
        (show x ∈ e.baseSet from hx)]
      rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas hc hx)]
      rfl
    rw [hderiv]
    exact e.continuousLinearMapAt_symmL hx _
  have hcoordinates (τ : ∀ y : M, E y) (x : M)
      (hx : x ∈ c.source ∩ (A.chart i).baseSet) :
      atlasSectionInChart A c i τ (c x) =
        (EuclideanSpace.equiv (Fin r) ℂ).symm (A.frameLinearEquiv i x hx.2 (τ x)) := by
    change (i.val ⟨c.symm (c x), τ (c.symm (c x))⟩).2 =
      (EuclideanSpace.equiv (Fin r) ℂ).symm
        ((EuclideanSpace.equiv (Fin r) ℂ) (i.val ⟨x, τ x⟩).2)
    rw [c.left_inv hx.1]
    rfl
  -- Keep chart indices and base points free, so derivatives use equality on a neighborhood.
  induction k with
  | zero =>
    intro indices x hx
    change x ∈ c.source ∩ (A.chart i).baseSet at hx
    change u.val x = (A.frameLinearEquiv i x hx.2).symm
      ((EuclideanSpace.equiv (Fin r) ℂ) (atlasSectionInChart A c i u.val (c x)))
    rw [hcoordinates u.val x hx]
    exact (A.frameLinearEquiv i x hx.2).symm_apply_apply (u.val x) |>.symm
  | succ k ih =>
    intro indices x hx
    change x ∈ c.source ∩ (A.chart i).baseSet at hx
    let α : Fin k → Fin n := fun a ↦ indices a.succ
    let W : ∀ y : M, E y := fun y ↦ covariantTensorEvaluation E k y
      (fun a ↦ Y (α a) y) (D k y)
    have hW := mdifferentiableAt_covariantTensorEvaluation k (D k)
      (fun a ↦ Y (α a)) x (hD k x) (fun a ↦ hY (α a) x hx.1)
    have hnear : atlasSectionInChart A c i W =ᶠ[nhds (c x)] components k α := by
      have hc' := contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hc) (c.map_source hx.1)
      have hi := hc'.continuousAt.preimage_mem_nhds (by
        rw [c.left_inv hx.1]
        exact (A.chart i).open_baseSet.mem_nhds hx.2)
      filter_upwards [c.open_target.mem_nhds (c.map_source hx.1), hi] with z hz hi
      have hlocal := ih α (c.symm z) ⟨c.map_target hz, hi⟩
      have ht := hcoordinates W (c.symm z) ⟨c.map_target hz, hi⟩
      change W (c.symm z) = _ at hlocal
      rw [hlocal, LinearEquiv.apply_symm_apply, c.right_inv hz] at ht
      exact ht
    have hconnection := nativeConnection_eq_atlasExpression covE covA hA W c hc i x hx hW
      (Y (indices 0) x)
    rw [hchart x hx.1 (indices 0), hnear.fderiv_eq, hnear.self_of_nhds] at hconnection
    -- Each old-slot tangent correction expands in the same coordinate tangent basis.
    have hcorrection (a : Fin k) :
        covariantTensorEvaluation E k x
          (Function.update (fun j ↦ Y (α j) x) a (covT (Y (α a)) x (Y (indices 0) x)))
          (D k x) =
        ∑ b : Fin n, (atlasTangentChristoffel covT c hc (c x) (indices 0) (α a) b : ℂ) •
          (A.frameLinearEquiv i x hx.2).symm ((EuclideanSpace.equiv (Fin r) ℂ)
            (components k (Function.update α a b) (c x))) := by
      let v : TangentSpace I x := covT (Y (α a)) x (Y (indices 0) x)
      let C : H := e.continuousLinearMapAt ℝ x v
      have hC (b : Fin n) : atlasTangentChristoffel covT c hc (c x)
          (indices 0) (α a) b = C b := by
        unfold atlasTangentChristoffel
        rw [c.left_inv hx.1]
        rfl
      have hv : v = ∑ b : Fin n, C b • Y b x := by
        have hsum : ∑ b : Fin n, C b • EuclideanSpace.single b 1 = C := by
          simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
            using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr C
        calc
          v = e.symmL ℝ x C := (e.symmL_continuousLinearMapAt hx.1 v).symm
          _ = ∑ b : Fin n, C b • Y b x := by
            conv_lhs => rw [← hsum]
            simp only [map_sum, map_smul, Y]
      rw [← covariantTensorMultilinearMap_apply]
      change covariantTensorMultilinearMap E k x (D k x)
        (Function.update (fun j ↦ Y (α j) x) a v) = _
      rw [hv, MultilinearMap.map_update_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [MultilinearMap.map_update_smul, covariantTensorMultilinearMap_apply]
      have hupdate : Function.update (fun j ↦ Y (α j) x) a (Y b x) =
          fun j ↦ Y (Function.update α a b j) x := by
        funext j
        by_cases h : j = a <;> simp [h]
      have hi : covariantTensorEvaluation E k x
          (fun j ↦ Y (Function.update α a b j) x) (D k x) =
          (A.frameLinearEquiv i x hx.2).symm ((EuclideanSpace.equiv (Fin r) ℂ)
            (components k (Function.update α a b) (c x))) :=
        ih (Function.update α a b) x hx
      rw [hupdate, hi, hC,
        RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    -- The full Hom Leibniz formula now becomes exactly the original d + Γ - Γ_T recursion.
    have hleibniz := covariantTensorConnection_evaluation covT covE k (D k)
      (Y (indices 0)) (fun a ↦ Y (α a)) x (hD k x) (hY (indices 0) x hx.1)
      (fun a ↦ hY (α a) x hx.1)
    change covariantTensorEvaluation E k x (fun a ↦ Y (α a) x)
      (covariantTensorConnection covT covE k (D k) x (Y (indices 0) x)) = _
    rw [hleibniz]
    change covE W x (Y (indices 0) x) - _ = _
    rw [hconnection]
    simp_rw [hcorrection]
    change _ = (A.frameLinearEquiv i x hx.2).symm ((EuclideanSpace.equiv (Fin r) ℂ)
      (fderiv ℝ (components k α) (c x) (EuclideanSpace.single (indices 0) 1) +
        covA.connectionForm c i (c x) (EuclideanSpace.single (indices 0) 1)
          (components k α (c x)) -
        ∑ a : Fin k, ∑ b : Fin n,
          (atlasTangentChristoffel covT c hc (c x) (indices 0) (α a) b : ℂ) •
            components k (Function.update α a b) (c x)))
    simp only [map_sub, map_sum, map_smul]
    rfl

omit [T2Space M] in
/-- Full contraction in any actual tangent basis computes the unchanged native tensor pairing. -/
theorem iteratedCovariantPairing_re_eq_sum_basis
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : SmoothHermitianMetric (n := n) (r := r) E) (k : ℕ) (x : M)
    (b : Module.Basis (Fin n) ℝ (TM x))
    (a d : CovariantTensorFiber (n := n) (r := r) E k x) :
    (iteratedCovariantPairing g h k x a d).re =
      ∑ indices : Fin k → Fin n, ∑ indices' : Fin k → Fin n,
        (∏ j : Fin k, g.inner x (LinearMap.toContinuousLinearMap (b.coord (indices j)))
          (LinearMap.toContinuousLinearMap (b.coord (indices' j)))) *
        ((h.toCore x).inner
          (covariantTensorEvaluation E k x (fun j ↦ b (indices j)) a)
          (covariantTensorEvaluation E k x (fun j ↦ b (indices' j)) d)).re := by
  classical
  induction k with
  | zero =>
    simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    rfl
  | succ k ih =>
    change TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k x at a d
    have hsum (f : (Fin (k + 1) → Fin n) → ℝ) :
        ∑ v, f v = ∑ i : Fin n, ∑ w : Fin k → Fin n, f (Fin.cons i w) := by
      rw [← (Fin.consEquiv (fun _ : Fin (k + 1) ↦ Fin n)).sum_comp,
        Fintype.sum_prod_type]
      rfl
    -- Separate the first covariant slot in the two full index lists.
    conv_rhs =>
      simp only [hsum]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      covariantTensorEvaluation, Fin.tail_def]
    rw [iteratedCovariantPairing_succ_re_eq_sum_basis g h k x b]
    simp_rw [ih]
    simp only [Finset.mul_sum, ← mul_assoc]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The atlas local squared length is the original native pairing on its valid chart domain. -/
theorem nativeAtlas_localCovariantDerivativeNormSq_eq
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (covT : CovariantDerivative MI (EuclideanSpace ℝ (Fin n)) TM)
    (covE : CovariantDerivative MI VF E)
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞) :
    letI := ComplexBundle.modelTopology VF E
    let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
    ∀ covA : AtlasComplexConnection A,
      (∀ (u : smoothSections (n := n) (r := r) E) (x : M) (v : TM x),
        covA.covariantDerivative
          ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) x v =
            covE u.val x v) →
      ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index)
        (u : smoothSections (n := n) (r := r) E) (k : ℕ)
        (x : M) (_hx : x ∈ c.source ∩ (A.chart i).baseSet),
        covA.localCovariantDerivativeNormSq covT c hc i g h.toContinuousHermitianMetric k
          ((nativeSmoothSectionLinearEquiv (n := n) (r := r) E).symm u) x =
        (iteratedCovariantPairing g h k x (iteratedCovariantDerivative covT covE k u.val x)
          (iteratedCovariantDerivative covT covE k u.val x)).re := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let H := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℂ (Fin r)
  let := ComplexBundle.modelTopology F E
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  change ∀ covA : AtlasComplexConnection A, _
  intro covA hA c hc i u k x hx
  change A.Index at i
  change x ∈ c.source ∩ (A.chart i).baseSet at hx
  let e : Trivialization H (TotalSpace.proj : TangentBundle I M → M) :=
    (tangentBundleCore I M).localTriv ⟨c, hc⟩
  let b : Module.Basis (Fin n) ℝ (TangentSpace I x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
      (e.continuousLinearEquivAt ℝ x hx.1).symm.toLinearEquiv
  have hb (a : Fin n) : b a = e.symmL ℝ x (EuclideanSpace.single a 1) := by
    rw [Module.Basis.map_apply]
    change (e.continuousLinearEquivAt ℝ x hx.1).symm
      ((EuclideanSpace.basisFun (Fin n) ℝ) a) = _
    rw [EuclideanSpace.basisFun_apply, e.symm_continuousLinearEquivAt_eq hx.1]
  have hderiv : mfderiv I I c x = e.continuousLinearMapAt ℝ x := by
    rw [(tangentBundleCore I M).localTriv_continuousLinearMapAt
      (show x ∈ e.baseSet from hx.1)]
    rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas hc hx.1)]
    rfl
  have hdual (a : Fin n) : LinearMap.toContinuousLinearMap (b.coord a) =
      covectorFromChart c x (EuclideanSpace.single a 1) := by
    ext v
    change b.repr v a = inner ℝ (EuclideanSpace.single a 1) (mfderiv I I c x v)
    simp only [b, Module.Basis.map_repr, LinearEquiv.trans_apply]
    rw [hderiv, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    change ((e.continuousLinearEquivAt ℝ x hx.1) v) a =
      ((e.continuousLinearMapAt ℝ x) v) a
    exact congrArg (fun z : H ↦ z a) (congrFun (e.coe_continuousLinearEquivAt_eq hx.1) v)
  -- Use the same native tensor on both sides of the arbitrary-basis contraction formula.
  rw [iteratedCovariantPairing_re_eq_sum_basis g h k x b]
  unfold AtlasComplexConnection.localCovariantDerivativeNormSq
  rw [dite_eq_left hx]
  apply Finset.sum_congr rfl
  intro indices hi
  apply Finset.sum_congr rfl
  intro indices' hi'
  apply congrArg₂ (fun s t : ℝ ↦ s * t)
  · apply Finset.prod_congr rfl
    intro j hj
    exact (congrArg₂ (fun p q ↦ g.inner x p q)
      (hdual (indices j)) (hdual (indices' j))).symm
  · have hvalues (v : Fin k → Fin n) :
        (A.frameLinearEquiv i x hx.2).symm ((EuclideanSpace.equiv (Fin r) ℂ)
          (covA.localIteratedCovariantDerivative covT c hc i
            ((nativeSmoothSectionLinearEquiv E).symm u) k v (c x))) =
        covariantTensorEvaluation E k x (fun j ↦ b (v j))
          (iteratedCovariantDerivative covT covE k u.val x) := by
      have hvectors : (fun j ↦ b (v j)) =
          fun j ↦ e.symmL ℝ x (EuclideanSpace.single (v j) 1) :=
        funext (fun j ↦ hb (v j))
      rw [hvectors]
      exact (iteratedCovariantDerivative_eq_atlasComponents covT covE hcovT hcovE
        covA hA c hc i u k v x hx).symm
    exact congrArg Complex.re (congrArg₂ (h.toCore x).inner
      (hvalues indices) (hvalues indices'))

end AtiyahSinger
