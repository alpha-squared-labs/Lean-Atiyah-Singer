/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasHermitianCoordinates
public import AtiyahSinger.Geometry.CotangentMetricCoordinates
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Metric comparison for finite covariant tensor arrays

Public module ID: M1104.

The original cotangent metric and original atlas Hermitian forms define a positive
real inner product on every finite array of tensor coefficients. For a smooth
atlas Hermitian metric, compact chart supports give uniform comparison with
coordinate squared norms. All ordered
slots and the varying rank of the specified frame are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped BigOperators Manifold ContDiff TensorProduct

/-- The full Gram contraction is a positive definite real inner product on finite tensor arrays.
The construction retains the specified basis and value metric in every ordered slot. -/
theorem exists_tensor_array_inner_core
    {U V ι : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (b : Module.Basis ι ℝ U) (h : InnerProductSpace.Core ℝ V) (k : ℕ) :
    ∃ c : InnerProductSpace.Core ℝ ((Fin k → ι) → V), ∀ F G,
      c.inner F G = ∑ p : Fin k → ι, ∑ q : Fin k → ι,
        (∏ a : Fin k, inner ℝ (b (p a)) (b (q a))) * h.inner (F p) (G q) := by
  classical
  let value (j : ℕ) (F G : (Fin j → ι) → V) : ℝ :=
    ∑ p : Fin j → ι, ∑ q : Fin j → ι,
      (∏ a : Fin j, inner ℝ (b (p a)) (b (q a))) * h.inner (F p) (G q)
  have hstep (j : ℕ) (F G : (Fin (j + 1) → ι) → V) :
      value (j + 1) F G = ∑ i : ι, ∑ l : ι, inner ℝ (b i) (b l) *
        value j (fun p ↦ F (Fin.cons i p)) (fun q ↦ G (Fin.cons l q)) := by
    dsimp only [value]
    rw [← (Fin.consEquiv (fun _ : Fin (j + 1) ↦ ι)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply]
    simp_rw [← (Fin.consEquiv (fun _ : Fin (j + 1) ↦ ι)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    simp_rw [Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    rfl
  change ∃ c : InnerProductSpace.Core ℝ ((Fin k → ι) → V),
    ∀ F G, c.inner F G = value k F G
  induction k with
  | zero =>
    let e : ((Fin 0 → ι) → V) →ₗ[ℝ] V := LinearMap.proj default
    have he : Function.Injective e := by
      intro F G hFG
      funext p
      have hp : p = default := Subsingleton.elim _ _
      change F default = G default at hFG
      simpa only [hp] using hFG
    refine ⟨{
      inner := fun F G ↦ h.inner (e F) (e G)
      conj_inner_symm := fun F G ↦ h.conj_inner_symm (e F) (e G)
      re_inner_nonneg := fun F ↦ h.re_inner_nonneg (e F)
      add_left := ?_
      smul_left := ?_
      definite := ?_ }, ?_⟩
    · intro F G J
      rw [map_add, h.add_left]
    · intro F G a
      rw [map_smul, h.smul_left]
    · intro F hF
      apply he
      rw [map_zero]
      exact h.definite _ hF
    · intro F G
      simp only [value, Finset.univ_unique, Finset.sum_singleton,
        Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      rfl
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    let embed : ((Fin (k + 1) → ι) → V) →ₗ[ℝ]
        TensorProduct ℝ U ((Fin k → ι) → V) := {
      toFun := fun F ↦ ∑ i : ι, TensorProduct.tmul ℝ (b i) (fun p ↦ F (Fin.cons i p))
      map_add' := by
        intro F G
        have hval (i : ι) : (fun p ↦ (F + G) (Fin.cons i p)) =
            (fun p ↦ F (Fin.cons i p)) + (fun p ↦ G (Fin.cons i p)) := rfl
        simp only [hval, TensorProduct.tmul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a F
        have hval (i : ι) : (fun p ↦ (a • F) (Fin.cons i p)) =
            a • (fun p ↦ F (Fin.cons i p)) := rfl
        simp only [hval, TensorProduct.tmul_smul, Finset.smul_sum, RingHom.id_apply] }
    -- Applying a dual basis coordinate recovers exactly the corresponding tail array.
    let recover (i : ι) : TensorProduct ℝ U ((Fin k → ι) → V) →ₗ[ℝ]
        ((Fin k → ι) → V) :=
      (TensorProduct.lid ℝ _).toLinearMap.comp
        (TensorProduct.map (b.coord i) LinearMap.id)
    have hrecover (i : ι) (F : (Fin (k + 1) → ι) → V) :
        recover i (embed F) = fun p ↦ F (Fin.cons i p) := by
      change recover i (∑ l : ι, TensorProduct.tmul ℝ (b l)
        (fun p ↦ F (Fin.cons l p))) = _
      rw [map_sum]
      have hterm (l : ι) : recover i
          (TensorProduct.tmul ℝ (b l) (fun p ↦ F (Fin.cons l p))) =
          (b.coord i (b l)) • (fun p ↦ F (Fin.cons l p)) := rfl
      simp only [hterm, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      simp
    have hinj : Function.Injective embed := by
      intro F G hFG
      funext p
      have hr := congrArg (fun t ↦ recover (p 0) t (Fin.tail p)) hFG
      simpa only [hrecover, Fin.cons_self_tail] using hr
    -- Only this algebraic realization receives the auxiliary tensor-product norm.
    let : InnerProductSpace.Core ℝ ((Fin k → ι) → V) := c
    let : NormedAddCommGroup ((Fin k → ι) → V) := c.toNormedAddCommGroup
    let : InnerProductSpace ℝ ((Fin k → ι) → V) := InnerProductSpace.ofCore c.toCore
    have hformula (F G : (Fin (k + 1) → ι) → V) :
        inner ℝ (embed F) (embed G) = value (k + 1) F G := by
      rw [hstep]
      simp only [embed, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
        TensorProduct.inner_tmul]
      rw [Finset.sum_comm]
      change (∑ i : ι, ∑ l : ι, inner ℝ (b i) (b l) *
        c.inner (fun p ↦ F (Fin.cons i p)) (fun q ↦ G (Fin.cons l q))) = _
      simp only [hc]
    refine ⟨{
      inner := fun F G ↦ inner ℝ (embed F) (embed G)
      conj_inner_symm := by
        intro F G
        change inner ℝ (embed G) (embed F) = inner ℝ (embed F) (embed G)
        exact real_inner_comm _ _
      re_inner_nonneg := by
        intro F
        change 0 ≤ inner ℝ (embed F) (embed F)
        exact real_inner_self_nonneg
      add_left := ?_
      smul_left := ?_
      definite := ?_ }, hformula⟩
    · intro F G J
      rw [map_add, inner_add_left]
    · intro F G a
      rw [map_smul, real_inner_smul_left]
      rfl
    · intro F hF
      apply hinj
      rw [map_zero]
      exact (inner_self_eq_zero (𝕜 := ℝ)).mp hF

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

namespace SmoothComplexBundleAtlas

/-- At a valid chart point, the original full tensor contraction is a real inner product
on the actual coordinate arrays. This supports both norm comparison and finite-sum estimates. -/
theorem exists_covariant_array_inner_core (A : SmoothComplexBundleAtlas (n := n) E)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : ComplexBundle.ContinuousHermitianMetric E)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (k : ℕ)
    (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet) :
    ∃ q : InnerProductSpace.Core ℝ
        ((Fin k → Fin n) → EuclideanSpace ℂ (Fin (A.rank i))), ∀ F G,
      q.inner F G =
        ∑ p : Fin k → Fin n, ∑ r : Fin k → Fin n,
          (∏ a : Fin k, g.inner x
            (covectorFromChart c x (EuclideanSpace.single (p a) 1))
            (covectorFromChart c x (EuclideanSpace.single (r a) 1))) *
          ((h.toCore x).inner
            ((A.frameLinearEquiv i x hx.2).symm
              ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (F p)))
            ((A.frameLinearEquiv i x hx.2).symm
              ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (G r)))).re := by
  classical
  -- Pull back the original complex form to this one coordinate fiber, then restrict to ℝ.
  let R : EuclideanSpace ℂ (Fin (A.rank i)) ≃ₗ[ℂ] E x :=
    (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toLinearEquiv.trans
      (A.frameLinearEquiv i x hx.2).symm
  let hR : InnerProductSpace.Core ℝ (EuclideanSpace ℂ (Fin (A.rank i))) := {
    inner := fun u v ↦ ((h.toCore x).inner (R u) (R v)).re
    conj_inner_symm := by
      intro u v
      change ((h.toCore x).inner (R v) (R u)).re = _
      simpa only [Complex.conj_re] using
        congrArg Complex.re ((h.toCore x).conj_inner_symm (R u) (R v))
    re_inner_nonneg := fun u ↦ (h.toCore x).re_inner_nonneg (R u)
    add_left := by
      intro u v w
      rw [map_add, (h.toCore x).add_left, Complex.add_re]
    smul_left := by
      intro u v t
      have hs : R (t • u) = (t : ℂ) • R u := by
        change R ((t : ℂ) • u) = _
        exact R.map_smul (t : ℂ) u
      change ((h.toCore x).inner (R (t • u)) (R v)).re =
        t * ((h.toCore x).inner (R u) (R v)).re
      rw [hs, (h.toCore x).smul_left]
      simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    definite := by
      intro u hu
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      have hz : R u = 0 := (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hu
      apply R.injective
      simpa only [map_zero] using hz }
  -- The actual chart pullback is an isomorphism on cotangent fibers at this point.
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] CotangentFiber (n := n) x := {
    toFun := covectorFromChart c x
    map_add' := by
      intro u v
      ext w
      exact inner_add_left u v _
    map_smul' := by
      intro t u
      ext w
      exact real_inner_smul_left u _ t }
  have hbij : Function.Bijective L := by
    constructor
    · intro u v huv
      have ht := congrArg (covectorInChart c x) huv
      simpa only [L, LinearMap.coe_mk, AddHom.coe_mk,
        covectorInChart_covectorFromChart c hc x hx.1] using ht
    · intro ξ
      exact ⟨covectorInChart c x ξ, covectorFromChart_covectorInChart c hc x hx.1 ξ⟩
  let e := LinearEquiv.ofBijective L hbij
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map e
  let : RiemannianBundle (CotangentFiber (n := n) (M := M)) := ⟨g.toRiemannianMetric⟩
  obtain ⟨q, hq⟩ := exists_tensor_array_inner_core b hR k
  refine ⟨q, ?_⟩
  intro F G
  have hb (a : Fin n) : b a = covectorFromChart c x (EuclideanSpace.single a 1) := by
    simp only [b, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply]
    rfl
  have hg (ξ η : CotangentFiber (n := n) x) : inner ℝ ξ η = g.inner x ξ η := rfl
  have hhR (u v : EuclideanSpace ℂ (Fin (A.rank i))) :
      hR.inner u v = ((h.toCore x).inner
        ((A.frameLinearEquiv i x hx.2).symm
          ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) u))
        ((A.frameLinearEquiv i x hx.2).symm
          ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) v))).re := rfl
  simpa only [hb, hg, hhR] using hq F G

/-- For the specified smooth Hermitian metric, the tensor metric on a compact chart/frame
support is uniformly equivalent to the sum of squared coordinate lengths, for arbitrary
arrays of the given tensor order. -/
theorem exists_covariant_array_norm_sq_bounds (A : SmoothComplexBundleAtlas (n := n) E)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (k : ℕ)
    (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.source ∩ (A.chart i).baseSet) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ (x : M) (hx : x ∈ K),
      ∀ F : (Fin k → Fin n) → EuclideanSpace ℂ (Fin (A.rank i)),
      let values := fun p ↦ (A.frameLinearEquiv i x (hKc hx).2).symm
        ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (F p))
      let Q := ∑ p : Fin k → Fin n, ∑ q : Fin k → Fin n,
        (∏ s : Fin k, g.inner x
          (covectorFromChart c x (EuclideanSpace.single (p s) 1))
          (covectorFromChart c x (EuclideanSpace.single (q s) 1))) *
        ((h.toCore x).inner (values p) (values q)).re
      a * (∑ p, ‖F p‖ ^ 2) ≤ Q ∧ Q ≤ b * (∑ p, ‖F p‖ ^ 2) := by
  classical
  let W := EuclideanSpace ℂ (Fin (A.rank i))
  let V := PiLp 2 (fun _ : Fin k → Fin n ↦ W)
  let Q (x : M) (F G : V) : ℝ :=
    ∑ p : Fin k → Fin n, ∑ q : Fin k → Fin n,
      (∏ a : Fin k, g.inner x
        (covectorFromChart c x (EuclideanSpace.single (p a) 1))
        (covectorFromChart c x (EuclideanSpace.single (q a) 1))) *
      (inner ℂ (F p) (A.hermitianGramOperator h i x (G q))).re
  have hcore (x : M) (hx : x ∈ K) :
      ∃ t : InnerProductSpace.Core ℝ ((Fin k → Fin n) → W), ∀ F G,
        t.inner F G = Q x (WithLp.toLp 2 F) (WithLp.toLp 2 G) := by
    obtain ⟨t, ht⟩ := A.exists_covariant_array_inner_core g h c hc i k x (hKc hx)
    refine ⟨t, ?_⟩
    intro F G
    rw [ht]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    have hp := A.pairing_eq_hermitianGramOperator h i x (hKc hx).2
      ((A.frameLinearEquiv i x (hKc hx).2).symm
        ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (F p)))
      ((A.frameLinearEquiv i x (hKc hx).2).symm
        ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (G q)))
    simpa only [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] using
      congrArg Complex.re hp
  let S : Set V := Metric.sphere 0 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hcont : ContinuousOn (fun z : M × V ↦ Q z.1 z.2 z.2) (K ×ˢ S) := by
    apply continuousOn_finsetSum
    intro p _
    apply continuousOn_finsetSum
    intro q _
    apply ContinuousOn.mul
    · apply continuousOn_finsetProd
      intro a _
      exact (g.contMDiffOn_inner_covectorFromChart c hc
        (EuclideanSpace.single (p a) 1) (EuclideanSpace.single (q a) 1)).continuousOn.comp
          continuous_fst.continuousOn (fun z hz ↦ (hKc hz.1).1)
    · apply Complex.continuous_re.comp_continuousOn
      have hp : Continuous (fun z : M × V ↦ z.2 p) :=
        (PiLp.continuous_apply 2 _ p).comp continuous_snd
      have hq : Continuous (fun z : M × V ↦ z.2 q) :=
        (PiLp.continuous_apply 2 _ q).comp continuous_snd
      have hH := (A.contMDiffOn_hermitianGramOperator h hh i).continuousOn.comp
        (continuous_fst.continuousOn : ContinuousOn (fun z : M × V ↦ z.1) (K ×ˢ S))
        (fun z hz ↦ (hKc hz.1).2)
      exact hp.continuousOn.inner (hH.clm_apply hq.continuousOn)
  -- Positive definiteness on a compact unit sphere supplies uniform positive bounds.
  have hpos (z : M × V) (hz : z ∈ K ×ˢ S) : 0 < Q z.1 z.2 z.2 := by
    obtain ⟨t, ht⟩ := hcore z.1 hz.1
    have heq : t.inner (WithLp.ofLp z.2) (WithLp.ofLp z.2) = Q z.1 z.2 z.2 :=
      ht _ _
    have hn := t.re_inner_nonneg (WithLp.ofLp z.2)
    change 0 ≤ t.inner (WithLp.ofLp z.2) (WithLp.ofLp z.2) at hn
    rw [← heq]
    apply lt_of_le_of_ne hn
    intro he
    have hzero := t.definite (WithLp.ofLp z.2) he.symm
    have hz0 : z.2 = 0 := by
      exact (WithLp.equiv 2 _).injective hzero
    simp [S, hz0] at hz
  obtain ⟨a, ha, hlow⟩ := (hK.prod hS).exists_forall_le' hcont hpos
  obtain ⟨B, hupper⟩ := ((hK.prod hS).image_of_continuousOn hcont).bddAbove
  let b := max B 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx F
  let z : V := WithLp.toLp 2 F
  obtain ⟨t, ht⟩ := hcore x hx
  have hdiag : Q x z z =
      ∑ p : Fin k → Fin n, ∑ q : Fin k → Fin n,
        (∏ s : Fin k, g.inner x
          (covectorFromChart c x (EuclideanSpace.single (p s) 1))
          (covectorFromChart c x (EuclideanSpace.single (q s) 1))) *
        ((h.toCore x).inner
          ((A.frameLinearEquiv i x (hKc hx).2).symm
            ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (F p)))
          ((A.frameLinearEquiv i x (hKc hx).2).symm
            ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (F q)))).re := by
    dsimp only [Q]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    have hp := A.pairing_eq_hermitianGramOperator h i x (hKc hx).2
      ((A.frameLinearEquiv i x (hKc hx).2).symm
        ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (F p)))
      ((A.frameLinearEquiv i x (hKc hx).2).symm
        ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (F q)))
    simpa only [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] using
      (congrArg Complex.re hp).symm
  change a * (∑ p, ‖F p‖ ^ 2) ≤ _ ∧ _ ≤ b * (∑ p, ‖F p‖ ^ 2)
  rw [← hdiag, ← PiLp.norm_sq_eq_of_L2 (fun _ : Fin k → Fin n ↦ W) z]
  by_cases hz : z = 0
  · have hzF : F = 0 := congrArg WithLp.ofLp hz
    have hqzero : Q x z z = 0 := by
      rw [← ht F F, hzF]
      let : InnerProductSpace.Core ℝ ((Fin k → Fin n) → W) := t
      exact InnerProductSpace.Core.inner_zero_left _
    rw [hqzero, hz]
    simp
  let y : V := ‖z‖⁻¹ • z
  have hy : y ∈ S := by
    simpa [S, y, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hz
  have hscale : ‖z‖ • y = z := by simp [y, smul_smul, norm_ne_zero_iff.mpr hz]
  have hqscale : Q x z z = Q x y y * ‖z‖ ^ 2 := by
    let : InnerProductSpace.Core ℝ ((Fin k → Fin n) → W) := t
    have hs := InnerProductSpace.Core.re_inner_smul_ofReal_smul_self
      (𝕜 := ℝ) (WithLp.ofLp y) (t := ‖z‖)
    change t.inner (‖z‖ • WithLp.ofLp y) (‖z‖ • WithLp.ofLp y) =
      t.inner (WithLp.ofLp y) (WithLp.ofLp y) * ‖z‖ * ‖z‖ at hs
    rw [ht, ht] at hs
    change Q x (‖z‖ • y) (‖z‖ • y) = Q x y y * ‖z‖ * ‖z‖ at hs
    rw [hscale] at hs
    simpa only [pow_two, mul_assoc] using hs
  rw [hqscale]
  exact ⟨mul_le_mul_of_nonneg_right (hlow (x, y) ⟨hx, hy⟩) (sq_nonneg ‖z‖),
    mul_le_mul_of_nonneg_right
      ((hupper ⟨(x, y), ⟨hx, hy⟩, rfl⟩).trans (le_max_left B 1)) (sq_nonneg ‖z‖)⟩

end SmoothComplexBundleAtlas

end AtiyahSinger
