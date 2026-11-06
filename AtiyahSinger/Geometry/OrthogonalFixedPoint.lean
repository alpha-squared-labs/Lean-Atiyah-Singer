/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereTangentCoordinates
public import AtiyahSinger.Geometry.TangentEmbedding

/-!
# Actual charts for a specified equivariant point inclusion

Public module ID: M1330.

P07, SG III.13, Lemma 13.7, printed p.253. The input is any specified
smooth map from the original zero-dimensional Euclidean point into the original
sphere. Its equivariance condition says that every value is fixed by O(r),
which is precisely equivariance for the trivial action on its one-point source.
No second group action or special predicate is introduced.

The chart is specified by its full rational ambient formula at that actual point.
Its proof computes the fixed locus, identifies the specified point with its
actual pole, and reuses the normalized pole chart with that full formula.
Its derivative
then gives a genuine tangent chart with the normal displacement followed by
the vertical tangent displacement. The horizontal derivative at zero is twice
the original frame; both real coordinates receive the same positive scaling.
The input inclusion, native sphere atlas and native tangent topology remain fixed.
Dimension zero is included. The proofs retain the original rational map,
its native derivative and its same-point equivariant tangent parametrization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent

set_option maxSynthPendingDepth 30

variable {r : ℕ}

/-- Any specified smooth map from the actual point is a proper smooth point embedding. -/
theorem orthogonalSpherePointEmbedding_properties
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞) :
    IsSmoothEmbedding (𝓡 0) (𝓡 r) ∞ j ∧ IsProperMap j := by
  /- Stage 1: the original source is a singleton, so j equals its constant
  value at zero. Its supplied smoothness is unchanged. The actual derivative
  has zero-dimensional domain and hence is injective, with complemented
  zero image and the unique continuous left inverse onto that domain.
  Thus j is an immersion and a topological embedding of the same singleton.
  Stage 2: this source is compact and the original sphere is Hausdorff.
  The existing compact-source criterion gives properness of the same j.
  No equivariance or positive-dimensional assumption is needed here. -/
  classical
  let V₀ := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin r)
  let a : OrthogonalSphere r := -(j 0)
  let e := stereographic' r a
  have hmem : e ∈ IsManifold.maximalAtlas (𝓡 r) ∞ (OrthogonalSphere r) :=
    IsManifold.subset_maximalAtlas ⟨a, rfl⟩
  have hpoint : ∀ x : V₀, j x = j 0 := fun x ↦ congrArg j (Subsingleton.elim x 0)
  have hsource (x : V₀) : j x ∈ e.source := by
    rw [stereographic'_source, hpoint]
    exact ne_neg_of_mem_unit_sphere ℝ (j 0)
  have hcenter : e (j 0) = 0 := by
    change (OrthonormalBasis.fromOrthogonalSpanSingleton r
      (ne_zero_of_mem_unit_sphere a)).repr (stereographic (norm_eq_of_mem_sphere a) (j 0)) = 0
    have ha : j 0 = -a := by simp [a]
    rw [ha, stereographic_apply_neg, map_zero]
  -- Use an actual centered native sphere chart and the full target as complement.
  have himm : IsImmersionOfComplement V (𝓡 0) (𝓡 r) ∞ j := by
    intro x
    refine IsImmersionAtOfComplement.mk_of_charts
      (ContinuousLinearEquiv.uniqueProd ℝ V V₀)
      (OpenPartialHomeomorph.refl V₀) e ?_ (hsource x) ?_ hmem ?_ ?_
    · trivial
    · exact IsManifold.subset_maximalAtlas rfl
    · intro y hy
      exact hsource y
    · intro y hy
      change e (j _) = 0
      rw [hpoint]
      exact hcenter
  -- The singleton source is compact; the original sphere is Hausdorff.
  exact ⟨⟨himm.isImmersion, IsEmbedding.of_subsingleton j⟩,
    j.contMDiff.continuous.isProperMap⟩

/-- The specified rational chart of the actual fixed point, with its normal-frame certificate. -/
theorem exists_orthogonalSphereFixedPointChart
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x) :
    ∃ f : ContMDiffMap (𝓡 r) (𝓡 r)
        (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r) ∞,
      (∀ u : EuclideanSpace ℝ (Fin r),
        (f u : OrthogonalSphereAmbient r) =
          WithLp.toLp 2
            (((2 : ℝ) / (1 + ‖u‖ ^ 2)) • u,
              (j 0).val.snd * (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2))) ∧
      f 0 = j 0 ∧ IsOpenEmbedding f ∧ Set.range f = {-(j 0)}ᶜ ∧
      (∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (u : EuclideanSpace ℝ (Fin r)),
        f (orthogonalEuclideanIsometry r A u) = A • f u) ∧
      ∀ v : EuclideanSpace ℝ (Fin r),
        mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r)
          (fun x : OrthogonalSphere r ↦ x.val) (f 0)
          (mfderiv (𝓡 r) (𝓡 r) f 0 v) = WithLp.toLp 2 ((2 : ℝ) • v, 0) := by
  /- Stage 1: apply hj to the original orthogonal matrix -I. Its action
  negates the horizontal component of j(0) and fixes its height, forcing
  the horizontal component to be zero. The sphere equation gives height
  squared equal to one. At r=0 the horizontal space is already zero, and
  the same height equation applies; no separate normalization is assumed.
  Stage 2: the displayed rational expression has norm one, equals j(0)
  at zero, and misses only -j(0). Its inverse on that complement is the
  horizontal coordinate divided by one plus height(j(0))*height(x).
  The denominator is nonzero there. These mutually inverse formulas are
  smooth in the original sphere charts, so they define this actual smooth
  open embedding, including the one-point open subset when r=0.
  Stage 3: the native orthogonal action preserves the horizontal norm and
  the height, so the same formula is equivariant for the original real
  matrix action. Differentiate it at zero in the actual ambient inclusion.
  Its horizontal derivative is 2v and its height derivative is zero.
  This is the actual frame of the normal of j, since dj has zero range;
  no arbitrary equal-dimensional normal space replaces that quotient. -/
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  -- The original -I action negates precisely the horizontal coordinate.
  have hneg := congrArg (fun x : OrthogonalSphere r ↦ x.val.fst) (hj (-1) 0)
  change Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ)
      (-1 : Matrix (Fin r) (Fin r) ℝ) (j 0).val.fst =
    (j 0).val.fst at hneg
  rw [map_neg, map_one] at hneg
  have hhorizontal : (j 0).val.fst = 0 := by
    ext i
    have hi := congrArg (fun u : V ↦ u i) hneg
    change -(j 0).val.fst i = (j 0).val.fst i at hi
    change (j 0).val.fst i = 0
    linarith
  have hheight : (j 0).val.snd = 1 ∨ (j 0).val.snd = -1 := by
    have hn : ‖(j 0).val‖ = 1 := norm_eq_of_mem_sphere (j 0)
    have hs := WithLp.prod_norm_sq_eq_of_L2 (j 0).val
    rw [hn, hhorizontal, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hs
    have hsq : (j 0).val.snd ^ 2 = 1 := by
      simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hs.symm
    exact sq_eq_one_iff.mp hsq
  obtain ⟨b, hb⟩ : ∃ b : Bool, j 0 = orthogonalSpherePole r b := by
    rcases hheight with hp | hp
    · refine ⟨true, ?_⟩
      apply Subtype.ext
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hhorizontal
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hp
    · refine ⟨false, ?_⟩
      apply Subtype.ext
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hhorizontal
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hp
  -- Identify the full rational formula with the native normalized inverse chart.
  let e := orthogonalSphereNormalizedChart r b
  let f : ContMDiffMap (𝓡 r) (𝓡 r) V (OrthogonalSphere r) ∞ :=
    ⟨e.symm, (orthogonalSphereNormalizedChart_smooth r b).2⟩
  have hformula (u : V) : (f u : W) =
      WithLp.toLp 2 (((2 : ℝ) / (1 + ‖u‖ ^ 2)) • u,
        (j 0).val.snd * (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2)) := by
    rw [hb]
    change ((e.symm u : OrthogonalSphere r) : W) = _
    rw [orthogonalSphereNormalizedChart_inverse_formula]
    cases b <;> simp [orthogonalSpherePole, orthogonalSphereNorth]
  have hzero : f 0 = j 0 :=
    (orthogonalSphereNormalizedChart_properties r b).2.2.1.trans hb.symm
  have htarget : e.target = Set.univ :=
    (orthogonalSphereNormalizedChart_properties r b).2.1
  have hopposite : orthogonalSpherePole r (!b) = -(j 0) := by
    rw [hb]
    cases b <;> simp [orthogonalSpherePole]
  have hrange : Set.range f = {-(j 0)}ᶜ := by
    rw [← hopposite, ← (orthogonalSphereNormalizedChart_properties r b).1]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact e.map_target (htarget.symm ▸ Set.mem_univ u)
    · intro hx
      exact ⟨e x, e.left_inv hx⟩
  have hequiv (A : Matrix.orthogonalGroup (Fin r) ℝ) (u : V) :
      f (orthogonalEuclideanIsometry r A u) = A • f u := by
    apply Subtype.ext
    change (f (orthogonalEuclideanIsometry r A u) : W) =
      orthogonalSphereBlockIsometry r A (f u : W)
    rw [hformula, hformula]
    change WithLp.toLp 2
        ((2 / (1 + ‖orthogonalEuclideanIsometry r A u‖ ^ 2)) •
          orthogonalEuclideanIsometry r A u,
          (j 0).val.snd * (1 - ‖orthogonalEuclideanIsometry r A u‖ ^ 2) /
            (1 + ‖orthogonalEuclideanIsometry r A u‖ ^ 2)) =
      WithLp.toLp 2
        (orthogonalEuclideanIsometry r A ((2 / (1 + ‖u‖ ^ 2)) • u),
          (j 0).val.snd * (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2))
    rw [(orthogonalEuclideanIsometry r A).norm_map, map_smul]
  refine ⟨f, hformula, hzero, e.symm.isOpenEmbedding htarget, hrange, hequiv, ?_⟩
  -- Differentiate the exact ambient formula at zero; both real coordinates use scale two.
  intro v
  have hn := (hasStrictFDerivAt_norm_sq (0 : V)).hasFDerivAt
  have hi := (hasFDerivAt_inv (by norm_num : (1 : ℝ) + ‖(0 : V)‖ ^ 2 ≠ 0)).comp
    (0 : V) ((hasFDerivAt_const (1 : ℝ) (0 : V)).add hn)
  have hh := ((hasFDerivAt_const (2 : ℝ) (0 : V)).mul hi).smul
    (hasFDerivAt_id (0 : V))
  have hv := ((hasFDerivAt_const ((j 0).val.snd) (0 : V)).mul
    ((hasFDerivAt_const (1 : ℝ) (0 : V)).sub hn)).mul hi
  let p := (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.toContinuousLinearMap
  have hp := p.hasFDerivAt.comp (0 : V) (hh.prodMk hv)
  have hfun : (fun u : V ↦ ((f u : OrthogonalSphere r) : W)) =
      (fun u : V ↦ WithLp.toLp 2
        (((2 : ℝ) * (1 + ‖u‖ ^ 2)⁻¹) • u,
          ((j 0).val.snd * (1 - ‖u‖ ^ 2)) * (1 + ‖u‖ ^ 2)⁻¹)) := by
    funext u
    simpa only [div_eq_mul_inv] using hformula u
  change HasFDerivAt (𝕜 := ℝ) (fun u : V ↦ WithLp.toLp 2
    (((2 : ℝ) * (1 + ‖u‖ ^ 2)⁻¹) • u,
      ((j 0).val.snd * (1 - ‖u‖ ^ 2)) * (1 + ‖u‖ ^ 2)⁻¹)) _ (0 : V) at hp
  rw [← hfun] at hp
  have hinc : MDifferentiable (𝓡 r) 𝓘(ℝ, W) (fun x : OrthogonalSphere r ↦ x.val) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)
  erw [← mfderiv_comp_apply (0 : V) (hinc (f 0))
    (f.contMDiff.mdifferentiable (by simp) 0) v]
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (fun u : V ↦ ((f u : OrthogonalSphere r) : W)) 0 v = _
  rw [hp.fderiv]
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [p, V]

/-- The actual fixed-point chart selected with its complete ambient and differential formula. -/
def orthogonalSphereFixedPointChart
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x) :
    ContMDiffMap (𝓡 r) (𝓡 r)
      (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r) ∞ :=
  (exists_orthogonalSphereFixedPointChart j hj).choose

/-- The actual derivative lift of that chart, in normal-base then vertical complex coordinates. -/
def orthogonalSphereFixedPointTangentMap
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x)
    (z : EuclideanSpace ℂ (Fin r)) : TangentBundle (𝓡 r) (OrthogonalSphere r) :=
  let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).re)
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).im)
  let f := orthogonalSphereFixedPointChart j hj
  ⟨f u, mfderiv (𝓡 r) (𝓡 r) f u v⟩

/-- The actual tangent lift is an equivariant open normal chart centered at the specified point. -/
theorem orthogonalSphereFixedPointTangentMap_properties
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x) :
    IsOpenEmbedding (orthogonalSphereFixedPointTangentMap j hj) ∧
      orthogonalSphereFixedPointTangentMap j hj 0 =
        (⟨j 0, 0⟩ : TangentBundle (𝓡 r) (OrthogonalSphere r)) ∧
      ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : EuclideanSpace ℂ (Fin r)),
        orthogonalSphereFixedPointTangentMap j hj (A • z) =
          A • orthogonalSphereFixedPointTangentMap j hj z := by
  /- Stage 1: the fixed-point equation and full rational chart formula
  identify j(0) with its actual pole and identify the base map with the
  normalized pole chart. Equality of these base maps identifies their
  native tangent maps in the same real/imaginary coordinate order.
  Reuse the pole tangent chart's open-embedding theorem.
  Stage 2: the original chart sends zero to j(0); its linear derivative
  sends the zero imaginary vector to zero in that same tangent fiber.
  Reuse the pole tangent chart's equivariance after the map equality.
  This keeps the original derivative action, with normal-base before
  vertical displacement. The chart need not be proper. -/
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  let f := orthogonalSphereFixedPointChart j hj
  have hf := (exists_orthogonalSphereFixedPointChart j hj).choose_spec
  have hzero : f 0 = j 0 := hf.2.1
  have hformula (u : V) : (f u : W) =
      WithLp.toLp 2 (((2 : ℝ) / (1 + ‖u‖ ^ 2)) • u,
        (j 0).val.snd * (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2)) := hf.1 u
  -- The selected chart's exact formula identifies the same fixed pole.
  have hhorizontal : (j 0).val.fst = 0 := by
    have h := congrArg (fun w : W ↦ w.fst) (hformula 0)
    simpa [hzero] using h
  have hheight : (j 0).val.snd = 1 ∨ (j 0).val.snd = -1 := by
    have hn : ‖(j 0).val‖ = 1 := norm_eq_of_mem_sphere (j 0)
    have hs := WithLp.prod_norm_sq_eq_of_L2 (j 0).val
    rw [hn, hhorizontal, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hs
    have hsq : (j 0).val.snd ^ 2 = 1 := by
      simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hs.symm
    exact sq_eq_one_iff.mp hsq
  obtain ⟨b, hb⟩ : ∃ b : Bool, j 0 = orthogonalSpherePole r b := by
    rcases hheight with hp | hp
    · refine ⟨true, ?_⟩
      apply Subtype.ext
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hhorizontal
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hp
    · refine ⟨false, ?_⟩
      apply Subtype.ext
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hhorizontal
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hp
  have hchart : (orthogonalSphereFixedPointChart j hj : V → OrthogonalSphere r) =
      (orthogonalSphereNormalizedChart r b).symm := by
    funext u
    apply Subtype.ext
    change (f u : W) = _
    rw [hformula, orthogonalSphereNormalizedChart_inverse_formula, hb]
    cases b <;> simp [orthogonalSpherePole, orthogonalSphereNorth]
  -- Equality of the original base maps identifies their actual native differentials.
  have htangent : orthogonalSphereFixedPointTangentMap j hj =
      (orthogonalSphereTangentChart r b : EuclideanSpace ℂ (Fin r) →
        TangentBundle (𝓡 r) (OrthogonalSphere r)) := by
    funext z
    exact congrArg (fun g : V → OrthogonalSphere r ↦ tangentMap (𝓡 r) (𝓡 r) g
      (⟨WithLp.toLp 2 (fun i ↦ (z i).re), WithLp.toLp 2 (fun i ↦ (z i).im)⟩ :
        TangentBundle (𝓡 r) V)) hchart
  refine ⟨?_, ?_, ?_⟩
  · rw [htangent]
    exact orthogonalSphereTangentChart_isOpenEmbedding r b
  · -- The zero imaginary vector is sent to zero in that very tangent fiber.
    have hre : (WithLp.toLp 2 (fun i : Fin r ↦ ((0 : EuclideanSpace ℂ (Fin r)) i).re) :
        V) = 0 := by ext i; simp
    have him : (WithLp.toLp 2 (fun i : Fin r ↦ ((0 : EuclideanSpace ℂ (Fin r)) i).im) :
        V) = 0 := by ext i; simp
    change (⟨f _, mfderiv (𝓡 r) (𝓡 r) f _ _⟩ :
      TangentBundle (𝓡 r) (OrthogonalSphere r)) = ⟨j 0, 0⟩
    rw [hre, him]
    apply TotalSpace.ext hzero
    apply heq_of_eq
    exact (mfderiv (𝓡 r) (𝓡 r) f (0 : V)).map_zero
  · intro A z
    rw [htangent]
    exact orthogonalSphereTangentChart_equivariant r b A z

/-- The fixed-point tangent chart as the actual continuous open map used for K extension. -/
def orthogonalSphereFixedPointTangentTube
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x) :
    C(EuclideanSpace ℂ (Fin r), TangentBundle (𝓡 r) (OrthogonalSphere r)) where
  toFun := orthogonalSphereFixedPointTangentMap j hj
  continuous_toFun := (orthogonalSphereFixedPointTangentMap_properties j hj).1.continuous

end AtiyahSinger
