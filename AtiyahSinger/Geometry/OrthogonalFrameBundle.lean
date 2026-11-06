/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothOrthogonalPrincipalBundle
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The orthogonal frame principal bundle of the original smooth real bundle

Public module ID: M1331.

A frame over x is an actual linear isometry from the fixed Euclidean model
to the original fiber. Its topology records the base point together with all
frame columns in the original vector-bundle total space. Recording the base
separately is essential in rank zero. The right orthogonal action is literal
precomposition with the existing orthogonal matrix representation.

One existence witness gives continuity of that action, a principal atlas with
smooth matrix transitions, and smoothness of the selected frame columns in
the original vector bundle. The last condition ties the principal atlas to
the original smooth structure; smooth transitions alone would not do so.
All subsequent selections retain this same witness and these original objects.

Sources: SG Appendix A, pp.370--372, and II.3, for orthogonal frame principal
bundles. Smooth local Gram--Schmidt in a supplied smooth positive metric is
the standard supplement constructed below. Mathlib supplies
ordinary smooth local frames and smooth metric evaluation, but its current
LocalFrame module lists the orthonormal-frame construction as future work.
No metric existence, global frame, positive rank or compactness is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Matrix.Norms.Elementwise

variable (r : ℕ) {B : Type*} (V : B → Type*)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]

/-- The standard orthogonal frame carrier, with its actual original fiber at each base point. -/
def OrthogonalFrameBundle : Type _ :=
  (x : B) × (EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] V x)

/-- The original base point of an orthogonal frame. -/
def orthogonalFrameProjection : OrthogonalFrameBundle r V → B :=
  fun p ↦ p.1

variable [TopologicalSpace B]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]

/-- The usual frame topology, retaining the base even when the column family is empty. -/
@[reducible]
def orthogonalFrameTopology : TopologicalSpace (OrthogonalFrameBundle r V) :=
  TopologicalSpace.induced
    (fun p : OrthogonalFrameBundle r V ↦
      (p.1, fun i : Fin r ↦
        (⟨p.1, p.2 (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin r)) V)))
    inferInstance

attribute [local instance] orthogonalFrameTopology

/-- Right multiplication of frames is precomposition by the original orthogonal isometry. -/
instance orthogonalFrameMulAction :
    MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ (OrthogonalFrameBundle r V) where
  smul A p := ⟨p.1, (orthogonalEuclideanIsometry r A.unop).trans p.2⟩
  one_smul p := by
    rcases p with ⟨x, f⟩
    change (⟨x, (orthogonalEuclideanIsometry r 1).trans f⟩ : OrthogonalFrameBundle r V) =
      ⟨x, f⟩
    rw [map_one]
    rfl
  mul_smul A C p := by
    rcases p with ⟨x, f⟩
    change (⟨x, (orthogonalEuclideanIsometry r (A * C).unop).trans f⟩ :
      OrthogonalFrameBundle r V) =
      ⟨x, (orthogonalEuclideanIsometry r A.unop).trans
        ((orthogonalEuclideanIsometry r C.unop).trans f)⟩
    rw [MulOpposite.unop_mul, map_mul]
    rfl

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] (I : ModelWithCorners ℝ EB HB) [ChartedSpace HB B]
  [hB : IsManifold I ∞ B]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [hV : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V I]
  [hMetric : IsContMDiffRiemannianBundle I ∞ (EuclideanSpace ℝ (Fin r)) V]

include hB hV hMetric

set_option linter.unusedSectionVars false in
/-- The original orthogonal frames have a smooth principal atlas compatible with the bundle. -/
theorem exists_smoothOrthogonalFrameAtlas :
    ∃ hAction : ContinuousSMul
        (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ (OrthogonalFrameBundle r V),
      letI := hAction
      ∃ S : SmoothOrthogonalPrincipalAtlas r I (orthogonalFrameProjection r V),
        ∀ (b : B) (i : Fin r),
          ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
            (fun x : B ↦
              let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
              (⟨p.1, p.2 (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
                TotalSpace (EuclideanSpace ℝ (Fin r)) V))
            (S.trivialization b).baseSet := by
  /- Stage 1: start with the original selected vector-bundle trivialization
  near each b and its standard smooth local frame. Apply finite Gram--Schmidt
  using the original fiber inner product. Smooth metric evaluation makes all
  Gram entries smooth. At each stage linear independence gives a strictly
  positive squared length, so division and positive square root preserve
  smoothness on the whole original chart domain. The resulting s_b(x) is
  an isometry from the fixed Euclidean model to the actual V_x. Each column
  is smooth as a section of that original bundle, not a new bundle atlas.
  Stage 2: the principal coordinates of p=(x,f) are (x,s_b(x) inverse*f).
  Their inverse sends (x,A) to (x,s_b(x)*A). Orthogonality identifies this
  change of frame with the original matrix orthogonal group. Both maps are
  continuous for the displayed frame topology: their entries are the original
  metric pairings of the columns, and the inverse columns are finite linear
  combinations of s_b(x)'s columns. The base coordinate is retained in rank
  zero, where the group and each frame fiber are singletons.
  Stage 3: precomposition fixes x and multiplies the principal group coordinate
  on the right, exactly gamma(p*A)=gamma(p)*A. Its column formula consists
  of finite sums with continuous matrix coefficients, proving joint continuity
  for the same action and topology. No replacement action is selected.
  Stage 4: the transition from chart b0 to chart b1 is
  s_b1(x) inverse*s_b0(x). Its matrix entries are smooth inner products of
  the two original smooth frame families on their actual overlap. This gives
  the required SmoothOrthogonalPrincipalAtlas in the specified direction.
  Stage 5: the frame at the inverse principal coordinate (x,1) is exactly
  s_b(x). Record smoothness of each actual column in the original total space
  in this same witness. On the baseSet its projection is x by the principal
  trivialization identity. This compatibility excludes a continuous nonsmooth
  gauge change whose abstract principal transition functions remain smooth.
  All steps are local; no separation, paracompactness, global orthonormal frame,
  positive rank or finite-dimensional assumption on the base model is needed. -/
  classical
  let F := EuclideanSpace ℝ (Fin r)
  let b₀ : OrthonormalBasis (Fin r) ℝ F := EuclideanSpace.basisFun (Fin r) ℝ
  let e (b : B) := trivializationAt F V b
  let U (b : B) : Set B := (e b).baseSet
  -- Complete each local basis pointwise outside its domain without changing that domain.
  let β (b x : B) : Module.Basis (Fin r) ℝ (V x) :=
    if hx : x ∈ U b then (e b).basisAt b₀.toBasis hx
    else (e x).basisAt b₀.toBasis (FiberBundle.mem_baseSet_trivializationAt' x)
  have hβ (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, β b x i⟩ : TotalSpace F V)) (U b) := by
    apply ((e b).contMDiffOn_localFrame_baseSet ∞ b₀.toBasis i).congr
    intro x hx
    simp [β, hx, Bundle.Trivialization.localFrame, U]
  let g (b : B) (i : Fin r) (x : B) : V x :=
    InnerProductSpace.gramSchmidt ℝ (β b x) i
  have hg_ne (b x : B) (i : Fin r) : g b i x ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero i (β b x).linearIndependent
  -- Smoothness follows inductively from the original metric's smooth inner products.
  have hg (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, g b i x⟩ : TotalSpace F V)) (U b) := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hcoeff (j : Fin r) (hj : j ∈ Finset.Iio i) :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun x ↦ inner ℝ (g b j x) (β b x i) / inner ℝ (g b j x) (g b j x))
            (U b) := by
        intro x hx
        exact ((ih j (Finset.mem_Iio.mp hj) x hx).inner_bundle (hβ b i x hx)).div₀
          ((ih j (Finset.mem_Iio.mp hj) x hx).inner_bundle
            (ih j (Finset.mem_Iio.mp hj) x hx))
          (inner_self_ne_zero.mpr (hg_ne b x j))
      have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
          (fun x ↦ (⟨x, ∑ j ∈ Finset.Iio i,
            (inner ℝ (g b j x) (β b x i) / inner ℝ (g b j x) (g b j x)) •
              g b j x⟩ : TotalSpace F V)) (U b) :=
        ContMDiffOn.sum_section fun j hj ↦
          (hcoeff j hj).smul_section (ih j (Finset.mem_Iio.mp hj))
      apply ((hβ b i).sub_section hsum).congr
      intro x _
      apply TotalSpace.mk_inj.mpr
      dsimp only [Pi.sub_apply]
      change InnerProductSpace.gramSchmidt ℝ (β b x) i = _
      rw [eq_sub_iff_add_eq]
      simpa only [real_inner_self_eq_norm_sq, RCLike.ofReal_real_eq_id, id_eq] using
        (InnerProductSpace.gramSchmidt_def'' ℝ (β b x) i).symm
  let o (b x : B) : OrthonormalBasis (Fin r) ℝ (V x) :=
    OrthonormalBasis.mk
      (InnerProductSpace.gramSchmidtNormed_orthonormal (β b x).linearIndependent)
      (by
        rw [InnerProductSpace.span_gramSchmidtNormed_range,
          InnerProductSpace.span_gramSchmidt, (β b x).span_eq])
  have ho (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, o b x i⟩ : TotalSpace F V)) (U b) := by
    have hnorm : ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ ‖g b i x‖) (U b) := by
      intro x hx
      have hs := (hg b i x hx).inner_bundle (hg b i x hx)
      have h := (Real.contDiffAt_sqrt
        (inner_self_ne_zero.mpr (hg_ne b x i))).comp_contMDiffWithinAt
          (f := fun y : B ↦ inner ℝ (g b i y) (g b i y)) hs
      simpa only [Function.comp_def, real_inner_self_eq_norm_sq,
        Real.sqrt_sq_eq_abs, abs_norm] using h
    have hinv : ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ ‖g b i x‖⁻¹) (U b) := by
      intro x hx
      exact (hnorm x hx).inv₀ (norm_ne_zero_iff.mpr (hg_ne b x i))
    simpa [o, OrthonormalBasis.coe_mk, InnerProductSpace.gramSchmidtNormed, g]
      using hinv.smul_section (hg b i)
  let s (b x : B) : F ≃ₗᵢ[ℝ] V x := (o b x).repr.symm
  have hs_basis (b x : B) (i : Fin r) : s b x (b₀ i) = o b x i := by
    change (o b x).repr.symm (EuclideanSpace.basisFun (Fin r) ℝ i) = _
    rw [EuclideanSpace.basisFun_apply, OrthonormalBasis.repr_symm_single]
  have hs (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
        (fun x ↦ (⟨x, s b x (b₀ i)⟩ : TotalSpace F V)) (U b) := by
    change ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun x ↦ (⟨x, (o b x).repr.symm (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
        TotalSpace F V)) (U b)
    simpa only [EuclideanSpace.basisFun_apply, OrthonormalBasis.repr_symm_single]
      using ho b i
  -- Matrix coordinates refer to the original orthogonal representation, in both directions.
  let G : Type := Matrix.orthogonalGroup (Fin r) ℝ
  let κ (A : F ≃ₗᵢ[ℝ] F) : G :=
    ⟨A.toLinearEquiv.toLinearMap.toMatrix b₀.toBasis b₀.toBasis,
      A.toMatrix_mem_unitaryGroup b₀ b₀⟩
  have hκ (A : F ≃ₗᵢ[ℝ] F) : orthogonalEuclideanIsometry r (κ A) = A := by
    apply LinearIsometryEquiv.toLinearEquiv_injective
    apply LinearEquiv.toLinearMap_injective
    change Matrix.toEuclideanLin
      (A.toLinearEquiv.toLinearMap.toMatrix b₀.toBasis b₀.toBasis) = A.toLinearEquiv.toLinearMap
    exact Matrix.toLin_toMatrix b₀.toBasis b₀.toBasis _
  have hκ' (A : G) : κ (orthogonalEuclideanIsometry r A) = A := by
    apply Subtype.ext
    change LinearMap.toMatrix b₀.toBasis b₀.toBasis (Matrix.toEuclideanLin A.val) = A.val
    exact LinearMap.toMatrix_toLin b₀.toBasis b₀.toBasis A.val
  have hκ_mul (A C : F ≃ₗᵢ[ℝ] F) : κ (C.trans A) = κ A * κ C := by
    apply Subtype.ext
    change LinearMap.toMatrix b₀.toBasis b₀.toBasis
      (A.toLinearEquiv.toLinearMap.comp C.toLinearEquiv.toLinearMap) = _
    exact LinearMap.toMatrix_comp b₀.toBasis b₀.toBasis b₀.toBasis _ _
  have hmodel (A : G) (j : Fin r) :
      orthogonalEuclideanIsometry r A (b₀ j) = ∑ i : Fin r, A.val i j • b₀ i :=
    Matrix.toLin_self b₀.toBasis b₀.toBasis A.val j
  let c (b : B) (p : OrthogonalFrameBundle r V) : G :=
    κ (p.2.trans (s b p.1).symm)
  have hc (b : B) (p : OrthogonalFrameBundle r V) (i j : Fin r) :
      (c b p).val i j = inner ℝ (o b p.1 i) (p.2 (b₀ j)) := by
    change (LinearMap.toMatrix b₀.toBasis b₀.toBasis
      (p.2.trans (s b p.1).symm).toLinearEquiv.toLinearMap) i j = _
    rw [LinearMap.toMatrix_apply]
    change ((o b p.1).repr (p.2 (b₀ j))) i = _
    exact (o b p.1).repr_apply_apply _ _
  let φ (b : B) : OrthogonalFrameBundle r V ≃ B × G :=
    { toFun := fun p ↦ (p.1, c b p)
      invFun := fun q ↦ ⟨q.1, (orthogonalEuclideanIsometry r q.2).trans (s b q.1)⟩
      left_inv := by
        rintro ⟨x, f⟩
        change (⟨x, (orthogonalEuclideanIsometry r
          (κ (f.trans (s b x).symm))).trans (s b x)⟩ : OrthogonalFrameBundle r V) = ⟨x, f⟩
        rw [hκ]
        apply congrArg (Sigma.mk x)
        ext v
        exact (s b x).apply_symm_apply (f v)
      right_inv := by
        rintro ⟨x, A⟩
        change (x, κ (((orthogonalEuclideanIsometry r A).trans (s b x)).trans
          (s b x).symm)) = (x, A)
        apply Prod.ext
        · rfl
        change κ (((orthogonalEuclideanIsometry r A).trans (s b x)).trans (s b x).symm) = A
        have h : ((orthogonalEuclideanIsometry r A).trans (s b x)).trans (s b x).symm =
            orthogonalEuclideanIsometry r A := by
          apply LinearIsometryEquiv.ext
          intro v
          exact (s b x).symm_apply_apply _
        rw [h, hκ'] }
  have hc_smul (b : B) (A : G) (p : OrthogonalFrameBundle r V) :
      c b (MulOpposite.op A • p) = c b p * A := by
    rcases p with ⟨x, f⟩
    change κ (((orthogonalEuclideanIsometry r A).trans f).trans (s b x).symm) =
      κ (f.trans (s b x).symm) * A
    rw [← LinearIsometryEquiv.trans_assoc, hκ_mul, hκ']
  -- Check both coordinate maps in the exact topology of base points and frame columns.
  let ι (p : OrthogonalFrameBundle r V) :=
    (p.1, fun i : Fin r ↦ (⟨p.1, p.2 (b₀ i)⟩ : TotalSpace F V))
  have hι : Topology.IsInducing ι := ⟨rfl⟩
  have hproj : Continuous (fun p : OrthogonalFrameBundle r V ↦ p.1) :=
    continuous_fst.comp hι.continuous
  have hcolumn (i : Fin r) :
      Continuous (fun p : OrthogonalFrameBundle r V ↦
        (⟨p.1, p.2 (b₀ i)⟩ : TotalSpace F V)) :=
    (continuous_apply i).comp (continuous_snd.comp hι.continuous)
  obtain ⟨metric, hmetric, hmetric_inner⟩ := hMetric.exists_contMDiff
  let : IsContinuousRiemannianBundle F V :=
    ⟨metric, hmetric.continuous, hmetric_inner⟩
  have hφ (b : B) : ContinuousOn (φ b) {p | p.1 ∈ U b} := by
    have hmatrix : ContinuousOn (fun p : OrthogonalFrameBundle r V ↦ (c b p).val)
        {p | p.1 ∈ U b} := by
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      have hsection := (ho b i).continuousOn.comp hproj.continuousOn (fun _ hx ↦ hx)
      exact (hsection.inner_bundle (hcolumn j).continuousOn).congr
        (fun p _ ↦ hc b p i j)
    have hcoordinate : ContinuousOn (c b) {p | p.1 ∈ U b} :=
      Topology.IsInducing.subtypeVal.continuousOn_iff.mpr hmatrix
    exact hproj.continuousOn.prodMk hcoordinate
  have hφ_symm_column (b : B) (j : Fin r) :
      ContinuousOn (fun q : B × G ↦
        (⟨q.1, ((φ b).symm q).2 (b₀ j)⟩ : TotalSpace F V)) (U b ×ˢ Set.univ) := by
    have hv (i : Fin r) :
        ContinuousOn (fun x : B ↦ (e b (⟨x, o b x i⟩ : TotalSpace F V)).2) (U b) :=
      ((e b).continuousOn.comp (ho b i).continuousOn
        (fun x hx ↦ (e b).mem_source.mpr hx)).snd
    have hsum : ContinuousOn (fun q : B × G ↦
        ∑ i : Fin r, q.2.val i j • (e b (⟨q.1, o b q.1 i⟩ : TotalSpace F V)).2)
        (U b ×ˢ Set.univ) := by
      apply continuousOn_finsetSum
      intro i _
      have hgroup : Continuous (fun A : G ↦ A.val) := continuous_subtype_val
      have ha : Continuous (fun q : B × G ↦ q.2.val i j) :=
        (continuous_apply j).comp
          ((continuous_apply i).comp (hgroup.comp continuous_snd))
      exact ha.continuousOn.smul
        ((hv i).comp continuous_fst.continuousOn (fun q hq ↦ hq.1))
    have hraw := (e b).toOpenPartialHomeomorph.continuousOn_invFun.comp
      (continuous_fst.continuousOn.prodMk hsum)
      (fun q hq ↦ (e b).mem_target.mpr hq.1)
    apply hraw.congr
    intro q hq
    have hvector : ((φ b).symm q).2 (b₀ j) =
        ∑ i : Fin r, q.2.val i j • o b q.1 i := by
      change (s b q.1) (orthogonalEuclideanIsometry r q.2 (b₀ j)) = _
      rw [hmodel, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hs_basis]
    have hcoords : e b (⟨q.1, ((φ b).symm q).2 (b₀ j)⟩ : TotalSpace F V) =
        (q.1, ∑ i : Fin r,
          q.2.val i j • (e b (⟨q.1, o b q.1 i⟩ : TotalSpace F V)).2) := by
      apply Prod.ext
      · exact (e b).coe_fst' hq.1
      · change ((e b).linearEquivAt ℝ q.1 hq.1) (((φ b).symm q).2 (b₀ j)) = _
        rw [hvector, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        rfl
    exact ((e b).left_inv ((e b).mem_source.mpr hq.1)).symm.trans
      (congrArg (e b).toOpenPartialHomeomorph.symm hcoords)
  have hφ_symm (b : B) : ContinuousOn (φ b).symm (U b ×ˢ Set.univ) := by
    apply hι.continuousOn_iff.mpr
    exact continuous_fst.continuousOn.prodMk
      (continuousOn_pi.mpr (hφ_symm_column b))
  let t (b : B) : Trivialization G (orthogonalFrameProjection r V) :=
    { toFun := φ b
      invFun := (φ b).symm
      source := {p | p.1 ∈ U b}
      target := U b ×ˢ Set.univ
      map_source' := fun {_} hp ↦ ⟨hp, Set.mem_univ _⟩
      map_target' := fun {_} hq ↦ hq.1
      left_inv' := fun {_} _ ↦ (φ b).left_inv _
      right_inv' := fun {_} _ ↦ (φ b).right_inv _
      continuousOn_toFun := hφ b
      continuousOn_invFun := hφ_symm b
      open_source := (e b).open_baseSet.preimage hproj
      open_target := (e b).open_baseSet.prod isOpen_univ
      baseSet := U b
      open_baseSet := (e b).open_baseSet
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  -- Principal transitions are the original metric pairings of two local smooth frames.
  have ht_transition (b₁ b₂ : B) :
      ContMDiffOn I 𝓘(ℝ, Fin r → Fin r → ℝ) ∞
        (fun x i j ↦ (t b₂ ((t b₁).toOpenPartialHomeomorph.symm (x, 1))).2.val i j)
        ((t b₁).baseSet ∩ (t b₂).baseSet) := by
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    have hinner := ((ho b₂ i).mono Set.inter_subset_right).inner_bundle
      ((ho b₁ j).mono Set.inter_subset_left)
    apply hinner.congr
    intro x _
    change (c b₂ ((φ b₁).symm (x, 1))).val i j = _
    rw [hc]
    change inner ℝ (o b₂ x i) ((s b₁ x) (orthogonalEuclideanIsometry r 1 (b₀ j))) = _
    rw [map_one]
    exact congrArg (inner ℝ (o b₂ x i)) (hs_basis b₁ x j)
  have hAction : ContinuousSMul Gᵐᵒᵖ (OrthogonalFrameBundle r V) := by
    constructor
    rw [continuous_iff_continuousAt]
    rintro ⟨A, p⟩
    let b := p.1
    have hp : p ∈ (t b).source :=
      (t b).mem_source.mpr (FiberBundle.mem_baseSet_trivializationAt' b)
    have hcoord : ContinuousAt
        (fun q : Gᵐᵒᵖ × OrthogonalFrameBundle r V ↦
          (q.2.1, c b q.2 * q.1.unop)) (A, p) := by
      have hchart : ContinuousAt
          (fun q : Gᵐᵒᵖ × OrthogonalFrameBundle r V ↦ t b q.2) (A, p) :=
        ((t b).toOpenPartialHomeomorph.continuousAt hp).comp
          (f := fun q : Gᵐᵒᵖ × OrthogonalFrameBundle r V ↦ q.2)
          continuous_snd.continuousAt
      exact (hproj.continuousAt.comp continuous_snd.continuousAt).prodMk
        (hchart.snd.mul ((MulOpposite.continuous_unop.comp continuous_fst).continuousAt))
    have htgt : (p.1, c b p * A.unop) ∈ (t b).target :=
      (t b).mem_target.mpr (FiberBundle.mem_baseSet_trivializationAt' b)
    have hlocal : ContinuousAt
        (fun q : Gᵐᵒᵖ × OrthogonalFrameBundle r V ↦
          (φ b).symm (q.2.1, c b q.2 * q.1.unop)) (A, p) :=
      ((t b).toOpenPartialHomeomorph.continuousAt_symm htgt).comp
        (f := fun q : Gᵐᵒᵖ × OrthogonalFrameBundle r V ↦
          (q.2.1, c b q.2 * q.1.unop)) hcoord
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [] with q
    change q.1 • q.2 = (φ b).symm (q.2.1, c b q.2 * q.1.unop)
    rw [← hc_smul]
    exact ((φ b).symm_apply_apply (q.1 • q.2)).symm
  refine ⟨hAction, ⟨?_, ?_⟩⟩
  · exact
      { projection_smul := fun _ _ ↦ rfl
        trivialization := t
        mem_baseSet := fun b ↦ FiberBundle.mem_baseSet_trivializationAt' b
        equivariant := fun b A p _ ↦ hc_smul b A p
        contMDiffOn_transition := ht_transition }
  · intro b i
    change ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun x ↦ (⟨x, (s b x) (orthogonalEuclideanIsometry r 1 (b₀ i))⟩ :
        TotalSpace F V)) (U b)
    simpa only [map_one, LinearIsometryEquiv.coe_one, id_eq] using hs b i

set_option linter.defProp false in
/-- Joint continuity for the same right action, selected with its compatible principal atlas. -/
@[reducible]
def continuousSMul_orthogonalFrame :
    ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ (OrthogonalFrameBundle r V) :=
  (exists_smoothOrthogonalFrameAtlas r V I).choose

/-- The smooth principal atlas selected for the actual orthogonal frame bundle. -/
def smoothOrthogonalFrameAtlas :
    SmoothOrthogonalPrincipalAtlas r I (orthogonalFrameProjection r V) :=
  (exists_smoothOrthogonalFrameAtlas r V I).choose_spec.choose

/-- The selected principal sections are smooth frames for the original vector-bundle atlas. -/
theorem contMDiffOn_orthogonalFrameAtlas_columns (b : B) (i : Fin r) :
    ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin r))) ∞
      (fun x : B ↦
        let e := (smoothOrthogonalFrameAtlas r V I).trivialization b
        let p := e.toOpenPartialHomeomorph.symm (x, 1)
        (⟨p.1, p.2 (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin r)) V))
      ((smoothOrthogonalFrameAtlas r V I).trivialization b).baseSet := by
  /- Unfold only the specified atlas selection and take the column-compatibility
  component of that same existence witness. Its local section uses the actual
  inverse principal chart at (x,1); on the chart baseSet the original projection
  is x. No independently chosen atlas or frame family is substituted. -/
  exact (exists_smoothOrthogonalFrameAtlas r V I).choose_spec.choose_spec b i

end AtiyahSinger
