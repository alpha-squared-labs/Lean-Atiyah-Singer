/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.ModelBundleTopology
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# The actual Hermitian full flag bundle

Public module ID: M1882.

An ordered orthogonal flag is represented by its rank-one, self-adjoint
projections, which sum to the identity on the original fiber. The total topology
is induced from the original endomorphism bundle and retains the base coordinate
explicitly, including in rank zero. The given Hermitian metric is used as form
data and does not replace the original fiber norms or total-space topology.

This is the projection description of Hatcher, Vector Bundles and K-Theory,
Section 1.1, p.16: ordered orthogonal lines in the same fiber. The local products
below are constructed directly on these projection tuples. Hatcher Section 3.1,
Proposition 3.3, pp.80--81, gives the iterated projective-bundle description.
SG III.11.1 additionally requests a smooth proper map. Properness and,
with smooth bundle and metric data, the smooth atlas are supplied separately
in `Geometry.HermitianFlagManifold` on this same projection space.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

/-- The standard full flag space as ordered orthogonal rank-one projections. -/
abbrev HermitianFlagSpace (r : ℕ) (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℂ V] (h : InnerProductSpace.Core ℂ V) : Type _ :=
  {P : Fin r → (V →L[ℂ] V) //
    (∀ i, (P i).comp (P i) = P i) ∧
    (∀ i, Module.finrank ℂ (LinearMap.range (P i).toLinearMap) = 1) ∧
    (∀ i j, i ≠ j → (P i).comp (P j) = 0) ∧
    (∑ i, P i) = ContinuousLinearMap.id ℂ V ∧
    ∀ i u v, h.inner (P i u) v = h.inner u (P i v)}

variable (r : ℕ) {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

/-- Ordered orthogonal flags in the actual original fibers of the bundle. -/
def HermitianFlagBundle : Type _ :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  (x : X) × HermitianFlagSpace r (E x) (h.toCore x)

variable [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- The ordinary flag topology induced by the native endomorphism-bundle topology. -/
@[reducible]
def hermitianFlagTopology : TopologicalSpace (HermitianFlagBundle r E h) :=
  TopologicalSpace.induced
    (fun p : HermitianFlagBundle r E h ↦
      (p.1, fun i : Fin r ↦
        (⟨p.1, p.2.val i⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
            (fun x ↦ E x →L[ℂ] E x))))
    inferInstance

attribute [local instance] hermitianFlagTopology

/-- The original base projection of the actual flag bundle. -/
def hermitianFlagProjection : C(HermitianFlagBundle r E h, X) where
  toFun := fun p ↦ p.1
  continuous_toFun := by
    -- Keep the base component of the defining induced-topology map.
    have htotal : Continuous (fun p : HermitianFlagBundle r E h ↦
        (p.1, fun i : Fin r ↦
          (⟨p.1, p.2.val i⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
              (fun x ↦ E x →L[ℂ] E x)))) := continuous_induced_dom
    exact continuous_fst.comp htotal

/-- Original local frames give local trivializations with the standard full flag fiber. -/
theorem exists_hermitianFlagTrivialization (x : X) :
    ∃ e : Trivialization
      (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore)
      (hermitianFlagProjection r E h : HermitianFlagBundle r E h → X),
      x ∈ e.baseSet := by
  /- Stage 1: take an original linear bundle chart around x. Apply finite
  Gram--Schmidt to its local frame using h. Joint continuity of the given
  positive form makes each normalization continuous; its denominator is
  strictly positive by linear independence. This gives continuous isometries
  from the fixed standard Hermitian space to the original fibers on that chart.
  Stage 2: transport every tuple of projections by conjugation with this frame.
  Conjugation preserves rank, idempotence, annihilation, the sum identity and
  self-adjointness for the specified forms. Its inverse is conjugation by the
  inverse frame. Native Hom-bundle coordinates show both maps are continuous
  for precisely the displayed induced topology.
  Stage 3: when r=0, every original fiber is zero-dimensional and the empty
  projection family is unique. The separate base coordinate gives the same
  local chart with singleton flag fiber. No nonzero-rank assumption, global
  frame, compactness or paracompactness of the base is used. -/
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let : ∀ y, FiniteDimensional ℂ (E y) := fun y ↦
    VectorBundle.finiteDimensional ℂ V E y
  let e := trivializationAt V E x
  let U : Set X := e.baseSet
  let b₀ : OrthonormalBasis (Fin r) ℂ V := EuclideanSpace.basisFun (Fin r) ℂ
  -- Complete the chosen original frame outside its domain only to totalize the formulas.
  let β (y : X) : Module.Basis (Fin r) ℂ (E y) :=
    if hy : y ∈ U then b₀.toBasis.map (e.linearEquivAt ℂ y hy).symm
    else b₀.toBasis.map ((trivializationAt V E y).linearEquivAt ℂ y
      (mem_baseSet_trivializationAt V E y)).symm
  have hcoord (v : ∀ y : X, E y)
      (hv : ContinuousOn (fun y ↦ (e ⟨y, v y⟩).2) U) :
      ContinuousOn (fun y ↦ (⟨y, v y⟩ : TotalSpace V E)) U := by
    have hinv := e.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_id.continuousOn.prodMk hv)
      (fun y hy ↦ e.mem_target.mpr hy)
    apply hinv.congr
    intro y hy
    exact (e.symm_apply_mk_proj (e.mem_source.mpr hy)).symm
  have hcoordinates (v : ∀ y : X, E y)
      (hv : ContinuousOn (fun y ↦ (⟨y, v y⟩ : TotalSpace V E)) U) :
      ContinuousOn (fun y ↦ (e ⟨y, v y⟩).2) U :=
    (e.continuousOn.comp hv (fun y hy ↦ e.mem_source.mpr hy)).snd
  have hβ (i : Fin r) :
      ContinuousOn (fun y ↦ (⟨y, β y i⟩ : TotalSpace V E)) U := by
    apply hcoord
    apply (continuous_const (y := b₀ i)).continuousOn.congr
    intro y hy
    change (e ⟨y, β y i⟩).2 = b₀ i
    simp only [β, dite_eq_left hy, Module.Basis.map_apply]
    exact (e.linearEquivAt ℂ y hy).apply_symm_apply (b₀ i)
  let := modelTopology V E
  let := sumTopology (E := E) (F := E)
  have hpair (v w : ∀ y : X, E y)
      (hv : ContinuousOn (fun y ↦ (⟨y, v y⟩ : TotalSpace V E)) U)
      (hw : ContinuousOn (fun y ↦ (⟨y, w y⟩ : TotalSpace V E)) U) :
      ContinuousOn (fun y ↦ (h.toCore y).inner (v y) (w y)) U := by
    have hdouble : ContinuousOn
        (fun y ↦ (⟨y, v y, w y⟩ : TotalSpace Unit (E ×ᵇ E))) U := by
      have hinducing : Topology.IsInducing
          (fun z : TotalSpace Unit (E ×ᵇ E) ↦
            ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit E),
              (⟨z.proj, z.snd.2⟩ : TotalSpace Unit E))) := ⟨rfl⟩
      apply hinducing.continuousOn_iff.mpr
      exact ((continuous_unitTotalEquiv_symm V E).comp_continuousOn hv).prodMk
        ((continuous_unitTotalEquiv_symm V E).comp_continuousOn hw)
    exact h.continuous_pairing.comp_continuousOn hdouble
  -- Gram--Schmidt uses the supplied form; its auxiliary norms never replace bundle topology.
  let H := h.toCore
  let originalModule : ∀ y : X, Module ℂ (E y) := fun y ↦ inferInstance
  let normed (y : X) : PLift (NormedAddCommGroup (E y)) :=
    ⟨(H y).toNormedAddCommGroup⟩
  let metric (y : X) :
      letI := (normed y).down
      letI := originalModule y
      PLift (InnerProductSpace ℂ (E y)) :=
    letI := (normed y).down
    letI := originalModule y
    ⟨InnerProductSpace.ofCore (H y).toCore⟩
  let g (i : Fin r) (y : X) : E y :=
    letI := (normed y).down
    letI := originalModule y
    letI := (metric y).down
    InnerProductSpace.gramSchmidt ℂ (β y) i
  let length (i : Fin r) (y : X) : ℝ :=
    letI := (normed y).down
    letI := originalModule y
    ‖g i y‖
  have hg_ne (i : Fin r) (y : X) : g i y ≠ 0 := by
    let := (normed y).down
    let := originalModule y
    let := (metric y).down
    exact InnerProductSpace.gramSchmidt_ne_zero i (β y).linearIndependent
  have hlength_ne (i : Fin r) (y : X) : length i y ≠ 0 := by
    let := (normed y).down
    let := originalModule y
    exact norm_ne_zero_iff.mpr (hg_ne i y)
  have hlength_eq (i : Fin r) (y : X) :
      length i y = Real.sqrt ((H y).inner (g i y) (g i y)).re := rfl
  have hg (i : Fin r) :
      ContinuousOn (fun y ↦ (⟨y, g i y⟩ : TotalSpace V E)) U := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hl (j : Fin r) (hj : j < i) : ContinuousOn (length j) U := by
        have hl := Real.continuous_sqrt.comp_continuousOn
          (Complex.continuous_re.comp_continuousOn (hpair (g j) (g j)
            (ih j hj) (ih j hj)))
        exact hl.congr (fun y _ ↦ hlength_eq j y)
      have hc (j : Fin r) (hj : j ∈ Finset.Iio i) : ContinuousOn
          (fun y ↦ (H y).inner (g j y) (β y i) /
            (length j y : ℂ) ^ 2) U := by
        exact (hpair (g j) (fun y ↦ β y i) (ih j (Finset.mem_Iio.mp hj))
          (hβ i)).div
          ((Complex.continuous_ofReal.comp_continuousOn
            (hl j (Finset.mem_Iio.mp hj))).pow 2)
          (fun y _ ↦ pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hlength_ne j y)))
      have hsum : ContinuousOn (fun y ↦ ∑ j ∈ Finset.Iio i,
          ((H y).inner (g j y) (β y i) / (length j y : ℂ) ^ 2) •
            (e ⟨y, g j y⟩).2) U := by
        apply continuousOn_finsetSum
        intro j hj
        exact (hc j hj).smul (hcoordinates (g j) (ih j (Finset.mem_Iio.mp hj)))
      apply hcoord
      apply ((hcoordinates (fun y ↦ β y i) (hβ i)).sub hsum).congr
      intro y hy
      have hrec : g i y = β y i - ∑ j ∈ Finset.Iio i,
          ((H y).inner (g j y) (β y i) / (length j y : ℂ) ^ 2) • g j y := by
        let := (normed y).down
        let := originalModule y
        let := (metric y).down
        change InnerProductSpace.gramSchmidt ℂ (β y) i = _
        rw [eq_sub_iff_add_eq]
        exact (InnerProductSpace.gramSchmidt_def'' ℂ (β y) i).symm
      change (e.linearEquivAt ℂ y hy) (g i y) = _
      rw [hrec, map_sub, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (e.linearEquivAt ℂ y hy).map_smul _ _
  let o (y : X) :
      letI := (normed y).down
      letI := originalModule y
      letI := (metric y).down
      OrthonormalBasis (Fin r) ℂ (E y) :=
    letI := (normed y).down
    letI := originalModule y
    letI := (metric y).down
    OrthonormalBasis.mk
      (InnerProductSpace.gramSchmidtNormed_orthonormal (β y).linearIndependent)
      (by
        rw [InnerProductSpace.span_gramSchmidtNormed_range,
          InnerProductSpace.span_gramSchmidt, (β y).span_eq])
  have ho (i : Fin r) :
      ContinuousOn (fun y ↦ (⟨y, o y i⟩ : TotalSpace V E)) U := by
    have hl : ContinuousOn (length i) U := by
      have hl := Real.continuous_sqrt.comp_continuousOn
        (Complex.continuous_re.comp_continuousOn (hpair (g i) (g i) (hg i) (hg i)))
      exact hl.congr (fun y _ ↦ hlength_eq i y)
    have hc : ContinuousOn (fun y ↦ ((length i y)⁻¹ : ℂ)) U :=
      (Complex.continuous_ofReal.comp_continuousOn hl).inv₀
        (fun y _ ↦ Complex.ofReal_ne_zero.mpr (hlength_ne i y))
    apply hcoord
    apply (hc.smul (hcoordinates (g i) (hg i))).congr
    intro y hy
    change (e.linearEquivAt ℂ y hy) (o y i) = _
    have hoy : o y i = ((length i y : ℂ)⁻¹) • g i y := by
      let := (normed y).down
      let := originalModule y
      let := (metric y).down
      simp only [o, OrthonormalBasis.coe_mk, InnerProductSpace.gramSchmidtNormed, g, length]
      rfl
    rw [hoy]
    exact (e.linearEquivAt ℂ y hy).map_smul _ _
  let sL (y : X) : V ≃ₗ[ℂ] E y :=
    letI := (normed y).down
    letI := originalModule y
    letI := (metric y).down
    (o y).repr.symm.toLinearEquiv
  let s (y : X) : V ≃L[ℂ] E y := (sL y).toContinuousLinearEquiv
  have hs_basis (y : X) (i : Fin r) : s y (b₀ i) = o y i := by
    let := (normed y).down
    let := originalModule y
    let := (metric y).down
    change (o y).repr.symm (EuclideanSpace.basisFun (Fin r) ℂ i) = _
    rw [EuclideanSpace.basisFun_apply, OrthonormalBasis.repr_symm_single]
  have hs_inner (y : X) (u v : V) :
      (H y).inner (s y u) (s y v) = inner ℂ u v := by
    let := (normed y).down
    let := originalModule y
    let := (metric y).down
    exact (o y).repr.symm.inner_map_map u v
  have hs (i : Fin r) :
      ContinuousOn (fun y ↦ (⟨y, s y (b₀ i)⟩ : TotalSpace V E)) U := by
    simpa only [hs_basis] using ho i
  -- Conjugation preserves every defining flag condition in precisely these original fibers.
  let C (y : X) : (E y →L[ℂ] E y) ≃A[ℂ] (V →L[ℂ] V) :=
    (s y).symm.conjContinuousAlgEquiv
  have hC_rank (y : X) (P : E y →L[ℂ] E y) :
      Module.finrank ℂ (LinearMap.range (C y P).toLinearMap) =
        Module.finrank ℂ (LinearMap.range P.toLinearMap) := by
    change Module.finrank ℂ (LinearMap.range
      ((s y).symm.toLinearEquiv.toLinearMap.comp
        (P.toLinearMap.comp (s y).toLinearEquiv.toLinearMap))) = _
    rw [LinearMap.range_comp, LinearEquiv.range_comp, LinearEquiv.finrank_map_eq]
  have hC_symmetric (y : X) (P : E y →L[ℂ] E y) :
      (∀ u v, (H y).inner (P u) v = (H y).inner u (P v)) ↔
        ∀ u v, inner ℂ (C y P u) v = inner ℂ u (C y P v) := by
    constructor
    · intro hP u v
      change inner ℂ ((s y).symm (P (s y u))) v =
        inner ℂ u ((s y).symm (P (s y v)))
      rw [← hs_inner y, ← hs_inner y]
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hP (s y u) (s y v)
    · intro hP u v
      have hp := hP ((s y).symm u) ((s y).symm v)
      change inner ℂ ((s y).symm (P (s y ((s y).symm u)))) ((s y).symm v) =
        inner ℂ ((s y).symm u) ((s y).symm (P (s y ((s y).symm v)))) at hp
      rw [← hs_inner y, ← hs_inner y] at hp
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp
  have hC_flag (y : X) (P : Fin r → E y →L[ℂ] E y) :
      ((∀ i, (P i).comp (P i) = P i) ∧
        (∀ i, Module.finrank ℂ (LinearMap.range (P i).toLinearMap) = 1) ∧
        (∀ i j, i ≠ j → (P i).comp (P j) = 0) ∧
        (∑ i, P i) = ContinuousLinearMap.id ℂ (E y) ∧
        ∀ i u v, (H y).inner (P i u) v = (H y).inner u (P i v)) ↔
      ((∀ i, (C y (P i)).comp (C y (P i)) = C y (P i)) ∧
        (∀ i, Module.finrank ℂ (LinearMap.range (C y (P i)).toLinearMap) = 1) ∧
        (∀ i j, i ≠ j → (C y (P i)).comp (C y (P j)) = 0) ∧
        (∑ i, C y (P i)) = ContinuousLinearMap.id ℂ V ∧
        ∀ i u v, inner ℂ (C y (P i) u) v = inner ℂ u (C y (P i) v)) := by
    constructor
    · rintro ⟨hid, hrank, horth, hsum, hself⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i
        simpa only [← ContinuousLinearMap.mul_def, map_mul] using
          congrArg (C y) (hid i)
      · intro i
        rw [hC_rank]
        exact hrank i
      · intro i j hij
        simpa only [← ContinuousLinearMap.mul_def, map_mul, map_zero] using
          congrArg (C y) (horth i j hij)
      · simpa only [map_sum, ← ContinuousLinearMap.one_def, map_one] using
          congrArg (C y) hsum
      · intro i
        exact (hC_symmetric y (P i)).mp (hself i)
    · rintro ⟨hid, hrank, horth, hsum, hself⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i
        apply (C y).injective
        simpa only [← ContinuousLinearMap.mul_def, map_mul,
          ContinuousAlgEquiv.coe_toAlgEquiv] using hid i
      · intro i
        rw [← hC_rank y (P i)]
        exact hrank i
      · intro i j hij
        apply (C y).injective
        simpa only [← ContinuousLinearMap.mul_def, map_mul, map_zero,
          ContinuousAlgEquiv.coe_toAlgEquiv] using horth i j hij
      · apply (C y).injective
        simpa only [map_sum, ← ContinuousLinearMap.one_def, map_one,
          ContinuousAlgEquiv.coe_toAlgEquiv] using hsum
      · intro i
        exact (hC_symmetric y (P i)).mpr (hself i)
  let tupleEquiv (y : X) : (Fin r → E y →L[ℂ] E y) ≃ (Fin r → V →L[ℂ] V) :=
    Equiv.piCongrRight (fun _ ↦ (C y).toEquiv)
  let flagEquiv (y : X) : HermitianFlagSpace r (E y) (H y) ≃
      HermitianFlagSpace r V InnerProductSpace.toCore :=
    (tupleEquiv y).subtypeEquiv (hC_flag y)
  -- Compare conjugation with the original native Hom chart using one change of frame.
  let A (y : X) : V →L[ℂ] V :=
    (e.continuousLinearMapAt ℂ y).comp (s y).toContinuousLinearMap
  let B (y : X) : V →L[ℂ] V :=
    (s y).symm.toContinuousLinearMap.comp (e.symmL ℂ y)
  have hA : ContinuousOn A U := by
    apply continuousOn_clm_apply.mpr
    intro v
    have hsum : ContinuousOn (fun y ↦ ∑ i : Fin r,
        v i • (e ⟨y, s y (b₀ i)⟩).2) U := by
      apply continuousOn_finsetSum
      intro i _
      exact (continuous_const (y := v i)).continuousOn.smul (hcoordinates _ (hs i))
    apply hsum.congr
    intro y hy
    have hsum' := congrArg (A y) (b₀.sum_repr v)
    change A y (∑ i : Fin r, v i • b₀ i) = A y v at hsum'
    simpa only [A, map_sum, map_smul,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.continuousLinearMapAt_apply_of_mem ℂ hy] using hsum'.symm
  have hB : ContinuousOn B U := by
    apply continuousOn_clm_apply.mpr
    intro v
    have hv : ContinuousOn (fun y ↦ (⟨y, e.symmL ℂ y v⟩ : TotalSpace V E)) U := by
      apply hcoord
      apply (continuous_const (y := v)).continuousOn.congr
      intro y hy
      change (e ⟨y, e.symmL ℂ y v⟩).2 = v
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hy]
      exact e.continuousLinearMapAt_symmL hy v
    have hcoeff : ContinuousOn
        (fun y i ↦ (H y).inner (o y i) (e.symmL ℂ y v)) U :=
      continuousOn_pi.mpr (fun i ↦ hpair (fun y ↦ o y i) (fun y ↦ e.symmL ℂ y v)
        (ho i) hv)
    apply ((PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).comp_continuousOn hcoeff).congr
    intro y _
    let := (normed y).down
    let := originalModule y
    let := (metric y).down
    apply PiLp.ext
    intro i
    change ((o y).repr (e.symmL ℂ y v)) i = _
    exact (o y).repr_apply_apply _ _
  let F := HermitianFlagSpace r V InnerProductSpace.toCore
  let ι (p : HermitianFlagBundle r E h) :=
    (p.1, fun i : Fin r ↦
      (⟨p.1, p.2.val i⟩ : TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y)))
  have hι : Topology.IsInducing ι := ⟨rfl⟩
  have hproj : Continuous (fun p : HermitianFlagBundle r E h ↦ p.1) :=
    (hermitianFlagProjection r E h).continuous
  have hcolumn (i : Fin r) : Continuous (fun p : HermitianFlagBundle r E h ↦
      (⟨p.1, p.2.val i⟩ : TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y))) :=
    (continuous_apply i).comp (continuous_snd.comp hι.continuous)
  let φ : HermitianFlagBundle r E h ≃ X × F :=
    { toFun := fun p ↦ (p.1, flagEquiv p.1 p.2)
      invFun := fun q ↦ ⟨q.1, (flagEquiv q.1).symm q.2⟩
      left_inv := fun p ↦ by
        rcases p with ⟨y, P⟩
        exact congrArg (Sigma.mk y) ((flagEquiv y).symm_apply_apply P)
      right_inv := fun q ↦ Prod.ext rfl ((flagEquiv q.1).apply_symm_apply q.2) }
  let t := e.continuousLinearMap (RingHom.id ℂ) e
  -- Native coordinates are conjugated by the same continuous pair A,B in both directions.
  have hφ : ContinuousOn φ {p | p.1 ∈ U} := by
    have hnative (i : Fin r) : ContinuousOn
        (fun p : HermitianFlagBundle r E h ↦
          (t (⟨p.1, p.2.val i⟩ :
            TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y))).2) {p | p.1 ∈ U} :=
      (t.continuousOn.comp (hcolumn i).continuousOn
        (fun p hp ↦ t.mem_source.mpr ⟨hp, hp⟩)).snd
    have hmodel (i : Fin r) : ContinuousOn
        (fun p : HermitianFlagBundle r E h ↦ (flagEquiv p.1 p.2).val i)
        {p | p.1 ∈ U} := by
      have hA' := hA.comp hproj.continuousOn (fun p hp ↦ hp)
      have hB' := hB.comp hproj.continuousOn (fun p hp ↦ hp)
      apply (hB'.clm_comp ((hnative i).clm_comp hA')).congr
      intro p hp
      apply ContinuousLinearMap.ext
      intro v
      change (s p.1).symm (p.2.val i (s p.1 v)) =
        (s p.1).symm (e.symmL ℂ p.1 (e.continuousLinearMapAt ℂ p.1
          (p.2.val i (e.symmL ℂ p.1 (e.continuousLinearMapAt ℂ p.1 (s p.1 v))))))
      rw [e.symmL_continuousLinearMapAt hp, e.symmL_continuousLinearMapAt hp]
    have hflag : ContinuousOn
        (fun p : HermitianFlagBundle r E h ↦ flagEquiv p.1 p.2) {p | p.1 ∈ U} :=
      Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        (continuousOn_pi.mpr hmodel)
    exact hproj.continuousOn.prodMk hflag
  have hφ_symm_column (i : Fin r) : ContinuousOn
      (fun q : X × F ↦
        (⟨q.1, (φ.symm q).2.val i⟩ :
          TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y)))
      (U ×ˢ Set.univ) := by
    have hA' : ContinuousOn (fun q : X × F ↦ A q.1) (U ×ˢ Set.univ) :=
      hA.comp continuous_fst.continuousOn (fun q hq ↦ hq.1)
    have hB' : ContinuousOn (fun q : X × F ↦ B q.1) (U ×ˢ Set.univ) :=
      hB.comp continuous_fst.continuousOn (fun q hq ↦ hq.1)
    have hQ : Continuous (fun q : X × F ↦ q.2.val i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    have hmatrix : ContinuousOn
        (fun q : X × F ↦ (A q.1).comp ((q.2.val i).comp (B q.1)))
        (U ×ˢ Set.univ) := hA'.clm_comp (hQ.continuousOn.clm_comp hB')
    have hraw := t.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_fst.continuousOn.prodMk hmatrix)
      (fun q hq ↦ t.mem_target.mpr ⟨hq.1, hq.1⟩)
    apply hraw.congr
    intro q hq
    have hcoords :
        t (⟨q.1, (φ.symm q).2.val i⟩ :
          TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y)) =
          (q.1, (A q.1).comp ((q.2.val i).comp (B q.1))) := by
      apply Prod.ext
      · rfl
      · ext v
        rfl
    exact (t.left_inv (t.mem_source.mpr ⟨hq.1, hq.1⟩)).symm.trans
      (congrArg t.toOpenPartialHomeomorph.symm hcoords)
  have hφ_symm : ContinuousOn φ.symm (U ×ˢ Set.univ) := by
    apply hι.continuousOn_iff.mpr
    exact continuous_fst.continuousOn.prodMk
      (continuousOn_pi.mpr hφ_symm_column)
  -- Restrict the total fiberwise equivalence to the original chart domain.
  let flagChart : Trivialization F (hermitianFlagProjection r E h) :=
    { toFun := φ
      invFun := φ.symm
      source := {p | p.1 ∈ U}
      target := U ×ˢ Set.univ
      map_source' := fun {_} hp ↦ ⟨hp, Set.mem_univ _⟩
      map_target' := fun {_} hq ↦ hq.1
      left_inv' := fun {_} _ ↦ φ.left_inv _
      right_inv' := fun {_} _ ↦ φ.right_inv _
      continuousOn_toFun := hφ
      continuousOn_invFun := hφ_symm
      open_source := e.open_baseSet.preimage hproj
      open_target := e.open_baseSet.prod isOpen_univ
      baseSet := U
      open_baseSet := e.open_baseSet
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  exact ⟨flagChart, mem_baseSet_trivializationAt V E x⟩

end AtiyahSinger.ComplexBundle
