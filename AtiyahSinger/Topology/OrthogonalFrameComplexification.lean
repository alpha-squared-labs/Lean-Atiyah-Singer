/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalComplexification
public import AtiyahSinger.Geometry.OrthogonalFrameBundle
public import AtiyahSinger.Topology.AssociatedVectorDescent
public import AtiyahSinger.Topology.ComplexificationHermitianMetric
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Orthogonal frame descent of the original complexification

Public module ID: M1977.

The scalar extension of each actual orthogonal frame descends through the
original associated-vector quotient. Its real and imaginary coordinates are
the same frame applied to the two standard real coordinate vectors. Continuity
is checked in the original frame-column topology and the original real-double
topology of the complexification, including rank zero.

This is the standard frame description of complexification (HU IV.5 and
Chapter 17, section 11). It supplies the specified coordinates needed for the
normal exterior Thom comparison; it does not itself identify support classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct Matrix.Norms.Elementwise

variable {n r : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin r)) V]

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "W" => EuclideanSpace ℂ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

attribute [local instance] orthogonalFrameTopology associatedVectorFiberAddCommGroup
  associatedVectorFiberModule associatedVectorTotalTopology

/-- The original orthogonal complexification in the existing finite-coordinate wrapper. -/
def orthogonalComplexificationFiniteRepresentation (r : ℕ) :
    FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ) :=
  FiniteContinuousRepresentation.ofEquiv
    (ContRepresentation.ofMonoidHom (orthogonalComplexificationRepresentation r))
    (show Continuous (fun z : Matrix.orthogonalGroup (Fin r) ℝ ×
        EuclideanSpace ℂ (Fin r) ↦ orthogonalComplexificationRepresentation r z.1 z.2)
      from continuous_smul)
    (EuclideanSpace.equiv (Fin r) ℂ)

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in
-- Keep the original scalar extension, frame topology and associated quotient together.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual associated vector bundle is the scalar extension, with every frame specified. -/
theorem exists_orthogonalFrame_complexification_iso :
    letI := continuousSMul_orthogonalFrame r V I
    let hP := (smoothOrthogonalFrameAtlas r V I).toIsPrincipalBundle
    let ρ := orthogonalComplexificationFiniteRepresentation r
    letI := complexificationTopology R V
    ∃ e : Iso (AssociatedVectorFiber hP ρ.representation) (fun b ↦ ℂ ⊗[ℝ] V b),
      ∀ (p : P) (z : Fin r → ℂ),
        complexificationReIm (V p.1)
            (e.linearEquiv p.1 (associatedVectorFiberMk hP ρ.representation p rfl z)) =
          (p.2 (WithLp.toLp 2 (fun i ↦ (z i).re)),
            p.2 (WithLp.toLp 2 (fun i ↦ (z i).im))) := by
  classical
  let := continuousSMul_orthogonalFrame r V I
  let S := smoothOrthogonalFrameAtlas r V I
  let hP := S.toIsPrincipalBundle
  let C := fun b : B ↦ ℂ ⊗[ℝ] V b
  let := complexificationTopology R V
  let := ComplexBundle.isFiniteRank_complexification R V
  let ρ := orthogonalComplexificationFiniteRepresentation r
  -- The standard finite coordinates retain the genuine tensor scalar extension.
  let d : (ℂ ⊗[ℝ] R) ≃ₗ[ℂ] (Fin r → ℂ) :=
    ((EuclideanSpace.equiv (Fin r) ℝ).toLinearEquiv.baseChange ℝ ℂ _ _).trans
      (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin r))
  have hd (w : ℂ ⊗[ℝ] R) (i : Fin r) :
      d w i = ((complexificationReIm R w).1 i : ℂ) +
        ((complexificationReIm R w).2 i : ℂ) * Complex.I := by
    induction w using TensorProduct.inductionOn with
    | tmul z v =>
      simp only [d, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
        TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Complex.real_smul, (complexificationReIm_properties R).1, PiLp.smul_apply]
      change (v i : ℂ) * z = ((z.re * v i : ℝ) : ℂ) +
        ((z.im * v i : ℝ) : ℂ) * Complex.I
      rw [Complex.ofReal_mul, Complex.ofReal_mul]
      calc
        (v i : ℂ) * z = (v i : ℂ) * (z.re + z.im * Complex.I) := by
          rw [Complex.re_add_im]
        _ = _ := by ring
    | add v w hv hw =>
      simp only [map_add, Pi.add_apply, Prod.fst_add, Prod.snd_add, PiLp.add_apply,
        Complex.ofReal_add, add_mul, hv, hw]
      ring
  let L (p : P) : (Fin r → ℂ) ≃ₗ[ℂ] C p.1 :=
    d.symm.trans (p.2.toLinearEquiv.baseChange ℝ ℂ _ _)
  have hcoords (p : P) (z : Fin r → ℂ) :
      complexificationReIm (V p.1) (L p z) =
        (p.2 (WithLp.toLp 2 (fun i ↦ (z i).re)),
          p.2 (WithLp.toLp 2 (fun i ↦ (z i).im))) := by
    have hbase (w : ℂ ⊗[ℝ] R) :
        complexificationReIm (V p.1) ((p.2.toLinearEquiv.baseChange ℝ ℂ _ _) w) =
          (p.2 (complexificationReIm R w).1, p.2 (complexificationReIm R w).2) := by
      induction w using TensorProduct.inductionOn with
      | tmul a v =>
        rw [LinearEquiv.baseChange_tmul, (complexificationReIm_properties _).1,
          (complexificationReIm_properties _).1, map_smul, map_smul]
        rfl
      | add v w hv hw =>
        simp only [map_add, hv, hw, Prod.fst_add, Prod.snd_add]
        rfl
    have hreal : (complexificationReIm R (d.symm z)).1 =
        WithLp.toLp 2 (fun i ↦ (z i).re) := by
      ext i
      have h := congrArg Complex.re (hd (d.symm z) i)
      simpa only [d.apply_symm_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero] using h.symm
    have himag : (complexificationReIm R (d.symm z)).2 =
        WithLp.toLp 2 (fun i ↦ (z i).im) := by
      ext i
      have h := congrArg Complex.im (hd (d.symm z) i)
      simpa only [d.apply_symm_apply, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        mul_one, zero_add, add_zero] using h.symm
    exact (hbase (d.symm z)).trans (by rw [hreal, himag])
  have hcov (p : P) (g : G) (z : Fin r → ℂ) :
      L (MulOpposite.op g • p) z = L p (ρ.representation g z) := by
    apply (complexificationReIm (V p.1)).injective
    change complexificationReIm (V (MulOpposite.op g • p).1)
      (L (MulOpposite.op g • p) z) = _
    have hleft := hcoords (MulOpposite.op g • p) z
    have hright := hcoords p (ρ.representation g z)
    refine Eq.trans hleft (Eq.trans ?_ hright.symm)
    apply Prod.ext
    · apply congrArg p.2
      ext i
      change ∑ j, (g.val i j) * (z j).re =
        (∑ j, (g.val i j : ℂ) * z j).re
      simp
    · apply congrArg p.2
      ext i
      change ∑ j, (g.val i j) * (z j).im =
        (∑ j, (g.val i j : ℂ) * z j).im
      simp
  -- Frame evaluation is continuous in the original column topology, also in rank zero.
  have hcols : Continuous (fun p : P ↦
      (p.1, fun i : Fin r ↦
        (⟨p.1, p.2 (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ : TotalSpace R V))) :=
    continuous_induced_dom
  have hcolumn (j : Fin r) : Continuous (fun p : P ↦
      (⟨p.1, p.2 (EuclideanSpace.basisFun (Fin r) ℝ j)⟩ : TotalSpace R V)) :=
    (continuous_apply j).comp hcols.snd
  have heval : Continuous (fun z : P × R ↦
      (⟨z.1.1, z.1.2 z.2⟩ : TotalSpace R V)) := by
    have hb := hP.projection_properties.1.comp (continuous_fst : Continuous (Prod.fst : P × R → P))
    rw [continuous_iff_continuousAt]
    intro z₀
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    let t := trivializationAt R V z₀.1.1
    have hj (j : Fin r) : ContinuousAt (fun z : P × R ↦
        (t ⟨z.1.1, z.1.2 (EuclideanSpace.basisFun (Fin r) ℝ j)⟩).2) z₀ :=
      ((FiberBundle.continuousAt_totalSpace R _).mp
        ((hcolumn j).comp continuous_fst).continuousAt).2
    have hsum : ContinuousAt (fun z : P × R ↦ ∑ j : Fin r,
        z.2 j • (t ⟨z.1.1, z.1.2 (EuclideanSpace.basisFun (Fin r) ℝ j)⟩).2) z₀ := by
      apply tendsto_finsetSum
      intro j _
      exact ((EuclideanSpace.proj j).continuous.comp continuous_snd).continuousAt.smul (hj j)
    apply hsum.congr_of_eventuallyEq
    filter_upwards [hb.continuousAt
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt R V z₀.1.1))] with z hz
    change (t ⟨z.1.1, z.1.2 z.2⟩).2 = _
    have ht (w : V z.1.1) :
        (t ⟨z.1.1, w⟩).2 = t.continuousLinearMapAt ℝ z.1.1 w :=
      (t.continuousLinearMapAt_apply_of_mem ℝ hz w).symm
    simp_rw [ht]
    have hs := (EuclideanSpace.basisFun (Fin r) ℝ).sum_repr z.2
    have h := congrArg (fun w ↦ t.continuousLinearMapAt ℝ z.1.1 (z.1.2 w)) hs
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr] using h.symm
  have hre : Continuous (fun z : (Fin r → ℂ) ↦
      WithLp.toLp 2 (fun i ↦ (z i).re)) :=
    (EuclideanSpace.equiv (Fin r) ℝ).symm.continuous.comp
      (continuous_pi (fun i ↦ Complex.continuous_re.comp (continuous_apply i)))
  have him : Continuous (fun z : (Fin r → ℂ) ↦
      WithLp.toLp 2 (fun i ↦ (z i).im)) :=
    (EuclideanSpace.equiv (Fin r) ℝ).symm.continuous.comp
      (continuous_pi (fun i ↦ Complex.continuous_im.comp (continuous_apply i)))
  have hL : Continuous (fun z : P × (Fin r → ℂ) ↦
      (⟨z.1.1, L z.1 z.2⟩ : TotalSpace Unit C)) := by
    have hreal := heval.comp (continuous_fst.prodMk (hre.comp continuous_snd))
    have himag := heval.comp (continuous_fst.prodMk (him.comp continuous_snd))
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    apply (hreal.prodMk himag).congr
    intro z
    change ((⟨z.1.1, _⟩ : TotalSpace R V), (⟨z.1.1, _⟩ : TotalSpace R V)) =
      ((⟨z.1.1, (complexificationReIm (V z.1.1) (L z.1 z.2)).1⟩ : TotalSpace R V),
        (⟨z.1.1, (complexificationReIm (V z.1.1) (L z.1 z.2)).2⟩ : TotalSpace R V))
    rw [hcoords]
    rfl
  -- Descend the same continuous covariant coordinates, retaining every representative.
  let f (b : B) (p : P) (hp : orthogonalFrameProjection r V p = b) :
      (Fin r → ℂ) ≃ₗ[ℂ] C b := by
    subst b
    exact L p
  have hf : Continuous (fun z : P × (Fin r → ℂ) ↦
      (⟨orthogonalFrameProjection r V z.1,
        f (orthogonalFrameProjection r V z.1) z.1 rfl z.2⟩ : TotalSpace Unit C)) := hL
  have hfcov (b : B) (p : P) (hp : orthogonalFrameProjection r V p = b) (g : G)
      (z : Fin r → ℂ) :
      f b (MulOpposite.op g • p) ((hP.projection_smul g p).trans hp) z =
        f b p hp (ρ.representation g z) := by
    subst b
    exact hcov p g z
  obtain ⟨e, he⟩ := exists_associatedVector_iso_of_covariant_equiv hP ρ C f hf hfcov
  refine ⟨e, ?_⟩
  intro p z
  rw [he]
  exact hcoords p z


include n in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In the original Euclidean representation, frame descent has these exact total coordinates. -/
theorem exists_orthogonalFrame_complexification_homeomorph :
    letI := continuousSMul_orthogonalFrame r V I
    letI := complexificationTopology R V
    ∃ e : AssociatedBundle G P W ≃ₜ TotalSpace Unit (fun b ↦ ℂ ⊗[ℝ] V b),
      ∀ (p : P) (z : W),
        e (associatedBundleMk G P W p z) =
          ⟨p.1, (complexificationReIm (V p.1)).symm
            (p.2 (WithLp.toLp 2 (fun i ↦ (z i).re)),
              p.2 (WithLp.toLp 2 (fun i ↦ (z i).im)))⟩ := by
  let := continuousSMul_orthogonalFrame r V I
  let hP := (smoothOrthogonalFrameAtlas r V I).toIsPrincipalBundle
  let ρ := orthogonalComplexificationFiniteRepresentation r
  let := complexificationTopology R V
  let : MulAction G (Fin r → ℂ) := associatedRepresentationAction ρ.representation
  let : ContinuousSMul G (Fin r → ℂ) := ⟨ρ.continuous_action⟩
  let q := EuclideanSpace.equiv (Fin r) ℂ
  -- The coordinate wrapper intertwines exactly the original orthogonal action.
  let f : C(AssociatedBundle G P W, AssociatedBundle G P (Fin r → ℂ)) :=
    associatedBundleMap ⟨q, q.continuous⟩ (fun _ _ ↦ rfl)
  let g : C(AssociatedBundle G P (Fin r → ℂ), AssociatedBundle G P W) :=
    associatedBundleMap ⟨q.symm, q.symm.continuous⟩ (fun _ _ ↦ rfl)
  let d : AssociatedBundle G P W ≃ₜ AssociatedBundle G P (Fin r → ℂ) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro z
        induction z using Quotient.inductionOn with
        | h w => rfl
      right_inv := by
        intro z
        induction z using Quotient.inductionOn with
        | h w => rfl
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  obtain ⟨a, ha⟩ := exists_orthogonalFrame_complexification_iso (n := n) (r := r) V
  -- The only transports are the original quotient-total equivalence and the descended Iso.
  let e := d.trans ((associatedVectorTotalHomeomorph hP ρ.representation).symm.trans
    a.totalHomeomorph)
  refine ⟨e, ?_⟩
  intro p z
  change (⟨p.1, a.linearEquiv p.1
      (associatedVectorFiberMk hP ρ.representation p rfl (q z))⟩ :
      TotalSpace Unit (fun b ↦ ℂ ⊗[ℝ] V b)) = _
  apply congrArg (fun w : ℂ ⊗[ℝ] V p.1 ↦
    (⟨p.1, w⟩ : TotalSpace Unit (fun b ↦ ℂ ⊗[ℝ] V b)))
  apply (complexificationReIm (V p.1)).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ha p (q z)

end AtiyahSinger
