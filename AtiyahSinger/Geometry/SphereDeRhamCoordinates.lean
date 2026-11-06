/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SphereDeRhamClass

/-!
# The native sphere Koszul differential in its actual pole coordinates

Public module ID: M1425.

AL02. The complexified derivative of the specified inverse pole chart identifies
the original Euclidean complex carrier with the actual complexified native
tangent fiber. Its real/imaginary formula and moving-fiber continuity retain
the fixed scalar-extension topology. The prescribed global vector and wedge
differential become exactly the two original hemisphere formulas.

The derivative is conformal for the round Hermitian metric, with the same
positive scalar as the original real chart. Thus the wedge differential
intertwines directly, but the compressed positive operators are not asserted
to intertwine for the standard Euclidean metric. Comparing the compressed
classes requires a positive metric homotopy on these same fibers, keeping the
same zero locus and compact control. No metric comparison is hidden in the
coordinate identity below.

Source: Atiyah--Singer I, Lemma (3.2), pp.499--500. The explicit native chart
bridge is the project's realization of its two-ball construction. These
formulas hold on the full pole charts and restrict to the source's closed
unit balls. The shared equator and its reflection transition were specified
in SphereTangentCoordinates; no independently chosen coordinate chart is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 25

attribute [local instance] sphereComplexifiedTangentTopology

/-- The complex-linear extension of the actual inverse-chart derivative on the standard basis. -/
def sphereTangentChartComplexification (r : ℕ) (atInfinity : Bool)
    (u : EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℂ (Fin r) →ₗ[ℂ]
      SphereComplexifiedTangent r ((orthogonalSphereNormalizedChart r atInfinity).symm u) :=
  (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.constr ℂ (fun i ↦
    (1 : ℂ) ⊗ₜ[ℝ]
      mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u
        (EuclideanSpace.basisFun (Fin r) ℝ i))

/-- These linear bijections have joint continuity and the stated round conformal pairing.
The grouped formulas certify this one chart construction, including its conformal factor. -/
theorem sphereTangentChartComplexification_properties (r : ℕ) (atInfinity : Bool) :
    (∀ u : EuclideanSpace ℝ (Fin r),
      Function.Bijective (sphereTangentChartComplexification r atInfinity u)) ∧
    (∀ (u : EuclideanSpace ℝ (Fin r)) (z : EuclideanSpace ℂ (Fin r)),
      sphereTangentChartComplexification r atInfinity u z =
        (1 : ℂ) ⊗ₜ[ℝ]
          mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u
            (WithLp.toLp 2 (fun i ↦ (z i).re)) +
        Complex.I ⊗ₜ[ℝ]
          mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u
            (WithLp.toLp 2 (fun i ↦ (z i).im))) ∧
    (∀ (u : EuclideanSpace ℝ (Fin r)) (z w : EuclideanSpace ℂ (Fin r)),
      ((sphereComplexifiedRoundMetric r).toCore
          ((orthogonalSphereNormalizedChart r atInfinity).symm u)).inner
          (sphereTangentChartComplexification r atInfinity u z)
          (sphereTangentChartComplexification r atInfinity u w) =
        ((4 / (1 + ‖u‖ ^ 2) ^ 2 : ℝ) : ℂ) * inner ℂ z w) ∧
    Continuous (fun p : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℂ (Fin r) ↦
      (⟨(orthogonalSphereNormalizedChart r atInfinity).symm p.1,
        sphereTangentChartComplexification r atInfinity p.1 p.2⟩ :
          TotalSpace Unit (SphereComplexifiedTangent r))) := by
  let V := EuclideanSpace ℝ (Fin r)
  let C := EuclideanSpace ℂ (Fin r)
  let e := orthogonalSphereNormalizedChart r atInfinity
  let E := fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x
  let re (z : C) : V := WithLp.toLp 2 (fun i ↦ (z i).re)
  let im (z : C) : V := WithLp.toLp 2 (fun i ↦ (z i).im)
  -- Expand the original basis construction, retaining the same real derivative.
  have hformula (u : EuclideanSpace ℝ (Fin r)) (z : EuclideanSpace ℂ (Fin r)) :
    sphereTangentChartComplexification r atInfinity u z =
      (1 : ℂ) ⊗ₜ[ℝ]
        mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u
          (WithLp.toLp 2 (fun i ↦ (z i).re)) +
      Complex.I ⊗ₜ[ℝ]
        mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u
          (WithLp.toLp 2 (fun i ↦ (z i).im)) := by
    let V := EuclideanSpace ℝ (Fin r)
    let C := EuclideanSpace ℂ (Fin r)
    let e := orthogonalSphereNormalizedChart r atInfinity
    let D : V →L[ℝ] TangentSpace (𝓡 r) (e.symm u) := mfderiv (𝓡 r) (𝓡 r) e.symm u
    let re : V := WithLp.toLp 2 (fun i ↦ (z i).re)
    let im : V := WithLp.toLp 2 (fun i ↦ (z i).im)
    have hsum (w : V) : ∑ j : Fin r, w j • EuclideanSpace.basisFun (Fin r) ℝ j = w :=
      (EuclideanSpace.basisFun (Fin r) ℝ).sum_repr w
    apply (complexificationReIm (TangentSpace (𝓡 r) (e.symm u))).injective
    simp only [sphereTangentChartComplexification, Module.Basis.constr_apply_fintype]
    change complexificationReIm _ (∑ j : Fin r, z j • ((1 : ℂ) ⊗ₜ[ℝ] D
      (EuclideanSpace.basisFun (Fin r) ℝ j))) = _
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_sum, map_add,
      (complexificationReIm_properties _).1, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, one_smul, zero_smul, Prod.mk_add_mk,
      add_zero, zero_add]
    apply Prod.ext
    · simp only [Prod.fst_sum]
      change (∑ j : Fin r, (z j).re • D (EuclideanSpace.basisFun (Fin r) ℝ j)) = D re
      simpa only [map_sum, map_smul] using congrArg D (hsum re)
    · simp only [Prod.snd_sum]
      change (∑ j : Fin r, (z j).im • D (EuclideanSpace.basisFun (Fin r) ℝ j)) = D im
      simpa only [map_sum, map_smul] using congrArg D (hsum im)
  have hcoords (u : V) (z : C) :
      complexificationReIm (E (e.symm u)) (sphereTangentChartComplexification r atInfinity u z) =
        (mfderiv (𝓡 r) (𝓡 r) e.symm u (re z),
          mfderiv (𝓡 r) (𝓡 r) e.symm u (im z)) := by
    rw [hformula, map_add, (complexificationReIm_properties _).1,
      (complexificationReIm_properties _).1]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      one_smul, zero_smul, Prod.mk_add_mk, add_zero, zero_add]
    rfl
  refine ⟨?_, hformula, ?_, ?_⟩
  · -- The real inverse chart has an invertible derivative at every model point.
    intro u
    have he : e.MDifferentiable (𝓡 r) (𝓡 r) :=
      ⟨(orthogonalSphereNormalizedChart_smooth r atInfinity).1.mdifferentiableOn (by simp),
        (orthogonalSphereNormalizedChart_smooth r atInfinity).2.mdifferentiable (by simp)
          |>.mdifferentiableOn⟩
    have hu : u ∈ e.target := by
      rw [(orthogonalSphereNormalizedChart_properties r atInfinity).2.1]
      trivial
    have hD : Function.Bijective (fun v : V ↦ mfderiv (𝓡 r) (𝓡 r) e.symm u v) :=
      he.symm.mfderiv_bijective hu
    constructor
    · intro z w h
      have hc := congrArg (complexificationReIm (E (e.symm u))) h
      rw [hcoords, hcoords] at hc
      have hre := hD.1 (congrArg Prod.fst hc)
      have him := hD.1 (congrArg Prod.snd hc)
      ext j
      exact Complex.ext (congrArg (fun a : V ↦ a j) hre)
        (congrArg (fun a : V ↦ a j) him)
    · intro a
      obtain ⟨v, hv⟩ := hD.2 (complexificationReIm (E (e.symm u)) a).1
      obtain ⟨w, hw⟩ := hD.2 (complexificationReIm (E (e.symm u)) a).2
      let z : C := WithLp.toLp 2 (fun j ↦ Complex.mk (v j) (w j))
      refine ⟨z, ?_⟩
      apply (complexificationReIm (E (e.symm u))).injective
      rw [hcoords]
      exact Prod.ext hv hw
  · -- The same positive conformal factor multiplies all four real pairings.
    intro u z w
    rw [sphereComplexifiedRoundMetric_inner]
    dsimp only [sphereComplexifiedRoundPairing]
    rw [hcoords, hcoords]
    have hmetric (v w : V) :
        (orthogonalSphereRoundMetric r).inner (e.symm u)
          (mfderiv (𝓡 r) (𝓡 r) e.symm u v) (mfderiv (𝓡 r) (𝓡 r) e.symm u w) =
            (4 / (1 + ‖u‖ ^ 2) ^ 2) * inner ℝ v w :=
      orthogonalSphereNormalizedChart_roundMetric r atInfinity u v w
    rw [hmetric, hmetric, hmetric, hmetric]
    generalize (4 / (1 + ‖u‖ ^ 2) ^ 2 : ℝ) = c
    change ((c * inner ℝ (re z) (re w) + c * inner ℝ (im z) (im w) : ℝ) : ℂ) +
      Complex.I * ((c * inner ℝ (re z) (im w) - c * inner ℝ (im z) (re w) : ℝ) : ℂ) =
        (c : ℂ) * inner ℂ z w
    dsimp only [re, im]
    change ((c * inner ℝ (WithLp.toLp 2 (fun j ↦ (z j).re) : EuclideanSpace ℝ (Fin r))
        (WithLp.toLp 2 (fun j ↦ (w j).re)) +
      c * inner ℝ (WithLp.toLp 2 (fun j ↦ (z j).im) : EuclideanSpace ℝ (Fin r))
        (WithLp.toLp 2 (fun j ↦ (w j).im)) : ℝ) : ℂ) +
      Complex.I * ((c * inner ℝ (WithLp.toLp 2 (fun j ↦ (z j).re) :
          EuclideanSpace ℝ (Fin r)) (WithLp.toLp 2 (fun j ↦ (w j).im)) -
        c * inner ℝ (WithLp.toLp 2 (fun j ↦ (z j).im) : EuclideanSpace ℝ (Fin r))
          (WithLp.toLp 2 (fun j ↦ (w j).re)) : ℝ) : ℂ) = (c : ℂ) * inner ℂ z w
    apply Complex.ext <;>
      simp [PiLp.inner_apply, RCLike.inner_apply, Complex.mul_re, Complex.mul_im,
        Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    ring
  · -- Transport two continuous native tangent maps through the original Re/Im homeomorphism.
    have hre : Continuous re := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
      (continuous_pi fun j ↦ Complex.continuous_re.comp
        (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) j))
    have him : Continuous im := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
      (continuous_pi fun j ↦ Complex.continuous_im.comp
        (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) j))
    have ht : Continuous (tangentMap (𝓡 r) (𝓡 r) e.symm) :=
      (orthogonalSphereNormalizedChart_smooth r atInfinity).2.continuous_tangentMap (by simp)
    have hreal := ht.comp ((tangentBundleModelSpaceHomeomorph (𝓡 r)).symm.continuous.comp
      (continuous_fst.prodMk (hre.comp continuous_snd)))
    have himag := ht.comp ((tangentBundleModelSpaceHomeomorph (𝓡 r)).symm.continuous.comp
      (continuous_fst.prodMk (him.comp continuous_snd)))
    apply (complexificationDoubleTotalHomeomorph V E).isInducing.continuous_iff.mpr
    apply (FiberBundle.Prod.isInducing_diag V E V E).continuous_iff.mpr
    apply (hreal.prodMk himag).congr
    intro p
    change ((⟨e.symm p.1, mfderiv (𝓡 r) (𝓡 r) e.symm p.1 (re p.2)⟩ :
        TotalSpace V E), (⟨e.symm p.1, mfderiv (𝓡 r) (𝓡 r) e.symm p.1 (im p.2)⟩ :
        TotalSpace V E)) =
      ((⟨e.symm p.1, (complexificationReIm (E (e.symm p.1))
        (sphereTangentChartComplexification r atInfinity p.1 p.2)).1⟩ : TotalSpace V E),
      (⟨e.symm p.1, (complexificationReIm (E (e.symm p.1))
        (sphereTangentChartComplexification r atInfinity p.1 p.2)).2⟩ : TotalSpace V E))
    rw [hcoords]

/-- The global native vector and exterior differential are exactly the source chart formulas. -/
theorem sphereDeRhamDifferential_chart (r : ℕ) (atInfinity : Bool) (s : ℝ)
    (z : EuclideanSpace ℂ (Fin r)) :
    let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).re)
    let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).im)
    let e := sphereTangentChartComplexification r atInfinity u
    e (sphereHemisphereKoszulVector r atInfinity s u v) =
        sphereDeRhamVector r s (orthogonalSphereTangentChart r atInfinity z) ∧
      (sphereDeRhamDifferential r s (orthogonalSphereTangentChart r atInfinity z)).comp
          (ExteriorAlgebra.map e).toLinearMap =
        (ExteriorAlgebra.map e).toLinearMap.comp
          (sphereHemisphereDifferential r atInfinity s u v) := by
  dsimp only
  let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j ↦ (z j).re)
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j ↦ (z j).im)
  let e := sphereTangentChartComplexification r atInfinity u
  let c := orthogonalSphereNormalizedChart r atInfinity
  let D : EuclideanSpace ℝ (Fin r) →L[ℝ] TangentSpace (𝓡 r) (c.symm u) :=
    mfderiv (𝓡 r) (𝓡 r) c.symm u
  -- The two signs match the already specified height gradient in the same chart.
  have hre : (WithLp.toLp 2 (fun j ↦
      (sphereHemisphereKoszulVector r atInfinity s u v j).re) :
      EuclideanSpace ℝ (Fin r)) = v := by
    cases atInfinity <;> ext j <;> simp [sphereHemisphereKoszulVector]
  have him : (WithLp.toLp 2 (fun j ↦
      (sphereHemisphereKoszulVector r atInfinity s u v j).im) :
      EuclideanSpace ℝ (Fin r)) = (-s) • ((if atInfinity then (-1 : ℝ) else 1) • u) := by
    cases atInfinity <;> ext j <;> simp [sphereHemisphereKoszulVector]
  have hvector : e (sphereHemisphereKoszulVector r atInfinity s u v) =
      sphereDeRhamVector r s (orthogonalSphereTangentChart r atInfinity z) := by
    rw [(sphereTangentChartComplexification_properties r atInfinity).2.1 u,
      hre, him]
    change (1 : ℂ) ⊗ₜ[ℝ] D v + Complex.I ⊗ₜ[ℝ]
      D ((-s) • ((if atInfinity then (-1 : ℝ) else 1) • u)) = _
    rw [map_smul]
    have hgradient : D ((if atInfinity then (-1 : ℝ) else 1) • u) =
        orthogonalSphereHeightGradient r (c.symm u) :=
      orthogonalSphereHeightGradient_chart r atInfinity u
    rw [hgradient, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    change (1 : ℂ) ⊗ₜ[ℝ] D v +
      ((-s) • Complex.I) ⊗ₜ[ℝ] orthogonalSphereHeightGradient r (c.symm u) =
      (1 : ℂ) ⊗ₜ[ℝ] D v -
        ((s : ℂ) * Complex.I) ⊗ₜ[ℝ] orthogonalSphereHeightGradient r (c.symm u)
    simp [Complex.real_smul, TensorProduct.neg_tmul, sub_eq_add_neg]
  refine ⟨hvector, ?_⟩
  -- Functoriality carries left wedge multiplication through this exact vector equality.
  apply LinearMap.ext
  intro a
  let y : SphereComplexifiedTangent r (c.symm u) :=
    sphereDeRhamVector r s (orthogonalSphereTangentChart r atInfinity z)
  change ExteriorAlgebra.ι ℂ y *
        ExteriorAlgebra.map e a =
      ExteriorAlgebra.map e
        (ExteriorAlgebra.ι ℂ (sphereHemisphereKoszulVector r atInfinity s u v) * a)
  rw [map_mul, ExteriorAlgebra.map_apply_ι, hvector]


end AtiyahSinger
