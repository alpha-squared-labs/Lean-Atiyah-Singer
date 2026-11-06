/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalComplexification
public import AtiyahSinger.Geometry.OrthogonalStereographic
public import AtiyahSinger.Geometry.SphereHodge
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Native tangent coordinates and the height gradient on the orthogonal sphere

Public module ID: M1440.

AL02. Atiyah--Singer I, Lemma (3.2), pp.499--500, uses two ball coordinates with
the same equatorial base point and tangent transition given by reflection in
its perpendicular hyperplane. We realize those coordinates on the existing
native sphere. The zero-pole chart is the existing stereographic projection
divided by two. The infinity-pole chart first reflects only the vertical
coordinate. An antipodal map would give a different equatorial base coordinate.

The actual derivative action is installed on the native tangent bundle. Its
pole chart has domain the existing complexified orthogonal representation:
`u + I*v` maps to the derivative of the inverse sphere chart at `u`, applied to
`v`. This is an equivariant open embedding whose range is the whole tangent
bundle over the sphere with the opposite pole removed. Properness is not
required by this construction.

The global vector field is the round-metric gradient of the ambient height.
It is selected by its unique actual ambient derivative image `north - t*x`,
independently of any exactness or K-theory conclusion. Its two coordinate
vectors are exactly `u` and `-u`, giving the source homotopy vectors `v - I*s*u`
and `v + I*s*u`. The pulled-back round metric is explicitly conformal, with
factor `4 / (1 + norm(u)^2)^2`; the coordinate derivative is not called an
isometry. Rank zero is included throughout.

The explicit native geometry and gradient realization are project supplements
to the source's ball construction. The original derivative action, both normalized
charts, their reflection transition and conformal metric, the equivariant open
tangent parametrizations, and the chosen global height gradient are proved below.
All statements retain the original native atlas and tangent-bundle topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology
open scoped Manifold ContDiff InnerProductSpace

set_option maxSynthPendingDepth 25

/-- The genuine derivative lift of the already specified orthogonal sphere action. -/
def orthogonalSphereTangentMap (r : ℕ) (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    TangentBundle (𝓡 r) (OrthogonalSphere r) →
      TangentBundle (𝓡 r) (OrthogonalSphere r) :=
  tangentMap (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A)

/-- The derivative lift obeys the action laws on the original tangent total space. -/
theorem orthogonalSphereTangentMap_laws (r : ℕ) :
    (∀ z : TangentBundle (𝓡 r) (OrthogonalSphere r),
      orthogonalSphereTangentMap r 1 z = z) ∧
    ∀ (A B : Matrix.orthogonalGroup (Fin r) ℝ)
        (z : TangentBundle (𝓡 r) (OrthogonalSphere r)),
      orthogonalSphereTangentMap r (A * B) z =
        orthogonalSphereTangentMap r A (orthogonalSphereTangentMap r B z) := by
  -- The base action identities lift through the identity and composition chain rules.
  constructor
  · intro z
    have hid : (orthogonalSphereDiffeomorph r 1 : OrthogonalSphere r → OrthogonalSphere r) =
        id := funext (one_smul (Matrix.orthogonalGroup (Fin r) ℝ))
    change tangentMap (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r 1) z = z
    rw [hid, tangentMap_id]
    rfl
  · intro A B z
    have hcomp : (orthogonalSphereDiffeomorph r (A * B) :
        OrthogonalSphere r → OrthogonalSphere r) =
        orthogonalSphereDiffeomorph r A ∘ orthogonalSphereDiffeomorph r B :=
      funext (mul_smul A B)
    change tangentMap (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r (A * B)) z = _
    rw [hcomp, tangentMap_comp
      ((orthogonalSphereDiffeomorph r A).mdifferentiable (by simp))
      ((orthogonalSphereDiffeomorph r B).mdifferentiable (by simp))]
    rfl

/-- The scalar action on the native tangent total space is the original derivative lift. -/
instance (priority := 1100) orthogonalSphereTangentSMul (r : ℕ) :
    SMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) where
  smul := orthogonalSphereTangentMap r

/-- The original orthogonal action on the native sphere tangent bundle. -/
instance orthogonalSphereTangentMulAction (r : ℕ) :
    MulAction (Matrix.orthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) where
  smul := orthogonalSphereTangentMap r
  one_smul := (orthogonalSphereTangentMap_laws r).1
  mul_smul := (orthogonalSphereTangentMap_laws r).2

/-- Joint continuity holds for the original matrix and tangent-bundle topologies. -/
theorem continuousSMul_orthogonalSphereTangent (r : ℕ) :
    ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) := by
  classical
  let Mat := Fin r → Fin r → ℝ
  let G : Type := Matrix.orthogonalGroup (Fin r) ℝ
  let S := OrthogonalSphere r
  let J := 𝓡 r
  let P := (𝓘(ℝ, Mat)).prod J
  let s : Set Mat := {b | b ∈ Matrix.orthogonalGroup (Fin r) ℝ}
  -- Extend matrices by identity off O(r), using smoothness only on the original subset.
  let A (b : Mat) : Mat := if b ∈ s then b else (1 : Matrix (Fin r) (Fin r) ℝ)
  have horth (b : Mat) : A b ∈ Matrix.orthogonalGroup (Fin r) ℝ := by
    by_cases hb : b ∈ s
    · have hAb : A b = b := by exact ite_eq_left hb
      exact hAb.symm ▸ hb
    · have hAb : A b = (1 : Matrix (Fin r) (Fin r) ℝ) := by exact ite_eq_right hb
      exact hAb.symm ▸ (Matrix.orthogonalGroup (Fin r) ℝ).one_mem
  have hA : ContMDiffOn 𝓘(ℝ, Mat) 𝓘(ℝ, Mat) ∞ A s := by
    apply contMDiffOn_id.congr
    intro b hb
    simp [A, hb]
  let F (b : Mat) (x : S) : S := (⟨A b, horth b⟩ : G) • x
  have hF : ContMDiffOn P J ∞ (Function.uncurry F) (s ×ˢ Set.univ) :=
    contMDiffOn_orthogonalSphere_parametric_smul 𝓘(ℝ, Mat) r A s hA horth
  let D (B : G) := orthogonalSphereDiffeomorph r B
  have hD (B : G) (x : S) : D B x = B • x := rfl
  have hslice (B : G) : F B.val = D B := by
    funext x
    dsimp only [F]
    have hAB : (⟨A B.val, horth B.val⟩ : G) = B := by
      apply Subtype.ext
      exact ite_eq_left (show B.val ∈ s from B.property)
    rw [hAB]
    rfl
  let Q := G × TangentBundle J S
  let := continuousSMul_orthogonalSphere r
  constructor
  apply continuous_iff_continuousAt.mpr
  intro q₀
  change ContinuousAt (fun q : Q ↦ tangentMap J J (D q.1) q.2) q₀
  clear_value F D
  have hbase : ContinuousAt (fun q : Q ↦ q.1 • q.2.proj) q₀ :=
    continuousAt_fst.smul
      ((FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin r))
        (TangentSpace J)).continuousAt.comp continuousAt_snd)
  have hp : ContinuousAt (fun q : Q ↦ (q.1.val, q.2.proj)) q₀ :=
    (continuous_subtype_val.continuousAt.comp continuousAt_fst).prodMk
      ((FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin r))
        (TangentSpace J)).continuousAt.comp continuousAt_snd)
  -- Differentiate only in the sphere variable; the matrix parameter stays in its subset.
  have hf : ContMDiffWithinAt (P.prod J) J ∞
      (fun p : (Mat × S) × S ↦ F p.1.1 p.2)
      ((s ×ˢ Set.univ) ×ˢ Set.univ) ((q₀.1.val, q₀.2.proj), q₀.2.proj) := by
    have hcomp : ContMDiffWithinAt (P.prod J) P ∞
        (fun p : (Mat × S) × S ↦ (p.1.1, p.2))
        ((s ×ˢ Set.univ) ×ˢ Set.univ) ((q₀.1.val, q₀.2.proj), q₀.2.proj) :=
      contMDiffWithinAt_fst.fst.prodMk contMDiffWithinAt_snd
    have hFp : ContMDiffWithinAt P J ∞ (Function.uncurry F) (s ×ˢ Set.univ)
        ((q₀.1.val, q₀.2.proj) : Mat × S) :=
      hF _ ⟨q₀.1.property, Set.mem_univ _⟩
    exact hFp.comp (((q₀.1.val, q₀.2.proj), q₀.2.proj) : (Mat × S) × S) hcomp
      (show Set.MapsTo (fun p : (Mat × S) × S ↦ (p.1.1, p.2))
        ((s ×ˢ Set.univ) ×ˢ Set.univ) (s ×ˢ Set.univ) from
        fun p hp ↦ ⟨hp.1.1, hp.2⟩)
  have hg : ContMDiffWithinAt P J ∞ (Prod.snd : Mat × S → S)
      (s ×ˢ Set.univ) (q₀.1.val, q₀.2.proj) := contMDiffWithinAt_snd
  have hd := hf.mfderivWithin (f := fun p : Mat × S ↦ F p.1) hg
    (show (q₀.1.val, q₀.2.proj) ∈ s ×ˢ Set.univ from
      ⟨q₀.1.property, Set.mem_univ _⟩)
    (Set.mapsTo_univ _ _) (by simp) (uniqueMDiffOn_univ (I := J))
  -- Restrict derivative coordinates back to actual orthogonal matrices and tangent bases.
  have hdc := hd.continuousWithinAt.comp
    (f := fun q : Q ↦ (q.1.val, q.2.proj)) hp.continuousWithinAt
    (show Set.MapsTo (fun q : Q ↦ (q.1.val, q.2.proj)) Set.univ (s ×ˢ Set.univ) from
      fun q _ ↦ ⟨q.1.property, Set.mem_univ _⟩)
  have hd' : ContinuousAt (fun q : Q ↦
      ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin r)) (TangentSpace J)
        (EuclideanSpace ℝ (Fin r)) (TangentSpace J) q₀.2.proj q.2.proj
        (D q₀.1 q₀.2.proj) (D q.1 q.2.proj)
        (mfderiv J J (D q.1) q.2.proj)) q₀ := by
    rw [continuousWithinAt_univ] at hdc
    change ContinuousAt (fun q : Q ↦
      ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin r)) (TangentSpace J)
        (EuclideanSpace ℝ (Fin r)) (TangentSpace J) q₀.2.proj q.2.proj
        (F q₀.1.val q₀.2.proj) (F q.1.val q.2.proj)
        (mfderivWithin J J (F q.1.val) Set.univ q.2.proj)) q₀ at hdc
    apply hdc.congr_of_eventuallyEq
    filter_upwards [] with q
    erw [hslice q₀.1, hslice q.1, mfderivWithin_univ]
  -- Apply the same derivative to the original native tangent vector.
  have hbase' : ContinuousAt (fun q : Q ↦ D q.1 q.2.proj) q₀ := by
    simpa only [hD] using hbase
  exact ContinuousAt.clm_apply_of_inCoordinates
    (ϕ := fun q : Q ↦ mfderiv J J (D q.1) q.2.proj)
    (v := fun q : Q ↦ q.2.snd) hd' continuousAt_snd hbase'

/-- The ambient vertical reflection fixes every horizontal coordinate. -/
def orthogonalSphereVerticalIsometry (r : ℕ) :
    OrthogonalSphereAmbient r ≃ₗᵢ[ℝ] OrthogonalSphereAmbient r :=
  LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin r)))
    (LinearIsometryEquiv.neg ℝ)

/-- Vertical reflection on the original unit sphere, rather than its antipodal map. -/
def orthogonalSphereVerticalReflection (r : ℕ) :
    OrthogonalSphere r ≃ₜ OrthogonalSphere r :=
  (orthogonalSphereVerticalIsometry r).toHomeomorph.subtype (fun x ↦ by
    simp only [Metric.mem_sphere, dist_zero_right]
    change ‖x‖ = 1 ↔ ‖orthogonalSphereVerticalIsometry r x‖ = 1
    rw [(orthogonalSphereVerticalIsometry r).norm_map])

/-- The source's zero pole is south; its infinity pole is the existing north pole. -/
def orthogonalSpherePole (r : ℕ) (atInfinity : Bool) : OrthogonalSphere r :=
  if atInfinity then orthogonalSphereNorth r else -orthogonalSphereNorth r

/-- Source-normalized stereographic charts, with the same horizontal equatorial point. -/
def orthogonalSphereNormalizedChart (r : ℕ) (atInfinity : Bool) :
    OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)) :=
  let h : OrthogonalSphere r ≃ₜ OrthogonalSphere r :=
    if atInfinity then orthogonalSphereVerticalReflection r else Homeomorph.refl _
  h.toOpenPartialHomeomorph.trans
    ((orthogonalSphereStereographic r).trans
      (Homeomorph.smulOfNeZero (1 / 2 : ℝ) (by norm_num)).toOpenPartialHomeomorph)

/-- Each normalized chart covers the opposite-pole complement and respects the fixed action. -/
theorem orthogonalSphereNormalizedChart_properties (r : ℕ) (atInfinity : Bool) :
    (orthogonalSphereNormalizedChart r atInfinity).source =
        {orthogonalSpherePole r (!atInfinity)}ᶜ ∧
    (orthogonalSphereNormalizedChart r atInfinity).target = Set.univ ∧
    (orthogonalSphereNormalizedChart r atInfinity).symm 0 =
        orthogonalSpherePole r atInfinity ∧
    ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r),
      x ∈ (orthogonalSphereNormalizedChart r atInfinity).source →
      orthogonalSphereNormalizedChart r atInfinity (A • x) =
        orthogonalEuclideanIsometry r A
          (orthogonalSphereNormalizedChart r atInfinity x) := by
  classical
  -- Vertical reflection swaps the two poles without changing the horizontal action.
  let R := orthogonalSphereVerticalReflection r
  have hpos : R (-orthogonalSphereNorth r) = orthogonalSphereNorth r := by
    apply Subtype.ext
    simp [R, orthogonalSphereVerticalReflection, orthogonalSphereVerticalIsometry,
      orthogonalSphereNorth]
  have hcomm (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r) :
      R (A • x) = A • R x := by
    apply Subtype.ext
    rfl
  -- The inverse at zero follows from the original chart at its south-pole source point.
  have hzero : (orthogonalSphereStereographic r).symm 0 = -orthogonalSphereNorth r := by
    have hz : orthogonalSphereStereographic r (-orthogonalSphereNorth r) = 0 := by
      simp [orthogonalSphereStereographic, stereographic_apply_neg]
    rw [← hz]
    apply (orthogonalSphereStereographic r).left_inv
    simpa [orthogonalSphereStereographic] using
      (ne_neg_of_mem_unit_sphere ℝ (orthogonalSphereNorth r)).symm
  have hRsym : R.symm = R := by
    apply Homeomorph.ext
    intro x
    apply Subtype.ext
    rfl
  cases atInfinity
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [orthogonalSphereNormalizedChart, orthogonalSpherePole,
        orthogonalSphereStereographic]
    · simp [orthogonalSphereNormalizedChart, orthogonalSphereStereographic]
    · simpa [orthogonalSphereNormalizedChart, orthogonalSpherePole] using hzero
    · intro A x hx
      change (1 / 2 : ℝ) • orthogonalSphereStereographic r (A • x) =
        orthogonalEuclideanIsometry r A ((1 / 2 : ℝ) • orthogonalSphereStereographic r x)
      rw [(orthogonalSphereStereographic_properties r).2.2 A x ?_, map_smul]
      simpa [orthogonalSphereNormalizedChart] using hx
  · refine ⟨?_, ?_, ?_, ?_⟩
    · ext x
      have hpre : R x = orthogonalSphereNorth r ↔ x = -orthogonalSphereNorth r := by
        conv_lhs => rw [← hpos]
        exact R.injective.eq_iff
      simpa [orthogonalSphereNormalizedChart, orthogonalSpherePole,
        orthogonalSphereStereographic] using not_congr hpre
    · simp [orthogonalSphereNormalizedChart, orthogonalSphereStereographic]
    · change R.symm ((orthogonalSphereStereographic r).symm
        ((Homeomorph.smulOfNeZero (1 / 2 : ℝ) (by norm_num)).symm 0)) =
        orthogonalSphereNorth r
      simpa only [Homeomorph.smulOfNeZero_symm_apply, smul_zero, hzero, hRsym] using hpos
    · intro A x hx
      change (1 / 2 : ℝ) • orthogonalSphereStereographic r (R (A • x)) =
        orthogonalEuclideanIsometry r A
          ((1 / 2 : ℝ) • orthogonalSphereStereographic r (R x))
      rw [hcomm, (orthogonalSphereStereographic_properties r).2.2 A (R x) ?_, map_smul]
      simpa [orthogonalSphereNormalizedChart, R] using hx

/-- Both directions are smooth in the original sphere atlas on their stated domains. -/
theorem orthogonalSphereNormalizedChart_smooth (r : ℕ) (atInfinity : Bool) :
    ContMDiffOn (𝓡 r) (𝓡 r) ∞ (orthogonalSphereNormalizedChart r atInfinity)
        (orthogonalSphereNormalizedChart r atInfinity).source ∧
    ContMDiff (𝓡 r) (𝓡 r) ∞ (orthogonalSphereNormalizedChart r atInfinity).symm := by
  classical
  -- Transfer the native maximal-atlas chart through the specified horizontal frame.
  let north := orthogonalSphereNorth r
  let H := orthogonalSphereHorizontalIsometry r
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
    r (ne_zero_of_mem_unit_sphere north)).repr
  let e := U.symm.trans H
  have hmem : stereographic' r north ∈ IsManifold.maximalAtlas (𝓡 r) ∞
      (OrthogonalSphere r) :=
    IsManifold.subset_maximalAtlas ⟨north, rfl⟩
  have hS : ContMDiffOn (𝓡 r) (𝓡 r) ∞ (orthogonalSphereStereographic r)
      (orthogonalSphereStereographic r).source := by
    have h := e.contDiff.contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas hmem)
    simpa [orthogonalSphereStereographic, stereographic', e, U, H, north,
      Function.comp_def] using h
  have hSi : ContMDiff (𝓡 r) (𝓡 r) ∞ (orthogonalSphereStereographic r).symm := by
    have h := contMDiffOn_symm_of_mem_maximalAtlas hmem
    have hi : ContMDiff (𝓡 r) (𝓡 r) ∞ (stereographic' r north).symm := by
      simpa only [stereographic'_target, contMDiffOn_univ] using h
    simpa [orthogonalSphereStereographic, stereographic', e, U, H, north,
      Function.comp_def] using hi.comp e.symm.contDiff.contMDiff
  -- Reflection and the fixed rescaling preserve smoothness in these same native models.
  let R := orthogonalSphereVerticalReflection r
  have hR : ContMDiff (𝓡 r) (𝓡 r) ∞ R := by
    apply ContMDiff.codRestrict_sphere
    exact (orthogonalSphereVerticalIsometry r).contDiff.contMDiff.comp contMDiff_coe_sphere
  have hRsym : R.symm = R := by
    apply Homeomorph.ext
    intro x
    apply Subtype.ext
    rfl
  have hmul (a : ℝ) : ContMDiff (𝓡 r) (𝓡 r) ∞
      (fun x : EuclideanSpace ℝ (Fin r) ↦ a • x) :=
    (contDiff_const_smul (𝕜 := ℝ) a :
      ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin r) ↦ a • x)).contMDiff
  have hRi : ContMDiff (𝓡 r) (𝓡 r) ∞ R.symm := by
    rw [hRsym]
    exact hR
  have hscale : ContMDiff (𝓡 r) (𝓡 r) ∞
      ((Homeomorph.smulOfNeZero (1 / 2 : ℝ) (by norm_num) :
        EuclideanSpace ℝ (Fin r) ≃ₜ EuclideanSpace ℝ (Fin r)).symm) := by
    simpa only [Homeomorph.smulOfNeZero_symm_apply] using hmul ((1 / 2 : ℝ)⁻¹)
  cases atInfinity
  · constructor
    · simpa [orthogonalSphereNormalizedChart] using (hmul (1 / 2 : ℝ)).comp_contMDiffOn hS
    · simpa [orthogonalSphereNormalizedChart] using hSi.comp hscale
  · constructor
    · have h := hS.comp hR.contMDiffOn
        (Set.mapsTo_preimage R (orthogonalSphereStereographic r).source)
      simpa [orthogonalSphereNormalizedChart, R, Function.comp_def] using
        (hmul (1 / 2 : ℝ)).comp_contMDiffOn h
    · simpa [orthogonalSphereNormalizedChart, R] using hRi.comp (hSi.comp hscale)

/-- The inverse chart has the original rational horizontal and height coordinates. -/
theorem orthogonalSphereNormalizedChart_inverse_formula (r : ℕ) (atInfinity : Bool)
    (u : EuclideanSpace ℝ (Fin r)) :
    (((orthogonalSphereNormalizedChart r atInfinity).symm u : OrthogonalSphere r) :
        OrthogonalSphereAmbient r) =
      WithLp.toLp 2
        (((2 : ℝ) / (1 + ‖u‖ ^ 2)) • u,
          (if atInfinity then 1 - ‖u‖ ^ 2 else ‖u‖ ^ 2 - 1) / (1 + ‖u‖ ^ 2)) := by
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  -- Expand the existing inverse stereographic map at twice the normalized coordinate.
  have hraw :
      (((orthogonalSphereStereographic r).symm ((2 : ℝ) • u) : OrthogonalSphere r) : W) =
        WithLp.toLp 2
          (((2 : ℝ) / (1 + ‖u‖ ^ 2)) • u,
            (‖u‖ ^ 2 - 1) / (1 + ‖u‖ ^ 2)) := by
    change stereoInvFunAux (orthogonalSphereNorth r : W)
      (WithLp.toLp 2 (((2 : ℝ) • u), (0 : ℝ))) = _
    rw [stereoInvFunAux_apply]
    have hnorm : ‖(WithLp.toLp 2 (((2 : ℝ) • u), (0 : ℝ)) : W)‖ ^ 2 =
        4 * ‖u‖ ^ 2 := by
      rw [WithLp.norm_toLp_fst, norm_smul]
      norm_num [mul_pow]
    rw [hnorm]
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change (4 * ‖u‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • ((2 : ℝ) • u) +
        (4 * ‖u‖ ^ 2 - 4) • (0 : V)) = (2 / (1 + ‖u‖ ^ 2)) • u
      simp only [smul_zero, add_zero, smul_smul]
      congr 1
      field_simp
      ring
    · change (4 * ‖u‖ ^ 2 + 4)⁻¹ * ((4 : ℝ) * 0 + (4 * ‖u‖ ^ 2 - 4) * 1) = _
      field_simp
      ring
  -- The upper chart changes only the height sign, leaving the horizontal coordinate fixed.
  cases atInfinity
  · change (((orthogonalSphereStereographic r).symm
        ((1 / 2 : ℝ)⁻¹ • u) : OrthogonalSphere r) : W) = _
    norm_num only [one_div, inv_inv] at *
    exact hraw
  · change (orthogonalSphereVerticalIsometry r).symm
      (((orthogonalSphereStereographic r).symm
        ((1 / 2 : ℝ)⁻¹ • u) : OrthogonalSphere r) : W) = _
    norm_num only [one_div, inv_inv] at *
    rw [hraw]
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · change -((‖u‖ ^ 2 - 1) / (1 + ‖u‖ ^ 2)) = (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2)
      ring

/-- The overlap transition is inversion, whose equatorial derivative is actual reflection. -/
theorem orthogonalSphereNormalizedChart_transition (r : ℕ) (atInfinity : Bool) :
    (∀ u : EuclideanSpace ℝ (Fin r), u ≠ 0 →
      orthogonalSphereNormalizedChart r (!atInfinity)
          ((orthogonalSphereNormalizedChart r atInfinity).symm u) =
        (‖u‖ ^ 2)⁻¹ • u) ∧
    ∀ u : EuclideanSpace ℝ (Fin r), ‖u‖ = 1 →
      fderiv ℝ (fun v : EuclideanSpace ℝ (Fin r) ↦
          orthogonalSphereNormalizedChart r (!atInfinity)
            ((orthogonalSphereNormalizedChart r atInfinity).symm v)) u =
        ((ℝ ∙ u)ᗮ.reflection).toContinuousLinearEquiv.toContinuousLinearMap := by
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  -- In the specified horizontal frame, normalized projection has its familiar denominator.
  have hprojection (x : W) :
      orthogonalSphereHorizontalIsometry r
        ((ℝ ∙ (orthogonalSphereNorth r : W))ᗮ.orthogonalProjectionOnto x) = x.fst := by
    change ((ℝ ∙ (orthogonalSphereNorth r : W))ᗮ.orthogonalProjectionOnto x).val.fst = _
    rw [Submodule.orthogonalProjectionOnto_orthogonal]
    change (x - (ℝ ∙ (orthogonalSphereNorth r : W)).starProjection x).fst = x.fst
    rw [Submodule.starProjection_unit_singleton ℝ
      (norm_eq_of_mem_sphere (orthogonalSphereNorth r))]
    simp [W, orthogonalSphereNorth]
  have hstereo (x : OrthogonalSphere r) :
      orthogonalSphereStereographic r x = (2 / (1 - x.val.snd)) • x.val.fst := by
    change orthogonalSphereHorizontalIsometry r
      (stereographic (norm_eq_of_mem_sphere (orthogonalSphereNorth r)) x) = _
    rw [stereographic_apply, map_smul, hprojection]
    simp [orthogonalSphereNorth, WithLp.prod_inner_apply, RCLike.inner_apply]
  have hforward (b : Bool) (x : OrthogonalSphere r) :
      orthogonalSphereNormalizedChart r b x =
        (if b then (1 + x.val.snd)⁻¹ else (1 - x.val.snd)⁻¹) • x.val.fst := by
    cases b
    · change (1 / 2 : ℝ) • orthogonalSphereStereographic r x = _
      rw [hstereo, smul_smul]
      congr 1
      simp only [Bool.false_eq_true, ite_false]
      ring
    · change (1 / 2 : ℝ) • orthogonalSphereStereographic r
        (orthogonalSphereVerticalReflection r x) = _
      rw [hstereo]
      change (1 / 2 : ℝ) • ((2 / (1 - -x.val.snd)) • x.val.fst) = _
      rw [smul_smul]
      congr 1
      simp only [ite_true, sub_neg_eq_add]
      ring
  have htransition (u : V) (hu : u ≠ 0) :
      orthogonalSphereNormalizedChart r (!atInfinity)
          ((orthogonalSphereNormalizedChart r atInfinity).symm u) =
        (‖u‖ ^ 2)⁻¹ • u := by
    rw [hforward, orthogonalSphereNormalizedChart_inverse_formula]
    have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hden : 1 + ‖u‖ ^ 2 ≠ 0 := by positivity
    cases atInfinity <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true, WithLp.toLp_fst, WithLp.toLp_snd] <;>
      rw [smul_smul] <;> congr 1 <;> field_simp [hn] <;> ring_nf
    all_goals field_simp [hn]
  refine ⟨htransition, ?_⟩
  intro u hu
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  -- The overlap agrees near this nonzero point with inversion in the unit sphere.
  have hlocal : (fun v : V ↦ orthogonalSphereNormalizedChart r (!atInfinity)
      ((orthogonalSphereNormalizedChart r atInfinity).symm v)) =ᶠ[𝓝 u]
        (fun v : V ↦ (‖v‖ ^ 2)⁻¹ • v) := by
    filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hu0] with v hv
    exact htransition v hv
  rw [hlocal.fderiv_eq]
  have hi := (hasFDerivAt_inv (show ‖u‖ ^ 2 ≠ 0 by rw [hu]; norm_num)).comp u
    (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have hd := hi.smul (hasFDerivAt_id u)
  change HasFDerivAt (fun v : V ↦ (‖v‖ ^ 2)⁻¹ • v) _ u at hd
  rw [hd.fderiv]
  ext v
  simp [hu, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    ContinuousLinearMap.smulRight_apply]
  ring

/-- The normalized coordinate derivative pulls back the specified round metric conformally. -/
theorem orthogonalSphereNormalizedChart_roundMetric (r : ℕ) (atInfinity : Bool)
    (u v w : EuclideanSpace ℝ (Fin r)) :
    (orthogonalSphereRoundMetric r).inner
        ((orthogonalSphereNormalizedChart r atInfinity).symm u)
        (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u v)
        (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u w) =
      (4 / (1 + ‖u‖ ^ 2) ^ 2) * inner ℝ v w := by
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  let e := orthogonalSphereNormalizedChart r atInfinity
  let s : ℝ := if atInfinity then -1 else 1
  let d : ℝ := 1 + ‖u‖ ^ 2
  have hd0 : d ≠ 0 := by dsimp [d]; positivity
  -- Differentiate the exact inverse formula in the fixed horizontal and height coordinates.
  have hn := (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have hi := (hasFDerivAt_inv hd0).comp u ((hasFDerivAt_const (1 : ℝ) u).add hn)
  have hh := ((hasFDerivAt_const (2 : ℝ) u).mul hi).smul (hasFDerivAt_id u)
  have hv := ((hasFDerivAt_const s u).mul (hn.sub (hasFDerivAt_const (1 : ℝ) u))).mul hi
  let p := (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.toContinuousLinearMap
  have hp := p.hasFDerivAt.comp u (hh.prodMk hv)
  have hformula : (fun y : V ↦ ((e.symm y : OrthogonalSphere r) : W)) =
      (fun y : V ↦ WithLp.toLp 2
        (((2 : ℝ) * (1 + ‖y‖ ^ 2)⁻¹) • y, (s * (‖y‖ ^ 2 - 1)) * (1 + ‖y‖ ^ 2)⁻¹)) := by
    funext y
    rw [orthogonalSphereNormalizedChart_inverse_formula]
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [div_eq_mul_inv]
    · cases atInfinity <;> simp [s, div_eq_mul_inv]
  have hderiv := hp
  change HasFDerivAt (𝕜 := ℝ) (fun y : V ↦ WithLp.toLp 2
    (((2 : ℝ) * (1 + ‖y‖ ^ 2)⁻¹) • y,
      (s * (‖y‖ ^ 2 - 1)) * (1 + ‖y‖ ^ 2)⁻¹)) _ u at hderiv
  rw [← hformula] at hderiv
  have hinc : MDifferentiable (𝓡 r) 𝓘(ℝ, W) (fun x : OrthogonalSphere r ↦ x.val) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)
  have he : MDifferentiable (𝓡 r) (𝓡 r) e.symm :=
    (orthogonalSphereNormalizedChart_smooth r atInfinity).2.mdifferentiable (by simp)
  have hD (z : V) :
      (mfderiv (𝓡 r) 𝓘(ℝ, W) (fun x : OrthogonalSphere r ↦ x.val) (e.symm u)
        (mfderiv (𝓡 r) (𝓡 r) e.symm u z) : W) =
      WithLp.toLp 2
        (((2 / d) • z - (4 * inner ℝ u z / d ^ 2) • u), s * (4 * inner ℝ u z / d ^ 2)) := by
    erw [← mfderiv_comp_apply u (hinc (e.symm u)) (he u) z]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun y : V ↦ ((e.symm y : OrthogonalSphere r) : W)) u z = _
    rw [hderiv.fderiv]
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · ext i
      simp [p, d, V, ContinuousLinearMap.smulRight_apply]
      field_simp
      ring
    · simp [p, d, V, ContinuousLinearMap.smulRight_apply]
      field_simp
      ring
  -- The mixed radial terms cancel in the original ambient L² inner product.
  rw [orthogonalSphereRoundMetric_inner, hD v, hD w]
  simp only [WithLp.prod_inner_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, RCLike.inner_apply, map_mul, conj_trivial]
  rw [real_inner_comm w u, real_inner_comm v u]
  cases atInfinity <;> dsimp [s, d] <;> field_simp <;> ring

/-- Complex coordinates `u+I*v` give the actual tangent map of the inverse pole chart. -/
def orthogonalSphereTangentChartMap (r : ℕ) (atInfinity : Bool)
    (z : EuclideanSpace ℂ (Fin r)) : TangentBundle (𝓡 r) (OrthogonalSphere r) :=
  let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).re)
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (z i).im)
  ⟨(orthogonalSphereNormalizedChart r atInfinity).symm u,
    mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u v⟩

/-- The pole tangent parametrization is continuous in the actual total-space topology. -/
theorem continuous_orthogonalSphereTangentChartMap (r : ℕ) (atInfinity : Bool) :
    Continuous (orthogonalSphereTangentChartMap r atInfinity) := by
  let V := EuclideanSpace ℝ (Fin r)
  let C := EuclideanSpace ℂ (Fin r)
  let re (z : C) : V := WithLp.toLp 2 (fun i ↦ (z i).re)
  let im (z : C) : V := WithLp.toLp 2 (fun i ↦ (z i).im)
  have hre : Continuous re := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
    (continuous_pi fun i ↦ Complex.continuous_re.comp
      (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) i))
  have him : Continuous im := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
    (continuous_pi fun i ↦ Complex.continuous_im.comp
      (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) i))
  -- The model-space homeomorphism retains the native tangent topology on the domain.
  have hinput : Continuous (fun z : C ↦ (⟨re z, im z⟩ : TangentBundle (𝓡 r) V)) :=
    (tangentBundleModelSpaceHomeomorph (𝓡 r)).symm.continuous.comp (hre.prodMk him)
  have ht : Continuous (tangentMap (𝓡 r) (𝓡 r)
      (orthogonalSphereNormalizedChart r atInfinity).symm) :=
    (orthogonalSphereNormalizedChart_smooth r atInfinity).2.continuous_tangentMap (by simp)
  change Continuous (tangentMap (𝓡 r) (𝓡 r)
    (orthogonalSphereNormalizedChart r atInfinity).symm ∘
      fun z : C ↦ (⟨re z, im z⟩ : TangentBundle (𝓡 r) V))
  exact ht.comp hinput

/-- The pole tangent chart as a continuous map for equivariant open extension in K-theory. -/
def orthogonalSphereTangentChart (r : ℕ) (atInfinity : Bool) :
    C(EuclideanSpace ℂ (Fin r), TangentBundle (𝓡 r) (OrthogonalSphere r)) where
  toFun := orthogonalSphereTangentChartMap r atInfinity
  continuous_toFun := continuous_orthogonalSphereTangentChartMap r atInfinity

/-- The actual tangent chart is an open embedding; it is not asserted to be proper. -/
theorem orthogonalSphereTangentChart_isOpenEmbedding (r : ℕ) (atInfinity : Bool) :
    IsOpenEmbedding (orthogonalSphereTangentChart r atInfinity) := by
  let V := EuclideanSpace ℝ (Fin r)
  let C := EuclideanSpace ℂ (Fin r)
  let e := orthogonalSphereNormalizedChart r atInfinity
  have het : e.target = Set.univ :=
    (orthogonalSphereNormalizedChart_properties r atInfinity).2.1
  let re (z : C) : V := WithLp.toLp 2 (fun i ↦ (z i).re)
  let im (z : C) : V := WithLp.toLp 2 (fun i ↦ (z i).im)
  change IsOpenEmbedding (fun z : C ↦ tangentMap (𝓡 r) (𝓡 r) e.symm
    (⟨re z, im z⟩ : TangentBundle (𝓡 r) V))
  have hs : ContMDiffOn (𝓡 r) (𝓡 r) ∞ e e.source ∧
      ContMDiff (𝓡 r) (𝓡 r) ∞ e.symm :=
    orthogonalSphereNormalizedChart_smooth r atInfinity
  clear_value e
  have he : e.MDifferentiable (𝓡 r) (𝓡 r) :=
    ⟨hs.1.mdifferentiableOn (by simp), hs.2.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  -- Lift the actual smooth chart and inverse to a partial homeomorphism of tangent spaces.
  let t : OpenPartialHomeomorph (TangentBundle (𝓡 r) V)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
    { toFun := tangentMap (𝓡 r) (𝓡 r) e.symm
      invFun := tangentMap (𝓡 r) (𝓡 r) e
      source := Set.univ
      target := TotalSpace.proj ⁻¹' e.source
      map_source' := by
        intro z _
        exact e.map_target (het.symm ▸ Set.mem_univ z.proj)
      map_target' := fun _ _ ↦ Set.mem_univ _
      left_inv' := by
        intro z _
        have hz : z.proj ∈ e.target := het.symm ▸ Set.mem_univ z.proj
        apply TotalSpace.ext (e.right_inv hz)
        apply heq_of_eq
        exact congrArg (fun L ↦ L z.snd) (he.comp_symm_deriv hz)
      right_inv' := by
        intro z hz
        apply TotalSpace.ext (e.left_inv hz)
        apply heq_of_eq
        exact congrArg (fun L ↦ L z.snd) (he.symm_comp_deriv hz)
      open_source := isOpen_univ
      open_target := e.open_source.preimage
        (FiberBundle.continuous_proj V (TangentSpace (𝓡 r)))
      continuousOn_toFun := (hs.2.continuous_tangentMap (by simp)).continuousOn
      continuousOn_invFun := by
        intro z hz
        have hlocal := (hs.1 z.proj hz).contMDiffAt (e.open_source.mem_nhds hz)
        exact (hlocal.continuousAt_tangentMap (by simp)).continuousWithinAt }
  have ht : IsOpenEmbedding (tangentMap (𝓡 r) (𝓡 r) e.symm) :=
    t.isOpenEmbedding rfl
  clear t
  -- Coordinatewise real and imaginary parts are a homeomorphism, in the original norms.
  have hre : Continuous re := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
    (continuous_pi fun i ↦ Complex.continuous_re.comp
      (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) i))
  have him : Continuous im := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
    (continuous_pi fun i ↦ Complex.continuous_im.comp
      (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) i))
  let c : C ≃ₜ V × V :=
    { toFun := fun z ↦ (re z, im z)
      invFun := fun p ↦ WithLp.toLp 2 (fun i ↦ (p.1 i : ℂ) + (p.2 i : ℂ) * Complex.I)
      left_inv := by
        intro z
        ext i
        exact Complex.re_add_im (z i)
      right_inv := by
        intro p
        apply Prod.ext <;> ext i <;> simp [re, im]
      continuous_toFun := hre.prodMk him
      continuous_invFun := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).comp
        (continuous_pi fun i ↦
          (Complex.continuous_ofReal.comp
            ((PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℝ) i).comp continuous_fst)).add
          ((Complex.continuous_ofReal.comp
            ((PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℝ) i).comp continuous_snd)).mul
            continuous_const)) }
  exact ht.comp ((tangentBundleModelSpaceHomeomorph (𝓡 r)).symm.isOpenEmbedding.comp
    c.isOpenEmbedding)

/-- Its range consists of all native tangent fibers except the fiber over the opposite pole. -/
theorem orthogonalSphereTangentChart_range (r : ℕ) (atInfinity : Bool) :
    Set.range (orthogonalSphereTangentChart r atInfinity) =
      {z : TangentBundle (𝓡 r) (OrthogonalSphere r) |
        z.proj ≠ orthogonalSpherePole r (!atInfinity)} := by
  let e := orthogonalSphereNormalizedChart r atInfinity
  have hes : e.source = {orthogonalSpherePole r (!atInfinity)}ᶜ :=
    (orthogonalSphereNormalizedChart_properties r atInfinity).1
  have het : e.target = Set.univ :=
    (orthogonalSphereNormalizedChart_properties r atInfinity).2.1
  have he : e.MDifferentiable (𝓡 r) (𝓡 r) :=
    ⟨(orthogonalSphereNormalizedChart_smooth r atInfinity).1.mdifferentiableOn (by simp),
      (orthogonalSphereNormalizedChart_smooth r atInfinity).2.mdifferentiable (by simp)
        |>.mdifferentiableOn⟩
  ext t
  constructor
  · rintro ⟨z, rfl⟩
    have hu : WithLp.toLp 2 (fun i ↦ (z i).re) ∈ e.target := by rw [het]; trivial
    have hs := e.map_target hu
    change e.symm (WithLp.toLp 2 (fun i ↦ (z i).re)) ≠ _
    simpa only [hes,
      Set.mem_compl_iff, Set.mem_singleton_iff] using hs
  · intro ht
    have hx : t.proj ∈ e.source := by
      simpa only [hes,
        Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq] using ht
    -- The inverse chart differential is onto the actual tangent fiber over this base.
    obtain ⟨w, hw⟩ := he.symm.mfderiv_surjective (e.map_source hx) t.snd
    let w' : EuclideanSpace ℝ (Fin r) := w
    let z : EuclideanSpace ℂ (Fin r) :=
      WithLp.toLp 2 (fun i ↦ Complex.mk (e t.proj i) (w' i))
    refine ⟨z, ?_⟩
    apply TotalSpace.ext (e.left_inv hx)
    apply heq_of_eq
    change mfderiv (𝓡 r) (𝓡 r) e.symm (e t.proj) w = t.snd
    exact hw

/-- The same complexified real matrix action intertwines the native derivative action. -/
theorem orthogonalSphereTangentChart_equivariant (r : ℕ) (atInfinity : Bool)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : EuclideanSpace ℂ (Fin r)) :
    orthogonalSphereTangentChart r atInfinity (A • z) =
      A • orthogonalSphereTangentChart r atInfinity z := by
  let V := EuclideanSpace ℝ (Fin r)
  let e := orthogonalSphereNormalizedChart r atInfinity
  let U := orthogonalEuclideanIsometry r A
  let D := orthogonalSphereDiffeomorph r A
  have ht : e.target = Set.univ :=
    (orthogonalSphereNormalizedChart_properties r atInfinity).2.1
  have hsource (u : V) : e.symm u ∈ e.source :=
    e.map_target (ht.symm ▸ Set.mem_univ u)
  -- The same forward-chart equivariance determines the actual inverse chart.
  have hinv (u : V) : D (e.symm u) = e.symm (U u) := by
    have hDsource : D (e.symm u) ∈ e.source := by
      rw [(orthogonalSphereNormalizedChart_properties r atInfinity).1]
      have h := (orthogonalSphereNormalizedChart_properties r atInfinity).1
      have hp : D (orthogonalSpherePole r (!atInfinity)) =
          orthogonalSpherePole r (!atInfinity) := by
        have hn : D (orthogonalSphereNorth r) = orthogonalSphereNorth r :=
          smul_orthogonalSphereNorth r A
        cases atInfinity
        · exact hn
        · apply Subtype.ext
          change orthogonalSphereBlockIsometry r A
            (-(orthogonalSphereNorth r : OrthogonalSphereAmbient r)) =
              -(orthogonalSphereNorth r : OrthogonalSphereAmbient r)
          rw [map_neg]
          exact congrArg Neg.neg (congrArg Subtype.val hn)
      intro heq
      have heq' : e.symm u = orthogonalSpherePole r (!atInfinity) := D.injective (heq.trans hp.symm)
      have := hsource u
      rw [h, Set.mem_compl_iff, Set.mem_singleton_iff] at this
      exact this heq'
    apply e.injOn hDsource (hsource (U u))
    rw [e.right_inv (ht.symm ▸ Set.mem_univ (U u))]
    exact ((orthogonalSphereNormalizedChart_properties r atInfinity).2.2.2 A
      (e.symm u) (hsource u)).trans
      (congrArg U (e.right_inv (ht.symm ▸ Set.mem_univ u)))
  let re (w : EuclideanSpace ℂ (Fin r)) : V := WithLp.toLp 2 (fun i ↦ (w i).re)
  let im (w : EuclideanSpace ℂ (Fin r)) : V := WithLp.toLp 2 (fun i ↦ (w i).im)
  have hre : re (A • z) = U (re z) := by
    ext i
    change (∑ j, (A.val i j : ℂ) * z j).re = ∑ j, A.val i j * (z j).re
    simp
  have him : im (A • z) = U (im z) := by
    ext i
    change (∑ j, (A.val i j : ℂ) * z j).im = ∑ j, A.val i j * (z j).im
    simp
  -- Differentiate the inverse-chart identity at the same real base and imaginary vector.
  have hfun : D ∘ e.symm = e.symm ∘ U := funext hinv
  have hEs := (orthogonalSphereNormalizedChart_smooth r atInfinity).2.mdifferentiable (by simp)
  have hUs : MDifferentiable (𝓡 r) (𝓡 r) U :=
    (U.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
  have hDs := D.mdifferentiable (by simp)
  have hmaps := congrArg (fun f ↦ tangentMap (𝓡 r) (𝓡 r) f
    (⟨re z, im z⟩ : TangentBundle (𝓡 r) V)) hfun
  rw [tangentMap_comp hDs hEs, tangentMap_comp hEs hUs] at hmaps
  have hU : tangentMap (𝓡 r) (𝓡 r) U
      (⟨re z, im z⟩ : TangentBundle (𝓡 r) V) = ⟨U (re z), U (im z)⟩ := by
    apply TotalSpace.ext
    · rfl
    apply heq_of_eq
    change mfderiv (𝓡 r) (𝓡 r) U (re z) (im z) = U (im z)
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ U.toContinuousLinearEquiv.toContinuousLinearMap (re z) (im z) = U (im z)
    rw [U.toContinuousLinearEquiv.toContinuousLinearMap.fderiv]
    rfl
  change tangentMap (𝓡 r) (𝓡 r) e.symm
    (⟨re (A • z), im (A • z)⟩ : TangentBundle (𝓡 r) V) =
      tangentMap (𝓡 r) (𝓡 r) D (tangentMap (𝓡 r) (𝓡 r) e.symm ⟨re z, im z⟩)
  rw [hre, him]
  simpa only [Function.comp_apply, hU] using hmaps.symm

/-- The ambient height gradient has a unique representative in each actual native tangent fiber. -/
theorem existsUnique_orthogonalSphereHeightGradient (r : ℕ) (x : OrthogonalSphere r) :
    ∃! v : TangentSpace (𝓡 r) x,
      mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r)
          (fun y : OrthogonalSphere r ↦ y.val) x v =
        (orthogonalSphereNorth r : OrthogonalSphereAmbient r) - x.val.snd • x.val := by
  -- The proposed ambient vector is perpendicular to the unit radius.
  let W := OrthogonalSphereAmbient r
  let L := mfderiv (𝓡 r) 𝓘(ℝ, W) (fun y : OrthogonalSphere r ↦ y.val) x
  let w : W := (orthogonalSphereNorth r : W) - x.val.snd • x.val
  have hnorm : ‖x.val‖ = 1 := by simp [Metric.mem_sphere, dist_zero_right]
  have hperp : w ∈ (ℝ ∙ x.val)ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change inner ℝ x.val ((orthogonalSphereNorth r : W) - x.val.snd • x.val) = 0
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hnorm]
    simp [orthogonalSphereNorth, WithLp.prod_inner_apply, RCLike.inner_apply]
  -- The native sphere inclusion has precisely this range and is injective.
  have hrange : L.range = (ℝ ∙ x.val)ᗮ := by
    exact range_mvfderiv_subtypeVal x
  have hinj : Function.Injective L := injective_mvfderiv_subtypeVal_sphere x
  have hw : w ∈ L.range := hrange.symm ▸ hperp
  obtain ⟨v, hv⟩ := hw
  refine ⟨v, hv, ?_⟩
  intro z hz
  exact hinj (hz.trans hv.symm)

/-- The native height gradient, specified independently by its unique ambient derivative image. -/
def orthogonalSphereHeightGradient (r : ℕ) (x : OrthogonalSphere r) :
    TangentSpace (𝓡 r) x :=
  (existsUnique_orthogonalSphereHeightGradient r x).exists.choose

/-- The chosen tangent field has exactly the intended ambient derivative image. -/
theorem orthogonalSphereHeightGradient_ambient (r : ℕ) (x : OrthogonalSphere r) :
    mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r)
        (fun y : OrthogonalSphere r ↦ y.val) x (orthogonalSphereHeightGradient r x) =
      (orthogonalSphereNorth r : OrthogonalSphereAmbient r) - x.val.snd • x.val := by
  -- Use precisely the witness chosen by the original field definition.
  exact (existsUnique_orthogonalSphereHeightGradient r x).exists.choose_spec

/-- This is the gradient of actual ambient height for the already fixed round metric. -/
theorem orthogonalSphereHeightGradient_gradient (r : ℕ) (x : OrthogonalSphere r)
    (v : TangentSpace (𝓡 r) x) :
    (orthogonalSphereRoundMetric r).inner x (orthogonalSphereHeightGradient r x) v =
      mfderiv (𝓡 r) 𝓘(ℝ, ℝ) (fun y : OrthogonalSphere r ↦ y.val.snd) x v := by
  let W := OrthogonalSphereAmbient r
  let w : W := mfderiv (𝓡 r) 𝓘(ℝ, W) (fun y : OrthogonalSphere r ↦ y.val) x v
  have hw : w ∈ (ℝ ∙ x.val)ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := r) x]
    exact ⟨v, rfl⟩
  have hperp : inner ℝ x.val w = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
  -- The induced round metric pairs the ambient gradient with a tangent ambient vector.
  rw [orthogonalSphereRoundMetric_inner, orthogonalSphereHeightGradient_ambient]
  change inner ℝ ((orthogonalSphereNorth r : W) - x.val.snd • x.val) w = _
  rw [inner_sub_left, inner_smul_left, hperp]
  simp only [mul_zero, sub_zero]
  -- The differential of height is exactly the final coordinate of the inclusion differential.
  let p : W →L[ℝ] ℝ := WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin r)) ℝ
  have hp : MDifferentiable 𝓘(ℝ, W) 𝓘(ℝ, ℝ) p :=
    (p.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
  have hinc : MDifferentiable (𝓡 r) 𝓘(ℝ, W) (fun y : OrthogonalSphere r ↦ y.val) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)
  change inner ℝ (orthogonalSphereNorth r : W) w =
    mfderiv (𝓡 r) 𝓘(ℝ, ℝ) (p ∘ fun y : OrthogonalSphere r ↦ y.val) x v
  rw [mfderiv_comp_apply x (hp x.val) (hinc x)]
  rw [mfderiv_eq_fderiv]
  change inner ℝ (orthogonalSphereNorth r : W) w = fderiv ℝ p x.val w
  rw [p.fderiv]
  simp [p, W, orthogonalSphereNorth, WithLp.prod_inner_apply, RCLike.inner_apply]

/-- The same gradient has exactly the two coordinate vectors required by the source homotopy. -/
theorem orthogonalSphereHeightGradient_chart (r : ℕ) (atInfinity : Bool)
    (u : EuclideanSpace ℝ (Fin r)) :
    mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereNormalizedChart r atInfinity).symm u
        ((if atInfinity then (-1 : ℝ) else 1) • u) =
      orthogonalSphereHeightGradient r
        ((orthogonalSphereNormalizedChart r atInfinity).symm u) := by
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  let e := orthogonalSphereNormalizedChart r atInfinity
  let s : ℝ := if atInfinity then -1 else 1
  let d : ℝ := 1 + ‖u‖ ^ 2
  have hd0 : d ≠ 0 := by dsimp [d]; positivity
  -- Differentiate the original inverse formula in horizontal and height coordinates.
  have hn := (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have hi := (hasFDerivAt_inv hd0).comp u ((hasFDerivAt_const (1 : ℝ) u).add hn)
  have hh := ((hasFDerivAt_const (2 : ℝ) u).mul hi).smul (hasFDerivAt_id u)
  have hv := ((hasFDerivAt_const s u).mul (hn.sub (hasFDerivAt_const (1 : ℝ) u))).mul hi
  let p := (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.toContinuousLinearMap
  have hp := p.hasFDerivAt.comp u (hh.prodMk hv)
  have hformula : (fun y : V ↦ ((e.symm y : OrthogonalSphere r) : W)) =
      (fun y : V ↦ WithLp.toLp 2
        (((2 : ℝ) * (1 + ‖y‖ ^ 2)⁻¹) • y, (s * (‖y‖ ^ 2 - 1)) * (1 + ‖y‖ ^ 2)⁻¹)) := by
    funext y
    rw [orthogonalSphereNormalizedChart_inverse_formula]
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [div_eq_mul_inv]
    · cases atInfinity <;> simp [s, div_eq_mul_inv]
  have hderiv := hp
  change HasFDerivAt (𝕜 := ℝ) (fun y : V ↦ WithLp.toLp 2
    (((2 : ℝ) * (1 + ‖y‖ ^ 2)⁻¹) • y,
      (s * (‖y‖ ^ 2 - 1)) * (1 + ‖y‖ ^ 2)⁻¹)) _ u at hderiv
  rw [← hformula] at hderiv
  have hinc : MDifferentiable (𝓡 r) 𝓘(ℝ, W) (fun x : OrthogonalSphere r ↦ x.val) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)
  have he : MDifferentiable (𝓡 r) (𝓡 r) e.symm :=
    (orthogonalSphereNormalizedChart_smooth r atInfinity).2.mdifferentiable (by simp)
  have hD (z : V) :
      (mfderiv (𝓡 r) 𝓘(ℝ, W) (fun x : OrthogonalSphere r ↦ x.val) (e.symm u)
        (mfderiv (𝓡 r) (𝓡 r) e.symm u z) : W) =
      WithLp.toLp 2
        (((2 / d) • z - (4 * inner ℝ u z / d ^ 2) • u), s * (4 * inner ℝ u z / d ^ 2)) := by
    erw [← mfderiv_comp_apply u (hinc (e.symm u)) (he u)]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun y : V ↦ ((e.symm y : OrthogonalSphere r) : W)) u z = _
    rw [hderiv.fderiv]
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · ext i
      simp [p, d, V, ContinuousLinearMap.smulRight_apply]
      field_simp
      ring
    · simp [p, d, V, ContinuousLinearMap.smulRight_apply]
      field_simp
      ring
  -- Specializing to u or -u gives the prescribed ambient height-gradient vector.
  -- Injectivity identifies this with the same chosen vector in the native tangent fiber.
  have hInjective : Function.Injective
      (mfderiv (𝓡 r) 𝓘(ℝ, W) (fun y : OrthogonalSphere r ↦ y.val) (e.symm u)) := by
    convert! injective_mvfderiv_subtypeVal_sphere (e.symm u)
  apply hInjective
  rw [orthogonalSphereHeightGradient_ambient, hD]
  rw [orthogonalSphereNormalizedChart_inverse_formula]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · cases atInfinity <;> ext i <;> simp [d, V, orthogonalSphereNorth]
    all_goals field_simp
    all_goals ring
  · cases atInfinity <;> simp [s, d, V, orthogonalSphereNorth]
    all_goals field_simp
    all_goals ring

/-- The specified gradient is a continuous section in the native tangent topology. -/
theorem continuous_orthogonalSphereHeightGradient (r : ℕ) :
    Continuous (fun x : OrthogonalSphere r ↦
      (⟨x, orthogonalSphereHeightGradient r x⟩ :
        TangentBundle (𝓡 r) (OrthogonalSphere r))) := by
  let Y (x : OrthogonalSphere r) : TangentBundle (𝓡 r) (OrthogonalSphere r) :=
    ⟨x, orthogonalSphereHeightGradient r x⟩
  have hlocal (b : Bool) : ContinuousOn Y (orthogonalSphereNormalizedChart r b).source := by
    let e := orthogonalSphereNormalizedChart r b
    let s : ℝ := if b then -1 else 1
    let c (u : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℂ (Fin r) :=
      WithLp.toLp 2 (fun i ↦ (u i : ℂ) + (s * u i : ℝ) * Complex.I)
    have hc : Continuous c := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).comp
      (continuous_pi fun i ↦
        (Complex.continuous_ofReal.comp
          (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℝ) i)).add
        ((Complex.continuous_ofReal.comp
          (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℝ) i))).mul
          continuous_const))
    have hcont : ContinuousOn (orthogonalSphereTangentChart r b ∘ c ∘ e) e.source :=
      (orthogonalSphereTangentChart r b).continuous.comp_continuousOn
        (hc.comp_continuousOn e.continuousOn)
    -- The chart formula identifies this local continuous section with the same chosen field.
    apply hcont.congr
    intro x hx
    have hre : WithLp.toLp 2 (fun i ↦ (c (e x) i).re) = e x := by
      ext i
      simp [c]
    have him : WithLp.toLp 2 (fun i ↦ (c (e x) i).im) = s • e x := by
      ext i
      simp [c]
    change Y x = orthogonalSphereTangentChartMap r b (c (e x))
    unfold orthogonalSphereTangentChartMap
    dsimp only
    rw [hre, him, orthogonalSphereHeightGradient_chart]
    rw [e.left_inv hx]
  -- The two original opposite-pole complements cover the sphere, also in dimension zero.
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨b, hb⟩ : ∃ b : Bool, x ∈ (orthogonalSphereNormalizedChart r b).source := by
    by_cases hx : x = orthogonalSphereNorth r
    · refine ⟨true, ?_⟩
      rw [(orthogonalSphereNormalizedChart_properties r true).1]
      simpa [orthogonalSpherePole, hx] using
        (ne_neg_of_mem_unit_sphere ℝ (orthogonalSphereNorth r))
    · refine ⟨false, ?_⟩
      simpa [(orthogonalSphereNormalizedChart_properties r false).1,
        orthogonalSpherePole] using hx
  exact (hlocal b x hb).continuousAt
    ((orthogonalSphereNormalizedChart r b).open_source.mem_nhds hb)

/-- The height gradient is equivariant for the same native derivative action. -/
theorem orthogonalSphereHeightGradient_equivariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r) :
    mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x
        (orthogonalSphereHeightGradient r x) =
      orthogonalSphereHeightGradient r (A • x) := by
  let W := OrthogonalSphereAmbient r
  let inc : OrthogonalSphere r → W := Subtype.val
  let D := orthogonalSphereDiffeomorph r A
  let B := orthogonalSphereBlockIsometry r A
  have hinc : MDifferentiable (𝓡 r) 𝓘(ℝ, W) inc :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)
  have hD : MDifferentiable (𝓡 r) (𝓡 r) D := D.mdifferentiable (by simp)
  have hB : MDifferentiable 𝓘(ℝ, W) 𝓘(ℝ, W) B :=
    (B.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp)
  have hlin : (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, W) B x.val : W →L[ℝ] W) =
      B.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ B.toContinuousLinearEquiv.toContinuousLinearMap x.val = _
    exact B.toContinuousLinearEquiv.toContinuousLinearMap.fderiv
  -- The original inclusion intertwines the native action with its actual ambient block map.
  have hfun : inc ∘ D = B ∘ inc := rfl
  have hd := congrArg (fun f : OrthogonalSphere r → W ↦ mvfderiv (𝓡 r) f x) hfun
  rw [mvfderiv_comp x (hinc (D x)) (hD x),
    mvfderiv_comp x (hB (inc x)) (hinc x)] at hd
  have hv := congrArg (fun L ↦ L (orthogonalSphereHeightGradient r x)) hd
  change mfderiv (𝓡 r) 𝓘(ℝ, W) inc (D x)
    (mfderiv (𝓡 r) (𝓡 r) D x (orthogonalSphereHeightGradient r x)) =
      mfderiv 𝓘(ℝ, W) 𝓘(ℝ, W) B x.val
        (mfderiv (𝓡 r) 𝓘(ℝ, W) inc x (orthogonalSphereHeightGradient r x)) at hv
  rw [hlin, orthogonalSphereHeightGradient_ambient] at hv
  have hn : B (orthogonalSphereNorth r : W) = (orthogonalSphereNorth r : W) :=
    congrArg Subtype.val (smul_orthogonalSphereNorth r A)
  -- The block action fixes both north and height, so uniqueness identifies the native vectors.
  apply injective_mvfderiv_subtypeVal_sphere (A • x)
  change mfderiv (𝓡 r) 𝓘(ℝ, W) inc (D x)
    (mfderiv (𝓡 r) (𝓡 r) D x (orthogonalSphereHeightGradient r x)) =
      mfderiv (𝓡 r) 𝓘(ℝ, W) inc (A • x) (orthogonalSphereHeightGradient r (A • x))
  rw [orthogonalSphereHeightGradient_ambient]
  rw [hv]
  change B ((orthogonalSphereNorth r : W) - x.val.snd • x.val) = _
  rw [map_sub, map_smul, hn]
  rfl

/-- Precisely the two original poles are zeros of the specified height gradient. -/
theorem orthogonalSphereHeightGradient_eq_zero_iff (r : ℕ) (x : OrthogonalSphere r) :
    orthogonalSphereHeightGradient r x = 0 ↔
      x = orthogonalSpherePole r false ∨ x = orthogonalSpherePole r true := by
  let W := OrthogonalSphereAmbient r
  let L := mfderiv (𝓡 r) 𝓘(ℝ, W) (fun y : OrthogonalSphere r ↦ y.val) x
  have hinj : Function.Injective L := injective_mvfderiv_subtypeVal_sphere x
  -- Injectivity reduces vanishing to the actual ambient height-gradient equation.
  have hzero : orthogonalSphereHeightGradient r x = 0 ↔
      (orthogonalSphereNorth r : W) - x.val.snd • x.val = 0 := by
    rw [← orthogonalSphereHeightGradient_ambient r x]
    exact ⟨fun h ↦ by rw [h, map_zero]; rfl, fun h ↦ hinj (h.trans (map_zero L).symm)⟩
  rw [hzero]
  constructor
  · intro h
    have hw : (orthogonalSphereNorth r : W) = x.val.snd • x.val := sub_eq_zero.mp h
    have ht : x.val.snd = -1 ∨ x.val.snd = 1 := by
      have hs := congrArg (fun y : W ↦ y.snd) hw
      change 1 = x.val.snd * x.val.snd at hs
      have hsq : x.val.snd ^ 2 = 1 := by nlinarith
      rcases (sq_eq_one_iff).mp hsq with hp | hn
      · exact Or.inr hp
      · exact Or.inl hn
    rcases ht with ht | ht
    · left
      apply Subtype.ext
      change x.val = -(orthogonalSphereNorth r : W)
      have hh := congrArg Neg.neg hw
      simpa only [ht, neg_one_smul, neg_neg] using hh.symm
    · right
      apply Subtype.ext
      change x.val = (orthogonalSphereNorth r : W)
      simpa only [ht, one_smul] using hw.symm
  · rintro (rfl | rfl) <;>
      simp [orthogonalSpherePole, orthogonalSphereNorth]


end AtiyahSinger
