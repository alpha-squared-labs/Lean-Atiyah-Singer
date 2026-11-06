/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereMusical
public import AtiyahSinger.Topology.EquivariantBottConjugation
public import AtiyahSinger.Topology.EquivariantOpenHomeomorph
public import AtiyahSinger.Topology.EquivariantOpenRestriction
public import AtiyahSinger.Topology.OrthogonalLineBottConjugation
public import AtiyahSinger.Topology.SphereDeRhamDecomposition

/-!
# Reflection, restriction and the low-dimensional pole classes

Public module ID: M1956.

There are two different maps: the tangent lift of equatorial reflection swaps
the poles, whereas theta fixes the base and negates only its tangent vector.
All pullbacks below use these actual maps on the native tangent bundle.
The special orthogonal action is literally the restriction of the derivative
orthogonal action, and restriction retains the original support presentation.

The line and plane identities are the pole-local forms of ASI I Lemma (2.8),
p.496, used with Lemma (3.2), pp.499--500, in Lemma (4.7), pp.507--508.
The SO(2) identity lives in the restricted K group; no inverse of restriction
and no identity for the unreduced O(2) class is asserted. The restriction/reflection
square and pole comparisons use these specified actions and maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphereTangent

/-- The derivative tangent scalar action restricted along the SO(r) inclusion. -/
instance (priority := 1100) specialOrthogonalSphereTangentSMul (r : ℕ) :
    SMul (Matrix.specialOrthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) where
  smul A z := (specialOrthogonalGroupInclusion r A) • z

/-- The native derivative sphere action precomposed with the original SO(r) inclusion. -/
instance specialOrthogonalSphereTangentMulAction (r : ℕ) :
    MulAction (Matrix.specialOrthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  MulAction.compHom _ (specialOrthogonalGroupInclusion r).toMonoidHom

/-- Joint continuity of that same restricted derivative action. -/
instance continuousSMul_specialOrthogonalSphereTangent (r : ℕ) :
    ContinuousSMul (Matrix.specialOrthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  MulAction.continuousSMul_compHom (specialOrthogonalGroupInclusion r).continuous

/-- Restrict the actual tangent support class, without changing its bundles or boundary. -/
def orthogonalSphereTangentRestrict (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) →+
      EquivariantSupportTripleKZero (Matrix.specialOrthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  equivariantSupportTripleKZeroRestrict (specialOrthogonalGroupInclusion r)

/-- Pullback by the actual derivative lift of the sphere's vertical reflection. -/
def orthogonalSphereReflectionPullback (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) →+
      EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  equivariantSupportTripleKZeroPullback
    ⟨orthogonalSphereVerticalTangentHomeomorph r,
      (orthogonalSphereVerticalTangentHomeomorph r).continuous⟩
    (orthogonalSphereVerticalTangentHomeomorph_equivariant r)
    (orthogonalSphereVerticalTangentHomeomorph r).isProperMap

/-- The same reflection pullback with the actual restricted SO(r) action. -/
def specialOrthogonalSphereReflectionPullback (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.specialOrthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) →+
      EquivariantSupportTripleKZero (Matrix.specialOrthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
  equivariantSupportTripleKZeroPullback
    ⟨orthogonalSphereVerticalTangentHomeomorph r,
      (orthogonalSphereVerticalTangentHomeomorph r).continuous⟩
    (fun A z ↦ orthogonalSphereVerticalTangentHomeomorph_equivariant r
      (specialOrthogonalGroupInclusion r A) z)
    (orthogonalSphereVerticalTangentHomeomorph r).isProperMap

/-- The actual reflection exchanges the two pole pushforwards with unchanged coefficients. -/
theorem orthogonalSphereReflectionPullback_pole (r : ℕ) (atInfinity : Bool)
    (a : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) :
    orthogonalSphereReflectionPullback r (orthogonalSpherePolePushforward r atInfinity a) =
      orthogonalSpherePolePushforward r (!atInfinity) a := by
  let := compactSpace_orthogonalGroup r
  let := (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
  let := tangentBundleFullChartedSpace (E := EuclideanSpace ℝ (Fin r))
    (M := OrthogonalSphere r)
  let := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r))
    (TangentBundle (𝓡 r) (OrthogonalSphere r))
  let D := orthogonalSphereVerticalTangentHomeomorph r
  let k : C(TangentBundle (𝓡 r) (OrthogonalSphere r),
      TangentBundle (𝓡 r) (OrthogonalSphere r)) := ⟨D.symm, D.symm.continuous⟩
  have he (g : Matrix.orthogonalGroup (Fin r) ℝ) (z) : D (g • z) = g • D z :=
    orthogonalSphereVerticalTangentHomeomorph_equivariant r g z
  have hi (g : Matrix.orthogonalGroup (Fin r) ℝ) (z) : k (g • z) = g • k z := by
    apply D.injective
    change D (D.symm (g • z)) = D (g • D.symm z)
    rw [D.apply_symm_apply, he, D.apply_symm_apply]
  -- Inverse reflection sends the whole original chart to the opposite one with unchanged input.
  have hchart : k.comp (orthogonalSphereTangentChart r atInfinity) =
      orthogonalSphereTangentChart r (!atInfinity) := by
    apply ContinuousMap.ext
    intro z
    apply D.injective
    change D (D.symm (orthogonalSphereTangentChart r atInfinity z)) = _
    rw [D.apply_symm_apply]
    simpa only [Bool.not_not] using
      (orthogonalSphereVerticalTangentHomeomorph_chart r (!atInfinity) z).symm
  have hcomp := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    (orthogonalSphereTangentChart r atInfinity)
    (orthogonalSphereTangentChart_isOpenEmbedding r atInfinity)
    (orthogonalSphereTangentChart_equivariant r atInfinity)
    k D.symm.isOpenEmbedding hi
  have hcomp' : equivariantSupportTripleKZeroOpenPushforward (G := Matrix.orthogonalGroup
      (Fin r) ℝ) (k.comp (orthogonalSphereTangentChart r atInfinity))
      (D.symm.isOpenEmbedding.comp (orthogonalSphereTangentChart_isOpenEmbedding r atInfinity))
      (fun g x ↦ (congrArg k (orthogonalSphereTangentChart_equivariant r atInfinity g x)).trans
        (hi g (orthogonalSphereTangentChart r atInfinity x))) =
      equivariantSupportTripleKZeroOpenPushforward (orthogonalSphereTangentChart r (!atInfinity))
        (orthogonalSphereTangentChart_isOpenEmbedding r (!atInfinity))
        (orthogonalSphereTangentChart_equivariant r (!atInfinity)) := by
    congr 1
  -- Use the actual homeomorphism pullback and the same full representation coefficient.
  change equivariantSupportTripleKZeroPullback ⟨D, D.continuous⟩ he D.isProperMap
    (equivariantSupportTripleKZeroOpenPushforward (orthogonalSphereTangentChart r atInfinity)
      (orthogonalSphereTangentChart_isOpenEmbedding r atInfinity)
      (orthogonalSphereTangentChart_equivariant r atInfinity)
      (equivariantBottLinearMap (orthogonalComplexification_unitary r) a)) =
    equivariantSupportTripleKZeroOpenPushforward (orthogonalSphereTangentChart r (!atInfinity))
      (orthogonalSphereTangentChart_isOpenEmbedding r (!atInfinity))
      (orthogonalSphereTangentChart_equivariant r (!atInfinity))
      (equivariantBottLinearMap (orthogonalComplexification_unitary r) a)
  rw [equivariantSupportTripleKZeroPullback_eq_openPushforward_symm D he hi]
  exact DFunLike.congr_fun (hcomp.symm.trans hcomp')
    (equivariantBottLinearMap (orthogonalComplexification_unitary r) a)

/-- The original restriction and reflection pullback commute on every tangent K class. -/
theorem orthogonalSphereTangentRestrict_reflectionPullback (r : ℕ) :
    (orthogonalSphereTangentRestrict r).comp (orthogonalSphereReflectionPullback r) =
      (specialOrthogonalSphereReflectionPullback r).comp
        (orthogonalSphereTangentRestrict r) := by
  /- Apply the original proper-pullback restriction square to the actual
  tangent reflection homeomorphism and the native SO(r) inclusion. Its
  restricted equivariance equation is precisely the one used above. Both
  routes retain the same original triple, inverse-image compact control,
  boundary and precomposed fiber actions; no K-group restriction inverse
  or surjectivity is required. -/
  -- Use the actual restricted action and the same tangent reflection in the existing square.
  exact equivariantSupportTripleKZeroRestrict_pullback (specialOrthogonalGroupInclusion r)
    ⟨orthogonalSphereVerticalTangentHomeomorph r,
      (orthogonalSphereVerticalTangentHomeomorph r).continuous⟩
    (orthogonalSphereVerticalTangentHomeomorph_equivariant r)
    (orthogonalSphereVerticalTangentHomeomorph r).isProperMap

/-- For the reflection circle, tangent-fiber reversal multiplies the pole class by minus det. -/
theorem orthogonalCircleTangentNegation_pole (atInfinity : Bool) :
    orthogonalSphereTangentNegationPullback 1
        (orthogonalSpherePolePushforward 1 atInfinity 1) =
      -(finiteRepresentationClass (orthogonalDeterminantRepresentation 1) •
        orthogonalSpherePolePushforward 1 atInfinity 1) := by
  /- Stage 1: the actual tangent-chart conjugation square identifies theta
  pullback of this open-extended Bott class with open extension of the
  conjugation pullback of that same class on the complexified real line.
  Use the controlled-generator formula, preserving its singleton control.
  Stage 2: apply the direct sign-line Bott-generator conjugation calculation
  in the original O(1) module, then linearity of the same open extension. The minus
  sign and determinant line are retained together; theta is not the
  equatorial reflection that exchanged the two poles. -/
  let V := EuclideanSpace ℂ (Fin 1)
  let T := TangentBundle (𝓡 1) (OrthogonalSphere 1)
  let := compactSpace_orthogonalGroup 1
  let := (tangentBundle_topology (EuclideanSpace ℝ (Fin 1)) (OrthogonalSphere 1)).1
  let := tangentBundleFullChartedSpace (E := EuclideanSpace ℝ (Fin 1))
    (M := OrthogonalSphere 1)
  let := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) T
  let f := orthogonalSphereTangentChart 1 atInfinity
  have hf := orthogonalSphereTangentChart_isOpenEmbedding 1 atInfinity
  have he := orthogonalSphereTangentChart_equivariant 1 atInfinity
  let θ := orthogonalSphereTangentNegation 1
  have hθ := (orthogonalSphereTangentNegation_properties 1).2.2
  have hp := (orthogonalSphereTangentNegation_properties 1).2.1
  have hθinv : Function.Involutive θ := by
    intro z
    cases z
    simp only [θ, orthogonalSphereTangentNegation, ContinuousMap.coe_mk, neg_neg]
  let e : T ≃ₜ T :=
    { toEquiv := ⟨θ, θ, hθinv, hθinv⟩
      continuous_toFun := θ.continuous
      continuous_invFun := θ.continuous }
  let k : C(T, T) := ⟨e.symm, e.symm.continuous⟩
  let c := orthogonalComplexificationConjugation 1
  have hc := orthogonalComplexificationConjugation_equivariant 1
  have hcinv : Function.Involutive c := by
    intro z
    ext i
    exact star_star (z i)
  let d : V ≃ₜ V :=
    { toEquiv := ⟨c, c, hcinv, hcinv⟩
      continuous_toFun := c.continuous
      continuous_invFun := c.continuous }
  let l : C(V, V) := ⟨d.symm, d.symm.continuous⟩
  have hchart : k.comp f = f.comp l := by
    apply ContinuousMap.ext
    intro z
    exact (orthogonalSphereTangentChart_conjugation 1 atInfinity z).symm
  have hmaps : equivariantSupportTripleKZeroOpenPushforward (k.comp f)
      (e.symm.isOpenEmbedding.comp hf)
      (fun g x ↦ (congrArg k (he g x)).trans (hθ g (f x))) =
    equivariantSupportTripleKZeroOpenPushforward (f.comp l)
      (hf.comp d.symm.isOpenEmbedding)
      (fun g x ↦ (congrArg f (hc g x)).trans (he g (l x))) := by
    congr 1
  have hleft := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    f hf he k e.symm.isOpenEmbedding hθ
  have hright := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    l d.symm.isOpenEmbedding hc f hf he
  let a := equivariantExteriorBottClass (orthogonalComplexification_unitary 1)
  let ξ := finiteRepresentationClass (orthogonalDeterminantRepresentation 1)
  have hpole : orthogonalSpherePolePushforward 1 atInfinity 1 =
      equivariantSupportTripleKZeroOpenPushforward f hf he a := by
    change equivariantSupportTripleKZeroOpenPushforward f hf he
      ((1 : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin 1) ℝ)) • a) = _
    rw [one_smul]
  have hcvalue : equivariantSupportTripleKZeroOpenPushforward l d.symm.isOpenEmbedding hc a =
      -(ξ • a) := by
    have hconv := equivariantSupportTripleKZeroPullback_eq_openPushforward_symm d hc hc
    exact (DFunLike.congr_fun hconv a).symm.trans orthogonalLineConjugationPullback_bott
  -- The exact chart square transports the generator identity to the original pole class.
  rw [hpole]
  change equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ hθ e.isProperMap
    (equivariantSupportTripleKZeroOpenPushforward f hf he a) = _
  rw [equivariantSupportTripleKZeroPullback_eq_openPushforward_symm e hθ hθ]
  have hcomp := DFunLike.congr_fun (hleft.symm.trans (hmaps.trans hright)) a
  simp only [AddMonoidHom.comp_apply] at hcomp
  rw [hcvalue, map_neg, equivariantSupportTripleKZeroOpenPushforward_smul] at hcomp
  exact hcomp

/-- On the restricted real two-plane class, tangent-fiber reversal fixes either pole class. -/
theorem specialOrthogonalPlaneTangentNegation_pole (atInfinity : Bool) :
    orthogonalSphereTangentRestrict 2
        (orthogonalSphereTangentNegationPullback 2
          (orthogonalSpherePolePushforward 2 atInfinity 1)) =
      orthogonalSphereTangentRestrict 2 (orthogonalSpherePolePushforward 2 atInfinity 1) := by
  /- Stage 1: restrict the same original pole triple and the tangent-chart
  conjugation square along SO(2) -> O(2). Restriction commutes with the
  actual proper pullback and with controlled open extension: both routes
  have precisely the same bundles, boundary and restricted fiber maps.
  Stage 2: apply specialOrthogonalPlaneConjugationPullback_eq on the
  complexification of the real two-plane, with its native restricted
  matrix action. Extend that equality through the same restricted chart.
  The resulting equality is in K_SO(2)(TS2), not K_O(2)(TS2); it makes no
  assertion that restriction is injective, surjective or invertible. -/
  let H := Matrix.specialOrthogonalGroup (Fin 2) ℝ
  let V := EuclideanSpace ℂ (Fin 2)
  let T := TangentBundle (𝓡 2) (OrthogonalSphere 2)
  let := compactSpace_orthogonalGroup 2
  have hc : IsCompact (Matrix.orthogonalGroup (Fin 2) ℝ :
      Set (Matrix (Fin 2) (Fin 2) ℝ)) :=
    isCompact_iff_compactSpace.mpr inferInstance
  have hd : IsClosed {A : Matrix (Fin 2) (Fin 2) ℝ | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  have hs : IsCompact (Matrix.specialOrthogonalGroup (Fin 2) ℝ :
      Set (Matrix (Fin 2) (Fin 2) ℝ)) :=
    hc.inter_right hd
  let : CompactSpace H := isCompact_iff_compactSpace.mp hs
  let := (tangentBundle_topology (EuclideanSpace ℝ (Fin 2)) (OrthogonalSphere 2)).1
  let := tangentBundleFullChartedSpace (E := EuclideanSpace ℝ (Fin 2))
    (M := OrthogonalSphere 2)
  let := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) T
  let φ := specialOrthogonalGroupInclusion 2
  let f := orthogonalSphereTangentChart 2 atInfinity
  have hf := orthogonalSphereTangentChart_isOpenEmbedding 2 atInfinity
  have he := orthogonalSphereTangentChart_equivariant 2 atInfinity
  have hr (A : H) (z : V) : f (A • z) = A • f z := he (φ A) z
  let θ := orthogonalSphereTangentNegation 2
  have hθ := (orthogonalSphereTangentNegation_properties 2).2.2
  have hp := (orthogonalSphereTangentNegation_properties 2).2.1
  have hθr (A : H) (z : T) : θ (A • z) = A • θ z := hθ (φ A) z
  -- Both inverse maps are their original involutions, on the specified native spaces.
  have hθinv : Function.Involutive θ := by
    intro z
    cases z
    simp only [θ, orthogonalSphereTangentNegation, ContinuousMap.coe_mk, neg_neg]
  let e : T ≃ₜ T :=
    { toEquiv := ⟨θ, θ, hθinv, hθinv⟩
      continuous_toFun := θ.continuous
      continuous_invFun := θ.continuous }
  let k : C(T, T) := ⟨e.symm, e.symm.continuous⟩
  let c := orthogonalComplexificationConjugation 2
  have hcinv : Function.Involutive c := by
    intro z
    ext i
    exact star_star (z i)
  let d : V ≃ₜ V :=
    { toEquiv := ⟨c, c, hcinv, hcinv⟩
      continuous_toFun := c.continuous
      continuous_invFun := c.continuous }
  let l : C(V, V) := ⟨d.symm, d.symm.continuous⟩
  have hcr (A : H) (z : V) : c (A • z) = A • c z :=
    orthogonalComplexificationConjugation_equivariant 2 (φ A) z
  have hchart : k.comp f = f.comp l := by
    apply ContinuousMap.ext
    intro z
    exact (orthogonalSphereTangentChart_conjugation 2 atInfinity z).symm
  have hleft := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    f hf hr k e.symm.isOpenEmbedding hθr
  have hright := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    l d.symm.isOpenEmbedding hcr f hf hr
  -- The chart square identifies reversal with conjugation before extending the same class.
  have hfixed (b : EquivariantSupportTripleKZero H V) :
      equivariantSupportTripleKZeroPullback θ hθr hp
        (equivariantSupportTripleKZeroOpenPushforward f hf hr b) =
      equivariantSupportTripleKZeroOpenPushforward f hf hr b := by
    have hmaps : equivariantSupportTripleKZeroOpenPushforward (G := H) (k.comp f)
        (e.symm.isOpenEmbedding.comp hf)
        (fun g x ↦ (congrArg k (hr g x)).trans (hθr g (f x))) =
      equivariantSupportTripleKZeroOpenPushforward (f.comp l)
        (hf.comp d.symm.isOpenEmbedding)
        (fun g x ↦ (congrArg f (hcr g x)).trans (hr g (l x))) := by
      congr 1
    have hcfix : equivariantSupportTripleKZeroOpenPushforward l d.symm.isOpenEmbedding
        hcr b = b := by
      have hconv := equivariantSupportTripleKZeroPullback_eq_openPushforward_symm d hcr hcr
      exact (DFunLike.congr_fun hconv b).symm.trans
        (specialOrthogonalPlaneConjugationPullback_eq b)
    change equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ hθr e.isProperMap
      (equivariantSupportTripleKZeroOpenPushforward f hf hr b) = _
    rw [equivariantSupportTripleKZeroPullback_eq_openPushforward_symm e hθr hθr]
    have hcomp := DFunLike.congr_fun (hleft.symm.trans (hmaps.trans hright)) b
    exact hcomp.trans (congrArg (equivariantSupportTripleKZeroOpenPushforward f hf hr) hcfix)
  -- Restrict the actual original Bott input; no surjectivity or inverse of restriction is used.
  let a := equivariantBottLinearMap (orthogonalComplexification_unitary 2) 1
  have hres := equivariantSupportTripleKZeroRestrict_openPushforward φ f hf he a
  have hpull := DFunLike.congr_fun
    (equivariantSupportTripleKZeroRestrict_pullback φ θ hθ hp)
      (equivariantSupportTripleKZeroOpenPushforward f hf he a)
  change equivariantSupportTripleKZeroRestrict φ
      (equivariantSupportTripleKZeroPullback θ hθ hp
        (equivariantSupportTripleKZeroOpenPushforward f hf he a)) =
    equivariantSupportTripleKZeroRestrict φ
      (equivariantSupportTripleKZeroOpenPushforward f hf he a)
  exact hpull.trans ((congrArg (equivariantSupportTripleKZeroPullback θ hθr hp) hres).trans
    ((hfixed (equivariantSupportTripleKZeroRestrict φ a)).trans hres.symm))

end AtiyahSinger
