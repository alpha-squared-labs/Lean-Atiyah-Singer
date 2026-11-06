/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticIndexDiffeomorph
public import AtiyahSinger.Analysis.CirclePointIndex
public import AtiyahSinger.Analysis.EquivariantAnalyticIndexDimension
public import AtiyahSinger.Analysis.SphereTangentIndex
public import AtiyahSinger.Geometry.OrthogonalCircle
public import AtiyahSinger.Topology.ExteriorBottComparison
public import AtiyahSinger.Topology.OrthogonalFixedPointPushforward

/-!
# The dimension-one augmentation for the actual O(1) pole index

Public module ID: M0842.

AL03 requires the ordinary dimension of the same equivariant point index that
occurs in the two-pole relation. The map below first applies the prescribed
round musical map on the native sphere tangent K group, then forgets the
original actions and uses the existing support compactification comparison.
The actual inverse-dual cotangent lift of `orthogonalCircleDiffeomorph` takes
this class into the original Circle cotangent K group.

Its value on either original pole class is the earlier `circlePointPushforward`,
defined independently from the Fourier operator. The AR02 normalization +1
therefore gives the required dimension of the original representation index.
No injectivity of representation dimension or cancellation of `1 - det` is
asserted here.

Sources: ASI I, Lemma (4.7), pp.507--508, the pole construction in Lemma (3.2),
pp.499--500, and the direct circle normalization in section 8, pp.525--526.
The same-object coordinate and forgetful diagrams
are explicit project supplements. The pole comparison uses naturality of the
original tangent and cotangent embedding pushforwards.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent

/-- Round musical transport, original forgetting, and the actual cotangent circle comparison. -/
def orthogonalCircleKZeroForget :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin 1) ℝ)
        (TangentBundle (𝓡 1) (OrthogonalSphere 1)) →+
      CompactSupportKZero (CotangentTotalSpace (n := 1) (M := Circle)) :=
  (cotangentKZeroDiffeomorph orthogonalCircleDiffeomorph).toAddMonoidHom.comp
    (supportTripleKZeroToCompactSupport.comp
      ((equivariantSupportTripleKZeroForget
        (G := Matrix.orthogonalGroup (Fin 1) ℝ)
        (X := CotangentTotalSpace (n := 1) (M := OrthogonalSphere 1))).comp
          (orthogonalSphereMusicalKMap 1)))

open scoped Matrix.Norms.L2Operator in
/-- Representation dimension commutes with the actual ordinary circle transport on every class. -/
theorem representationDimension_orthogonalCircleTangentIndex
    (μ : Measure Circle) [IsSmoothPositiveMeasure (n := 1) μ]
    (u : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin 1) ℝ)
      (TangentBundle (𝓡 1) (OrthogonalSphere 1))) :
    representationDimension (Matrix.orthogonalGroup (Fin 1) ℝ)
        (orthogonalSphereTangentAnalyticIndex 1 u) =
      analyticIndexOfComponents μ (orthogonalCircleKZeroForget u) := by
  /- Stage 1: the tangent index is the original cotangent equivariant index
  after exactly orthogonalSphereMusicalKMap 1. Apply the existing arbitrary-
  class representation-dimension comparison to that resulting equivariant
  class, using a smooth positive measure on the same original sphere.
  The group-action adapter is exactly the one in orthogonalSphereAnalyticIndex;
  it changes only the certificate for the equal original inverse-dual action.
  Stage 2: the ordinary class is the original forgetful image followed by
  supportTripleKZeroToCompactSupport. Apply analyticIndexOfComponents_diffeomorph
  to the actual orthogonalCircleDiffeomorph and its inverse-dual cotangent
  transport. This keeps the original class u and all its boundary data.
  The target density can be the supplied μ by the existing independence of
  positive smooth density. The composite on this side is exactly the declared
  orthogonalCircleKZeroForget; equality therefore holds on every class,
  independently of the pole or any eventual normalization result. -/
  let := orthogonalGroupChartedSpace 1
  let := lieGroup_orthogonalGroup 1
  let := compactSpace_orthogonalGroup 1
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin 1) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin 1) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin 1) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere 1) := borel (OrthogonalSphere 1)
  let : BorelSpace (OrthogonalSphere 1) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := exists_smoothPositiveMeasure (n := 1) (M := OrthogonalSphere 1)
  let := hν
  have hforget := DFunLike.congr_fun
    (representationDimension_equivariantAnalyticIndexMap
      (VG := OrthogonalGroupModel 1) (G := Matrix.orthogonalGroup (Fin 1) ℝ) ν)
    (orthogonalSphereMusicalKMap 1 u)
  have hdiff := DFunLike.congr_fun
    (analyticIndexOfComponents_diffeomorph ν μ orthogonalCircleDiffeomorph)
    (supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget (orthogonalSphereMusicalKMap 1 u)))
  exact hforget.trans hdiff.symm

set_option maxHeartbeats 1000000 in
-- Compare the same native bundle topologies and the chosen zero-dimensional units.
/-- Both original pole classes become the same positive point pushforwards on the circle. -/
theorem orthogonalCircleKZeroForget_polePushforward (atInfinity : Bool)
    (g₀ : SmoothTangentMetric (n := 0) (M := EuclideanSpace ℝ (Fin 0)))
    (g₁ : SmoothTangentMetric (n := 1) (M := Circle)) :
    orthogonalCircleKZeroForget (orthogonalSpherePolePushforward 1 atInfinity 1) =
      circlePointPushforward
        (orthogonalCircleDiffeomorph (orthogonalSpherePole 1 atInfinity)) g₀ g₁ := by
  classical
  let E₀ := EuclideanSpace ℝ (Fin 0)
  let T₀ := TangentBundle (𝓡 0) E₀
  let T₁ := TangentBundle (𝓡 1) (OrthogonalSphere 1)
  let : T2Space T₀ := (tangentBundle_topology E₀ E₀).1
  let : LocallyCompactSpace T₀ := ChartedSpace.locallyCompactSpace (E₀ × E₀) T₀
  let : T2Space T₁ := (tangentBundle_topology (EuclideanSpace ℝ (Fin 1))
    (OrthogonalSphere 1)).1
  let := tangentBundleFullChartedSpace (E := EuclideanSpace ℝ (Fin 1))
    (M := OrthogonalSphere 1)
  let : LocallyCompactSpace T₁ := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) T₁
  let : Unique (ModelProd E₀ E₀) :=
    { default := (0, 0)
      uniq := fun x ↦ by
        apply Prod.ext <;> ext i <;> exact Fin.elim0 i }
  let pt := (tangentBundleModelSpaceHomeomorph (𝓡 0)).trans
    (Homeomorph.homeomorphOfUnique (ModelProd E₀ E₀) PUnit.{1})
  let cp := (cotangentProjectionHomeomorphOfDimZero (n := 0) (M := E₀) rfl).trans
    (Homeomorph.homeomorphOfUnique E₀ PUnit.{1})
  let j : ContMDiffMap (𝓡 0) (𝓡 1) E₀ (OrthogonalSphere 1) ∞ :=
    ContMDiffMap.const (orthogonalSpherePole 1 atInfinity)
  have hj (A : Matrix.orthogonalGroup (Fin 1) ℝ) (x : E₀) : A • j x = j x := by
    change A • orthogonalSpherePole 1 atInfinity = orthogonalSpherePole 1 atInfinity
    cases atInfinity
    · apply Subtype.ext
      change WithLp.toLp 2 ((orthogonalEuclideanIsometry 1 A) (-0), (-1 : ℝ)) =
        WithLp.toLp 2 ((-0 : EuclideanSpace ℝ (Fin 1)), (-1 : ℝ))
      simp only [neg_zero, map_zero]
    · exact smul_orthogonalSphereNorth 1 A
  -- The fixed-point comparison selects precisely this pole, retaining its positive unit.
  obtain ⟨b, hb, hmap⟩ := orthogonalSphereFixedPointPushforward_eq_pole j hj
  have hb' : b = atInfinity := by
    have hc := congrArg (fun z : OrthogonalSphere 1 ↦ z.val.snd) (hb 0)
    cases b <;> cases atInfinity
    all_goals first
      | rfl
      | norm_num [j, ContMDiffMap.const, orthogonalSpherePole, orthogonalSphereNorth] at hc
  subst b
  have hforget := orthogonalSphereFixedPointPushforward_forget j hj
  rw [hmap] at hforget
  change supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget (orthogonalSpherePolePushforward 1 atInfinity 1)) =
    tangentEmbeddingPushforward j (orthogonalSpherePointEmbedding_properties j).1
      (orthogonalSpherePointEmbedding_properties j).2
      (compactSupportKZeroHomeomorph pt.symm compactSupportKZeroPointOne) at hforget
  -- Every map between the actual zero-dimensional points preserves this same positive unit.
  have hunit : (tangentCotangentKZeroEquiv g₀).symm circlePointCotangentUnit =
      compactSupportKZeroHomeomorph pt.symm compactSupportKZeroPointOne := by
    apply (tangentCotangentKZeroEquiv g₀).injective
    rw [AddEquiv.apply_symm_apply]
    change compactSupportKZeroHomeomorph cp.symm compactSupportKZeroPointOne =
      compactSupportKZeroHomeomorph g₀.flatHomeomorph
        (compactSupportKZeroHomeomorph pt.symm compactSupportKZeroPointOne)
    have he : (g₀.flatHomeomorph : T₀ → _) ∘ pt.symm = (cp.symm : PUnit → _) := by
      funext x
      apply cp.injective
      exact Subsingleton.elim _ _
    rw [← AddMonoidHom.comp_apply,
      ← compactSupportKZeroOpenPushforward_homeomorph g₀.flatHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph pt.symm,
      ← compactSupportKZeroOpenPushforward_comp]
    simpa only [he] using (DFunLike.congr_fun
      (compactSupportKZeroOpenPushforward_homeomorph cp.symm)
      compactSupportKZeroPointOne).symm
  let gS := orthogonalSphereRoundMetric 1
  let e := orthogonalCircleDiffeomorph
  -- Forgetting and compactification commute with the prescribed inverse musical pullback.
  have hmusical : supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (orthogonalSphereMusicalKMap 1 (orthogonalSpherePolePushforward 1 atInfinity 1))) =
      cotangentEmbeddingPushforward j (orthogonalSpherePointEmbedding_properties j).1
        (orthogonalSpherePointEmbedding_properties j).2 g₀ gS circlePointCotangentUnit := by
    have h₁ := DFunLike.congr_fun
      (equivariantSupportTripleKZeroForget_pullback
        ⟨gS.flatHomeomorph.symm, gS.flatHomeomorph.symm.continuous⟩
        (orthogonalSphereRoundMetric_flat_symm_equivariant 1)
        gS.flatHomeomorph.symm.isProperMap)
      (orthogonalSpherePolePushforward 1 atInfinity 1)
    have h₂ := DFunLike.congr_fun
      (supportTripleKZeroToCompactSupport_pullback
        ⟨gS.flatHomeomorph.symm, gS.flatHomeomorph.symm.continuous⟩
        gS.flatHomeomorph.symm.isProperMap)
      (equivariantSupportTripleKZeroForget (orthogonalSpherePolePushforward 1 atInfinity 1))
    simp only [AddMonoidHom.comp_apply] at h₁ h₂
    change supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (orthogonalSphereMusicalKMap 1 (orthogonalSpherePolePushforward 1 atInfinity 1))) = _
    rw [show equivariantSupportTripleKZeroForget
      (orthogonalSphereMusicalKMap 1 (orthogonalSpherePolePushforward 1 atInfinity 1)) = _
      from h₁]
    rw [show supportTripleKZeroToCompactSupport
      (supportTripleKZeroPullback
        ⟨gS.flatHomeomorph.symm, gS.flatHomeomorph.symm.continuous⟩
        gS.flatHomeomorph.symm.isProperMap
        (equivariantSupportTripleKZeroForget
          (orthogonalSpherePolePushforward 1 atInfinity 1))) = _ from h₂]
    rw [hforget]
    change (tangentCotangentKZeroEquiv gS)
      (tangentEmbeddingPushforward j (orthogonalSpherePointEmbedding_properties j).1
        (orthogonalSpherePointEmbedding_properties j).2
        (compactSupportKZeroHomeomorph pt.symm compactSupportKZeroPointOne)) =
      (tangentCotangentKZeroEquiv gS)
        (tangentEmbeddingPushforward j (orthogonalSpherePointEmbedding_properties j).1
        (orthogonalSpherePointEmbedding_properties j).2
          ((tangentCotangentKZeroEquiv g₀).symm circlePointCotangentUnit))
    rw [hunit]
  -- Compose with the actual circle diffeomorphism; its differential has its true inverse.
  have he : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ e := by
    refine ⟨isImmersion_of_injective_mfderiv e.toContMDiffMap ?_, e.toHomeomorph.isEmbedding⟩
    intro x u v huv
    have hchain := mfderiv_comp (I := 𝓡 1) (I' := 𝓡 1) (I'' := 𝓡 1) x
      (e.symm.contMDiff.mdifferentiable (by simp) (e x))
      (e.contMDiff.mdifferentiable (by simp) x)
    rw [show (e.symm : Circle → OrthogonalSphere 1) ∘ e = id from
      funext e.symm_apply_apply, mfderiv_id] at hchain
    have hu := DFunLike.congr_fun hchain u
    have hv := DFunLike.congr_fun hchain v
    exact hu.trans ((congrArg (mfderiv (𝓡 1) (𝓡 1) e.symm (e x)) huv).trans hv.symm)
  have hcomp := DFunLike.congr_fun
    (cotangentEmbeddingPushforward_comp j e.toContMDiffMap
      (orthogonalSpherePointEmbedding_properties j).1 he
      (orthogonalSpherePointEmbedding_properties j).2 e.toHomeomorph.isProperMap g₀ gS g₁)
    circlePointCotangentUnit
  rw [cotangentEmbeddingPushforward_diffeomorph e he e.toHomeomorph.isProperMap] at hcomp
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass] at hcomp
  have hjcomp : e.toContMDiffMap.comp j =
      circlePointEmbedding (e (orthogonalSpherePole 1 atInfinity)) := by
    ext x
    rfl
  change cotangentKZeroDiffeomorph e
    (supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (orthogonalSphereMusicalKMap 1 (orthogonalSpherePolePushforward 1 atInfinity 1)))) = _
  rw [hmusical, ← hcomp]
  simp only [hjcomp, circlePointPushforward]
  rfl

/-- AR02 supplies dimension one for either pole of the same O(1)-valued sphere tangent index. -/
theorem representationDimension_orthogonalCirclePoleIndex (atInfinity : Bool) :
    representationDimension (Matrix.orthogonalGroup (Fin 1) ℝ)
      (orthogonalSphereTangentAnalyticIndex 1
        (orthogonalSpherePolePushforward 1 atInfinity 1)) = 1 := by
  let g₀ := (SmoothTangentMetric.nonempty
    (n := 0) (M := EuclideanSpace ℝ (Fin 0))).some
  let g₁ := (SmoothTangentMetric.nonempty (n := 1) (M := Circle)).some
  let := isSmoothPositiveMeasure_fourierCircleMeasure
  -- First forget the same pole class, then apply its ordinary positive normalization.
  rw [representationDimension_orthogonalCircleTangentIndex fourierCircleMeasure,
    orthogonalCircleKZeroForget_polePushforward atInfinity g₀ g₁]
  exact analyticIndexOfComponents_circlePointPushforward _ g₀ g₁ fourierCircleMeasure

end AtiyahSinger
