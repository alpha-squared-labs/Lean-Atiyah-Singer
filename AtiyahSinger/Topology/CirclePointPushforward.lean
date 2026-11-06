/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CircleCotangent
public import AtiyahSinger.Topology.CircleMusicalTube
public import AtiyahSinger.Topology.CompactSupportProductLaws
public import AtiyahSinger.Topology.CotangentEmbeddingPushforward
public import AtiyahSinger.Topology.ExteriorBottComparison
public import AtiyahSinger.Topology.PointChartPushforward

/-!
# The original point inclusion and its circle cotangent pushforward

Public module ID: M1614.

AR02 uses the actual inclusion of a point into `Circle`, the positive rank-one
point class, and the existing cotangent embedding pushforward. Both tangent
metrics remain explicit. The comparison theorem identifies its value with open
extension of the original multiplication-by-z Bott line class along the fixed
normalized tube from `CircleCotangent`.

The point class is transported through the actual zero-dimensional cotangent
projection and the unique homeomorphism to `PUnit`. It is not defined from the
circle Fourier symbol or from its desired analytic index. The tube comparison
uses the existing quotient-direction-then-vertical complexification convention.

Sources: Atiyah--Singer I, section 8, p.526 and Figure 3; SG III.12, p.241 for
the ordered complexification in the actual embedding pushforward. These are
statements about the same positive exterior Thom convention. The actual
normalized angular chart has positive derivative; a whole-cylinder isotopy
removes its positive musical coefficient for either supplied metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

/-- The actual inclusion of the zero-dimensional point at a specified circle point. -/
def circlePointEmbedding (a : Circle) :
    ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      (EuclideanSpace ℝ (Fin 0)) Circle ∞ :=
  ContMDiffMap.const a

/-- The specified point inclusion is a smooth embedding of its zero-dimensional source. -/
theorem isSmoothEmbedding_circlePointEmbedding (a : Circle) :
    IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ (circlePointEmbedding a) := by
  /- The source is a singleton and its image is the specified point a.
  The centered circle chart sends a to zero. The unique product equivalence
  with the whole target model as complement gives the native immersion
  normal form for this constant map. The actual singleton source also gives
  its topological embedding, completing the same smooth embedding. -/
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  -- The preferred circle chart is centered at a, so it sends the point map to zero.
  have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) a a = 0 := by
    change stereographic' 1 (-a) a = 0
    change (OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (ne_zero_of_mem_unit_sphere (-a))).repr
        (stereographic (norm_eq_of_mem_sphere (-a)) a) = 0
    exact (congrArg (OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (ne_zero_of_mem_unit_sphere (-a))).repr (stereographic_neg_apply a)).trans (map_zero _)
  constructor
  · -- The whole target model is a complement to the zero-dimensional source model.
    apply IsImmersionOfComplement.isImmersion (F := EuclideanSpace ℝ (Fin 1))
    intro x
    apply IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
      (circlePointEmbedding a).property.continuous.continuousAt
      (ContinuousLinearEquiv.uniqueProd ℝ (EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace ℝ (Fin 0)))
    intro y hy
    simpa only [Function.comp_apply, circlePointEmbedding, ContMDiffMap.const,
      ContinuousLinearEquiv.uniqueProd_apply] using hcenter
  · -- A map from the actual singleton source is a topological embedding.
    exact IsEmbedding.of_subsingleton _

/-- The positive rank-one unit on the actual zero-dimensional cotangent point. -/
def circlePointCotangentUnit :
    CompactSupportKZero
      (CotangentTotalSpace (n := 0) (M := EuclideanSpace ℝ (Fin 0))) :=
  compactSupportKZeroHomeomorph
    ((cotangentProjectionHomeomorphOfDimZero (n := 0)
      (M := EuclideanSpace ℝ (Fin 0)) rfl).trans
        (Homeomorph.homeomorphOfUnique (EuclideanSpace ℝ (Fin 0)) PUnit.{1})).symm
    compactSupportKZeroPointOne

/-- The value j!1 of the original cotangent embedding pushforward, with both metrics explicit. -/
def circlePointPushforward (a : Circle)
    (g₀ : SmoothTangentMetric (n := 0) (M := EuclideanSpace ℝ (Fin 0)))
    (g₁ : SmoothTangentMetric (n := 1) (M := Circle)) :
    CompactSupportKZero (CotangentTotalSpace (n := 1) (M := Circle)) :=
  cotangentEmbeddingPushforward (circlePointEmbedding a)
    (isSmoothEmbedding_circlePointEmbedding a)
    (circlePointEmbedding a).property.continuous.isProperMap g₀ g₁ circlePointCotangentUnit

set_option maxHeartbeats 1400000 in
-- Normalize the positive point unit and its actual musical and open-extension maps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual point pushforward is open extension of the positive multiplication-by-z class. -/
theorem circlePointPushforward_eq_openPushforward (a : Circle)
    (g₀ : SmoothTangentMetric (n := 0) (M := EuclideanSpace ℝ (Fin 0)))
    (g₁ : SmoothTangentMetric (n := 1) (M := Circle)) :
    circlePointPushforward a g₀ g₁ =
      compactSupportKZeroOpenPushforward (circlePointCotangentTube a)
        (isOpenEmbedding_circlePointCotangentTube a) bottLineClass := by
  classical
  let E0 := EuclideanSpace ℝ (Fin 0)
  let E1 := EuclideanSpace ℝ (Fin 1)
  let W := EuclideanSpace ℂ (Fin 1)
  let T0 := TangentBundle (𝓡 0) E0
  let T1 := TangentBundle (𝓡 1) Circle
  let CT0 := CotangentTotalSpace (n := 0) (M := E0)
  let CT1 := CotangentTotalSpace (n := 1) (M := Circle)
  let : T2Space T0 := (tangentBundle_topology E0 E0).1
  let : LocallyCompactSpace T0 := ChartedSpace.locallyCompactSpace (E0 × E0) T0
  let : T2Space T1 := (tangentBundle_topology E1 Circle).1
  let : LocallyCompactSpace T1 := ChartedSpace.locallyCompactSpace (E1 × E1) T1
  let e0 : CT0 ≃ₜ PUnit.{1} :=
    (cotangentProjectionHomeomorphOfDimZero (n := 0) (M := E0) rfl).trans
      (Homeomorph.homeomorphOfUnique E0 PUnit.{1})
  let p : T0 ≃ₜ PUnit.{1} := g₀.flatHomeomorph.trans e0
  let unit := compactSupportKZeroHomeomorph p.symm compactSupportKZeroPointOne
  -- The actual zero-dimensional musical transport carries the same positive point unit.
  have hunit : (tangentCotangentKZeroEquiv g₀).symm circlePointCotangentUnit = unit := by
    apply (tangentCotangentKZeroEquiv g₀).injective
    rw [AddEquiv.apply_symm_apply]
    change compactSupportKZeroHomeomorph e0.symm compactSupportKZeroPointOne =
      compactSupportKZeroHomeomorph g₀.flatHomeomorph
        (compactSupportKZeroHomeomorph p.symm compactSupportKZeroPointOne)
    have hm : (g₀.flatHomeomorph : T0 → CT0) ∘ p.symm = e0.symm := by
      funext z
      exact g₀.flatHomeomorph.apply_symm_apply (e0.symm z)
    rw [← compactSupportKZeroOpenPushforward_homeomorph g₀.flatHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph p.symm,
      ← AddMonoidHom.comp_apply,
      ← compactSupportKZeroOpenPushforward_comp p.symm p.symm.isOpenEmbedding
        g₀.flatHomeomorph g₀.flatHomeomorph.isOpenEmbedding]
    simp only [hm]
    rw [compactSupportKZeroOpenPushforward_homeomorph e0.symm]
  -- The positive exterior class is extended through the derivative of the same angular chart.
  obtain ⟨c, hvalue, hc, hinj, hder⟩ := exists_circlePointAngularChart a
  have hzero : c 0 = circlePointEmbedding a 0 := by
    rw [hvalue]
    change a * Circle.exp (2 * Real.arctan (0 / 2)) = a
    simp
  obtain ⟨htube, hpoint⟩ := tangentEmbeddingPushforward_pointChart 1
    (circlePointEmbedding a) (isSmoothEmbedding_circlePointEmbedding a)
    (circlePointEmbedding a).contMDiff.continuous.isProperMap c hc hinj hzero p
  let tube : W → T1 := fun z ↦
    ⟨c (WithLp.toLp 2 (fun i ↦ (z i).re)),
      mfderiv (𝓡 1) (𝓡 1) c (WithLp.toLp 2 (fun i ↦ (z i).re))
        (WithLp.toLp 2 (fun i ↦ (z i).im))⟩
  let R : W ≃ₜ ℂ := (PiLp.homeomorph 2 (fun _ : Fin 1 ↦ ℂ)).trans
    (Homeomorph.funUnique (Fin 1) ℂ)
  let Q : ℂ ≃ₜ TangentBundle (𝓡 1) E1 :=
    (Homeomorph.funUnique (Fin 1) ℂ).symm.trans
      (euclideanTangentComplexHomeomorph 1).symm
  let β : C(ℂ, CT1) :=
    ⟨g₁.flatHomeomorph ∘ smoothTangentMap c ∘ Q,
      g₁.flatHomeomorph.continuous.comp
        ((smoothTangentMap c).contMDiff.continuous.comp Q.continuous)⟩
  have hβ : IsOpenEmbedding β := g₁.flatHomeomorph.isOpenEmbedding.comp
    ((isOpenEmbedding_smoothTangentMap c hc hinj).comp Q.isOpenEmbedding)
  have hm : (g₁.flatHomeomorph : T1 → CT1) ∘ tube = β ∘ R := by
    funext z
    apply congrArg g₁.flatHomeomorph
    change smoothTangentMap c ((euclideanTangentComplexHomeomorph 1).symm
      ((PiLp.homeomorph 2 (fun _ : Fin 1 ↦ ℂ)) z)) = smoothTangentMap c (Q (R z))
    apply congrArg (smoothTangentMap c)
    exact congrArg (euclideanTangentComplexHomeomorph 1).symm
      ((Homeomorph.funUnique (Fin 1) ℂ).symm_apply_apply
        ((PiLp.homeomorph 2 (fun _ : Fin 1 ↦ ℂ)) z)).symm
  have hbott : compactSupportKZeroHomeomorph R (exteriorBottClass W) = bottLineClass := by
    have h := exteriorBottEuclideanClass_one
    change compactSupportKZeroHomeomorph (Homeomorph.funUnique (Fin 1) ℂ)
      (compactSupportKZeroHomeomorph (PiLp.homeomorph 2 (fun _ : Fin 1 ↦ ℂ))
        (exteriorBottClass W)) = bottLineClass at h
    rw [← compactSupportKZeroOpenPushforward_homeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp] at h
    rw [← compactSupportKZeroOpenPushforward_homeomorph R]
    exact h
  -- Musical transport changes only a positive vertical coefficient on the whole open cylinder.
  have hisotopy := circlePointMusicalTube_openPushforward a c hc hinj hvalue hder g₁
  change compactSupportKZeroOpenPushforward β hβ = _ at hisotopy
  change compactSupportKZeroHomeomorph g₁.flatHomeomorph
    (tangentEmbeddingPushforward (circlePointEmbedding a)
      (isSmoothEmbedding_circlePointEmbedding a)
      (circlePointEmbedding a).contMDiff.continuous.isProperMap
      ((tangentCotangentKZeroEquiv g₀).symm circlePointCotangentUnit)) = _
  rw [hunit, hpoint]
  change compactSupportKZeroHomeomorph g₁.flatHomeomorph
    (compactSupportKZeroOpenPushforward tube htube (exteriorBottClass W)) = _
  rw [← compactSupportKZeroOpenPushforward_homeomorph,
    ← AddMonoidHom.comp_apply,
    ← compactSupportKZeroOpenPushforward_comp tube htube
      g₁.flatHomeomorph g₁.flatHomeomorph.isOpenEmbedding]
  simp only [hm]
  rw [compactSupportKZeroOpenPushforward_comp R R.isOpenEmbedding β hβ,
    AddMonoidHom.comp_apply, compactSupportKZeroOpenPushforward_homeomorph R,
    hbott, hisotopy]

end AtiyahSinger
