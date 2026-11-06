/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedKernelMetric
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalKernelRealization
public import AtiyahSinger.Geometry.AssociatedProductMeasure
public import AtiyahSinger.Geometry.AtlasHermitianMetric

/-!
# The integral pairing of the original associated kernel evaluation

Public module ID: M0099.

The integral Gram form of the specified finite family of smooth sphere
sections determines a metric on its actual associated coefficient bundle.
Tensor evaluation preserves that pairing after integration over the whole
sphere, and the original associated product measure gives the same global
pairing on the base. The evaluation map, coefficient metric, tensor metric
and product measure are all retained. This is the metric comparison needed
for the odd coefficient adjoint in SG III.13; no domain equality is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
  [MeasurableSpace (OrthogonalSphere r)] [BorelSpace (OrthogonalSphere r)]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "C" => fun b : B ↦ E b ⊗[ℂ] K b

omit [T2Space B] [SecondCountableTopology B] in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- Normalize the same associated kernel evaluation and invariant integral pairing.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified associated kernel evaluation preserves the complete original integral pairing. -/
theorem associatedTensorKernelEvaluation_integral
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : ContinuousHermitianMetric F) (hk : A.IsSmoothHermitianMetric k)
    (μ : Measure B) [IsFiniteMeasure μ] (ν : Measure Y) [IsFiniteMeasure ν]
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    (f : (Fin ρ.dimension → ℂ) →ₗ[ℂ] A.smoothSections)
    (ev : Hom ((πS : Z → B) *ᵖ K) D)
    (hev : ∀ (p : P) (y : Y) (v : Fin ρ.dimension → ℂ),
      ev.linearMap (associatedBundleMk G P Y p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((f v).val y)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
      (associatedOrthogonalRepresentationAtlas S ρ)
    ∀ (l : ContinuousHermitianMetric T) (c : ContinuousHermitianMetric C),
      AT.IsSmoothHermitianMetric l →
      (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F y),
        (l.toCore (associatedBundleMk G P Y p y)).inner
            (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
            (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
          h.pairing (projection p) u v * (k.toCore y).inner s t) →
      (∀ (p : P) (u v : E (projection p)) (s t : Fin ρ.dimension → ℂ),
        (c.toCore (projection p)).inner
            (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
            (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
          h.pairing (projection p) u v *
            ∫ y, (k.toCore y).inner ((f s).val y) ((f t).val y) ∂ν) →
      ∀ (u v : AC.smoothSections) (s t : AT.smoothSections),
        (∀ z, s.val z = TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) →
        (∀ z, t.val z = TensorProduct.map LinearMap.id (ev.linearMap z) (v.val (πS z))) →
        (∫ z, (l.toCore z).inner (s.val z) (t.val z)
          ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) =
          ∫ b, (c.toCore b).inner (u.val b) (v.val b) ∂μ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro AT AC l c hl hpair hgram u v s t hs ht
  have hi (w z : Fin ρ.dimension → ℂ) :
      Integrable (fun y ↦ (k.toCore y).inner ((f w).val y) ((f z).val y)) ν :=
    (A.contMDiff_pairing k hk (f w) (f z)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- At a fixed original representative, finite tensor expansion preserves the integral Gram form.
  have hfiber (p : P) (w z : C (projection p)) :
      (∫ y, (l.toCore (associatedBundleMk G P Y p y)).inner
        (TensorProduct.map LinearMap.id (ev.linearMap _) w)
        (TensorProduct.map LinearMap.id (ev.linearMap _) z) ∂ν) =
        (c.toCore (projection p)).inner w z := by
    let L (y : Y) : C (projection p) →ₗ[ℂ] T (associatedBundleMk G P Y p y) :=
      TensorProduct.map LinearMap.id (ev.linearMap (associatedBundleMk G P Y p y))
    have hcalc (y : Y) (a b : E (projection p)) (v w : Fin ρ.dimension → ℂ) :
        (l.toCore (associatedBundleMk G P Y p y)).inner
          (L y (a ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v))
          (L y (b ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl w)) =
          h.pairing (projection p) a b * (k.toCore y).inner ((f v).val y) ((f w).val y) := by
      have heval (a : E (projection p)) (v : Fin ρ.dimension → ℂ) :
          L y (a ⊗ₜ[ℂ]
            associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
          associatedSphereTensorFiberEquiv S E σ p y (a ⊗ₜ[ℂ] (f v).val y) := by
        exact congrArg (fun w ↦ a ⊗ₜ[ℂ] w) (hev p y v)
      rw [heval, heval]
      exact hpair p y a b ((f v).val y) ((f w).val y)
    have hleft (y : Y) (a b d : C (projection p)) :
        (l.toCore (associatedBundleMk G P Y p y)).inner (L y (a + b)) (L y d) =
          (l.toCore (associatedBundleMk G P Y p y)).inner (L y a) (L y d) +
          (l.toCore (associatedBundleMk G P Y p y)).inner (L y b) (L y d) := by
      rw [map_add]
      exact (l.toCore _).add_left _ _ _
    have hright (y : Y) (a b d : C (projection p)) :
        (l.toCore (associatedBundleMk G P Y p y)).inner (L y a) (L y (b + d)) =
          (l.toCore (associatedBundleMk G P Y p y)).inner (L y a) (L y b) +
          (l.toCore (associatedBundleMk G P Y p y)).inner (L y a) (L y d) := by
      rw [map_add]
      let := l.toCore (associatedBundleMk G P Y p y)
      exact InnerProductSpace.Core.inner_add_right _ _ _
    have hcRight (a b d : C (projection p)) :
        (c.toCore (projection p)).inner a (b + d) =
          (c.toCore (projection p)).inner a b + (c.toCore (projection p)).inner a d := by
      let := c.toCore (projection p)
      exact InnerProductSpace.Core.inner_add_right _ _ _
    have hiL (w z : C (projection p)) : Integrable (fun y ↦
        (l.toCore (associatedBundleMk G P Y p y)).inner (L y w) (L y z)) ν := by
      induction w using TensorProduct.inductionOn with
      | tmul a b =>
        obtain ⟨b, rfl⟩ :=
          (associatedVectorFiberMk_bijective S.toIsPrincipalBundle ρ.representation p rfl).2 b
        induction z using TensorProduct.inductionOn with
        | tmul d e =>
          obtain ⟨e, rfl⟩ :=
            (associatedVectorFiberMk_bijective S.toIsPrincipalBundle ρ.representation p rfl).2 e
          simpa only [hcalc] using (hi b e).const_mul (h.pairing (projection p) a d)
        | add z₁ z₂ hz₁ hz₂ => simpa only [hright, Pi.add_def] using hz₁.add hz₂
      | add w₁ w₂ hw₁ hw₂ => simpa only [hleft, Pi.add_def] using hw₁.add hw₂
    change (∫ y, (l.toCore (associatedBundleMk G P Y p y)).inner (L y w) (L y z) ∂ν) = _
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      obtain ⟨b, rfl⟩ :=
        (associatedVectorFiberMk_bijective S.toIsPrincipalBundle ρ.representation p rfl).2 b
      induction z using TensorProduct.inductionOn with
      | tmul d e =>
        obtain ⟨e, rfl⟩ :=
          (associatedVectorFiberMk_bijective S.toIsPrincipalBundle ρ.representation p rfl).2 e
        simp only [hcalc, integral_const_mul, hgram]
      | add z₁ z₂ hz₁ hz₂ =>
        simp only [hright, hcRight]
        rw [integral_add (hiL _ z₁) (hiL _ z₂), hz₁, hz₂]
    | add w₁ w₂ hw₁ hw₂ =>
      simp only [hleft, (c.toCore _).add_left]
      rw [integral_add (hiL w₁ _) (hiL w₂ _), hw₁, hw₂]
  -- The actual product measure integrates this same whole-fiber identity on the base.
  let pairing : C(Z, ℂ) := ⟨fun z ↦ (l.toCore z).inner (s.val z) (t.val z),
    (AT.contMDiff_pairing l hl s t).continuous⟩
  change (∫ z, pairing z ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) = _
  rw [integral_associatedProductMeasure_complex]
  apply integral_congr_ae
  filter_upwards with b
  obtain ⟨p, rfl⟩ := S.toIsPrincipalBundle.projection_properties.2.2 b
  rw [associatedFiberIntegral_apply S.toIsPrincipalBundle ν hν]
  change (∫ y, (l.toCore (associatedBundleMk G P Y p y)).inner
    (s.val _) (t.val _) ∂ν) = _
  simp_rw [hs, ht]
  exact hfiber p (u.val (projection p)) (v.val (projection p))

end AtiyahSinger
