/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAtlasOperator
public import AtiyahSinger.Geometry.AssociatedSmoothBundleDescent

/-!
# Restriction to the actual associated sphere fiber

Restriction at every specified principal point gives a linear map from the
original associated smooth sections to the original sphere smooth sections.
The identity holds in the original quotient fiber for every sphere point.

Smoothness is verified in the given associated charts. An arbitrary principal
coordinate acts on the sphere section by its actual smooth representation;
the inverse action removes that coordinate. No global principal section or
smooth choice of representatives is assumed. This supplies the vertical
operator's full-fiber restriction in SG III.13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {E : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (E y)]
  [∀ y, Module ℂ (E y)] [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (A : SmoothComplexBundleAtlas (n := r) E)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) E)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction at a principal point preserves the actual smooth fiber sections. -/
theorem exists_associatedSphereFiberRestriction (p : P) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∃ R : (associatedSphereSmoothBundleAtlas S A σ hσ).smoothSections →ₗ[ℂ] A.smoothSections,
      ∀ (w : (associatedSphereSmoothBundleAtlas S A σ hσ).smoothSections)
        (y : OrthogonalSphere r),
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((R w).val y) =
          w.val (associatedBundleMk G P (OrthogonalSphere r) p y) := by
  classical
  let := lieGroup_orthogonalGroup r
  let := associatedSphereChartedSpace S
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let t := associatedSphereTrivialization S
  let e (y : OrthogonalSphere r) : E y ≃ₗ[ℂ]
      D (associatedBundleMk G P (OrthogonalSphere r) p y) :=
    LinearEquiv.ofBijective
      (associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle σ p y rfl).mk'
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p y rfl)
  let R₀ : AD.smoothSections →ₗ[ℂ] (∀ y : OrthogonalSphere r, E y) :=
    LinearMap.pi fun y ↦ (e y).symm.toLinearMap.comp
      ((LinearMap.proj (associatedBundleMk G P (OrthogonalSphere r) p y)).comp
        AD.smoothSections.subtype)
  have hR (w : AD.smoothSections) (y : OrthogonalSphere r) :
      associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl (R₀ w y) =
        w.val (associatedBundleMk G P (OrthogonalSphere r) p y) :=
    (e y).apply_symm_apply _
  have hsmooth (w : AD.smoothSections) : A.IsSmoothSection (R₀ w) := by
    let b := projection p
    let g : G := (S.trivialization b p).2
    let s := R₀ w
    let sg := σ.dependentSectionLinearMap g s
    -- In a fixed principal chart, the upstairs coordinates detect g acting on the section.
    have htotal (y : OrthogonalSphere r) :
        (⟨y, sg y⟩ : TotalSpace Unit E) =
          ⟨g • (g⁻¹ • y), σ.linearMap g (g⁻¹ • y) (s (g⁻¹ • y))⟩ := by
      let transport : ∀ {x z : OrthogonalSphere r}, x = z → E x →ₗ[ℂ] E z :=
        fun {x z} h ↦ by
          subst z
          exact LinearMap.id
      have htransport {x z : OrthogonalSphere r} (h : x = z) (v : E x) :
          (⟨z, transport h v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
        subst z
        rfl
      exact htransport (smul_inv_smul g y) _
    have hsg : A.IsSmoothSection sg := by
      intro j
      let f (y : OrthogonalSphere r) : Z :=
        associatedBundleMk G P (OrthogonalSphere r) p (g⁻¹ • y)
      have hf : ContMDiff (𝓡 r) (𝓡 (n + r)) ∞ f :=
        d.contMDiff.comp ((smoothAssociatedSphereFiberInclusion S p).contMDiff.comp
          (orthogonalSphereDiffeomorph r g⁻¹).contMDiff)
      have htb : (t b).baseSet = (S.trivialization b).baseSet :=
        (exists_associatedBundleTrivialization S.toIsPrincipalBundle
          (S.trivialization b) (S.equivariant b)).choose_spec.1
      have ht (y : OrthogonalSphere r) : t b (f y) = (b, y) := by
        have h := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
          (S.trivialization b) (S.equivariant b)).choose_spec.2.1
          p (g⁻¹ • y) (S.mem_baseSet b)
        have h' : t b (f y) = (b, g • (g⁻¹ • y)) := h
        simpa only [smul_inv_smul] using h' 
      have hbase (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet) :
          f y ∈ (AD.chart (b, j)).baseSet := by
        have hADbase : (AD.chart (b, j)).baseSet =
            (t b).source ∩ (t b) ⁻¹' (Set.univ ×ˢ (A.chart j).baseSet) :=
          (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
            (S.trivialization b) (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.1
        rw [hADbase]
        refine ⟨(t b).mem_source.mpr (htb.symm ▸ S.mem_baseSet b), ?_⟩
        rw [Set.mem_preimage, ht]
        exact ⟨Set.mem_univ b, hy⟩
      have hcoord := (w.property (b, j)).comp hf.contMDiffOn hbase
      apply hcoord.congr
      intro y _
      have h := (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
        (S.trivialization b) (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.2.2
        p (g⁻¹ • y) (f y) rfl (s (g⁻¹ • y)) (S.mem_baseSet b)
      rw [hR] at h
      exact (congrArg (fun z : TotalSpace Unit E ↦ (A.chart j z).2) (htotal y)).trans h.symm
    -- Apply the actual inverse smooth action, whose group law recovers this same section.
    let props := σ.atlasSmoothSectionAction_properties 𝓘(ℝ, OrthogonalGroupModel r) A hσ
    have hback := props.1 g⁻¹ ⟨sg, hsg⟩
    have heq : σ.dependentSectionLinearMap g⁻¹ sg = s := by
      change ((σ.dependentSectionLinearMap g⁻¹).comp
        (σ.dependentSectionLinearMap g)) s = s
      rw [← props.2.2, inv_mul_cancel, props.2.1]
      rfl
    change A.IsSmoothSection (σ.dependentSectionLinearMap g⁻¹ sg) at hback
    rw [heq] at hback
    exact hback
  let R : AD.smoothSections →ₗ[ℂ] A.smoothSections :=
    { toFun w := ⟨R₀ w, hsmooth w⟩
      map_add' u v := Subtype.ext (R₀.map_add u v)
      map_smul' c u := Subtype.ext (R₀.map_smul c u) }
  exact ⟨R, hR⟩

/-- Restriction to the whole sphere at the specified principal point, in its original
coordinates. -/
def associatedSphereFiberRestriction (p : P) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereSmoothBundleAtlas S A σ hσ).smoothSections →ₗ[ℂ] A.smoothSections :=
  (exists_associatedSphereFiberRestriction S A σ hσ p).choose

set_option maxSynthPendingDepth 30 in
/-- The chosen restriction has the specified value at every point of the original fiber. -/
theorem associatedSphereFiberRestriction_apply (p : P) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (w : (associatedSphereSmoothBundleAtlas S A σ hσ).smoothSections)
      (y : OrthogonalSphere r),
      associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl
          ((associatedSphereFiberRestriction S A σ hσ p w).val y) =
        w.val (associatedBundleMk G P (OrthogonalSphere r) p y) :=
  (exists_associatedSphereFiberRestriction S A σ hσ p).choose_spec

end AtiyahSinger
