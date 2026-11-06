/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSmoothSections
public import AtiyahSinger.Geometry.OpenSections
public import AtiyahSinger.Geometry.SmoothEquivariantPullback
public import AtiyahSinger.Geometry.SmoothSectionPullback

/-!
# Equivariant pullback and clopen zero extension of original sections

Public module ID: M0567.

The geometric action is compared in the original total space, before canceling
its base transports. Smooth pullback therefore intertwines the same bundle
actions. On an invariant clopen open submanifold, genuine zero extension also
intertwines them; this supplies the action square used for the actual diagonal
PDO blocks and their finite kernel and quotient-cokernel representations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {r : ℕ} {E : X → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]

/-- The geometric section action is the original action on the same total vector. -/
theorem EquivariantStructure.sectionLinearMap_totalSpace
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (g : G) (s : ∀ x, E x) (x : X) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    (⟨x, σ.sectionLinearMap g s x⟩ : TotalSpace Unit E) =
      ⟨g • (g⁻¹ • x), σ.linearMap g (g⁻¹ • x) (s (g⁻¹ • x))⟩ := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let transport : ∀ {x y : X}, x = y → E x →ₗ[ℂ] E y := fun {x y} h ↦ by
    subst y
    exact LinearMap.id
  have ht {x y : X} (hxy : x = y) (v : E x) :
      (⟨y, transport hxy v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
    subst y
    rfl
  exact ht (smul_inv_smul g x) _

variable {Y : Type*} [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

omit [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E] in
/-- Geometric section actions commute with the actual equivariant pullback values. -/
theorem EquivariantStructure.sectionLinearMap_modelPullback
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (g : G) (s : ∀ x, E x) (y : Y) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)
    (σ.modelPullback f heq).sectionLinearMap g (fun z ↦ s (f z)) y =
      σ.sectionLinearMap g s (f y) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)
  apply TotalSpace.mk_injective (f y) (F := Unit)
  -- Lift the pulled action first; equivariance then identifies its moved original base point.
  have hp := congrArg
    (fun z : TotalSpace Unit ((f : Y → X) *ᵖ E) ↦
      (⟨f z.proj, z.snd⟩ : TotalSpace Unit E))
    ((σ.modelPullback f heq).sectionLinearMap_totalSpace g (fun z ↦ s (f z)) y)
  refine hp.trans ((σ.modelPullback_lift f heq g (g⁻¹ • y) (s (f (g⁻¹ • y)))).trans ?_)
  refine (congrArg (fun z : X ↦
    (⟨g • z, σ.linearMap g z (s z)⟩ : TotalSpace Unit E)) (heq g⁻¹ y)).trans ?_
  exact (σ.sectionLinearMap_totalSpace g s (f y)).symm

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG) [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  {n m : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) Y]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ X]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ Y]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G X]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Smooth section pullback intertwines the given original jointly smooth actions. -/
theorem EquivariantStructure.smoothSectionPullback_intertwines
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (hσ : σ.IsSmooth (n := n) (r := r) IG)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f) :
    letI := isSmoothComplexBundle_pullback (n := n) (m := m) (r := r) E f hf
    ∀ (g : G) (s : smoothSections (n := n) (r := r) E),
      smoothSectionPullback E f hf (σ.smoothSectionRepresentation (n := n) (r := r) IG hσ g s) =
        (σ.modelPullback f heq).smoothSectionRepresentation (n := m) (r := r) IG
          (σ.modelPullback_isSmooth IG hσ f heq hf) g (smoothSectionPullback E f hf s) := by
  let := isSmoothComplexBundle_pullback (n := n) (m := m) (r := r) E f hf
  intro g s
  apply Subtype.ext
  funext y
  exact (σ.sectionLinearMap_modelPullback f heq g s.val y).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual zero extension on an invariant clopen piece intertwines the original actions. -/
theorem EquivariantStructure.smoothSectionZeroExtension_intertwines
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (hσ : σ.IsSmooth (n := n) (r := r) IG)
    (U : Opens X) (hclosed : IsClosed (U : Set X))
    [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    (heq : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X)) :
    let f : C(U, X) := ContinuousMap.subtypeVal (U : Set X)
    letI := isSmoothComplexBundle_pullback (n := n) (m := n) (r := r)
      E f contMDiff_subtype_val
    let τ := σ.modelPullback f heq
    let hτ := σ.modelPullback_isSmooth IG hσ f heq contMDiff_subtype_val
    let Z : smoothSections (n := n) (r := r) ((f : U → X) *ᵖ E) →
        smoothSections (n := n) (r := r) E := fun u ↦
      smoothSectionZeroExtension E U (U : Set X) hclosed Set.Subset.rfl
        ⟨u, fun y hy ↦ False.elim (hy y.property)⟩
    ∀ g u, Z (τ.smoothSectionRepresentation (n := n) (r := r) IG hτ g u) =
      σ.smoothSectionRepresentation (n := n) (r := r) IG hσ g (Z u) := by
  classical
  let f : C(U, X) := ContinuousMap.subtypeVal (U : Set X)
  let := isSmoothComplexBundle_pullback (n := n) (m := n) (r := r)
    E f contMDiff_subtype_val
  let τ := σ.modelPullback f heq
  let hτ := σ.modelPullback_isSmooth IG hσ f heq contMDiff_subtype_val
  let Z : smoothSections (n := n) (r := r) ((f : U → X) *ᵖ E) →
      smoothSections (n := n) (r := r) E := fun u ↦
    smoothSectionZeroExtension E U (U : Set X) hclosed Set.Subset.rfl
      ⟨u, fun y hy ↦ False.elim (hy y.property)⟩
  dsimp only
  intro g u
  change Z (τ.smoothSectionRepresentation IG hτ g u) =
    σ.smoothSectionRepresentation IG hσ g (Z u)
  have hrestrict (v : smoothSections (n := n) (r := r) ((f : U → X) *ᵖ E)) :
      smoothSectionRestriction E U (Z v) = v := by
    apply Subtype.ext
    funext x
    change (if hx : x.val ∈ U then v.val ⟨x.val, hx⟩ else 0) = v.val x
    rw [dite_eq_left x.property]
  have hcomm := σ.smoothSectionPullback_intertwines IG hσ f heq contMDiff_subtype_val g (Z u)
  change smoothSectionRestriction E U (σ.smoothSectionRepresentation IG hσ g (Z u)) =
    τ.smoothSectionRepresentation IG hτ g (smoothSectionRestriction E U (Z u)) at hcomm
  rw [hrestrict] at hcomm
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ U
  · -- On the piece, the pullback square and restriction of zero extension recover u exactly.
    change (if hx' : x ∈ U then
      (τ.smoothSectionRepresentation IG hτ g u).val ⟨x, hx'⟩ else (0 : E x)) = _
    rw [dite_eq_left hx]
    exact (congrArg (fun v ↦ v.val ⟨x, hx⟩) hcomm).symm
  · -- Invariance keeps the inverse-translated input outside the piece, where it is zero.
    have houtside : g⁻¹ • x ∉ U := by
      intro hmem
      have hm := (g • (⟨g⁻¹ • x, hmem⟩ : U)).property
      rw [heq, smul_inv_smul] at hm
      exact hx hm
    have hz : (Z u).val (g⁻¹ • x) = 0 := by
      change (if h : g⁻¹ • x ∈ U then u.val ⟨g⁻¹ • x, h⟩ else (0 : E (g⁻¹ • x))) = 0
      exact dite_eq_right houtside
    change (if hx' : x ∈ U then
      (τ.smoothSectionRepresentation IG hτ g u).val ⟨x, hx'⟩ else (0 : E x)) =
        σ.sectionLinearMap g (Z u).val x
    rw [dite_eq_right hx]
    apply TotalSpace.mk_injective x (F := Unit)
    rw [σ.sectionLinearMap_totalSpace, hz, map_zero]
    exact congrArg (fun y : X ↦ (⟨y, (0 : E y)⟩ : TotalSpace Unit E))
      (smul_inv_smul g x).symm

end AtiyahSinger.ComplexBundle
