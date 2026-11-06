/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Geometry.AssociatedSectionEvaluation
public import AtiyahSinger.Geometry.NativeSmoothAtlas

/-!
# The associated coefficient of the original smooth kernel

Specified finite representation coordinates on the actual kernel of a smooth
section operator descend to its associated coefficient evaluation. The image
over an entire fiber is exactly that kernel, and the coefficient-to-section
map is injective. Both statements use the original principal representatives
and the original native smooth sections, rather than a rank comparison.

SG III.13.6 uses this construction for the fiber operator and its formal
adjoint. This result retains whichever finite coordinates were specified for
those kernels; it does not choose them again or assert an upstairs index law.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology isFiniteRank_model

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E) (hσ : σ.IsSmooth (n := n) (r := r) IG)
  {P B W : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [AddCommGroup W] [Module ℂ W]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified finite kernel descends with its exact evaluation and full-fiber image. -/
theorem exists_associatedKernelEvaluation (hP : IsPrincipalBundle G projection)
    (T : smoothSections (n := n) (r := r) E →ₗ[ℂ] W)
    (κ : FiniteContinuousRepresentation G)
    (e : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] T.ker)
    (he : ∀ (g : G) (v : Fin κ.dimension → ℂ),
      (e (κ.representation g v)).val = σ.smoothSectionRepresentation IG hσ g (e v).val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    let q := associatedBundleProjection (F := M) hP
    ∃ a : Hom ((q : AssociatedBundle G P M → B) *ᵖ
        (AssociatedVectorFiber hP κ.representation)) (AssociatedEquivariantFiber hP σ),
      (∀ (p : P) (x : M) (v : Fin κ.dimension → ℂ),
        a.linearMap (associatedBundleMk G P M p x)
            (associatedVectorFiberMk hP κ.representation p rfl v) =
          associatedEquivariantFiberMk hP σ p x rfl ((e v).val.val x)) ∧
      (∀ (p : P) (u : smoothSections (n := n) (r := r) E),
        T u = 0 ↔ ∃ v : AssociatedVectorFiber hP κ.representation (projection p),
          ∀ x : M, a.linearMap (associatedBundleMk G P M p x) v =
            associatedEquivariantFiberMk hP σ p x rfl (u.val x)) ∧
      (∀ p : P,
        Function.Injective (fun v : AssociatedVectorFiber hP κ.representation (projection p) ↦
          fun x : M ↦ a.linearMap (associatedBundleMk G P M p x) v)) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let : IsFiniteRank E := A.isFiniteRank
  -- The atlas adapter retains every original native section and its kernel membership.
  let s : (Fin κ.dimension → ℂ) →ₗ[ℂ] A.smoothSections :=
    { toFun v := ⟨(e v).val.val,
        (isSmoothSection_nativeSmoothComplexBundleAtlas_iff E _).mpr (e v).val.property⟩
      map_add' u v := by
        apply Subtype.ext
        exact congrArg (fun w : T.ker ↦ w.val.val) (e.map_add u v)
      map_smul' c v := by
        apply Subtype.ext
        exact congrArg (fun w : T.ker ↦ w.val.val) (e.map_smul c v) }
  have hs : Function.Injective s := by
    intro u v huv
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : A.smoothSections ↦ w.val) huv
  have hsg (g : G) (x : M) (v : Fin κ.dimension → ℂ) :
      (s (κ.representation g v)).val (g • x) = σ.linearMap g x ((s v).val x) := by
    change (e (κ.representation g v)).val.val (g • x) = _
    rw [he]
    exact σ.sectionLinearMap_smul g (e v).val.val x
  obtain ⟨a, ha, himage, hinj⟩ := exists_associatedSectionEvaluation hP A σ κ s hsg
  refine ⟨a, ha, ?_, hinj hs⟩
  -- Surjectivity of the same finite coordinates gives exactly the original full kernel.
  intro p u
  rw [himage p u.val]
  constructor
  · intro hu
    let w : T.ker := ⟨u, hu⟩
    refine ⟨e.symm w, ?_⟩
    change (e (e.symm w)).val.val = u.val
    rw [e.apply_symm_apply]
  · rintro ⟨v, hv⟩
    have huv : (e v).val = u := Subtype.ext hv
    rw [← huv]
    exact (e v).property

end AtiyahSinger
