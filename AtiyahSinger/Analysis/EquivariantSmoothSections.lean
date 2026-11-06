/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import Mathlib.RepresentationTheory.Basic

/-!
# The original equivariant action on smooth sections

Public module ID: M0579.

The action is the geometric formula `(g * s)(x) = g * s(g⁻¹ * x)` from
SG III.9, printed p.211. The moved fiber is identified with the original
fiber only along the actual equality `g * (g⁻¹ * x) = x`. The standard
representation is built on the existing `smoothSections`, without choosing
a new section space, basis, norm, metric, or representation.

The group and bundle actions are jointly smooth in the supplied original
atlases. The group is not assumed compact for this algebraic construction.
Continuity for the derivative-seminorm topology is a separate statement;
no pointwise section topology is used here as a substitute for that topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [TopologicalSpace M] [MulAction G M] [ContinuousSMul G M]
  {r : ℕ} {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]

/-- The actual geometric section action, using only its original moving-fiber linear maps. -/
def EquivariantStructure.sectionLinearMap
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) (g : G) : (∀ x, E x) →ₗ[ℂ] (∀ x, E x) := by
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  -- Equality transport changes only the dependent fiber index, with no chosen fiber isomorphism.
  let transport : ∀ {x y : M}, x = y → E x →ₗ[ℂ] E y := fun {x y} h ↦ by
    subst y
    exact LinearMap.id
  exact LinearMap.pi fun x ↦
    (transport (smul_inv_smul g x)).comp
      ((σ.linearMap g (g⁻¹ • x)).comp (LinearMap.proj (g⁻¹ • x)))

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG) [ChartedSpace HG G]
  {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hG : IsManifold IG ∞ G]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

include hG hM hE hAction in
set_option linter.unusedSectionVars false in
/-- The geometric action preserves smooth sections and satisfies the original group laws. -/
theorem EquivariantStructure.smoothSectionAction_properties
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) (hσ : σ.IsSmooth (n := n) (r := r) IG) :
    (∀ (g : G) (s : smoothSections (n := n) (r := r) E),
      IsSmoothSection (n := n) (r := r) E (σ.sectionLinearMap g s.val)) ∧
      σ.sectionLinearMap 1 = LinearMap.id ∧
      ∀ g h : G, σ.sectionLinearMap (g * h) =
        (σ.sectionLinearMap g).comp (σ.sectionLinearMap h) := by
  /- Use a source frame near g⁻¹*x and a target frame near x. In those same
  frames the transformed section is the finite sum of its smooth source
  coordinates times the prescribed smooth action columns. The group laws
  are then checked in the original total space, so the only fiber transport
  is the one already present in sectionLinearMap. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let transport : ∀ {x y : M}, x = y → E x →ₗ[ℂ] E y := fun {x y} h ↦ by
    subst y
    exact LinearMap.id
  have htransport {x y : M} (hxy : x = y) (v : E x) :
      (⟨y, transport hxy v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
    subst y
    rfl
  -- Record the original action formula as an equality of total vectors.
  have htotal (g : G) (s : ∀ x, E x) (x : M) :
      (⟨x, σ.sectionLinearMap g s x⟩ : TotalSpace Unit E) =
        g • (⟨g⁻¹ • x, s (g⁻¹ • x)⟩ : TotalSpace Unit E) := by
    change (⟨x, transport (smul_inv_smul g x)
      (σ.linearMap g (g⁻¹ • x) (s (g⁻¹ • x)))⟩ : TotalSpace Unit E) = _
    exact htransport (smul_inv_smul g x) _
  refine ⟨?_, ?_, ?_⟩
  · intro g s f hf x hx
    let := hf
    let d := trivializationAt (EuclideanSpace ℂ (Fin r)) E (g⁻¹ • x)
    let U : Set M := {y | g⁻¹ • y ∈ d.baseSet ∧ y ∈ f.baseSet}
    have hdx : g⁻¹ • x ∈ d.baseSet := mem_baseSet_trivializationAt _ _ _
    have hk : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun y : M ↦ g⁻¹ • y) :=
      ContMDiffSMul.contMDiff_const_smul (I := IG) g⁻¹
    have hopen : IsOpen U :=
      (d.open_baseSet.preimage hk.continuous).inter f.open_baseSet
    have hsource := (s.property d inferInstance).comp hk.contMDiffOn
      (show Set.MapsTo (fun y : M ↦ g⁻¹ • y) U d.baseSet from fun _ hy ↦ hy.1)
    -- Restrict the joint action columns to (g, g⁻¹*y) in the original overlap.
    have hcolumns (j : Fin r) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
          (fun y ↦ (f ⟨g • (g⁻¹ • y),
            σ.linearMap g (g⁻¹ • y)
              (d.symmL ℂ (g⁻¹ • y) (EuclideanSpace.single j 1))⟩).2) U := by
      apply (hσ d f j).comp (contMDiff_const.prodMk hk).contMDiffOn
      intro y hy
      exact ⟨hy.1, by simpa only [smul_inv_smul] using hy.2⟩
    have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
        (fun y ↦ ∑ j : Fin r, (d ⟨g⁻¹ • y, s.val (g⁻¹ • y)⟩).2 j •
          (f ⟨g • (g⁻¹ • y), σ.linearMap g (g⁻¹ • y)
            (d.symmL ℂ (g⁻¹ • y) (EuclideanSpace.single j 1))⟩).2) U := by
      apply contMDiffOn_finsetSum
      intro j _
      have hcoeff := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).restrictScalars
        ℝ).contMDiff.comp_contMDiffOn hsource
      have hmul : ContDiff ℝ ∞
          (fun p : ℂ × EuclideanSpace ℂ (Fin r) ↦ p.1 • p.2) := contDiff_smul
      exact hmul.contMDiff.comp_contMDiffOn (hcoeff.prodMk_space (hcolumns j))
    -- Finite-frame reconstruction identifies this sum with the actual section.
    have hlocal := hsum.congr (f₁ := fun y ↦ (f ⟨y, σ.sectionLinearMap g s.val y⟩).2) ?_
    · exact (hlocal.contMDiffAt (hopen.mem_nhds ⟨hdx, hx⟩)).contMDiffWithinAt
    · intro y hy
      have hmoved : g • (g⁻¹ • y) ∈ f.baseSet := by
        simpa only [smul_inv_smul] using hy.2
      let L := (f.linearMapAt ℂ (g • (g⁻¹ • y))).comp
        ((σ.linearMap g (g⁻¹ • y)).comp (d.symmL ℂ (g⁻¹ • y)).toLinearMap)
      have hexpand := congrArg L
        ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr (d ⟨g⁻¹ • y, s.val (g⁻¹ • y)⟩).2)
      have hcoordinates := congrArg
        (fun z : TotalSpace Unit E ↦
          (f (⟨z.proj, z.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)).2)
        (htotal g s.val y)
      exact hcoordinates.trans (by
        change (f ⟨g • (g⁻¹ • y), σ.linearMap g (g⁻¹ • y)
          (s.val (g⁻¹ • y))⟩).2 = _
        simpa [L, map_sum, map_smul, EuclideanSpace.basisFun_apply,
          EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hmoved,
          d.symmL_apply hy.1, d.symm_apply_apply_mk hy.1] using hexpand.symm)
  · -- The identity law holds before restricting to the smooth subspace.
    apply LinearMap.ext
    intro s
    funext x
    apply TotalSpace.mk_injective (F := Unit) x
    have hbase : (1 : G)⁻¹ • x = x := by rw [inv_one, one_smul]
    exact (htotal 1 s x).trans ((one_smul G _).trans
      (congrArg (fun y : M ↦ (⟨y, s y⟩ : TotalSpace Unit E)) hbase))
  · -- Composition uses the same source point h⁻¹*(g⁻¹*x) on both sides.
    intro g h
    apply LinearMap.ext
    intro s
    funext x
    apply TotalSpace.mk_injective (F := Unit) x
    change (⟨x, σ.sectionLinearMap (g * h) s x⟩ : TotalSpace Unit E) =
      ⟨x, σ.sectionLinearMap g (σ.sectionLinearMap h s) x⟩
    rw [htotal, htotal, htotal, mul_smul]
    apply congrArg (fun z : TotalSpace Unit E ↦ g • h • z)
    apply congrArg (fun y : M ↦ (⟨y, s y⟩ : TotalSpace Unit E))
    rw [mul_inv_rev, mul_smul]

/-- Restriction of the original geometric action to the existing space of smooth sections. -/
def EquivariantStructure.smoothSectionRepresentation
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) (hσ : σ.IsSmooth (n := n) (r := r) IG) :
    Representation ℂ G (smoothSections (n := n) (r := r) E) := by
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let h := σ.smoothSectionAction_properties IG hσ
  exact
    { toFun := fun g ↦
        { toFun := fun s ↦ ⟨σ.sectionLinearMap g s.val, h.1 g s⟩
          map_add' := fun s t ↦ Subtype.ext ((σ.sectionLinearMap g).map_add s.val t.val)
          map_smul' := fun c s ↦ Subtype.ext ((σ.sectionLinearMap g).map_smul c s.val) }
      map_one' := by
        apply LinearMap.ext
        intro s
        apply Subtype.ext
        exact congrArg (fun T : (∀ x, E x) →ₗ[ℂ] (∀ x, E x) ↦ T s.val) h.2.1
      map_mul' := by
        intro g k
        apply LinearMap.ext
        intro s
        apply Subtype.ext
        exact congrArg (fun T : (∀ x, E x) →ₗ[ℂ] (∀ x, E x) ↦ T s.val) (h.2.2 g k) }

end AtiyahSinger.ComplexBundle
