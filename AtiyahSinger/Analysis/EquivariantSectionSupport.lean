/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSmoothSections

/-!
# Support under the geometric section action

Public module ID: M0569.

The prescribed bundle action carries the closed nonzero set of a section to its
image under the same base action. This standard support identity applies before
restricting to smooth sections and is used for both conjugation and averaging.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [TopologicalSpace M] [MulAction G M] [ContinuousSMul G M]
  {r : ℕ} {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]

/-- The section formula is the original moving-fiber action in the total space. -/
theorem EquivariantStructure.mk_sectionLinearMap
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) (g : G) (s : ∀ x, E x) (x : M) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    (⟨x, σ.sectionLinearMap g s x⟩ : TotalSpace Unit E) =
      ⟨g • (g⁻¹ • x), σ.linearMap g (g⁻¹ • x) (s (g⁻¹ • x))⟩ := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let transport : ∀ {x y : M}, x = y → E x →ₗ[ℂ] E y := fun {x y} h ↦ by
    subst y
    exact LinearMap.id
  have htransport {x y : M} (hxy : x = y) (v : E x) :
      (⟨y, transport hxy v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
    subst y
    rfl
  change (⟨x, transport (smul_inv_smul g x)
    (σ.linearMap g (g⁻¹ • x) (s (g⁻¹ • x)))⟩ : TotalSpace Unit E) = _
  exact htransport (smul_inv_smul g x) _

/-- At a moved point, the section action is exactly the specified fiber action. -/
theorem EquivariantStructure.sectionLinearMap_smul
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) (g : G) (s : ∀ x, E x) (x : M) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    σ.sectionLinearMap g s (g • x) = σ.linearMap g x (s x) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  apply TotalSpace.mk_injective (F := Unit) (g • x)
  have h := σ.mk_sectionLinearMap g s (g • x)
  change (⟨g • x, σ.sectionLinearMap g s (g • x)⟩ : TotalSpace Unit E) =
    ⟨g • (g⁻¹ • (g • x)), σ.linearMap g (g⁻¹ • (g • x)) (s (g⁻¹ • (g • x)))⟩ at h
  rw [inv_smul_smul] at h
  exact h

/-- The actual geometric section action transports closed support by the base action. -/
theorem EquivariantStructure.closure_support_sectionLinearMap
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E) (g : G) (s : ∀ x, E x) :
    closure {x | σ.sectionLinearMap g s x ≠ 0} =
      (fun x : M ↦ g • x) '' closure {x | s x ≠ 0} := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  -- Express the moving fiber by a total-space equality, retaining the original cast.
  have htotal (x : M) :
      (⟨x, σ.sectionLinearMap g s x⟩ : TotalSpace Unit E) =
        g • (⟨g⁻¹ • x, s (g⁻¹ • x)⟩ : TotalSpace Unit E) := by
    exact σ.mk_sectionLinearMap g s x
  have hzero (x : M) :
      g • (⟨g⁻¹ • x, 0⟩ : TotalSpace Unit E) = ⟨x, 0⟩ := by
    change (⟨g • (g⁻¹ • x), σ.linearMap g (g⁻¹ • x) 0⟩ : TotalSpace Unit E) = _
    simp only [map_zero]
    exact congrArg (fun y : M ↦ (⟨y, 0⟩ : TotalSpace Unit E)) (smul_inv_smul g x)
  have heq (x : M) : σ.sectionLinearMap g s x = 0 ↔ s (g⁻¹ • x) = 0 := by
    constructor
    · intro h
      apply TotalSpace.mk_injective (F := Unit) (g⁻¹ • x)
      apply (MulAction.injective g)
      exact (htotal x).symm.trans ((congrArg (fun v : E x ↦
        (⟨x, v⟩ : TotalSpace Unit E)) h).trans (hzero x).symm)
    · intro h
      apply TotalSpace.mk_injective (F := Unit) x
      exact (htotal x).trans ((congrArg (fun v : E (g⁻¹ • x) ↦
        g • (⟨g⁻¹ • x, v⟩ : TotalSpace Unit E)) h).trans (hzero x))
  -- A base homeomorphism carries both the nonzero set and its closure to their images.
  have hset : {x | σ.sectionLinearMap g s x ≠ 0} =
      (fun x : M ↦ g • x) '' {x | s x ≠ 0} := by
    ext x
    constructor
    · intro hx
      exact ⟨g⁻¹ • x, (heq x).not.mp hx, smul_inv_smul g x⟩
    · rintro ⟨y, hy, rfl⟩
      apply (heq (g • y)).not.mpr
      rw [inv_smul_smul]
      exact hy
  rw [hset]
  exact ((Homeomorph.smul g).image_closure {x | s x ≠ 0}).symm

end AtiyahSinger.ComplexBundle
