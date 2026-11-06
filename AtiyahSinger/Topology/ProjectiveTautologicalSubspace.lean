/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveSubspace
public import AtiyahSinger.Topology.ProjectiveTautologicalLine

/-!
# Tautological lines on a projective subspace

Public module ID: M2029.

The inclusion of a complex subspace sends its actual tautological range line
isomorphically to the ambient tautological range line. The forward map keeps
the original vector through the subspace inclusion. Its inverse is the unique
inverse of this same map between the one-dimensional ranges. The normalized
first Chern classes therefore agree under this specified projective inclusion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open Bundle

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

attribute [local instance] tautologicalLineTopology isFiniteRank_tautologicalLine
  isFiniteRank_pullback

/-- The actual inclusion of the smaller tautological range is an isomorphism onto its pullback. -/
def tautologicalSubspaceLineIso (K : Submodule ℂ V) :
    Iso (TautologicalLine K)
      ((linearImageMap K.subtypeL Subtype.val_injective :
        HermitianProjectiveSpace K InnerProductSpace.toCore →
          HermitianProjectiveSpace V InnerProductSpace.toCore) *ᵖ (TautologicalLine V)) := by
  let Q := HermitianProjectiveSpace K InnerProductSpace.toCore
  let L := TautologicalLine K
  let L₀ := TautologicalLine V
  let i := linearImageMap K.subtypeL Subtype.val_injective
  let F := (i : Q → HermitianProjectiveSpace V InnerProductSpace.toCore) *ᵖ L₀
  have hmem (P : Q) (v : L P) : v.val.val ∈ LinearMap.range (i P).val.toLinearMap := by
    obtain ⟨w, hw⟩ := v.property
    refine ⟨v.val.val, ?_⟩
    rw [← hw]
    exact linearImage_apply_image K.subtypeL P (subtype_comp_ne_zero K P) w
  let f : Hom L F :=
    { linearMap P :=
        { toFun := fun v ↦ ⟨v.val.val, hmem P v⟩
          map_add' := fun _ _ ↦ Subtype.ext rfl
          map_smul' := fun _ _ ↦ Subtype.ext rfl }
      continuous_total := by
        -- The induced topologies retain exactly the original point and included vector.
        have hc : Continuous (fun z : TotalSpace Unit L ↦ (z.proj, z.snd.val)) :=
          continuous_induced_dom
        rw [(inducing_pullbackTotalSpaceEmbedding Unit L₀ i).continuous_iff]
        refine hc.fst.prodMk ?_
        apply continuous_induced_rng.mpr
        exact (i.continuous.comp hc.fst).prodMk (continuous_subtype_val.comp hc.snd) }
  have hf (P : Q) : Function.Bijective (f.linearMap P) := by
    have hi : Function.Injective (f.linearMap P) := by
      intro v w hvw
      have hv : v.val.val = w.val.val :=
        congrArg (fun z : F P ↦ z.val) hvw
      exact Subtype.ext (Subtype.ext hv)
    let := finite_fiber (E := L) P
    let : FiniteDimensional ℂ (F P) := finite_fiber (E := L₀) (i P)
    have hr : Module.finrank ℂ (L P) = Module.finrank ℂ (F P) :=
      P.property.2.1.trans (i P).property.2.1.symm
    exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mp hi⟩
  exact
    { linearEquiv P := LinearEquiv.ofBijective (f.linearMap P) (hf P)
      continuous_total := f.continuous_total
      continuous_symm := f.continuous_inverse hf }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified projective subspace inclusion preserves the normalized tautological Chern root. -/
theorem tautologicalChernRoot_pullback_subspace (K : Submodule ℂ V) :
    singularCohomologyPullback ℤ (linearImageMap K.subtypeL Subtype.val_injective) 2
        (tautologicalChernRoot V) = tautologicalChernRoot K := by
  let L := TautologicalLine V
  let L' := TautologicalLine K
  let i := linearImageMap K.subtypeL Subtype.val_injective
  let F := (i : HermitianProjectiveSpace K InnerProductSpace.toCore →
    HermitianProjectiveSpace V InnerProductSpace.toCore) *ᵖ L
  let : ∀ P, NormedAddCommGroup (F P) :=
    fun P ↦ (inferInstance : NormedAddCommGroup (L (i P)))
  let : ∀ P, NormedSpace ℂ (F P) :=
    fun P ↦ (inferInstance : NormedSpace ℂ (L (i P)))
  let hL (P : HermitianProjectiveSpace V InnerProductSpace.toCore) :
      Module.finrank ℂ (L P) = 1 := P.property.2.1
  -- The original complex Thom normalization is compared on this same actual line inclusion.
  have hiso := firstChernClass_eq_of_iso (F := F) L' (fun P ↦ P.property.2.1)
    (fun P ↦ hL (i P)) (tautologicalSubspaceLineIso K)
  exact (firstChernClass_pullback L hL i).symm.trans hiso.symm

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
