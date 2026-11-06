/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveCoordinates

/-!
# The tautological line over an orthogonal projective space

Public module ID: M2028.

The fiber is the literal range of the original rank-one projector. Its total
topology is induced from projective space times the original vector space.
On an affine chart the normalized projected reference vector trivializes this
line, with coefficient given by its inner product with the reference vector.
The first Chern class is the existing normalized integral line-bundle class.

Source: the usual tautological line and affine charts on complex projective
space, in Hatcher, Vector Bundles and K-Theory, Sections 1.1 and 3.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.HermitianProjectiveSpace

open Bundle

universe u

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The tautological fiber is the actual range of the original projector. -/
abbrev TautologicalLine (P : HermitianProjectiveSpace V InnerProductSpace.toCore) : Type u :=
  LinearMap.range P.val.toLinearMap

/-- The tautological total topology is the original subspace topology
in projective space times V. -/
@[reducible]
def tautologicalLineTopology : TopologicalSpace (TotalSpace Unit (TautologicalLine V)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (TautologicalLine V) ↦ (z.proj, z.snd.val)) inferInstance

attribute [local instance] tautologicalLineTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The normalized affine sections make the actual range fibers a complex line bundle. -/
theorem isFiniteRank_tautologicalLine : IsFiniteRank (TautologicalLine V) := by
  classical
  let Q := HermitianProjectiveSpace V InnerProductSpace.toCore
  let L := TautologicalLine V
  constructor
  intro P₀
  obtain ⟨e, he⟩ : ∃ e : V, P₀.val e ≠ 0 := by
    by_contra hz
    push Not at hz
    have hP : P₀.val.toLinearMap = 0 := LinearMap.ext hz
    have hr := P₀.property.2.1
    rw [hP, LinearMap.range_zero] at hr
    simp at hr
  let U : Set Q := {P | P.val e ≠ 0}
  have hU : IsOpen U := isOpen_affineChart_source e
  -- The affine normalization is a nonzero section of the same one-dimensional range.
  let s (P : Q) : L P :=
    ⟨(inner ℂ e (P.val e))⁻¹ • P.val e,
      ⟨(inner ℂ e (P.val e))⁻¹ • e, P.val.map_smul _ _⟩⟩
  have hinner (P : Q) (hP : P ∈ U) : inner ℂ e (s P).val = 1 :=
    (affineChart e ⟨P, hP⟩).property
  have hs : ContinuousOn (fun P : Q ↦ (s P).val) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp (affineChart e).continuous
  have hnonzero (P : Q) (hP : P ∈ U) : s P ≠ 0 := by
    intro hz
    have hi := hinner P hP
    have hv : (s P).val = 0 := congrArg Subtype.val hz
    rw [hv, inner_zero_right] at hi
    exact zero_ne_one hi
  let coeff (P : Q) (v : L P) : ℂ := inner ℂ e v.val
  have hleft (P : Q) (hP : P ∈ U) (v : L P) : coeff P v • s P = v := by
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one P.property.2.1 (hnonzero P hP) v
    rw [← hc]
    change inner ℂ e (c • (s P).val) • s P = c • s P
    rw [inner_smul_right, hinner P hP, mul_one]
  have hright (P : Q) (hP : P ∈ U) (c : ℂ) : coeff P (c • s P) = c := by
    change inner ℂ e (c • (s P).val) = c
    rw [inner_smul_right, hinner P hP, mul_one]
  -- Both chart directions use the induced topology of the original pairs (P,v).
  have hind : Topology.IsInducing (fun z : TotalSpace Unit L ↦ (z.proj, z.snd.val)) :=
    ⟨rfl⟩
  have hinc : Continuous (fun z : TotalSpace Unit L ↦ (z.proj, z.snd.val)) :=
    continuous_induced_dom
  have hb : Continuous (fun z : TotalSpace Unit L ↦ z.proj) := hinc.fst
  have hv : Continuous (fun z : TotalSpace Unit L ↦ z.snd.val) := hinc.snd
  have hcoeff : Continuous (fun z : TotalSpace Unit L ↦ coeff z.proj z.snd) :=
    continuous_const.inner hv
  have hfront : ContinuousOn (fun z : Q × (Fin 1 → ℂ) ↦
      (⟨z.1, z.2 0 • s z.1⟩ : TotalSpace Unit L)) (U ×ˢ Set.univ) := by
    apply hind.continuousOn_iff.mpr
    exact continuous_fst.continuousOn.prodMk
      (((continuous_apply 0).comp continuous_snd).continuousOn.smul
        (hs.comp continuous_fst.continuousOn (fun z hz ↦ hz.1)))
  let t : Trivialization (Fin 1 → ℂ) (π Unit L) :=
    { toFun := fun z ↦ (z.proj, fun _ ↦ coeff z.proj z.snd)
      invFun := fun z ↦ ⟨z.1, z.2 0 • s z.1⟩
      source := (π Unit L) ⁻¹' U
      target := U ×ˢ Set.univ
      baseSet := U
      open_source := hU.preimage hb
      open_target := hU.prod isOpen_univ
      open_baseSet := hU
      map_source' := fun z hz ↦ ⟨hz, Set.mem_univ _⟩
      map_target' := fun z hz ↦ hz.1
      left_inv' := by
        intro z hz
        exact congrArg (fun v : L z.proj ↦ (⟨z.proj, v⟩ : TotalSpace Unit L))
          (hleft z.proj hz z.snd)
      right_inv' := by
        intro z hz
        apply Prod.ext
        · rfl
        · funext i
          exact hright z.1 hz.1 (z.2 0) |>.trans
            (congrArg z.2 (Subsingleton.elim 0 i))
      continuousOn_toFun := hb.continuousOn.prodMk
        (continuousOn_pi.mpr fun _ ↦ hcoeff.continuousOn)
      continuousOn_invFun := hfront
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  refine ⟨1, t, he, ?_⟩
  intro P _
  constructor
  · intro v w
    funext i
    exact inner_add_right e v.val w.val
  · intro c v
    funext i
    exact inner_smul_right e v.val c

attribute [local instance] isFiniteRank_tautologicalLine

/-- The normalized integral first Chern class of the actual tautological range line. -/
def tautologicalChernRoot :
    singularCohomology ℤ (HermitianProjectiveSpace V InnerProductSpace.toCore) 2 :=
  firstChernClass (TautologicalLine V) (fun P ↦ P.property.2.1)

end AtiyahSinger.ComplexBundle.HermitianProjectiveSpace
