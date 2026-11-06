/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ThomZeroSection

/-!
# The alternating exterior class of an actual line bundle

Public module ID: M1926.

The scalar inclusion identifies the even exterior bundle with the trivial
line, and the original vector inclusion identifies the odd exterior bundle
with the given line. Their continuity is checked in the original finite
wedge-sum topology. Thus the alternating class of the line is one minus
its original K class, with the exterior convention used by the Thom symbol.

Source: SG III.12, Lemma 12.3 and the line calculation underlying (12.11).
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity
  trivialTopology isFiniteRank_trivial

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The alternating exterior class of a line is the unit minus the class of that same line. -/
theorem lambdaMinusOne_eq_one_sub_of_finrank_eq_one
    (hline : ∀ x, Module.finrank ℂ (E x) = 1) :
    lambdaMinusOne E =
      AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1) - kZeroClass E := by
  classical
  let P (i : ZMod 2) (x : X) : Type _ :=
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
  -- Every pair of vectors in a line is dependent, so their exterior product vanishes.
  have hmul (x : X) (u v : E x) : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v = 0 := by
    let : Nontrivial (E x) := Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [hline x]
      exact zero_lt_one)
    obtain ⟨w, hw⟩ := exists_ne (0 : E x)
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one (hline x) hw u
    obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one (hline x) hw v
    rw [← ha, ← hb, map_smul, map_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      ExteriorAlgebra.ι_sq_zero, smul_zero, smul_zero]
  have heven (x : X) (a : P 0 x) :
      ∃ c : ℂ, algebraMap ℂ (ExteriorAlgebra ℂ (E x)) c = a.val := by
    induction a.val, a.property using CliffordAlgebra.even_induction with
    | algebraMap c => exact ⟨c, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨d, rfl⟩ := hb
      exact ⟨c + d, map_add _ c d⟩
    | ι_mul_ι_mul u v a _ _ =>
      refine ⟨0, ?_⟩
      change algebraMap ℂ (ExteriorAlgebra ℂ (E x)) 0 =
        ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v * a
      rw [hmul, zero_mul, map_zero]
  have hodd (x : X) (a : P 1 x) : ∃ v : E x, ExteriorAlgebra.ι ℂ v = a.val := by
    induction a.val, a.property using CliffordAlgebra.odd_induction with
    | ι v => exact ⟨v, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, rfl⟩ := ha
      obtain ⟨v, rfl⟩ := hb
      exact ⟨u + v, map_add _ u v⟩
    | ι_mul_ι_mul u v a _ _ =>
      refine ⟨0, ?_⟩
      change ExteriorAlgebra.ι ℂ (0 : E x) =
        ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v * a
      rw [hmul, zero_mul, map_zero]
  -- Degree-zero and degree-one generators give continuity in the original exterior topology.
  let D (k : ℕ) := TotalSpace Unit
    (fun x ↦ (Fin 1 → ℂ) × (Fin 1 → Fin k → E x))
  let (k : ℕ) : TopologicalSpace (D k) := TopologicalSpace.induced
    (fun z : D k ↦ (z.proj, z.snd.1,
      fun (i : Fin 1) (j : Fin k) ↦ (⟨z.proj, z.snd.2 i j⟩ : TotalSpace Unit E))) inferInstance
  have hgen (k : ℕ) : Continuous (fun z : D k ↦
      (⟨z.proj, ∑ i : Fin 1, z.snd.1 i • ExteriorAlgebra.ιMulti ℂ k (z.snd.2 i)⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) :=
    continuous_iSup_rng (i := 1)
      (continuous_iSup_rng (i := fun _ : Fin 1 ↦ k) continuous_coinduced_rng)
  let T := Bundle.Trivial X (Fin 1 → ℂ)
  have hscalar : Continuous (fun z : TotalSpace Unit T ↦
      (⟨z.proj, algebraMap ℂ (ExteriorAlgebra ℂ (E z.proj)) (z.snd 0)⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
    let q (z : TotalSpace Unit T) : D 0 := ⟨z.proj, z.snd, fun _ ↦ Fin.elim0⟩
    have hq : Continuous q := by
      have hz : Continuous (fun z : TotalSpace Unit T ↦ (z.proj, z.snd)) :=
        continuous_induced_dom
      apply continuous_induced_rng.mpr
      refine hz.fst.prodMk (hz.snd.prodMk ?_)
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact j.elim0
    apply ((hgen 0).comp hq).congr
    intro z
    simp only [Function.comp_apply, q, Fin.sum_univ_one, ExteriorAlgebra.ιMulti_zero_apply,
      Algebra.algebraMap_eq_smul_one]
  have hvector : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, ExteriorAlgebra.ι ℂ z.snd⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
    let q (z : TotalSpace Unit E) : D 1 := ⟨z.proj, fun _ ↦ 1, fun _ _ ↦ z.snd⟩
    have hq : Continuous q := by
      apply continuous_induced_rng.mpr
      refine (continuous_proj (E := E)).prodMk (continuous_const.prodMk ?_)
      exact continuous_pi fun _ ↦ continuous_pi fun _ ↦ continuous_id
    apply ((hgen 1).comp hq).congr
    intro z
    simp only [Function.comp_apply, q, Fin.sum_univ_one, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one, one_smul]
  let e₀ : Hom T (P 0) :=
    { linearMap x :=
        { toFun c := ⟨algebraMap ℂ (ExteriorAlgebra ℂ (E x)) (c 0),
            SetLike.algebraMap_mem_graded _ _⟩
          map_add' c d := Subtype.ext (map_add _ (c 0) (d 0))
          map_smul' a c := by
            apply Subtype.ext
            change algebraMap ℂ (ExteriorAlgebra ℂ (E x)) (a * c 0) =
              a • algebraMap ℂ (ExteriorAlgebra ℂ (E x)) (c 0)
            rw [map_mul, Algebra.smul_def] }
      continuous_total := continuous_induced_rng.mpr hscalar }
  let e₁ : Hom E (P 1) :=
    { linearMap x := (ExteriorAlgebra.ι ℂ).codRestrict
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
        (CliffordAlgebra.ι_mem_evenOdd_one (0 : QuadraticForm ℂ (E x)))
      continuous_total := continuous_induced_rng.mpr hvector }
  -- The canonical maps are bijective fiberwise, hence genuine Isos of the original bundles.
  have he₀ (x : X) : Function.Bijective (e₀.linearMap x) := by
    constructor
    · intro c d hcd
      have hzero : c 0 = d 0 := (ExteriorAlgebra.algebraMap_leftInverse (E x)).injective
        (congrArg Subtype.val hcd)
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hzero
    · intro a
      obtain ⟨c, hc⟩ := heven x a
      exact ⟨fun _ ↦ c, Subtype.ext hc⟩
  have he₁ (x : X) : Function.Bijective (e₁.linearMap x) := by
    constructor
    · intro u v huv
      exact ExteriorAlgebra.ι_leftInverse.injective (congrArg Subtype.val huv)
    · intro a
      obtain ⟨v, hv⟩ := hodd x a
      exact ⟨v, Subtype.ext hv⟩
  unfold lambdaMinusOne
  rw [← kZeroClass_eq_of_iso (e₀.toIso he₀), ← kZeroClass_eq_of_iso (e₁.toIso he₁),
    kZeroClass_trivial]

end AtiyahSinger.ComplexBundle
