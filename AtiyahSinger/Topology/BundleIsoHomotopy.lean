/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleRestriction
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies through actual bundle isomorphisms

Public module ID: M1579.

D07/K02. Joint continuity is encoded on the pullbacks to I × X; every time slice
is invertible, and both endpoint equations are explicit. Evaluating a slice on
the original total spaces uses their continuous projections, supplied by local
finite rank. This is the geometric
homotopy used in Karoubi II.2.13–2.16, without a compactness assumption.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : X → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]

/-- A jointly continuous path of bundle isomorphisms with specified endpoints. -/
structure IsoHomotopy (e₀ e₁ : Iso E F) where
  /-- The isomorphism on the two cylinder pullbacks. -/
  iso : Iso ((Prod.snd : I × X → X) *ᵖ E) ((Prod.snd : I × X → X) *ᵖ F)
  /-- The initial slice is the given initial isomorphism. -/
  map_zero : ∀ x v, iso.linearEquiv (0, x) v = e₀.linearEquiv x v
  /-- The terminal slice is the given terminal isomorphism. -/
  map_one : ∀ x v, iso.linearEquiv (1, x) v = e₁.linearEquiv x v

/-- A cylinder isomorphism restricts continuously to each time slice. -/
theorem IsoHomotopy.exists_eval [IsFiniteRank E] [IsFiniteRank F]
    {e₀ e₁ : Iso E F} (H : IsoHomotopy e₀ e₁) (t : I) :
    ∃ e : Iso E F, ∀ x v, e.linearEquiv x v = H.iso.linearEquiv (t, x) v := by
  /- Insert the fixed time into the cylinder total spaces. This insertion is
  continuous using the original continuous bundle projections and the constant
  time coordinate. Local finite rank supplies these projections. Compose
  with H and project back; the same construction with its inverse is continuous. -/
  -- Insert the same time into the original cylinder, then use its canonical lift.
  let f : I × X → X := Prod.snd
  have hE (t : I) : Continuous (fun z : TotalSpace Unit E ↦
      (⟨(t, z.proj), z.snd⟩ : TotalSpace Unit (f *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    exact (continuous_const.prodMk (continuous_proj (E := E))).prodMk continuous_id
  have hF (t : I) : Continuous (fun z : TotalSpace Unit F ↦
      (⟨(t, z.proj), z.snd⟩ : TotalSpace Unit (f *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
    exact (continuous_const.prodMk (continuous_proj (E := F))).prodMk continuous_id
  refine ⟨{ linearEquiv := fun x ↦ H.iso.linearEquiv (t, x)
            continuous_total := (Pullback.continuous_lift Unit F f).comp
              (H.iso.continuous_total.comp (hE t))
            continuous_symm := (Pullback.continuous_lift Unit E f).comp
              (H.iso.continuous_symm.comp (hF t)) }, fun _ _ ↦ rfl⟩

/-- Evaluate the homotopy at a time using its actual fiber maps. -/
def IsoHomotopy.eval [IsFiniteRank E] [IsFiniteRank F]
    {e₀ e₁ : Iso E F} (H : IsoHomotopy e₀ e₁) (t : I) : Iso E F :=
  (H.exists_eval t).choose

/-- Evaluation has the specified fiber action. -/
theorem IsoHomotopy.eval_apply [IsFiniteRank E] [IsFiniteRank F]
    {e₀ e₁ : Iso E F} (H : IsoHomotopy e₀ e₁)
    (t : I) (x : X) (v : E x) :
    (H.eval t).linearEquiv x v = H.iso.linearEquiv (t, x) v := by
  /- Use the fiber formula in the existence statement selecting the evaluation.
  It prevents the chosen isomorphism from being an unrelated isomorphism of the bundles. -/
  exact (H.exists_eval t).choose_spec x v

/-- Evaluation recovers the prescribed initial endpoint. -/
theorem IsoHomotopy.eval_zero [IsFiniteRank E] [IsFiniteRank F]
    {e₀ e₁ : Iso E F} (H : IsoHomotopy e₀ e₁) :
    H.eval 0 = e₀ := by
  /- Apply isomorphism extensionality and the evaluation formula. The map_zero
  field identifies the fiber map with the specified endpoint at every point and vector. -/
  apply Iso.ext
  intro x
  ext v
  exact (H.eval_apply 0 x v).trans (H.map_zero x v)

/-- Evaluation recovers the prescribed terminal endpoint. -/
theorem IsoHomotopy.eval_one [IsFiniteRank E] [IsFiniteRank F]
    {e₀ e₁ : Iso E F} (H : IsoHomotopy e₀ e₁) :
    H.eval 1 = e₁ := by
  /- Apply isomorphism extensionality and the evaluation formula. The map_one
  field identifies the fiber map with the specified endpoint at every point and vector. -/
  apply Iso.ext
  intro x
  ext v
  exact (H.eval_apply 1 x v).trans (H.map_one x v)

/-- There is a constant homotopy at every isomorphism. -/
theorem IsoHomotopy.nonempty_refl (e : Iso E F) : Nonempty (IsoHomotopy e e) := by
  /- Pull e back along the cylinder projection. Its fiber map is independent of
  time, so the two endpoint formulas follow by evaluating the same equivalence. -/
  exact ⟨{ iso := e.pullback ⟨Prod.snd, continuous_snd⟩
           map_zero := fun _ _ ↦ rfl
           map_one := fun _ _ ↦ rfl }⟩

/-- The constant homotopy exists by the explicit cylinder construction. -/
def IsoHomotopy.refl (e : Iso E F) : IsoHomotopy e e where
  iso := e.pullback ⟨Prod.snd, continuous_snd⟩
  map_zero _ _ := rfl
  map_one _ _ := rfl

/-- Reversing the time variable reverses a homotopy. -/
theorem IsoHomotopy.nonempty_symm {e₀ e₁ : Iso E F} (H : IsoHomotopy e₀ e₁) :
    Nonempty (IsoHomotopy e₁ e₀) := by
  /- Pull the cylinder isomorphism back along (t,x) ↦ (1-t,x). The endpoints
  are exchanged. Forward and inverse continuity follow from that continuous change of time. -/
  let f : I × X → X := Prod.snd
  -- Reversing time preserves the original base point and fiber vector.
  have hrevE : Continuous (fun z : TotalSpace Unit (f *ᵖ E) ↦
      (⟨(unitInterval.symm z.proj.1, z.proj.2), z.snd⟩ :
        TotalSpace Unit (f *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    exact ((unitInterval.continuous_symm.comp (Pullback.continuous_proj Unit E f).fst).prodMk
      (Pullback.continuous_proj Unit E f).snd).prodMk (Pullback.continuous_lift Unit E f)
  have hrevF : Continuous (fun z : TotalSpace Unit (f *ᵖ F) ↦
      (⟨(unitInterval.symm z.proj.1, z.proj.2), z.snd⟩ :
        TotalSpace Unit (f *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
    exact ((unitInterval.continuous_symm.comp (Pullback.continuous_proj Unit F f).fst).prodMk
      (Pullback.continuous_proj Unit F f).snd).prodMk (Pullback.continuous_lift Unit F f)
  have hforward := (Pullback.continuous_lift Unit F f).comp
    (H.iso.continuous_total.comp hrevE)
  have hbackward := (Pullback.continuous_lift Unit E f).comp
    (H.iso.continuous_symm.comp hrevF)
  let e : Iso (f *ᵖ E) (f *ᵖ F) :=
    { linearEquiv := fun x ↦ H.iso.linearEquiv (unitInterval.symm x.1, x.2)
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
        exact (Pullback.continuous_proj Unit E f).prodMk
          hforward
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
        exact (Pullback.continuous_proj Unit F f).prodMk
          hbackward }
  refine ⟨{ iso := e, map_zero := ?_, map_one := ?_ }⟩
  · intro x v
    change H.iso.linearEquiv (unitInterval.symm 0, x) v = e₁.linearEquiv x v
    rw [unitInterval.symm_zero]
    exact H.map_one x v
  · intro x v
    change H.iso.linearEquiv (unitInterval.symm 1, x) v = e₀.linearEquiv x v
    rw [unitInterval.symm_one]
    exact H.map_zero x v

/-- Choose a reverse path using the time-reversal existence theorem. -/
def IsoHomotopy.symm {e₀ e₁ : Iso E F} (H : IsoHomotopy e₀ e₁) :
    IsoHomotopy e₁ e₀ :=
  H.nonempty_symm.some

/-- Homotopies with matching endpoints can be concatenated. -/
theorem IsoHomotopy.nonempty_trans {e₀ e₁ e₂ : Iso E F}
    (H : IsoHomotopy e₀ e₁) (K : IsoHomotopy e₁ e₂) :
    Nonempty (IsoHomotopy e₀ e₂) := by
  /- Use H at twice the time on the first closed half interval and K at twice
  the time minus one on the second. Their maps and inverses agree at the seam by
  the common endpoint. The finite closed pasting lemma gives joint continuity. -/
  classical
  let f : I × X → X := Prod.snd
  -- Clamp both affine time changes to the unit interval, obtaining global continuous maps.
  let a : C(I, I) := ⟨fun t ↦ Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)), by fun_prop⟩
  let b : C(I, I) := ⟨fun t ↦ Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1), by fun_prop⟩
  have ha (t : I) (ht : (t : ℝ) = 1 / 2) : a t = 1 := by
    apply _root_.projIcc_eq_one.mpr
    linarith
  have hb (t : I) (ht : (t : ℝ) = 1 / 2) : b t = 0 := by
    apply _root_.projIcc_eq_zero.mpr
    linarith
  have hinE (c : C(I, I)) : Continuous (fun z : TotalSpace Unit (f *ᵖ E) ↦
      (⟨(c z.proj.1, z.proj.2), z.snd⟩ : TotalSpace Unit (f *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    exact ((c.continuous.comp (Pullback.continuous_proj Unit E f).fst).prodMk
      (Pullback.continuous_proj Unit E f).snd).prodMk (Pullback.continuous_lift Unit E f)
  have hinF (c : C(I, I)) : Continuous (fun z : TotalSpace Unit (f *ᵖ F) ↦
      (⟨(c z.proj.1, z.proj.2), z.snd⟩ : TotalSpace Unit (f *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
    exact ((c.continuous.comp (Pullback.continuous_proj Unit F f).fst).prodMk
      (Pullback.continuous_proj Unit F f).snd).prodMk (Pullback.continuous_lift Unit F f)
  let reparam (c : C(I, I)) (L : Iso (f *ᵖ E) (f *ᵖ F)) : Iso (f *ᵖ E) (f *ᵖ F) :=
    { linearEquiv := fun x ↦ L.linearEquiv (c x.1, x.2)
      continuous_total := by
        have hc := (Pullback.continuous_lift Unit F f).comp (L.continuous_total.comp (hinE c))
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
        exact (Pullback.continuous_proj Unit E f).prodMk hc
      continuous_symm := by
        have hc := (Pullback.continuous_lift Unit E f).comp (L.continuous_symm.comp (hinF c))
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
        exact (Pullback.continuous_proj Unit F f).prodMk hc }
  let A := reparam a H.iso
  let B := reparam b K.iso
  have hseam (t : I) (ht : (t : ℝ) = 1 / 2) (x : X) :
      A.linearEquiv (t, x) = B.linearEquiv (t, x) := by
    change H.iso.linearEquiv (a t, x) = K.iso.linearEquiv (b t, x)
    rw [ha t ht, hb t ht]
    ext v
    exact (H.map_one x v).trans (K.map_zero x v).symm
  -- Both the maps and their inverses agree at the seam; paste on the two closed halves.
  let e : Iso (f *ᵖ E) (f *ᵖ F) :=
    { linearEquiv := fun x ↦ if (x.1 : ℝ) ≤ 1 / 2 then A.linearEquiv x else B.linearEquiv x
      continuous_total := by
        have hc := continuous_if_le
          (continuous_subtype_val.comp (Pullback.continuous_proj Unit E f).fst) continuous_const
          A.continuous_total.continuousOn B.continuous_total.continuousOn
          (fun z hz ↦ congrArg (fun l : E z.proj.2 ≃ₗ[ℂ] F z.proj.2 ↦
            (⟨z.proj, l z.snd⟩ : TotalSpace Unit (f *ᵖ F))) (hseam z.proj.1 hz z.proj.2))
        apply hc.congr
        intro z
        dsimp only [Function.comp_apply]
        split_ifs <;> rfl
      continuous_symm := by
        have hc := continuous_if_le
          (continuous_subtype_val.comp (Pullback.continuous_proj Unit F f).fst) continuous_const
          A.continuous_symm.continuousOn B.continuous_symm.continuousOn
          (fun z hz ↦ congrArg (fun l : E z.proj.2 ≃ₗ[ℂ] F z.proj.2 ↦
            (⟨z.proj, l.symm z.snd⟩ : TotalSpace Unit (f *ᵖ E)))
              (hseam z.proj.1 hz z.proj.2))
        apply hc.congr
        intro z
        dsimp only [Function.comp_apply]
        split_ifs <;> rfl }
  refine ⟨{ iso := e, map_zero := ?_, map_one := ?_ }⟩
  · intro x v
    change (if (0 : ℝ) ≤ 1 / 2 then A.linearEquiv (0, x) else B.linearEquiv (0, x)) v = _
    rw [ite_eq_left (by norm_num)]
    have htime : a 0 = 0 := _root_.projIcc_eq_zero.mpr (by norm_num)
    change H.iso.linearEquiv (a 0, x) v = e₀.linearEquiv x v
    rw [htime]
    exact H.map_zero x v
  · intro x v
    change (if (1 : ℝ) ≤ 1 / 2 then A.linearEquiv (1, x) else B.linearEquiv (1, x)) v = _
    rw [ite_eq_right (by norm_num)]
    have htime : b 1 = 1 := _root_.projIcc_eq_one.mpr (by norm_num)
    change K.iso.linearEquiv (b 1, x) v = e₂.linearEquiv x v
    rw [htime]
    exact K.map_one x v

/-- Choose a path with the endpoints supplied by the concatenation theorem. -/
def IsoHomotopy.trans {e₀ e₁ e₂ : Iso E F}
    (H : IsoHomotopy e₀ e₁) (K : IsoHomotopy e₁ e₂) : IsoHomotopy e₀ e₂ :=
  (H.nonempty_trans K).some

/-- Pointwise inverse preserves joint continuity and endpoints. -/
theorem IsoHomotopy.nonempty_inverse {e₀ e₁ : Iso E F} (H : IsoHomotopy e₀ e₁) :
    Nonempty (IsoHomotopy e₀.symm e₁.symm) := by
  /- Use the inverse of the given cylinder isomorphism. Its continuity is already
  part of the structure; invert the two endpoint equalities to identify its slices. -/
  refine ⟨{ iso := H.iso.symm, map_zero := ?_, map_one := ?_ }⟩
  · intro x v
    change (H.iso.linearEquiv (0, x)).symm v = (e₀.linearEquiv x).symm v
    apply (H.iso.linearEquiv (0, x)).injective
    calc
      _ = v := (H.iso.linearEquiv (0, x)).apply_symm_apply v
      _ = _ := ((H.map_zero x ((e₀.linearEquiv x).symm v)).trans
        ((e₀.linearEquiv x).apply_symm_apply v)).symm
  · intro x v
    change (H.iso.linearEquiv (1, x)).symm v = (e₁.linearEquiv x).symm v
    apply (H.iso.linearEquiv (1, x)).injective
    calc
      _ = v := (H.iso.linearEquiv (1, x)).apply_symm_apply v
      _ = _ := ((H.map_one x ((e₁.linearEquiv x).symm v)).trans
        ((e₁.linearEquiv x).apply_symm_apply v)).symm

/-- Composition of two isomorphism homotopies is again a homotopy. -/
theorem IsoHomotopy.nonempty_comp {e₀ e₁ : Iso E F} {f₀ f₁ : Iso F G}
    (H : IsoHomotopy e₀ e₁) (K : IsoHomotopy f₀ f₁) :
    Nonempty (IsoHomotopy (e₀.trans f₀) (e₁.trans f₁)) := by
  /- Compose the two cylinder isomorphisms. At each endpoint the respective
  equations identify the fiber map with the corresponding composite. This does
  not require compactness or a choice of norm on the bundles. -/
  refine ⟨{ iso := H.iso.trans K.iso, map_zero := ?_, map_one := ?_ }⟩
  · intro x v
    exact (K.map_zero x _).trans (congrArg (f₀.linearEquiv x) (H.map_zero x v))
  · intro x v
    exact (K.map_one x _).trans (congrArg (f₁.linearEquiv x) (H.map_one x v))

/-- Restriction of a homotopy has the restricted endpoints. -/
theorem IsoHomotopy.nonempty_restrict {e₀ e₁ : Iso E F}
    (H : IsoHomotopy e₀ e₁) (A : Set X) :
    Nonempty (IsoHomotopy (e₀.restrict A) (e₁.restrict A)) := by
  /- Pull the cylinder maps back along (t,a) ↦ (t,a.val). Identify the iterated
  pullbacks by the vector-preserving comparisons. The endpoint equations restrict to A. -/
  let f : I × X → X := Prod.snd
  let a : A → X := Subtype.val
  let fA : I × A → A := Prod.snd
  -- Insert the restricted cylinder into the original cylinder without changing vectors.
  have hE : Continuous (fun z : TotalSpace Unit (fA *ᵖ (a *ᵖ E)) ↦
      (⟨(z.proj.1, z.proj.2.val), z.snd⟩ : TotalSpace Unit (f *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    exact ((Pullback.continuous_proj Unit (a *ᵖ E) fA).fst.prodMk
      (continuous_subtype_val.comp (Pullback.continuous_proj Unit (a *ᵖ E) fA).snd)).prodMk
      ((Pullback.continuous_lift Unit E a).comp (Pullback.continuous_lift Unit (a *ᵖ E) fA))
  have hF : Continuous (fun z : TotalSpace Unit (fA *ᵖ (a *ᵖ F)) ↦
      (⟨(z.proj.1, z.proj.2.val), z.snd⟩ : TotalSpace Unit (f *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
    exact ((Pullback.continuous_proj Unit (a *ᵖ F) fA).fst.prodMk
      (continuous_subtype_val.comp (Pullback.continuous_proj Unit (a *ᵖ F) fA).snd)).prodMk
      ((Pullback.continuous_lift Unit F a).comp (Pullback.continuous_lift Unit (a *ᵖ F) fA))
  let e : Iso (fA *ᵖ (a *ᵖ E)) (fA *ᵖ (a *ᵖ F)) :=
    { linearEquiv := fun x ↦ H.iso.linearEquiv (x.1, x.2.val)
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (a *ᵖ F) fA).continuous_iff]
        apply (Pullback.continuous_proj Unit (a *ᵖ E) fA).prodMk
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F a).continuous_iff]
        exact (Pullback.continuous_proj Unit (a *ᵖ E) fA).snd.prodMk
          ((Pullback.continuous_lift Unit F f).comp (H.iso.continuous_total.comp hE))
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (a *ᵖ E) fA).continuous_iff]
        apply (Pullback.continuous_proj Unit (a *ᵖ F) fA).prodMk
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E a).continuous_iff]
        exact (Pullback.continuous_proj Unit (a *ᵖ F) fA).snd.prodMk
          ((Pullback.continuous_lift Unit E f).comp (H.iso.continuous_symm.comp hF)) }
  exact ⟨{ iso := e
           map_zero := fun x v ↦ H.map_zero x.val v
           map_one := fun x v ↦ H.map_one x.val v }⟩

attribute [local instance] sumTopology

/-- Direct sum with a constant isomorphism preserves homotopy. -/
theorem IsoHomotopy.nonempty_sum_refl {e₀ e₁ : Iso E F}
    (H : IsoHomotopy e₀ e₁) (g : Iso G G) :
    Nonempty (IsoHomotopy (e₀.sum g) (e₁.sum g)) := by
  /- Take the direct sum of the cylinder path with the constant pullback of g.
  Pullback and sum have the same induced topology after their canonical comparison;
  endpoint evaluation gives precisely the two direct-sum isomorphisms. -/
  let f : I × X → X := Prod.snd
  -- Extract the first summand into its cylinder; the second remains in its original total space.
  have hE : Continuous (fun z : TotalSpace Unit (f *ᵖ (E ×ᵇ G)) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace Unit (f *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    exact (Pullback.continuous_proj Unit (E ×ᵇ G) f).prodMk
      ((continuous_sum_fst (E := E) (F := G)).comp
        (Pullback.continuous_lift Unit (E ×ᵇ G) f))
  have hF : Continuous (fun z : TotalSpace Unit (f *ᵖ (F ×ᵇ G)) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace Unit (f *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
    exact (Pullback.continuous_proj Unit (F ×ᵇ G) f).prodMk
      ((continuous_sum_fst (E := F) (F := G)).comp
        (Pullback.continuous_lift Unit (F ×ᵇ G) f))
  let e : Iso (f *ᵖ (E ×ᵇ G)) (f *ᵖ (F ×ᵇ G)) :=
    { linearEquiv := fun x ↦ (H.iso.linearEquiv x).prodCongr (g.linearEquiv x.2)
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (F ×ᵇ G) f).continuous_iff]
        apply (Pullback.continuous_proj Unit (E ×ᵇ G) f).prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit F f).comp
          (H.iso.continuous_total.comp hE)).prodMk
          (g.continuous_total.comp ((continuous_sum_snd (E := E) (F := G)).comp
            (Pullback.continuous_lift Unit (E ×ᵇ G) f)))
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (E ×ᵇ G) f).continuous_iff]
        apply (Pullback.continuous_proj Unit (F ×ᵇ G) f).prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit E f).comp
          (H.iso.continuous_symm.comp hF)).prodMk
          (g.continuous_symm.comp ((continuous_sum_snd (E := F) (F := G)).comp
            (Pullback.continuous_lift Unit (F ×ᵇ G) f))) }
  refine ⟨{ iso := e, map_zero := ?_, map_one := ?_ }⟩
  · intro x v
    exact Prod.ext (H.map_zero x v.1) rfl
  · intro x v
    exact Prod.ext (H.map_one x v.1) rfl

end AtiyahSinger.ComplexBundle
