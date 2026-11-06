/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopy
public import AtiyahSinger.Topology.BundleSum

/-!
# Rotation between the identity and a signed interchange

Public module ID: M1582.

D07/K02. Karoubi II.2.14 uses the elementary rotation on a pair of isomorphic
bundles. Three elementary shears give the same signed interchange, without
choosing metrics or replacing the original total-space topologies. The path
is jointly continuous and every intermediate map is invertible.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

attribute [local instance] sumTopology isFiniteRank_sum

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

/-- An isomorphism gives a signed interchange homotopic to the identity on the sum. -/
theorem Iso.exists_signed_swap_homotopy (a : Iso E F) :
    ∃ b : Iso (E ×ᵇ F) (E ×ᵇ F),
      (∀ x v, b.linearEquiv x v =
        (-(a.linearEquiv x).symm v.2, a.linearEquiv x v.1)) ∧
      Nonempty (IsoHomotopy (Iso.refl (E ×ᵇ F)) b) := by
  let S := E ×ᵇ F
  let f : I × X → X := Prod.snd
  let T := TotalSpace Unit (f *ᵖ S)
  -- Pull back to the cylinder total space to use continuity of fiberwise operations.
  let p : C(T, X) := ⟨fun z ↦ z.proj.2, (Pullback.continuous_proj Unit S f).snd⟩
  let : IsFiniteRank ((p : T → X) *ᵖ S) := isFiniteRank_pullback p
  let shearMap (N : Hom S S) (c : ℂ) (x : X) : S x →ₗ[ℂ] S x :=
    LinearMap.id + c • N.linearMap x
  have hsum (N : Hom S S) (c : C(I × X, ℂ)) :
      Continuous (fun z : T ↦ (⟨z.proj, shearMap N (c z.proj) z.proj.2 z.snd⟩ :
        TotalSpace Unit (f *ᵖ S))) := by
    have hi : Continuous (fun z : T ↦
        (⟨z, z.snd⟩ : TotalSpace Unit ((p : T → X) *ᵖ S))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit S p).continuous_iff]
      exact continuous_id.prodMk (Pullback.continuous_lift Unit S f)
    have hN : Continuous (fun z : T ↦
        (⟨z, N.linearMap z.proj.2 z.snd⟩ : TotalSpace Unit ((p : T → X) *ᵖ S))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit S p).continuous_iff]
      exact continuous_id.prodMk (N.continuous_total.comp
        (Pullback.continuous_lift Unit S f))
    let d : C(T, ℂ) := ⟨fun z ↦ c z.proj,
      c.continuous.comp (Pullback.continuous_proj Unit S f)⟩
    have hadd := continuous_add_section ((p : T → X) *ᵖ S) _ _ hi
      (continuous_smul_section ((p : T → X) *ᵖ S) d _ hN)
    rw [(inducing_pullbackTotalSpaceEmbedding Unit S f).continuous_iff]
    exact (Pullback.continuous_proj Unit S f).prodMk
      ((Pullback.continuous_lift Unit S p).comp hadd)
  -- A square-zero bundle map yields an invertible shear, with the opposite shear as inverse.
  let shear (N : Hom S S) (hN : ∀ x v, N.linearMap x (N.linearMap x v) = 0)
      (c : C(I × X, ℂ)) : Iso (f *ᵖ S) (f *ᵖ S) :=
    { linearEquiv := fun x ↦
        { toLinearMap := shearMap N (c x) x.2
          invFun := shearMap N (-c x) x.2
          left_inv := by
            intro v
            change S x.2 at v
            change v + c x • N.linearMap x.2 v +
              (-c x) • N.linearMap x.2 (v + c x • N.linearMap x.2 v) = v
            simp [map_add, hN]
            abel
          right_inv := by
            intro v
            change S x.2 at v
            change v + (-c x) • N.linearMap x.2 v +
              c x • N.linearMap x.2 (v + (-c x) • N.linearMap x.2 v) = v
            simp [map_add, hN] }
      continuous_total := hsum N c
      continuous_symm := hsum N (-c) }
  let upper : Hom S S := sumInl.comp (a.symm.toHom.comp sumSnd)
  let lower : Hom S S := sumInr.comp (a.toHom.comp sumFst)
  have hu : ∀ x v, upper.linearMap x (upper.linearMap x v) = 0 := by
    intro x v
    change ((a.linearEquiv x).symm 0, 0) = 0
    simp
  have hl : ∀ x v, lower.linearMap x (lower.linearMap x v) = 0 := by
    intro x v
    change (0, a.linearEquiv x 0) = 0
    simp
  let time : C(I × X, ℂ) := ⟨fun x ↦ ((x.1 : ℝ) : ℂ), by fun_prop⟩
  let U := shear upper hu (-time)
  let L := shear lower hl time
  have hU (t : I) (x : X) (v : S x) : U.linearEquiv (t, x) v =
      (v.1 - ((t : ℝ) : ℂ) • (a.linearEquiv x).symm v.2, v.2) := by
    change (v.1 + (-((t : ℝ) : ℂ)) • (a.linearEquiv x).symm v.2,
      v.2 + (-((t : ℝ) : ℂ)) • 0) = _
    simp [sub_eq_add_neg]
  have hL (t : I) (x : X) (v : S x) : L.linearEquiv (t, x) v =
      (v.1, v.2 + ((t : ℝ) : ℂ) • a.linearEquiv x v.1) := by
    change (v.1 + ((t : ℝ) : ℂ) • 0,
      v.2 + ((t : ℝ) : ℂ) • a.linearEquiv x v.1) = _
    simp
  let path := (U.trans L).trans U
  -- Extract the terminal map on the original sum, with both continuity directions retained.
  have hin : Continuous (fun z : TotalSpace Unit S ↦
      (⟨((1 : I), z.proj), z.snd⟩ : TotalSpace Unit (f *ᵖ S))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit S f).continuous_iff]
    exact (continuous_const.prodMk (continuous_proj (E := S))).prodMk continuous_id
  let b : Iso S S :=
    { linearEquiv := fun x ↦ path.linearEquiv (1, x)
      continuous_total := (Pullback.continuous_lift Unit S f).comp
        (path.continuous_total.comp hin)
      continuous_symm := (Pullback.continuous_lift Unit S f).comp
        (path.continuous_symm.comp hin) }
  refine ⟨b, ?_, ⟨{ iso := path, map_zero := ?_, map_one := fun _ _ ↦ rfl }⟩⟩
  · intro x v
    -- U₁ L₁ U₁ sends (v,w) to (-a⁻¹w,av), using the original inverse identities.
    change U.linearEquiv (1, x) (L.linearEquiv (1, x) (U.linearEquiv (1, x) v)) = _
    erw [hU, hL, hU]
    apply Prod.ext <;> simp [map_sub]
  · intro x v
    -- All three shears are the identity at time zero.
    change U.linearEquiv (0, x) (L.linearEquiv (0, x) (U.linearEquiv (0, x) v)) = v
    erw [hU, hL, hU]
    simp only [Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul, sub_zero, add_zero]
    rfl

end AtiyahSinger.ComplexBundle
