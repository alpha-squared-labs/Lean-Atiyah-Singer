/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopyPullback
public import AtiyahSinger.Topology.EquivariantOpenBundleGluing

/-!
# Extend a bundle-isomorphism homotopy fixed on an open overlap

Public module ID: M1580.

A homotopy on one member of an open cover extends by the original global
isomorphism on the other member when it is fixed throughout their overlap.
The construction glues the actual cylinder isomorphisms and retains all
time slices, rather than only their endpoint homotopy classes.

This is the open gluing step used to extend a relative cotangent homotopy
across exterior zero covectors while keeping one compact control.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace

attribute [local instance] isFiniteRank_pullback

variable {X : Type*} [TopologicalSpace X]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Glue a homotopy to a constant exterior homotopy on a covering open set. -/
theorem IsoHomotopy.exists_extension_of_fixed_overlap
    (U V : Opens X) (hcover : (U : Set X) ∪ (V : Set X) = Set.univ)
    (a : Iso E F)
    {aU bU : Iso ((Subtype.val : U → X) *ᵖ E) ((Subtype.val : U → X) *ᵖ F)}
    (H : IsoHomotopy aU bU)
    (haU : ∀ (x : U) (v : E x.val), aU.linearEquiv x v = a.linearEquiv x.val v)
    (hfix : ∀ (t : unitInterval) (x : U), x.val ∈ V → ∀ v : E x.val,
      H.iso.linearEquiv (t, x) v = a.linearEquiv x.val v) :
    ∃ b : Iso E F, ∃ G : IsoHomotopy a b,
      (∀ (t : unitInterval) (x : U) (v : E x.val),
        G.iso.linearEquiv (t, x.val) v = H.iso.linearEquiv (t, x) v) ∧
      (∀ (t : unitInterval) (x : V) (v : E x.val),
        G.iso.linearEquiv (t, x.val) v = a.linearEquiv x.val v) := by
  classical
  let T := unitInterval × X
  let p : C(T, X) := ⟨Prod.snd, continuous_snd⟩
  let ET := (p : T → X) *ᵖ E
  let FT := (p : T → X) *ᵖ F
  let i : C(U, X) := ContinuousMap.subtypeVal (U : Set X)
  let EU := (i : U → X) *ᵖ E
  let FU := (i : U → X) *ᵖ F
  let q : C(unitInterval × U, U) := ⟨Prod.snd, continuous_snd⟩
  let UT : Opens T := ⟨Prod.snd ⁻¹' (U : Set X), U.isOpen.preimage continuous_snd⟩
  let VT : Opens T := ⟨Prod.snd ⁻¹' (V : Set X), V.isOpen.preimage continuous_snd⟩
  let j : C(UT, T) := ContinuousMap.subtypeVal (UT : Set T)
  let f : C(UT, unitInterval × U) :=
    ⟨fun z ↦ (z.val.1, ⟨z.val.2, z.property⟩),
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)⟩
  -- Canonical reassociation identifies both cylinder restrictions with the same original fiber.
  let eE : Iso ((j : UT → T) *ᵖ ET) ((f : UT → unitInterval × U) *ᵖ
      ((q : unitInterval × U → U) *ᵖ EU)) :=
    (pullbackCompIso (E := E) p j).trans
      ((pullbackCompIso (E := EU) q f).trans
        (pullbackCompIso (E := E) i (q.comp f))).symm
  let eF : Iso ((j : UT → T) *ᵖ FT) ((f : UT → unitInterval × U) *ᵖ
      ((q : unitInterval × U → U) *ᵖ FU)) :=
    (pullbackCompIso (E := F) p j).trans
      ((pullbackCompIso (E := FU) q f).trans
        (pullbackCompIso (E := F) i (q.comp f))).symm
  let u : RelativeTriple ET FT (UT : Set T) := eE.trans ((H.iso.pullback f).trans eF.symm)
  let v : RelativeTriple ET FT (VT : Set T) := (a.pullback p).restrict (VT : Set T)
  have hu (z : UT) (w : E z.val.2) :
      u.linearEquiv z w = H.iso.linearEquiv (f z) w := by
    have heE : eE.linearEquiv z w = w := by
      let B := (pullbackCompIso (E := EU) q f).trans
        (pullbackCompIso (E := E) i (q.comp f))
      apply (B.linearEquiv z).injective
      change B.linearEquiv z ((B.linearEquiv z).symm
        ((pullbackCompIso (E := E) p j).linearEquiv z w)) = B.linearEquiv z w
      rw [LinearEquiv.apply_symm_apply]
      change (pullbackCompIso (E := E) p j).linearEquiv z w =
        (pullbackCompIso (E := E) i (q.comp f)).linearEquiv z
          ((pullbackCompIso (E := EU) q f).linearEquiv z w)
      rw [pullbackCompIso_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    have heF (v : F z.val.2) : eF.linearEquiv z v = v := by
      let B := (pullbackCompIso (E := FU) q f).trans
        (pullbackCompIso (E := F) i (q.comp f))
      apply (B.linearEquiv z).injective
      change B.linearEquiv z ((B.linearEquiv z).symm
        ((pullbackCompIso (E := F) p j).linearEquiv z v)) = B.linearEquiv z v
      rw [LinearEquiv.apply_symm_apply]
      change (pullbackCompIso (E := F) p j).linearEquiv z v =
        (pullbackCompIso (E := F) i (q.comp f)).linearEquiv z
          ((pullbackCompIso (E := FU) q f).linearEquiv z v)
      rw [pullbackCompIso_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    change (eF.linearEquiv z).symm ((H.iso.linearEquiv (f z)) (eE.linearEquiv z w)) = _
    rw [heE]
    apply (eF.linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, heF]
  have hv (z : VT) (w : E z.val.2) : v.linearEquiv z w = a.linearEquiv z.val.2 w := by
    rfl
  have hcoverT : (UT : Set T) ∪ (VT : Set T) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : z.2 ∈ (U : Set X) ∪ (V : Set X) := by rw [hcover]; trivial
    exact hz
  have hagree (z : T) (hzU : z ∈ UT) (hzV : z ∈ VT) :
      u.linearEquiv ⟨z, hzU⟩ = v.linearEquiv ⟨z, hzV⟩ := by
    apply LinearEquiv.ext
    intro w
    exact (hu ⟨z, hzU⟩ w).trans ((hfix z.1 ⟨z.2, hzU⟩ hzV w).trans
      (hv ⟨z, hzV⟩ w).symm)
  -- The trivial one-point action reuses actual open gluing for the whole cylinder.
  let : MulAction PUnit.{1} T :=
    { smul _ x := x
      one_smul _ := rfl
      mul_smul _ _ _ := rfl }
  let : ContinuousSMul PUnit.{1} T := ⟨continuous_snd⟩
  let ρE : EquivariantStructure PUnit.{1} ET :=
    { linearMap _ _ := LinearMap.id
      one_map _ _ := rfl
      mul_map _ _ _ _ := rfl
      continuous_action := continuous_snd }
  let ρF : EquivariantStructure PUnit.{1} FT :=
    { linearMap _ _ := LinearMap.id
      one_map _ _ := rfl
      mul_map _ _ _ _ := rfl
      continuous_action := continuous_snd }
  obtain ⟨J, _, hJU, hJV⟩ := Iso.exists_equivariant_gluing ρE ρF
    (UT : Set T) (VT : Set T) UT.isOpen VT.isOpen hcoverT
    (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) u v hagree
    (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
  -- Evaluate this very cylinder at one; no separate endpoint isomorphism is chosen.
  have hinE : Continuous (fun z : TotalSpace Unit E ↦
      (⟨((1 : unitInterval), z.proj), z.snd⟩ : TotalSpace Unit ET)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact (continuous_const.prodMk continuous_proj).prodMk continuous_id
  have hinF : Continuous (fun z : TotalSpace Unit F ↦
      (⟨((1 : unitInterval), z.proj), z.snd⟩ : TotalSpace Unit FT)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
    exact (continuous_const.prodMk continuous_proj).prodMk continuous_id
  let b : Iso E F :=
    { linearEquiv x := J.linearEquiv (1, x)
      continuous_total := (Pullback.continuous_lift Unit F p).comp
        (J.continuous_total.comp hinE)
      continuous_symm := (Pullback.continuous_lift Unit E p).comp
        (J.continuous_symm.comp hinF) }
  have hzero (x : X) (w : E x) : J.linearEquiv (0, x) w = a.linearEquiv x w := by
    by_cases hx : x ∈ U
    · rw [hJU (0, x) hx]
      exact (hu ⟨(0, x), hx⟩ w).trans
        ((H.map_zero ⟨x, hx⟩ w).trans (haU ⟨x, hx⟩ w))
    · have hxV : x ∈ V := by
        have hm : x ∈ (U : Set X) ∪ (V : Set X) := by rw [hcover]; trivial
        exact hm.resolve_left hx
      rw [hJV (0, x) hxV]
      exact hv ⟨(0, x), hxV⟩ w
  let G : IsoHomotopy a b :=
    { iso := J
      map_zero := hzero
      map_one _ _ := rfl }
  refine ⟨b, G, ?_, ?_⟩
  · intro t x w
    change J.linearEquiv (t, x.val) w = _
    rw [hJU (t, x.val) x.property]
    exact hu ⟨(t, x.val), x.property⟩ w
  · intro t x w
    change J.linearEquiv (t, x.val) w = _
    rw [hJV (t, x.val) x.property]
    exact hv ⟨(t, x.val), x.property⟩ w

end AtiyahSinger.ComplexBundle
