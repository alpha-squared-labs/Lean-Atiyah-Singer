/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Lifting homology through a countable tower

Public module ID: M0012.

Compatible homology classes can be represented by compatible cycles when the
transition maps on bounding chains are surjective. If the preceding cycle
transitions are surjective as well, compatible boundaries have compatible
primitives. A degreewise realization therefore gives a unique homology class.
This is the elementary vanishing-obstruction case of the Milnor inverse-limit
argument, stated without assuming that homology commutes with arbitrary limits.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits

universe u

/-- Countable compatible cycles and primitives realize a unique homology class.
The two lifting hypotheses and the two separation hypotheses express the actual
limit in the relevant chain degrees. Surjectivity on preceding cycles is the
condition that removes the inverse-limit obstruction to uniqueness. -/
theorem existsUnique_homology_of_surjective_tower
    (R : Type) [CommRing R] (S : ℕ → ShortComplex (ModuleCat.{u} R))
    (f : ∀ i : ℕ, S (i + 1) ⟶ S i) (L : ShortComplex (ModuleCat.{u} R))
    (p : ∀ i : ℕ, L ⟶ S i)
    (hp : ∀ i : ℕ, p (i + 1) ≫ f i = p i)
    (hlift₁ : ∀ c : ∀ i : ℕ, (S i).X₁,
      (∀ i : ℕ, (f i).τ₁ (c (i + 1)) = c i) →
        ∃ b : L.X₁, ∀ i : ℕ, (p i).τ₁ b = c i)
    (hlift₂ : ∀ c : ∀ i : ℕ, (S i).X₂,
      (∀ i : ℕ, (f i).τ₂ (c (i + 1)) = c i) →
        ∃ b : L.X₂, ∀ i : ℕ, (p i).τ₂ b = c i)
    (hsep₂ : ∀ x y : L.X₂, (∀ i : ℕ, (p i).τ₂ x = (p i).τ₂ y) → x = y)
    (hsep₃ : ∀ x y : L.X₃, (∀ i : ℕ, (p i).τ₃ x = (p i).τ₃ y) → x = y)
    (hsurj : ∀ i : ℕ, Function.Surjective (f i).τ₁)
    (hcycle : ∀ (i : ℕ) (a : (S i).X₁), (S i).f a = 0 →
      ∃ b : (S (i + 1)).X₁, (S (i + 1)).f b = 0 ∧ (f i).τ₁ b = a)
    (z : ∀ i : ℕ, (S i).homology)
    (hz : ∀ i : ℕ, ShortComplex.homologyMap (f i) (z (i + 1)) = z i) :
    ∃! a : L.homology, ∀ i : ℕ, ShortComplex.homologyMap (p i) a = z i := by
  classical
  -- Work with the original categorical homology via its concrete cycle representatives.
  let cl (T : ShortComplex (ModuleCat.{u} R)) (x : T.X₂) (hx : T.g x = 0) :
      T.homology := T.homologyπ (T.cyclesMk x hx)
  have hclι (T : ShortComplex (ModuleCat.{u} R)) (x : T.X₂) (hx : T.g x = 0) :
      T.homologyι (cl T x hx) = T.pOpcycles x := by
    change (T.homologyπ ≫ T.homologyι) (T.cyclesMk x hx) = _
    rw [T.homology_π_ι]
    exact congrArg (fun y : T.X₂ ↦ T.pOpcycles y) (T.i_cyclesMk x hx)
  have hrep (T : ShortComplex (ModuleCat.{u} R)) (a : T.homology) :
      ∃ x : T.X₂, ∃ hx : T.g x = 0, cl T x hx = a := by
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance a
    have hc : T.g (T.iCycles c) = 0 := by
      change (T.iCycles ≫ T.g) c = 0
      rw [T.iCycles_g]
      rfl
    refine ⟨T.iCycles c, hc, ?_⟩
    apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
    rw [hclι]
    change T.pOpcycles (T.iCycles c) = (T.homologyπ ≫ T.homologyι) c
    rw [T.homology_π_ι]
    rfl
  have heq (T : ShortComplex (ModuleCat.{u} R)) (x y : T.X₂)
      (hx : T.g x = 0) (hy : T.g y = 0) :
      cl T x hx = cl T y hy ↔ ∃ b : T.X₁, T.f b = x - y := by
    rw [← ((ModuleCat.mono_iff_injective T.homologyι).mp inferInstance).eq_iff,
      hclι, hclι, T.moduleCat_pOpcycles_eq_iff]
    rfl
  have hnat {T U : ShortComplex (ModuleCat.{u} R)} (φ : T ⟶ U)
      (x : T.X₂) (hx : T.g x = 0) (hy : U.g (φ.τ₂ x) = 0) :
      ShortComplex.homologyMap φ (cl T x hx) = cl U (φ.τ₂ x) hy := by
    apply (ModuleCat.mono_iff_injective U.homologyι).mp inferInstance
    rw [hclι]
    change (ShortComplex.homologyMap φ ≫ U.homologyι) (cl T x hx) = _
    rw [ShortComplex.homologyι_naturality]
    change ShortComplex.opcyclesMap φ (T.homologyι (cl T x hx)) = _
    rw [hclι]
    change (T.pOpcycles ≫ ShortComplex.opcyclesMap φ) x = _
    rw [ShortComplex.p_opcyclesMap]
    rfl
  have hcommg {T U : ShortComplex (ModuleCat.{u} R)} (φ : T ⟶ U)
      (x : T.X₂) : U.g (φ.τ₂ x) = φ.τ₃ (T.g x) :=
    congrArg (fun a ↦ a x) φ.comm₂₃
  have hcommf {T U : ShortComplex (ModuleCat.{u} R)} (φ : T ⟶ U)
      (x : T.X₁) : U.f (φ.τ₁ x) = φ.τ₂ (T.f x) :=
    congrArg (fun a ↦ a x) φ.comm₁₂
  -- Correct each next cycle by a lifted boundary so that its chain image is exact.
  let F (i : ℕ) := {x : (S i).X₂ // ∃ hx : (S i).g x = 0, cl (S i) x hx = z i}
  have hstep (i : ℕ) (x : F i) :
      ∃ y : F (i + 1), (f i).τ₂ y.val = x.val := by
    obtain ⟨y, hy, hyz⟩ := hrep (S (i + 1)) (z (i + 1))
    have hfy : (S i).g ((f i).τ₂ y) = 0 := by rw [hcommg, hy, map_zero]
    have hclass : cl (S i) ((f i).τ₂ y) hfy = cl (S i) x.val x.property.choose := by
      rw [← hnat (f i) y hy hfy, hyz, hz i, x.property.choose_spec]
    obtain ⟨b, hb⟩ := (heq _ _ _ _ _).mp hclass
    obtain ⟨b', hb'⟩ := hsurj i b
    let y' := y - (S (i + 1)).f b'
    have hy' : (S (i + 1)).g y' = 0 := by
      simp [y', hy]
    have heq' : cl (S (i + 1)) y' hy' = z (i + 1) := by
      rw [← hyz]
      apply (heq _ _ _ _ _).mpr
      refine ⟨-b', ?_⟩
      simp [y']
    refine ⟨⟨y', hy', heq'⟩, ?_⟩
    change (f i).τ₂ (y - (S (i + 1)).f b') = x.val
    rw [map_sub, ← hcommf, hb', hb]
    abel
  obtain ⟨x₀, hx₀, hx₀z⟩ := hrep (S 0) (z 0)
  let c : ∀ i : ℕ, F i := fun i ↦ Nat.recOn i (⟨x₀, hx₀, hx₀z⟩ : F 0)
    (fun i x ↦ (hstep i x).choose)
  have hc (i : ℕ) : (f i).τ₂ (c (i + 1)).val = (c i).val :=
    (hstep i (c i)).choose_spec
  obtain ⟨a, ha⟩ := hlift₂ (fun i ↦ (c i).val) hc
  have hacycle : L.g a = 0 := by
    apply hsep₃
    intro i
    rw [← hcommg, ha, (c i).property.choose, map_zero]
  have haz (i : ℕ) : ShortComplex.homologyMap (p i) (cl L a hacycle) = z i := by
    have hpi : (S i).g ((p i).τ₂ a) = 0 := by rw [hcommg, hacycle, map_zero]
    rw [hnat (p i) a hacycle hpi]
    simpa only [ha i] using (c i).property.choose_spec
  refine ⟨cl L a hacycle, haz, ?_⟩
  -- Uniqueness requires compatible primitives, not just separately vanishing classes.
  intro b hb
  obtain ⟨v, hv, hvb⟩ := hrep L b
  have hboundary (i : ℕ) : ∃ q : (S i).X₁, (S i).f q = (p i).τ₂ (v - a) := by
    have hv' : (S i).g ((p i).τ₂ v) = 0 := by rw [hcommg, hv, map_zero]
    have ha' : (S i).g ((p i).τ₂ a) = 0 := by rw [hcommg, hacycle, map_zero]
    have hclasses : cl (S i) ((p i).τ₂ v) hv' = cl (S i) ((p i).τ₂ a) ha' := by
      rw [← hnat (p i) v hv hv', ← hnat (p i) a hacycle ha', hvb, hb, haz]
    simpa only [map_sub] using (heq _ _ _ _ _).mp hclasses
  let G (i : ℕ) := {q : (S i).X₁ // (S i).f q = (p i).τ₂ (v - a)}
  -- The desired compatibility of the projected difference follows from that of c and p(v).
  have hdcompat (i : ℕ) :
      (f i).τ₂ ((p (i + 1)).τ₂ (v - a)) = (p i).τ₂ (v - a) := by
    exact congrArg (fun φ ↦ φ.τ₂ (v - a)) (hp i)
  have hstepG (i : ℕ) (q : G i) :
      ∃ q' : G (i + 1), (f i).τ₁ q'.val = q.val := by
    obtain ⟨b, hb⟩ := hboundary (i + 1)
    have hkernel : (S i).f ((f i).τ₁ b - q.val) = 0 := by
      rw [map_sub, hcommf, hb, hdcompat, q.property, sub_self]
    obtain ⟨w, hw, hw'⟩ := hcycle i ((f i).τ₁ b - q.val) hkernel
    refine ⟨⟨b - w, ?_⟩, ?_⟩
    · rw [map_sub, hb, hw, sub_zero]
    · rw [map_sub, hw']
      abel
  let q : ∀ i : ℕ, G i := fun i ↦ Nat.recOn i
    (⟨(hboundary 0).choose, (hboundary 0).choose_spec⟩ : G 0)
    (fun i q ↦ (hstepG i q).choose)
  have hq (i : ℕ) : (f i).τ₁ (q (i + 1)).val = (q i).val :=
    (hstepG i (q i)).choose_spec
  obtain ⟨w, hw⟩ := hlift₁ (fun i ↦ (q i).val) hq
  have hwb : L.f w = v - a := by
    apply hsep₂
    intro i
    rw [← hcommf, hw]
    exact (q i).property
  rw [← hvb]
  exact (heq _ _ _ _ _).mpr ⟨w, hwb⟩

end AtiyahSinger
