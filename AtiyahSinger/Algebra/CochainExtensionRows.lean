/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Tactic

/-!
# Exact rows under native extension by zero

Public module ID: M0004.

Extending nonnegative cochain complexes upward by a fixed natural degree
preserves degreewise exactness and injectivity. In supported degrees the
proof uses the actual `extendXIso` and `extendMap` formulas; below the
extension degree it uses the native zero objects. These adapters retain
both the original complexes and their original maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex

universe u

variable (R : Type) [CommRing R]

/-- Native extension by zero preserves degreewise exact pairs of cochain maps. -/
theorem exact_extendMap_f
    {C D E : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) (g : D ⟶ E)
    (r : ℕ) (h : ∀ q, Function.Exact (f.f q) (g.f q)) (n : ℕ) :
    Function.Exact
      ((extendMap f (ComplexShape.embeddingUp'Add (1 : ℕ) r)).f n)
      ((extendMap g (ComplexShape.embeddingUp'Add (1 : ℕ) r)).f n) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  change Function.Exact ((extendMap f e).f n) ((extendMap g e).f n)
  by_cases hn : r ≤ n
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    let I := C.extendXIso e (i := q) (i' := q + r) rfl
    let J := D.extendXIso e (i := q) (i' := q + r) rfl
    let K := E.extendXIso e (i := q) (i' := q + r) rfl
    -- The same degreewise maps are conjugated by the canonical extension isomorphisms.
    have hf (x : (C.extend e).X (q + r)) :
        J.hom ((extendMap f e).f (q + r) x) = f.f q (I.hom x) := by
      rw [extendMap_f f e (i := q) (i' := q + r) rfl]
      change J.hom (J.inv (f.f q (I.hom x))) = _
      exact J.inv_hom_id_apply _
    have hg (x : (D.extend e).X (q + r)) :
        K.hom ((extendMap g e).f (q + r) x) = g.f q (J.hom x) := by
      rw [extendMap_f g e (i := q) (i' := q + r) rfl]
      change K.hom (K.inv (g.f q (J.hom x))) = _
      exact K.inv_hom_id_apply _
    intro x
    constructor
    · intro hx
      have hclosed : g.f q (J.hom x) = 0 := by
        rw [← hg, hx, map_zero]
      obtain ⟨a, ha⟩ := (h q _).mp hclosed
      refine ⟨I.inv a, ?_⟩
      apply J.toLinearEquiv.injective
      change J.hom _ = J.hom _
      rw [hf, I.inv_hom_id_apply]
      exact ha
    · rintro ⟨a, rfl⟩
      apply K.toLinearEquiv.injective
      change K.hom _ = K.hom _
      rw [hg, hf, map_zero]
      exact (h q _).mpr ⟨I.hom a, rfl⟩
  · -- The middle object is the actual zero object below the extension degree.
    have hzero := D.isZero_extend_X e n (by
      intro q hq
      change q + r = n at hq
      omega)
    have : Subsingleton ((D.extend e).X n) := ModuleCat.subsingleton_of_isZero hzero
    intro x
    constructor
    · intro _
      exact ⟨0, Subsingleton.elim _ _⟩
    · intro _
      exact (congrArg ((extendMap g e).f n) (Subsingleton.elim x 0)).trans (map_zero _)

/-- Native extension by zero preserves a degreewise injective cochain map. -/
theorem injective_extendMap_f
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D)
    (r : ℕ) (h : ∀ q, Function.Injective (f.f q)) (n : ℕ) :
    Function.Injective ((extendMap f (ComplexShape.embeddingUp'Add (1 : ℕ) r)).f n) := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  change Function.Injective ((extendMap f e).f n)
  by_cases hn : r ≤ n
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    let I := C.extendXIso e (i := q) (i' := q + r) rfl
    let J := D.extendXIso e (i := q) (i' := q + r) rfl
    have hf (x : (C.extend e).X (q + r)) :
        J.hom ((extendMap f e).f (q + r) x) = f.f q (I.hom x) := by
      rw [extendMap_f f e (i := q) (i' := q + r) rfl]
      change J.hom (J.inv (f.f q (I.hom x))) = _
      exact J.inv_hom_id_apply _
    intro x y hxy
    apply I.toLinearEquiv.injective
    change I.hom _ = I.hom _
    apply h q
    exact (hf x).symm.trans ((congrArg J.hom hxy).trans (hf y))
  · -- Below the extension degree, every source element is the same zero element.
    have hzero := C.isZero_extend_X e n (by
      intro q hq
      change q + r = n at hq
      omega)
    have : Subsingleton ((C.extend e).X n) := ModuleCat.subsingleton_of_isZero hzero
    exact fun _ _ _ ↦ Subsingleton.elim _ _

end AtiyahSinger
