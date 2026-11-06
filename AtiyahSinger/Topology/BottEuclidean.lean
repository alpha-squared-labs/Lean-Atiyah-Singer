/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportProductLaws
public import AtiyahSinger.Topology.GeometricBott
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Bott periodicity in finite complex coordinates

Public module ID: M1565.

K03 and the product part of D10. The class on `Fin n → ℂ` is the ordered external
product of the existing multiplication-by-z line class, with the positive rank-one
class at n = 0. Coordinate assembly uses mathlib's actual `Fin.appendHomeomorph`.
The resulting periodicity equivalence has this external product as its forward map.

Sources: SG I.9.26 and Appendix C.2--C.6; Karoubi III.1.2--1.4. Finite iteration,
block multiplicativity and coordinate permutation invariance follow from line
periodicity and degree-zero external-product coherence. The full even-to-odd
exterior-symbol comparison is proved in `ExteriorBottComparison`. Integer
normalization here comes from the point rank through the prescribed product
equivalence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Append one complex coordinate, keeping the previous coordinates in their original order. -/
def complexFinSuccHomeomorph (n : ℕ) :
    ((Fin n → ℂ) × ℂ) ≃ₜ (Fin (n + 1) → ℂ) :=
  ((Homeomorph.refl (Fin n → ℂ)).prodCongr (Homeomorph.funUnique (Fin 1) ℂ).symm).trans
    (Fin.appendHomeomorph n 1)

/-- The finite external power of the specified line class, including the rank-one zero power. -/
def bottEuclideanClass : (n : ℕ) → CompactSupportKZero (Fin n → ℂ)
  | 0 => compactSupportKZeroHomeomorph
      (Homeomorph.homeomorphOfUnique PUnit.{1} (Fin 0 → ℂ)) compactSupportKZeroPointOne
  | n + 1 => compactSupportKZeroHomeomorph (complexFinSuccHomeomorph n)
      (compactSupportKZeroExternalProduct (bottEuclideanClass n) bottLineClass)

/-- External product with the actual finite power of the multiplication-by-z class. -/
def bottEuclideanExternalProduct {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] (n : ℕ) :
    CompactSupportKZero X →+ CompactSupportKZero (X × (Fin n → ℂ)) :=
  compactSupportKZeroExternalProduct.flip (bottEuclideanClass n)

/-- Finite-dimensional complex Bott periodicity for the prescribed external-product map. -/
theorem bottEuclideanExternalProduct_bijective (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] (n : ℕ) :
    Function.Bijective (bottEuclideanExternalProduct (X := X) n) := by
  /- Stage 1: for n = 0, the class is the transported positive point unit.
  Product naturality and the right unit law identify the asserted map with
  transport along the inverse of X×ℂ⁰→X. In particular the zero-dimensional
  case is a genuine equivalence, including when X is empty.
  Stage 2: assume the result for n. Compose the prescribed n-dimensional
  product with bottLineEquiv on X×ℂⁿ. Reassociate (X×ℂⁿ)×ℂ to X×(ℂⁿ×ℂ)
  using Homeomorph.prodAssoc, then append the final coordinate using exactly
  complexFinSuccHomeomorph n. Each map is bijective.
  Stage 3: the product associativity and homeomorphism naturality theorems
  identify this composite with the displayed (n+1)-dimensional product, since
  bottEuclideanClass uses those same coordinate and external-product maps.
  Thus induction proves bijectivity of the specified map, not just existence
  of an abstract isomorphism. All intermediate bases are LCH; no compactness,
  connectedness, nonemptiness, or CW hypothesis is imposed on X. -/
  have hid (a : CompactSupportKZero X) :
      compactSupportKZeroHomeomorph (Homeomorph.refl X) a = a := by
    change compactSupportKZeroPullback (ContinuousMap.id X) isProperMap_id a = a
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  induction n with
  | zero =>
    -- The zero-fold class is the original point unit transported to the empty coordinate space.
    let e₀ := Homeomorph.homeomorphOfUnique PUnit.{1} (Fin 0 → ℂ)
    let u := compactSupportKZeroHomeomorphEquiv (Homeomorph.prodUnique X PUnit.{1})
    let v := compactSupportKZeroHomeomorphEquiv ((Homeomorph.refl X).prodCongr e₀)
    let e := u.symm.trans v
    have he : bottEuclideanExternalProduct (X := X) 0 = e.toAddMonoidHom := by
      apply AddMonoidHom.ext
      intro a
      have hunit : compactSupportKZeroExternalProduct a compactSupportKZeroPointOne =
          u.symm a := by
        apply u.injective
        rw [u.apply_symm_apply]
        exact compactSupportKZeroExternalProduct_one_right a
      have hproduct := compactSupportKZeroExternalProduct_homeomorph
        (Homeomorph.refl X) e₀ a compactSupportKZeroPointOne
      rw [hid, hunit] at hproduct
      exact hproduct.symm
    rw [he]
    exact e.bijective
  | succ n ih =>
    -- Append the same final coordinate after the specified product associator.
    let A := Fin n → ℂ
    let e := (compactSupportKZeroHomeomorphEquiv (Homeomorph.prodAssoc X A ℂ)).trans
      (compactSupportKZeroHomeomorphEquiv
        ((Homeomorph.refl X).prodCongr (complexFinSuccHomeomorph n)))
    let F := e.toAddMonoidHom.comp
      (bottLineExternalProduct.comp (bottEuclideanExternalProduct (X := X) n))
    have hF : Function.Bijective F :=
      e.bijective.comp ((bottLineExternalProduct_bijective (X × A)).comp ih)
    have he : bottEuclideanExternalProduct (X := X) (n + 1) = F := by
      apply AddMonoidHom.ext
      intro a
      change compactSupportKZeroExternalProduct a
        (compactSupportKZeroHomeomorph (complexFinSuccHomeomorph n)
          (compactSupportKZeroExternalProduct (bottEuclideanClass n) bottLineClass)) =
        compactSupportKZeroHomeomorph ((Homeomorph.refl X).prodCongr (complexFinSuccHomeomorph n))
          (compactSupportKZeroHomeomorph (Homeomorph.prodAssoc X A ℂ)
            (compactSupportKZeroExternalProduct
              (compactSupportKZeroExternalProduct a (bottEuclideanClass n)) bottLineClass))
      rw [compactSupportKZeroExternalProduct_assoc]
      have hproduct := compactSupportKZeroExternalProduct_homeomorph
        (Homeomorph.refl X) (complexFinSuccHomeomorph n) a
        (compactSupportKZeroExternalProduct (bottEuclideanClass n) bottLineClass)
      rw [hid] at hproduct
      exact hproduct.symm
    rw [he]
    exact hF

/-- The Bott equivalence whose forward map is the specified finite external product. -/
def bottEuclideanEquiv (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] (n : ℕ) :
    CompactSupportKZero X ≃+ CompactSupportKZero (X × (Fin n → ℂ)) :=
  AddEquiv.ofBijective (bottEuclideanExternalProduct n)
    (bottEuclideanExternalProduct_bijective X n)

/-- The integer coordinate induced by the same finite-dimensional Bott map and point rank. -/
def bottEuclideanClassEquivInt (n : ℕ) : CompactSupportKZero (Fin n → ℂ) ≃+ ℤ :=
  (((compactSupportKZeroHomeomorphEquiv
    (Homeomorph.uniqueProd PUnit.{1} (Fin n → ℂ))).symm.trans
      (bottEuclideanEquiv PUnit.{1} n).symm).trans
        (compactSupportKZeroCompactEquiv PUnit.{1})).trans complexKZeroPointEquivInt

/-- The actual iterated line class is the positive generator in every finite complex dimension. -/
theorem bottEuclideanClassEquivInt_bottEuclideanClass (n : ℕ) :
    bottEuclideanClassEquivInt n (bottEuclideanClass n) = 1 := by
  /- Stage 1: the left point-unit law identifies the external product of the
  positive point class and bottEuclideanClass n with that same class after
  the displayed PUnit×ℂⁿ→ℂⁿ projection.
  Stage 2: apply the inverse of the same Bott equivalence, then the prescribed
  compact-to-absolute restriction. The result is the original rank-one class.
  Stage 3: the existing point rank normalization sends this class to +1.
  This includes n = 0 and fixes the sign from the original point rank.
  The separate exterior-symbol comparison is not used. -/
  -- The same point-unit product is the original finite Bott class after the given projection.
  let e := compactSupportKZeroHomeomorphEquiv
    (Homeomorph.uniqueProd PUnit.{1} (Fin n → ℂ))
  have hclass : e.symm (bottEuclideanClass n) =
      bottEuclideanEquiv PUnit.{1} n compactSupportKZeroPointOne := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (compactSupportKZeroExternalProduct_one_left (bottEuclideanClass n)).symm
  change complexKZeroPointEquivInt (compactSupportKZeroCompactEquiv PUnit.{1}
    ((bottEuclideanEquiv PUnit.{1} n).symm (e.symm (bottEuclideanClass n)))) = 1
  rw [hclass, AddEquiv.symm_apply_apply]
  change complexKZeroPointEquivInt (compactSupportKZeroCompactEquiv PUnit.{1}
    ((compactSupportKZeroCompactEquiv PUnit.{1}).symm
      (kZeroClass C(PUnit.{1}, ℂ) (IdempotentMatrix.identity C(PUnit.{1}, ℂ) 1)))) = 1
  rw [AddEquiv.apply_symm_apply]
  -- The original point rank sends this same rank-one matrix to the positive integer one.
  rw [complexKZeroPointEquivInt, AddEquiv.ofBijective_apply, complexKZeroRankAt,
    AddMonoidHom.comp_apply, kZeroMap_class, kZeroRank_class]
  change (Module.finrank ℂ (Matrix.mulVecLin
    ((ContinuousMap.evalAlgHom ℂ ℂ PUnit.unit).toRingHom.mapMatrix
      (1 : Matrix (Fin 1) (Fin 1) C(PUnit.{1}, ℂ)))).range : ℤ) = 1
  rw [map_one, Matrix.mulVecLin_one, LinearMap.range_id]
  simp

/-- Appending coordinate blocks multiplies the actual finite Bott classes. -/
theorem bottEuclideanClass_add (m n : ℕ) :
    compactSupportKZeroHomeomorph (Fin.appendHomeomorph (X := ℂ) m n)
      (compactSupportKZeroExternalProduct (bottEuclideanClass m) (bottEuclideanClass n)) =
        bottEuclideanClass (m + n) := by
  /- Induct on the second block length. At zero, use the rank-one unit and
  the actual empty-block append map. At a successor, product associativity
  and naturality let the last line factor pass through the previous block
  assembly. The two resulting coordinate maps agree at every Fin index:
  the m coordinates come first, followed by the n coordinates and the last
  coordinate. Transport composition gives the claimed equality of classes.
  No graded interchange is needed, so no extra sign is introduced. -/
  have hcomp {A B C : Type} [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A]
      [TopologicalSpace B] [LocallyCompactSpace B] [T2Space B]
      [TopologicalSpace C] [LocallyCompactSpace C] [T2Space C]
      (e : A ≃ₜ B) (f : B ≃ₜ C) (a : CompactSupportKZero A) :
      compactSupportKZeroHomeomorph f (compactSupportKZeroHomeomorph e a) =
        compactSupportKZeroHomeomorph (e.trans f) a := by
    unfold compactSupportKZeroHomeomorph
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  have hid {A : Type} [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A]
      (a : CompactSupportKZero A) :
      compactSupportKZeroHomeomorph (Homeomorph.refl A) a = a := by
    change compactSupportKZeroPullback (ContinuousMap.id A) isProperMap_id a = a
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  induction n with
  | zero =>
    -- The empty second block is the original positive point unit under its unique map.
    let e₀ := Homeomorph.homeomorphOfUnique PUnit.{1} (Fin 0 → ℂ)
    have hp := compactSupportKZeroExternalProduct_homeomorph
      (Homeomorph.refl (Fin m → ℂ)) e₀ (bottEuclideanClass m) compactSupportKZeroPointOne
    rw [hid] at hp
    change compactSupportKZeroHomeomorph (Fin.appendHomeomorph (X := ℂ) m 0)
      (compactSupportKZeroExternalProduct (bottEuclideanClass m)
        (compactSupportKZeroHomeomorph e₀ compactSupportKZeroPointOne)) = _
    rw [← hp, hcomp]
    have hcoords : ((Homeomorph.refl (Fin m → ℂ)).prodCongr e₀).trans
        (Fin.appendHomeomorph m 0) = Homeomorph.prodUnique (Fin m → ℂ) PUnit.{1} := by
      ext z i
      exact congrFun (Fin.append_right_nil z.1 (e₀ z.2) rfl) i
    rw [hcoords]
    exact compactSupportKZeroExternalProduct_one_right (bottEuclideanClass m)
  | succ n ih =>
    let A := Fin m → ℂ
    let B := Fin n → ℂ
    let e := Fin.appendHomeomorph (X := ℂ) m n
    let f := complexFinSuccHomeomorph n
    let g := Fin.appendHomeomorph (X := ℂ) m (n + 1)
    let k := complexFinSuccHomeomorph (m + n)
    let a := bottEuclideanClass m
    let b := bottEuclideanClass n
    let c := bottLineClass
    -- Both orders of coordinate assembly retain m coordinates, then n, then the last line.
    have hcoords : ((Homeomorph.prodAssoc A B ℂ).trans
        ((Homeomorph.refl A).prodCongr f)).trans g =
        (e.prodCongr (Homeomorph.refl ℂ)).trans k := by
      ext z i
      exact (congrFun (Fin.append_assoc z.1.1 z.1.2 (fun _ : Fin 1 ↦ z.2)) i).symm
    have hleft := compactSupportKZeroExternalProduct_homeomorph
      (Homeomorph.refl A) f a (compactSupportKZeroExternalProduct b c)
    rw [hid] at hleft
    have hright := compactSupportKZeroExternalProduct_homeomorph
      e (Homeomorph.refl ℂ) (compactSupportKZeroExternalProduct a b) c
    rw [hid] at hright
    -- Reassociate the same three factors and move only their specified coordinate maps.
    calc
      compactSupportKZeroHomeomorph g
          (compactSupportKZeroExternalProduct a (bottEuclideanClass (n + 1))) =
          compactSupportKZeroHomeomorph g
            (compactSupportKZeroHomeomorph ((Homeomorph.refl A).prodCongr f)
              (compactSupportKZeroExternalProduct a
                (compactSupportKZeroExternalProduct b c))) := by rw [hleft]; rfl
      _ = compactSupportKZeroHomeomorph g
          (compactSupportKZeroHomeomorph ((Homeomorph.refl A).prodCongr f)
            (compactSupportKZeroHomeomorph (Homeomorph.prodAssoc A B ℂ)
              (compactSupportKZeroExternalProduct
                (compactSupportKZeroExternalProduct a b) c))) := by
          rw [compactSupportKZeroExternalProduct_assoc]
      _ = compactSupportKZeroHomeomorph
          (((Homeomorph.prodAssoc A B ℂ).trans ((Homeomorph.refl A).prodCongr f)).trans g)
          (compactSupportKZeroExternalProduct
            (compactSupportKZeroExternalProduct a b) c) := by
          rw [hcomp, hcomp]
          rfl
      _ = compactSupportKZeroHomeomorph ((e.prodCongr (Homeomorph.refl ℂ)).trans k)
          (compactSupportKZeroExternalProduct
            (compactSupportKZeroExternalProduct a b) c) := by rw [hcoords]
      _ = compactSupportKZeroHomeomorph k
          (compactSupportKZeroExternalProduct
            (compactSupportKZeroHomeomorph e (compactSupportKZeroExternalProduct a b)) c) := by
          rw [← hcomp, hright]
      _ = bottEuclideanClass (m + (n + 1)) := by
          change compactSupportKZeroHomeomorph k
            (compactSupportKZeroExternalProduct
              (compactSupportKZeroHomeomorph e
                (compactSupportKZeroExternalProduct (bottEuclideanClass m)
                  (bottEuclideanClass n))) bottLineClass) = _
          rw [ih]
          rfl

/-- The one-coordinate class agrees with the original line class under evaluation at zero. -/
theorem bottEuclideanClass_one :
    compactSupportKZeroHomeomorph (Homeomorph.funUnique (Fin 1) ℂ)
      (bottEuclideanClass 1) = bottLineClass := by
  /- Expand the successor of the zero-dimensional class. Naturality transports
  its point unit through the unique map to ℂ⁰, and the point-unit law removes
  that factor. Evaluation of the resulting appended coordinate is the original
  complex number, not its inverse or conjugate, so the remaining class is
  exactly bottLineClass with multiplication-by-z boundary. -/
  let e₀ := Homeomorph.homeomorphOfUnique PUnit.{1} (Fin 0 → ℂ)
  let e₁ := Homeomorph.funUnique (Fin 1) ℂ
  have hid : compactSupportKZeroHomeomorph (Homeomorph.refl ℂ) bottLineClass =
      bottLineClass := by
    change compactSupportKZeroPullback (ContinuousMap.id ℂ) isProperMap_id bottLineClass = _
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  -- Move the original point unit into the actual empty coordinate space.
  have hproduct := compactSupportKZeroExternalProduct_homeomorph e₀ (Homeomorph.refl ℂ)
    compactSupportKZeroPointOne bottLineClass
  rw [hid] at hproduct
  have htransport (a : CompactSupportKZero (PUnit.{1} × ℂ)) :
      compactSupportKZeroHomeomorph e₁
        (compactSupportKZeroHomeomorph (complexFinSuccHomeomorph 0)
          (compactSupportKZeroHomeomorph (e₀.prodCongr (Homeomorph.refl ℂ)) a)) =
        compactSupportKZeroHomeomorph (Homeomorph.uniqueProd PUnit.{1} ℂ) a := by
    -- The successive inverse coordinate maps keep precisely the original complex number.
    unfold compactSupportKZeroHomeomorph
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  change compactSupportKZeroHomeomorph e₁
    (compactSupportKZeroHomeomorph (complexFinSuccHomeomorph 0)
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroHomeomorph e₀ compactSupportKZeroPointOne) bottLineClass)) = _
  rw [← hproduct, htransport]
  exact compactSupportKZeroExternalProduct_one_left bottLineClass

/-- Permuting complex coordinates preserves the iterated degree-zero Bott class. -/
theorem bottEuclideanClass_perm (n : ℕ) (e : Equiv.Perm (Fin n)) :
    compactSupportKZeroHomeomorph (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) e)
      (bottEuclideanClass n) = bottEuclideanClass n := by
  /- Express a finite permutation as a product of adjacent interchanges.
  The recursive product isolates the two adjacent line factors. Product
  associativity, naturality and the degree-zero swap law exchange those
  identical factors without a sign, and transport composition handles the
  full permutation. The displayed homeomorphism uses e⁻¹ on coordinates;
  its inverse pullback is the existing compact-support transport convention.
  This is complex-coordinate permutation invariance, not invariance under
  arbitrary real coordinate changes or complex conjugation. -/
  classical
  have hcomp {A B C : Type} [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A]
      [TopologicalSpace B] [LocallyCompactSpace B] [T2Space B]
      [TopologicalSpace C] [LocallyCompactSpace C] [T2Space C]
      (f : A ≃ₜ B) (g : B ≃ₜ C) (a : CompactSupportKZero A) :
      compactSupportKZeroHomeomorph g (compactSupportKZeroHomeomorph f a) =
        compactSupportKZeroHomeomorph (f.trans g) a := by
    unfold compactSupportKZeroHomeomorph
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  have hid {A : Type} [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A]
      (a : CompactSupportKZero A) :
      compactSupportKZeroHomeomorph (Homeomorph.refl A) a = a := by
    change compactSupportKZeroPullback (ContinuousMap.id A) isProperMap_id a = a
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  -- The recursive coordinate assembly is exactly a tuple with one coordinate appended.
  have hsnoc (m : ℕ) (x : Fin m → ℂ) (z : ℂ) :
      complexFinSuccHomeomorph m (x, z) = Fin.snoc x z := by
    exact Fin.append_right_eq_snoc x (fun _ : Fin 1 ↦ z)
  have hpermApply (m : ℕ) (p : Equiv.Perm (Fin m)) (x : Fin m → ℂ) (i : Fin m) :
      Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) p x i = x (p.symm i) := by
    simpa only [Equiv.apply_symm_apply] using
      Homeomorph.piCongrLeft_apply_apply (Y := fun _ ↦ ℂ) p x (p.symm i)
  have hsnocSwap (m : ℕ) (x : Fin m → ℂ) (z : ℂ) (i j : Fin m) :
      Fin.snoc x z ∘ Equiv.swap i.castSucc j.castSucc =
        Fin.snoc (x ∘ Equiv.swap i j) z := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · have hi : Fin.last m ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
      have hj : Fin.last m ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hi hj, Fin.snoc_last]
    · rw [Function.comp_apply, ← Function.Injective.map_swap (Fin.castSucc_injective m),
        Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl
  have hlastSwap (m : ℕ) (x : Fin m → ℂ) (z w : ℂ) :
      Fin.snoc (Fin.snoc x z) w ∘
          Equiv.swap (Fin.last m).castSucc (Fin.last m).succ =
        Fin.snoc (Fin.snoc x w) z := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp
    · refine Fin.lastCases ?_ (fun k ↦ ?_) k
      · simp
      · have h₁ : k.castSucc.castSucc ≠ (Fin.last m).castSucc := by simp
        have h₂ : k.castSucc.castSucc ≠ (Fin.last m).succ :=
          Fin.castSucc_ne_last k.castSucc
        simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂,
          Fin.snoc_castSucc]
  -- Isolate the last two line factors; their degree-zero product is fixed by exchange.
  have hlast (m : ℕ) :
      compactSupportKZeroHomeomorph
        (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
          (Equiv.swap (Fin.last m).castSucc (Fin.last m).succ))
        (bottEuclideanClass (m + 2)) = bottEuclideanClass (m + 2) := by
    let A := Fin m → ℂ
    let a := bottEuclideanClass m
    let b := bottLineClass
    let q := compactSupportKZeroExternalProduct a (compactSupportKZeroExternalProduct b b)
    let k := ((complexFinSuccHomeomorph m).prodCongr (Homeomorph.refl ℂ)).trans
      (complexFinSuccHomeomorph (m + 1))
    let r := (Homeomorph.prodAssoc A ℂ ℂ).symm.trans k
    let s := (Homeomorph.refl A).prodCongr (Homeomorph.prodComm ℂ ℂ)
    have hq : compactSupportKZeroHomeomorph s q = q := by
      rw [compactSupportKZeroExternalProduct_homeomorph, hid,
        compactSupportKZeroExternalProduct_swap]
    have hr : compactSupportKZeroHomeomorph r q = bottEuclideanClass (m + 2) := by
      rw [show q = compactSupportKZeroHomeomorph (Homeomorph.prodAssoc A ℂ ℂ)
          (compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct a b) b)
        from (compactSupportKZeroExternalProduct_assoc a b b).symm, hcomp]
      have hmaps : (Homeomorph.prodAssoc A ℂ ℂ).trans r = k := by
        ext z
        rfl
      rw [hmaps]
      change compactSupportKZeroHomeomorph
        (((complexFinSuccHomeomorph m).prodCongr (Homeomorph.refl ℂ)).trans
          (complexFinSuccHomeomorph (m + 1))) _ = _
      rw [← hcomp, compactSupportKZeroExternalProduct_homeomorph, hid]
      rfl
    have hcoords : r.trans (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
        (Equiv.swap (Fin.last m).castSucc (Fin.last m).succ)) = s.trans r := by
      ext z j
      change Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
        (Equiv.swap (Fin.last m).castSucc (Fin.last m).succ) (r z) j = r (s z) j
      rw [hpermApply]
      change (complexFinSuccHomeomorph (m + 1)
        (complexFinSuccHomeomorph m (z.1, z.2.1), z.2.2))
          ((Equiv.swap (Fin.last m).castSucc (Fin.last m).succ).symm j) =
        complexFinSuccHomeomorph (m + 1)
          (complexFinSuccHomeomorph m (z.1, z.2.2), z.2.1) j
      rw [hsnoc, hsnoc, hsnoc, hsnoc]
      exact congrFun (hlastSwap m z.1 z.2.1 z.2.2) j
    rw [← hr, hcomp, hcoords, ← hcomp, hq]
  -- Earlier adjacent interchanges are transported through the unchanged final line factor.
  have hadjacent (m : ℕ) (i : Fin m) :
      compactSupportKZeroHomeomorph (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
          (Equiv.swap i.castSucc i.succ))
        (bottEuclideanClass (m + 1)) = bottEuclideanClass (m + 1) := by
    induction m with
    | zero => exact Fin.elim0 i
    | succ m ih =>
      refine Fin.lastCases (hlast m) (fun j ↦ ?_) i
      let p := Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) (Equiv.swap j.castSucc j.succ)
      let q := Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
        (Equiv.swap j.castSucc.castSucc j.castSucc.succ)
      have hcoords : (complexFinSuccHomeomorph (m + 1)).trans q =
          (p.prodCongr (Homeomorph.refl ℂ)).trans (complexFinSuccHomeomorph (m + 1)) := by
        ext z k
        change Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
          (Equiv.swap j.castSucc.castSucc j.castSucc.succ)
            (complexFinSuccHomeomorph (m + 1) z) k = _
        rw [hpermApply]
        change (complexFinSuccHomeomorph (m + 1) z)
            ((Equiv.swap j.castSucc.castSucc j.castSucc.succ).symm k) =
          complexFinSuccHomeomorph (m + 1) (p z.1, z.2) k
        rw [show z = (z.1, z.2) from rfl, hsnoc, hsnoc]
        have hp : p z.1 = z.1 ∘ Equiv.swap j.castSucc j.succ := by
          ext l
          exact hpermApply (m + 1) (Equiv.swap j.castSucc j.succ) z.1 l
        rw [hp]
        simpa only [Equiv.symm_swap, Fin.castSucc_succ, Function.comp_apply] using
          congrFun (hsnocSwap (m + 1) z.1 z.2 j.castSucc j.succ) k
      change compactSupportKZeroHomeomorph q
        (compactSupportKZeroHomeomorph (complexFinSuccHomeomorph (m + 1))
          (compactSupportKZeroExternalProduct (bottEuclideanClass (m + 1)) bottLineClass)) = _
      rw [hcomp, hcoords, ← hcomp, compactSupportKZeroExternalProduct_homeomorph, hid, ih]
      rfl
  -- Adjacent transpositions generate the full finite symmetric group, including the empty case.
  cases n with
  | zero =>
    have he : e = Equiv.refl (Fin 0) := Subsingleton.elim _ _
    rw [he, Homeomorph.piCongrLeft_refl, hid]
  | succ n =>
    have he : e ∈ Submonoid.closure
        (Set.range fun i : Fin n ↦ Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction he using Submonoid.closure_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      exact hadjacent n i
    | one => exact hid _
    | mul p q _ _ hp hq =>
      have hcoords : (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) q).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) p) =
          Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) (p * q) := by
        ext z i
        change Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) p
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) q z) i = _
        rw [hpermApply, hpermApply, hpermApply]
        rfl
      rw [← hcoords, ← hcomp, hq, hp]

end AtiyahSinger
