/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomotopyFiber
public import Mathlib.Tactic

/-!
# Cohomology of the original nonnegative homotopy fiber

Public module ID: M0036.

These adapters expose the source and shifted target summands of mathlib's
actual `HomologicalComplex.homotopyFiber`. They change no object or differential.
The nonnegative endpoint has only the source summand, and positive-degree
coordinates have differential `(F c - d y, d c)`. This retains the native
opposite-cofiber sign when using the standard acyclicity criterion for a
quasi-isomorphism.

`homologyMap_bijective_iff_cycle_lifting` identifies bijectivity of the actual
cohomology map with reflection of boundaries and lifting of cycles modulo
boundaries. `homologyMap_bijective_iff_exact_homotopyFiber` then characterizes
quasi-isomorphisms by exactness of the same native nonnegative fiber.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] ComplexShape.decidableRelSymm

universe u

variable {R : Type} [CommRing R]
  {C D : CochainComplex (ModuleCat.{u} R) ℕ} (F : C ⟶ D)

/-- The canonical projection of the native fiber to its source. -/
def homotopyFiberSource (n : ℕ) :
    (HomologicalComplex.homotopyFiber F).X n ⟶ C.X n :=
  (HomologicalComplex.homotopyCofiber.inrX
    ((HomologicalComplex.opFunctor _ _).map F.op) n).unop

/-- The source summand in each degree of the native fiber. -/
def homotopyFiberSourceInclusion (n : ℕ) :
    C.X n ⟶ (HomologicalComplex.homotopyFiber F).X n :=
  (HomologicalComplex.homotopyCofiber.sndX
    ((HomologicalComplex.opFunctor _ _).map F.op) n).unop

/-- The shifted target projection of the native fiber in positive degree. -/
def homotopyFiberTarget (n : ℕ) :
    (HomologicalComplex.homotopyFiber F).X (n + 1) ⟶ D.X n :=
  (HomologicalComplex.homotopyCofiber.inlX
    ((HomologicalComplex.opFunctor _ _).map F.op) n (n + 1) (by rfl)).unop

/-- The shifted target summand of the native fiber in positive degree. -/
def homotopyFiberTargetInclusion (n : ℕ) :
    D.X n ⟶ (HomologicalComplex.homotopyFiber F).X (n + 1) :=
  (HomologicalComplex.homotopyCofiber.fstX
    ((HomologicalComplex.opFunctor _ _).map F.op) (n + 1) n (by rfl)).unop

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Degree zero in the native nonnegative fiber is exactly its source degree zero. -/
def homotopyFiberZeroEquiv :
    (HomologicalComplex.homotopyFiber F).X 0 ≃ₗ[R] C.X 0 :=
  { (homotopyFiberSource F 0).hom with
    invFun := homotopyFiberSourceInclusion F 0
    left_inv := by
      intro x
      exact congrArg (fun f ↦ f x) (congrArg Quiver.Hom.unop
        (HomologicalComplex.homotopyCofiber.sndX_inrX
          ((HomologicalComplex.opFunctor _ _).map F.op) 0 (by
            change ¬ (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev 0) 0
            simp)))
    right_inv := by
      intro x
      exact congrArg (fun f ↦ f x) (congrArg Quiver.Hom.unop
        (HomologicalComplex.homotopyCofiber.inrX_sndX
          ((HomologicalComplex.opFunctor _ _).map F.op) 0)) }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical shifted-target/source coordinates of the native fiber. -/
def homotopyFiberSuccEquiv (n : ℕ) :
    (HomologicalComplex.homotopyFiber F).X (n + 1) ≃ₗ[R] D.X n × C.X (n + 1) := by
  let f := (HomologicalComplex.opFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ)).map F.op
  have hs : homotopyFiberSource F (n + 1) ≫ homotopyFiberSourceInclusion F (n + 1) +
      homotopyFiberTarget F n ≫ homotopyFiberTargetInclusion F n = 𝟙 _ := by
    have h : HomologicalComplex.homotopyCofiber.sndX f (n + 1) ≫
        HomologicalComplex.homotopyCofiber.inrX f (n + 1) +
        HomologicalComplex.homotopyCofiber.fstX f (n + 1) n (by rfl) ≫
        HomologicalComplex.homotopyCofiber.inlX f n (n + 1) (by rfl) = 𝟙 _ := by
      apply HomologicalComplex.homotopyCofiber.ext_from_X f n (n + 1) (by rfl)
      · simp
      · simp
    exact congrArg Quiver.Hom.unop h
  have hCC : homotopyFiberSourceInclusion F (n + 1) ≫
      homotopyFiberSource F (n + 1) = 𝟙 _ :=
    congrArg Quiver.Hom.unop (HomologicalComplex.homotopyCofiber.inrX_sndX f (n + 1))
  have hDD : homotopyFiberTargetInclusion F n ≫ homotopyFiberTarget F n = 𝟙 _ :=
    congrArg Quiver.Hom.unop (HomologicalComplex.homotopyCofiber.inlX_fstX f n (n + 1) (by rfl))
  have hCD : homotopyFiberSourceInclusion F (n + 1) ≫ homotopyFiberTarget F n = 0 :=
    congrArg Quiver.Hom.unop (HomologicalComplex.homotopyCofiber.inlX_sndX f n (n + 1) (by rfl))
  have hDC : homotopyFiberTargetInclusion F n ≫ homotopyFiberSource F (n + 1) = 0 :=
    congrArg Quiver.Hom.unop (HomologicalComplex.homotopyCofiber.inrX_fstX f (n + 1) n (by rfl))
  refine
    { toLinearMap :=
        (homotopyFiberTarget F n).hom.prod (homotopyFiberSource F (n + 1)).hom
      invFun := fun p ↦ homotopyFiberTargetInclusion F n p.1 +
        homotopyFiberSourceInclusion F (n + 1) p.2
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    have h := congrArg (fun f ↦ f x) hs
    change homotopyFiberSourceInclusion F (n + 1) (homotopyFiberSource F (n + 1) x) +
      homotopyFiberTargetInclusion F n (homotopyFiberTarget F n x) = x at h
    change homotopyFiberTargetInclusion F n (homotopyFiberTarget F n x) +
      homotopyFiberSourceInclusion F (n + 1) (homotopyFiberSource F (n + 1) x) = x
    exact (add_comm _ _).trans h
  · intro p
    have hDD' := congrArg (fun f ↦ f p.1) hDD
    have hDC' := congrArg (fun f ↦ f p.1) hDC
    have hCC' := congrArg (fun f ↦ f p.2) hCC
    have hCD' := congrArg (fun f ↦ f p.2) hCD
    apply Prod.ext
    · change homotopyFiberTarget F n (_ + _) = p.1
      rw [map_add]
      exact (congrArg₂ (· + ·) hDD' hCD').trans (add_zero p.1)
    · change homotopyFiberSource F (n + 1) (_ + _) = p.2
      rw [map_add]
      exact (congrArg₂ (· + ·) hDC' hCC').trans (zero_add p.2)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original fiber differential at the nonnegative endpoint, in canonical coordinates. -/
theorem homotopyFiberZeroEquiv_d
    (x : (HomologicalComplex.homotopyFiber F).X 0) :
    homotopyFiberSuccEquiv F 0 ((HomologicalComplex.homotopyFiber F).d 0 1 x) =
      (F.f 0 (homotopyFiberZeroEquiv F x), C.d 0 1 (homotopyFiberZeroEquiv F x)) := by
  apply Prod.ext
  · exact congrArg (fun f ↦ f x) (congrArg Quiver.Hom.unop
      (HomologicalComplex.homotopyCofiber.inlX_d'
        ((HomologicalComplex.opFunctor _ _).map F.op) 1 0 (by rfl) (by
          change ¬ (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev 0) 0
          simp)))
  · exact congrArg (fun f ↦ f x) (congrArg Quiver.Hom.unop
      (HomologicalComplex.homotopyCofiber.inrX_d
        ((HomologicalComplex.opFunctor _ _).map F.op) 1 0))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original positive-degree fiber differential retains its negative target differential. -/
theorem homotopyFiberSuccEquiv_d (n : ℕ)
    (x : (HomologicalComplex.homotopyFiber F).X (n + 1)) :
    homotopyFiberSuccEquiv F (n + 1)
        ((HomologicalComplex.homotopyFiber F).d (n + 1) (n + 2) x) =
      (F.f (n + 1) (homotopyFiberSuccEquiv F n x).2 -
          D.d n (n + 1) (homotopyFiberSuccEquiv F n x).1,
        C.d (n + 1) (n + 2) (homotopyFiberSuccEquiv F n x).2) := by
  apply Prod.ext
  · have h : (HomologicalComplex.homotopyFiber F).d (n + 1) (n + 2) ≫
        homotopyFiberTarget F (n + 1) = -(homotopyFiberTarget F n ≫ D.d n (n + 1)) +
          homotopyFiberSource F (n + 1) ≫ F.f (n + 1) :=
      congrArg Quiver.Hom.unop (HomologicalComplex.homotopyCofiber.inlX_d
        ((HomologicalComplex.opFunctor _ _).map F.op) (n + 2) (n + 1) n (by rfl) (by rfl))
    exact (congrArg (fun f ↦ f x) h).trans (neg_add_eq_sub _ _)
  · exact congrArg
      (fun f : (HomologicalComplex.homotopyFiber F).X (n + 1) ⟶ C.X (n + 2) ↦ f x)
      (congrArg Quiver.Hom.unop (HomologicalComplex.homotopyCofiber.inrX_d
        ((HomologicalComplex.opFunctor _ _).map F.op) (n + 2) (n + 1)))

/-- The source projection is the native morphism obtained by dualizing cofiber inclusion. -/
def homotopyFiberSourceMap : HomologicalComplex.homotopyFiber F ⟶ C :=
  (HomologicalComplex.unopFunctor _ _).map
    (HomologicalComplex.homotopyCofiber.inr
      ((HomologicalComplex.opFunctor _ _).map F.op)).op

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A cochain map is bijective in cohomology precisely when it reflects boundaries
and lifts every closed target cochain modulo an actual boundary. -/
theorem homologyMap_bijective_iff_cycle_lifting
    {R : Type} [CommRing R] {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap F n) ↔
      (∀ c : C.X n, C.d n (n + 1) c = 0 →
        (∃ y : D.X (n - 1), D.d (n - 1) n y = F.f n c) →
        ∃ x : C.X (n - 1), C.d (n - 1) n x = c) ∧
      (∀ y : D.X n, D.d n (n + 1) y = 0 →
        ∃ c : C.X n, C.d n (n + 1) c = 0 ∧
          ∃ z : D.X (n - 1), F.f n c + D.d (n - 1) n z = y) := by
  -- Use the canonical module cycle quotients of the original cochain complexes.
  let cc (B : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (c : (B.sc k).moduleCatLeftHomologyData.K) : B.homology k :=
    (B.sc k).moduleCatHomologyIso.inv ((B.sc k).moduleCatToCycles.range.mkQ c)
  have hprev (k : ℕ) : (ComplexShape.up ℕ).prev k = k - 1 := by
    cases k <;> simp [CochainComplex.prev_nat_zero, CochainComplex.prev_nat_succ]
  have hzero (B : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (c : (B.sc k).moduleCatLeftHomologyData.K) :
      cc B k c = 0 ↔ ∃ b : B.X (k - 1), B.d (k - 1) k b = c.val := by
    let S := B.sc k
    rw [← hprev k]
    change S.moduleCatHomologyIso.toLinearEquiv.symm (S.moduleCatToCycles.range.mkQ c) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact (Submodule.Quotient.mk_eq_zero _).trans
      (exists_congr fun b ↦ Subtype.ext_iff)
  have hrep (B : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ) (z : B.homology k) :
      ∃ c : (B.sc k).moduleCatLeftHomologyData.K, cc B k c = z := by
    exact ((B.sc k).moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
      (B.sc k).moduleCatToCycles.range.mkQ_surjective) z
  have hclosed (B : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (c : (B.sc k).moduleCatLeftHomologyData.K) : B.d k (k + 1) c.val = 0 := by
    have h : B.d k ((ComplexShape.up ℕ).next k) c.val = 0 := c.property
    exact (congrArg (fun j ↦ B.d k j c.val = 0) (CochainComplex.next ℕ k)).mp h
  have hcycle (B : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (c : B.X k) (hc : B.d k (k + 1) c = 0) : c ∈ ((B.sc k).g).hom.ker := by
    change B.d k ((ComplexShape.up ℕ).next k) c = 0
    exact (congrArg (fun j ↦ B.d k j c = 0) (CochainComplex.next ℕ k)).mpr hc
  have hsub (B : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (c d : (B.sc k).moduleCatLeftHomologyData.K) :
      cc B k (c - d) = cc B k c - cc B k d := by
    dsimp only [cc]
    rw [map_sub, map_sub]
  have hmap (k : ℕ) (b : (C.sc k).moduleCatLeftHomologyData.K)
      (c : (D.sc k).moduleCatLeftHomologyData.K) (h : F.f k b.val = c.val) :
      HomologicalComplex.homologyMap F k (cc C k b) = cc D k c := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) k).map F
    let G := ShortComplex.leftHomologyMapData S
      (C.sc k).moduleCatLeftHomologyData (D.sc k).moduleCatLeftHomologyData
    have hcycles : G.φK b = c := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f b) G.commi).trans h
    have hquot := congrArg (fun f ↦ f b) G.commπ
    change G.φH ((C.sc k).moduleCatToCycles.range.mkQ b) =
      (D.sc k).moduleCatToCycles.range.mkQ (G.φK b) at hquot
    rw [hcycles] at hquot
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F k = _ at hmap
    rw [hmap]
    change (D.sc k).moduleCatHomologyIso.inv
      (G.φH ((C.sc k).moduleCatHomologyIso.hom
        ((C.sc k).moduleCatHomologyIso.inv ((C.sc k).moduleCatToCycles.range.mkQ b)))) = _
    have hcancel : (C.sc k).moduleCatHomologyIso.hom
        ((C.sc k).moduleCatHomologyIso.inv ((C.sc k).moduleCatToCycles.range.mkQ b)) =
          (C.sc k).moduleCatToCycles.range.mkQ b :=
      congrArg (fun f ↦ f ((C.sc k).moduleCatToCycles.range.mkQ b))
        (C.sc k).moduleCatHomologyIso.inv_hom_id
    rw [hcancel, hquot]
  have hmapClosed (k : ℕ) (c : C.X k) (hc : C.d k (k + 1) c = 0) :
      D.d k (k + 1) (F.f k c) = 0 := by
    have h := congrArg (fun f ↦ f c) (F.comm k (k + 1))
    change D.d k (k + 1) (F.f k c) = F.f (k + 1) (C.d k (k + 1) c) at h
    rw [h, hc, map_zero]
  constructor
  · intro hF
    constructor
    · intro c hc hb
      let c₀ : (C.sc n).moduleCatLeftHomologyData.K := ⟨c, hcycle C n c hc⟩
      let c₁ : (D.sc n).moduleCatLeftHomologyData.K :=
        ⟨F.f n c, hcycle D n _ (hmapClosed n c hc)⟩
      have hz : cc C n c₀ = 0 := hF.injective
        ((hmap n c₀ c₁ rfl).trans ((hzero D n c₁).mpr hb) |>.trans (map_zero _).symm)
      exact (hzero C n c₀).mp hz
    · intro y hy
      let y₀ : (D.sc n).moduleCatLeftHomologyData.K := ⟨y, hcycle D n y hy⟩
      obtain ⟨a, ha⟩ := hF.surjective (cc D n y₀)
      obtain ⟨c, rfl⟩ := hrep C n a
      let c₁ : (D.sc n).moduleCatLeftHomologyData.K :=
        ⟨F.f n c.val, hcycle D n _ (hmapClosed n c.val (hclosed C n c))⟩
      have heq : cc D n c₁ = cc D n y₀ := (hmap n c c₁ rfl).symm.trans ha
      have hz : cc D n (y₀ - c₁) = 0 := by rw [hsub, heq, sub_self]
      obtain ⟨z, hz⟩ := (hzero D n (y₀ - c₁)).mp hz
      refine ⟨c.val, hclosed C n c, z, ?_⟩
      change D.d (n - 1) n z = y - F.f n c.val at hz
      rw [hz]
      abel
  · rintro ⟨hreflect, hlift⟩
    constructor
    · have hker (a : C.homology n) (ha : HomologicalComplex.homologyMap F n a = 0) :
          a = 0 := by
        obtain ⟨c, rfl⟩ := hrep C n a
        let c₁ : (D.sc n).moduleCatLeftHomologyData.K :=
          ⟨F.f n c.val, hcycle D n _ (hmapClosed n c.val (hclosed C n c))⟩
        have hz : cc D n c₁ = 0 := (hmap n c c₁ rfl).symm.trans ha
        exact (hzero C n c).mpr (hreflect c.val (hclosed C n c) ((hzero D n c₁).mp hz))
      intro a b hab
      apply sub_eq_zero.mp
      apply hker
      rw [map_sub, hab, sub_self]
    · intro a
      obtain ⟨y, rfl⟩ := hrep D n a
      obtain ⟨c, hc, z, hz⟩ := hlift y.val (hclosed D n y)
      let c₀ : (C.sc n).moduleCatLeftHomologyData.K := ⟨c, hcycle C n c hc⟩
      let c₁ : (D.sc n).moduleCatLeftHomologyData.K :=
        ⟨F.f n c, hcycle D n _ (hmapClosed n c hc)⟩
      refine ⟨cc C n c₀, (hmap n c₀ c₁ rfl).trans ?_⟩
      apply sub_eq_zero.mp
      rw [← hsub]
      apply (hzero D n (c₁ - y)).mpr
      refine ⟨-z, ?_⟩
      change D.d (n - 1) n (-z) = F.f n c - (show D.X n from y.val)
      rw [map_neg, ← hz, sub_add_eq_sub_sub, sub_self, zero_sub]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original nonnegative homotopy fiber is acyclic exactly when the original map
is bijective in every cohomological degree. -/
theorem homologyMap_bijective_iff_exact_homotopyFiber
    {R : Type} [CommRing R] {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) :
    (∀ n, Function.Bijective (HomologicalComplex.homologyMap F n)) ↔
      ∀ n, Function.Exact
        ((HomologicalComplex.homotopyFiber F).d (n - 1) n)
        ((HomologicalComplex.homotopyFiber F).d n (n + 1)) := by
  -- A fiber cocycle records a source cycle whose image has a specified target primitive.
  -- Reflection of boundaries removes its source component; lifting a target cycle
  -- removes the remaining defect. Conversely, a fiber primitive supplies both lifts.
  let K := HomologicalComplex.homotopyFiber F
  have hcomm (p q : ℕ) (x : K.X p) :
      C.d p q (homotopyFiberSource F p x) =
        homotopyFiberSource F q (K.d p q x) :=
    congrArg (fun f ↦ f x) ((homotopyFiberSourceMap F).comm p q)
  constructor
  · intro h n x
    constructor
    · intro hx
      cases n with
      | zero =>
        have hcoords := congrArg (homotopyFiberSuccEquiv F 0) hx
        rw [homotopyFiberZeroEquiv_d, map_zero] at hcoords
        have hfc : F.f 0 (homotopyFiberZeroEquiv F x) = 0 := congrArg Prod.fst hcoords
        have hc : C.d 0 1 (homotopyFiberZeroEquiv F x) = 0 := congrArg Prod.snd hcoords
        obtain ⟨a, ha⟩ := ((homologyMap_bijective_iff_cycle_lifting F 0).mp (h 0)).1
          (homotopyFiberZeroEquiv F x) hc ⟨0, (map_zero _).trans hfc.symm⟩
        have hd : C.d 0 0 = 0 := C.shape 0 0 (by simp)
        have hc0 : homotopyFiberZeroEquiv F x = 0 := by
          rw [← ha, hd]
          rfl
        have hx0 : x = 0 := (homotopyFiberZeroEquiv F).injective
          (hc0.trans (map_zero _).symm)
        exact ⟨0, (map_zero _).trans hx0.symm⟩
      | succ n =>
        let y := (homotopyFiberSuccEquiv F n x).1
        let c := (homotopyFiberSuccEquiv F n x).2
        have hcoords := congrArg (homotopyFiberSuccEquiv F (n + 1)) hx
        rw [homotopyFiberSuccEquiv_d, map_zero] at hcoords
        have hfc : F.f (n + 1) c = D.d n (n + 1) y :=
          sub_eq_zero.mp (congrArg Prod.fst hcoords)
        have hc : C.d (n + 1) (n + 2) c = 0 := congrArg Prod.snd hcoords
        have hprimitive : ∃ a : C.X n, C.d n (n + 1) a = c := by
          simpa using
            ((homologyMap_bijective_iff_cycle_lifting F (n + 1)).mp
              (h (n + 1))).1 c hc ⟨y, hfc.symm⟩
        obtain ⟨a, ha⟩ := hprimitive
        let u := y - F.f n a
        have hu : D.d n (n + 1) u = 0 := by
          change D.d n (n + 1) (y - F.f n a) = 0
          rw [map_sub]
          have hf := congrArg (fun f ↦ f a) (F.comm n (n + 1))
          change D.d n (n + 1) (F.f n a) = F.f (n + 1) (C.d n (n + 1) a) at hf
          rw [hf, ha, hfc, sub_self]
        obtain ⟨b, hb, hv⟩ := ((homologyMap_bijective_iff_cycle_lifting F n).mp (h n)).2
          u hu
        -- A source primitive is corrected by a source cycle so its target defect is a boundary.
        cases n with
        | zero =>
          obtain ⟨v, hv⟩ := hv
          refine ⟨(homotopyFiberZeroEquiv F).symm (a + b), ?_⟩
          apply (homotopyFiberSuccEquiv F 0).injective
          rw [homotopyFiberZeroEquiv_d, LinearEquiv.apply_symm_apply]
          apply Prod.ext
          · change F.f 0 (a + b) = y
            have hd : D.d 0 0 = 0 := D.shape 0 0 (by simp)
            change F.f 0 b + D.d 0 0 v = y - F.f 0 a at hv
            rw [hd] at hv
            change F.f 0 b + 0 = y - F.f 0 a at hv
            rw [map_add]
            rw [add_zero] at hv
            exact (add_comm _ _).trans (eq_sub_iff_add_eq.mp hv)
          · change C.d 0 1 (a + b) = c
            rw [map_add, ha, hb, add_zero]
        | succ k =>
          simp only [Nat.add_one_sub_one] at hv
          obtain ⟨v, hv⟩ := hv
          simp only [Nat.add_succ_sub_one, Nat.add_zero]
          refine ⟨(homotopyFiberSuccEquiv F k).symm (-v, a + b), ?_⟩
          apply (homotopyFiberSuccEquiv F (k + 1)).injective
          rw [homotopyFiberSuccEquiv_d, LinearEquiv.apply_symm_apply]
          apply Prod.ext
          · change F.f (k + 1) (a + b) - D.d k (k + 1) (-v) = y
            change F.f (k + 1) b + D.d k (k + 1) v = y - F.f (k + 1) a at hv
            rw [map_add, map_neg, sub_neg_eq_add]
            calc
              _ = (F.f (k + 1) b + D.d k (k + 1) v) + F.f (k + 1) a := by abel
              _ = y := eq_sub_iff_add_eq.mp hv
          · change C.d (k + 1) (k + 2) (a + b) = c
            rw [map_add, ha, hb, add_zero]
    · rintro ⟨v, rfl⟩
      exact congrArg (fun f ↦ f v) (K.d_comp_d (n - 1) n (n + 1))
  · intro h n
    apply (homologyMap_bijective_iff_cycle_lifting F n).mpr
    constructor
    · intro c hc hboundary
      cases n with
      | zero =>
        obtain ⟨y, hy⟩ := hboundary
        let x := (homotopyFiberZeroEquiv F).symm c
        have hdD : D.d 0 0 = 0 := D.shape 0 0 (by simp)
        have hfc : F.f 0 c = 0 := by rw [← hy, hdD]; rfl
        have hx : K.d 0 1 x = 0 := by
          apply (homotopyFiberSuccEquiv F 0).injective
          rw [homotopyFiberZeroEquiv_d, LinearEquiv.apply_symm_apply, map_zero]
          exact Prod.ext hfc hc
        obtain ⟨a, ha⟩ := (h 0 x).mp hx
        have hdK : K.d 0 0 = 0 := K.shape 0 0 (by simp)
        have hx0 : x = 0 := by rw [← ha, hdK]; rfl
        have hc0 : c = 0 := by
          have hv := congrArg (homotopyFiberZeroEquiv F) hx0
          simpa only [x, LinearEquiv.apply_symm_apply, map_zero] using hv
        exact ⟨0, (map_zero _).trans hc0.symm⟩
      | succ k =>
        simp only [Nat.add_one_sub_one] at hboundary
        obtain ⟨y, hy⟩ := hboundary
        let x := (homotopyFiberSuccEquiv F k).symm (y, c)
        have hx : K.d (k + 1) (k + 2) x = 0 := by
          apply (homotopyFiberSuccEquiv F (k + 1)).injective
          rw [homotopyFiberSuccEquiv_d, LinearEquiv.apply_symm_apply, map_zero]
          apply Prod.ext
          · exact sub_eq_zero.mpr hy.symm
          · exact hc
        have hprimitive : ∃ a : K.X k, K.d k (k + 1) a = x := by
          simpa using (h (k + 1) x).mp hx
        obtain ⟨a, ha⟩ := hprimitive
        simp only [Nat.add_succ_sub_one, Nat.add_zero]
        refine ⟨homotopyFiberSource F k a, ?_⟩
        rw [hcomm, ha]
        exact congrArg Prod.snd ((homotopyFiberSuccEquiv F k).apply_symm_apply (y, c))
    · intro y hy
      let x := (homotopyFiberSuccEquiv F n).symm (y, 0)
      have hx : K.d (n + 1) (n + 2) x = 0 := by
        apply (homotopyFiberSuccEquiv F (n + 1)).injective
        change homotopyFiberSuccEquiv F (n + 1)
          ((HomologicalComplex.homotopyFiber F).d (n + 1) (n + 2) x) = _
        rw [homotopyFiberSuccEquiv_d, LinearEquiv.apply_symm_apply]
        simp only [map_zero, hy, sub_self, Prod.zero_eq_mk]
      have hprimitive : ∃ a : K.X n, K.d n (n + 1) a = x := by
        simpa using (h (n + 1) x).mp hx
      obtain ⟨a, ha⟩ := hprimitive
      let c := homotopyFiberSource F n a
      have hc : C.d n (n + 1) c = 0 := by
        rw [hcomm, ha]
        exact congrArg Prod.snd ((homotopyFiberSuccEquiv F n).apply_symm_apply (y, 0))
      refine ⟨c, hc, ?_⟩
      -- The shifted target component of the primitive gives precisely the boundary correction.
      cases n with
      | zero =>
        refine ⟨0, ?_⟩
        have hv := congrArg (homotopyFiberSuccEquiv F 0) ha
        rw [homotopyFiberZeroEquiv_d, LinearEquiv.apply_symm_apply] at hv
        rw [map_zero, add_zero]
        exact congrArg Prod.fst hv
      | succ k =>
        refine ⟨-(homotopyFiberSuccEquiv F k a).1, ?_⟩
        have hv := congrArg (homotopyFiberSuccEquiv F (k + 1)) ha
        rw [homotopyFiberSuccEquiv_d, LinearEquiv.apply_symm_apply] at hv
        change F.f (k + 1) (homotopyFiberSuccEquiv F k a).2 +
          D.d k (k + 1) (-(homotopyFiberSuccEquiv F k a).1) = y
        rw [map_neg, ← sub_eq_add_neg]
        exact congrArg Prod.fst hv

end AtiyahSinger
