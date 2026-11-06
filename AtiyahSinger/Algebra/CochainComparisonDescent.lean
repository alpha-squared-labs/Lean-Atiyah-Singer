/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CochainDescent
public import AtiyahSinger.Algebra.HomotopyFiberCohomology

/-!
# Comparison for exact augmented cochain rows

Public module ID: M0002.

A commutative map between two exact augmented rows is a quasi-isomorphism on
the augmentation whenever it is a quasi-isomorphism on every later column.
The proof applies finite cohomological descent to mathlib's native homotopy
fibers, with their actual zero-degree endpoint and differential signs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A commuting square acts on the original nonnegative homotopy fibers.
This coordinate description uses the native source and shifted-target projections. -/
def homotopyFiberMap
    {R : Type} [CommRing R] {C D C' D' : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (G : C' ⟶ D') (a : C ⟶ C') (b : D ⟶ D')
    (h : F ≫ b = a ≫ G) :
    HomologicalComplex.homotopyFiber F ⟶ HomologicalComplex.homotopyFiber G := by
  let f : ∀ n, (HomologicalComplex.homotopyFiber F).X n ⟶
      (HomologicalComplex.homotopyFiber G).X n
    | 0 => ModuleCat.ofHom ((homotopyFiberZeroEquiv G).symm.toLinearMap.comp
        ((a.f 0).hom.comp (homotopyFiberZeroEquiv F).toLinearMap))
    | n + 1 => ModuleCat.ofHom ((homotopyFiberSuccEquiv G n).symm.toLinearMap.comp
        (((b.f n).hom.prodMap (a.f (n + 1)).hom).comp
          (homotopyFiberSuccEquiv F n).toLinearMap))
  have ha (i j : ℕ) (x : C.X i) : C'.d i j (a.f i x) = a.f j (C.d i j x) :=
    congrArg (fun f ↦ f x) (a.comm i j)
  have hb (i j : ℕ) (x : D.X i) : D'.d i j (b.f i x) = b.f j (D.d i j x) :=
    congrArg (fun f ↦ f x) (b.comm i j)
  have hs (i : ℕ) (x : C.X i) : G.f i (a.f i x) = b.f i (F.f i x) :=
    (congrArg (fun f ↦ f.f i x) h).symm
  refine CochainComplex.ofHom f ?_
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  cases n with
  | zero =>
    apply (homotopyFiberSuccEquiv G 0).injective
    change homotopyFiberSuccEquiv G 0
      ((HomologicalComplex.homotopyFiber G).d 0 1
        ((homotopyFiberZeroEquiv G).symm (a.f 0 (homotopyFiberZeroEquiv F x)))) = _
    rw [homotopyFiberZeroEquiv_d, LinearEquiv.apply_symm_apply]
    change _ = homotopyFiberSuccEquiv G 0 ((homotopyFiberSuccEquiv G 0).symm
      ((b.f 0 ((homotopyFiberSuccEquiv F 0)
          ((HomologicalComplex.homotopyFiber F).d 0 1 x)).1),
       (a.f 1 ((homotopyFiberSuccEquiv F 0)
          ((HomologicalComplex.homotopyFiber F).d 0 1 x)).2)))
    rw [LinearEquiv.apply_symm_apply, homotopyFiberZeroEquiv_d]
    exact Prod.ext (hs 0 _) (ha 0 1 _)
  | succ n =>
    apply (homotopyFiberSuccEquiv G (n + 1)).injective
    change homotopyFiberSuccEquiv G (n + 1)
      ((HomologicalComplex.homotopyFiber G).d (n + 1) (n + 2)
        ((homotopyFiberSuccEquiv G n).symm
          (b.f n (homotopyFiberSuccEquiv F n x).1,
            a.f (n + 1) (homotopyFiberSuccEquiv F n x).2))) = _
    rw [homotopyFiberSuccEquiv_d, LinearEquiv.apply_symm_apply]
    change _ = homotopyFiberSuccEquiv G (n + 1) ((homotopyFiberSuccEquiv G (n + 1)).symm
      (b.f (n + 1) ((homotopyFiberSuccEquiv F (n + 1))
          ((HomologicalComplex.homotopyFiber F).d (n + 1) (n + 2) x)).1,
        a.f (n + 2) ((homotopyFiberSuccEquiv F (n + 1))
          ((HomologicalComplex.homotopyFiber F).d (n + 1) (n + 2) x)).2))
    rw [LinearEquiv.apply_symm_apply, homotopyFiberSuccEquiv_d]
    apply Prod.ext
    · change G.f (n + 1) (a.f (n + 1) _) - D'.d n (n + 1) (b.f n _) = _
      rw [hs, hb, map_sub]
    · exact ha (n + 1) (n + 2) _

/-- Degree zero of the induced fiber map is the original source map. -/
theorem homotopyFiberZeroEquiv_map
    {R : Type} [CommRing R] {C D C' D' : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (G : C' ⟶ D') (a : C ⟶ C') (b : D ⟶ D')
    (h : F ≫ b = a ≫ G) (x : (HomologicalComplex.homotopyFiber F).X 0) :
    homotopyFiberZeroEquiv G ((homotopyFiberMap F G a b h).f 0 x) =
      a.f 0 (homotopyFiberZeroEquiv F x) :=
  (homotopyFiberZeroEquiv G).apply_symm_apply _

/-- In positive degrees the induced native fiber map acts on both specified summands. -/
theorem homotopyFiberSuccEquiv_map
    {R : Type} [CommRing R] {C D C' D' : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (G : C' ⟶ D') (a : C ⟶ C') (b : D ⟶ D')
    (h : F ≫ b = a ≫ G) (n : ℕ) (x : (HomologicalComplex.homotopyFiber F).X (n + 1)) :
    homotopyFiberSuccEquiv G n ((homotopyFiberMap F G a b h).f (n + 1) x) =
      (b.f n (homotopyFiberSuccEquiv F n x).1,
        a.f (n + 1) (homotopyFiberSuccEquiv F n x).2) :=
  (homotopyFiberSuccEquiv G n).apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A map of exact augmented nonnegative cochain rows is a quasi-isomorphism on
its augmentation if it is a quasi-isomorphism in every positive column. -/
theorem homologyMap_bijective_of_exact_rows (R : Type) [CommRing R]
    (C D : ℕ → CochainComplex (ModuleCat.{u} R) ℕ)
    (δC : ∀ i, C i ⟶ C (i + 1)) (δD : ∀ i, D i ⟶ D (i + 1))
    (hsqC : ∀ i, δC i ≫ δC (i + 1) = 0)
    (hsqD : ∀ i, δD i ≫ δD (i + 1) = 0)
    (hrowC : ∀ i q, Function.Exact ((δC i).f q) ((δC (i + 1)).f q))
    (hrowD : ∀ i q, Function.Exact ((δD i).f q) ((δD (i + 1)).f q))
    (hmonoC : ∀ q, Function.Injective ((δC 0).f q))
    (hmonoD : ∀ q, Function.Injective ((δD 0).f q))
    (F : ∀ i, C i ⟶ D i) (hcomm : ∀ i, F i ≫ δD i = δC i ≫ F (i + 1))
    (hlocal : ∀ i, 1 ≤ i → ∀ n,
      Function.Bijective (HomologicalComplex.homologyMap (F i) n)) :
    ∀ n, Function.Bijective (HomologicalComplex.homologyMap (F 0) n) := by
  let K (i : ℕ) := HomologicalComplex.homotopyFiber (F i)
  let δ (i : ℕ) : K i ⟶ K (i + 1) :=
    homotopyFiberMap (F i) (F (i + 1)) (δC i) (δD i) (hcomm i)
  have hzero (i : ℕ) (x : (K i).X 0) :
      homotopyFiberZeroEquiv (F (i + 1)) ((δ i).f 0 x) =
        (δC i).f 0 (homotopyFiberZeroEquiv (F i) x) :=
    homotopyFiberZeroEquiv_map _ _ _ _ _ _
  have hsucc (i q : ℕ) (x : (K i).X (q + 1)) :
      homotopyFiberSuccEquiv (F (i + 1)) q ((δ i).f (q + 1) x) =
        ((δD i).f q (homotopyFiberSuccEquiv (F i) q x).1,
          (δC i).f (q + 1) (homotopyFiberSuccEquiv (F i) q x).2) :=
    homotopyFiberSuccEquiv_map _ _ _ _ _ _ _
  have hcc (i q : ℕ) (x : (C i).X q) :
      (δC (i + 1)).f q ((δC i).f q x) = 0 :=
    congrArg (fun f ↦ f.f q x) (hsqC i)
  have hdd (i q : ℕ) (x : (D i).X q) :
      (δD (i + 1)).f q ((δD i).f q x) = 0 :=
    congrArg (fun f ↦ f.f q x) (hsqD i)
  -- The same source and target rows give the exact rows of the native fibers.
  have hsq (i : ℕ) : δ i ≫ δ (i + 1) = 0 := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (δ (i + 1)).f q ((δ i).f q x) = 0
    cases q with
    | zero =>
      apply (homotopyFiberZeroEquiv (F (i + 2))).injective
      rw [hzero, hzero, map_zero]
      exact hcc i 0 _
    | succ q =>
      apply (homotopyFiberSuccEquiv (F (i + 2)) q).injective
      rw [hsucc, hsucc, map_zero]
      exact Prod.ext (hdd i q _) (hcc i (q + 1) _)
  have hrow (i q : ℕ) : Function.Exact ((δ i).f q) ((δ (i + 1)).f q) := by
    intro x
    constructor
    · intro hx
      cases q with
      | zero =>
        have hc := congrArg (homotopyFiberZeroEquiv (F (i + 2))) hx
        rw [hzero, map_zero] at hc
        obtain ⟨c, hc⟩ := (hrowC i 0 _).mp hc
        refine ⟨(homotopyFiberZeroEquiv (F i)).symm c, ?_⟩
        apply (homotopyFiberZeroEquiv (F (i + 1))).injective
        rw [hzero, LinearEquiv.apply_symm_apply]
        exact hc
      | succ q =>
        have hcoord := congrArg (homotopyFiberSuccEquiv (F (i + 2)) q) hx
        rw [hsucc, map_zero] at hcoord
        obtain ⟨y, hy⟩ := (hrowD i q _).mp (congrArg Prod.fst hcoord)
        obtain ⟨c, hc⟩ := (hrowC i (q + 1) _).mp (congrArg Prod.snd hcoord)
        refine ⟨(homotopyFiberSuccEquiv (F i) q).symm (y, c), ?_⟩
        apply (homotopyFiberSuccEquiv (F (i + 1)) q).injective
        rw [hsucc, LinearEquiv.apply_symm_apply]
        exact Prod.ext hy hc
    · rintro ⟨y, rfl⟩
      exact congrArg (fun f ↦ f.f q y) (hsq i)
  have hmono (q : ℕ) : Function.Injective ((δ 0).f q) := by
    intro x y hxy
    cases q with
    | zero =>
      apply (homotopyFiberZeroEquiv (F 0)).injective
      apply hmonoC 0
      have hcoord := congrArg (homotopyFiberZeroEquiv (F 1)) hxy
      rwa [hzero, hzero] at hcoord
    | succ q =>
      apply (homotopyFiberSuccEquiv (F 0) q).injective
      have hcoord := congrArg (homotopyFiberSuccEquiv (F 1) q) hxy
      rw [hsucc, hsucc] at hcoord
      exact Prod.ext (hmonoD q (congrArg Prod.fst hcoord))
        (hmonoC (q + 1) (congrArg Prod.snd hcoord))
  -- Quasi-isomorphisms in the later columns make their native fibers acyclic.
  have hvan (i : ℕ) (hi : 1 ≤ i) (q : ℕ) :
      Function.Exact ((K i).d (q - 1) q) ((K i).d q (q + 1)) :=
    (homologyMap_bijective_iff_exact_homotopyFiber (F i)).mp (hlocal i hi) q
  have hprev (n : ℕ) : (ComplexShape.up ℕ).prev n = n - 1 := by
    cases n <;> simp [CochainComplex.prev_nat_zero, CochainComplex.prev_nat_succ]
  have hexact (B : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
      Function.Exact (B.d (n - 1) n) (B.d n (n + 1)) ↔ B.ExactAt n := by
    rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
    change Function.Exact (B.d (n - 1) n) (B.d n (n + 1)) ↔
      ∀ x : B.X n, B.d n ((ComplexShape.up ℕ).next n) x = 0 →
        ∃ y : B.X ((ComplexShape.up ℕ).prev n),
          B.d ((ComplexShape.up ℕ).prev n) n y = x
    rw [hprev, CochainComplex.next]
    constructor
    · intro h x hx
      exact (h x).mp hx
    · intro h x
      constructor
      · exact h x
      · rintro ⟨y, rfl⟩
        exact congrArg (fun f ↦ f y) (B.d_comp_d (n - 1) n (n + 1))
  apply (homologyMap_bijective_iff_exact_homotopyFiber (F 0)).mpr
  intro n
  apply (hexact (K 0) n).mpr
  apply (HomologicalComplex.exactAt_iff_isZero_homology (K 0) n).mpr
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have hzeroOne : CategoryTheory.Limits.IsZero ((K 1).homology n) :=
    ((hexact (K 1) n).mp (hvan 1 (by omega) n)).isZero_homology
  have : Subsingleton ((K 1).homology n) := ModuleCat.subsingleton_of_isZero hzeroOne
  -- Finite descent at this degree identifies augmented cohomology with the zero group.
  obtain ⟨z, _, hz⟩ := existsUnique_cohomology_of_exact_rows R K δ hsq hrow hmono n
    (fun i hi q _ ↦ hvan i (by omega) q) 0 (map_zero _)
  exact ⟨fun x y ↦ (hz x (Subsingleton.elim _ _)).trans
    (hz y (Subsingleton.elim _ _)).symm⟩

end AtiyahSinger
