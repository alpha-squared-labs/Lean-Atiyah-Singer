/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic

/-!
# Descent in the first nonzero cohomological degree

Public module ID: M0003.

An augmented sequence of nonnegative cochain complexes has exact rows.
If the overlap columns vanish below degree n, its degree-n cohomology
identifies with the kernel of the induced map from the first to the second
nonaugmentation column. The proof eliminates
the finitely many obstructions one degree at a time, so it uses no
convergence or inverse-limit assumption.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Exact augmented rows and lower-degree overlap vanishing give unique cohomology gluing. -/
theorem existsUnique_cohomology_of_exact_rows (R : Type) [CommRing R]
    (C : ℕ → CochainComplex (ModuleCat.{u} R) ℕ)
    (δ : ∀ i, C i ⟶ C (i + 1)) (hsq : ∀ i, δ i ≫ δ (i + 1) = 0)
    (hrow : ∀ i q, Function.Exact ((δ i).f q) ((δ (i + 1)).f q))
    (hmono : ∀ q, Function.Injective ((δ 0).f q))
    (n : ℕ) (hvan : ∀ i, 2 ≤ i → ∀ q, q < n →
      Function.Exact ((C i).d (q - 1) q) ((C i).d q (q + 1)))
    (a : (C 1).homology n) (ha : HomologicalComplex.homologyMap (δ 1) n a = 0) :
    ∃! z : (C 0).homology n, HomologicalComplex.homologyMap (δ 0) n z = a := by
  have hδδ (i q : ℕ) (x : (C i).X q) :
      (δ (i + 1)).f q ((δ i).f q x) = 0 :=
    congrArg (fun F ↦ F.f q x) (hsq i)
  have hcomm (i p q : ℕ) (x : (C i).X p) :
      (C (i + 1)).d p q ((δ i).f p x) = (δ i).f q ((C i).d p q x) :=
    congrArg (fun f ↦ f x) ((δ i).comm p q)
  have hdd (i p q k : ℕ) (x : (C i).X p) :
      (C i).d q k ((C i).d p q x) = 0 :=
    congrArg (fun f ↦ f x) ((C i).d_comp_d p q k)
  -- Move a primitive one column to the left, modulo a vertical boundary.
  -- The recursion stops in degree zero, where an exact cocycle is literally zero.
  have hlift (q : ℕ) (hq : q < n) : ∀ i,
      (b : (C (i + 1)).X q) →
      (δ (i + 1)).f (q + 1) ((C (i + 1)).d q (q + 1) b) = 0 →
      ∃ x : (C i).X q, ∃ y : (C (i + 1)).X (q - 1),
        b = (δ i).f q x + (C (i + 1)).d (q - 1) q y := by
    induction q with
    | zero =>
      intro i b hb
      have hclosed : (C (i + 2)).d 0 1 ((δ (i + 1)).f 0 b) = 0 :=
        (hcomm (i + 1) 0 1 b).trans hb
      obtain ⟨y, hy⟩ := (hvan (i + 2) (by omega) 0 hq _).mp hclosed
      have hzero : (δ (i + 1)).f 0 b = 0 := by
        rw [← hy]
        have hd : (C (i + 2)).d 0 0 = 0 := (C (i + 2)).shape 0 0 (by simp)
        rw [hd]
        rfl
      obtain ⟨x, hx⟩ := (hrow i 0 b).mp hzero
      refine ⟨x, 0, ?_⟩
      simpa using hx.symm
    | succ q ih =>
      intro i b hb
      have hclosed : (C (i + 2)).d (q + 1) (q + 2) ((δ (i + 1)).f (q + 1) b) = 0 :=
        (hcomm (i + 1) (q + 1) (q + 2) b).trans hb
      obtain ⟨c, hc⟩ := (hvan (i + 2) (by omega) (q + 1) hq _).mp hclosed
      have hrel : (C (i + 2)).d q (q + 1) c = (δ (i + 1)).f (q + 1) b := by
        simpa using hc
      have hcclosed : (δ (i + 2)).f (q + 1) ((C (i + 2)).d q (q + 1) c) = 0 := by
        rw [hrel]
        exact hδδ (i + 1) (q + 1) b
      obtain ⟨x, y, hxy⟩ := ih (by omega) (i + 1) c hcclosed
      have hz : (δ (i + 1)).f (q + 1) (b - (C (i + 1)).d q (q + 1) x) = 0 := by
        rw [map_sub, ← hcomm (i + 1) q (q + 1) x, ← hrel, hxy, map_add,
          hdd, add_zero, sub_self]
      obtain ⟨z, hz'⟩ := (hrow i (q + 1) _).mp hz
      refine ⟨z, x, ?_⟩
      simpa using (sub_eq_iff_eq_add.mp hz'.symm)
  -- Representatives in the original cycle quotient turn gluing into the preceding finite chase.
  have hmap (B D : CochainComplex (ModuleCat.{u} R) ℕ) (F : B ⟶ D) (k : ℕ)
      (b : (B.sc k).moduleCatLeftHomologyData.K)
      (c : (D.sc k).moduleCatLeftHomologyData.K) (h : F.f k b.val = c.val) :
      HomologicalComplex.homologyMap F k
          ((B.sc k).moduleCatHomologyIso.inv ((B.sc k).moduleCatToCycles.range.mkQ b)) =
        (D.sc k).moduleCatHomologyIso.inv ((D.sc k).moduleCatToCycles.range.mkQ c) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) k).map F
    let G := ShortComplex.leftHomologyMapData S
      (B.sc k).moduleCatLeftHomologyData (D.sc k).moduleCatLeftHomologyData
    have hcycles : G.φK b = c := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f b) G.commi).trans h
    have hquot := congrArg (fun f ↦ f b) G.commπ
    change G.φH ((B.sc k).moduleCatToCycles.range.mkQ b) =
      (D.sc k).moduleCatToCycles.range.mkQ (G.φK b) at hquot
    rw [hcycles] at hquot
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F k = _ at hmap
    rw [hmap]
    change (D.sc k).moduleCatHomologyIso.inv
      (G.φH ((B.sc k).moduleCatHomologyIso.hom
        ((B.sc k).moduleCatHomologyIso.inv ((B.sc k).moduleCatToCycles.range.mkQ b)))) = _
    have hcancel : (B.sc k).moduleCatHomologyIso.hom
        ((B.sc k).moduleCatHomologyIso.inv ((B.sc k).moduleCatToCycles.range.mkQ b)) =
          (B.sc k).moduleCatToCycles.range.mkQ b :=
      congrArg (fun f ↦ f ((B.sc k).moduleCatToCycles.range.mkQ b))
        (B.sc k).moduleCatHomologyIso.inv_hom_id
    rw [hcancel, hquot]
  let cc (i k : ℕ) (c : ((C i).sc k).moduleCatLeftHomologyData.K) : (C i).homology k :=
    ((C i).sc k).moduleCatHomologyIso.inv (((C i).sc k).moduleCatToCycles.range.mkQ c)
  have hprev (k : ℕ) : (ComplexShape.up ℕ).prev k = k - 1 := by
    cases k <;> simp [CochainComplex.prev_nat_zero, CochainComplex.prev_nat_succ]
  have hzero (i k : ℕ) (c : ((C i).sc k).moduleCatLeftHomologyData.K) :
      cc i k c = 0 ↔ ∃ b : (C i).X (k - 1), (C i).d (k - 1) k b = c.val := by
    let S := (C i).sc k
    rw [← hprev k]
    change S.moduleCatHomologyIso.toLinearEquiv.symm (S.moduleCatToCycles.range.mkQ c) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact (Submodule.Quotient.mk_eq_zero _).trans
      (exists_congr fun b ↦ Subtype.ext_iff)
  have hrep (i k : ℕ) (z : (C i).homology k) :
      ∃ c : ((C i).sc k).moduleCatLeftHomologyData.K, cc i k c = z := by
    exact (((C i).sc k).moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
      ((C i).sc k).moduleCatToCycles.range.mkQ_surjective) z
  have hclosed (i k : ℕ) (c : ((C i).sc k).moduleCatLeftHomologyData.K) :
      (C i).d k (k + 1) c.val = 0 := by
    have h : (C i).d k ((ComplexShape.up ℕ).next k) c.val = 0 := c.property
    exact (congrArg (fun j ↦ (C i).d k j c.val = 0) (CochainComplex.next ℕ k)).mp h
  have hcycle (i k : ℕ) (c : (C i).X k) (hc : (C i).d k (k + 1) c = 0) :
      c ∈ (((C i).sc k).g).hom.ker := by
    change (C i).d k ((ComplexShape.up ℕ).next k) c = 0
    exact (congrArg (fun j ↦ (C i).d k j c = 0) (CochainComplex.next ℕ k)).mpr hc
  have hmapClosed (i k : ℕ) (c : ((C i).sc k).moduleCatLeftHomologyData.K) :
      (C (i + 1)).d k (k + 1) ((δ i).f k c.val) = 0 := by
    rw [hcomm, hclosed, map_zero]
  have hclassSub (i k : ℕ) (c d : ((C i).sc k).moduleCatLeftHomologyData.K) :
      cc i k (c - d) = cc i k c - cc i k d := by
    dsimp only [cc]
    rw [map_sub, map_sub]
  -- Injectivity follows by lifting a local primitive and using the injective augmentation.
  have hinj : Function.Injective (HomologicalComplex.homologyMap (δ 0) n) := by
    have hker (z : (C 0).homology n)
        (hz : HomologicalComplex.homologyMap (δ 0) n z = 0) : z = 0 := by
      obtain ⟨c, rfl⟩ := hrep 0 n z
      let c₁ : ((C 1).sc n).moduleCatLeftHomologyData.K :=
        ⟨(δ 0).f n c.val, hcycle 1 n _ (hmapClosed 0 n c)⟩
      have hmc : HomologicalComplex.homologyMap (δ 0) n (cc 0 n c) = cc 1 n c₁ :=
        hmap _ _ (δ 0) n c c₁ rfl
      obtain ⟨b, hb⟩ := (hzero 1 n c₁).mp (hmc.symm.trans hz)
      cases n with
      | zero =>
        have hdb : (C 1).d 0 0 = 0 := (C 1).shape 0 0 (by simp)
        have hc0 : (δ 0).f 0 c.val = 0 := by
          change (C 1).d 0 0 b = (δ 0).f 0 c.val at hb
          exact hb.symm.trans (congrArg (fun f ↦ f b) hdb)
        have hc : c.val = 0 := hmono 0 (hc0.trans (map_zero _).symm)
        apply (hzero 0 0 c).mpr
        exact ⟨0, (map_zero _).trans hc.symm⟩
      | succ k =>
        change (C 1).d k (k + 1) b = (δ 0).f (k + 1) c.val at hb
        have hbclosed : (δ 1).f (k + 1) ((C 1).d k (k + 1) b) = 0 := by
          rw [hb]
          exact hδδ 0 (k + 1) c.val
        obtain ⟨x, y, hxy⟩ := hlift k (by omega) 0 b hbclosed
        have hx : (C 0).d k (k + 1) x = c.val := by
          apply hmono (k + 1)
          rw [← hcomm, ← hb, hxy, map_add, hdd, add_zero]
        exact (hzero 0 (k + 1) c).mpr ⟨x, hx⟩
    intro z w h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, h, sub_self]
  obtain ⟨c, rfl⟩ := hrep 1 n a
  let c₂ : ((C 2).sc n).moduleCatLeftHomologyData.K :=
    ⟨(δ 1).f n c.val, hcycle 2 n _ (hmapClosed 1 n c)⟩
  have hmc : HomologicalComplex.homologyMap (δ 1) n (cc 1 n c) = cc 2 n c₂ :=
    hmap _ _ (δ 1) n c c₂ rfl
  obtain ⟨b, hb⟩ := (hzero 2 n c₂).mp (hmc.symm.trans ha)
  -- Correct the local cocycle by a boundary until its restrictions agree as cochains.
  have hex : ∃ z : ((C 0).sc n).moduleCatLeftHomologyData.K,
      HomologicalComplex.homologyMap (δ 0) n (cc 0 n z) = cc 1 n c := by
    cases n with
    | zero =>
      have hd : (C 2).d 0 0 = 0 := (C 2).shape 0 0 (by simp)
      have hc0 : (δ 1).f 0 c.val = 0 := by
        change (C 2).d 0 0 b = (δ 1).f 0 c.val at hb
        exact hb.symm.trans (congrArg (fun f ↦ f b) hd)
      obtain ⟨z, hz⟩ := (hrow 0 0 c.val).mp hc0
      have hzclosed : (C 0).d 0 1 z = 0 := by
        apply hmono 1
        rw [← hcomm, hz, hclosed, map_zero]
      refine ⟨⟨z, hcycle 0 _ z hzclosed⟩, ?_⟩
      exact hmap _ _ (δ 0) 0 ⟨z, hcycle 0 _ z hzclosed⟩ c hz
    | succ k =>
      change (C 2).d k (k + 1) b = (δ 1).f (k + 1) c.val at hb
      have hbclosed : (δ 2).f (k + 1) ((C 2).d k (k + 1) b) = 0 := by
        rw [hb]
        exact hδδ 1 (k + 1) c.val
      obtain ⟨x, y, hxy⟩ := hlift k (by omega) 1 b hbclosed
      have hc0 : (δ 1).f (k + 1) ((show (C 1).X (k + 1) from c.val) - (C 1).d k (k + 1) x) = 0 := by
        rw [map_sub, ← hcomm, ← hb, hxy, map_add, hdd, add_zero, sub_self]
      obtain ⟨z, hz⟩ := (hrow 0 (k + 1) _).mp hc0
      have hzclosed : (C 0).d (k + 1) (k + 2) z = 0 := by
        apply hmono (k + 2)
        rw [← hcomm, hz, map_sub, hclosed, hdd, sub_self, map_zero]
      let z₀ : ((C 0).sc (k + 1)).moduleCatLeftHomologyData.K := ⟨z, hcycle 0 _ z hzclosed⟩
      let z₁ : ((C 1).sc (k + 1)).moduleCatLeftHomologyData.K :=
        ⟨(δ 0).f (k + 1) z, hcycle 1 _ _ (hmapClosed 0 (k + 1) z₀)⟩
      refine ⟨z₀, (hmap _ _ (δ 0) (k + 1) z₀ z₁ rfl).trans ?_⟩
      apply sub_eq_zero.mp
      rw [← hclassSub]
      apply (hzero 1 (k + 1) (z₁ - c)).mpr
      refine ⟨-x, ?_⟩
      change (C 1).d k (k + 1) (-x) = (δ 0).f (k + 1) z - (show (C 1).X (k + 1) from c.val)
      rw [map_neg, hz]
      abel
  obtain ⟨z, hz⟩ := hex
  exact ⟨cc 0 n z, hz, fun w hw ↦ hinj (hw.trans hz.symm)⟩

end AtiyahSinger
