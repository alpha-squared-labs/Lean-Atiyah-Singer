/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import AtiyahSinger.Topology.SingularSmallChains
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Chain homotopy methods for singular excision

Public module ID: M2090.

The small-chain quotient is contracted using subdivision: subdivision is
homotopic to the identity, and its induced endomorphism on the quotient is
locally nilpotent. Finite geometric sums then invert identity minus subdivision.
This supplies a genuine contraction over the original coefficient ring.

The algebraic lemmas below retain actual chain maps and homotopies. They are
used with the original free singular-simplex modules, without substituting a
different model of relative cohomology or dualizing a mere quasi-isomorphism.
The geometric smallness and relative quotient comparisons remain separate steps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

universe u v w

/-- A locally nilpotent endomorphism has invertible difference from the identity. -/
theorem bijective_one_sub_of_locally_nilpotent
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (f : Module.End R M) (hf : ∀ x : M, ∃ n : ℕ, (f ^ n) x = 0) :
    Function.Bijective (1 - f : Module.End R M) := by
  constructor
  · -- The geometric sum annihilates a vector fixed by f only when that vector is zero.
    intro x y h
    obtain ⟨n, hn⟩ := hf (x - y)
    have hz : (1 - f) (x - y) = 0 := by
      rw [map_sub, h, sub_self]
    have heq := congrArg (fun g : Module.End R M ↦ g (x - y)) (geom_sum_mul_neg f n)
    have hxy : x - y = 0 := by
      simpa only [Module.End.mul_apply, hz, map_zero, LinearMap.sub_apply,
        Module.End.one_apply, hn, sub_zero] using heq.symm
    exact sub_eq_zero.mp hxy
  · -- Each vector has its own finite geometric preimage; no uniform exponent is required.
    intro y
    obtain ⟨n, hn⟩ := hf y
    refine ⟨(∑ k ∈ Finset.range n, f ^ k) y, ?_⟩
    have heq := congrArg (fun g : Module.End R M ↦ g y) (mul_neg_geom_sum f n)
    simpa only [Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hn, sub_zero] using heq

/-- A locally nilpotent chain map homotopic to the identity contracts its complex. -/
theorem contractible_of_homotopy_id_of_locally_nilpotent
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (f : C ⟶ C)
    (h : Homotopy (𝟙 C) f)
    (hf : ∀ n (x : C.X n), ∃ k : ℕ, ((f.f n).hom ^ k) x = 0) :
    Nonempty (Homotopy (𝟙 C) 0) := by
  -- Finite geometric sums show invertibility in every original module degree.
  have (n : ι) : IsIso ((𝟙 C - f).f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact bijective_one_sub_of_locally_nilpotent (f.f n).hom (hf n)
  have : IsIso (𝟙 C - f) := HomologicalComplex.Hom.isIso_of_components _
  -- The inverse is a chain map, so composing the original homotopy yields a contraction.
  let H : Homotopy (𝟙 C - f) 0 := Homotopy.equivSubZero h
  exact ⟨by simpa only [IsIso.inv_hom_id, comp_zero] using H.compLeft (inv (𝟙 C - f))⟩

/-- A degreewise split inclusion with contractible quotient is a chain homotopy equivalence. -/
theorem homotopyEquivalences_of_degreewiseSplit_of_contractibleCokernel
    {V : Type u} [Category.{v} V] [Preadditive V] {ι : Type w} {c : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex V c))
    (σ : ∀ n, (S.map (HomologicalComplex.eval V c n)).Splitting)
    (h : Homotopy (𝟙 S.X₃) 0) :
    HomologicalComplex.homotopyEquivalences V c S.f := by
  -- Lift the quotient contraction through the prescribed degreewise section.
  let L (n m : ι) : S.X₂.X n ⟶ S.X₂.X m :=
    S.g.f n ≫ h.hom n m ≫ (σ m).s
  have hLzero (n m : ι) (hnm : ¬c.Rel m n) : L n m = 0 := by
    simp [L, h.zero n m hnm]
  have hnull : Homotopy.nullHomotopicMap h.hom = 𝟙 S.X₃ := by
    ext n : 1
    simpa only [Homotopy.nullHomotopicMap, HomologicalComplex.zero_f_apply, add_zero]
      using (h.comm n).symm
  have hLq : Homotopy.nullHomotopicMap L ≫ S.g = S.g := by
    rw [Homotopy.nullHomotopicMap_comp]
    have hfamily : (fun n m ↦ L n m ≫ S.g.f m) =
        (fun n m ↦ S.g.f n ≫ h.hom n m) := by
      funext n m
      dsimp only [L]
      rw [Category.assoc, Category.assoc]
      have hs : (σ m).s ≫ S.g.f m = 𝟙 (S.X₃.X m) := (σ m).s_g
      rw [hs, Category.comp_id]
    rw [hfamily, ← Homotopy.comp_nullHomotopicMap, hnull, Category.comp_id]
  let e : S.X₂ ⟶ S.X₂ := 𝟙 S.X₂ - Homotopy.nullHomotopicMap L
  have heq : e ≫ S.g = 0 := by
    dsimp only [e]
    rw [Preadditive.sub_comp, Category.id_comp, hLq, sub_self]
  -- The correction is zero on the original subcomplex, so it fixes its inclusion.
  have hfi : S.f ≫ e = S.f := by
    dsimp only [e]
    rw [Preadditive.comp_sub, Category.comp_id, Homotopy.comp_nullHomotopicMap]
    have hfamily : (fun n m ↦ S.f.f n ≫ L n m) = (fun n m ↦ 0) := by
      funext n m
      dsimp only [L]
      have hfg : S.f.f n ≫ S.g.f n = 0 :=
        congrArg (fun f ↦ f.f n) S.zero
      rw [← Category.assoc, hfg, zero_comp]
    rw [hfamily]
    have hz : Homotopy.nullHomotopicMap (fun n m ↦ (0 : S.X₁.X n ⟶ S.X₂.X m)) = 0 := by
      ext n : 1
      simp [Homotopy.nullHomotopicMap, dNext, prevD]
    rw [hz, sub_zero]
  -- Its image lies in the kernel of the quotient map, hence in the same included complex.
  have hr (n : ι) : (e.f n ≫ (σ n).r) ≫ S.f.f n = e.f n := by
    have hsplit : (σ n).r ≫ S.f.f n = 𝟙 _ - S.g.f n ≫ (σ n).s := (σ n).r_f
    have hzero : e.f n ≫ S.g.f n = 0 := congrArg (fun f ↦ f.f n) heq
    rw [Category.assoc, hsplit, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, hzero, zero_comp, sub_zero]
  let r : S.X₂ ⟶ S.X₁ :=
    { f := fun n ↦ e.f n ≫ (σ n).r
      comm' := by
        intro n m hnm
        have : Mono (S.f.f m) := (σ m).mono_f
        apply (cancel_mono (S.f.f m)).mp
        change ((e.f n ≫ (σ n).r) ≫ S.X₁.d n m) ≫ S.f.f m =
          (S.X₂.d n m ≫ e.f m ≫ (σ m).r) ≫ S.f.f m
        calc
          _ = ((e.f n ≫ (σ n).r) ≫ S.f.f n) ≫ S.X₂.d n m := by
            rw [Category.assoc, ← S.f.comm n m, ← Category.assoc]
          _ = e.f n ≫ S.X₂.d n m := by rw [hr n]
          _ = S.X₂.d n m ≫ e.f m := e.comm n m
          _ = _ := by
            simpa only [Category.assoc] using
              congrArg (fun f ↦ S.X₂.d n m ≫ f) (hr m).symm }
  have hrf : r ≫ S.f = e := by
    ext n : 1
    exact hr n
  have hfr : S.f ≫ r = 𝟙 S.X₁ := by
    ext n : 1
    have hfix : S.f.f n ≫ e.f n = S.f.f n := congrArg (fun f ↦ f.f n) hfi
    change S.f.f n ≫ e.f n ≫ (σ n).r = 𝟙 _
    rw [← Category.assoc, hfix]
    exact (σ n).f_r
  -- The lifted homotopy operator supplies the second inverse identity up to homotopy.
  have he : Homotopy e (𝟙 S.X₂) := by
    have H := (Homotopy.refl (𝟙 S.X₂)).add
      ((Homotopy.nullHomotopy L hLzero).smul (-1 : ℤ))
    simpa only [e, neg_one_zsmul, add_zero, neg_zero, sub_eq_add_neg] using H
  exact ⟨⟨S.f, r, Homotopy.ofEq hfr, (Homotopy.ofEq hrf).trans he⟩, rfl⟩

/-- A degreewise split quotient with contractible kernel is a chain homotopy equivalence. -/
theorem homotopyEquivalences_of_degreewiseSplit_of_contractibleKernel
    {V : Type u} [Category.{v} V] [Preadditive V] {ι : Type w} {c : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex V c))
    (σ : ∀ n, (S.map (HomologicalComplex.eval V c n)).Splitting)
    (h : Homotopy (𝟙 S.X₁) 0) :
    HomologicalComplex.homotopyEquivalences V c S.g := by
  -- Extend the kernel contraction using the prescribed degreewise retraction.
  let L (n m : ι) : S.X₂.X n ⟶ S.X₂.X m :=
    (σ n).r ≫ h.hom n m ≫ S.f.f m
  have hLzero (n m : ι) (hnm : ¬c.Rel m n) : L n m = 0 := by
    simp [L, h.zero n m hnm]
  have hnull : Homotopy.nullHomotopicMap h.hom = 𝟙 S.X₁ := by
    ext n : 1
    simpa only [Homotopy.nullHomotopicMap, HomologicalComplex.zero_f_apply, add_zero]
      using (h.comm n).symm
  have hfL : S.f ≫ Homotopy.nullHomotopicMap L = S.f := by
    rw [Homotopy.comp_nullHomotopicMap]
    have hfamily : (fun n m ↦ S.f.f n ≫ L n m) =
        (fun n m ↦ h.hom n m ≫ S.f.f m) := by
      funext n m
      dsimp only [L]
      have hr : S.f.f n ≫ (σ n).r = 𝟙 (S.X₁.X n) := (σ n).f_r
      rw [← Category.assoc, hr, Category.id_comp]
    rw [hfamily, ← Homotopy.nullHomotopicMap_comp, hnull, Category.id_comp]
  let e : S.X₂ ⟶ S.X₂ := 𝟙 S.X₂ - Homotopy.nullHomotopicMap L
  have hfe : S.f ≫ e = 0 := by
    dsimp only [e]
    rw [Preadditive.comp_sub, Category.comp_id, hfL, sub_self]
  -- The correction lies in the original kernel and disappears after the quotient.
  have heg : e ≫ S.g = S.g := by
    dsimp only [e]
    rw [Preadditive.sub_comp, Category.id_comp, Homotopy.nullHomotopicMap_comp]
    have hfamily : (fun n m ↦ L n m ≫ S.g.f m) = (fun n m ↦ 0) := by
      funext n m
      dsimp only [L]
      have hfg : S.f.f m ≫ S.g.f m = 0 :=
        congrArg (fun f ↦ f.f m) S.zero
      rw [Category.assoc, Category.assoc, hfg, comp_zero, comp_zero]
    rw [hfamily]
    have hz : Homotopy.nullHomotopicMap (fun n m ↦ (0 : S.X₂.X n ⟶ S.X₃.X m)) = 0 := by
      ext n : 1
      simp [Homotopy.nullHomotopicMap, dNext, prevD]
    rw [hz, sub_zero]
  -- Correcting the original degreewise section now makes it a genuine chain map.
  have hs (n : ι) : S.g.f n ≫ (σ n).s ≫ e.f n = e.f n := by
    have hsplit := (σ n).g_s
    dsimp only [ShortComplex.map, HomologicalComplex.eval] at hsplit
    have hzero : S.f.f n ≫ e.f n = 0 := congrArg (fun f ↦ f.f n) hfe
    rw [← Category.assoc, hsplit, Preadditive.sub_comp, Category.id_comp,
      Category.assoc, hzero, comp_zero, sub_zero]
  let s : S.X₃ ⟶ S.X₂ :=
    { f := fun n ↦ (σ n).s ≫ e.f n
      comm' := by
        intro n m hnm
        have : Epi (S.g.f n) := (σ n).epi_g
        apply (cancel_epi (S.g.f n)).mp
        calc
          _ = e.f n ≫ S.X₂.d n m := by rw [← Category.assoc, hs n]
          _ = S.X₂.d n m ≫ e.f m := e.comm n m
          _ = _ := by
            rw [← Category.assoc, S.g.comm n m, Category.assoc, hs m] }
  have hgs : S.g ≫ s = e := by
    ext n : 1
    exact hs n
  have hsg : s ≫ S.g = 𝟙 S.X₃ := by
    ext n : 1
    have hfix : e.f n ≫ S.g.f n = S.g.f n := congrArg (fun f ↦ f.f n) heg
    change ((σ n).s ≫ e.f n) ≫ S.g.f n = 𝟙 _
    rw [Category.assoc, hfix]
    exact (σ n).s_g
  -- Its failure to be the other strict inverse is precisely the lifted kernel contraction.
  have he : Homotopy e (𝟙 S.X₂) := by
    have H := (Homotopy.refl (𝟙 S.X₂)).add
      ((Homotopy.nullHomotopy L hLzero).smul (-1 : ℤ))
    simpa only [e, neg_one_zsmul, add_zero, neg_zero, sub_eq_add_neg] using H
  exact ⟨⟨S.g, s, (Homotopy.ofEq hgs).trans he, Homotopy.ofEq hsg⟩, rfl⟩

/-- For i : A → B, an endomorphism of B homotopic to identity contracts coker i when it and
its homotopy preserve the image of i and every vector eventually enters that image. -/
theorem contractible_cokernel_of_homotopy_of_eventually_range
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B : HomologicalComplex (ModuleCat.{v} R) c} (i : A ⟶ B)
    (f : B ⟶ B) (h : Homotopy (𝟙 B) f)
    (hf : ∀ n (x : A.X n), f.f n (i.f n x) ∈ (i.f n).hom.range)
    (hh : ∀ n m (x : A.X n), h.hom n m (i.f n x) ∈ (i.f m).hom.range)
    (hevent : ∀ n (x : B.X n), ∃ k : ℕ, ((f.f n).hom ^ k) x ∈ (i.f n).hom.range) :
    Nonempty (Homotopy (𝟙 (cokernel i)) 0) := by
  let q := cokernel.π i
  let Q (n : ι) := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{v} R) c n) i
  have hq (n : ι) : Epi (q.f n) := epi_of_isColimit_cofork (Q n)
  have hzero (n : ι) (x : A.X n) : q.f n (i.f n x) = 0 :=
    congrArg (fun g ↦ g.f n x) (cokernel.condition i)
  -- The original endomorphism descends by the cokernel universal property.
  have hvan : i ≫ f ≫ q = 0 := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change q.f n (f.f n (i.f n x)) = 0
    obtain ⟨y, hy⟩ := hf n x
    rw [← hy]
    exact hzero n y
  let f' : cokernel i ⟶ cokernel i := cokernel.desc i (f ≫ q) hvan
  have hf' : q ≫ f' = f ≫ q := cokernel.π_desc _ _ _
  -- Every component of the original homotopy descends through the same degreewise quotient.
  let lift (n m : ι) := CokernelCofork.IsColimit.desc' (Q n)
    (h.hom n m ≫ q.f m) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change q.f m (h.hom n m (i.f n x)) = 0
      obtain ⟨y, hy⟩ := hh n m x
      rw [← hy]
      exact hzero m y)
  let T (n m : ι) : (cokernel i).X n ⟶ (cokernel i).X m := (lift n m).val
  have hT (n m : ι) : q.f n ≫ T n m = h.hom n m ≫ q.f m := (lift n m).property
  have hTzero (n m : ι) (hnm : ¬c.Rel m n) : T n m = 0 := by
    apply (cancel_epi (q.f n)).mp
    rw [hT, h.zero n m hnm, zero_comp, comp_zero]
  have hnull : Homotopy.nullHomotopicMap h.hom = 𝟙 B - f := by
    ext n : 1
    have hn := h.comm n
    change 𝟙 (B.X n) = (Homotopy.nullHomotopicMap h.hom).f n + f.f n at hn
    exact (eq_sub_iff_add_eq.mpr hn.symm)
  have hnullT : Homotopy.nullHomotopicMap T = 𝟙 (cokernel i) - f' := by
    apply (cancel_epi q).mp
    rw [Homotopy.comp_nullHomotopicMap]
    have hfamily : (fun n m ↦ q.f n ≫ T n m) =
        (fun n m ↦ h.hom n m ≫ q.f m) := funext fun n ↦ funext fun m ↦ hT n m
    rw [hfamily, ← Homotopy.nullHomotopicMap_comp, hnull,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
      Category.comp_id, hf']
  have h' : Homotopy (𝟙 (cokernel i)) f' :=
    Homotopy.equivSubZero.symm
      ((Homotopy.ofEq hnullT.symm).trans (Homotopy.nullHomotopy T hTzero))
  -- Each quotient vector is represented by an original chain and is killed by a finite iterate.
  apply contractible_of_homotopy_id_of_locally_nilpotent (cokernel i) f' h'
  intro n y
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (q.f n)).mp (hq n) y
  have hpow (k : ℕ) (z : B.X n) :
      ((f'.f n).hom ^ k) (q.f n z) = q.f n (((f.f n).hom ^ k) z) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      exact congrArg (fun g ↦ g.f n (((f.f n).hom ^ k) z)) hf'
  obtain ⟨k, z, hz⟩ := hevent n x
  refine ⟨k, ?_⟩
  rw [hpow, ← hz]
  exact hzero n z

/-- For i : A → B and a degreewise split j : B → C, contractibility of coker i makes
coker (i ≫ j) → coker j a homotopy equivalence via the canonical comparison. -/
theorem homotopyEquivalences_cokernel_desc_of_contractible
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c} (i : A ⟶ B) (j : B ⟶ C)
    (hj : ∀ n, IsSplitMono (j.f n)) (h : Homotopy (𝟙 (cokernel i)) 0) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{v} R) c
      (cokernel.desc (i ≫ j) (cokernel.π j) (by simp)) := by
  let p := cokernel.π (i ≫ j)
  let k : cokernel i ⟶ cokernel (i ≫ j) :=
    cokernel.desc i (j ≫ p) (by simp [p, ← Category.assoc])
  let q : cokernel (i ≫ j) ⟶ cokernel j :=
    cokernel.desc (i ≫ j) (cokernel.π j) (by simp)
  have hk : cokernel.π i ≫ k = j ≫ p := cokernel.π_desc _ _ _
  have hq : p ≫ q = cokernel.π j := cokernel.π_desc _ _ _
  have hkq : k ≫ q = 0 := by
    apply (cancel_epi (cokernel.π i)).mp
    rw [← Category.assoc, hk, Category.assoc, hq, cokernel.condition, comp_zero]
  let S := ShortComplex.mk k q hkq
  have : Epi q := epi_of_epi_fac hq
  -- The same universal quotient square identifies q as the cokernel of k.
  have hQ : IsColimit (CokernelCofork.ofπ q hkq) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro T u hu
    have hju : j ≫ p ≫ u = 0 := by
      rw [← Category.assoc, ← hk, Category.assoc, hu, comp_zero]
    refine ⟨cokernel.desc j (p ≫ u) hju, ?_⟩
    apply (cancel_epi p).mp
    rw [← Category.assoc, hq, cokernel.π_desc]
  have hExact : S.Exact := S.exact_of_g_is_cokernel hQ
  -- Each retraction of j descends to a retraction on these same quotient modules.
  let Qi (n : ι) := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{v} R) c n) i
  let Qij (n : ι) := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{v} R) c n) (i ≫ j)
  have hsplit (n : ι) : (S.map (HomologicalComplex.eval (ModuleCat.{v} R) c n)).Splitting := by
    have : IsSplitMono (j.f n) := hj n
    let r := retraction (j.f n)
    have hjr : j.f n ≫ r = 𝟙 (B.X n) := IsSplitMono.id _
    have hvan : (i ≫ j).f n ≫ (r ≫ (cokernel.π i).f n) = 0 := by
      rw [HomologicalComplex.comp_f, Category.assoc, ← Category.assoc (j.f n), hjr,
        Category.id_comp]
      exact congrArg (fun f ↦ f.f n) (cokernel.condition i)
    let r' := CokernelCofork.IsColimit.desc' (Qij n) (r ≫ (cokernel.π i).f n) hvan
    have hr' : p.f n ≫ r'.val = r ≫ (cokernel.π i).f n := r'.property
    have hkr : k.f n ≫ r'.val = 𝟙 ((cokernel i).X n) := by
      have : Epi ((cokernel.π i).f n) := epi_of_isColimit_cofork (Qi n)
      apply (cancel_epi ((cokernel.π i).f n)).mp
      have hkn : (cokernel.π i).f n ≫ k.f n = j.f n ≫ p.f n :=
        congrArg (fun f ↦ f.f n) hk
      rw [← Category.assoc, hkn, Category.assoc, hr', ← Category.assoc, hjr,
        Category.id_comp, Category.comp_id]
    exact ShortComplex.Splitting.ofExactOfRetraction _
      (hExact.map (HomologicalComplex.eval (ModuleCat.{v} R) c n)) r'.val hkr
      (by change Epi (q.f n); infer_instance)
  exact homotopyEquivalences_of_degreewiseSplit_of_contractibleKernel S hsplit h

/-- For a two-set family, small chains are exactly the image of the original sum of the
subspace chain inclusions. The statement concerns degreewise images, not a simplexwise union. -/
theorem range_smallSingularChainsInclusion_pair
    (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
    (A B : Set X) (n : ℕ) :
    ((smallSingularChainsInclusion R {A, B}).f n).hom.range =
      ((biprod.desc (singularSubspaceChains R A) (singularSubspaceChains R B)).f n).hom.range := by
  classical
  let P := smallSingularSet ({A, B} : Set (Set X))
  let j := smallSingularChainsInclusion R ({A, B} : Set (Set X))
  let i := biprod.desc (singularSubspaceChains R A) (singularSubspaceChains R B)
  let inc (U : Set X) := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
  have hlift (U : Set X) (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌))
      (hσ : Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ) ⊆ U) :
      ∃ τ : (TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋n⦌),
        (inc U).app (op ⦋n⦌) τ = σ := by
    let τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U) :=
      ⟨fun t ↦ ⟨(TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ t, hσ ⟨t, rfl⟩⟩,
        ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ).continuous.subtype_mk _⟩
    exact ⟨((TopCat.of U).toSSetObjEquiv (op ⦋n⦌)).symm τ, rfl⟩
  -- Lift each actual small generator to one of the two original summands.
  have hgenerator (σ : P.toSSet.obj (op ⦋n⦌)) :
      ∃ v : singularCoefficient R ⟶ (singularChains R A ⊞ singularChains R B).X n,
        v ≫ i.f n = (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ.val := by
    obtain ⟨U, hU, hσ⟩ := σ.property
    have hcases : U = A ∨ U = B := by simpa using hU
    rcases hcases with hUA | hUB
    · subst U
      obtain ⟨τ, hτ⟩ := hlift A σ.val hσ
      refine ⟨(TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
        (biprod.inl : singularChains R A ⟶ singularChains R A ⊞ singularChains R B).f n, ?_⟩
      have hinl := congrArg (fun g ↦ g.f n)
        (biprod.inl_desc (singularSubspaceChains R A) (singularSubspaceChains R B))
      simp only [HomologicalComplex.comp_f] at hinl
      erw [Category.assoc, hinl]
      change (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
        (SSet.chainComplexMap (inc A) (singularCoefficient R)).f n = _
      rw [SSet.ι_chainComplexMap_f, hτ]
    · subst U
      obtain ⟨τ, hτ⟩ := hlift B σ.val hσ
      refine ⟨(TopCat.toSSet.obj (TopCat.of B)).ιChainComplex τ ≫
        (biprod.inr : singularChains R B ⟶ singularChains R A ⊞ singularChains R B).f n, ?_⟩
      have hinr := congrArg (fun g ↦ g.f n)
        (biprod.inr_desc (singularSubspaceChains R A) (singularSubspaceChains R B))
      simp only [HomologicalComplex.comp_f] at hinr
      erw [Category.assoc, hinr]
      change (TopCat.toSSet.obj (TopCat.of B)).ιChainComplex τ ≫
        (SSet.chainComplexMap (inc B) (singularCoefficient R)).f n = _
      rw [SSet.ι_chainComplexMap_f, hτ]
  let r : (smallSingularChains R {A, B}).X n ⟶
      (singularChains R A ⊞ singularChains R B).X n := Sigma.desc fun σ ↦ (hgenerator σ).choose
  have hr : r ≫ i.f n = j.f n := by
    apply SSet.chainComplex_hom_ext
    intro σ
    change Sigma.ι (fun _ : P.toSSet.obj (op ⦋n⦌) ↦ singularCoefficient R) σ ≫
      (r ≫ i.f n) = P.toSSet.ιChainComplex σ ≫
        (SSet.chainComplexMap P.ι (singularCoefficient R)).f n
    rw [← Category.assoc, SSet.ι_chainComplexMap_f]
    dsimp only [r]
    rw [Sigma.ι_comp_desc]
    exact (hgenerator σ).choose_spec
  -- Conversely, each entire subspace has its canonical map into the same small simplicial set.
  have hinc (U : Set X) (hU : U ∈ ({A, B} : Set (Set X))) :
      SSet.Subcomplex.range (inc U) ≤ P := by
    intro m σ hσ
    obtain ⟨τ, rfl⟩ := hσ
    refine ⟨U, hU, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact ((TopCat.of U).toSSetObjEquiv m τ t).property
  let a := SSet.chainComplexMap (SSet.Subcomplex.lift (inc A) (hinc A (by simp)))
    (singularCoefficient R)
  let b := SSet.chainComplexMap (SSet.Subcomplex.lift (inc B) (hinc B (by simp)))
    (singularCoefficient R)
  have ha : a ≫ j = singularSubspaceChains R A := by
    change ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (singularCoefficient R)).map _ ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (singularCoefficient R)).map _ = _
    rw [← Functor.map_comp, SSet.Subcomplex.lift_ι]
    rfl
  have hb : b ≫ j = singularSubspaceChains R B := by
    change ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (singularCoefficient R)).map _ ≫
      ((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (singularCoefficient R)).map _ = _
    rw [← Functor.map_comp, SSet.Subcomplex.lift_ι]
    rfl
  have hsum : biprod.desc a b ≫ j = i := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc]
      exact ha.trans (biprod.inl_desc _ _).symm
    · rw [biprod.inr_desc_assoc]
      exact hb.trans (biprod.inr_desc _ _).symm
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact ⟨r y, congrArg (fun f ↦ f y) hr⟩
  · rintro x ⟨y, rfl⟩
    exact ⟨(biprod.desc a b).f n y, congrArg (fun f ↦ f.f n y) hsum⟩

/-- The iterated relative quotient is canonically the quotient by the target subspace and
all source chains. This uses the original map of pairs and its original cokernel projections. -/
def cokernelRelativeSingularChainsMapIso
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    cokernel (relativeSingularChainsMap R f hf) ≅
      cokernel (biprod.desc (singularSubspaceChains R B)
        ((singularChainsFunctor R).map (TopCat.ofHom f))) := by
  let F := (singularChainsFunctor R).map (TopCat.ofHom f)
  let G := relativeSingularChainsMap R f hf
  let i := biprod.desc (singularSubspaceChains R B) F
  let q := relativeSingularChainsProjection R B ≫ cokernel.π G
  have hpair : relativeSingularChainsProjection R A ≫ G =
      F ≫ relativeSingularChainsProjection R B := by
    simp [G, F, relativeSingularChainsMap, relativeSingularChainsProjection]
  have hiq : i ≫ q = 0 := by
    apply biprod.hom_ext'
    · simp [i, q, relativeSingularChainsProjection]
    · rw [biprod.inr_desc_assoc]
      change F ≫ relativeSingularChainsProjection R B ≫ cokernel.π G = 0
      rw [← Category.assoc, ← hpair, Category.assoc, cokernel.condition, comp_zero]
  have : Epi q := inferInstance
  have H : IsColimit (CokernelCofork.ofπ q hiq) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro T u hu
    have hBu : singularSubspaceChains R B ≫ u = 0 := by
      have hz := congrArg
        (fun v ↦ (biprod.inl : singularChains R B ⟶ singularChains R B ⊞ singularChains R X) ≫ v)
        hu
      dsimp only [i] at hz
      simp only [biprod.inl_desc_assoc, comp_zero] at hz
      exact hz
    have hFu : F ≫ u = 0 := by
      have hz := congrArg
        (fun v ↦ (biprod.inr : singularChains R X ⟶ singularChains R B ⊞ singularChains R X) ≫ v)
        hu
      dsimp only [i] at hz
      simp only [biprod.inr_desc_assoc, comp_zero] at hz
      exact hz
    let v := cokernel.desc (singularSubspaceChains R B) u hBu
    have hv : relativeSingularChainsProjection R B ≫ v = u := cokernel.π_desc _ _ _
    have hGv : G ≫ v = 0 := by
      apply (cancel_epi (relativeSingularChainsProjection R A)).mp
      rw [← Category.assoc, hpair, Category.assoc, hv, hFu, comp_zero]
    refine ⟨cokernel.desc G v hGv, ?_⟩
    change (relativeSingularChainsProjection R B ≫ cokernel.π G) ≫ _ = u
    rw [Category.assoc, cokernel.π_desc, hv]
  let e := H.coconePointUniqueUpToIso (cokernelIsCokernel i)
  exact e

/-- An injective continuous map induces split injections on the relative chain modules
when the source subspace is the actual inverse image of the target subspace. -/
theorem isSplitMono_relativeSingularChainsMap_preimage
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Function.Injective f) (B : Set Y) (n : ℕ) :
    IsSplitMono ((relativeSingularChainsMap R f
      (A := f ⁻¹' B) (B := B) (fun _ hx ↦ hx)).f n) := by
  classical
  let g := TopCat.toSSet.map (TopCat.ofHom f)
  let A := f ⁻¹' B
  let F := (singularChainsFunctor R).map (TopCat.ofHom f)
  let G := relativeSingularChainsMap R f (A := A) (B := B) (fun _ hx ↦ hx)
  let PX := relativeSingularChainsProjection R A
  let PY := relativeSingularChainsProjection R B
  let iA := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
  let iB := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(B, Y)))
  have hg : Function.Injective (g.app (op ⦋n⦌)) := by
    intro σ τ h
    apply ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)).injective
    apply ContinuousMap.ext
    intro t
    apply hf
    exact congrArg (fun η ↦ (TopCat.of Y).toSSetObjEquiv (op ⦋n⦌) η t) h
  -- Project onto exactly those target simplices that come from the source.
  let r : (singularChains R Y).X n ⟶ (singularChains R X).X n :=
    Sigma.desc fun τ ↦
      if h : τ ∈ Set.range (g.app (op ⦋n⦌)) then
        (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex h.choose else 0
  have hrgen (τ : (TopCat.toSSet.obj (TopCat.of Y)).obj (op ⦋n⦌)) :
      (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex τ ≫ r =
        if h : τ ∈ Set.range (g.app (op ⦋n⦌)) then
          (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex h.choose else 0 :=
    Sigma.ι_comp_desc _ _
  have hFr : F.f n ≫ r = 𝟙 ((singularChains R X).X n) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    change (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
      (SSet.chainComplexMap g (singularCoefficient R)).f n ≫ r = _
    rw [← Category.assoc, SSet.ι_chainComplexMap_f, hrgen]
    have hmem : g.app (op ⦋n⦌) σ ∈ Set.range (g.app (op ⦋n⦌)) := ⟨σ, rfl⟩
    have hchoose : hmem.choose = σ := hg hmem.choose_spec
    simp only [hmem, ↓reduceDIte, hchoose]
    exact (Category.comp_id _).symm
  -- A source simplex whose image lies in B lies in its actual inverse image A.
  have hlift (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌))
      (τ : (TopCat.toSSet.obj (TopCat.of B)).obj (op ⦋n⦌))
      (hστ : g.app (op ⦋n⦌) σ = iB.app (op ⦋n⦌) τ) :
      ∃ υ : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋n⦌),
        iA.app (op ⦋n⦌) υ = σ := by
    have hσ (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
        (TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ t ∈ A := by
      change f ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ t) ∈ B
      have ht := congrArg (fun η ↦ (TopCat.of Y).toSSetObjEquiv (op ⦋n⦌) η t) hστ
      change f ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ t) =
        ((TopCat.of B).toSSetObjEquiv (op ⦋n⦌) τ t).val at ht
      rw [ht]
      exact ((TopCat.of B).toSSetObjEquiv (op ⦋n⦌) τ t).property
    let υ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
      ⟨fun t ↦ ⟨(TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ t, hσ t⟩,
        ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ).continuous.subtype_mk _⟩
    exact ⟨((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm υ, rfl⟩
  have hvan : (singularSubspaceChains R B).f n ≫ r ≫ PX.f n = 0 := by
    apply SSet.chainComplex_hom_ext
    intro τ
    change (TopCat.toSSet.obj (TopCat.of B)).ιChainComplex τ ≫
      (SSet.chainComplexMap iB (singularCoefficient R)).f n ≫ (r ≫ PX.f n) = _
    rw [← Category.assoc, SSet.ι_chainComplexMap_f, ← Category.assoc, hrgen]
    by_cases hmem : iB.app (op ⦋n⦌) τ ∈ Set.range (g.app (op ⦋n⦌))
    · rw [dite_eq_left hmem]
      obtain ⟨υ, hυ⟩ := hlift hmem.choose τ hmem.choose_spec
      have hgen : (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex hmem.choose =
          (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex υ ≫
            (singularSubspaceChains R A).f n := by
        change _ = (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex υ ≫
          (SSet.chainComplexMap iA (singularCoefficient R)).f n
        rw [SSet.ι_chainComplexMap_f, hυ]
      erw [hgen, Category.assoc]
      have hz : (singularSubspaceChains R A).f n ≫ PX.f n = 0 :=
        congrArg (fun g ↦ g.f n) (cokernel.condition (singularSubspaceChains R A))
      erw [hz]
      exact (comp_zero).trans (comp_zero).symm
    · simp only [hmem, ↓reduceDIte]
      exact (zero_comp).trans (comp_zero).symm
  -- This support-preserving retraction descends through the original target quotient.
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    (singularSubspaceChains R B)
  let r' := CokernelCofork.IsColimit.desc' Q (r ≫ PX.f n) hvan
  have hr' : PY.f n ≫ r'.val = r ≫ PX.f n := r'.property
  refine ⟨⟨r'.val, ?_⟩⟩
  have hpair : PX ≫ G = F ≫ PY := by
    simp [PX, PY, G, F, relativeSingularChainsMap]
  have hpairn : PX.f n ≫ G.f n = F.f n ≫ PY.f n := congrArg (fun g ↦ g.f n) hpair
  apply (cancel_epi (PX.f n)).mp
  change PX.f n ≫ G.f n ≫ r'.val = PX.f n ≫ 𝟙 _
  rw [← Category.assoc, hpairn, Category.assoc, hr', ← Category.assoc,
    hFr, Category.id_comp, Category.comp_id]

/-- Excision for the actual map of relative singular chains follows from contraction of
the quotient by the target subspace and the source-chain image. -/
theorem homotopyEquivalences_relativeSingularChainsMap_preimage_of_contractible
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Function.Injective f) (B : Set Y)
    (h : Homotopy (𝟙 (cokernel (biprod.desc (singularSubspaceChains R B)
      ((singularChainsFunctor R).map (TopCat.ofHom f))))) 0) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
      (relativeSingularChainsMap R f (A := f ⁻¹' B) (B := B) (fun _ hx ↦ hx)) := by
  let G := relativeSingularChainsMap R f (A := f ⁻¹' B) (B := B) (fun _ hx ↦ hx)
  let e := cokernelRelativeSingularChainsMapIso R f (A := f ⁻¹' B) (B := B) (fun _ hx ↦ hx)
  -- Transport the actual contraction across the canonical iterated-quotient identification.
  have hQ : Homotopy (𝟙 (cokernel G)) 0 := by
    have H := (h.compLeft e.hom).compRight e.inv
    simpa only [Category.comp_id, e.hom_inv_id, comp_zero, zero_comp] using H
  let S := ShortComplex.cokernelSequence G
  have hsplit (n : ℕ) :
      (S.map (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)).Splitting := by
    let split : SplitMono (G.f n) :=
      (isSplitMono_relativeSingularChainsMap_preimage R f hf B n).exists_splitMono.some
    exact ShortComplex.Splitting.ofExactOfRetraction _
      ((ShortComplex.cokernelSequence_exact G).map
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n))
      split.retraction split.id
      (by change Epi ((cokernel.π G).f n); infer_instance)
  exact homotopyEquivalences_of_degreewiseSplit_of_contractibleCokernel S hsplit hQ

/-- For an embedded source, the small-chain image for the subspace and the range is
exactly the image of their original two chain maps. -/
theorem range_smallSingularChainsInclusion_pair_range
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Topology.IsEmbedding f) (B : Set Y) (n : ℕ) :
    ((smallSingularChainsInclusion R {B, Set.range f}).f n).hom.range =
      ((biprod.desc (singularSubspaceChains R B)
        ((singularChainsFunctor R).map (TopCat.ofHom f))).f n).hom.range := by
  rw [range_smallSingularChainsInclusion_pair]
  -- Replace the range subspace only through the embedding's canonical homeomorphism.
  let e := (singularChainsFunctor R).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of (Set.range f)) hf.toHomeomorph)
  let E := biprod.mapIso (Iso.refl (singularChains R B)) e
  let i := biprod.desc (singularSubspaceChains R B)
    (singularSubspaceChains R (Set.range f))
  let j := biprod.desc (singularSubspaceChains R B)
    ((singularChainsFunctor R).map (TopCat.ofHom f))
  have he : e.hom ≫ singularSubspaceChains R (Set.range f) =
      (singularChainsFunctor R).map (TopCat.ofHom f) := by
    change (singularChainsFunctor R).map _ ≫ (singularChainsFunctor R).map _ = _
    rw [← Functor.map_comp]
    rfl
  have hE : E.hom ≫ i = j := by
    apply biprod.hom_ext'
    · simp [E, i, j]
    · simpa [E, i, j] using he
  have hEn : E.hom.f n ≫ i.f n = j.f n := congrArg (fun g ↦ g.f n) hE
  have hEnInv : E.inv.f n ≫ j.f n = i.f n := by
    have h : E.inv ≫ j = i := by rw [← hE, ← Category.assoc, E.inv_hom_id, Category.id_comp]
    exact congrArg (fun g ↦ g.f n) h
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact ⟨E.inv.f n y, congrArg (fun g ↦ g y) hEnInv⟩
  · rintro x ⟨y, rfl⟩
    exact ⟨E.hom.f n y, congrArg (fun g ↦ g y) hEn⟩

/-- Chain maps into the same complex with equal degreewise images have canonically
isomorphic cokernels, with both maps characterized by the original projections. -/
def cokernelIsoOfDegreewiseRangeEq
    {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c} (i : A ⟶ C) (j : B ⟶ C)
    (h : ∀ n, (i.f n).hom.range = (j.f n).hom.range) : cokernel i ≅ cokernel j := by
  have hij : i ≫ cokernel.π j = 0 := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : i.f n x ∈ (j.f n).hom.range :=
      (h n) ▸ (show i.f n x ∈ (i.f n).hom.range from ⟨x, rfl⟩)
    obtain ⟨y, hy⟩ := hx
    change (cokernel.π j).f n (i.f n x) = 0
    rw [← hy]
    exact congrArg (fun g ↦ g.f n y) (cokernel.condition j)
  have hji : j ≫ cokernel.π i = 0 := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : j.f n x ∈ (i.f n).hom.range := (h n).symm ▸
      (show j.f n x ∈ (j.f n).hom.range from ⟨x, rfl⟩)
    obtain ⟨y, hy⟩ := hx
    change (cokernel.π i).f n (j.f n x) = 0
    rw [← hy]
    exact congrArg (fun g ↦ g.f n y) (cokernel.condition i)
  exact
    { hom := cokernel.desc i (cokernel.π j) hij
      inv := cokernel.desc j (cokernel.π i) hji
      hom_inv_id := by
        apply (cancel_epi (cokernel.π i)).mp
        simp
      inv_hom_id := by
        apply (cancel_epi (cokernel.π j)).mp
        simp }

/-- A contraction of the actual small-chain quotient for the subspace and the embedded
range gives excision for the original relative map of pairs. -/
theorem homotopyEquivalences_relativeSingularChainsMap_preimage_of_smallChainContraction
    (R : Type) [CommRing R] {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Topology.IsEmbedding f) (B : Set Y)
    (h : Homotopy (𝟙 (cokernel (smallSingularChainsInclusion R {B, Set.range f}))) 0) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
      (relativeSingularChainsMap R f (A := f ⁻¹' B) (B := B) (fun _ hx ↦ hx)) := by
  let i := biprod.desc (singularSubspaceChains R B)
    ((singularChainsFunctor R).map (TopCat.ofHom f))
  let e := cokernelIsoOfDegreewiseRangeEq
    (smallSingularChainsInclusion R {B, Set.range f}) i
      (range_smallSingularChainsInclusion_pair_range R f hf B)
  have hsum : Homotopy (𝟙 (cokernel i)) 0 := by
    have H := (h.compLeft e.inv).compRight e.hom
    simpa only [Category.comp_id, e.inv_hom_id, comp_zero, zero_comp] using H
  exact homotopyEquivalences_relativeSingularChainsMap_preimage_of_contractible
    R f hf.injective B hsum

/-- Algebraic dualization of a genuine chain homotopy equivalence induces an isomorphism
on cohomology over every commutative coefficient ring. -/
theorem isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences
    (R : Type) [CommRing R] {C D : ChainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D)
    (hf : HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ) f)
    (n : ℕ) : IsIso
      (HomologicalComplex.homologyMap ((singularCochainDualFunctor R).map f.op) n) := by
  obtain ⟨e, rfl⟩ := hf
  let dual := ((linearYoneda R (ModuleCat.{u} R)).obj (singularCoefficient R)).rightOp
  -- Dualize both original inverse homotopies, reversing their order under opposition.
  have hleft : Homotopy
      ((singularCochainDualFunctor R).map e.hom.op ≫
        (singularCochainDualFunctor R).map e.inv.op) (𝟙 _) := by
    have H := (dual.mapHomotopy e.homotopyInvHomId).unop
    change Homotopy ((singularCochainDualFunctor R).map (e.inv ≫ e.hom).op)
      ((singularCochainDualFunctor R).map (𝟙 D).op) at H
    exact (Homotopy.ofEq
      ((singularCochainDualFunctor R).map_comp e.hom.op e.inv.op).symm).trans
        (H.trans (Homotopy.ofEq ((singularCochainDualFunctor R).map_id (op D))))
  have hright : Homotopy
      ((singularCochainDualFunctor R).map e.inv.op ≫
        (singularCochainDualFunctor R).map e.hom.op) (𝟙 _) := by
    have H := (dual.mapHomotopy e.homotopyHomInvId).unop
    change Homotopy ((singularCochainDualFunctor R).map (e.hom ≫ e.inv).op)
      ((singularCochainDualFunctor R).map (𝟙 C).op) at H
    exact (Homotopy.ofEq
      ((singularCochainDualFunctor R).map_comp e.inv.op e.hom.op).symm).trans
        (H.trans (Homotopy.ofEq ((singularCochainDualFunctor R).map_id (op C))))
  let E : HomotopyEquiv ((singularCochainDualFunctor R).obj (op D))
      ((singularCochainDualFunctor R).obj (op C)) :=
    { hom := (singularCochainDualFunctor R).map e.hom.op
      inv := (singularCochainDualFunctor R).map e.inv.op
      homotopyHomInvId := hleft
      homotopyInvHomId := hright }
  change IsIso (E.toHomologyIso n).hom
  infer_instance

end AtiyahSinger
