/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationClass

/-!
# Integral generator signs measured on the original local cycles

Public module ID: M2048.

A primitive integral fiber cohomology class evaluates to an integral unit on
each specified primitive real orientation cycle. The two evaluations therefore
compare the cycles from any two native linear coordinate bases, including rank
zero. Both signs refer to the same cohomology class and the original cap pairing.

Source: Milnor--Stasheff, Characteristic Classes, section 9, the comparison of
integral orientation generators. These formulas retain the project's actual
simplex, cap evaluation, and signed zero-dimensional convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable {r : ℕ} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A primitive integral cohomology class evaluates to a unit on the specified real cycle. -/
theorem isUnit_realOrientationEvaluation_of_generator
    (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r))
    (a : relativeSingularCohomology ℤ {v : V | v ≠ 0} r)
    (ha : Function.Bijective (fun m : ℤ ↦ m • a)) :
    IsUnit (realOrientationEvaluation b o a) := by
  let ev : relativeSingularCohomology ℤ {v : V | v ≠ 0} r →+ ℤ :=
    { toFun := realOrientationEvaluation b o
      map_zero' := by
        unfold realOrientationEvaluation
        erw [map_zero, LinearMap.zero_apply, map_zero]
        rfl
      map_add' := by
        intro a a'
        unfold realOrientationEvaluation
        erw [map_add, LinearMap.add_apply, map_add]
        rfl }
  let u := realOrientationClass b o
  have hu : Function.Bijective (fun m : ℤ ↦ m • u) :=
    realOrientationClass_is_generator b o
  have hev : ev u = 1 := realOrientationClass_evaluation b o
  -- Express each primitive class as an integral multiple of the other.
  obtain ⟨m, hm⟩ := hu.surjective a
  obtain ⟨n, hn⟩ := ha.surjective u
  change m • u = a at hm
  change n • a = u at hn
  have hnm : n * m = 1 := hu.injective (by
    rw [mul_smul, hm, hn, one_smul])
  -- Evaluation relative to the normalized class reads the invertible coefficient of a.
  have hvalue : ev a = m := by
    rw [← hm, map_zsmul, hev, smul_eq_mul, mul_one]
  change IsUnit (ev a)
  rw [hvalue]
  exact isUnit_iff_exists_inv'.mpr ⟨n, hnm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The evaluations of one primitive cohomology class give the exact sign comparing
the original positive cycles of two coordinate bases. -/
theorem realOrientationCycle_eq_evaluation_mul_smul
    (b c : Module.Basis (Fin r) ℝ V)
    (a : relativeSingularCohomology ℤ {v : V | v ≠ 0} r)
    (ha : Function.Bijective (fun m : ℤ ↦ m • a)) :
    realOrientationCycle b b.orientation =
      (realOrientationEvaluation b b.orientation a *
        realOrientationEvaluation c c.orientation a) • realOrientationCycle c c.orientation := by
  let ev : relativeSingularHomology ℤ {v : V | v ≠ 0} r →+ ℤ :=
    { toFun := fun z ↦ (((TopCat.of V).singularHomology₀ε (singularCoefficient ℤ))
        (relativeSingularCapProduct ℤ {v : V | v ≠ 0} r 0 a z)).down
      map_zero' := by erw [map_zero, map_zero]; rfl
      map_add' := by
        intro z z'
        erw [map_add, map_add]
        rfl }
  -- The second geometric cycle is a primitive homology generator.
  obtain ⟨m, hm⟩ := (realOrientationCycle_is_generator c c.orientation).surjective
    (realOrientationCycle b b.orientation)
  have hvalue : realOrientationEvaluation b b.orientation a =
      m * realOrientationEvaluation c c.orientation a := by
    change ev (realOrientationCycle b b.orientation) =
      m * ev (realOrientationCycle c c.orientation)
    rw [← hm, map_zsmul, smul_eq_mul]
  -- An integral unit is its own inverse, including either signed rank-zero class.
  have hunit := isUnit_realOrientationEvaluation_of_generator c c.orientation a ha
  have hcoeff : m = realOrientationEvaluation b b.orientation a *
      realOrientationEvaluation c c.orientation a := by
    rcases Int.isUnit_iff.mp hunit with h | h
    · rw [h] at hvalue ⊢
      linarith
    · rw [h] at hvalue ⊢
      linarith
  rw [← hcoeff]
  exact hm.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual transition between two linear coordinate systems acts at every fiber point
by the product of their evaluations on the same primitive integral cohomology class. -/
theorem relativeSingularHomologyMap_linearCoordChange_eq_smul
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : Module.Basis (Fin r) ℝ W) (e f : V ≃L[ℝ] W)
    (a : relativeSingularCohomology ℤ {v : V | v ≠ 0} r)
    (ha : Function.Bijective (fun m : ℤ ↦ m • a)) (v : W) :
    relativeSingularHomologyMap ℤ
        (⟨e.symm.trans f, (e.symm.trans f).continuous⟩ : C(W, W))
        (A := ({v}ᶜ : Set W)) (B := ({f (e.symm v)}ᶜ : Set W))
        (fun _ hz heq ↦ hz ((e.symm.trans f).injective heq)) r =
      (realOrientationEvaluation (b.map e.symm.toLinearEquiv)
          (b.map e.symm.toLinearEquiv).orientation a *
        realOrientationEvaluation (b.map f.symm.toLinearEquiv)
          (b.map f.symm.toLinearEquiv).orientation a) •
        relativeSingularHomologyMap ℤ
          (⟨fun w : W ↦ f (e.symm v) + (w - v),
            continuous_const.add (continuous_id.sub continuous_const)⟩ : C(W, W))
          (A := ({v}ᶜ : Set W)) (B := ({f (e.symm v)}ᶜ : Set W))
          (fun _ hz heq ↦ hz (sub_eq_zero.mp
            (add_left_cancel (heq.trans (add_zero _).symm)))) r := by
  open CategoryTheory in
  let L : W ≃L[ℝ] W := e.symm.trans f
  let b₁ := b.map e.symm.toLinearEquiv
  let b₂ := b.map f.symm.toLinearEquiv
  let s := realOrientationEvaluation b₁ b₁.orientation a *
    realOrientationEvaluation b₂ b₂.orientation a
  let l : C(W, W) := ⟨L, L.continuous⟩
  have hl₀ : Set.MapsTo l {w : W | w ≠ 0} {w : W | w ≠ 0} :=
    fun _ hz heq ↦ hz (L.injective (heq.trans L.map_zero.symm))
  have hlv : Set.MapsTo l ({v}ᶜ : Set W) ({L v}ᶜ : Set W) :=
    fun _ hz heq ↦ hz (L.injective heq)
  -- Compare the two original fiber cycles before returning to the coordinate model.
  have hcycle : relativeSingularHomologyMap ℤ l hl₀ r
      (realOrientationCycle b b.orientation) = s • realOrientationCycle b b.orientation := by
    have hb₂ : b₂.map f.toLinearEquiv = b := by
      apply Module.Basis.eq_of_apply_eq
      intro i
      exact f.apply_symm_apply (b i)
    have hbL : b.map L.toLinearEquiv = b₁.map f.toLinearEquiv := by
      apply Module.Basis.eq_of_apply_eq
      intro i
      rfl
    let F := relativeSingularHomologyMap ℤ (⟨f, f.continuous⟩ : C(V, W))
      (A := {z : V | z ≠ 0}) (B := {w : W | w ≠ 0})
      (fun _ hz heq ↦ hz (f.injective (heq.trans f.map_zero.symm))) r
    have hmap := congrArg (fun z ↦ F z)
      (realOrientationCycle_eq_evaluation_mul_smul b₁ b₂ a ha)
    dsimp only [F] at hmap
    rw [map_zsmul, realOrientationCycle_map_basis, realOrientationCycle_map_basis,
      hb₂] at hmap
    rw [realOrientationCycle_map_basis, hbL]
    exact hmap
  -- A map on this free rank-one group is determined by its value on that same cycle.
  have hzero : relativeSingularHomologyMap ℤ l hl₀ r = s • (𝟙 _) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨m, hm⟩ := (realOrientationCycle_is_generator b b.orientation).surjective z
    rw [← hm]
    change relativeSingularHomologyMap ℤ l hl₀ r (m • realOrientationCycle b b.orientation) =
      s • (m • realOrientationCycle b b.orientation)
    rw [map_zsmul, hcycle, smul_smul, smul_smul, mul_comm m s]
  let ta : C(W, W) := ⟨fun w ↦ v + w, continuous_const.add continuous_id⟩
  let sa : C(W, W) := ⟨fun w ↦ w - v, continuous_id.sub continuous_const⟩
  let tb : C(W, W) := ⟨fun w ↦ L v + w, continuous_const.add continuous_id⟩
  let t : C(W, W) := ⟨fun w ↦ L v + (w - v),
    continuous_const.add (continuous_id.sub continuous_const)⟩
  have hta : Set.MapsTo ta {w : W | w ≠ 0} ({v}ᶜ : Set W) :=
    fun _ hz heq ↦ hz (add_left_cancel (heq.trans (add_zero v).symm))
  have hsa : Set.MapsTo sa ({v}ᶜ : Set W) {w : W | w ≠ 0} :=
    fun _ hz heq ↦ hz (sub_eq_zero.mp heq)
  have htb : Set.MapsTo tb {w : W | w ≠ 0} ({L v}ᶜ : Set W) :=
    fun _ hz heq ↦ hz (add_left_cancel (heq.trans (add_zero (L v)).symm))
  have ht : Set.MapsTo t ({v}ᶜ : Set W) ({L v}ᶜ : Set W) :=
    fun _ hz heq ↦ hz (sub_eq_zero.mp (add_left_cancel (heq.trans (add_zero _).symm)))
  let Ta := relativeSingularHomologyMap ℤ ta hta r
  let Tb := relativeSingularHomologyMap ℤ tb htb r
  let : CategoryTheory.IsIso Ta := isIso_relativeSingularHomologyMap_of_inverse ℤ ta sa hta hsa
    (by apply ContinuousMap.ext; intro w; dsimp [ta, sa]; abel)
    (by apply ContinuousMap.ext; intro w; dsimp [ta, sa]; abel) r
  have hcomp (p q : C(W, W)) {S T U : Set W}
      (hp : Set.MapsTo p S T) (hq : Set.MapsTo q T U) :
      relativeSingularHomologyMap ℤ (q.comp p) (hq.comp hp) r =
        relativeSingularHomologyMap ℤ p hp r ≫ relativeSingularHomologyMap ℤ q hq r := by
    change HomologicalComplex.homologyMap _ r =
      HomologicalComplex.homologyMap _ r ≫ HomologicalComplex.homologyMap _ r
    rw [← HomologicalComplex.homologyMap_comp, relativeSingularChainsMap_comp]
  have hcongr {p q : C(W, W)} {S T : Set W}
      (hp : Set.MapsTo p S T) (hq : Set.MapsTo q S T) (h : p = q) :
      relativeSingularHomologyMap ℤ p hp r = relativeSingularHomologyMap ℤ q hq r := by
    subst q
    rfl
  have hlinear : Ta ≫ relativeSingularHomologyMap ℤ l hlv r =
      relativeSingularHomologyMap ℤ l hl₀ r ≫ Tb := by
    rw [← hcomp ta l hta hlv, ← hcomp l tb hl₀ htb]
    apply hcongr
    apply ContinuousMap.ext
    intro w
    exact L.map_add v w
  have htranslate : Ta ≫ relativeSingularHomologyMap ℤ t ht r = Tb := by
    rw [← hcomp ta t hta ht]
    apply hcongr
    apply ContinuousMap.ext
    intro w
    change L v + (v + w - v) = L v + w
    abel
  -- Translate from zero to v at both ends of the identical coordinate transition.
  change relativeSingularHomologyMap ℤ l hlv r = s • relativeSingularHomologyMap ℤ t ht r
  apply (CategoryTheory.cancel_epi Ta).mp
  rw [CategoryTheory.Linear.comp_smul, hlinear, htranslate, hzero,
    CategoryTheory.Linear.smul_comp, CategoryTheory.Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation on the original positive cycle commutes with an actual linear pullback. -/
theorem realOrientationEvaluation_pullback
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : Module.Basis (Fin r) ℝ V) (e : V ≃L[ℝ] W)
    (a : relativeSingularCohomology ℤ {w : W | w ≠ 0} r) :
    realOrientationEvaluation b b.orientation
        (relativeSingularCohomologyPullback ℤ (⟨e, e.continuous⟩ : C(V, W))
          (A := {v : V | v ≠ 0}) (B := {w : W | w ≠ 0})
          (fun _ hv heq ↦ hv (e.injective (heq.trans e.map_zero.symm))) r a) =
      realOrientationEvaluation (b.map e.toLinearEquiv) (b.map e.toLinearEquiv).orientation a := by
  let f : C(V, W) := ⟨e, e.continuous⟩
  have hf : Set.MapsTo f {v : V | v ≠ 0} {w : W | w ≠ 0} :=
    fun _ hv heq ↦ hv (e.injective (heq.trans e.map_zero.symm))
  unfold realOrientationEvaluation
  rw [relativeSingularCapProduct_augmentation, relativeSingularCapProduct_augmentation]
  change (singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ {v : V | v ≠ 0}) r
    (HomologicalComplex.homologyMap
      ((singularCochainDualFunctor ℤ).map (relativeSingularChainsMap ℤ f hf).op) r a)
    (realOrientationCycle b b.orientation)).down = _
  rw [← singularCochainHomologyEvaluation_naturality]
  change (singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ {w : W | w ≠ 0}) r a
    (relativeSingularHomologyMap ℤ f hf r (realOrientationCycle b b.orientation))).down = _
  rw [realOrientationCycle_map_basis]

end AtiyahSinger
