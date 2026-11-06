/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexBundleRealOrientation
public import AtiyahSinger.Topology.LocalRelativeCupNormalization

/-!
Public module ID: M1717.

# Normalized local cup products and complex orientations

The ordered relative cup of positively normalized local orientation classes
is the positively normalized class in the same concatenated coordinates.
The proof uses evaluation on the original rationalized integral cycle, so it
determines the sign and does not merely recognize an unspecified generator.

Source: Milnor--Stasheff, Sections 9 and 14, product orientations and the
canonical orientation of a complex direct sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordered local product has the original positive orientation in concatenated coordinates. -/
theorem realOrientationClass_rationalization_liftedPi_unionCup (n r : ℕ) :
    let V := ULift.{u} (Fin n → ℝ)
    let W := ULift.{u} (Fin r → ℝ)
    let T := ULift.{u} (Fin (r + n) → ℝ)
    let bV := (Pi.basisFun ℝ (Fin n)).map (ULift.moduleEquiv : V ≃ₗ[ℝ] _).symm
    let bW := (Pi.basisFun ℝ (Fin r)).map (ULift.moduleEquiv : W ≃ₗ[ℝ] _).symm
    let bT := (Pi.basisFun ℝ (Fin (r + n))).map (ULift.moduleEquiv : T ≃ₗ[ℝ] _).symm
    let f : C(T, V) :=
      ⟨fun x ↦ ULift.up (fun i ↦ x.down ⟨i.val, by omega⟩), by dsimp only [T, V]; fun_prop⟩
    let g : C(T, W) :=
      ⟨fun x ↦ ULift.up (fun i ↦ x.down ⟨n + i.val, by omega⟩),
        by dsimp only [T, W]; fun_prop⟩
    let A : Set T := f ⁻¹' {v : V | v ≠ 0}
    let B : Set T := g ⁻¹' {w : W | w ≠ 0}
    let P : Set T := {v | v ≠ 0}
    ∀ hP : Set.MapsTo (ContinuousMap.id T) P (A ∪ B),
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_comm n r))
        (relativeSingularCohomologyPullback ℚ (ContinuousMap.id T) hP (n + r)
          (relativeSingularCohomologyUnionCup ℚ A B
            ((isOpen_ne_fun continuous_id continuous_const).preimage f.continuous)
            ((isOpen_ne_fun continuous_id continuous_const).preimage g.continuous) n r
            (relativeSingularCohomologyPullback ℚ f (A := A) (B := {v : V | v ≠ 0})
              (fun _ hv ↦ hv) n (relativeSingularCohomologyRationalization
                {v : V | v ≠ 0} n (realOrientationClass bV bV.orientation)))
            (relativeSingularCohomologyPullback ℚ g (A := B) (B := {w : W | w ≠ 0})
              (fun _ hw ↦ hw) r (relativeSingularCohomologyRationalization
                {w : W | w ≠ 0} r (realOrientationClass bW bW.orientation))))) =
      relativeSingularCohomologyRationalization P (r + n)
        (realOrientationClass bT bT.orientation) := by
  dsimp only
  intro hP
  -- Evaluation on the original signed integral cycle detects every rational local class.
  have hnorm {m : ℕ} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (b : Module.Basis (Fin m) ℝ V) :
      (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ {v : V | v ≠ 0}) m
        (relativeSingularCohomologyRationalization {v : V | v ≠ 0} m
          (realOrientationClass b b.orientation))
        (relativeSingularHomologyRationalization {v : V | v ≠ 0} m
          (realOrientationCycle b b.orientation))).down = 1 := by
    rw [singularCochainHomologyEvaluation_rationalization,
      ← relativeSingularCapProduct_augmentation]
    change (realOrientationEvaluation b b.orientation (realOrientationClass b b.orientation) :
      ℚ) = 1
    rw [realOrientationClass_evaluation]
    rfl
  let bT := (Pi.basisFun ℝ (Fin (r + n))).map
    (ULift.moduleEquiv : ULift.{u} (Fin (r + n) → ℝ) ≃ₗ[ℝ] _).symm
  apply (rationalRealOrientationEvaluation_bijective bT bT.orientation).injective
  -- The original relative cup evaluates as the product 1*1 in this precise coordinate order.
  refine (relativeSingularCohomologyUnionCup_liftedPi_evaluation n r _ _ hP).trans ?_
  rw [hnorm, hnorm, one_mul]
  exact (hnorm bT).symm

private def orientationCoordinates {n : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    ULift.{u} (Fin n → ℝ) ≃L[ℝ] V := by
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  exact ((ULift.moduleEquiv : ULift.{u} (Fin n → ℝ) ≃ₗ[ℝ] _).trans
    b.equivFun.symm).toContinuousLinearEquiv

private theorem orientationCoordinates_map_basis {n : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    ((Pi.basisFun ℝ (Fin n)).map
      (ULift.moduleEquiv : ULift.{u} (Fin n → ℝ) ≃ₗ[ℝ] _).symm).map
        (orientationCoordinates b).toLinearEquiv = b := by
  apply DFunLike.ext
  intro i
  apply b.equivFun.injective
  funext j
  change b.equivFun (b.equivFun.symm (Pi.basisFun ℝ (Fin n) i)) j = _
  rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_self]
  simp only [Pi.basisFun_apply, Pi.single_apply, eq_comm]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem rationalOrientation_pullback_coordinates {n : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    let d := (Pi.basisFun ℝ (Fin n)).map
      (ULift.moduleEquiv : ULift.{u} (Fin n → ℝ) ≃ₗ[ℝ] _).symm
    let e := orientationCoordinates b
    relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(_, V))
      (A := {v | v ≠ 0}) (B := {v | v ≠ 0})
      (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) n
      (relativeSingularCohomologyRationalization {v : V | v ≠ 0} n
        (realOrientationClass b b.orientation)) =
    relativeSingularCohomologyRationalization {v : ULift.{u} (Fin n → ℝ) | v ≠ 0} n
      (realOrientationClass d d.orientation) := by
  dsimp only
  let d := (Pi.basisFun ℝ (Fin n)).map
    (ULift.moduleEquiv : ULift.{u} (Fin n → ℝ) ≃ₗ[ℝ] _).symm
  let e := orientationCoordinates b
  rw [← relativeSingularCohomologyRationalization_naturality]
  congr 1
  apply realOrientationClass_pullback d d.orientation b b.orientation e
  rw [← Module.Basis.orientation_map, orientationCoordinates_map_basis]

set_option maxHeartbeats 1000000 in
-- The product comparison retains the original spaces and all support and degree transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The local cup of normalized orientations is the normalized product orientation. -/
theorem realOrientationClass_rationalization_prod {n r : ℕ} {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (bV : Module.Basis (Fin n) ℝ V) (bW : Module.Basis (Fin r) ℝ W) :
    let A : Set (V × W) := {z | z.1 ≠ 0}
    let B : Set (V × W) := {z | z.2 ≠ 0}
    let P : Set (V × W) := {z | z ≠ 0}
    let bT := (bV.prod bW).reindex
      ((finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r)).trans (finCongr (Nat.add_comm n r)))
    ∀ hP : Set.MapsTo (ContinuousMap.id (V × W)) P (A ∪ B),
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.add_comm n r))
        (relativeSingularCohomologyPullback ℚ (ContinuousMap.id (V × W)) hP (n + r)
          (relativeSingularCohomologyUnionCup ℚ A B
            (isOpen_ne_fun continuous_fst continuous_const)
            (isOpen_ne_fun continuous_snd continuous_const) n r
            (relativeSingularCohomologyPullback ℚ (ContinuousMap.fst : C(V × W, V))
              (A := A) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) n
              (relativeSingularCohomologyRationalization {v : V | v ≠ 0} n
                (realOrientationClass bV bV.orientation)))
            (relativeSingularCohomologyPullback ℚ (ContinuousMap.snd : C(V × W, W))
              (A := B) (B := {w | w ≠ 0}) (fun _ hw ↦ hw) r
              (relativeSingularCohomologyRationalization {w : W | w ≠ 0} r
                (realOrientationClass bW bW.orientation))))) =
      relativeSingularCohomologyRationalization P (r + n)
        (realOrientationClass bT bT.orientation) := by
  classical
  dsimp only
  intro hP
  let V₀ := ULift.{u} (Fin n → ℝ)
  let W₀ := ULift.{u} (Fin r → ℝ)
  let T₀ := ULift.{u} (Fin (r + n) → ℝ)
  let bT := (bV.prod bW).reindex
    ((finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r)).trans (finCongr (Nat.add_comm n r)))
  let eV := orientationCoordinates bV
  let eW := orientationCoordinates bW
  let eT := orientationCoordinates bT
  let f : C(T₀, V₀) :=
    ⟨fun z ↦ ULift.up (fun i ↦ z.down ⟨i.val, by omega⟩), by dsimp only [T₀, V₀]; fun_prop⟩
  let g : C(T₀, W₀) :=
    ⟨fun z ↦ ULift.up (fun i ↦ z.down ⟨n + i.val, by omega⟩),
      by dsimp only [T₀, W₀]; fun_prop⟩
  let e : C(T₀, V × W) := ⟨eT, eT.continuous⟩
  -- The original product basis lists the first fiber's coordinates before the second fiber's.
  have hfirst : (ContinuousMap.fst : C(V × W, V)).comp e =
      (⟨eV, eV.continuous⟩ : C(V₀, V)).comp f := by
    apply ContinuousMap.ext
    intro z
    apply bV.equivFun.injective
    funext i
    have hcoord := congrArg (fun a : Fin (r + n) → ℝ ↦
      a (Fin.cast (Nat.add_comm n r) (Fin.castAdd r i)))
      (bT.equivFun.apply_symm_apply z.down)
    change bT.repr (eT z) (Fin.cast (Nat.add_comm n r) (Fin.castAdd r i)) = _ at hcoord
    have hr : bV.equivFun (eV (f z)) i = (f z).down i :=
      congrArg (fun a : Fin n → ℝ ↦ a i) (bV.equivFun.apply_symm_apply (f z).down)
    change bV.equivFun (eT z).1 i = bV.equivFun (eV (f z)) i
    rw [hr]
    change bV.repr (eT z).1 i = _
    simp only [bT, Module.Basis.repr_reindex_apply, Equiv.symm_trans_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq,
      finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_repr_inl] at hcoord
    exact hcoord.trans (congrArg z.down (Fin.ext rfl))
  have hsecond : (ContinuousMap.snd : C(V × W, W)).comp e =
      (⟨eW, eW.continuous⟩ : C(W₀, W)).comp g := by
    apply ContinuousMap.ext
    intro z
    apply bW.equivFun.injective
    funext i
    have hcoord := congrArg (fun a : Fin (r + n) → ℝ ↦
      a (Fin.cast (Nat.add_comm n r) (Fin.natAdd n i)))
      (bT.equivFun.apply_symm_apply z.down)
    change bT.repr (eT z) (Fin.cast (Nat.add_comm n r) (Fin.natAdd n i)) = _ at hcoord
    have hr : bW.equivFun (eW (g z)) i = (g z).down i :=
      congrArg (fun a : Fin r → ℝ ↦ a i) (bW.equivFun.apply_symm_apply (g z).down)
    change bW.equivFun (eT z).2 i = bW.equivFun (eW (g z)) i
    rw [hr]
    change bW.repr (eT z).2 i = _
    simp only [bT, Module.Basis.repr_reindex_apply, Equiv.symm_trans_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq,
      finSumFinEquiv_symm_apply_natAdd, Module.Basis.prod_repr_inr] at hcoord
    exact hcoord.trans (congrArg z.down (Fin.ext rfl))
  let A : Set (V × W) := {z | z.1 ≠ 0}
  let B : Set (V × W) := {z | z.2 ≠ 0}
  let P : Set (V × W) := {z | z ≠ 0}
  let A₀ : Set T₀ := f ⁻¹' {v | v ≠ 0}
  let B₀ : Set T₀ := g ⁻¹' {w | w ≠ 0}
  let P₀ : Set T₀ := {z | z ≠ 0}
  have heA : Set.MapsTo e A₀ A := by
    intro z hz hzero
    have hv := congrArg (fun F ↦ F z) hfirst
    exact hz (eV.injective (hv.symm.trans (hzero.trans eV.map_zero.symm)))
  have heB : Set.MapsTo e B₀ B := by
    intro z hz hzero
    have hv := congrArg (fun F ↦ F z) hsecond
    exact hz (eW.injective (hv.symm.trans (hzero.trans eW.map_zero.symm)))
  have heP : Set.MapsTo e P₀ P :=
    fun _ hz hzero ↦ hz (eT.injective (hzero.trans eT.map_zero.symm))
  have hP₀ : Set.MapsTo (ContinuousMap.id T₀) P₀ (A₀ ∪ B₀) := by
    intro z hz
    by_contra h
    have hfz : f z = 0 := not_ne_iff.mp (not_or.mp h).1
    have hgz : g z = 0 := not_ne_iff.mp (not_or.mp h).2
    apply heP hz
    apply Prod.ext
    · have h := congrArg (fun F ↦ F z) hfirst
      change (e z).1 = eV (f z) at h
      change (e z).1 = 0
      simpa only [hfz, map_zero] using h
    · have h := congrArg (fun F ↦ F z) hsecond
      change (e z).2 = eW (g z) at h
      change (e z).2 = 0
      simpa only [hgz, map_zero] using h
  let a : relativeSingularCohomology ℚ {v : V | v ≠ 0} n :=
    relativeSingularCohomologyRationalization {v : V | v ≠ 0} n
    (realOrientationClass bV bV.orientation)
  let b : relativeSingularCohomology ℚ {w : W | w ≠ 0} r :=
    relativeSingularCohomologyRationalization {w : W | w ≠ 0} r
    (realOrientationClass bW bW.orientation)
  let dV := (Pi.basisFun ℝ (Fin n)).map (ULift.moduleEquiv : V₀ ≃ₗ[ℝ] _).symm
  let dW := (Pi.basisFun ℝ (Fin r)).map (ULift.moduleEquiv : W₀ ≃ₗ[ℝ] _).symm
  let a₀ : relativeSingularCohomology ℚ {v : V₀ | v ≠ 0} n :=
    relativeSingularCohomologyRationalization {v : V₀ | v ≠ 0} n
      (realOrientationClass dV dV.orientation)
  let b₀ : relativeSingularCohomology ℚ {v : W₀ | v ≠ 0} r :=
    relativeSingularCohomologyRationalization {v : W₀ | v ≠ 0} r
      (realOrientationClass dW dW.orientation)
  have hfactorA : relativeSingularCohomologyPullback ℚ e heA n
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.fst : C(V × W, V))
        (A := A) (B := {v | v ≠ 0}) (fun _ hz ↦ hz) n a) =
      relativeSingularCohomologyPullback ℚ f (A := A₀) (B := {v | v ≠ 0})
        (fun _ hz ↦ hz) n a₀ := by
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    simp only [hfirst]
    rw [relativeSingularCohomologyPullback_comp ℚ f (⟨eV, eV.continuous⟩ : C(V₀, V))
      (A := A₀) (B := {v : V₀ | v ≠ 0}) (C := {v : V | v ≠ 0})
      (fun _ hz ↦ hz) (fun _ hz hzero ↦ hz (eV.injective (hzero.trans eV.map_zero.symm))),
      ModuleCat.comp_apply, rationalOrientation_pullback_coordinates bV]
  have hfactorB : relativeSingularCohomologyPullback ℚ e heB r
      (relativeSingularCohomologyPullback ℚ (ContinuousMap.snd : C(V × W, W))
        (A := B) (B := {v | v ≠ 0}) (fun _ hz ↦ hz) r b) =
      relativeSingularCohomologyPullback ℚ g (A := B₀) (B := {v | v ≠ 0})
        (fun _ hz ↦ hz) r b₀ := by
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    simp only [hsecond]
    rw [relativeSingularCohomologyPullback_comp ℚ g (⟨eW, eW.continuous⟩ : C(W₀, W))
      (A := B₀) (B := {v : W₀ | v ≠ 0}) (C := {v : W | v ≠ 0})
      (fun _ hz ↦ hz) (fun _ hz hzero ↦ hz (eW.injective (hzero.trans eW.map_zero.symm))),
      ModuleCat.comp_apply, rationalOrientation_pullback_coordinates bW]
  have hdegree {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
      (f : C(S, T)) {A : Set S} {B : Set T} (hf : Set.MapsTo f A B)
      (k l : ℕ) (hkl : k = l) (c : relativeSingularCohomology ℚ B k) :
      relativeSingularCohomologyPullback ℚ f hf l
        (cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ B j)) hkl) c) =
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ A j)) hkl)
        (relativeSingularCohomologyPullback ℚ f hf k c) := by
    subst l
    rfl
  let inv : C(V × W, T₀) := ⟨eT.symm, eT.symm.continuous⟩
  have hinv : Set.MapsTo inv P P₀ :=
    fun _ hz hzero ↦ hz (eT.symm.injective (hzero.trans eT.symm.map_zero.symm))
  let := isIso_relativeSingularCohomologyPullback_of_inverse ℚ e inv heP hinv
    (by apply ContinuousMap.ext; exact eT.symm_apply_apply)
    (by apply ContinuousMap.ext; exact eT.apply_symm_apply) (r + n)
  apply (ConcreteCategory.bijective_of_isIso
    (relativeSingularCohomologyPullback ℚ e heP (r + n))).injective
  -- Pull the actual union cup to its original ordered coordinates before using normalization.
  rw [hdegree _ _ _ _ (Nat.add_comm n r), rationalOrientation_pullback_coordinates bT]
  have hU : Set.MapsTo e (A₀ ∪ B₀) (A ∪ B) :=
    fun _ hz ↦ hz.elim (fun hz ↦ Or.inl (heA hz)) (fun hz ↦ Or.inr (heB hz))
  have hcomp (c : relativeSingularCohomology ℚ (A ∪ B) (n + r)) :
      relativeSingularCohomologyPullback ℚ e heP (n + r)
        (relativeSingularCohomologyPullback ℚ (ContinuousMap.id (V × W)) hP (n + r) c) =
      relativeSingularCohomologyPullback ℚ (ContinuousMap.id T₀) hP₀ (n + r)
        (relativeSingularCohomologyPullback ℚ e hU (n + r) c) := by
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp,
      ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    rfl
  rw [hcomp]
  have hcup := relativeSingularCohomologyPullback_unionCup ℚ e
    (isOpen_ne_fun f.continuous continuous_const) (isOpen_ne_fun g.continuous continuous_const)
    (isOpen_ne_fun continuous_fst continuous_const) (isOpen_ne_fun continuous_snd continuous_const)
    heA heB n r
    (relativeSingularCohomologyPullback ℚ (ContinuousMap.fst : C(V × W, V))
      (A := A) (B := {v | v ≠ 0}) (fun _ hz ↦ hz) n a)
    (relativeSingularCohomologyPullback ℚ (ContinuousMap.snd : C(V × W, W))
      (A := B) (B := {w | w ≠ 0}) (fun _ hz ↦ hz) r b)
  have hcup' := hcup.trans (congrArg₂ (fun x y ↦
    relativeSingularCohomologyUnionCup ℚ A₀ B₀
      (isOpen_ne_fun f.continuous continuous_const)
      (isOpen_ne_fun g.continuous continuous_const) n r x y) hfactorA hfactorB)
  exact (congrArg (fun c ↦ cast
    (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P₀ k)) (Nat.add_comm n r))
    (relativeSingularCohomologyPullback ℚ (ContinuousMap.id T₀) hP₀ (n + r) c)) hcup').trans
      (realOrientationClass_rationalization_liftedPi_unionCup n r hP₀)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Interleaving each complex block agrees with the real basis of the ordered complex sum. -/
theorem complexBasisRealification_prod {n r : ℕ} {V W : Type u}
    [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
    (bV : Module.Basis (Fin n) ℂ V) (bW : Module.Basis (Fin r) ℂ W) :
    ((complexBasisRealification bV).prod (complexBasisRealification bW)).reindex
      (finSumFinEquiv : Fin (2 * n) ⊕ Fin (2 * r) ≃ Fin (2 * n + 2 * r)) =
    (complexBasisRealification ((bV.prod bW).reindex
      (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r)))).reindex
        (finCongr (Nat.mul_add 2 n r)) := by
  let ρ (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))
  apply DFunLike.ext
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · obtain ⟨⟨j, k⟩, rfl⟩ := (ρ n).surjective j
    have hidx : (finCongr (Nat.mul_add 2 n r)).symm
        (Fin.castAdd (2 * r) (ρ n (j, k))) = ρ (n + r) (Fin.castAdd r j, k) := by
      apply Fin.ext
      rfl
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply,
      finSumFinEquiv_symm_apply_castAdd, hidx]
    have hV : complexBasisRealification bV (ρ n (j, k)) = Complex.basisOneI k • bV j := by
      rw [complexBasisRealification, Module.Basis.reindex_apply]
      exact congrArg (Complex.basisOneI.smulTower' bV) ((ρ n).symm_apply_apply (j, k))
        |>.trans (Module.Basis.smulTower'_apply _ _ _)
    have hT : complexBasisRealification ((bV.prod bW).reindex finSumFinEquiv)
        (ρ (n + r) (Fin.castAdd r j, k)) =
      Complex.basisOneI k • ((bV.prod bW).reindex finSumFinEquiv) (Fin.castAdd r j) := by
      rw [complexBasisRealification, Module.Basis.reindex_apply]
      exact congrArg (Complex.basisOneI.smulTower' ((bV.prod bW).reindex finSumFinEquiv))
        ((ρ (n + r)).symm_apply_apply (Fin.castAdd r j, k))
        |>.trans (Module.Basis.smulTower'_apply _ _ _)
    rw [hT, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd]
    apply Prod.ext
    · simpa only [Module.Basis.prod_apply_inl_fst, Prod.smul_fst] using hV
    · simp only [Module.Basis.prod_apply_inl_snd, Prod.smul_snd, smul_zero]
  · obtain ⟨⟨j, k⟩, rfl⟩ := (ρ r).surjective j
    have hidx : (finCongr (Nat.mul_add 2 n r)).symm
        (Fin.natAdd (2 * n) (ρ r (j, k))) = ρ (n + r) (Fin.natAdd n j, k) := by
      apply Fin.ext
      change 2 * n + (k.val + 2 * j.val) = k.val + 2 * (n + j.val)
      omega
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply,
      finSumFinEquiv_symm_apply_natAdd, hidx]
    have hW : complexBasisRealification bW (ρ r (j, k)) = Complex.basisOneI k • bW j := by
      rw [complexBasisRealification, Module.Basis.reindex_apply]
      exact congrArg (Complex.basisOneI.smulTower' bW) ((ρ r).symm_apply_apply (j, k))
        |>.trans (Module.Basis.smulTower'_apply _ _ _)
    have hT : complexBasisRealification ((bV.prod bW).reindex finSumFinEquiv)
        (ρ (n + r) (Fin.natAdd n j, k)) =
      Complex.basisOneI k • ((bV.prod bW).reindex finSumFinEquiv) (Fin.natAdd n j) := by
      rw [complexBasisRealification, Module.Basis.reindex_apply]
      exact congrArg (Complex.basisOneI.smulTower' ((bV.prod bW).reindex finSumFinEquiv))
        ((ρ (n + r)).symm_apply_apply (Fin.natAdd n j, k))
        |>.trans (Module.Basis.smulTower'_apply _ _ _)
    rw [hT, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd]
    apply Prod.ext
    · simp only [Module.Basis.prod_apply_inr_fst, Prod.smul_fst, smul_zero]
    · simpa only [Module.Basis.prod_apply_inr_snd, Prod.smul_snd] using hW

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original complex orientations multiply to the canonical orientation of the complex sum. -/
theorem complexOrientationClass_rationalization_prod {n r : ℕ} {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
    (bV : Module.Basis (Fin n) ℂ V) (bW : Module.Basis (Fin r) ℂ W) :
    let A : Set (V × W) := {z | z.1 ≠ 0}
    let B : Set (V × W) := {z | z.2 ≠ 0}
    let P : Set (V × W) := {z | z ≠ 0}
    let bT := complexBasisRealification ((bV.prod bW).reindex
      (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r)))
    ∀ hP : Set.MapsTo (ContinuousMap.id (V × W)) P (A ∪ B),
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k)) (Nat.mul_add 2 n r).symm)
        (relativeSingularCohomologyPullback ℚ (ContinuousMap.id (V × W)) hP (2 * n + 2 * r)
          (relativeSingularCohomologyUnionCup ℚ A B
            (isOpen_ne_fun continuous_fst continuous_const)
            (isOpen_ne_fun continuous_snd continuous_const) (2 * n) (2 * r)
            (relativeSingularCohomologyPullback ℚ (ContinuousMap.fst : C(V × W, V))
              (A := A) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) (2 * n)
              (relativeSingularCohomologyRationalization {v : V | v ≠ 0} (2 * n)
                (realOrientationClass (complexBasisRealification bV)
                  (complexBasisRealification bV).orientation)))
            (relativeSingularCohomologyPullback ℚ (ContinuousMap.snd : C(V × W, W))
              (A := B) (B := {w | w ≠ 0}) (fun _ hw ↦ hw) (2 * r)
              (relativeSingularCohomologyRationalization {w : W | w ≠ 0} (2 * r)
                (realOrientationClass (complexBasisRealification bW)
                  (complexBasisRealification bW).orientation))))) =
      relativeSingularCohomologyRationalization P (2 * (n + r))
        (realOrientationClass bT bT.orientation) := by
  dsimp only
  intro hP
  let P : Set (V × W) := {z | z ≠ 0}
  let dV := complexBasisRealification bV
  let dW := complexBasisRealification bW
  let d := (dV.prod dW).reindex
    ((finSumFinEquiv : Fin (2 * n) ⊕ Fin (2 * r) ≃ Fin (2 * n + 2 * r)).trans
      (finCongr (Nat.add_comm (2 * n) (2 * r))))
  let b := complexBasisRealification ((bV.prod bW).reindex
    (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r)))
  have hdegree : 2 * r + 2 * n = 2 * (n + r) := by omega
  -- The complex realification uses the same first block followed by the same second block.
  have hb : d.reindex (finCongr hdegree) = b := by
    apply DFunLike.ext
    intro i
    have h := congrArg (fun B ↦ B (Fin.cast (Nat.mul_add 2 n r) i))
      (complexBasisRealification_prod bV bW)
    simp only [Module.Basis.reindex_apply, finCongr_symm, finCongr_apply,
      Fin.cast_cast, Fin.cast_refl, id_eq] at h
    simpa only [d, Module.Basis.reindex_apply, Equiv.symm_trans_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, dV, dW] using h
  have hclass {m k : ℕ} (hmk : m = k) (c : Module.Basis (Fin m) ℝ (V × W)) :
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ P j)) hmk)
        (relativeSingularCohomologyRationalization P m (realOrientationClass c c.orientation)) =
      relativeSingularCohomologyRationalization P k
        (realOrientationClass (c.reindex (finCongr hmk))
          (c.reindex (finCongr hmk)).orientation) := by
    subst k
    have hreindex : c.reindex (finCongr rfl) = c := by
      apply DFunLike.ext
      intro i
      rw [Module.Basis.reindex_apply]
      rfl
    rw [hreindex]
    rfl
  have hcast {k l m : ℕ} (hkl : k = l) (hlm : l = m) (hkm : k = m)
      (a : relativeSingularCohomology ℚ P k) :
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ P j)) hlm)
        (cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ P j)) hkl) a) =
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ P j)) hkm) a := by
    subst l
    subst m
    rfl
  -- The already normalized real cup is transported only in degree, without a permutation.
  have h := congrArg (cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ P j)) hdegree))
    (realOrientationClass_rationalization_prod dV dW hP)
  rw [hcast (Nat.add_comm (2 * n) (2 * r)) hdegree (Nat.mul_add 2 n r).symm,
    hclass hdegree d, hb] at h
  exact h

end AtiyahSinger
