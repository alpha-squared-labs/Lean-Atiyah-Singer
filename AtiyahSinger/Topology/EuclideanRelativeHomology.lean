/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularMayerVietoris
public import AtiyahSinger.Topology.SingularHomologyContraction
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dimension bounds for Euclidean local singular homology

Public module ID: M1825.

Punctured products are covered by the complements of the two opposite closed
half axes. Each member contracts to its endpoint, while their intersection
retracts to the punctured transverse space. The actual open-cover homology
sequence therefore supplies induction on dimension over any coefficient ring.
The relative pair sequence then gives local vanishing above the dimension.
The coordinate calculation is proved once in an arbitrary universe; its ordinary
version follows by the zero-universe specialization and the original homology maps.
-/

@[expose] public noncomputable section

/- The header macro names anonymous instance binders while leaving theorem bodies unchanged. -/
local syntax "legacy_instance_names " "[" str,* "]" " in " command : command
local macro_rules
  | `(legacy_instance_names [$names:str,*] in $cmd:command) => do
    let names := names.getElems
    let (cmd, i) ← (cmd.raw.replaceM (m := StateT Nat Lean.MacroM) fun stx => do
      let i ← get
      if stx.isOfKind ``Lean.Parser.Command.declValSimple then
        return some stx
      else if stx.isOfKind ``Lean.Parser.Term.instBinder then
        if stx[1].getNumArgs != 0 then
          liftM (Lean.Macro.throwErrorAt stx "expected an anonymous instance binder")
        if i ≥ names.size then
          liftM (Lean.Macro.throwErrorAt stx "too many instance binders")
        let name := names[i]!.getString.splitOn "." |>.foldl (fun name part =>
          match part.toNat? with
          | some k => Lean.Name.num name k
          | none => Lean.Name.str name part) Lean.Name.anonymous
        let id := Lean.mkIdent name
        set (i + 1)
        let type : Lean.TSyntax `term := ⟨stx[2]⟩
        return some (← `(bracketedBinder| [$id:ident : $type:term])).raw
      else
        return none).run 0
    if i != names.size then
      Lean.Macro.throwError "unused instance names"
    return cmd


namespace AtiyahSinger

open scoped unitInterval

universe u

variable (R : Type) [CommRing R]

/-- The punctured product has vanishing homology one degree above the punctured factor. -/
theorem subsingleton_singularHomology_punctured_prod
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    [Subsingleton (singularHomology R {x : E | x ≠ 0} j)] :
    Subsingleton (singularHomology R {z : ℝ × E | z ≠ 0} (j + 1)) := by
  let X := {z : ℝ × E | z ≠ 0}
  let A (s : ℝ) : Set (ℝ × E) := {z | 0 < s * z.1 ∨ z.2 ≠ 0}
  let U (s : ℝ) : Set X := {z | z.val ∈ A s}
  have hne (s : ℝ) {z : ℝ × E} (hz : z ∈ A s) : z ≠ 0 := by
    intro h
    rcases hz with hz | hz
    · simp [h] at hz
    · exact hz (congrArg Prod.snd h)
  -- The same straight segments contract the two complements of the opposite half axes.
  have hcontract (s : ℝ) (hs : s ≠ 0) : ContractibleSpace (U s) := by
    have hstar : StarConvex ℝ (s, (0 : E)) (A s) := by
      intro z hz a b ha hb hab
      change 0 < s * (a * s + b * z.1) ∨ a • (0 : E) + b • z.2 ≠ 0
      by_cases hzero : b = 0
      · left
        have ha' : a = 1 := by linarith
        simpa only [ha', hzero, one_mul, zero_mul, add_zero] using mul_self_pos.mpr hs
      · have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hzero)
        rcases hz with hz | hz
        · left
          have hsq : 0 ≤ a * s ^ 2 := mul_nonneg ha (sq_nonneg s)
          have hp : 0 < b * (s * z.1) := mul_pos hb' hz
          nlinarith
        · right
          simpa using smul_ne_zero hzero hz
    let : ContractibleSpace (A s) := hstar.contractibleSpace
      ⟨(s, 0), Or.inl (by simpa [pow_two] using sq_pos_of_ne_zero hs)⟩
    let e : A s ≃ₜ U s :=
      { toFun z := ⟨⟨z.val, hne s z.property⟩, z.property⟩
        invFun z := ⟨z.val.val, z.property⟩
        left_inv _ := rfl
        right_inv _ := rfl
        continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
        continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
    exact e.symm.contractibleSpace
  have hOpen (s : ℝ) : IsOpen (U s) := by
    exact (isOpen_lt continuous_const
      (continuous_const.mul (continuous_fst.comp continuous_subtype_val))).union
        (isOpen_ne_fun (continuous_snd.comp continuous_subtype_val) continuous_const)
  have hcover : U 1 ∪ U (-1) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z.val.2 = 0
    · have hfirst : z.val.1 ≠ 0 := by
        intro h
        exact z.property (Prod.ext h hz)
      rcases lt_or_gt_of_ne hfirst with h | h
      · exact Or.inr (Or.inl (by simpa [A, U] using neg_pos.mpr h))
      · exact Or.inl (Or.inl (by simpa [A, U] using h))
    · exact Or.inl (Or.inr hz)
  have hinter (z : X) : z ∈ U 1 ∩ U (-1) ↔ z.val.2 ≠ 0 := by
    constructor
    · rintro ⟨h₁, h₂⟩ hzero
      have hpos : 0 < z.val.1 := by simpa [U, A, hzero] using h₁
      have hneg : z.val.1 < 0 := by simpa [U, A, hzero] using h₂
      exact (lt_asymm hpos hneg)
    · intro h
      exact ⟨Or.inr h, Or.inr h⟩
  -- On the intersection only the transverse vector matters; contract the first coordinate.
  let f : C(↥(U 1 ∩ U (-1)), {x : E | x ≠ 0}) :=
    ⟨fun z ↦ ⟨z.val.val.2, (hinter z.val).mp z.property⟩, by fun_prop⟩
  let g : C({x : E | x ≠ 0}, ↥(U 1 ∩ U (-1))) :=
    ⟨fun x ↦ ⟨⟨(0, x.val), fun h ↦ x.property (congrArg Prod.snd h)⟩,
      ⟨Or.inr x.property, Or.inr x.property⟩⟩, by fun_prop⟩
  have hgf : (g.comp f).Homotopic (ContinuousMap.id ↥(U 1 ∩ U (-1))) := by
    refine ⟨{ toFun p := ⟨⟨((p.1 : ℝ) * p.2.val.val.1, p.2.val.val.2),
                fun h ↦ (hinter p.2.val).mp p.2.property (congrArg Prod.snd h)⟩,
                ⟨Or.inr ((hinter p.2.val).mp p.2.property),
                  Or.inr ((hinter p.2.val).mp p.2.property)⟩⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      simp [g, f]
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      simp
  let := subsingleton_singularHomology_of_homotopy_retract R f g hgf j
  let := hcontract 1 one_ne_zero
  let := hcontract (-1) (by norm_num)
  let := subsingleton_singularHomology_of_contractible R (U 1) (j + 1) (by omega)
  let := subsingleton_singularHomology_of_contractible R (U (-1)) (j + 1) (by omega)
  exact singularHomology_subsingleton_of_openCover R (U 1) (U (-1))
    (hOpen 1) (hOpen (-1)) hcover j

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.EuclideanHomologyULift.812749332._hygCtx._hyg.3"] in
/-- Punctured coordinate space has no singular homology in or above its dimension. -/
theorem subsingleton_singularHomology_punctured_pi_ulift (R : Type) [CommRing R]
    (n k : ℕ) (hk : n ≤ k) :
    Subsingleton (singularHomology R {x : Fin n → ULift.{u} ℝ | x ≠ 0} k) := by
  induction n generalizing k with
  | zero =>
    -- The punctured zero-dimensional space is empty, including in degree zero.
    let : IsEmpty {x : Fin 0 → ULift.{u} ℝ | x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    exact subsingleton_singularHomology_of_isEmpty R _ k
  | succ n ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    let := ih j (by omega)
    let := subsingleton_singularHomology_punctured_prod R (Fin n → ULift.{u} ℝ) j
    -- Split off the first coordinate and apply the punctured-product calculation.
    let e : (Fin (n + 1) → ULift.{u} ℝ) ≃ₜ ℝ × (Fin n → ULift.{u} ℝ) :=
      { toFun x := ((x 0).down, fun i ↦ x i.succ)
        invFun z := Fin.cases (ULift.up z.1) z.2
        left_inv x := by funext i; exact Fin.cases rfl (fun _ ↦ rfl) i
        right_inv _ := rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by
          apply continuous_pi
          intro i
          exact Fin.cases (continuous_uliftUp.comp continuous_fst)
            (fun i ↦ (continuous_apply i).comp continuous_snd) i }
    have hzero : e 0 = 0 := rfl
    let ep : {x : Fin (n + 1) → ULift.{u} ℝ | x ≠ 0} ≃ₜ
        {z : ℝ × (Fin n → ULift.{u} ℝ) | z ≠ 0} :=
      { toFun x := ⟨e x, fun h ↦ x.property (e.injective (h.trans hzero.symm))⟩
        invFun z := ⟨e.symm z, fun h ↦ z.property (by
          calc
            z.val = e (e.symm z.val) := (e.apply_symm_apply z.val).symm
            _ = 0 := by rw [h, hzero])⟩
        left_inv x := Subtype.ext (e.symm_apply_apply x)
        right_inv z := Subtype.ext (e.apply_symm_apply z)
        continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
    exact subsingleton_singularHomology_of_homotopy_retract R
      ep.toHomotopyEquiv.toFun ep.toHomotopyEquiv.invFun ep.toHomotopyEquiv.left_inv (j + 1)

/-- Punctured coordinate space has no singular homology in or above its dimension. -/
theorem subsingleton_singularHomology_punctured_pi (n k : ℕ) (hk : n ≤ k) :
    Subsingleton (singularHomology R {x : Fin n → ℝ | x ≠ 0} k) := by
  -- Specialize the universe-polymorphic calculation without changing the coefficient object.
  let := subsingleton_singularHomology_punctured_pi_ulift.{0} R n k hk
  -- Both coordinate spaces now lie in Type 0, so the original homology maps apply.
  let e : (Fin n → ℝ) ≃ₜ (Fin n → ULift.{0} ℝ) :=
    Homeomorph.piCongrRight (fun _ : Fin n ↦ Homeomorph.ulift.symm)
  have hzero : e 0 = 0 := rfl
  let ep : {x : Fin n → ℝ | x ≠ 0} ≃ₜ {y : Fin n → ULift.{0} ℝ | y ≠ 0} :=
    e.subtype (fun x ↦ by rw [← hzero]; exact e.injective.ne_iff.symm)
  exact subsingleton_singularHomology_of_homotopy_retract R
    ep.toHomotopyEquiv.toFun ep.toHomotopyEquiv.invFun ep.toHomotopyEquiv.left_inv k

/-- Puncturing a Euclidean space leaves no singular homology in or above its dimension. -/
theorem subsingleton_singularHomology_punctured_euclidean (n k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (hk : n ≤ k) :
    Subsingleton (singularHomology R {y : EuclideanSpace ℝ (Fin n) | y ≠ x} k) := by
  let := subsingleton_singularHomology_punctured_pi R n k hk
  -- Translation and the native coordinate equivalence identify the actual complements.
  let e := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  let ep : {y : EuclideanSpace ℝ (Fin n) | y ≠ x} ≃ₜ
      {z : Fin n → ℝ | z ≠ 0} :=
    { toFun y := ⟨e (y.val - x), fun h ↦ y.property (sub_eq_zero.mp
        ((EuclideanSpace.equiv (Fin n) ℝ).map_eq_zero_iff.mp h))⟩
      invFun z := ⟨e.symm z + x, fun h ↦ z.property (by
        have hz : e.symm z.val = 0 := (add_right_cancel (h.trans (zero_add x).symm))
        simpa [e] using congrArg e hz)⟩
      left_inv y := Subtype.ext (by simp)
      right_inv z := Subtype.ext (by simp)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact subsingleton_singularHomology_of_homotopy_retract R
    ep.toHomotopyEquiv.toFun ep.toHomotopyEquiv.invFun ep.toHomotopyEquiv.left_inv k

/-- Euclidean local relative homology vanishes strictly above the dimension. -/
theorem subsingleton_relativeSingularHomology_euclidean (n k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (hk : n < k) :
    Subsingleton (relativeSingularHomology R
      (Set.ofPred (fun y : EuclideanSpace ℝ (Fin n) ↦ y ≠ x)) k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- The pair sequence has zero adjacent terms: the ambient space contracts,
  -- and the punctured space vanishes in degree at least the dimension.
  let := subsingleton_singularHomology_of_contractible R
    (EuclideanSpace ℝ (Fin n)) (j + 1) (by omega)
  let := subsingleton_singularHomology_punctured_euclidean R n j x (by omega)
  exact relativeSingularHomology_subsingleton_of_absolute R _ j

end AtiyahSinger
