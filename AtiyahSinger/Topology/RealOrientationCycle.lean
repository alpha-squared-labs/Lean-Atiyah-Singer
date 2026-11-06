/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCapProduct
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Orientation

/-!
# The actual signed affine simplex in a punctured real vector space

Public module ID: M2045.

The affine simplex with vertices minus the sum of a finite basis and then its
ordered basis vectors has zero in its interior. The sign prescribed by the
native real orientation multiplies its actual relative singular cycle.
This signed cycle is used in the local homology generator calculation.
-/

@[expose] public noncomputable section


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

open CategoryTheory Convexity Opposite
open scoped Simplicial

universe u

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.RealOrientationClass.1118800971._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.RealOrientationClass.1118800971._hygCtx._hyg.9"] in
/-- The affine simplex centered on zero with positively ordered edge vectors in b. -/
def realOrientationSimplex {r : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin r) ℝ V) :
    (TopCat.toSSet.obj (TopCat.of V)).obj (op ⦋r⦌) :=
  ((TopCat.of V).toSSetObjEquiv (op ⦋r⦌)).symm
    ⟨fun t ↦ ∑ i : Fin r, ((t.weights i.succ : ℝ) - (t.weights 0 : ℝ)) • b i,
      by fun_prop⟩

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.RealOrientationClass.1421001044._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.RealOrientationClass.1421001044._hygCtx._hyg.9"] in
/-- The relative simplex chain with the sign prescribed by the native orientation. -/
def realOrientationRelativeChain {r : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r)) :
    (relativeSingularChains ℤ (Set.ofPred (fun v : V ↦ v ≠ 0))).X r := by
  classical
  exact (relativeSingularChainsProjection ℤ (Set.ofPred (fun v : V ↦ v ≠ 0))).f r
    ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
      (R := singularCoefficient ℤ) (realOrientationSimplex b)
      (ULift.up (if b.orientation = o then 1 else -1)))

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.RealOrientationClass.3983851465._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.RealOrientationClass.3983851465._hygCtx._hyg.9"] in
/-- The signed simplex has boundary entirely in the complement of zero. -/
theorem realOrientationRelativeChain_mem_cycles {r : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r)) :
    ((relativeSingularChains ℤ (Set.ofPred (fun v : V ↦ v ≠ 0))).sc r).g
      (realOrientationRelativeChain b o) = 0 := by
  /- Stage 1: independence of the basis forces a zero image to have every
  barycentric coordinate equal to the zeroth one. Since the coordinates sum
  to one, each is 1/(r+1), and no boundary face contains that point.
  Stage 2: for positive rank every face chain lies in the punctured vector
  space. The actual relative chain projection kills its alternating boundary;
  multiplying the chain by either sign preserves this identity. For rank zero
  the singular-chain differential is zero, so the signed point is a cycle. -/
  classical
  let S := TopCat.toSSet.obj (TopCat.of V)
  let A := Set.ofPred (fun v : V ↦ v ≠ 0)
  let Q := relativeSingularChains ℤ A
  let π := relativeSingularChainsProjection ℤ A
  cases r with
  | zero =>
    -- In degree zero the nonnegative singular chain complex has no outgoing boundary.
    change Q.dFrom 0 (realOrientationRelativeChain b o) = 0
    rw [HomologicalComplex.dFrom_eq_zero]
    · rfl
    · simp [ComplexShape.down_Rel]
  | succ n =>
    -- A zero image would force every barycentric weight to coincide, so none can vanish.
    have hnonzero (t : StdSimplex ℝ (Fin (n + 2)))
        (i : Fin (n + 2)) (hi : t.weights i = 0) :
        (∑ j : Fin (n + 1), (t.weights j.succ - t.weights 0) • b j) ≠ 0 := by
      intro hz
      have heq (j : Fin (n + 1)) : t.weights j.succ = t.weights 0 := by
        have h := congrArg (fun v ↦ b.repr v j) hz
        simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h
        exact sub_eq_zero.mp h
      have hall (j : Fin (n + 2)) : t.weights j = t.weights 0 :=
        Fin.cases rfl heq j
      have hzero : t.weights 0 = 0 := (hall i).symm.trans hi
      have hone := t.total_of_fintype
      simp only [hall, hzero, Finset.sum_const_zero] at hone
      exact zero_ne_one hone
    -- Each actual face therefore lifts to a simplex in the original punctured space.
    have hface (i : Fin (n + 2)) :
        S.ιChainComplex (R := singularCoefficient ℤ) (S.δ i (realOrientationSimplex b)) ≫
          π.f n = 0 := by
      let face := (TopCat.of V).toSSetObjEquiv (op ⦋n⦌)
        (S.δ i (realOrientationSimplex b))
      have hpunctured (t : StdSimplex ℝ (Fin (n + 1))) : face t ∈ A := by
        apply hnonzero (t.map i.succAbove) i
        exact Finsupp.mapDomain_of_notMem_range t.weights i
          (by rintro ⟨j, hj⟩; exact i.succAbove_ne j hj)
      let τ := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm
        (⟨fun t ↦ ⟨face t, hpunctured t⟩, face.continuous.subtype_mk _⟩ :
          C(StdSimplex ℝ (Fin (n + 1)), A))
      let f := TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, V)))
      have heq : f.app (op ⦋n⦌) τ = S.δ i (realOrientationSimplex b) := rfl
      rw [← heq, ← SSet.ι_chainComplexMap_f]
      erw [Category.assoc]
      have hzero := congrArg (fun g ↦ g.f n)
        (Limits.cokernel.condition (singularSubspaceChains ℤ A))
      change (singularSubspaceChains ℤ A).f n ≫ π.f n = 0 at hzero
      change _ ≫ ((singularSubspaceChains ℤ A).f n ≫ π.f n) = 0
      erw [hzero, Limits.comp_zero]
    -- The original alternating boundary is killed face by face by this same quotient.
    have hd : S.ιChainComplex (R := singularCoefficient ℤ) (realOrientationSimplex b) ≫
        π.f (n + 1) ≫ Q.d (n + 1) n = 0 := by
      erw [π.comm, ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
      apply Finset.sum_eq_zero
      intro i _hi
      erw [Preadditive.zsmul_comp, hface]
      exact smul_zero _
    change Q.dFrom (n + 1) (realOrientationRelativeChain b o) = 0
    rw [HomologicalComplex.dFrom_eq (r := rfl), ModuleCat.comp_apply]
    change (Q.xNextIso rfl).inv
      ((S.ιChainComplex (R := singularCoefficient ℤ) (realOrientationSimplex b) ≫
        π.f (n + 1) ≫ Q.d (n + 1) n)
        (ULift.up (if b.orientation = o then 1 else -1))) = 0
    rw [hd]
    exact map_zero _

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.RealOrientationClass.3134052895._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.RealOrientationClass.3134052895._hygCtx._hyg.9"] in
/-- The local relative homology class selected by the signed actual affine simplex. -/
def realOrientationCycle {r : ℕ} {V : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin r) ℝ V) (o : Orientation ℝ V (Fin r)) :
    relativeSingularHomology ℤ (Set.ofPred (fun v : V ↦ v ≠ 0)) r :=
  relativeSingularCycleClass ℤ (Set.ofPred (fun v : V ↦ v ≠ 0)) r
    ⟨realOrientationRelativeChain b o, realOrientationRelativeChain_mem_cycles b o⟩

end AtiyahSinger
