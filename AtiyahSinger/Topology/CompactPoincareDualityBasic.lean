/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomology
public import AtiyahSinger.Topology.HomologicalOrientation
public import AtiyahSinger.Topology.RelativeCapProduct
public import AtiyahSinger.Topology.RelativeSingularCohomologyVanishing

/-!
# The specified compact-support cap-duality map

Public module ID: M1643.

The original compact-relative fundamental classes define a compatible family of
actual relative cap maps. Descent through the original compact-support colimit
retains the chosen orientation and each compact representative. This foundational
module separates the map and its normalization from the Poincare-duality theorem,
so its already proved open-extension naturality can be used without an import cycle.
-/

@[expose] public noncomputable section

/- This local syntax preserves the specified hierarchical names of anonymous
  instance binders in declaration headers. It skips proof bodies while traversing
  the command, so naming the binders does not alter the proof expressions. -/
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

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.CompactPoincareDuality.3750496118._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.3750496118._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.3750496118._hygCtx._hyg.22",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.3750496118._hygCtx._hyg.25"] in
/-- Cap with the rational image of the specified integral fundamental class over K. -/
def compactRelativeDuality {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    (O : HomologicalOrientation n M) (K : Compacts M)
    (p q : ℕ) (h : p + q = n) :
    relativeSingularCohomology ℚ ((K : Set M)ᶜ) p →ₗ[ℚ] singularHomology ℚ M q :=
  (relativeSingularCapProduct ℚ ((K : Set M)ᶜ) p q).flip
    ((eqToIso (congrArg (relativeSingularHomology ℚ ((K : Set M)ᶜ)) h.symm)).hom
      (rationalCompactRelativeFundamentalClass O K))

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.CompactPoincareDuality.1052650428._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.1052650428._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.1052650428._hygCtx._hyg.22",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.1052650428._hygCtx._hyg.25"] in
/-- Enlarging the compact support preserves the duality class in ordinary homology. -/
theorem compactRelativeDuality_support {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    (O : HomologicalOrientation n M)
    {K L : Compacts M} (hKL : K ≤ L) (p q : ℕ) (h : p + q = n)
    (a : relativeSingularCohomology ℚ ((K : Set M)ᶜ) p) :
    compactRelativeDuality O L p q h
        ((compactSupportCohomologyFunctor ℚ M p).map (homOfLE hKL) a) =
      compactRelativeDuality O K p q h a := by
  -- Eliminating the degree equality makes both cap maps use the literal degree p + q.
  subst n
  change relativeSingularCapProduct ℚ ((L : Set M)ᶜ) p q
      (relativeSingularCohomologyRestriction ℚ ((L : Set M)ᶜ) ((K : Set M)ᶜ)
        (Set.compl_subset_compl.mpr hKL) p a) (rationalCompactRelativeFundamentalClass O L) =
    relativeSingularCapProduct ℚ ((K : Set M)ᶜ) p q a
      (rationalCompactRelativeFundamentalClass O K)
  -- Cap naturality and the normalized fundamental classes use the same inclusion of complements.
  rw [relativeSingularCapProduct_inclusion,
    rationalCompactRelativeFundamentalClass_inclusion O hKL]

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.CompactPoincareDuality.4144328483._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.4144328483._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.4144328483._hygCtx._hyg.22",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.4144328483._hygCtx._hyg.25"] in
/-- The actual cap-duality map descended through the original compact-support colimit. -/
def compactPoincareDuality {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    (O : HomologicalOrientation n M)
    (p q : ℕ) (h : p + q = n) :
    compactSupportCohomology ℚ M p ⟶ singularHomology ℚ M q :=
  colimit.desc (compactSupportCohomologyFunctor ℚ M p)
    { pt := singularHomology ℚ M q
      ι :=
        { app := fun K ↦ ModuleCat.ofHom (compactRelativeDuality O K p q h)
          naturality := by
            intro K L f
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro a
            exact compactRelativeDuality_support O (leOfHom f) p q h a } }

legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.CompactPoincareDuality.4072305862._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.4072305862._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.4072305862._hygCtx._hyg.22",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.4072305862._hygCtx._hyg.25"] in
/-- A compact representative is sent to cap with its own normalized relative fundamental class. -/
theorem compactPoincareDuality_representative {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    (O : HomologicalOrientation n M)
    (K : Compacts M) (p q : ℕ) (h : p + q = n)
    (a : relativeSingularCohomology ℚ ((K : Set M)ᶜ) p) :
    compactPoincareDuality O p q h (compactSupportCohomologyClass ℚ M K p a) =
      compactRelativeDuality O K p q h a := by
  -- Evaluate the defining colimit descent on its specified K-th representative map.
  change (colimit.ι (compactSupportCohomologyFunctor ℚ M p) K ≫
    colimit.desc (compactSupportCohomologyFunctor ℚ M p) _) a = _
  rw [colimit.ι_desc]
  rfl

-- The original orientation parameter is retained although this vanishing needs no orientation.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
legacy_instance_names
  ["inst._@.AtiyahSinger.Topology.CompactPoincareDuality.1407311230._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.1407311230._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.1407311230._hygCtx._hyg.22",
    "inst._@.AtiyahSinger.Topology.CompactPoincareDuality.1407311230._hygCtx._hyg.25"] in
/-- Compactly supported cohomology vanishes above the manifold dimension. -/
theorem compactSupportCohomology_subsingleton_above_dim {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    (O : HomologicalOrientation n M)
    (p : ℕ) (h : n < p) : Subsingleton (compactSupportCohomology ℚ M p) := by
  -- Each compact-relative cohomology group vanishes by the field duality argument.
  have hzero (a : compactSupportCohomology ℚ M p) : a = 0 := by
    obtain ⟨K, b, hb⟩ := compactSupportCohomology_exists_representative ℚ M p a
    have := relativeSingularHomology_subsingleton_compact_manifold ℚ n
      (K : Set M) K.isCompact p h
    have := subsingleton_relativeSingularCohomology_of_subsingleton_homology ℚ
      ((K : Set M)ᶜ) p
    have hb0 : b = 0 := Subsingleton.elim _ _
    rw [hb0, map_zero] at hb
    exact hb.symm
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩


end AtiyahSinger
