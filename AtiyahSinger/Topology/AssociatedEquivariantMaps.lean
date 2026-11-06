/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedEquivariantBundle

/-!
# Descent of the original equivariant bundle maps

Public module ID: M1533.

An original continuous equivariant map of finite vector bundles over Y descends
to the associated vector families over the same quotient P associated Y. On
every actual representative it sends [p,(y,v)] to [p,(y,f_y(v))]. This determines
one continuous bundle map between the existing associated fibers and topologies.
Fiberwise bijectivity is preserved using the same representative coordinates.
The associated isomorphism retains this descended forward map; its inverse
continuity follows from the existing finite-rank bundle isomorphism criterion.

Sources: HU IV.5--6 and SG II.3 and Appendix A for associated-bundle maps.
The explicit varying-fiber map and bijectivity certificates are project
supplements to that standard functorial construction. No compactness,
separation, local compactness, metric, or continuous choice of representatives
is assumed. The original descended maps and their representative formulas
are proved below for these same fibers and total topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : Y → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant

/-- The original map has a unique descent with its exact formula on every representative. -/
theorem existsUnique_associatedEquivariantHom (hP : IsPrincipalBundle G projection)
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (f : Hom E F) (hf : f.IsEquivariant ρE ρF) :
    ∃! a : Hom (AssociatedEquivariantFiber hP ρE) (AssociatedEquivariantFiber hP ρF),
      ∀ (p : P) (y : Y) {z : AssociatedBundle G P Y}
        (hz : associatedBundleMk G P Y p y = z) (v : E y),
        a.linearMap z (associatedEquivariantFiberMk hP ρE p y hz v) =
          associatedEquivariantFiberMk hP ρF p y hz (f.linearMap y v) := by
  /- Stage 1: the original total map of f intertwines the two original
  total-space actions because hf is precisely its moving-fiber equation.
  The existing associatedBundleMap therefore descends [p,(y,v)] to
  [p,(y,f_y(v))] continuously on the two actual associated total quotients.
  It commutes with their original projections to [p,y], so restrict it to
  the actual associated fiber subtypes at every z.
  Stage 2: use a common representative (p,y) of z. Its two representative
  maps are linear and bijective for the existing transferred algebra, and
  the descended map between those coordinates is exactly the original f_y.
  This proves fiberwise linearity. Transport the continuous total quotient
  map only through the existing associatedEquivariantTotalHomeomorphs to
  give continuity in the specified associated-family total topologies.
  Stage 3: every vector in the source associated fiber has such a
  representative by associatedEquivariantFiberMk_bijective. The displayed
  formula therefore determines every fiber map, and bundle-map extensionality
  gives uniqueness. No unrelated continuous map or representative family is chosen. -/
  classical
  let : MulAction G (TotalSpace Unit E) := ρE.toMulAction
  let : MulAction G (TotalSpace Unit F) := ρF.toMulAction
  let : ContinuousSMul G (TotalSpace Unit E) := ⟨ρE.continuous_action⟩
  let : ContinuousSMul G (TotalSpace Unit F) := ⟨ρF.continuous_action⟩
  have htotal (g : G) (w : TotalSpace Unit E) : f.totalMap (g • w) = g • f.totalMap w :=
    congrArg (fun v : F (g • w.proj) ↦ (⟨g • w.proj, v⟩ : TotalSpace Unit F))
      (hf g w.proj w.snd)
  let qmap := associatedBundleMap (G := G) (P := P) ⟨f.totalMap, f.continuous_total⟩ htotal
  have hproj (q : AssociatedBundle G P (TotalSpace Unit E)) :
      associatedEquivariantProjection ρF (qmap q) = associatedEquivariantProjection ρE q := by
    induction q using Quotient.inductionOn with
    | h w => rfl
  let fiberMap (z : AssociatedBundle G P Y) (v : AssociatedEquivariantFiber hP ρE z) :
      AssociatedEquivariantFiber hP ρF z := ⟨qmap v.val, (hproj v.val).trans v.property⟩
  have hformula (p : P) (y : Y) {z : AssociatedBundle G P Y}
      (hz : associatedBundleMk G P Y p y = z) (v : E y) :
      fiberMap z (associatedEquivariantFiberMk hP ρE p y hz v) =
        associatedEquivariantFiberMk hP ρF p y hz (f.linearMap y v) := rfl
  -- The same representative on both sides identifies the descended fiber map with f_y.
  have hlinear (z : AssociatedBundle G P Y) : IsLinearMap ℂ (fiberMap z) := by
    let p := (Quotient.out z).1
    let y := (Quotient.out z).2
    have hz : associatedBundleMk G P Y p y = z := Quotient.out_eq z
    have hE := associatedEquivariantFiberMk_isLinear hP ρE p y hz
    have hF := associatedEquivariantFiberMk_isLinear hP ρF p y hz
    have hsurj := (associatedEquivariantFiberMk_bijective hP ρE p y hz).2
    constructor
    · intro u v
      obtain ⟨u₀, rfl⟩ := hsurj u
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hE.map_add, hformula, hformula, hformula, map_add, hF.map_add]
    · intro c v
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hE.map_smul, hformula, hformula, map_smul, hF.map_smul]
  let HE := associatedEquivariantTotalHomeomorph hP ρE
  let HF := associatedEquivariantTotalHomeomorph hP ρF
  let a : Hom (AssociatedEquivariantFiber hP ρE) (AssociatedEquivariantFiber hP ρF) := {
    linearMap z := IsLinearMap.mk' (fiberMap z) (hlinear z)
    continuous_total := by
      -- Continuity refers to the original total quotients via their existing homeomorphisms.
      have hc := HF.symm.continuous_toFun.comp (qmap.continuous.comp HE.continuous_toFun)
      apply hc.congr
      intro w
      apply HF.injective
      exact HF.apply_symm_apply (qmap (HE w)) }
  refine ⟨a, ?_, ?_⟩
  · intro p y z hz v
    exact hformula p y hz v
  · -- Every actual fiber vector has these coordinates, so the formula forces uniqueness.
    intro b hb
    apply Hom.ext
    intro z
    apply LinearMap.ext
    intro v
    let p := (Quotient.out z).1
    let y := (Quotient.out z).2
    have hz : associatedBundleMk G P Y p y = z := Quotient.out_eq z
    obtain ⟨v₀, rfl⟩ := (associatedEquivariantFiberMk_bijective hP ρE p y hz).2 v
    exact hb p y hz v₀

/-- The same descended bundle map, chosen only by its formula on all original representatives. -/
def associatedEquivariantHom (hP : IsPrincipalBundle G projection)
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (f : Hom E F) (hf : f.IsEquivariant ρE ρF) :
    Hom (AssociatedEquivariantFiber hP ρE) (AssociatedEquivariantFiber hP ρF) :=
  (existsUnique_associatedEquivariantHom hP ρE ρF f hf).choose

/-- The selected descent retains the original fiber-map value on every actual representative. -/
theorem associatedEquivariantHom_apply (hP : IsPrincipalBundle G projection)
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (f : Hom E F) (hf : f.IsEquivariant ρE ρF) (p : P) (y : Y)
    {z : AssociatedBundle G P Y} (hz : associatedBundleMk G P Y p y = z) (v : E y) :
    (associatedEquivariantHom hP ρE ρF f hf).linearMap z
        (associatedEquivariantFiberMk hP ρE p y hz v) =
      associatedEquivariantFiberMk hP ρF p y hz (f.linearMap y v) := by
  /- Read the representative formula from the exact unique existence
  certificate used to select this map. Its original principal point, base
  point, vector, specified actions and descended fiber are all unchanged. -/
  exact (existsUnique_associatedEquivariantHom hP ρE ρF f hf).choose_spec.1 p y hz v

/-- Original fiberwise bijectivity is retained on each actual associated fiber. -/
theorem associatedEquivariantHom_bijective (hP : IsPrincipalBundle G projection)
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (f : Hom E F) (hf : f.IsEquivariant ρE ρF)
    (hb : ∀ y : Y, Function.Bijective (f.linearMap y)) (z : AssociatedBundle G P Y) :
    Function.Bijective ((associatedEquivariantHom hP ρE ρF f hf).linearMap z) := by
  /- Choose one original representative (p,y) of z. Both representative
  maps are bijective, and associatedEquivariantHom_apply gives a commuting
  square whose coordinate map is exactly f_y. Its supplied bijectivity
  therefore implies injectivity and surjectivity of the specified descended
  map. The pointwise choice is only algebraic; no continuous family of
  representatives or inverse maps on quotient carriers is postulated. -/
  classical
  let p := (Quotient.out z).1
  let y := (Quotient.out z).2
  have hz : associatedBundleMk G P Y p y = z := Quotient.out_eq z
  have hE := associatedEquivariantFiberMk_bijective hP ρE p y hz
  have hF := associatedEquivariantFiberMk_bijective hP ρF p y hz
  constructor
  · -- Injectivity is the original fiber injectivity in the same two representative coordinates.
    intro u v huv
    obtain ⟨u₀, rfl⟩ := hE.2 u
    obtain ⟨v₀, rfl⟩ := hE.2 v
    rw [associatedEquivariantHom_apply, associatedEquivariantHom_apply] at huv
    exact congrArg (associatedEquivariantFiberMk hP ρE p y hz)
      ((hb y).1 (hF.1 huv))
  · -- An original fiber preimage gives an actual quotient-fiber preimage with this representative.
    intro v
    obtain ⟨v₀, rfl⟩ := hF.2 v
    obtain ⟨u₀, hu₀⟩ := (hb y).2 v₀
    refine ⟨associatedEquivariantFiberMk hP ρE p y hz u₀, ?_⟩
    rw [associatedEquivariantHom_apply, hu₀]

/-- An original equivariant isomorphism descends with exactly its original descended forward map. -/
def associatedEquivariantIso (hP : IsPrincipalBundle G projection)
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (e : Iso E F) (he : e.IsEquivariant ρE ρF) :
    Iso (AssociatedEquivariantFiber hP ρE) (AssociatedEquivariantFiber hP ρF) :=
  (associatedEquivariantHom hP ρE ρF e.toHom he).toIso
    (associatedEquivariantHom_bijective hP ρE ρF e.toHom he
      (fun y ↦ (e.linearEquiv y).bijective))

end AtiyahSinger
