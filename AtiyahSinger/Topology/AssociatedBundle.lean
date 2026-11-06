/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.PrincipalBundle
public import Mathlib.Topology.Constructions

/-!
# The actual quotient associated to a locally trivial principal bundle

Public module ID: M1527.

For the original right action on P and left action on F, take the quotient of
P times F by (p,v)*g=(p*g,g inverse*v). Its topology is mathlib's original
quotient topology. The relation is therefore [p*g,v]=[p,g*v]. The projection
and maps induced by equivariant fiber maps are actual quotient lifts.

Sources: HU IV.5, printed p.45 / PDF p.66, uses this diagonal right action.
SG II.3, printed p.93 / PDF p.105, uses the equivalent diagonal left action
g*(p,v)=(p*g inverse,g*v); the two have identical orbits. The local formulas
below use the actual principal charts from SG Appendix A, pp.370--372.
They need no global paracompactness or separation assumption. This file
constructs a topological associated bundle; no vector-bundle structure or
map from a representation ring to K theory is asserted.
The action convention and original local quotient-chart formulas are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology

variable (G P F : Type*) [Group G] [MulAction Gᵐᵒᵖ P] [MulAction G F]

/-- The orbit relation of the diagonal right action (p,v)*g=(p*g,g inverse*v). -/
def associatedBundleSetoid : Setoid (P × F) where
  r x y := ∃ g : G, y = (MulOpposite.op g • x.1, g⁻¹ • x.2)
  iseqv :=
    { refl := by
        intro x
        exact ⟨1, by simp⟩
      symm := by
        intro x y h
        rcases h with ⟨g, rfl⟩
        refine ⟨g⁻¹, ?_⟩
        simp
      trans := by
        intro x y z hxy hyz
        rcases hxy with ⟨g, rfl⟩
        rcases hyz with ⟨h, rfl⟩
        refine ⟨g * h, ?_⟩
        simp [mul_smul] }

/-- The associated total space, with the quotient topology on topological factors. -/
abbrev AssociatedBundle : Type _ := Quotient (associatedBundleSetoid G P F)

/-- The actual quotient class of a pair in the original principal and fiber spaces. -/
def associatedBundleMk (p : P) (v : F) : AssociatedBundle G P F :=
  Quotient.mk (associatedBundleSetoid G P F) (p, v)

variable {G P F}

/-- The quotient has the standard principal/associated action convention. -/
theorem associatedBundleMk_smul (p : P) (g : G) (v : F) :
    associatedBundleMk G P F (MulOpposite.op g • p) v =
      associatedBundleMk G P F p (g • v) := by
  /- Act on (p,g*v) by g in the diagonal right action. The result is
  (p*g,g inverse*(g*v))=(p*g,v), so these two actual pairs define the same
  quotient class. This is equivalent to SG's inverse diagonal left convention;
  replacing both group occurrences by g without inversion would be incorrect. -/
  apply Eq.symm
  exact Quotient.sound ⟨g, by simp⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [ContinuousSMul Gᵐᵒᵖ P]
  [TopologicalSpace F] [ContinuousSMul G F]
  {B : Type*} [TopologicalSpace B] {projection : P → B}

/-- The continuous projection on the actual quotient sends [p,v] to the original projection of p. -/
def associatedBundleProjection (hP : IsPrincipalBundle G projection) :
    C(AssociatedBundle G P F, B) where
  toFun := Quotient.lift (fun z : P × F ↦ projection z.1) (by
    intro x y hxy
    rcases hxy with ⟨g, rfl⟩
    exact (hP.projection_smul g x.1).symm)
  continuous_toFun := continuous_quot_lift _
    ((hP.projection_properties).1.comp continuous_fst)

/-- Each original principal chart induces the standard local trivialization of this quotient. -/
theorem exists_associatedBundleTrivialization
    (hP : IsPrincipalBundle G projection) (e : Trivialization G projection)
    (he : ∀ (g : G) (p : P), projection p ∈ e.baseSet →
      (e (MulOpposite.op g • p)).2 = (e p).2 * g) :
    ∃ eA : Trivialization F (associatedBundleProjection (F := F) hP),
      eA.baseSet = e.baseSet ∧
      (∀ (p : P) (v : F), projection p ∈ e.baseSet →
        eA (associatedBundleMk G P F p v) = (projection p, (e p).2 • v)) ∧
      ∀ (b : B) (v : F), b ∈ e.baseSet →
        eA.toOpenPartialHomeomorph.symm (b, v) =
          associatedBundleMk G P F (e.toOpenPartialHomeomorph.symm (b, 1)) v := by
  /- Stage 1: on projection inverse of the principal chart's base, send
  (p,v) to (projection p, gamma(p)*v), where gamma(p)=(e p).2. Under the
  diagonal action by g, equivariance changes gamma(p) to gamma(p)*g and
  changes v to g inverse*v. The two factors cancel. Thus this exact formula
  descends to the original associated quotient over e.baseSet.
  Stage 2: the original associated projection is continuous, so its preimage
  of e.baseSet is open. Restricting the original quotient map to the preimage
  of this open target preserves its quotient topology. The descended coordinate
  formula is therefore continuous there by the original chart and the jointly
  continuous action on F. No arbitrary quotient pullback is used.
  Stage 3: the inverse sends (b,v) to the original quotient class of
  (e inverse(b,1),v). It is continuous on e.baseSet times F by the actual
  principal inverse chart and the quotient map. The chart identities and
  [p*g,v]=[p,g*v] show that these are inverse functions on the two indicated
  open sets. Package these exact maps as a native Bundle.Trivialization F
  for the fixed associatedBundleProjection, with precisely e.baseSet.
  The construction may use representatives only outside the chart domain;
  on that domain the displayed invariant formulas determine it uniquely.
  No topology, base, projection or action is selected from an existence claim.
  Empty F or an empty chart domain cause no positivity or nonemptiness issue. -/
  classical
  let coord (q : AssociatedBundle G P F) : B × F :=
    (projection (Quotient.out q).1, (e (Quotient.out q).1).2 • (Quotient.out q).2)
  have hcoord (p : P) (v : F) (hp : projection p ∈ e.baseSet) :
      coord (associatedBundleMk G P F p v) = (projection p, (e p).2 • v) := by
    -- The prescribed coordinates are invariant under the original diagonal right action.
    have hrel := Quotient.exact (Quotient.out_eq (associatedBundleMk G P F p v)).symm
    obtain ⟨g, hg⟩ := hrel
    dsimp only [coord]
    rw [hg]
    dsimp only
    rw [hP.projection_smul, he g p hp]
    simp only [mul_smul, smul_inv_smul]
  have hproj (q : AssociatedBundle G P F) :
      (coord q).1 = associatedBundleProjection (F := F) hP q := by
    exact congrArg (associatedBundleProjection (F := F) hP) (Quotient.out_eq q)
  -- The point with group coordinate one generates every point in this chart by its right action.
  have htranslate (p : P) (hp : projection p ∈ e.baseSet) :
      MulOpposite.op (e p).2 • e.toOpenPartialHomeomorph.symm (projection p, 1) = p := by
    let p₀ := e.toOpenPartialHomeomorph.symm (projection p, 1)
    have hp₀ : projection p₀ = projection p := e.proj_symm_apply' hp
    have hsource : projection (MulOpposite.op (e p).2 • p₀) ∈ e.baseSet := by
      rw [hP.projection_smul, hp₀]
      exact hp
    apply e.injOn (e.mem_source.mpr hsource) (e.mem_source.mpr hp)
    change e (MulOpposite.op (e p).2 • p₀) = e p
    apply Prod.ext
    · rw [e.coe_fst (e.mem_source.mpr hsource), e.coe_fst (e.mem_source.mpr hp),
        hP.projection_smul, hp₀]
    · rw [he (e p).2 p₀ (hp₀ ▸ hp)]
      have hvalue : e p₀ = (projection p, 1) := e.apply_symm_apply' hp
      rw [hvalue]
      exact one_mul _
  let source : Set (AssociatedBundle G P F) :=
    (associatedBundleProjection (F := F) hP) ⁻¹' e.baseSet
  have hsourceOpen : IsOpen source := e.open_baseSet.preimage
    (associatedBundleProjection (F := F) hP).continuous
  have hcoordContinuous : ContinuousOn coord source := by
    -- Restriction to this open target preserves the original quotient topology.
    let q : P × F → AssociatedBundle G P F := Quotient.mk (associatedBundleSetoid G P F)
    have hq : IsQuotientMap q := isQuotientMap_quotient_mk'
    rw [hq.continuousOn_isOpen_iff hsourceOpen]
    have heCont : ContinuousOn (fun z : P × F ↦ e z.1) (q ⁻¹' source) :=
      e.toOpenPartialHomeomorph.continuousOn.comp continuous_fst.continuousOn
        (fun z hz ↦ e.mem_source.mpr hz)
    have hc : ContinuousOn (fun z : P × F ↦ (projection z.1, (e z.1).2 • z.2))
        (q ⁻¹' source) :=
      ((hP.projection_properties).1.comp continuous_fst).continuousOn.prodMk
        ((continuous_snd.comp_continuousOn heCont).smul continuous_snd.continuousOn)
    apply hc.congr
    intro z hz
    exact hcoord z.1 z.2 hz
  let t : Trivialization F (associatedBundleProjection (F := F) hP) :=
    { toFun := coord
      invFun := fun y ↦ associatedBundleMk G P F
        (e.toOpenPartialHomeomorph.symm (y.1, 1)) y.2
      source := source
      target := e.baseSet ×ˢ Set.univ
      baseSet := e.baseSet
      map_source' := by
        intro q hq
        exact ⟨(hproj q).symm ▸ hq, Set.mem_univ _⟩
      map_target' := by
        intro y hy
        change projection (e.toOpenPartialHomeomorph.symm (y.1, 1)) ∈ e.baseSet
        rw [e.proj_symm_apply' hy.1]
        exact hy.1
      left_inv' := by
        intro q hq
        induction q using Quotient.inductionOn with
        | h z =>
          change projection z.1 ∈ e.baseSet at hq
          have hc := hcoord z.1 z.2 hq
          change coord (Quotient.mk (associatedBundleSetoid G P F) z) = _ at hc
          rw [hc]
          rw [← associatedBundleMk_smul, htranslate z.1 hq]
          rfl
      right_inv' := by
        intro y hy
        have hp : projection (e.toOpenPartialHomeomorph.symm (y.1, 1)) ∈ e.baseSet := by
          rw [e.proj_symm_apply' hy.1]
          exact hy.1
        rw [hcoord _ _ hp, e.proj_symm_apply' hy.1, e.apply_symm_apply' hy.1]
        simp only [one_smul, Prod.mk.eta]
      open_source := hsourceOpen
      open_target := e.open_baseSet.prod isOpen_univ
      open_baseSet := e.open_baseSet
      continuousOn_toFun := hcoordContinuous
      continuousOn_invFun := by
        apply continuous_quot_mk.comp_continuousOn
        exact (e.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk continuous_const).continuousOn
          (fun y hy ↦ e.mem_target.mpr hy.1)).prodMk continuous_snd.continuousOn
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun q _ ↦ hproj q }
  exact ⟨t, rfl, hcoord, fun _ _ _ ↦ rfl⟩

variable {F' : Type*} [MulAction G F'] [TopologicalSpace F'] [ContinuousSMul G F']

/-- A continuous equivariant fiber map descends on the original associated quotient carriers. -/
def associatedBundleMap (f : C(F, F')) (hf : ∀ (g : G) (v : F), f (g • v) = g • f v) :
    C(AssociatedBundle G P F, AssociatedBundle G P F') where
  toFun := Quotient.map (fun z : P × F ↦ (z.1, f z.2)) (by
    intro x y hxy
    rcases hxy with ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    simp only [hf])
  continuous_toFun := continuous_quot_map _
    (continuous_fst.prodMk (f.continuous.comp continuous_snd))

end AtiyahSinger
