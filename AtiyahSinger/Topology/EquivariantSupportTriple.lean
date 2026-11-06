/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantVectorBundle
public import AtiyahSinger.Topology.SupportBundleTriple

/-!
# Equivariant boundary data with invariant compact control

Public module ID: M1817.

An equivariant structure augments an original compact-support triple: its chosen
compact control is invariant and its original exterior isomorphism intertwines
the specified actions on the original source and target bundles. Bundled data
is attached to an existing SupportBundleTriple; no second triple carrier or
replacement boundary map is introduced. Enlargement, inverse and direct sum use
exactly the previous nonequivariant operations.

Boundary homotopies use the original IsoHomotopy, one invariant compact control
for all times, and intertwining at every time. Both bundles and both actions
remain fixed. This is a more specific notion than arbitrary equivariant bundle
homotopies on the cylinder; no stable equivalence or equivariant K quotient is
defined here. The parameter is fixed by the group throughout.

Sources: SG I.9.23 and I.9.26; Atiyah--Singer I, Section 2, printed pp.489 and
494--495, for compact support and its equivariant extension. The detailed
fixed-bundle certificates are project supplements to those standard definitions.
An invariant control is supplied explicitly for a general topological group.
Only the separate compact-saturation result assumes compactness of the group.
No Hausdorffness, local compactness or closedness of the control is inferred.
The proofs below preserve the original controls, actions and full cylinder maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Pointwise unitInterval


set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E F : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- Equivariance of the specified compact control and the original exterior isomorphism. -/
structure CompactSupportTriple.IsEquivariant (a : CompactSupportTriple E F)
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F) : Prop where
  /-- The same chosen control, and hence its complement, is invariant under every group element. -/
  invariant_control : ∀ (g : G) (x : X), g • x ∈ a.control ↔ x ∈ a.control
  /-- The original boundary map intertwines the two original moving-fiber actions. -/
  boundary_intertwines : ∀ (g : G) (x : (a.controlᶜ : Set X)) (v : E x),
    a.boundary.linearEquiv
        ⟨g • x.val, fun hx ↦ x.property ((invariant_control g x.val).mp hx)⟩
        (ρE.linearMap g x.val v) =
      ρF.linearMap g x.val (a.boundary.linearEquiv x v)

/-- Compact-group saturation gives an actual invariant compact enlargement of a compact set. -/
theorem compact_saturation_properties [CompactSpace G] (K : Set X) (hK : IsCompact K) :
    IsCompact ((Set.univ : Set G) • K) ∧ K ⊆ (Set.univ : Set G) • K ∧
      ∀ (g : G) (x : X),
        g • x ∈ (Set.univ : Set G) • K ↔ x ∈ (Set.univ : Set G) • K := by
  /- Stage 1: this exact pointwise saturation is the image of G times K under
  the original continuous action. Compactness of both factors gives compactness
  of the image; no separation assumption or closed-image claim is needed.
  Stage 2: the identity element puts every point of K in that same saturation.
  Multiplying the acting group element by g proves forward invariance, and
  multiplying by g inverse gives its converse. This produces an invariant
  compact enlargement, not a claim that arbitrary orbit saturations are compact. -/
  refine ⟨isCompact_univ.smul_set hK, ?_, ?_⟩
  · intro x hx
    exact Set.mem_smul.mpr ⟨1, Set.mem_univ _, x, hx, one_smul G x⟩
  · intro g x
    constructor
    · rintro ⟨k, _, y, hy, hky⟩
      refine ⟨g⁻¹ * k, Set.mem_univ _, y, hy, ?_⟩
      change (g⁻¹ * k) • y = x
      change k • y = g • x at hky
      rw [mul_smul, hky, inv_smul_smul]
    · rintro ⟨k, _, y, hy, rfl⟩
      exact ⟨g * k, Set.mem_univ _, y, hy, mul_smul g k y⟩

/-- Restriction to a larger invariant compact control preserves the original equivariance. -/
theorem CompactSupportTriple.IsEquivariant.enlarge {a : CompactSupportTriple E F}
    {ρE : EquivariantStructure G E} {ρF : EquivariantStructure G F}
    (ha : a.IsEquivariant ρE ρF) (K : Set X) (hK : IsCompact K) (h : a.control ⊆ K)
    (hInv : ∀ (g : G) (x : X), g • x ∈ K ↔ x ∈ K) :
    (a.enlarge K hK h).IsEquivariant ρE ρF := by
  /- Keep the supplied invariant control K. Outside K, both x and g*x are
  outside the original control. The enlargement uses the original boundary
  values on this smaller domain, so its intertwining square is precisely
  the old square at the same points and vectors. -/
  refine ⟨hInv, ?_⟩
  intro g x v
  let gx : (Kᶜ : Set X) :=
    ⟨g • x.val, fun hx ↦ x.property ((hInv g x.val).mp hx)⟩
  exact (a.enlarge_apply K hK h gx (ρE.linearMap g x.val v)).trans
    ((ha.boundary_intertwines g ⟨x.val, fun hx ↦ x.property (h hx)⟩ v).trans
      (congrArg (ρF.linearMap g x.val) (a.enlarge_apply K hK h x v)).symm)

/-- Inverting the original boundary isomorphism exchanges the same two equivariant bundles. -/
theorem CompactSupportTriple.IsEquivariant.inverse {a : CompactSupportTriple E F}
    {ρE : EquivariantStructure G E} {ρF : EquivariantStructure G F}
    (ha : a.IsEquivariant ρE ρF) : a.inverse.IsEquivariant ρF ρE := by
  /- Retain the original invariant compact control. Apply the original
  intertwining square to the inverse image of a target vector, then apply
  the inverse boundary isomorphism at g*x. Its two inverse identities give
  the desired square for the actual inverse boundary map. -/
  refine ⟨ha.invariant_control, ?_⟩
  intro g x v
  change (a.controlᶜ : Set X) at x
  let gx : (a.controlᶜ : Set X) :=
    ⟨g • x.val, fun hx ↦ x.property ((ha.invariant_control g x.val).mp hx)⟩
  change (a.boundary.linearEquiv gx).symm (ρF.linearMap g x.val v) =
    ρE.linearMap g x.val ((a.boundary.linearEquiv x).symm v)
  apply (a.boundary.linearEquiv gx).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := ha.boundary_intertwines g x ((a.boundary.linearEquiv x).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

variable {E' F' : X → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
  [TopologicalSpace (TotalSpace Unit E')]
  [∀ x, AddCommGroup (F' x)] [∀ x, Module ℂ (F' x)]
  [TopologicalSpace (TotalSpace Unit F')]

attribute [local instance] sumTopology

/-- The actual direct sum is equivariant outside the union of the two invariant compact controls. -/
theorem CompactSupportTriple.IsEquivariant.sum {a : CompactSupportTriple E F}
    {b : CompactSupportTriple E' F'}
    {ρE : EquivariantStructure G E} {ρF : EquivariantStructure G F}
    {ρE' : EquivariantStructure G E'} {ρF' : EquivariantStructure G F'}
    (ha : a.IsEquivariant ρE ρF) (hb : b.IsEquivariant ρE' ρF') :
    (a.sum b).IsEquivariant (ρE.sum ρE') (ρF.sum ρF') := by
  /- The union of the two original controls is compact and invariant.
  Restrict both original boundary maps to its complement. The existing
  RelativeTriple.sum formula and the componentwise action on the original
  sum fibers turn the desired square into the two supplied squares, both
  evaluated at the same x and g*x. The induced sum topology is unchanged. -/
  have hInv (g : G) (x : X) : g • x ∈ a.control ∪ b.control ↔
      x ∈ a.control ∪ b.control :=
    or_congr (ha.invariant_control g x) (hb.invariant_control g x)
  let hK := a.isCompact_control.union b.isCompact_control
  have hA := ha.enlarge (a.control ∪ b.control) hK Set.subset_union_left hInv
  have hB := hb.enlarge (a.control ∪ b.control) hK Set.subset_union_right hInv
  refine ⟨hInv, ?_⟩
  intro g x v
  let A := (a.enlarge (a.control ∪ b.control) hK Set.subset_union_left).boundary
  let B := (b.enlarge (a.control ∪ b.control) hK Set.subset_union_right).boundary
  let gx : ((a.control ∪ b.control)ᶜ : Set X) :=
    ⟨g • x.val, fun hx ↦ x.property ((hInv g x.val).mp hx)⟩
  have hleft := RelativeTriple.sum_apply A B gx
    (ρE.linearMap g x.val v.1, ρE'.linearMap g x.val v.2)
  have hright := RelativeTriple.sum_apply A B x v
  exact hleft.trans ((Prod.ext (hA.boundary_intertwines g x v.1)
    (hB.boundary_intertwines g x v.2)).trans
      (congrArg (fun w : F x × F' x ↦
        (ρF.linearMap g x.val w.1, ρF'.linearMap g x.val w.2)) hright).symm)

variable (G)

/-- Equivariant data on an existing finite-rank support triple, retaining its original carrier. -/
structure SupportBundleTriple.EquivariantStructure (a : SupportBundleTriple X) where
  /-- The specified action on the original source bundle. -/
  sourceAction : ComplexBundle.EquivariantStructure G a.source.Fiber
  /-- The specified action on the original target bundle. -/
  targetAction : ComplexBundle.EquivariantStructure G a.target.Fiber
  /-- Invariance and intertwining for exactly the original compact-support datum. -/
  isEquivariant : a.datum.IsEquivariant sourceAction targetAction

variable {G}

/-- Enlarge the original control without changing either action or the surviving boundary values. -/
def SupportBundleTriple.EquivariantStructure.enlarge {a : SupportBundleTriple X}
    (s : SupportBundleTriple.EquivariantStructure G a)
    (K : Set X) (hK : IsCompact K) (h : a.datum.control ⊆ K)
    (hInv : ∀ (g : G) (x : X), g • x ∈ K ↔ x ∈ K) :
    SupportBundleTriple.EquivariantStructure G (a.enlarge K hK h) where
  sourceAction := s.sourceAction
  targetAction := s.targetAction
  isEquivariant := s.isEquivariant.enlarge K hK h hInv

/-- The inverse uses the original inverse triple and swaps its two original actions. -/
def SupportBundleTriple.EquivariantStructure.inverse {a : SupportBundleTriple X}
    (s : SupportBundleTriple.EquivariantStructure G a) :
    SupportBundleTriple.EquivariantStructure G a.inverse where
  sourceAction := s.targetAction
  targetAction := s.sourceAction
  isEquivariant := s.isEquivariant.inverse

/-- Direct sum equips the original sum triple with the componentwise original actions. -/
def SupportBundleTriple.EquivariantStructure.sum {a b : SupportBundleTriple X}
    (s : SupportBundleTriple.EquivariantStructure G a)
    (t : SupportBundleTriple.EquivariantStructure G b) :
    SupportBundleTriple.EquivariantStructure G (a.sum b) where
  sourceAction := s.sourceAction.sum t.sourceAction
  targetAction := s.targetAction.sum t.targetAction
  isEquivariant := s.isEquivariant.sum t.isEquivariant

/-- A fixed-bundle equivariant boundary homotopy with one invariant compact control. -/
structure CompactSupportTriple.EquivariantHomotopy
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (a b : CompactSupportTriple E F) where
  /-- One original-space control set for the entire homotopy. -/
  control : Set X
  /-- The uniform control is compact. -/
  isCompact_control : IsCompact control
  /-- The same uniform control, and hence its complement, is invariant. -/
  invariant_control : ∀ (g : G) (x : X), g • x ∈ control ↔ x ∈ control
  /-- The initial boundary map is defined outside this control. -/
  left_control : a.control ⊆ control
  /-- The terminal boundary map is defined outside the same control. -/
  right_control : b.control ⊆ control
  /-- The original cylinder isomorphism, with joint inverse continuity and exact endpoints. -/
  homotopy : IsoHomotopy (a.enlarge control isCompact_control left_control).boundary
    (b.enlarge control isCompact_control right_control).boundary
  /-- Every time slice intertwines the fixed actions; the group leaves the time coordinate fixed. -/
  intertwines : ∀ (t : I) (g : G) (x : (controlᶜ : Set X)) (v : E x),
    homotopy.iso.linearEquiv
        (t, ⟨g • x.val, fun hx ↦ x.property ((invariant_control g x.val).mp hx)⟩)
        (ρE.linearMap g x.val v) =
      ρF.linearMap g x.val (homotopy.iso.linearEquiv (t, x) v)

/-- Existence of an actual uniformly controlled homotopy with both equivariant bundles fixed. -/
def CompactSupportTriple.EquivariantlyHomotopic (a b : CompactSupportTriple E F)
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F) : Prop :=
  Nonempty (CompactSupportTriple.EquivariantHomotopy ρE ρF a b)

/-- Fixed-action homotopy is an equivalence on equivariant triples and forgets correctly. -/
theorem CompactSupportTriple.equivariantlyHomotopic_properties
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F) :
    Equivalence (fun a b : {a : CompactSupportTriple E F // a.IsEquivariant ρE ρF} ↦
      a.val.EquivariantlyHomotopic b.val ρE ρF) ∧
    ∀ (a b : CompactSupportTriple E F), a.EquivariantlyHomotopic b ρE ρF → a.Homotopic b := by
  /- Stage 1: for reflexivity retain the given equivariant triple's original
  invariant compact control and use its constant original cylinder isomorphism.
  The subtype premise supplies the required intertwining at every time.
  Stage 2: reverse an actual cylinder by (t,x) -> (1-t,x), preserving its
  original uniform invariant control. Because the group fixes t, the original
  intertwining equation persists. Construct this reflected map explicitly,
  rather than choosing an unspecified nonequivariant reverse homotopy.
  Stage 3: for transitivity take the union of the two original uniform controls,
  which is compact and invariant. Restrict both original cylinders there.
  The explicit path J(t) composed with b inverse composed with H(t) has the
  required endpoints: the same middle boundary map b cancels at each end.
  Composition preserves joint continuity of both directions and intertwining
  at every time. This is a direct fixed-bundle supplement to the usual
  concatenation argument and requires no change of bundles or actions.
  Stage 4: forget only invariance and intertwining. The same control, endpoint
  inclusions and original IsoHomotopy witness give the existing Homotopic relation.
  This proves no stable equivalence law for changing bundles or actions and
  introduces no equivariant K-theory quotient. -/
  classical
  -- Restriction preserves the entire original cylinder, not only its endpoints.
  have hrestrict {S T : Set X} (hTS : T ⊆ S)
      {e₀ e₁ : RelativeTriple E F S} (H : IsoHomotopy e₀ e₁) :
      ∃ J : IsoHomotopy (e₀.restrictTo hTS) (e₁.restrictTo hTS),
        ∀ (t : I) (x : T) (v : E x), J.iso.linearEquiv (t, x) v =
          H.iso.linearEquiv (t, Set.inclusion hTS x) v := by
    obtain ⟨K, hK⟩ := H.exists_pullback ⟨Set.inclusion hTS, continuous_inclusion hTS⟩
    let U := restrictSubsetIso (E := E) S T hTS
    let V := restrictSubsetIso (E := F) S T hTS
    let L := (U.symm.pullback ⟨Prod.snd, continuous_snd⟩).trans
      (K.iso.trans (V.pullback ⟨Prod.snd, continuous_snd⟩))
    have hU (x : T) (v : E x) : (U.linearEquiv x).symm v = v := by
      exact (restrictSubsetIso_apply (E := E) S T hTS x _).symm.trans
        ((U.linearEquiv x).apply_symm_apply v)
    have hL (t : I) (x : T) (v : E x) :
        L.linearEquiv (t, x) v = H.iso.linearEquiv (t, Set.inclusion hTS x) v := by
      change V.linearEquiv x (K.iso.linearEquiv (t, x) ((U.linearEquiv x).symm v)) = _
      rw [hU]
      exact (restrictSubsetIso_apply (E := F) S T hTS x _).trans (hK t x v)
    refine ⟨{ iso := L, map_zero := ?_, map_one := ?_ }, hL⟩
    · intro x v
      exact (hL 0 x v).trans ((H.map_zero (Set.inclusion hTS x) v).trans
        (Iso.restrictTo_apply e₀ hTS x v).symm)
    · intro x v
      exact (hL 1 x v).trans ((H.map_one (Set.inclusion hTS x) v).trans
        (Iso.restrictTo_apply e₁ hTS x v).symm)
  have henlarge {a b : CompactSupportTriple E F}
      (H : CompactSupportTriple.EquivariantHomotopy ρE ρF a b)
      (L : Set X) (hL : IsCompact L) (hHL : H.control ⊆ L)
      (hInv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L) :
      ∃ J : CompactSupportTriple.EquivariantHomotopy ρE ρF a b,
        J.control = L := by
    obtain ⟨K, hK⟩ := hrestrict (Set.compl_subset_compl.mpr hHL) H.homotopy
    -- Retain this same restricted cylinder, with the endpoints computed in the original triples.
    let Q : IsoHomotopy
        (a.enlarge L hL (H.left_control.trans hHL)).boundary
        (b.enlarge L hL (H.right_control.trans hHL)).boundary :=
      { iso := K.iso
        map_zero := by
          intro x v
          exact (hK 0 x v).trans ((H.homotopy.map_zero
            (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v).trans
            ((a.enlarge_apply H.control H.isCompact_control H.left_control
                (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v).trans
              (a.enlarge_apply L hL (H.left_control.trans hHL) x v).symm))
        map_one := by
          intro x v
          exact (hK 1 x v).trans ((H.homotopy.map_one
            (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v).trans
            ((b.enlarge_apply H.control H.isCompact_control H.right_control
                (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v).trans
              (b.enlarge_apply L hL (H.right_control.trans hHL) x v).symm)) }
    refine ⟨{ control := L
              isCompact_control := hL
              invariant_control := hInv
              left_control := H.left_control.trans hHL
              right_control := H.right_control.trans hHL
              homotopy := Q
              intertwines := ?_ }, rfl⟩
    intro t g x v
    change K.iso.linearEquiv
      (t, ⟨g • x.val, fun hx ↦ x.property ((hInv g x.val).mp hx)⟩)
      (ρE.linearMap g x.val v) = ρF.linearMap g x.val (K.iso.linearEquiv (t, x) v)
    rw [hK, hK]
    exact H.intertwines t g (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro a
      refine ⟨{ control := a.val.control
                isCompact_control := a.val.isCompact_control
                invariant_control := a.property.invariant_control
                left_control := Set.Subset.refl _
                right_control := Set.Subset.refl _
                homotopy := IsoHomotopy.refl _
                intertwines := ?_ }⟩
      intro t g x v
      exact (a.property.enlarge a.val.control a.val.isCompact_control
        (Set.Subset.refl _) a.property.invariant_control).boundary_intertwines g x v
    · rintro a b ⟨H⟩
      -- Reflect time in the given cylinder; the base and every original fiber vector remain fixed.
      let Z := (H.controlᶜ : Set X)
      let πE : I × Z → Z := Prod.snd
      have hrevE : Continuous (fun z : TotalSpace Unit (πE *ᵖ (Restrict E H.controlᶜ)) ↦
          (⟨(unitInterval.symm z.proj.1, z.proj.2), z.snd⟩ :
            TotalSpace Unit (πE *ᵖ (Restrict E H.controlᶜ)))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict E H.controlᶜ) πE).continuous_iff]
        exact ((unitInterval.continuous_symm.comp
          (Pullback.continuous_proj Unit (Restrict E H.controlᶜ) πE).fst).prodMk
          (Pullback.continuous_proj Unit (Restrict E H.controlᶜ) πE).snd).prodMk
          (Pullback.continuous_lift Unit (Restrict E H.controlᶜ) πE)
      have hrevF : Continuous (fun z : TotalSpace Unit (πE *ᵖ (Restrict F H.controlᶜ)) ↦
          (⟨(unitInterval.symm z.proj.1, z.proj.2), z.snd⟩ :
            TotalSpace Unit (πE *ᵖ (Restrict F H.controlᶜ)))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict F H.controlᶜ) πE).continuous_iff]
        exact ((unitInterval.continuous_symm.comp
          (Pullback.continuous_proj Unit (Restrict F H.controlᶜ) πE).fst).prodMk
          (Pullback.continuous_proj Unit (Restrict F H.controlᶜ) πE).snd).prodMk
          (Pullback.continuous_lift Unit (Restrict F H.controlᶜ) πE)
      have hforward := (Pullback.continuous_lift Unit (Restrict F H.controlᶜ) πE).comp
        (H.homotopy.iso.continuous_total.comp hrevE)
      have hbackward := (Pullback.continuous_lift Unit (Restrict E H.controlᶜ) πE).comp
        (H.homotopy.iso.continuous_symm.comp hrevF)
      let L : Iso (πE *ᵖ (Restrict E H.controlᶜ)) (πE *ᵖ (Restrict F H.controlᶜ)) :=
        { linearEquiv := fun z ↦ H.homotopy.iso.linearEquiv (unitInterval.symm z.1, z.2)
          continuous_total := by
            rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict F H.controlᶜ)
              πE).continuous_iff]
            exact (Pullback.continuous_proj Unit (Restrict E H.controlᶜ) πE).prodMk
              hforward
          continuous_symm := by
            rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict E H.controlᶜ)
              πE).continuous_iff]
            exact (Pullback.continuous_proj Unit (Restrict F H.controlᶜ) πE).prodMk
              hbackward }
      refine ⟨{ control := H.control
                isCompact_control := H.isCompact_control
                invariant_control := H.invariant_control
                left_control := H.right_control
                right_control := H.left_control
                homotopy := { iso := L, map_zero := ?_, map_one := ?_ }
                intertwines := fun t g x v ↦ H.intertwines (unitInterval.symm t) g x v }⟩
      · intro x v
        change H.homotopy.iso.linearEquiv (unitInterval.symm 0, x) v = _
        rw [unitInterval.symm_zero]
        exact H.homotopy.map_one x v
      · intro x v
        change H.homotopy.iso.linearEquiv (unitInterval.symm 1, x) v = _
        rw [unitInterval.symm_one]
        exact H.homotopy.map_zero x v
    · rintro a b c ⟨H⟩ ⟨J⟩
      let S := H.control ∪ J.control
      have hS : IsCompact S := H.isCompact_control.union J.isCompact_control
      have hInv (g : G) (x : X) : g • x ∈ S ↔ x ∈ S :=
        or_congr (H.invariant_control g x) (J.invariant_control g x)
      obtain ⟨H', hH'⟩ := henlarge H S hS Set.subset_union_left hInv
      obtain ⟨J', hJ'⟩ := henlarge J S hS Set.subset_union_right hInv
      -- Work on precisely one control; equality transport changes only its proof certificates.
      rcases H' with ⟨K, hK, hKI, haK, hbK, H₀, hH₀⟩
      rcases J' with ⟨L, hL, hLI, hbL, hcL, J₀, hJ₀⟩
      dsimp only at hH' hJ'
      subst K
      subst L
      let mid := (b.val.enlarge S hS hbK).boundary
      have hmid := (b.property.enlarge S hS hbK hInv).inverse
      let C := mid.symm.pullback (⟨Prod.snd, continuous_snd⟩ : C(I × (Sᶜ : Set X), (Sᶜ : Set X)))
      let Q := H₀.iso.trans (C.trans J₀.iso)
      -- The explicit path is J(t) composed with b inverse composed with H(t).
      -- Its original middle map cancels at both endpoints and intertwines at every time.
      refine ⟨{ control := S
                isCompact_control := hS
                invariant_control := hInv
                left_control := haK
                right_control := hcL
                homotopy := { iso := Q, map_zero := ?_, map_one := ?_ }
                intertwines := ?_ }⟩
      · intro x v
        change J₀.iso.linearEquiv (0, x)
          ((mid.linearEquiv x).symm (H₀.iso.linearEquiv (0, x) v)) = _
        rw [J₀.map_zero, H₀.map_zero]
        exact (mid.linearEquiv x).apply_symm_apply _
      · intro x v
        change J₀.iso.linearEquiv (1, x)
          ((mid.linearEquiv x).symm (H₀.iso.linearEquiv (1, x) v)) = _
        rw [H₀.map_one, LinearEquiv.symm_apply_apply]
        exact J₀.map_one x v
      · intro t g x v
        let gx : (Sᶜ : Set X) :=
          ⟨g • x.val, fun hx ↦ x.property ((hInv g x.val).mp hx)⟩
        change J₀.iso.linearEquiv (t, gx)
          ((mid.linearEquiv gx).symm (H₀.iso.linearEquiv (t, gx)
            (ρE.linearMap g x.val v))) =
          ρF.linearMap g x.val (J₀.iso.linearEquiv (t, x)
            ((mid.linearEquiv x).symm (H₀.iso.linearEquiv (t, x) v)))
        rw [hH₀ t g x v]
        have hi := hmid.boundary_intertwines g x (H₀.iso.linearEquiv (t, x) v)
        change (mid.linearEquiv gx).symm
          (ρF.linearMap g x.val (H₀.iso.linearEquiv (t, x) v)) =
          ρE.linearMap g x.val ((mid.linearEquiv x).symm
            (H₀.iso.linearEquiv (t, x) v)) at hi
        rw [hi]
        exact hJ₀ t g x _
  · rintro a b ⟨H⟩
    exact ⟨H.control, H.isCompact_control, H.left_control, H.right_control, ⟨H.homotopy⟩⟩

end AtiyahSinger.ComplexBundle
