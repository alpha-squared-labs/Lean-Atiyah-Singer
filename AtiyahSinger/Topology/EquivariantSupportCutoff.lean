/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantSupportIsomorphism
public import AtiyahSinger.Topology.SupportTripleCutoff
public import AtiyahSinger.Topology.SupportTripleHomotopy
public import Mathlib.Topology.Order.Compact

/-!
# Invariant spatial cutoffs and equivariant isomorphisms at infinity

Public module ID: M1810.

A compact group action on a locally compact Hausdorff space admits an invariant
interval-valued cutoff, zero near any specified compact set and one outside a
larger invariant compact set. Taking the minimum of an ordinary cutoff along
each orbit gives the construction without Haar measure or measurable structure.
The group itself needs no additional Hausdorff assumption.

An invariant cutoff turns an original uniformly controlled equivariant boundary
homotopy into an actual global equivariant isomorphism square at infinity. The
same construction applied to Karoubi's elementary shear path identifies a triple
plus its actual inverse with the identity on its original source-plus-target
bundle. All actions, boundary maps and bundle topologies are retained.

Sources: SG I.9.23--9.26, ASI I Section 2 for the equivariant compact-support
framework, and KA II.2.14, printed pp.61--62, for the elementary matrix inverse
path. The invariant spatial cutoff and its use to produce global equivariant
squares are project supplements spelling out the locally compact construction.
They are not exact lifting assertions from arbitrary noncompact closed subsets.
The three original assertions are proved below with their specified actions and cutoffs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Pointwise unitInterval

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- A compact set has an invariant time cutoff between invariant open and compact neighborhoods. -/
theorem exists_invariant_time_cutoff [CompactSpace G] [LocallyCompactSpace X] [T2Space X]
    (K : Set X) (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      (∀ (g : G) (x : X), g • x ∈ U ↔ x ∈ U) ∧
      ∃ L : Set X, IsCompact L ∧ U ⊆ L ∧
        (∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L) ∧
        ∃ ρ : C(X, I), (∀ (g : G) (x : X), ρ (g • x) = ρ x) ∧
          (∀ x ∈ U, ρ x = 0) ∧ ∀ x ∉ L, ρ x = 1 := by
  /- Stage 1: apply exists_time_cutoff to the specified compact K. It gives
  an ordinary cutoff rho0, zero on an open U0 containing K and one outside a
  compact L0 containing U0. This uses local compactness and Hausdorffness of X,
  with no paracompactness or global normality assumption.
  Stage 2: take U = G*U0 and L = G*L0 under the original action. Each fixed
  group element acts by a homeomorphism, so U is open. The set L is the
  continuous image of compact G times compact L0, hence compact. Group laws
  make both sets invariant, and the identity gives K contained in U contained
  in L. The original K need not itself have been invariant.
  Stage 3: define rho(x) as the minimum of rho0(g*x) over g in G. The group is
  nonempty because it contains its identity. For each x, the continuous image
  of compact G in I is compact and nonempty, so this minimum is attained.
  Joint continuity and a finite cover of compact G give local uniform control
  of the change in rho0(g*x) as x varies. Taking minima preserves that bound,
  so rho is continuous without first countability or Hausdorffness of G.
  Right translation g -> g*k reindexes exactly the same orbit values, giving
  invariance of rho. If x lies in U, some inverse group element takes it into
  U0, so the minimum is zero. If x is outside L, every g*x is outside L0,
  so all orbit values, and their minimum, are one. No integration or choice
  of a measurable structure is involved. -/
  classical
  obtain ⟨U₀, hU₀, hKU₀, L₀, hL₀, hU₀L₀, ρ₀, hρ₀zero, hρ₀one⟩ :=
    exists_time_cutoff K hK
  let U := (Set.univ : Set G) • U₀
  let L := (Set.univ : Set G) • L₀
  obtain ⟨hL, _, hLinv⟩ := compact_saturation_properties (G := G) L₀ hL₀
  have hUinv (g : G) (x : X) : g • x ∈ U ↔ x ∈ U := by
    constructor
    · rintro ⟨k, _, y, hy, hky⟩
      refine ⟨g⁻¹ * k, Set.mem_univ _, y, hy, ?_⟩
      change (g⁻¹ * k) • y = x
      change k • y = g • x at hky
      rw [mul_smul, hky, inv_smul_smul]
    · rintro ⟨k, _, y, hy, rfl⟩
      exact ⟨g * k, Set.mem_univ _, y, hy, mul_smul g k y⟩
  -- The orbit minimum is attained and is continuous in the original base topology.
  let f (x : X) (g : G) : ℝ := ρ₀ (g • x)
  have hf : Continuous (Function.uncurry f) :=
    continuous_subtype_val.comp (ρ₀.continuous.comp (continuous_snd.smul continuous_fst))
  let m (x : X) : ℝ := sInf (f x '' Set.univ)
  have hmin (x : X) : ∃ g : G, m x = f x g ∧ ∀ k : G, f x g ≤ f x k := by
    obtain ⟨g, _, hvalue, hleast⟩ := isCompact_univ.exists_sInf_image_eq_and_le
      (Set.univ_nonempty : (Set.univ : Set G).Nonempty)
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
    exact ⟨g, hvalue, fun k ↦ hleast k (Set.mem_univ k)⟩
  have hmrange (x : X) : m x ∈ I := by
    obtain ⟨g, hg, _⟩ := hmin x
    rw [hg]
    exact (ρ₀ (g • x)).property
  let ρ : C(X, I) := ⟨fun x ↦ ⟨m x, hmrange x⟩,
    (isCompact_univ.continuous_sInf hf).subtype_mk hmrange⟩
  have hρinv (g : G) (x : X) : ρ (g • x) = ρ x := by
    apply Subtype.ext
    change sInf (f (g • x) '' Set.univ) = sInf (f x '' Set.univ)
    congr 1
    apply Set.Subset.antisymm
    · rintro y ⟨k, _, rfl⟩
      exact ⟨k * g, Set.mem_univ _, congrArg (fun z ↦ (ρ₀ z : ℝ)) (mul_smul k g x)⟩
    · rintro y ⟨k, _, rfl⟩
      refine ⟨k * g⁻¹, Set.mem_univ _, ?_⟩
      dsimp only [f]
      rw [mul_smul, inv_smul_smul]
  refine ⟨U, hU₀.smul_left, ?_, hUinv, L, hL, ?_, hLinv, ρ, hρinv, ?_, ?_⟩
  · intro x hx
    exact ⟨1, Set.mem_univ _, x, hKU₀ hx, one_smul G x⟩
  · exact Set.smul_subset_smul_left hU₀L₀
  · -- An orbit meeting the inner neighborhood has minimum zero.
    rintro x ⟨g, _, y, hy, rfl⟩
    rw [hρinv]
    apply Subtype.ext
    change m y = 0
    obtain ⟨k, hk, hleast⟩ := hmin y
    apply le_antisymm
    · calc
        m y = f y k := hk
        _ ≤ f y 1 := hleast 1
        _ = 0 := by simp only [f, one_smul, hρ₀zero y hy, Set.Icc.coe_zero]
    · exact (hmrange y).1
  · -- Outside the saturated compact set every orbit value is exactly one.
    intro x hx
    apply Subtype.ext
    change m x = 1
    obtain ⟨g, hg, _⟩ := hmin x
    rw [hg]
    have hgout : g • x ∉ L₀ := by
      intro h
      apply hx
      exact ⟨g⁻¹, Set.mem_univ _, g • x, h, inv_smul_smul g x⟩
    exact congrArg Subtype.val (hρ₀one (g • x) hgout)

set_option backward.isDefEq.respectTransparency.types false in
/-- A fixed-action boundary homotopy gives an actual equivariant global square at infinity. -/
theorem equivariantSupportBundleTriple_isIsomorphic_of_homotopic
    [CompactSpace G] [LocallyCompactSpace X] [T2Space X]
    (E F : FiniteBundle X)
    (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber)
    (a b : CompactSupportTriple E.Fiber F.Fiber)
    (ha : a.IsEquivariant ρE ρF) (hb : b.IsEquivariant ρE ρF)
    (H : a.EquivariantlyHomotopic b ρE ρF) :
    (EquivariantSupportBundleTriple.ofBoundary E F a ρE ρF ha).IsIsomorphic
      (EquivariantSupportBundleTriple.ofBoundary E F b ρE ρF hb) := by
  /- Stage 1: unpack the original equivariant homotopy and its one invariant
  compact control K. On its complement, compose each boundary map H_t with
  the inverse of the initial boundary map. This is an actual automorphism
  homotopy A_t of the original target bundle, with A_0 = identity and
  A_1 = b composed with a inverse. The original pointwise intertwining squares
  show that every A_t commutes with the same moving-fiber target action.
  Stage 2: choose the invariant time cutoff rho with K contained in U contained
  in L. Outside K use A_(rho(x)); on U use the identity. The two formulas agree
  on U minus K because rho is zero there. Since compact K is closed in the
  Hausdorff base, these are two open domains covering X. Glue the forward maps.
  Their fiberwise bijectivity and finite rank give a global isomorphism T.
  Invariance of rho makes T equivariant: the homotopy is evaluated at the
  same time at x and g*x, and both domains are invariant.
  Stage 3: outside the same invariant compact L, rho is one and T equals
  b composed with a inverse. Together with the original source identity this
  gives T composed with a = b, the required global equivariant square. Use
  exactly L as the common control and the original inclusion witnesses from
  the homotopy. No independently chosen nonequivariant extension is used. -/
  classical
  obtain ⟨H⟩ := H
  let K := H.control
  let hK := H.isCompact_control
  let aK := (a.enlarge K hK H.left_control).boundary
  let bK := (b.enlarge K hK H.right_control).boundary
  let J : IsoHomotopy (RelativeTriple.identity F.Fiber Kᶜ) (aK.symm.trans bK) :=
    { iso := (aK.symm.pullback ⟨Prod.snd, continuous_snd⟩).trans H.homotopy.iso
      map_zero := by
        intro x v
        change H.homotopy.iso.linearEquiv (0, x) ((aK.linearEquiv x).symm v) = v
        rw [H.homotopy.map_zero]
        exact (aK.linearEquiv x).apply_symm_apply v
      map_one := by
        intro x v
        exact H.homotopy.map_one x ((aK.linearEquiv x).symm v) }
  have hJ (t : I) (g : G) (x : (Kᶜ : Set X)) (v : F.Fiber x) :
      J.iso.linearEquiv
        (t, ⟨g • x.val, fun hx ↦ x.property ((H.invariant_control g x.val).mp hx)⟩)
        (ρF.linearMap g x.val v) =
      ρF.linearMap g x.val (J.iso.linearEquiv (t, x) v) := by
    have hinverse := (ha.enlarge K hK H.left_control H.invariant_control).inverse
    let gx : (Kᶜ : Set X) :=
      ⟨g • x.val, fun hx ↦ x.property ((H.invariant_control g x.val).mp hx)⟩
    have heq := hinverse.boundary_intertwines g x v
    change (aK.linearEquiv gx).symm (ρF.linearMap g x.val v) =
      ρE.linearMap g x.val ((aK.linearEquiv x).symm v) at heq
    exact (congrArg (H.homotopy.iso.linearEquiv (t, gx)) heq).trans
      (H.intertwines t g x ((aK.linearEquiv x).symm v))
  obtain ⟨U, hU, hKU, _, L, hL, hUL, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
    exists_invariant_time_cutoff (G := G) K hK
  have hKL : K ⊆ L := hKU.trans hUL
  let eFiber (x : X) : F.Fiber x ≃ₗ[ℂ] F.Fiber x :=
    if hx : x ∈ K then LinearEquiv.refl ℂ (F.Fiber x) else
      J.iso.linearEquiv (ρ x, ⟨x, hx⟩)
  have hidentity (x : X) (hx : x ∈ U) (v : F.Fiber x) : eFiber x v = v := by
    dsimp only [eFiber]
    split_ifs with hKx
    · rfl
    · rw [hρzero x hx]
      exact J.map_zero ⟨x, hKx⟩ v
  -- Off K, insert the spatially varying time into the actual cylinder pullback.
  let R : Set (TotalSpace Unit F.Fiber) := {z | z.proj ∉ K}
  let base (z : R) : (Kᶜ : Set X) := ⟨z.val.proj, z.property⟩
  have hbase : Continuous base :=
    ((continuous_proj (E := F.Fiber)).comp continuous_subtype_val).subtype_mk _
  let restricted (z : R) : TotalSpace Unit (Restrict F.Fiber Kᶜ) :=
    ⟨base z, z.val.snd⟩
  have hrestricted : Continuous restricted := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber
      (Subtype.val : (Kᶜ : Set X) → X)).continuous_iff]
    exact hbase.prodMk continuous_subtype_val
  let cylinder (z : R) : TotalSpace Unit
      ((Prod.snd : I × (Kᶜ : Set X) → (Kᶜ : Set X)) *ᵖ (Restrict F.Fiber Kᶜ)) :=
    ⟨(ρ z.val.proj, base z), z.val.snd⟩
  have hcylinder : Continuous cylinder := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict F.Fiber Kᶜ)
      (Prod.snd : I × (Kᶜ : Set X) → (Kᶜ : Set X))).continuous_iff]
    exact ((ρ.continuous.comp ((continuous_proj (E := F.Fiber)).comp
      continuous_subtype_val)).prodMk hbase).prodMk hrestricted
  have hout := (Pullback.continuous_lift Unit F.Fiber
    (Subtype.val : (Kᶜ : Set X) → X)).comp
      ((Pullback.continuous_lift Unit (Restrict F.Fiber Kᶜ)
        (Prod.snd : I × (Kᶜ : Set X) → (Kᶜ : Set X))).comp
          (J.iso.continuous_total.comp hcylinder))
  have hexterior : ContinuousOn (fun z : TotalSpace Unit F.Fiber ↦
      (⟨z.proj, eFiber z.proj z.snd⟩ : TotalSpace Unit F.Fiber)) R := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply hout.congr
    intro z
    change (⟨z.val.proj, J.iso.linearEquiv (ρ z.val.proj, base z) z.val.snd⟩ :
      TotalSpace Unit F.Fiber) = ⟨z.val.proj, eFiber z.val.proj z.val.snd⟩
    dsimp only [eFiber]
    rw [dite_eq_right z.property]
    rfl
  -- On U the exact formula is identity; these two open regions cover the total space.
  have hcontinuous : Continuous (fun z : TotalSpace Unit F.Fiber ↦
      (⟨z.proj, eFiber z.proj z.snd⟩ : TotalSpace Unit F.Fiber)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.proj ∈ U
    · apply continuousAt_id.congr_of_eventuallyEq
      filter_upwards [(hU.preimage (continuous_proj (E := F.Fiber))).mem_nhds hz] with w hw
      exact congrArg (TotalSpace.mk w.proj) (hidentity w.proj hw w.snd)
    · have hzK : z.proj ∉ K := fun h ↦ hz (hKU h)
      exact hexterior.continuousAt
        ((hK.isClosed.isOpen_compl.preimage (continuous_proj (E := F.Fiber))).mem_nhds hzK)
  -- Retain this particular extension: its equivariance uses the same invariant cutoff.
  let e : Hom F.Fiber F.Fiber :=
    { linearMap := fun x ↦ (eFiber x).toLinearMap, continuous_total := hcontinuous }
  let T : Iso F.Fiber F.Fiber := e.toIso (fun x ↦ (eFiber x).bijective)
  have hT : T.IsEquivariant ρF ρF := by
    intro g x v
    change eFiber (g • x) (ρF.linearMap g x v) = ρF.linearMap g x (eFiber x v)
    by_cases hx : x ∈ K
    · have hgx : g • x ∈ K := (H.invariant_control g x).mpr hx
      dsimp only [eFiber]
      rw [dite_eq_left hx, dite_eq_left hgx]
      rfl
    · have hgx : g • x ∉ K := fun h ↦ hx ((H.invariant_control g x).mp h)
      dsimp only [eFiber]
      rw [dite_eq_right hx, dite_eq_right hgx, hρinv]
      exact hJ (ρ x) g ⟨x, hx⟩ v
  have hterminal (x : (Lᶜ : Set X)) (v : F.Fiber x) :
      T.linearEquiv x v =
        (aK.symm.trans bK).linearEquiv ⟨x, fun hx ↦ x.property (hKL hx)⟩ v := by
    have hxK : (x : X) ∉ K := fun hx ↦ x.property (hKL hx)
    change eFiber x v = _
    dsimp only [eFiber]
    rw [dite_eq_right hxK, hρone x x.property]
    exact J.map_one ⟨x, hxK⟩ v
  refine ⟨L, hL, hLinv, H.left_control.trans hKL, H.right_control.trans hKL,
    Iso.refl E.Fiber, T, (fun _ _ _ ↦ rfl), hT, ?_⟩
  intro x v
  let y : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (hKL hx)⟩
  have hleft : (a.enlarge L hL (H.left_control.trans hKL)).boundary.linearEquiv x v =
      aK.linearEquiv y v :=
    (a.enlarge_apply L hL (H.left_control.trans hKL) x v).trans
      (a.enlarge_apply K hK H.left_control y v).symm
  have hright : (b.enlarge L hL (H.right_control.trans hKL)).boundary.linearEquiv x v =
      bK.linearEquiv y v :=
    (b.enlarge_apply L hL (H.right_control.trans hKL) x v).trans
      (b.enlarge_apply K hK H.right_control y v).symm
  -- Outside L the same target map yields the exact square for the original boundaries.
  change T.linearEquiv x
    ((a.enlarge L hL (H.left_control.trans hKL)).boundary.linearEquiv x v) =
      (b.enlarge L hL (H.right_control.trans hKL)).boundary.linearEquiv x v
  rw [hleft, hterminal]
  change bK.linearEquiv y ((aK.linearEquiv y).symm (aK.linearEquiv y v)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact hright.symm

attribute [local instance] sumTopology isFiniteRank_sum

set_option backward.isDefEq.respectTransparency.types false in
/-- A triple and its inverse sum to the identity germ through global equivariant bundle maps. -/
theorem EquivariantSupportBundleTriple.isIsomorphic_sum_inverse
    [CompactSpace G] [LocallyCompactSpace X] [T2Space X]
    (a : EquivariantSupportBundleTriple G X) :
    (a.sum a.inverse).IsIsomorphic
      (EquivariantSupportBundleTriple.identity (a.1.source.sum a.1.target)
        (a.2.sourceAction.sum a.2.targetAction)) := by
  /- Stage 1: retain the original invariant compact control and write alpha
  for the original boundary E -> F on its complement. On E plus F use the
  actual elementary shears U_t = [[Id, -t alpha inverse], [0, Id]] and
  L_t = [[Id, 0], [t alpha, Id]]. Karoubi II.2.14 uses the path U_t L_t U_t.
  It starts at identity and ends at beta = [[0, -alpha inverse], [alpha, 0]].
  Its inverse is U_(-t) L_(-t) U_(-t), so both directions are jointly continuous.
  Every block uses only the original boundary, its actual inverse and scalar
  multiples of identity; the original intertwining equation therefore makes
  every time slice equivariant for the original sum action.
  Stage 2: evaluate this path at an invariant time cutoff. The implementation
  first extends rho times alpha and rho times alpha inverse by zero, then
  forms the same three shears; thus the product is identity near the control. The result
  is a global equivariant automorphism T of E plus F, equal to beta outside
  one larger invariant compact L. No global isomorphism E -> F is assumed.
  Stage 3: the actual signed swap s : F plus E -> E plus F sends (u,v) to
  (-v,u). It is a global equivariant isomorphism for the swapped original
  sum actions, and beta = s composed with diag(alpha, alpha inverse).
  Use T as the source isomorphism and s as the target isomorphism. Outside
  L this is precisely the square from the original sum-with-inverse boundary
  to the identity boundary on E plus F. Zero ranks and locally varying ranks
  cause no change to the block formulas or the original bundle topologies. -/
  classical
  let E := a.1.source.Fiber
  let F := a.1.target.Fiber
  let S := E ×ᵇ F
  let K := a.1.datum.control
  let ρE := a.2.sourceAction
  let ρF := a.2.targetAction
  obtain ⟨V, hV, hKV, _, L, hL, hVL, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
    exists_invariant_time_cutoff (G := G) K a.1.datum.isCompact_control
  have hKL : K ⊆ L := hKV.trans hVL
  let forward : Hom E F := a.1.datum.cutoffHom ρ V hV hKV hρzero
  let backward : Hom F E := a.1.datum.inverse.cutoffHom ρ V hV hKV hρzero
  -- Both zero extensions retain the exact original moving-fiber intertwining equations.
  have hforward (g : G) (x : X) (v : E x) :
      forward.linearMap (g • x) (ρE.linearMap g x v) =
        ρF.linearMap g x (forward.linearMap x v) := by
    change a.1.datum.cutoffLinearMap ρ (g • x) (ρE.linearMap g x v) =
      ρF.linearMap g x (a.1.datum.cutoffLinearMap ρ x v)
    by_cases hx : x ∈ K
    · have hgx : g • x ∈ K := (a.2.isEquivariant.invariant_control g x).mpr hx
      dsimp only [CompactSupportTriple.cutoffLinearMap]
      rw [dite_eq_left hx, dite_eq_left hgx]
      exact (map_zero (ρF.linearMap g x)).symm
    · have hgx : g • x ∉ K :=
        fun h ↦ hx ((a.2.isEquivariant.invariant_control g x).mp h)
      dsimp only [CompactSupportTriple.cutoffLinearMap]
      rw [dite_eq_right hx, dite_eq_right hgx]
      change ((ρ (g • x) : ℝ) : ℂ) • a.1.datum.boundary.linearEquiv
        ⟨g • x, hgx⟩ (ρE.linearMap g x v) =
          ρF.linearMap g x (((ρ x : ℝ) : ℂ) • a.1.datum.boundary.linearEquiv ⟨x, hx⟩ v)
      rw [hρinv]
      exact (congrArg (fun w : F (g • x) ↦ ((ρ x : ℝ) : ℂ) • w)
        (a.2.isEquivariant.boundary_intertwines g ⟨x, hx⟩ v)).trans
          ((ρF.linearMap g x).map_smul _ _).symm
  have hbackward (g : G) (x : X) (v : F x) :
      backward.linearMap (g • x) (ρF.linearMap g x v) =
        ρE.linearMap g x (backward.linearMap x v) := by
    change a.1.datum.inverse.cutoffLinearMap ρ (g • x) (ρF.linearMap g x v) =
      ρE.linearMap g x (a.1.datum.inverse.cutoffLinearMap ρ x v)
    by_cases hx : x ∈ K
    · have hgx : g • x ∈ K := (a.2.isEquivariant.invariant_control g x).mpr hx
      dsimp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse]
      rw [dite_eq_left hx, dite_eq_left hgx]
      exact (map_zero (ρE.linearMap g x)).symm
    · have hgx : g • x ∉ K :=
        fun h ↦ hx ((a.2.isEquivariant.invariant_control g x).mp h)
      dsimp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse]
      rw [dite_eq_right hx, dite_eq_right hgx]
      change ((ρ (g • x) : ℝ) : ℂ) • (a.1.datum.boundary.linearEquiv
        ⟨g • x, hgx⟩).symm (ρF.linearMap g x v) =
          ρE.linearMap g x (((ρ x : ℝ) : ℂ) •
            (a.1.datum.boundary.linearEquiv ⟨x, hx⟩).symm v)
      rw [hρinv]
      exact (congrArg (fun w : E (g • x) ↦ ((ρ x : ℝ) : ℂ) • w)
        (a.2.isEquivariant.inverse.boundary_intertwines g ⟨x, hx⟩ v)).trans
          ((ρE.linearMap g x).map_smul _ _).symm
  -- A square-zero global bundle map gives an invertible shear on the original sum topology.
  let p : C(TotalSpace Unit S, X) := ⟨π Unit S, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit S → X) *ᵖ S) := isFiniteRank_pullback p
  let shearMap (N : Hom S S) (c : ℂ) (x : X) : S x →ₗ[ℂ] S x :=
    LinearMap.id + c • N.linearMap x
  have hcontinuous (N : Hom S S) (c : ℂ) :
      Continuous (fun z : TotalSpace Unit S ↦
        (⟨z.proj, shearMap N c z.proj z.snd⟩ : TotalSpace Unit S)) := by
    have hi : Continuous (fun z : TotalSpace Unit S ↦
        (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit S → X) *ᵖ S))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit S p).continuous_iff]
      exact continuous_id.prodMk continuous_id
    have hN : Continuous (fun z : TotalSpace Unit S ↦
        (⟨z, N.linearMap z.proj z.snd⟩ :
          TotalSpace Unit ((p : TotalSpace Unit S → X) *ᵖ S))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit S p).continuous_iff]
      exact continuous_id.prodMk N.continuous_total
    have hs := continuous_add_section ((p : TotalSpace Unit S → X) *ᵖ S) _ _ hi
      (continuous_smul_section ((p : TotalSpace Unit S → X) *ᵖ S)
        (ContinuousMap.const _ c) _ hN)
    exact (Pullback.continuous_lift Unit S p).comp hs
  let shear (N : Hom S S) (hN : ∀ x v, N.linearMap x (N.linearMap x v) = 0)
      (c : ℂ) : Iso S S :=
    { linearEquiv := fun x ↦
        { toLinearMap := shearMap N c x
          invFun := shearMap N (-c) x
          left_inv := by
            intro v
            change v + c • N.linearMap x v +
              (-c) • N.linearMap x (v + c • N.linearMap x v) = v
            simp [map_add, hN]
            abel
          right_inv := by
            intro v
            change v + (-c) • N.linearMap x v +
              c • N.linearMap x (v + (-c) • N.linearMap x v) = v
            simp [map_add, hN] }
      continuous_total := hcontinuous N c
      continuous_symm := hcontinuous N (-c) }
  let upper : Hom S S := sumInl.comp (backward.comp sumSnd)
  let lower : Hom S S := sumInr.comp (forward.comp sumFst)
  have hu : ∀ x v, upper.linearMap x (upper.linearMap x v) = 0 := by
    intro x v
    change (backward.linearMap x 0, 0) = 0
    simp
  have hl : ∀ x v, lower.linearMap x (lower.linearMap x v) = 0 := by
    intro x v
    change (0, forward.linearMap x 0) = 0
    simp
  let U := shear upper hu (-1)
  let D := shear lower hl 1
  have hU (x : X) (v : S x) : U.linearEquiv x v =
      (v.1 - backward.linearMap x v.2, v.2) := by
    change (v.1 + (-1 : ℂ) • backward.linearMap x v.2,
      v.2 + (-1 : ℂ) • 0) = _
    simp [sub_eq_add_neg]
  have hD (x : X) (v : S x) : D.linearEquiv x v =
      (v.1, v.2 + forward.linearMap x v.1) := by
    change (v.1 + (1 : ℂ) • 0, v.2 + (1 : ℂ) • forward.linearMap x v.1) = _
    simp
  have hUeq : U.IsEquivariant (ρE.sum ρF) (ρE.sum ρF) := by
    intro g x v
    change U.linearEquiv (g • x) ((ρE.sum ρF).linearMap g x v) =
      (ρE.sum ρF).linearMap g x (U.linearEquiv x v)
    rw [hU, hU]
    exact Prod.ext ((congrArg (fun w ↦ ρE.linearMap g x v.1 - w)
      (hbackward g x v.2)).trans (map_sub _ _ _).symm) rfl
  have hDeq : D.IsEquivariant (ρE.sum ρF) (ρE.sum ρF) := by
    intro g x v
    change D.linearEquiv (g • x) ((ρE.sum ρF).linearMap g x v) =
      (ρE.sum ρF).linearMap g x (D.linearEquiv x v)
    rw [hD, hD]
    exact Prod.ext rfl ((congrArg (fun w ↦ ρF.linearMap g x v.2 + w)
      (hforward g x v.1)).trans (map_add _ _ _).symm)
  let T := (U.trans D).trans U
  have hT : T.IsEquivariant (ρE.sum ρF) (ρE.sum ρF) := by
    intro g x v
    exact (congrArg (U.linearEquiv (g • x))
      ((congrArg (D.linearEquiv (g • x)) (hUeq g x v)).trans
        (hDeq g x (U.linearEquiv x v)))).trans
          (hUeq g x (D.linearEquiv x (U.linearEquiv x v)))
  have hterminal (x : (Lᶜ : Set X)) (v : S x) : T.linearEquiv x v =
      (-(a.1.datum.boundary.linearEquiv
          ⟨x, fun hx ↦ x.property (hKL hx)⟩).symm v.2,
        a.1.datum.boundary.linearEquiv ⟨x, fun hx ↦ x.property (hKL hx)⟩ v.1) := by
    let y : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (hKL hx)⟩
    have hboundary := a.1.datum.cutoffHom_boundary ρ V hV hKV hρzero y
      (hρone x x.property)
    change U.linearEquiv x (D.linearEquiv x (U.linearEquiv x v)) = _
    rw [hU, hD, hU]
    change (v.1 - backward.linearMap x v.2 -
      backward.linearMap x (v.2 + forward.linearMap x (v.1 - backward.linearMap x v.2)),
      v.2 + forward.linearMap x (v.1 - backward.linearMap x v.2)) = _
    let α : E x ≃ₗ[ℂ] F x := a.1.datum.boundary.linearEquiv y
    change forward.linearMap x = α.toLinearMap ∧
      backward.linearMap x = α.symm.toLinearMap at hboundary
    rw [hboundary.1, hboundary.2]
    change (v.1 - α.symm v.2 - α.symm (v.2 + α (v.1 - α.symm v.2)),
      v.2 + α (v.1 - α.symm v.2)) = (-α.symm v.2, α v.1)
    apply Prod.ext <;> simp [map_sub]
  -- The global signed swap uses negation on the original first summand.
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit E → X) *ᵖ E) := isFiniteRank_pullback p
  have hi : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit E → X) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hn : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, -z.snd⟩ : TotalSpace Unit E)) := by
    have hs := continuous_smul_section ((p : TotalSpace Unit E → X) *ᵖ E)
      (ContinuousMap.const _ (-1 : ℂ)) _ hi
    have hc := (Pullback.continuous_lift Unit E p).comp hs
    change Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, (-1 : ℂ) • z.snd⟩ : TotalSpace Unit E)) at hc
    simpa only [neg_one_smul] using hc
  let n : Iso E E :=
    { linearEquiv := fun _ ↦ LinearEquiv.neg ℂ
      continuous_total := hn
      continuous_symm := hn }
  let swap : Iso (F ×ᵇ E) S := sumCommIso.trans (n.sum (Iso.refl F))
  have hswap : swap.IsEquivariant (ρF.sum ρE) (ρE.sum ρF) := by
    intro g x v
    exact Prod.ext (map_neg _ _).symm rfl
  have hsum : (a.sum a.inverse).1.datum.control ⊆ L := Set.union_subset hKL hKL
  refine ⟨L, hL, hLinv, hsum, Set.empty_subset _, T, swap, hT, hswap, ?_⟩
  intro x v
  let y : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (hKL hx)⟩
  have hs : ((a.sum a.inverse).1.datum.enlarge L hL hsum).boundary.linearEquiv x v =
      (a.1.datum.boundary.linearEquiv y v.1,
        (a.1.datum.boundary.linearEquiv y).symm v.2) := by
    simp only [EquivariantSupportBundleTriple.sum, EquivariantSupportBundleTriple.inverse,
      SupportBundleTriple.sum, SupportBundleTriple.ofBoundary,
      SupportBundleTriple.inverse, CompactSupportTriple.sum, CompactSupportTriple.inverse,
      CompactSupportTriple.enlarge, Iso.restrictTo_apply, RelativeTriple.sum_apply]
    rfl
  -- The same invariant exterior is used for both the cutoff endpoint and the original square.
  change swap.linearEquiv x
    (((a.sum a.inverse).1.datum.enlarge L hL hsum).boundary.linearEquiv x v) = _
  rw [hs]
  simp only [EquivariantSupportBundleTriple.identity, SupportBundleTriple.identity,
    SupportBundleTriple.ofBoundary, CompactSupportTriple.enlarge, Iso.restrictTo_apply,
    CompactSupportTriple.ofIso]
  change (-(a.1.datum.boundary.linearEquiv y).symm v.2,
    a.1.datum.boundary.linearEquiv y v.1) = T.linearEquiv x v
  exact (hterminal x v).symm

end AtiyahSinger.ComplexBundle
