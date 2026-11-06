/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundleEmbedding
public import AtiyahSinger.Topology.EquivariantKExternalProduct
public import AtiyahSinger.Topology.EquivariantOpenBundleGluing
public import AtiyahSinger.Topology.EquivariantPullbackTransport
public import AtiyahSinger.Topology.OpenEmbeddingKZero
public import AtiyahSinger.Topology.RelativeSymbolExtension

/-!
# Open extension on the original equivariant support group

Public module ID: M1794.

An equivariant open embedding extends compactly supported classes
covariantly. It need not be proper. The construction first restricts an actual
ambient triple whose chosen compact control is contained in the open image.
Its bundles, boundary and actions are precisely their original pullbacks; only
the compactness argument uses the inverse homeomorphism on that image.

For a compact Hausdorff group and locally compact Hausdorff bases, every source
triple is stably the restriction of such an ambient triple. One first stabilizes
on a compact invariant neighborhood by a finite representation complement, then
glues using the actual boundary map outside the control. This does not extend
an arbitrary source bundle individually across the boundary of the open image.
The resulting controlled generator equations determine a unique additive map
on the existing equivariant support presentation. Its specified representation
action, ordinary forgetful comparison and external product are retained.

Sources: Atiyah--Singer I, section 2, pp.489--495, for compact-support functoriality
and its equivariant extension; Spin Geometry I.9.26 and Karoubi II.4.1--4.3 for
open excision. The required equivariant finite-representation complement is
Karoubi I.9.31(d),(g), already stated in EquivariantBundleEmbedding. Its compact
Hausdorff group hypothesis suffices: no Lie atlas, countability, global bundle
rank bound or extension of a bundle to a compactification is assumed here.
The actual controlled-restriction presentation argument is a project supplement.
Controlled restriction, stable extension existence, excision and the unique class
map are proved below, together with its representation action, forgetful comparison,
composition law and original external-product compatibility.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {E F : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- Restrict a controlled triple to an open image containing its entire original control. -/
def CompactSupportTriple.openRestrict (a : CompactSupportTriple E F)
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (hc : a.control ⊆ Set.range f) :
    CompactSupportTriple ((f : X → Y) *ᵖ E) ((f : X → Y) *ᵖ F) where
  control := f ⁻¹' a.control
  isCompact_control := hf.isEmbedding.isInducing.isCompact_preimage' a.isCompact_control hc
  boundary := a.boundary.pullback f

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]

/-- The controlled restriction uses the original pulled actions and boundary square. -/
theorem CompactSupportTriple.IsEquivariant.openRestrict
    {a : CompactSupportTriple E F} {ρE : EquivariantStructure G E}
    {ρF : EquivariantStructure G F} (ha : a.IsEquivariant ρE ρF)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hc : a.control ⊆ Set.range f) :
    (a.openRestrict f hf hc).IsEquivariant (ρE.pullback f heq) (ρF.pullback f heq) := by
  /- Stage 1: the inverse-image control is compact because the entire old
  control is in the open image. Equivariance of f and invariance of the old
  control give invariance of this precise inverse image.
  Stage 2: the original RelativeTriple.pullback evaluates the old boundary
  at f(x). Its intertwining equation is the old equation at that same point,
  with exactly the base transport heq used in the two pulled actions.
  This argument does not infer that f is proper or restrict triples whose
  controls meet the boundary outside its open image. -/
  have hInv (g : G) (x : X) : g • x ∈ (a.openRestrict f hf hc).control ↔
      x ∈ (a.openRestrict f hf hc).control := by
    change f (g • x) ∈ a.control ↔ f x ∈ a.control
    rw [heq g x]
    exact ha.invariant_control g (f x)
  refine ⟨hInv, ?_⟩
  intro g x v
  -- Read both pulled boundary values on their original fibers at f(x).
  have htransport (y z : Y) (hyz : y = z) (hy : y ∈ a.controlᶜ)
      (hz : z ∈ a.controlᶜ) (LE : E (f x) →ₗ[ℂ] E z) (LF : F (f x) →ₗ[ℂ] F z)
      (hsquare : ∀ w, a.boundary.linearEquiv ⟨z, hz⟩ (LE w) =
        LF (a.boundary.linearEquiv ⟨f x, x.property⟩ w)) :
      a.boundary.linearEquiv ⟨y, hy⟩
          ((Eq.mpr (congrArg (fun b ↦ E (f x) →ₗ[ℂ] E b) hyz) LE) v) =
        (Eq.mpr (congrArg (fun b ↦ F (f x) →ₗ[ℂ] F b) hyz) LF)
          (a.boundary.linearEquiv ⟨f x, x.property⟩ v) := by
    subst z
    exact hsquare v
  -- Transport the same original intertwining square along the supplied equivariance equality.
  have hsquare := htransport (f (g • x)) (g • f x) (heq g x)
    (fun h ↦ x.property ((hInv g x).mp h))
    (fun h ↦ x.property ((ha.invariant_control g (f x)).mp h))
    (ρE.linearMap g (f x)) (ρF.linearMap g (f x))
    (ha.boundary_intertwines g ⟨f x, x.property⟩)
  have hl := RelativeTriple.pullback_apply a.boundary f
    ⟨g • x.val, fun h ↦ x.property ((hInv g x).mp h)⟩
    ((ρE.pullback f heq).linearMap g x v)
  have hr := RelativeTriple.pullback_apply a.boundary f x v
  exact hl.trans (hsquare.trans
    (congrArg ((ρF.pullback f heq).linearMap g x) hr).symm)

/-- The actual restricted finite bundles, original boundary and pulled actions. -/
def EquivariantSupportBundleTriple.openRestrict
    (a : EquivariantSupportBundleTriple G Y) (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hc : a.1.datum.control ⊆ Set.range f) : EquivariantSupportBundleTriple G X :=
  EquivariantSupportBundleTriple.ofBoundary (a.1.source.pullback f) (a.1.target.pullback f)
    (a.1.datum.openRestrict f hf hc)
    (a.2.sourceAction.pullback f heq) (a.2.targetAction.pullback f heq)
    (a.2.isEquivariant.openRestrict f hf heq hc)

variable [hGC : CompactSpace G] [hGT : T2Space G]
  [hLX : LocallyCompactSpace X] [hTX : T2Space X]
  [hLY : LocallyCompactSpace Y] [hTY : T2Space Y]

include hGC hGT hLX hTX hLY hTY

section

attribute [local instance] trivialTopology isFiniteRank_trivial sumTopology isFiniteRank_sum
  isFiniteRank_pullback

set_option maxHeartbeats 600000 in

set_option linter.unusedSectionVars false in
/-- A source triple extends stably with compact control inside the actual open image. -/
theorem EquivariantSupportBundleTriple.exists_openExtension
    (a : EquivariantSupportBundleTriple G X) (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    ∃ b : EquivariantSupportBundleTriple G Y,
      ∃ hc : b.1.datum.control ⊆ Set.range f,
        (b.openRestrict f hf heq hc).IsStablyIsomorphic a :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  -- Stabilize only on one invariant compact window; retain both original bundle actions.
  let E := a.1.source.Fiber
  let F := a.1.target.Fiber
  let σ := a.2.sourceAction
  let τ := a.2.targetAction
  obtain ⟨V, hV, hKV, hVinv, K, hK, hVK, hKinv, ρ, hρinv, hρzero, hρone⟩ :=
    exists_invariant_time_cutoff (G := G) a.1.datum.control a.1.datum.isCompact_control
  obtain ⟨U, hU, hKU, hUinv, L, hL, hUL, hLinv, _, _, _, _⟩ :=
    exists_invariant_time_cutoff (G := G) K hK
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let : MulAction G L := {
    smul g x := ⟨g • x.val, (hLinv g x.val).mpr x.property⟩
    one_smul x := Subtype.ext (one_smul G x.val)
    mul_smul g h x := Subtype.ext (mul_smul g h x.val) }
  let : ContinuousSMul G L := ⟨
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  let j : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let EL := a.1.source.pullback j
  let FL := a.1.target.pullback j
  let σL := σ.pullback j (fun _ _ ↦ rfl)
  let τL := τ.pullback j (fun _ _ ↦ rfl)
  obtain ⟨CE, υ, κE, eE, heE⟩ := σL.exists_finiteRepresentation_complement
  obtain ⟨CF, ω, κF, eF, heF⟩ := τL.exists_finiteRepresentation_complement
  let TE := Bundle.Trivial L (Fin κE.dimension → ℂ)
  let TF := Bundle.Trivial L (Fin κF.dimension → ℂ)
  let A := TE ×ᵇ TF
  let σE : EquivariantStructure G TE := .ofFiniteRepresentation κE
  let σF : EquivariantStructure G TF := .ofFiniteRepresentation κF
  let δ : Hom E F := a.1.datum.cutoffHom ρ V hV hKV hρzero
  let ε : Hom F E := a.1.datum.inverse.cutoffHom ρ V hV hKV hρzero
  have hδ := a.2.isEquivariant.cutoffHom ρ V hV hKV hρzero hρinv
  have hε := a.2.isEquivariant.inverse.cutoffHom ρ V hV hKV hρzero hρinv
  let δL : Hom EL.Fiber FL.Fiber := δ.pullback j
  let εL : Hom FL.Fiber EL.Fiber := ε.pullback j
  let iE : Hom EL.Fiber TE := eE.toHom.comp sumInl
  let iF : Hom FL.Fiber TF := eF.toHom.comp sumInl
  let iC : Hom CF.Fiber TF := eF.toHom.comp sumInr
  let rE : Hom TE EL.Fiber := sumFst.comp eE.symm.toHom
  let rF : Hom TF FL.Fiber := sumFst.comp eF.symm.toHom
  let rC : Hom TF CF.Fiber := sumSnd.comp eF.symm.toHom
  have hrEiE (x : L) (v : EL.Fiber x) : rE.linearMap x (iE.linearMap x v) = v := by
    change ((eE.linearEquiv x).symm (eE.linearEquiv x (v, 0))).1 = v
    rw [LinearEquiv.symm_apply_apply]
  have hrFiF (x : L) (v : FL.Fiber x) : rF.linearMap x (iF.linearMap x v) = v := by
    change ((eF.linearEquiv x).symm (eF.linearEquiv x (v, 0))).1 = v
    rw [LinearEquiv.symm_apply_apply]
  have hrCiC (x : L) (v : CF.Fiber x) : rC.linearMap x (iC.linearMap x v) = v := by
    change ((eF.linearEquiv x).symm (eF.linearEquiv x (0, v))).2 = v
    rw [LinearEquiv.symm_apply_apply]
  have hrCiF (x : L) (v : FL.Fiber x) : rC.linearMap x (iF.linearMap x v) = 0 := by
    change ((eF.linearEquiv x).symm (eF.linearEquiv x (v, 0))).2 = 0
    rw [LinearEquiv.symm_apply_apply]
  have hrFiC (x : L) (v : CF.Fiber x) : rF.linearMap x (iC.linearMap x v) = 0 := by
    change ((eF.linearEquiv x).symm (eF.linearEquiv x (0, v))).1 = 0
    rw [LinearEquiv.symm_apply_apply]
  have hiFrF (x : L) (v : TF x) :
      iF.linearMap x (rF.linearMap x v) + iC.linearMap x (rC.linearMap x v) = v := by
    change eF.linearEquiv x (((eF.linearEquiv x).symm v).1, 0) +
      eF.linearEquiv x (0, ((eF.linearEquiv x).symm v).2) = v
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    exact (eF.linearEquiv x).apply_symm_apply v
  have hiEeq : iE.IsEquivariant σL σE := by
    intro g x v
    have h := heE g x (v, 0)
    change eE.linearEquiv (g • x) (σL.linearMap g x v, υ.linearMap g x 0) = _ at h
    rw [map_zero] at h
    exact h
  have hiFeq : iF.IsEquivariant τL σF := by
    intro g x v
    have h := heF g x (v, 0)
    change eF.linearEquiv (g • x) (τL.linearMap g x v, ω.linearMap g x 0) = _ at h
    rw [map_zero] at h
    exact h
  have hiCeq : iC.IsEquivariant ω σF := by
    intro g x v
    have h := heF g x (0, v)
    change eF.linearEquiv (g • x) (τL.linearMap g x 0, ω.linearMap g x v) = _ at h
    rw [map_zero] at h
    exact h
  have hrEeq : rE.IsEquivariant σE σL := by
    intro g x v
    have h := heE g x ((eE.linearEquiv x).symm v)
    change eE.linearEquiv (g • x)
      ((σL.sum υ).linearMap g x ((eE.linearEquiv x).symm v)) =
      σE.linearMap g x (eE.linearEquiv x ((eE.linearEquiv x).symm v)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact congrArg Prod.fst ((congrArg (eE.linearEquiv (g • x)).symm h).symm.trans
      ((eE.linearEquiv (g • x)).symm_apply_apply _))
  have hrFeq : rF.IsEquivariant σF τL := by
    intro g x v
    have h := heF g x ((eF.linearEquiv x).symm v)
    change eF.linearEquiv (g • x)
      ((τL.sum ω).linearMap g x ((eF.linearEquiv x).symm v)) =
      σF.linearMap g x (eF.linearEquiv x ((eF.linearEquiv x).symm v)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact congrArg Prod.fst ((congrArg (eF.linearEquiv (g • x)).symm h).symm.trans
      ((eF.linearEquiv (g • x)).symm_apply_apply _))
  have hrCeq : rC.IsEquivariant σF ω := by
    intro g x v
    have h := heF g x ((eF.linearEquiv x).symm v)
    change eF.linearEquiv (g • x)
      ((τL.sum ω).linearMap g x ((eF.linearEquiv x).symm v)) =
      σF.linearMap g x (eF.linearEquiv x ((eF.linearEquiv x).symm v)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact congrArg Prod.snd ((congrArg (eF.linearEquiv (g • x)).symm h).symm.trans
      ((eF.linearEquiv (g • x)).symm_apply_apply _))
  -- Three elementary shears make the image a fixed summand outside K.
  let l : Hom TE TF := iF.comp (δL.comp rE)
  let b : Hom TF TE := iE.comp (εL.comp rF)
  have hlEq : l.IsEquivariant σE σF := by
    intro g x v
    change iF.linearMap (g • x)
      (δ.linearMap ((g • x : L) : X) (rE.linearMap (g • x) (σE.linearMap g x v))) =
        σF.linearMap g x (iF.linearMap x (δ.linearMap x (rE.linearMap x v)))
    rw [hrEeq]
    have hd : δ.linearMap ((g • x : L) : X) (σL.linearMap g x (rE.linearMap x v)) =
        τL.linearMap g x (δ.linearMap x (rE.linearMap x v)) := hδ g x (rE.linearMap x v)
    rw [hd, hiFeq]
  have hbEq : b.IsEquivariant σF σE := by
    intro g x v
    change iE.linearMap (g • x)
      (ε.linearMap ((g • x : L) : X) (rF.linearMap (g • x) (σF.linearMap g x v))) =
        σE.linearMap g x (iE.linearMap x (ε.linearMap x (rF.linearMap x v)))
    rw [hrFeq]
    have hd : ε.linearMap ((g • x : L) : X) (τL.linearMap g x (rF.linearMap x v)) =
        σL.linearMap g x (ε.linearMap x (rF.linearMap x v)) := hε g x (rF.linearMap x v)
    rw [hd, hiEeq]
  let upper : Hom A A := sumInl.comp (b.comp sumSnd)
  let lower : Hom A A := sumInr.comp (l.comp sumFst)
  have hu : ∀ x v, upper.linearMap x (upper.linearMap x v) = 0 := by
    intro x v
    change (b.linearMap x 0, 0) = 0
    simp
  have hd : ∀ x v, lower.linearMap x (lower.linearMap x v) = 0 := by
    intro x v
    change (0, l.linearMap x 0) = 0
    simp
  have hueq : upper.IsEquivariant (σE.sum σF) (σE.sum σF) := by
    intro g x v
    exact Prod.ext (hbEq g x v.2) (map_zero (σF.linearMap g x)).symm
  have hdeq : lower.IsEquivariant (σE.sum σF) (σE.sum σF) := by
    intro g x v
    exact Prod.ext (map_zero (σE.linearMap g x)).symm (hlEq g x v.1)
  obtain ⟨B, hB, hBval, hBinv⟩ := upper.exists_equivariant_shear (σE.sum σF) hu hueq (-1)
  obtain ⟨D, hD, hDval, hDinv⟩ := lower.exists_equivariant_shear (σE.sum σF) hd hdeq 1
  have hBval' (x : L) (v : A x) : B.linearEquiv x v =
      (v.1 - b.linearMap x v.2, v.2) := by
    rw [hBval]
    change (v.1 + (-1 : ℂ) • b.linearMap x v.2, v.2 + (-1 : ℂ) • 0) = _
    simp [sub_eq_add_neg]
  have hDval' (x : L) (v : A x) : D.linearEquiv x v =
      (v.1, v.2 + l.linearMap x v.1) := by
    rw [hDval]
    change (v.1 + (1 : ℂ) • 0, v.2 + (1 : ℂ) • l.linearMap x v.1) = _
    simp
  have hBinv' (x : L) (v : A x) : (B.linearEquiv x).symm v =
      (v.1 + b.linearMap x v.2, v.2) := by
    rw [hBinv]
    change (v.1 + (-(-1) : ℂ) • b.linearMap x v.2, v.2 + (-(-1) : ℂ) • 0) = _
    simp
  have hDinv' (x : L) (v : A x) : (D.linearEquiv x).symm v =
      (v.1, v.2 - l.linearMap x v.1) := by
    rw [hDinv]
    change (v.1 + (-1 : ℂ) • 0, v.2 + (-1 : ℂ) • l.linearMap x v.1) = _
    simp [sub_eq_add_neg]
  let S := (B.trans D).trans B
  have hSeq : S.IsEquivariant (σE.sum σF) (σE.sum σF) := by
    intro g x v
    exact (congrArg (B.linearEquiv (g • x))
      ((congrArg (D.linearEquiv (g • x)) (hB g x v)).trans
        (hD g x (B.linearEquiv x v)))).trans
          (hB g x (D.linearEquiv x (B.linearEquiv x v)))
  let H := EL.Fiber ×ᵇ CF.Fiber
  let I : Hom H A := iE.sum iC
  let J : Hom A H := rE.sum rC
  have hJI (x : L) (v : H x) : J.linearMap x (I.linearMap x v) = v :=
    Prod.ext (hrEiE x v.1) (hrCiC x v.2)
  let P : Hom A A := S.toHom.comp (I.comp (J.comp S.symm.toHom))
  have hPidem (x : L) (v : A x) : P.linearMap x (P.linearMap x v) = P.linearMap x v := by
    change S.linearEquiv x (I.linearMap x (J.linearMap x ((S.linearEquiv x).symm
      (S.linearEquiv x (I.linearMap x (J.linearMap x ((S.linearEquiv x).symm v))))))) = _
    rw [LinearEquiv.symm_apply_apply, hJI]
    rfl
  -- Outside the smaller control, the cutoff maps are the original boundary and its inverse.
  have hεδ (x : L) (hx : x.val ∉ K) (v : EL.Fiber x) :
      εL.linearMap x (δL.linearMap x v) = v := by
    let y : (a.1.datum.controlᶜ : Set X) := ⟨x, fun h ↦ hx (hVK (hKV h))⟩
    obtain ⟨hforward, hbackward⟩ :=
      a.1.datum.cutoffHom_boundary ρ V hV hKV hρzero y (hρone x hx)
    change (a.1.datum.inverse.cutoffHom ρ V hV hKV hρzero).linearMap x
      ((a.1.datum.cutoffHom ρ V hV hKV hρzero).linearMap x v) = v
    rw [hforward, hbackward]
    exact (a.1.datum.boundary.linearEquiv y).symm_apply_apply v
  have hδε (x : L) (hx : x.val ∉ K) (v : FL.Fiber x) :
      δL.linearMap x (εL.linearMap x v) = v := by
    let y : (a.1.datum.controlᶜ : Set X) := ⟨x, fun h ↦ hx (hVK (hKV h))⟩
    obtain ⟨hforward, hbackward⟩ :=
      a.1.datum.cutoffHom_boundary ρ V hV hKV hρzero y (hρone x hx)
    change (a.1.datum.cutoffHom ρ V hV hKV hρzero).linearMap x
      ((a.1.datum.inverse.cutoffHom ρ V hV hKV hρzero).linearMap x v) = v
    rw [hforward, hbackward]
    exact (a.1.datum.boundary.linearEquiv y).apply_symm_apply v
  have hSI (x : L) (hx : x.val ∉ K) (v : H x) :
      S.linearEquiv x (I.linearMap x v) =
        (0, iF.linearMap x (δL.linearMap x v.1) + iC.linearMap x v.2) := by
    change B.linearEquiv x (D.linearEquiv x (B.linearEquiv x
      (iE.linearMap x v.1, iC.linearMap x v.2))) = _
    rw [hBval', hDval', hBval']
    dsimp only
    simp only [b, l, Hom.comp, LinearMap.comp_apply, hrFiC, map_zero, sub_zero,
      hrEiE, map_add, hrFiF, zero_add, hεδ x hx, sub_self, add_comm]
  have hJSinv (x : L) (hx : x.val ∉ K) (v : A x) :
      J.linearMap x ((S.linearEquiv x).symm v) =
        (εL.linearMap x (rF.linearMap x v.2), rC.linearMap x v.2) := by
    change J.linearMap x ((B.linearEquiv x).symm
      ((D.linearEquiv x).symm ((B.linearEquiv x).symm v))) = _
    rw [hBinv', hDinv', hBinv']
    change (rE.linearMap x _, rC.linearMap x _) = _
    dsimp only
    simp only [b, l, Hom.comp, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, map_add, map_sub,
      hrEiE, hrFiF, hrCiF, hεδ x hx]
    apply Prod.ext
    · change (rE.linearMap x v.1 + εL.linearMap x (rF.linearMap x v.2)) +
        (εL.linearMap x (rF.linearMap x v.2) -
          (rE.linearMap x v.1 + εL.linearMap x (rF.linearMap x v.2))) =
        εL.linearMap x (rF.linearMap x v.2)
      abel
    · simp only [add_zero, sub_zero]
  have hPout (x : L) (hx : x.val ∉ K) (v : A x) : P.linearMap x v = (0, v.2) := by
    change S.linearEquiv x (I.linearMap x (J.linearMap x ((S.linearEquiv x).symm v))) = _
    rw [hJSinv x hx, hSI x hx]
    exact Prod.ext rfl ((congrArg (fun w ↦ iF.linearMap x w +
      iC.linearMap x (rC.linearMap x v.2)) (hδε x hx (rF.linearMap x v.2))).trans
        (hiFrF x v.2))
  have hSinveq : S.symm.IsEquivariant (σE.sum σF) (σE.sum σF) := by
    intro g x v
    apply (S.linearEquiv (g • x)).injective
    change S.linearEquiv (g • x) ((S.linearEquiv (g • x)).symm
      ((σE.sum σF).linearMap g x v)) =
        S.linearEquiv (g • x) ((σE.sum σF).linearMap g x ((S.linearEquiv x).symm v))
    rw [LinearEquiv.apply_symm_apply]
    have ht := hSeq g x ((S.linearEquiv x).symm v)
    change S.linearEquiv (g • x) ((σE.sum σF).linearMap g x ((S.linearEquiv x).symm v)) =
      (σE.sum σF).linearMap g x (S.linearEquiv x ((S.linearEquiv x).symm v)) at ht
    rw [LinearEquiv.apply_symm_apply] at ht
    exact ht.symm
  have hIeq : I.IsEquivariant (σL.sum ω) (σE.sum σF) := by
    intro g x v
    exact Prod.ext (hiEeq g x v.1) (hiCeq g x v.2)
  have hJeq : J.IsEquivariant (σE.sum σF) (σL.sum ω) := by
    intro g x v
    exact Prod.ext (hrEeq g x v.1) (hrCeq g x v.2)
  have hPeq : P.IsEquivariant (σE.sum σF) (σE.sum σF) := by
    intro g x v
    change S.linearEquiv (g • x) (I.linearMap (g • x) (J.linearMap (g • x)
      ((S.linearEquiv (g • x)).symm ((σE.sum σF).linearMap g x v)))) = _
    have h₁ := hSinveq g x v
    change (S.linearEquiv (g • x)).symm ((σE.sum σF).linearMap g x v) =
      (σE.sum σF).linearMap g x ((S.linearEquiv x).symm v) at h₁
    exact (congrArg (fun w ↦ S.linearEquiv (g • x)
      (I.linearMap (g • x) (J.linearMap (g • x) w))) h₁).trans
      ((congrArg (fun w ↦ S.linearEquiv (g • x) (I.linearMap (g • x) w))
        (hJeq g x ((S.linearEquiv x).symm v))).trans
          ((congrArg (S.linearEquiv (g • x))
            (hIeq g x (J.linearMap x ((S.linearEquiv x).symm v)))).trans
              (hSeq g x (I.linearMap x (J.linearMap x ((S.linearEquiv x).symm v))))))
  -- Use the ordered representation coordinates to extend that very projection by a constant.
  let κ := κE.directSum κF
  let W := Fin κ.dimension → ℂ
  let e : W ≃L[ℂ] ((Fin κE.dimension → ℂ) × (Fin κF.dimension → ℂ)) :=
    (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin κE.dimension ⊕ Fin κF.dimension ↦ ℂ)
      finSumFinEquiv.symm).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin κE.dimension) (Fin κF.dimension)
        (fun _ ↦ ℂ))
  let T := Bundle.Trivial L W
  have hEcoords : Continuous (fun z : TotalSpace Unit TE ↦ z.snd) :=
    (show Continuous (fun z : TotalSpace Unit TE ↦ (z.proj, z.snd)) from
      continuous_induced_dom).snd
  have hFcoords : Continuous (fun z : TotalSpace Unit TF ↦ z.snd) :=
    (show Continuous (fun z : TotalSpace Unit TF ↦ (z.proj, z.snd)) from
      continuous_induced_dom).snd
  have hAcoords : Continuous (fun z : TotalSpace Unit A ↦
      ((z.proj, z.snd) : L × ((Fin κE.dimension → ℂ) × (Fin κF.dimension → ℂ)))) :=
    (continuous_proj (E := A)).prodMk
      ((hEcoords.comp continuous_sum_fst).prodMk (hFcoords.comp continuous_sum_snd))
  have hTcoords : Continuous (fun z : TotalSpace Unit T ↦ (z.proj, z.snd)) :=
    continuous_induced_dom
  let c : Iso A T := {
    linearEquiv _ := e.symm.toLinearEquiv
    continuous_total := continuous_induced_rng.mpr
      (hAcoords.fst.prodMk (e.symm.continuous.comp hAcoords.snd))
    continuous_symm := continuous_induced_rng.mpr
      ((continuous_induced_rng.mpr
        (hTcoords.fst.prodMk ((e.continuous.comp hTcoords.snd).fst))).prodMk
          (continuous_induced_rng.mpr
            (hTcoords.fst.prodMk ((e.continuous.comp hTcoords.snd).snd)))) }
  have hceq : c.IsEquivariant (σE.sum σF) (.ofFiniteRepresentation κ) := by
    intro g x v
    change e.symm (κE.representation g v.1, κF.representation g v.2) =
      e.symm (κE.representation g (e (e.symm v)).1,
        κF.representation g (e (e.symm v)).2)
    rw [e.apply_symm_apply]
  have hκeq (g : G) (v : W) :
      e (κ.representation g v) = (κE.representation g (e v).1,
        κF.representation g (e v).2) := e.apply_symm_apply _
  let P₀ : Hom T T := c.toHom.comp (P.comp c.symm.toHom)
  let p : C(L, W →L[ℂ] W) := ⟨fun x ↦ (P₀.linearMap x).toContinuousLinearMap, by
    apply continuous_clm_apply.mpr
    intro v
    have hsection : Continuous (fun x : L ↦ (⟨x, v⟩ : TotalSpace Unit T)) :=
      continuous_induced_rng.mpr (continuous_id.prodMk continuous_const)
    exact (continuous_induced_rng.mp (P₀.continuous_total.comp hsection)).snd⟩
  have hpval (x : L) (v : W) : p x v = e.symm (P.linearMap x (e v)) := rfl
  have hp (x : L) (v : W) : p x (p x v) = p x v := by
    simp only [hpval, e.apply_symm_apply, hPidem]
  let q : W →L[ℂ] W := e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.prod (0 : W →L[ℂ] (Fin κE.dimension → ℂ))
      ((ContinuousLinearMap.snd ℂ (Fin κE.dimension → ℂ)
        (Fin κF.dimension → ℂ)).comp e.toContinuousLinearMap)))
  have hqval (v : W) : q v = e.symm (0, (e v).2) := rfl
  have hq (v : W) : q (q v) = q v := by
    simp only [hqval, e.apply_symm_apply]
  have hpout (x : L) (hx : x.val ∉ U) : p x = q := by
    ext v
    rw [hpval, hqval, hPout x (fun h ↦ hx (hKU h))]
  have hpeq (g : G) (x : L) (v : W) : p (g • x) (κ.representation g v) =
      κ.representation g (p x v) := by
    apply e.injective
    rw [hpval, e.apply_symm_apply, hκeq, hpval, hκeq, e.apply_symm_apply]
    exact hPeq g x (e v)
  have hqeq (g : G) (v : W) : q (κ.representation g v) = κ.representation g (q v) := by
    apply e.injective
    rw [hqval, e.apply_symm_apply, hκeq, hqval, hκeq, e.apply_symm_apply]
    exact Prod.ext (map_zero (κE.representation g)).symm rfl
  obtain ⟨Z, ζ, i, r, hi, hr, hri, hir, hirout⟩ :=
    Hom.exists_equivariant_image_extension κ f hf heq L U hL hU hUL hLinv p q hp hq
      hpout hpeq hqeq
  -- The split image supplies an actual ambient boundary on the complement of f(K).
  have hiinj (y : Y) : Function.Injective (i.linearMap y) := by
    intro v w hvw
    exact (hri y v).symm.trans ((congrArg (r.linearMap y) hvw).trans (hri y w))
  have hirK (y : Y) (hy : y ∉ f '' K) (v : W) :
      i.linearMap y (r.linearMap y v) = q v := by
    by_cases hyL : y ∈ f '' L
    · obtain ⟨x, hx, rfl⟩ := hyL
      rw [hir ⟨x, hx⟩, hpval, hPout ⟨x, hx⟩ (fun h ↦ hy ⟨x, h, rfl⟩)]
      exact (hqval v).symm
    · exact hirout _ (fun h ↦ hyL (Set.image_mono hUL h)) v
  let FY := Bundle.Trivial Y (Fin κF.dimension → ℂ)
  let WY := Bundle.Trivial Y W
  let inc : (Fin κF.dimension → ℂ) →L[ℂ] W :=
    e.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℂ (Fin κE.dimension → ℂ) (Fin κF.dimension → ℂ))
  let proj : W →L[ℂ] (Fin κF.dimension → ℂ) :=
    (ContinuousLinearMap.snd ℂ (Fin κE.dimension → ℂ) (Fin κF.dimension → ℂ)).comp
      e.toContinuousLinearMap
  let m : Hom Z.Fiber FY := {
    linearMap y := proj.toLinearMap.comp (i.linearMap y)
    continuous_total := by
      have hc := continuous_induced_rng.mp i.continuous_total
      exact continuous_induced_rng.mpr (hc.fst.prodMk (proj.continuous.comp hc.snd)) }
  let n : Hom FY Z.Fiber := {
    linearMap y := (r.linearMap y).comp inc.toLinearMap
    continuous_total := by
      have hc : Continuous (fun z : TotalSpace Unit FY ↦ (z.proj, z.snd)) :=
        continuous_induced_dom
      have hc' : Continuous (fun z : TotalSpace Unit FY ↦
          (⟨z.proj, inc z.snd⟩ : TotalSpace Unit WY)) :=
        continuous_induced_rng.mpr (hc.fst.prodMk (inc.continuous.comp hc.snd))
      exact r.continuous_total.comp hc' }
  have hmn (y : Y) (hy : y ∉ f '' K) (v : FY y) :
      m.linearMap y (n.linearMap y v) = v := by
    change proj (i.linearMap y (r.linearMap y (inc v))) = v
    rw [hirK y hy, hqval]
    change (e (e.symm (0, (e (e.symm (0, v))).2))).2 = v
    rw [e.apply_symm_apply, e.apply_symm_apply]
  have hnm (y : Y) (hy : y ∉ f '' K) (v : Z.Fiber y) :
      n.linearMap y (m.linearMap y v) = v := by
    apply hiinj y
    change i.linearMap y (r.linearMap y (inc (proj (i.linearMap y v)))) = i.linearMap y v
    rw [hirK y hy, hqval]
    change e.symm (0, (e (e.symm (0, (e (i.linearMap y v)).2))).2) = i.linearMap y v
    rw [e.apply_symm_apply]
    exact (hirK y hy (i.linearMap y v)).symm.trans
      (congrArg (i.linearMap y) (hri y v))
  have hmeq (g : G) (y : Y) (v : Z.Fiber y) :
      m.linearMap (g • y) (ζ.linearMap g y v) = κF.representation g (m.linearMap y v) := by
    change (e (i.linearMap (g • y) (ζ.linearMap g y v))).2 =
      κF.representation g (e (i.linearMap y v)).2
    have h := hi g y v
    change i.linearMap (g • y) (ζ.linearMap g y v) = κ.representation g (i.linearMap y v) at h
    rw [h, hκeq]
  let KY := f '' K
  have hKY : IsCompact KY := hK.image f.continuous
  have hKYinv (g : G) (y : Y) : g • y ∈ KY ↔ y ∈ KY := by
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨g⁻¹ • x, (hKinv g⁻¹ x).mpr hx, ?_⟩
      rw [heq, hxy, inv_smul_smul]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g • x, (hKinv g x).mpr hx, heq g x⟩
  let k : C((KYᶜ : Set Y), Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let β : RelativeTriple Z.Fiber FY KYᶜ := (m.pullback k).toIso (fun y ↦ by
    constructor
    · intro v w hvw
      exact (hnm y y.property v).symm.trans
        ((congrArg (n.linearMap y) hvw).trans (hnm y y.property w))
    · intro v
      exact ⟨n.linearMap y v, hmn y y.property v⟩)
  let d : CompactSupportTriple Z.Fiber FY := {
    control := KY
    isCompact_control := hKY
    boundary := β }
  have hd : d.IsEquivariant ζ (.ofFiniteRepresentation κF) := {
    invariant_control := hKYinv
    boundary_intertwines g y v := hmeq g y v }
  let ambient : EquivariantSupportBundleTriple G Y :=
    .ofBoundary Z (FiniteBundle.trivial Y κF.dimension) d ζ (.ofFiniteRepresentation κF) hd
  have hambient : ambient.1.datum.control ⊆ Set.range f := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  -- Compare the ambient image with E plus the chosen target complement on the same window.
  let fL := f.comp j
  let ZL := Z.pullback fL
  let ζL := ζ.pullback fL (fun g x ↦ heq g x)
  let t := pullbackTrivialIso fL κ.dimension
  have ht (x : L) (v : W) : t.linearEquiv x v = v := pullbackTrivialIso_apply _ _ _ _
  have hti (x : L) (v : W) : (t.linearEquiv x).symm v = v := by
    apply (t.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, ht]
  let iL : Hom ZL.Fiber A := c.symm.toHom.comp (t.toHom.comp (i.pullback fL))
  let rL : Hom A ZL.Fiber := (r.pullback fL).comp (t.symm.toHom.comp c.toHom)
  have hiLval (x : L) (v : ZL.Fiber x) : iL.linearMap x v = e (i.linearMap (f x) v) := by
    change e (t.linearEquiv x (i.linearMap (f x) v)) = _
    rw [ht]
  have hrLval (x : L) (v : A x) : rL.linearMap x v = r.linearMap (f x) (e.symm v) := by
    change r.linearMap (f x) ((t.linearEquiv x).symm (e.symm v)) = _
    rw [hti]
  have hriL (x : L) (v : ZL.Fiber x) : rL.linearMap x (iL.linearMap x v) = v := by
    rw [hrLval, hiLval, e.symm_apply_apply, hri]
  have hirL (x : L) (v : A x) : iL.linearMap x (rL.linearMap x v) = P.linearMap x v := by
    rw [hiLval, hrLval, hir x, hpval, e.apply_symm_apply, e.apply_symm_apply]
  have hiLinj (x : L) : Function.Injective (iL.linearMap x) := by
    intro v w h
    exact (hriL x v).symm.trans ((congrArg (rL.linearMap x) h).trans (hriL x w))
  have hiLeq : iL.IsEquivariant ζL (σE.sum σF) := by
    intro g x v
    have h := (ζ.pullback_maps (.ofFiniteRepresentation κ) fL
      (fun g x ↦ heq g x)).1 i hi g x v
    change i.linearMap (f (g • x.val)) (ζL.linearMap g x v) =
      κ.representation g (i.linearMap (f x) v) at h
    change iL.linearMap (g • x) (ζL.linearMap g x v) =
      (σE.sum σF).linearMap g x (iL.linearMap x v)
    rw [hiLval, hiLval]
    exact (congrArg e h).trans (hκeq g (i.linearMap (f x) v))
  have hrLeq : rL.IsEquivariant (σE.sum σF) ζL := by
    intro g x v
    have h := ((EquivariantStructure.ofFiniteRepresentation κ).pullback_maps ζ fL
      (fun g x ↦ heq g x)).1 r hr g x (e.symm v)
    change r.linearMap (f (g • x.val)) (κ.representation g (e.symm v)) =
      ζL.linearMap g x (r.linearMap (f x) (e.symm v)) at h
    have hc := hceq g x v
    change e.symm ((σE.sum σF).linearMap g x v) = κ.representation g (e.symm v) at hc
    change rL.linearMap (g • x) ((σE.sum σF).linearMap g x v) =
      ζL.linearMap g x (rL.linearMap x v)
    rw [hrLval, hrLval, hc]
    exact h
  let u : Hom H ZL.Fiber := rL.comp (S.toHom.comp I)
  let v : Hom ZL.Fiber H := J.comp (S.symm.toHom.comp iL)
  have hvu (x : L) (w : H x) : v.linearMap x (u.linearMap x w) = w := by
    change J.linearMap x ((S.linearEquiv x).symm
      (iL.linearMap x (rL.linearMap x (S.linearEquiv x (I.linearMap x w))))) = w
    rw [hirL]
    change J.linearMap x ((S.linearEquiv x).symm
      (S.linearEquiv x (I.linearMap x (J.linearMap x ((S.linearEquiv x).symm
        (S.linearEquiv x (I.linearMap x w))))))) = w
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hJI, hJI]
  have huv (x : L) (w : ZL.Fiber x) : u.linearMap x (v.linearMap x w) = w := by
    change rL.linearMap x (P.linearMap x (iL.linearMap x w)) = w
    rw [← hirL, hriL, hriL]
  have hueq' : u.IsEquivariant (σL.sum ω) ζL := by
    intro g x w
    exact (congrArg (fun z ↦ rL.linearMap (g • x) (S.linearEquiv (g • x) z))
      (hIeq g x w)).trans ((congrArg (rL.linearMap (g • x))
        (hSeq g x (I.linearMap x w))).trans (hrLeq g x (S.linearEquiv x (I.linearMap x w))))
  have hveq : v.IsEquivariant ζL (σL.sum ω) := by
    intro g x w
    exact (congrArg (fun z ↦ J.linearMap (g • x) ((S.linearEquiv (g • x)).symm z))
      (hiLeq g x w)).trans ((congrArg (J.linearMap (g • x))
        (hSinveq g x (iL.linearMap x w))).trans
          (hJeq g x ((S.linearEquiv x).symm (iL.linearMap x w))))
  let z : Iso H ZL.Fiber := u.toIso (fun x ↦
    ⟨fun w₁ w₂ h ↦ (hvu x w₁).symm.trans ((congrArg (v.linearMap x) h).trans (hvu x w₂)),
      fun w ↦ ⟨v.linearMap x w, huv x w⟩⟩)
  have hzval (x : L) (w : H x) : z.linearEquiv x w = u.linearMap x w := rfl
  have hzinv (x : L) (w : ZL.Fiber x) : (z.linearEquiv x).symm w = v.linearMap x w := by
    apply (z.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, hzval, huv]
  have hzEq : z.IsEquivariant (σL.sum ω) ζL := hueq'
  -- Stabilize the original pair with the same witnesses and retain the necessary minus sign.
  let pF : C(TotalSpace Unit FL.Fiber, L) := ⟨π Unit FL.Fiber, continuous_proj⟩
  have hFsection : Continuous (fun w : TotalSpace Unit FL.Fiber ↦
      (⟨w, w.snd⟩ : TotalSpace Unit ((pF : TotalSpace Unit FL.Fiber → L) *ᵖ FL.Fiber))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit FL.Fiber pF).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hneg : Continuous (fun w : TotalSpace Unit FL.Fiber ↦
      (⟨w.proj, -w.snd⟩ : TotalSpace Unit FL.Fiber)) := by
    have hc := (Pullback.continuous_lift Unit FL.Fiber pF).comp
      (continuous_smul_section ((pF : TotalSpace Unit FL.Fiber → L) *ᵖ FL.Fiber)
        (ContinuousMap.const _ (-1 : ℂ)) _ hFsection)
    change Continuous (fun w : TotalSpace Unit FL.Fiber ↦
      (⟨w.proj, (-1 : ℂ) • w.snd⟩ : TotalSpace Unit FL.Fiber)) at hc
    simpa only [neg_one_smul] using hc
  let negF : Iso FL.Fiber FL.Fiber := {
    linearEquiv _ := LinearEquiv.neg ℂ
    continuous_total := hneg
    continuous_symm := hneg }
  let assoc := EL.sumAssocIso CF FL
  have hassoc (x : L) (w : EL.Fiber x × (CF.Fiber x × FL.Fiber x)) :
      (assoc.linearEquiv x).symm w = ((w.1, w.2.1), w.2.2) := by
    apply (assoc.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, FiniteBundle.sumAssocIso_apply]
  let initial : Iso (EL.Fiber ×ᵇ TF) (ZL.Fiber ×ᵇ FL.Fiber) :=
    ((Iso.refl EL.Fiber).sum eF.symm).trans
      (((Iso.refl EL.Fiber).sum (sumCommIso (E := FL.Fiber) (F := CF.Fiber))).trans
        (assoc.symm.trans (z.sum negF)))
  have hinitial (x : L) (w : EL.Fiber x × TF x) : initial.linearEquiv x w =
      (u.linearMap x (w.1, rC.linearMap x w.2), -rF.linearMap x w.2) := by
    change (z.sum negF).linearEquiv x ((assoc.linearEquiv x).symm
      (w.1, ((eF.linearEquiv x).symm w.2).2, ((eF.linearEquiv x).symm w.2).1)) = _
    rw [hassoc]
    rfl
  have hinitialEq : initial.IsEquivariant (σL.sum σF) (ζL.sum τL) := by
    intro g x w
    change initial.linearEquiv (g • x) ((σL.sum σF).linearMap g x w) =
      (ζL.sum τL).linearMap g x (initial.linearEquiv x w)
    rw [hinitial, hinitial]
    apply Prod.ext
    · change u.linearMap (g • x)
        (σL.linearMap g x w.1, rC.linearMap (g • x) (σF.linearMap g x w.2)) = _
      rw [hrCeq]
      exact hueq' g x (w.1, rC.linearMap x w.2)
    · change -(rF.linearMap (g • x) (σF.linearMap g x w.2)) =
        τL.linearMap g x (-rF.linearMap x w.2)
      rw [hrFeq, map_neg]
  -- A second rotation gives the boundary-plus-swap map outside K.
  let a₂ : Hom ZL.Fiber FL.Fiber := δL.comp (sumFst.comp v)
  let b₂ : Hom FL.Fiber ZL.Fiber := u.comp (sumInl.comp εL)
  have ha₂Eq : a₂.IsEquivariant ζL τL := by
    intro g x w
    have h := hveq g x w
    have h' := congrArg Prod.fst h
    change (v.linearMap (g • x) (ζL.linearMap g x w)).1 =
      σL.linearMap g x (v.linearMap x w).1 at h'
    change δL.linearMap (g • x) (v.linearMap (g • x) (ζL.linearMap g x w)).1 = _
    rw [h']
    exact hδ g x (v.linearMap x w).1
  have hb₂Eq : b₂.IsEquivariant τL ζL := by
    intro g x w
    have h : εL.linearMap (g • x) (τL.linearMap g x w) =
      σL.linearMap g x (εL.linearMap x w) := hε g x w
    change u.linearMap (g • x) (εL.linearMap (g • x) (τL.linearMap g x w), 0) = _
    rw [h]
    have ht := hueq' g x (εL.linearMap x w, 0)
    change u.linearMap (g • x) (σL.linearMap g x (εL.linearMap x w), ω.linearMap g x 0) = _ at ht
    rw [map_zero] at ht
    exact ht
  let S₂ := ZL.Fiber ×ᵇ FL.Fiber
  let up₂ : Hom S₂ S₂ := sumInl.comp (b₂.comp sumSnd)
  let low₂ : Hom S₂ S₂ := sumInr.comp (a₂.comp sumFst)
  have hup₂ : ∀ x w, up₂.linearMap x (up₂.linearMap x w) = 0 := by
    intro x w
    change (b₂.linearMap x 0, 0) = 0
    rw [map_zero]
    rfl
  have hlow₂ : ∀ x w, low₂.linearMap x (low₂.linearMap x w) = 0 := by
    intro x w
    change (0, a₂.linearMap x 0) = 0
    rw [map_zero]
    rfl
  have hup₂Eq : up₂.IsEquivariant (ζL.sum τL) (ζL.sum τL) := by
    intro g x w
    exact Prod.ext (hb₂Eq g x w.2) (map_zero (τL.linearMap g x)).symm
  have hlow₂Eq : low₂.IsEquivariant (ζL.sum τL) (ζL.sum τL) := by
    intro g x w
    exact Prod.ext (map_zero (ζL.linearMap g x)).symm (ha₂Eq g x w.1)
  obtain ⟨up, hUp, hUpval, _⟩ := up₂.exists_equivariant_shear (ζL.sum τL) hup₂ hup₂Eq (-1)
  obtain ⟨low, hLow, hLowval, _⟩ := low₂.exists_equivariant_shear (ζL.sum τL) hlow₂ hlow₂Eq 1
  have hUpval' (x : L) (w : S₂ x) : up.linearEquiv x w =
      (w.1 - b₂.linearMap x w.2, w.2) := by
    rw [hUpval]
    change (w.1 + (-1 : ℂ) • b₂.linearMap x w.2, w.2 + (-1 : ℂ) • 0) = _
    simp [sub_eq_add_neg]
  have hLowval' (x : L) (w : S₂ x) : low.linearEquiv x w =
      (w.1, w.2 + a₂.linearMap x w.1) := by
    rw [hLowval]
    change (w.1 + (1 : ℂ) • 0, w.2 + (1 : ℂ) • a₂.linearMap x w.1) = _
    simp
  let square := initial.trans ((up.trans low).trans up)
  have hsquareEq : square.IsEquivariant (σL.sum σF) (ζL.sum τL) := by
    intro g x w
    exact (congrArg (fun z ↦ up.linearEquiv (g • x)
      (low.linearEquiv (g • x) (up.linearEquiv (g • x) z))) (hinitialEq g x w)).trans
      ((congrArg (fun z ↦ up.linearEquiv (g • x) (low.linearEquiv (g • x) z))
        (hUp g x (initial.linearEquiv x w))).trans
          ((congrArg (up.linearEquiv (g • x))
            (hLow g x (up.linearEquiv x (initial.linearEquiv x w)))).trans
              (hUp g x (low.linearEquiv x (up.linearEquiv x (initial.linearEquiv x w))))))
  have hsqout (x : L) (hx : x.val ∉ K) (w : EL.Fiber x × TF x) :
      square.linearEquiv x w =
        (u.linearMap x (εL.linearMap x (rF.linearMap x w.2), rC.linearMap x w.2),
          δL.linearMap x w.1) := by
    have haValue (w : H x) : a₂.linearMap x (u.linearMap x w) = δL.linearMap x w.1 := by
      change δL.linearMap x (v.linearMap x (u.linearMap x w)).1 = _
      rw [hvu]
    have hbValue (w : FL.Fiber x) : b₂.linearMap x w = u.linearMap x (εL.linearMap x w, 0) :=
      rfl
    -- The negative F component makes the first shear add the missing source component.
    have hfirst : up.linearEquiv x (initial.linearEquiv x w) =
        (u.linearMap x (w.1 + εL.linearMap x (rF.linearMap x w.2), rC.linearMap x w.2),
          -rF.linearMap x w.2) := by
      rw [hinitial, hUpval']
      change (u.linearMap x (w.1, rC.linearMap x w.2) - b₂.linearMap x (-rF.linearMap x w.2),
        -rF.linearMap x w.2) = _
      rw [map_neg, hbValue, sub_neg_eq_add, ← map_add]
      apply Prod.ext
      · apply congrArg (u.linearMap x)
        change (w.1 + εL.linearMap x (rF.linearMap x w.2), rC.linearMap x w.2 + 0) = _
        rw [add_zero]
      · rfl
    -- The exterior inverse identity cancels precisely the original target projection.
    have hsecond : low.linearEquiv x (up.linearEquiv x (initial.linearEquiv x w)) =
        (u.linearMap x (w.1 + εL.linearMap x (rF.linearMap x w.2), rC.linearMap x w.2),
          δL.linearMap x w.1) := by
      rw [hfirst, hLowval']
      dsimp only
      rw [haValue, map_add, hδε x hx]
      apply Prod.ext
      · rfl
      · change -rF.linearMap x w.2 +
          (δL.linearMap x w.1 + rF.linearMap x w.2) = δL.linearMap x w.1
        abel
    change up.linearEquiv x (low.linearEquiv x (up.linearEquiv x
      (initial.linearEquiv x w))) = _
    rw [hsecond, hUpval']
    dsimp only
    rw [hbValue, hεδ x hx, ← map_sub]
    apply Prod.ext
    · apply congrArg (u.linearMap x)
      change (w.1 + εL.linearMap x (rF.linearMap x w.2) - w.1, rC.linearMap x w.2 - 0) = _
      simp
    · rfl
  have hiLu (x : L) (w : H x) : iL.linearMap x (u.linearMap x w) =
      S.linearEquiv x (I.linearMap x w) := by
    change iL.linearMap x (rL.linearMap x (S.linearEquiv x (I.linearMap x w))) = _
    rw [hirL]
    change S.linearEquiv x (I.linearMap x (J.linearMap x ((S.linearEquiv x).symm
      (S.linearEquiv x (I.linearMap x w))))) = _
    rw [LinearEquiv.symm_apply_apply, hJI]
  have hfxout (x : X) (hx : x ∉ K) : f x ∉ f '' K := by
    rintro ⟨y, hy, hyx⟩
    exact hx ((hf.injective hyx) ▸ hy)
  have hun (x : L) (hx : x.val ∉ K) (w : TF x) :
      u.linearMap x (εL.linearMap x (rF.linearMap x w), rC.linearMap x w) =
        n.linearMap (f x) w := by
    apply hiLinj x
    rw [hiLu, hSI x hx, hiLval]
    dsimp only
    rw [hδε x hx, hiFrF]
    change (0, w) = e (i.linearMap (f x) (r.linearMap (f x) (inc w)))
    rw [hirK (f x) (hfxout x hx), hqval]
    change (0, w) = e (e.symm (0, (e (e.symm (0, w))).2))
    rw [e.apply_symm_apply, e.apply_symm_apply]
  have hsqout' (x : L) (hx : x.val ∉ K) (w : EL.Fiber x × TF x) :
      square.linearEquiv x w = (n.linearMap (f x) w.2, δ.linearMap x w.1) := by
    rw [hsqout x hx, hun x hx]
    rfl
  -- Transfer the local square through the vector-preserving native pullback comparisons.
  let RX := FiniteBundle.trivial X κF.dimension
  let ZX := Z.pullback f
  let σRX : EquivariantStructure G RX.Fiber := .ofFiniteRepresentation κF
  let ζX := ζ.pullback f heq
  let A₀ := E ×ᵇ RX.Fiber
  let A₁ := ZX.Fiber ×ᵇ F
  let σ₀ := σ.sum σRX
  let σ₁ := ζX.sum τ
  let c₀ : Iso (Restrict A₀ L) (EL.Fiber ×ᵇ TF) :=
    (sumPullbackIso j a.1.source RX).trans
      ((Iso.refl EL.Fiber).sum (pullbackTrivialIso j κF.dimension))
  let cZ := pullbackCompIso (E := Z.Fiber) f j
  let c₁ : Iso (ZL.Fiber ×ᵇ FL.Fiber) (Restrict A₁ L) :=
    (cZ.symm.sum (Iso.refl FL.Fiber)).trans (sumPullbackIso j ZX a.1.target).symm
  have hc₀ (x : L) (w : A₀ x) : c₀.linearEquiv x w = w := by
    change (w.1, (pullbackTrivialIso j κF.dimension).linearEquiv x w.2) = w
    rw [pullbackTrivialIso_apply]
  have hcZ (x : L) (w : ZL.Fiber x) : (cZ.linearEquiv x).symm w = w := by
    apply (cZ.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
  have hc₁ (x : L) (w : ZL.Fiber x × FL.Fiber x) : c₁.linearEquiv x w = w := by
    change ((cZ.linearEquiv x).symm w.1, w.2) = w
    rw [hcZ]
    rfl
  obtain ⟨nativeSquare, hnative⟩ : ∃ nativeSquare : RelativeTriple A₀ A₁ L,
      ∀ (x : L) (w : A₀ x), nativeSquare.linearEquiv x w = square.linearEquiv x w := by
    refine ⟨c₀.trans (square.trans c₁), ?_⟩
    intro x w
    change c₁.linearEquiv x (square.linearEquiv x (c₀.linearEquiv x w)) = _
    rw [hc₀, hc₁]
  let inside : RelativeTriple A₀ A₁ U := nativeSquare.restrictTo hUL
  have hinside (x : U) (w : A₀ x) : inside.linearEquiv x w =
      square.linearEquiv ⟨x, hUL x.property⟩ w := by
    exact (Iso.restrictTo_apply (E := A₀) (F := A₁) nativeSquare hUL x w).trans
      (hnative ⟨x.val, hUL x.property⟩ w)
  have hinsideEq (g : G) (x : U) (w : A₀ x) :
      inside.linearEquiv ⟨g • x.val, (hUinv g x.val).mpr x.property⟩
          (σ₀.linearMap g x.val w) = σ₁.linearMap g x.val (inside.linearEquiv x w) := by
    rw [hinside, hinside]
    exact hsquareEq g ⟨x, hUL x.property⟩ w
  let tF := pullbackTrivialIso f κF.dimension
  have htF (x : X) (w : Fin κF.dimension → ℂ) : tF.linearEquiv x w = w :=
    pullbackTrivialIso_apply _ _ _ _
  have htFi (x : X) (w : Fin κF.dimension → ℂ) : (tF.linearEquiv x).symm w = w := by
    apply (tF.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, htF]
  let mX : Hom ZX.Fiber RX.Fiber := tF.toHom.comp (m.pullback f)
  let nX : Hom RX.Fiber ZX.Fiber := (n.pullback f).comp tF.symm.toHom
  have hmX (x : X) (w : ZX.Fiber x) : mX.linearMap x w = m.linearMap (f x) w := by
    change tF.linearEquiv x (m.linearMap (f x) w) = _
    rw [htF]
  have hnX (x : X) (w : RX.Fiber x) : nX.linearMap x w = n.linearMap (f x) w := by
    change n.linearMap (f x) ((tF.linearEquiv x).symm w) = _
    rw [htFi]
  let kX : C((Kᶜ : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  let outZ : RelativeTriple ZX.Fiber RX.Fiber Kᶜ := (mX.pullback kX).toIso (fun x ↦ by
    constructor
    · intro w₁ w₂ h
      have h' : m.linearMap (f x) w₁ = m.linearMap (f x) w₂ :=
        (hmX x w₁).symm.trans (h.trans (hmX x w₂))
      exact (hnm (f x) (hfxout x x.property) w₁).symm.trans
        ((congrArg (n.linearMap (f x)) h').trans (hnm (f x) (hfxout x x.property) w₂))
    · intro w
      refine ⟨n.linearMap (f x) w, ?_⟩
      exact (hmX x _).trans (hmn (f x) (hfxout x x.property) w))
  have houtZ (x : (Kᶜ : Set X)) (w : ZX.Fiber x) :
      outZ.linearEquiv x w = m.linearMap (f x) w := hmX x w
  have houtZi (x : (Kᶜ : Set X)) (w : RX.Fiber x) :
      (outZ.linearEquiv x).symm w = n.linearMap (f x) w := by
    apply (outZ.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, houtZ, hmn (f x) (hfxout x x.property)]
  let α := (a.1.datum.enlarge K hK (hKV.trans hVK)).boundary
  let outside : RelativeTriple A₀ A₁ Kᶜ := (sumPullbackIso kX a.1.source RX).trans
    ((Iso.sum α outZ.symm).trans
      ((sumCommIso (E := Restrict F Kᶜ) (F := Restrict ZX.Fiber Kᶜ)).trans
        (sumPullbackIso kX ZX a.1.target).symm))
  have houtside (x : (Kᶜ : Set X)) (w : A₀ x) : outside.linearEquiv x w =
      (n.linearMap (f x) w.2, α.linearEquiv x w.1) := by
    change ((outZ.linearEquiv x).symm w.2, α.linearEquiv x w.1) = _
    rw [houtZi]
  -- Glue that square to the original exterior map; both pieces use the same actions.
  have hnEq : n.IsEquivariant (.ofFiniteRepresentation κF) ζ := by
    intro g y w
    have hinc : inc (κF.representation g w) = κ.representation g (inc w) := by
      apply e.injective
      change e (e.symm (0, κF.representation g w)) = e (κ.representation g (inc w))
      rw [e.apply_symm_apply, hκeq]
      change (0, κF.representation g w) =
        (κE.representation g (e (e.symm (0, w))).1,
          κF.representation g (e (e.symm (0, w))).2)
      rw [e.apply_symm_apply, map_zero]
    change r.linearMap (g • y) (inc (κF.representation g w)) =
      ζ.linearMap g y (r.linearMap y (inc w))
    rw [hinc]
    exact hr g y (inc w)
  have hnXEq (g : G) (x : X) (w : RX.Fiber x) :
      n.linearMap (f (g • x)) (σRX.linearMap g x w) = ζX.linearMap g x (n.linearMap (f x) w) :=
    ((EquivariantStructure.ofFiniteRepresentation κF).pullback_maps ζ f heq).1 n hnEq g x w
  have hα := a.2.isEquivariant.enlarge K hK (hKV.trans hVK) hKinv
  have houtsideEq (g : G) (x : (Kᶜ : Set X)) (w : A₀ x) :
      outside.linearEquiv ⟨g • x.val, fun h ↦ x.property ((hKinv g x.val).mp h)⟩
          (σ₀.linearMap g x.val w) = σ₁.linearMap g x.val (outside.linearEquiv x w) := by
    rw [houtside, houtside]
    exact Prod.ext (hnXEq g x w.2) (hα.boundary_intertwines g x w.1)
  have hδout (x : (Kᶜ : Set X)) (w : E x) : δ.linearMap x w = α.linearEquiv x w := by
    let y : (a.1.datum.controlᶜ : Set X) := ⟨x, fun h ↦ x.property (hVK (hKV h))⟩
    have hforward := (a.1.datum.cutoffHom_boundary ρ V hV hKV hρzero y
      (hρone x x.property)).1
    have hc : δ.linearMap x w = a.1.datum.boundary.linearEquiv y w :=
      congrArg (fun L ↦ L w) hforward
    change δ.linearMap x w = (a.1.datum.boundary.restrictTo _).linearEquiv x w
    rw [Iso.restrictTo_apply]
    exact hc
  have hagree (x : X) (hxU : x ∈ U) (hxK : x ∈ Kᶜ) :
      inside.linearEquiv ⟨x, hxU⟩ = outside.linearEquiv ⟨x, hxK⟩ := by
    apply LinearEquiv.ext
    intro w
    change A₀ x at w
    calc
      inside.linearEquiv ⟨x, hxU⟩ w = square.linearEquiv ⟨x, hUL hxU⟩ w :=
        hinside ⟨x, hxU⟩ w
      _ = (n.linearMap (f x) w.2, δ.linearMap x w.1) :=
        hsqout' ⟨x, hUL hxU⟩ hxK w
      _ = (n.linearMap (f x) w.2, α.linearEquiv ⟨x, hxK⟩ w.1) :=
        Prod.ext rfl (hδout ⟨x, hxK⟩ w.1)
      _ = outside.linearEquiv ⟨x, hxK⟩ w := (houtside ⟨x, hxK⟩ w).symm
  have hcover : U ∪ Kᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  have hKcinv (g : G) (x : X) : g • x ∈ Kᶜ ↔ x ∈ Kᶜ := not_congr (hKinv g x)
  obtain ⟨uG, huG, _, huGout⟩ := Iso.exists_equivariant_gluing σ₀ σ₁ U Kᶜ hU
    hK.isClosed.isOpen_compl hcover hUinv hKcinv inside outside hagree hinsideEq houtsideEq
  let vG : Iso (F ×ᵇ RX.Fiber) (((f : X → Y) *ᵖ FY) ×ᵇ F) :=
    sumCommIso.trans (tF.symm.sum (Iso.refl F))
  have hvG (x : X) (w : F x × RX.Fiber x) : vG.linearEquiv x w = (w.2, w.1) := by
    change ((tF.linearEquiv x).symm w.2, w.1) = _
    rw [htFi]
  let ar := ambient.openRestrict f hf heq hambient
  have hvGEq : vG.IsEquivariant (τ.sum σRX) (ar.2.targetAction.sum τ) := by
    intro g x w
    change vG.linearEquiv (g • x) ((τ.sum σRX).linearMap g x w) =
      (ar.2.targetAction.sum τ).linearMap g x (vG.linearEquiv x w)
    rw [hvG, hvG]
    rfl
  have haControl : (a.sum (.identity RX σRX)).1.datum.control ⊆ K := by
    change a.1.datum.control ∪ ∅ ⊆ K
    exact Set.union_subset (hKV.trans hVK) (Set.empty_subset _)
  have hbControl : (ar.sum (.identity a.1.target τ)).1.datum.control ⊆ K := by
    change f ⁻¹' (f '' K) ∪ ∅ ⊆ K
    apply Set.union_subset _ (Set.empty_subset _)
    rintro x ⟨y, hy, hyx⟩
    exact (hf.injective hyx) ▸ hy
  -- The two global maps now witness the original identity-stable relation on one control.
  have hstable : a.IsStablyIsomorphic ar := by
    refine ⟨RX, a.1.target, σRX, τ, K, hK, hKinv, haControl, hbControl,
      uG, vG, huG, hvGEq, ?_⟩
    intro x w
    change A₀ x at w
    have hug : uG.linearEquiv x w = (n.linearMap (f x) w.2, α.linearEquiv x w.1) :=
      (congrArg (fun L ↦ L w) (huGout x x.property)).trans (houtside x w)
    have hleft : ((a.sum (.identity RX σRX)).1.datum.enlarge K hK haControl).boundary.linearEquiv
        x w = (α.linearEquiv x w.1, w.2) := by
      simp only [EquivariantSupportBundleTriple.sum, EquivariantSupportBundleTriple.identity,
        SupportBundleTriple.sum, SupportBundleTriple.identity, SupportBundleTriple.ofBoundary,
        CompactSupportTriple.sum, CompactSupportTriple.enlarge, Iso.restrictTo_apply,
        RelativeTriple.sum_apply, CompactSupportTriple.ofIso]
      let y : (a.1.datum.controlᶜ : Set X) := ⟨x, fun h ↦ x.property (hVK (hKV h))⟩
      change (a.1.datum.boundary.linearEquiv y w.1, w.2) = (α.linearEquiv x w.1, w.2)
      apply Prod.ext
      · exact (Iso.restrictTo_apply a.1.datum.boundary
          (Set.compl_subset_compl.mpr (hKV.trans hVK)) x w.1).symm
      · rfl
    have hright (w : ar.1.source.Fiber x × F x) :
        ((ar.sum (.identity a.1.target τ)).1.datum.enlarge K hK hbControl).boundary.linearEquiv
          x w = (m.linearMap (f x) w.1, w.2) := by
      simp only [EquivariantSupportBundleTriple.sum, EquivariantSupportBundleTriple.identity,
        SupportBundleTriple.sum, SupportBundleTriple.identity, SupportBundleTriple.ofBoundary,
        CompactSupportTriple.sum, CompactSupportTriple.enlarge, Iso.restrictTo_apply,
        RelativeTriple.sum_apply, CompactSupportTriple.ofIso]
      let y : (f ⁻¹' d.controlᶜ : Set X) := ⟨x, hfxout x x.property⟩
      change ((d.boundary.pullback f).linearEquiv y w.1, w.2) = _
      rw [RelativeTriple.pullback_apply]
      rfl
    change vG.linearEquiv x
      (((a.sum (.identity RX σRX)).1.datum.enlarge K hK haControl).boundary.linearEquiv x w) = _
    rw [hleft, hvG, hright]
    change (w.2, α.linearEquiv x w.1) =
      (m.linearMap (f x) (uG.linearEquiv x w).1, (uG.linearEquiv x w).2)
    rw [hug, hmn (f x) (hfxout x x.property)]
  have hdone : ∃ b : EquivariantSupportBundleTriple G Y,
      ∃ hc : b.1.datum.control ⊆ Set.range f,
        (b.openRestrict f hf heq hc).IsStablyIsomorphic a :=
    ⟨ambient, hambient, EquivariantSupportBundleTriple.isStablyIsomorphic_properties.1.symm hstable⟩
  exact hdone

end

section

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial
  isFiniteRank_pullback

omit hLY

set_option maxHeartbeats 1200000 in
-- The local stable square is transported through its original dependent pullbacks.
/-- A controlled ambient triple whose actual restriction is zero has zero ambient class. -/
theorem EquivariantSupportBundleTriple.kZeroClass_eq_zero_of_openRestrict
    (b : EquivariantSupportBundleTriple G Y) (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hc : b.1.datum.control ⊆ Set.range f)
    (hz : (b.openRestrict f hf heq hc).kZeroClass = 0) : b.kZeroClass = 0 :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let a := b.openRestrict f hf heq hc
  let Z := a.1.target
  let τZ := a.2.targetAction
  have hzero := (equivariantSupportTripleKZero_generator_relations
    (G := G) (X := X)).2.2 Z τZ
  obtain ⟨C, D, σC, σD, K, hK, hKinv, haK, hzK, u, v, hu, hv, hsquare⟩ :=
    (a.kZeroClass_eq_iff_stable (.identity Z τZ)).mp (hz.trans hzero.symm)
  let w : Iso (a.1.source.sum C).Fiber (a.1.target.sum C).Fiber := u.trans v.symm
  have hw (x : X) (s : (a.1.source.sum C).Fiber x) :
      v.linearEquiv x (w.linearEquiv x s) = u.linearEquiv x s :=
    (v.linearEquiv x).apply_symm_apply _
  have hwEq : w.IsEquivariant (a.2.sourceAction.sum σC) (a.2.targetAction.sum σC) := by
    intro g x s
    apply (v.linearEquiv (g • x)).injective
    change v.linearEquiv (g • x) (w.linearEquiv (g • x) _) =
      v.linearEquiv (g • x) ((a.2.targetAction.sum σC).linearMap g x (w.linearEquiv x s))
    rw [hw]
    exact (hu g x s).trans ((hv g x (w.linearEquiv x s)).trans
      (congrArg ((τZ.sum σD).linearMap g x) (hw x s))).symm
  have ha : a.1.datum.control ⊆ K := fun x hx ↦ haK (Or.inl hx)
  let α := (a.1.datum.enlarge K hK ha).boundary
  have hwout (x : (Kᶜ : Set X)) (s : (a.1.source.sum C).Fiber x) :
      w.linearEquiv x s = (α.linearEquiv x s.1, s.2) := by
    apply (v.linearEquiv x).injective
    rw [hw]
    have h := hsquare x s
    simp only [EquivariantSupportBundleTriple.sum, EquivariantSupportBundleTriple.identity,
      SupportBundleTriple.sum, SupportBundleTriple.identity, SupportBundleTriple.ofBoundary,
      CompactSupportTriple.sum, CompactSupportTriple.enlarge, Iso.restrictTo_apply,
      RelativeTriple.sum_apply, CompactSupportTriple.ofIso] at h
    simp only [α, CompactSupportTriple.enlarge, Iso.restrictTo_apply]
    exact h.symm
  -- Replace the one common stabilizer by a fixed representation only on a compact window.
  obtain ⟨U, hU, hKU, hUinv, L, hL, hUL, hLinv, _, _, _, _⟩ :=
    exists_invariant_time_cutoff (G := G) K hK
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let : MulAction G L := {
    smul g x := ⟨g • x.val, (hLinv g x.val).mpr x.property⟩
    one_smul x := Subtype.ext (one_smul G x.val)
    mul_smul g h x := Subtype.ext (mul_smul g h x.val) }
  let : ContinuousSMul G L := ⟨
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  let j : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let fL := f.comp j
  let CL := C.pullback j
  let σCL := σC.pullback j (fun _ _ ↦ rfl)
  obtain ⟨H, σH, κ, e, he⟩ := σCL.exists_finiteRepresentation_complement
  let T := FiniteBundle.trivial Y κ.dimension
  let σT : EquivariantStructure G T.Fiber := .ofFiniteRepresentation κ
  let q (B : FiniteBundle Y) : Iso ((B.sum T).pullback fL).Fiber
      ((((B.pullback f).sum C).pullback j).Fiber ×ᵇ H.Fiber) :=
    (sumPullbackIso fL B T).trans
      ((((pullbackCompIso (E := B.Fiber) f j).symm).sum
          (pullbackTrivialIso fL κ.dimension)).trans
        (((Iso.refl ((B.pullback f).pullback j).Fiber).sum e.symm).trans
          ((((B.pullback f).pullback j).sumAssocIso CL H).symm.trans
            ((sumPullbackIso j (B.pullback f) C).symm.sum (Iso.refl H.Fiber)))))
  have hq (B : FiniteBundle Y) (x : L) (s : ((B.sum T).pullback fL).Fiber x) :
      (q B).linearEquiv x s =
        ((s.1, ((e.linearEquiv x).symm s.2).1), ((e.linearEquiv x).symm s.2).2) := by
    have hcomp (s : B.Fiber (f x)) :
        ((pullbackCompIso (E := B.Fiber) f j).linearEquiv x).symm s = s := by
      apply ((pullbackCompIso (E := B.Fiber) f j).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    have hassoc (s : B.Fiber (f x) × (CL.Fiber x × H.Fiber x)) :
        ((((B.pullback f).pullback j).sumAssocIso CL H).linearEquiv x).symm s =
          ((s.1, s.2.1), s.2.2) := by
      apply ((((B.pullback f).pullback j).sumAssocIso CL H).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, FiniteBundle.sumAssocIso_apply]
      rfl
    change (((((B.pullback f).pullback j).sumAssocIso CL H).linearEquiv x).symm
      (((pullbackCompIso (E := B.Fiber) f j).linearEquiv x).symm s.1,
        (e.linearEquiv x).symm ((pullbackTrivialIso fL κ.dimension).linearEquiv x s.2))) = _
    rw [hcomp, pullbackTrivialIso_apply, hassoc]
  let W : Iso ((b.1.source.sum T).pullback fL).Fiber
      ((b.1.target.sum T).pullback fL).Fiber :=
    (q b.1.source).trans (((w.pullback j).sum (Iso.refl H.Fiber)).trans (q b.1.target).symm)
  have hW (x : L) (s : ((b.1.source.sum T).pullback fL).Fiber x) :
      W.linearEquiv x s =
        ((w.linearEquiv x (s.1, ((e.linearEquiv x).symm s.2).1)).1,
          e.linearEquiv x ((w.linearEquiv x (s.1, ((e.linearEquiv x).symm s.2).1)).2,
            ((e.linearEquiv x).symm s.2).2)) := by
    apply ((q b.1.target).linearEquiv x).injective
    change (q b.1.target).linearEquiv x
      (((q b.1.target).linearEquiv x).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    change (w.linearEquiv x ((q b.1.source).linearEquiv x s).1,
      ((q b.1.source).linearEquiv x s).2) = (q b.1.target).linearEquiv x _
    simp only [hq, LinearEquiv.symm_apply_apply]
    rfl
  have heinv (g : G) (x : L) (t : Fin κ.dimension → ℂ) :
      (e.linearEquiv (g • x)).symm (κ.representation g t) =
        (σC.linearMap g x ((e.linearEquiv x).symm t).1,
          σH.linearMap g x ((e.linearEquiv x).symm t).2) := by
    apply (e.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((he g x ((e.linearEquiv x).symm t)).trans
      (congrArg (κ.representation g) ((e.linearEquiv x).apply_symm_apply t))).symm
  have hWEq (g : G) (x : L) (s : ((b.1.source.sum T).pullback fL).Fiber x) :
      W.linearEquiv (g • x) (a.2.sourceAction.linearMap g x s.1, κ.representation g s.2) =
        (a.2.targetAction.linearMap g x (W.linearEquiv x s).1,
          κ.representation g (W.linearEquiv x s).2) := by
    rw [hW, hW, heinv]
    have h : w.linearEquiv (g • x.val)
        (a.2.sourceAction.linearMap g x s.1,
          σC.linearMap g x ((e.linearEquiv x).symm s.2).1) =
        (a.2.targetAction.linearMap g x
          (w.linearEquiv x (s.1, ((e.linearEquiv x).symm s.2).1)).1,
          σC.linearMap g x (w.linearEquiv x (s.1, ((e.linearEquiv x).symm s.2).1)).2) :=
      hwEq g x (s.1, ((e.linearEquiv x).symm s.2).1)
    dsimp only at h ⊢
    exact (congrArg (fun z : (a.1.target.sum C).Fiber (g • x.val) ↦
      (z.1, e.linearEquiv (g • x) (z.2,
        σH.linearMap g x ((e.linearEquiv x).symm s.2).2))) h).trans
      (Prod.ext rfl (he g x
        ((w.linearEquiv x (s.1, ((e.linearEquiv x).symm s.2).1)).2,
          ((e.linearEquiv x).symm s.2).2)))
  let c := b.sum (.identity T σT)
  let KY := f '' K
  have hKY : IsCompact KY := hK.image f.continuous
  have himageinv (S : Set X) (hinv : ∀ (g : G) (x : X), g • x ∈ S ↔ x ∈ S)
      (g : G) (y : Y) : g • y ∈ f '' S ↔ y ∈ f '' S := by
    constructor
    · rintro ⟨x, hx, hxy⟩
      refine ⟨g⁻¹ • x, (hinv g⁻¹ x).mpr hx, ?_⟩
      rw [heq, hxy, inv_smul_smul]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g • x, (hinv g x).mpr hx, heq g x⟩
  have hbK : b.1.datum.control ⊆ KY := by
    intro y hy
    obtain ⟨x, rfl⟩ := hc hy
    exact ⟨x, ha hy, rfl⟩
  have hcK : c.1.datum.control ⊆ KY :=
    Set.union_subset hbK (Set.empty_subset _)
  let β := (c.1.datum.enlarge KY hKY hcK).boundary
  have hfx (x : X) (hx : x ∉ K) : f x ∉ KY := by
    rintro ⟨z, hz, hzx⟩
    exact hx ((hf.injective hzx) ▸ hz)
  have hβ (y : (KYᶜ : Set Y)) (s : c.1.source.Fiber y) :
      β.linearEquiv y s =
        (b.1.datum.boundary.linearEquiv ⟨y, fun h ↦ y.property (hbK h)⟩ s.1, s.2) := by
    simp only [β, c, EquivariantSupportBundleTriple.sum,
      EquivariantSupportBundleTriple.identity, SupportBundleTriple.sum,
      SupportBundleTriple.identity, SupportBundleTriple.ofBoundary, CompactSupportTriple.sum,
      CompactSupportTriple.enlarge, Iso.restrictTo_apply, RelativeTriple.sum_apply,
      CompactSupportTriple.ofIso]
    rfl
  have hWout (x : L) (hx : x.val ∉ K)
      (s : ((b.1.source.sum T).pullback fL).Fiber x) :
      W.linearEquiv x s = β.linearEquiv ⟨f x, hfx x hx⟩ s := by
    rw [hW, hwout ⟨x, hx⟩]
    change (α.linearEquiv ⟨x, hx⟩ s.1,
      e.linearEquiv x ((e.linearEquiv x).symm s.2)) = _
    rw [LinearEquiv.apply_symm_apply, hβ]
    have hα : α.linearEquiv ⟨x, hx⟩ s.1 =
        b.1.datum.boundary.linearEquiv ⟨f x, fun h ↦ hx (ha h)⟩ s.1 := by
      simp only [α, CompactSupportTriple.enlarge, Iso.restrictTo_apply]
      exact RelativeTriple.pullback_apply b.1.datum.boundary f
        ⟨x, fun h ↦ hx (ha h)⟩ s.1
    exact congrArg (fun z : b.1.target.Fiber (f x) ↦ (z, s.2)) hα
  -- Descend this exact local square, then glue to the original boundary outside the control.
  obtain ⟨d, hd⟩ := Iso.exists_descend_embedding (E := c.1.source.Fiber) (F := c.1.target.Fiber) fL
    (hf.isEmbedding.comp IsEmbedding.subtypeVal) W
  have hUrange : f '' U ⊆ Set.range fL := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hUL hx⟩, rfl⟩
  let inside := d.restrictTo hUrange
  have hin (x : X) (hx : x ∈ U) (s : c.1.source.Fiber (f x)) :
      inside.linearEquiv ⟨f x, ⟨x, hx, rfl⟩⟩ s = W.linearEquiv ⟨x, hUL hx⟩ s := by
    rw [Iso.restrictTo_apply]
    exact hd ⟨x, hUL hx⟩ s
  have hinsideEq (g : G) (y : f '' U) (s : c.1.source.Fiber y) :
      inside.linearEquiv ⟨g • y.val, (himageinv U hUinv g y).mpr y.property⟩
          (c.2.sourceAction.linearMap g y s) =
        c.2.targetAction.linearMap g y (inside.linearEquiv y s) := by
    rcases y with ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    have hpull : inside.linearEquiv ⟨f (g • x), ⟨g • x, (hUinv g x).mpr hx, rfl⟩⟩
        ((c.2.sourceAction.pullback f heq).linearMap g x s) =
      (c.2.targetAction.pullback f heq).linearMap g x
        (inside.linearEquiv ⟨f x, ⟨x, hx, rfl⟩⟩ s) := by
      rw [hin (g • x) ((hUinv g x).mpr hx), hin x hx]
      have hsource : (c.2.sourceAction.pullback f heq).linearMap g x s =
          (a.2.sourceAction.linearMap g x s.1, κ.representation g s.2) :=
        EquivariantStructure.sumPullbackIso_isEquivariant b.1.source T
          b.2.sourceAction σT f heq g x s
      have htarget : (c.2.targetAction.pullback f heq).linearMap g x
          (W.linearEquiv ⟨x, hUL hx⟩ s) =
          (a.2.targetAction.linearMap g x (W.linearEquiv ⟨x, hUL hx⟩ s).1,
            κ.representation g (W.linearEquiv ⟨x, hUL hx⟩ s).2) :=
        EquivariantStructure.sumPullbackIso_isEquivariant b.1.target T
          b.2.targetAction σT f heq g x (W.linearEquiv ⟨x, hUL hx⟩ s)
      exact (congrArg (W.linearEquiv ⟨g • x, hUL ((hUinv g x).mpr hx)⟩) hsource).trans
        ((hWEq g ⟨x, hUL hx⟩ s).trans htarget.symm)
    have htransport (y z : Y) (h : y = z) (hy : y ∈ f '' U) (hz : z ∈ f '' U)
        (LE : c.1.source.Fiber (f x) →ₗ[ℂ] c.1.source.Fiber z)
        (LF : c.1.target.Fiber (f x) →ₗ[ℂ] c.1.target.Fiber z)
        (hs : inside.linearEquiv ⟨y, hy⟩
            ((Eq.mpr (congrArg (fun t ↦ c.1.source.Fiber (f x) →ₗ[ℂ]
              c.1.source.Fiber t) h) LE) s) =
          (Eq.mpr (congrArg (fun t ↦ c.1.target.Fiber (f x) →ₗ[ℂ]
            c.1.target.Fiber t) h) LF) (inside.linearEquiv ⟨f x, ⟨x, hx, rfl⟩⟩ s)) :
        inside.linearEquiv ⟨z, hz⟩ (LE s) =
          LF (inside.linearEquiv ⟨f x, ⟨x, hx, rfl⟩⟩ s) := by
      subst z
      exact hs
    exact htransport (f (g • x)) (g • f x) (heq g x) _ _
      (c.2.sourceAction.linearMap g (f x)) (c.2.targetAction.linearMap g (f x)) hpull
  have hagree (y : Y) (hy : y ∈ f '' U) (hyK : y ∈ KYᶜ) :
      inside.linearEquiv ⟨y, hy⟩ = β.linearEquiv ⟨y, hyK⟩ := by
    obtain ⟨x, hx, rfl⟩ := hy
    apply LinearEquiv.ext
    intro s
    exact (hin x hx s).trans (hWout ⟨x, hUL hx⟩ (fun h ↦ hyK ⟨x, h, rfl⟩) s)
  have hcover : f '' U ∪ KYᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ KY
    · exact Or.inl (Set.image_mono hKU hy)
    · exact Or.inr hy
  have hβeq := c.2.isEquivariant.enlarge KY hKY hcK (himageinv K hKinv)
  obtain ⟨J, hJ, _, hJout⟩ := Iso.exists_equivariant_gluing
    c.2.sourceAction c.2.targetAction (f '' U) KYᶜ (hf.isOpenMap U hU)
    hKY.isClosed.isOpen_compl hcover (himageinv U hUinv)
    (fun g y ↦ not_congr (himageinv K hKinv g y)) inside β hagree hinsideEq
    hβeq.boundary_intertwines
  have hiso : c.IsIsomorphic (.identity c.1.target c.2.targetAction) := by
    refine ⟨KY, hKY, himageinv K hKinv, hcK, Set.empty_subset _,
      J, Iso.refl c.1.target.Fiber, hJ, (fun _ _ _ ↦ rfl), ?_⟩
    intro y s
    change β.linearEquiv y s =
      (((CompactSupportTriple.ofIso (Iso.refl c.1.target.Fiber)).enlarge
        KY hKY (Set.empty_subset _)).boundary.linearEquiv y) (J.linearEquiv y s)
    simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply,
      CompactSupportTriple.ofIso]
    exact (congrArg (fun L ↦ L s) (hJout y y.property)).symm
  -- The ambient isomorphism kills the stabilized triple; the same identity summand has zero class.
  obtain ⟨hi, hsum, hid⟩ := equivariantSupportTripleKZero_generator_relations
    (G := G) (X := Y)
  have hclass := (hi _ _ hiso).trans (hid c.1.target c.2.targetAction)
  change (b.sum (.identity T σT)).kZeroClass = 0 at hclass
  rw [hsum, hid, add_zero] at hclass
  exact hclass


end

section

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback

set_option maxHeartbeats 600000 in
-- The generator comparisons retain the complete original sum and pullback expressions.
/-- Controlled restriction and stable gluing determine a unique open-extension homomorphism. -/
theorem existsUnique_equivariantSupportTripleKZeroOpenPushforward
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    ∃! Φ : EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G Y,
      ∀ (b : EquivariantSupportBundleTriple G Y)
        (hc : b.1.datum.control ⊆ Set.range f),
        Φ (b.openRestrict f hf heq hc).kZeroClass = b.kZeroClass :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  have hsum (A B : EquivariantSupportBundleTriple G Y)
      (hA : A.1.datum.control ⊆ Set.range f) (hB : B.1.datum.control ⊆ Set.range f) :
      ((A.sum B).openRestrict f hf heq (Set.union_subset hA hB)).kZeroClass =
        (A.openRestrict f hf heq hA).kZeroClass + (B.openRestrict f hf heq hB).kZeroClass := by
    let a := A.openRestrict f hf heq hA
    let b := B.openRestrict f hf heq hB
    let c := (A.sum B).openRestrict f hf heq (Set.union_subset hA hB)
    let K := c.1.datum.control
    have hK : IsCompact K := c.1.datum.isCompact_control
    let u := sumPullbackIso f A.1.source B.1.source
    let v := sumPullbackIso f A.1.target B.1.target
    have hi : c.IsIsomorphic (a.sum b) := by
      refine ⟨K, hK, c.2.isEquivariant.invariant_control, Set.Subset.rfl,
        Set.Subset.rfl, u, v,
        EquivariantStructure.sumPullbackIso_isEquivariant _ _ _ _ f heq,
        EquivariantStructure.sumPullbackIso_isEquivariant _ _ _ _ f heq, ?_⟩
      intro x s
      let R := A.1.datum.control ∪ B.1.datum.control
      have hR : IsCompact R := A.1.datum.isCompact_control.union B.1.datum.isCompact_control
      let y : (Rᶜ : Set Y) := ⟨f x, x.property⟩
      have hl := c.1.datum.enlarge_apply K hK (Set.Subset.refl _) x s
      have hp := RelativeTriple.pullback_apply (A.1.datum.sum B.1.datum).boundary f x s
      have hs := RelativeTriple.sum_apply
        (A.1.datum.enlarge R hR Set.subset_union_left).boundary
        (B.1.datum.enlarge R hR Set.subset_union_right).boundary y s
      have ha := A.1.datum.enlarge_apply R hR Set.subset_union_left y s.1
      have hb := B.1.datum.enlarge_apply R hR Set.subset_union_right y s.2
      have hleft := hl.trans (hp.trans (hs.trans (congrArg₂ Prod.mk ha hb)))
      have hr := (a.1.datum.sum b.1.datum).enlarge_apply K hK (Set.Subset.refl _) x s
      have ht := RelativeTriple.sum_apply
        (a.1.datum.enlarge K hK Set.subset_union_left).boundary
        (b.1.datum.enlarge K hK Set.subset_union_right).boundary x s
      have hpa := a.1.datum.enlarge_apply K hK Set.subset_union_left x s.1
      have hpb := b.1.datum.enlarge_apply K hK Set.subset_union_right x s.2
      have hqa := RelativeTriple.pullback_apply A.1.datum.boundary f
        ⟨x.val, fun h ↦ x.property (Or.inl h)⟩ s.1
      have hqb := RelativeTriple.pullback_apply B.1.datum.boundary f
        ⟨x.val, fun h ↦ x.property (Or.inr h)⟩ s.2
      have hright := hr.trans (ht.trans (congrArg₂ Prod.mk (hpa.trans hqa) (hpb.trans hqb)))
      exact hleft.trans hright.symm
    exact ((equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).1
      c (a.sum b) hi).trans
      ((equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).2.1 a b)
  have hinverse (B : EquivariantSupportBundleTriple G Y)
      (hB : B.1.datum.control ⊆ Set.range f) :
      (B.inverse.openRestrict f hf heq hB).kZeroClass =
        -(B.openRestrict f hf heq hB).kZeroClass := by
    let a := B.openRestrict f hf heq hB
    let b := B.inverse.openRestrict f hf heq hB
    let K := a.1.datum.control
    have hK : IsCompact K := a.1.datum.isCompact_control
    have hi : b.IsIsomorphic a.inverse := by
      refine ⟨K, hK, a.2.isEquivariant.invariant_control, Set.Subset.rfl,
        Set.Subset.rfl, Iso.refl _, Iso.refl _, (fun _ _ _ ↦ rfl),
        (fun _ _ _ ↦ rfl), ?_⟩
      intro x s
      simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
      change (RelativeTriple.pullback B.1.datum.boundary.symm f).linearEquiv x s =
        ((RelativeTriple.pullback B.1.datum.boundary f).linearEquiv x).symm s
      apply ((RelativeTriple.pullback B.1.datum.boundary f).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, RelativeTriple.pullback_apply,
        RelativeTriple.pullback_apply]
      exact (B.1.datum.boundary.linearEquiv ⟨f x, x.property⟩).apply_symm_apply s
    exact ((equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).1
      b a.inverse hi).trans a.kZeroClass_inverse
  -- Equality of restrictions detects equality of controlled ambient classes by excision.
  have hsame (A B : EquivariantSupportBundleTriple G Y)
      (hA : A.1.datum.control ⊆ Set.range f) (hB : B.1.datum.control ⊆ Set.range f)
      (h : (A.openRestrict f hf heq hA).kZeroClass =
        (B.openRestrict f hf heq hB).kZeroClass) : A.kZeroClass = B.kZeroClass := by
    have hz : ((A.sum B.inverse).openRestrict f hf heq (Set.union_subset hA hB)).kZeroClass =
        0 := by
      rw [hsum A B.inverse hA hB, hinverse B hB, h, add_neg_cancel]
    have hzero := (A.sum B.inverse).kZeroClass_eq_zero_of_openRestrict
      f hf heq (Set.union_subset hA hB) hz
    rw [(equivariantSupportTripleKZero_generator_relations (G := G) (X := Y)).2.1,
      B.kZeroClass_inverse] at hzero
    exact eq_of_sub_eq_zero hzero
  -- Choose actual stable extensions; their ambient classes are independent of all choices.
  let extension (a : EquivariantSupportBundleTriple G X) :=
    Classical.choose (a.exists_openExtension f hf heq)
  have hextension (a : EquivariantSupportBundleTriple G X) :
      ∃ hc : (extension a).1.datum.control ⊆ Set.range f,
        ((extension a).openRestrict f hf heq hc).IsStablyIsomorphic a :=
    Classical.choose_spec (a.exists_openExtension f hf heq)
  let control (a : EquivariantSupportBundleTriple G X) := (hextension a).choose
  have hclass (a : EquivariantSupportBundleTriple G X) :
      ((extension a).openRestrict f hf heq (control a)).kZeroClass = a.kZeroClass :=
    EquivariantSupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic _ _
      (hextension a).choose_spec
  let value (a : EquivariantSupportBundleTriple G X) := (extension a).kZeroClass
  have hi (a b : EquivariantSupportBundleTriple G X) (h : a.IsIsomorphic b) :
      value a = value b := by
    apply hsame (extension a) (extension b) (control a) (control b)
    exact (hclass a).trans
      (((equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).1 a b h).trans
        (hclass b).symm)
  have hs (a b : EquivariantSupportBundleTriple G X) : value (a.sum b) = value a + value b := by
    have h := hsame (extension (a.sum b)) ((extension a).sum (extension b))
      (control (a.sum b)) (Set.union_subset (control a) (control b)) (by
        rw [hsum (extension a) (extension b) (control a) (control b),
          hclass, hclass, hclass]
        exact (equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).2.1 a b)
    exact h.trans
      ((equivariantSupportTripleKZero_generator_relations (G := G) (X := Y)).2.1 _ _)
  have hz (E : FiniteBundle X) (σ : EquivariantStructure G E.Fiber) :
      value (.identity E σ) = 0 := by
    apply EquivariantSupportBundleTriple.kZeroClass_eq_zero_of_openRestrict
      (extension (.identity E σ)) f hf heq (control (.identity E σ))
    exact (hclass (.identity E σ)).trans
      ((equivariantSupportTripleKZero_generator_relations (G := G) (X := X)).2.2 E σ)
  obtain ⟨Φ, hΦ, _⟩ := equivariantSupportTripleKZero_universal_property value hi hs hz
  have hcontrolled (b : EquivariantSupportBundleTriple G Y)
      (hc : b.1.datum.control ⊆ Set.range f) :
      Φ (b.openRestrict f hf heq hc).kZeroClass = b.kZeroClass := by
    rw [hΦ]
    exact hsame (extension (b.openRestrict f hf heq hc)) b
      (control (b.openRestrict f hf heq hc)) hc (hclass _)
  refine ⟨Φ, hcontrolled, ?_⟩
  intro Ψ hΨ
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective z
  rw [← hclass a, hΨ, hcontrolled]


end

/-- Open extension is the unique map characterized by the actual controlled triples. -/
def equivariantSupportTripleKZeroOpenPushforward (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G Y :=
  Classical.choose (existsUnique_equivariantSupportTripleKZeroOpenPushforward f hf heq).exists

/-- Open extension recovers any original ambient triple controlled inside the open image. -/
theorem equivariantSupportTripleKZeroOpenPushforward_class
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (b : EquivariantSupportBundleTriple G Y) (hc : b.1.datum.control ⊆ Set.range f) :
    equivariantSupportTripleKZeroOpenPushforward f hf heq
      (b.openRestrict f hf heq hc).kZeroClass = b.kZeroClass := by
  -- Read the generator equation from the exact existence witness used by the definition.
  exact (Classical.choose_spec
    (existsUnique_equivariantSupportTripleKZeroOpenPushforward f hf heq).exists) b hc

section

open scoped TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor isFiniteRank_pullback
  trivialTopology isFiniteRank_trivial

/-- Open extension preserves the full original representation-ring coefficient. -/
theorem equivariantSupportTripleKZeroOpenPushforward_smul
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (r : RepresentationGrothendieckGroup G) (a : EquivariantSupportTripleKZero G X) :
    equivariantSupportTripleKZeroOpenPushforward f hf heq (r • a) =
      r • equivariantSupportTripleKZeroOpenPushforward f hf heq a :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let μX := equivariantSupportRepresentationAction (G := G) (X := X)
  let μY := equivariantSupportRepresentationAction (G := G) (X := Y)
  let P := equivariantSupportTripleKZeroOpenPushforward f hf heq
  have hcompare (ρ : FiniteContinuousRepresentation G) (b : EquivariantSupportBundleTriple G Y)
      (hc : b.1.datum.control ⊆ Set.range f) :
      ((b.tensorRepresentation ρ).openRestrict f hf heq hc).IsIsomorphic
        ((b.openRestrict f hf heq hc).tensorRepresentation ρ) := by
    -- These comparisons preserve the tensor vector across the two native total topologies.
    let u (J : FiniteBundle Y) :
        Iso (((FiniteBundle.trivial Y ρ.dimension).tensor J).pullback f).Fiber
          ((FiniteBundle.trivial X ρ.dimension).tensor (J.pullback f)).Fiber :=
      (pullbackTensorIso (E := (FiniteBundle.trivial Y ρ.dimension).Fiber)
        (F := J.Fiber) f).trans
        ((pullbackTrivialIso f ρ.dimension).tensor (Iso.refl (J.pullback f).Fiber))
    have hu (J : FiniteBundle Y) (y : X)
        (v : (Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber (f y)) :
        (u J).linearEquiv y v = v := by
      have hlin : ((u J).linearEquiv y).toLinearMap = LinearMap.id := by
        apply TensorProduct.ext'
        intro t w
        change (pullbackTrivialIso f ρ.dimension).linearEquiv y t ⊗ₜ[ℂ] w = t ⊗ₜ[ℂ] w
        rw [pullbackTrivialIso_apply]
      exact DFunLike.congr_fun hlin v
    -- Pulling a tensor action back transports precisely the original second-factor target.
    have haction (J : FiniteBundle Y) (σ : EquivariantStructure G J.Fiber)
        (g : G) (y : X) (v : (Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber (f y)) :
        (((EquivariantStructure.ofFiniteRepresentation ρ).tensor σ).pullback f heq).linearMap
            g y v =
          ((EquivariantStructure.ofFiniteRepresentation ρ).tensor
            (σ.pullback f heq)).linearMap g y v := by
      have htransport (x z : Y) (hxz : x = z) (L : J.Fiber (f y) →ₗ[ℂ] J.Fiber z) :
          (Eq.mpr (congrArg (fun t ↦
            ((Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber (f y)) →ₗ[ℂ]
              ((Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber t)) hxz)
            (TensorProduct.map (ρ.representation g).toLinearMap L)) v =
          TensorProduct.map (ρ.representation g).toLinearMap
            (Eq.mpr (congrArg (fun t ↦ J.Fiber (f y) →ₗ[ℂ] J.Fiber t) hxz) L) v := by
        subst z
        rfl
      exact htransport (f (g • y)) (g • f y) (heq g y) (σ.linearMap g (f y))
    let L := (b.tensorRepresentation ρ).openRestrict f hf heq hc
    let R := (b.openRestrict f hf heq hc).tensorRepresentation ρ
    let K := f ⁻¹' b.1.datum.control
    have hK : IsCompact K := (b.openRestrict f hf heq hc).1.datum.isCompact_control
    have hInv (g : G) (y : X) : g • y ∈ K ↔ y ∈ K := by
      change f (g • y) ∈ b.1.datum.control ↔ f y ∈ b.1.datum.control
      rw [heq g y]
      exact b.2.isEquivariant.invariant_control g (f y)
    refine ⟨K, hK, hInv, Set.Subset.refl _, Set.Subset.refl _,
      u b.1.source, u b.1.target, ?_, ?_, ?_⟩
    · intro g y v
      exact (hu b.1.source (g • y) _).trans
        ((haction b.1.source b.2.sourceAction g y v).trans
          (congrArg (R.2.sourceAction.linearMap g y) (hu b.1.source y v)).symm)
    · intro g y v
      exact (hu b.1.target (g • y) _).trans
        ((haction b.1.target b.2.targetAction g y v).trans
          (congrArg (R.2.targetAction.linearMap g y) (hu b.1.target y v)).symm)
    · intro y v
      -- The same inverse-image compact exterior is used on both sides of the boundary square.
      have hboundary : (L.1.datum.boundary.linearEquiv y).toLinearMap =
          (R.1.datum.boundary.linearEquiv y).toLinearMap := by
        apply TensorProduct.ext'
        intro t w
        have hp := RelativeTriple.pullback_apply
          (b.1.datum.boundary.tensorLeft (FiniteBundle.trivial Y ρ.dimension).Fiber)
          f y (t ⊗ₜ[ℂ] w)
        have hl := RelativeTriple.tensorLeft_tmul
          (FiniteBundle.trivial Y ρ.dimension).Fiber b.1.datum.boundary
          ⟨f y, y.property⟩ t w
        have hr := RelativeTriple.tensorLeft_tmul
          (FiniteBundle.trivial X ρ.dimension).Fiber (b.1.datum.boundary.pullback f) y t w
        have hq := RelativeTriple.pullback_apply b.1.datum.boundary f y w
        exact (hp.trans hl).trans
          ((congrArg (fun w : b.1.target.Fiber (f y) ↦ t ⊗ₜ[ℂ] w) hq).symm.trans hr.symm)
      have hl := L.1.datum.enlarge_apply K hK (Set.Subset.refl _) y v
      have hr := R.1.datum.enlarge_apply K hK (Set.Subset.refl _) y v
      exact (hu b.1.target y _).trans
        ((hl.trans ((DFunLike.congr_fun hboundary v).trans hr.symm)).trans
          (congrArg ((R.1.datum.enlarge K hK (Set.Subset.refl _)).boundary.linearEquiv y)
            (hu b.1.source y v)).symm)
  -- Choose an actual ambient extension and retain that same tensor representative.
  have hgen (ρ : FiniteContinuousRepresentation G) (b : EquivariantSupportBundleTriple G X) :
      P (μX (finiteRepresentationClass ρ) b.kZeroClass) =
        μY (finiteRepresentationClass ρ) (P b.kZeroClass) := by
    obtain ⟨B, hB, hstable⟩ := b.exists_openExtension f hf heq
    have hb := EquivariantSupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic _ _ hstable
    rw [← hb]
    change equivariantSupportTripleKZeroOpenPushforward f hf heq
        (equivariantSupportRepresentationAction (finiteRepresentationClass ρ)
          (B.openRestrict f hf heq hB).kZeroClass) =
      equivariantSupportRepresentationAction (finiteRepresentationClass ρ)
        (equivariantSupportTripleKZeroOpenPushforward f hf heq
          (B.openRestrict f hf heq hB).kZeroClass)
    rw [equivariantSupportTripleKZeroOpenPushforward_class,
      equivariantSupportRepresentationAction_finiteClass,
      equivariantSupportRepresentationAction_finiteClass]
    have hsame := (equivariantSupportTripleKZero_generator_relations
      (G := G) (X := X)).1 _ _ (hcompare ρ B hB)
    rw [← hsame]
    exact equivariantSupportTripleKZeroOpenPushforward_class f hf heq
      (B.tensorRepresentation ρ) hB
  -- Extend through both original additive presentations, keeping the full representation class.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      P.comp (μX (finiteRepresentationClass ρ)) =
        (μY (finiteRepresentationClass ρ)).comp P := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact hgen ρ
  have h : P.comp (μX.flip a) = μY.flip (P a) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    exact DFunLike.congr_fun (hρ ρ) a
  exact DFunLike.congr_fun h r


end

/-- The linear packaging keeps the specified open-extension map as its underlying function. -/
def equivariantSupportTripleKZeroOpenLinearMap (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    EquivariantSupportTripleKZero G X →ₗ[RepresentationGrothendieckGroup G]
      EquivariantSupportTripleKZero G Y where
  toFun := equivariantSupportTripleKZeroOpenPushforward f hf heq
  map_add' := (equivariantSupportTripleKZeroOpenPushforward f hf heq).map_add
  map_smul' := equivariantSupportTripleKZeroOpenPushforward_smul f hf heq

section

attribute [local instance] isFiniteRank_pullback

/-- Forgetting agrees with the original ordinary open extension and support comparison. -/
theorem equivariantSupportTripleKZeroOpenPushforward_forget
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (a : EquivariantSupportTripleKZero G X) :
    supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget
        (equivariantSupportTripleKZeroOpenPushforward f hf heq a)) =
      compactSupportKZeroOpenPushforward f hf
        (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget a)) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  -- Choose one actual ambient extension before forgetting any of its specified actions.
  obtain ⟨b, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective a
  obtain ⟨B, hc, hstable⟩ := b.exists_openExtension f hf heq
  have hb := EquivariantSupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic _ _ hstable
  rw [← hb, equivariantSupportTripleKZeroOpenPushforward_class,
    equivariantSupportTripleKZeroForget_apply, equivariantSupportTripleKZeroForget_apply,
    supportTripleKZeroToCompactSupport_apply, supportTripleKZeroToCompactSupport_apply]
  let d := B.1.datum.openRestrict f hf hc
  have hcontrol : B.1.datum.control ⊆ f '' d.control := by
    intro y hy
    obtain ⟨x, rfl⟩ := hc hy
    exact ⟨x, hy, rfl⟩
  have hs := CompactSupportTriple.compactSupportClass_eq_openPushforward
    d B.1.datum f hf hcontrol (Iso.refl _) (Iso.refl _) (by
      intro x hx hy v
      exact RelativeTriple.pullback_apply B.1.datum.boundary f ⟨x, hx⟩ v)
  -- Ordinary excision is evaluated on these exact bundles, control and boundary maps.
  have hB := compactSupportTriple_compactSupportClass_ofBoundary
    B.1.source B.1.target B.1.datum
  have hd := compactSupportTriple_compactSupportClass_ofBoundary
    (B.1.source.pullback f) (B.1.target.pullback f) d
  exact hB.symm.trans (hs.trans (congrArg (compactSupportKZeroOpenPushforward f hf) hd))

end

variable {Z : Type*} [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
  [LocallyCompactSpace Z] [T2Space Z]

/-- Identity and composition laws for the same covariant open-extension construction. -/
theorem equivariantSupportTripleKZeroOpenPushforward_functoriality :
    equivariantSupportTripleKZeroOpenPushforward (G := G) (ContinuousMap.id X)
        IsOpenEmbedding.id (fun _ _ ↦ rfl) =
      AddMonoidHom.id (EquivariantSupportTripleKZero G X) ∧
    ∀ (f : C(X, Y)) (hf : IsOpenEmbedding f)
      (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
      (k : C(Y, Z)) (hk : IsOpenEmbedding k)
      (keq : ∀ (g : G) (y : Y), k (g • y) = g • k y),
      equivariantSupportTripleKZeroOpenPushforward (k.comp f) (hk.comp hf)
          (fun g x ↦ (congrArg k (heq g x)).trans (keq g (f x))) =
        (equivariantSupportTripleKZeroOpenPushforward k hk keq).comp
          (equivariantSupportTripleKZeroOpenPushforward f hf heq) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  -- The identity embedding uses its original proper pullback, whose fibers are unchanged.
  constructor
  · apply (existsUnique_equivariantSupportTripleKZeroOpenPushforward
      (G := G) (ContinuousMap.id X) IsOpenEmbedding.id (fun _ _ ↦ rfl)).unique
    · exact equivariantSupportTripleKZeroOpenPushforward_class _ _ _
    · intro b hc
      change (b.openRestrict (ContinuousMap.id X) IsOpenEmbedding.id
        (fun _ _ ↦ rfl) hc).kZeroClass = b.kZeroClass
      have h := equivariantSupportTripleKZeroPullback_apply (G := G)
        (ContinuousMap.id X) (fun _ _ ↦ rfl) isProperMap_id b
      rw [equivariantSupportTripleKZeroPullback_id] at h
      exact h.symm
  · -- Compare the two successive restrictions on the same inverse-image control.
    intro f hf heq k hk keq
    let compEq (g : G) (x : X) := (congrArg k (heq g x)).trans (keq g (f x))
    apply (existsUnique_equivariantSupportTripleKZeroOpenPushforward
      (k.comp f) (hk.comp hf) compEq).unique
    · exact equivariantSupportTripleKZeroOpenPushforward_class _ _ _
    · intro b hc
      have hck : b.1.datum.control ⊆ Set.range k := by
        intro z hz
        obtain ⟨x, rfl⟩ := hc hz
        exact ⟨f x, rfl⟩
      let a := b.openRestrict k hk keq hck
      have hcf : a.1.datum.control ⊆ Set.range f := by
        intro y hy
        obtain ⟨x, hx⟩ := hc hy
        exact ⟨x, hk.injective hx⟩
      let d := a.openRestrict f hf heq hcf
      let c := b.openRestrict (k.comp f) (hk.comp hf) compEq hc
      have hi : d.IsIsomorphic c := by
        let K := c.1.datum.control
        have hK : IsCompact K := c.1.datum.isCompact_control
        let u := pullbackCompIso (E := b.1.source.Fiber) k f
        let v := pullbackCompIso (E := b.1.target.Fiber) k f
        refine ⟨K, hK, c.2.isEquivariant.invariant_control, Set.Subset.rfl,
          Set.Subset.rfl, u, v,
          b.2.sourceAction.pullbackCompIso_isEquivariant k keq f heq,
          b.2.targetAction.pullbackCompIso_isEquivariant k keq f heq, ?_⟩
        intro x s
        have hl := d.1.datum.enlarge_apply K hK (Set.Subset.refl _) x s
        have hp := RelativeTriple.pullback_apply (b.1.datum.boundary.pullback k) f x s
        have hq := RelativeTriple.pullback_apply b.1.datum.boundary k ⟨f x, x.property⟩ s
        have hr := c.1.datum.enlarge_apply K hK (Set.Subset.refl _) x s
        have ht := RelativeTriple.pullback_apply b.1.datum.boundary (k.comp f) x s
        have hv := pullbackCompIso_apply (E := b.1.target.Fiber) k f x
          ((d.1.datum.enlarge K hK (Set.Subset.refl _)).boundary.linearEquiv x s)
        have hu := pullbackCompIso_apply (E := b.1.source.Fiber) k f x s
        exact hv.trans (((hl.trans (hp.trans hq)).trans (hr.trans ht).symm).trans
          (congrArg ((c.1.datum.enlarge K hK (Set.Subset.refl _)).boundary.linearEquiv x)
            hu).symm)
      have hclass := (equivariantSupportTripleKZero_generator_relations
        (G := G) (X := X)).1 d c hi
      change equivariantSupportTripleKZeroOpenPushforward k hk keq
        (equivariantSupportTripleKZeroOpenPushforward f hf heq c.kZeroClass) = b.kZeroClass
      rw [← hclass]
      exact (congrArg (equivariantSupportTripleKZeroOpenPushforward k hk keq)
        (equivariantSupportTripleKZeroOpenPushforward_class f hf heq a hcf)).trans
          (equivariantSupportTripleKZeroOpenPushforward_class k hk keq b hck)

variable {W : Type*} [TopologicalSpace W] [MulAction G W] [ContinuousSMul G W]
  [LocallyCompactSpace W] [T2Space W]

section

open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback
  tensorTopology isFiniteRank_tensor

set_option maxHeartbeats 800000 in

/-- The original external product commutes with open extension in both factors. -/
theorem equivariantSupportKZeroExternalProduct_openPushforward
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (k : C(Z, W)) (hk : IsOpenEmbedding k)
    (keq : ∀ (g : G) (z : Z), k (g • z) = g • k z)
    (a : EquivariantSupportTripleKZero G X) (b : EquivariantSupportTripleKZero G Z) :
    equivariantSupportTripleKZeroOpenPushforward (f.prodMap k) (hf.prodMap hk)
        (fun g z ↦ Prod.ext (heq g z.1) (keq g z.2))
        (equivariantSupportKZeroExternalProduct a b) =
      equivariantSupportKZeroExternalProduct
        (equivariantSupportTripleKZeroOpenPushforward f hf heq a)
        (equivariantSupportTripleKZeroOpenPushforward k hk keq b) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  have tensor_comparison (f : C(X, Y)) (k : C(Z, W))
      (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
      (keq : ∀ (g : G) (y : Z), k (g • y) = g • k y)
      (E : FiniteBundle Y) (F : FiniteBundle W)
      (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber) :
      ∃ e : Iso
        ((((E.pullback ContinuousMap.fst).tensor
          (F.pullback ContinuousMap.snd)).pullback (f.prodMap k)).Fiber)
        (((E.pullback f).pullback ContinuousMap.fst).tensor
          ((F.pullback k).pullback ContinuousMap.snd)).Fiber,
        (∀ z v, e.linearEquiv z v = v) ∧
          e.IsEquivariant
            (((ρE.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
              (ρF.pullback ContinuousMap.snd (fun _ _ ↦ rfl))).pullback (f.prodMap k)
                (fun g z ↦ Prod.ext (heq g z.1) (keq g z.2)))
            (((ρE.pullback f heq).pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
              ((ρF.pullback k keq).pullback ContinuousMap.snd (fun _ _ ↦ rfl))) := by
    let p : C(Y × W, Y) := ContinuousMap.fst
    let q : C(Y × W, W) := ContinuousMap.snd
    let p' : C(X × Z, X) := ContinuousMap.fst
    let q' : C(X × Z, Z) := ContinuousMap.snd
    let h : C(X × Z, Y × W) := f.prodMap k
    -- Compare the two actual iterated pullback topologies using the same vectors.
    let eE : Iso (((E.pullback p).pullback h).Fiber)
        (((E.pullback f).pullback p').Fiber) :=
      (pullbackCompIso (E := E.Fiber) p h).trans
        (pullbackCompIso (E := E.Fiber) f p').symm
    let eF : Iso (((F.pullback q).pullback h).Fiber)
        (((F.pullback k).pullback q').Fiber) :=
      (pullbackCompIso (E := F.Fiber) q h).trans
        (pullbackCompIso (E := F.Fiber) k q').symm
    have hE (z : X × Z) (v : E.Fiber (f z.1)) : eE.linearEquiv z v = v := by
      apply (pullbackCompIso (E := E.Fiber) f p').linearEquiv z |>.injective
      change (pullbackCompIso (E := E.Fiber) f p').linearEquiv z
        (((pullbackCompIso (E := E.Fiber) f p').linearEquiv z).symm
          ((pullbackCompIso (E := E.Fiber) p h).linearEquiv z v)) = _
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    have hF (z : X × Z) (v : F.Fiber (k z.2)) : eF.linearEquiv z v = v := by
      apply (pullbackCompIso (E := F.Fiber) k q').linearEquiv z |>.injective
      change (pullbackCompIso (E := F.Fiber) k q').linearEquiv z
        (((pullbackCompIso (E := F.Fiber) k q').linearEquiv z).symm
          ((pullbackCompIso (E := F.Fiber) q h).linearEquiv z v)) = _
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    let e := (pullbackTensorIso (E := (E.pullback p).Fiber)
      (F := (F.pullback q).Fiber) h).trans (eE.tensor eF)
    have he (z : X × Z) (v : E.Fiber (f z.1) ⊗[ℂ] F.Fiber (k z.2)) :
        e.linearEquiv z v = v := by
      change TensorProduct.congr (eE.linearEquiv z) (eF.linearEquiv z) v = v
      have hmap : (TensorProduct.congr (eE.linearEquiv z) (eF.linearEquiv z)).toLinearMap =
          LinearMap.id := by
        apply TensorProduct.ext'
        intro u w
        simp only [LinearEquiv.coe_coe, TensorProduct.congr_tmul, hE, hF]
        rfl
      exact LinearMap.congr_fun hmap v
    refine ⟨e, he, ?_⟩
    intro g z v
    change e.linearEquiv (g • z) _ =
      ((((ρE.pullback f heq).pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        ((ρF.pullback k keq).pullback ContinuousMap.snd (fun _ _ ↦ rfl))).linearMap
        g z (e.linearEquiv z v))
    rw [he, he]
    -- Split transport along the same supplied product equality into its two factors.
    have htransport (x₀ x₁ : Y) (y₀ y₁ : W) (hx : x₀ = x₁) (hy : y₀ = y₁)
        (A : E.Fiber (f z.1) →ₗ[ℂ] E.Fiber x₁)
        (B : F.Fiber (k z.2) →ₗ[ℂ] F.Fiber y₁) :
        (Eq.mpr (congrArg
          (fun w : Y × W ↦ (E.Fiber (f z.1) ⊗[ℂ] F.Fiber (k z.2)) →ₗ[ℂ]
            (E.Fiber w.1 ⊗[ℂ] F.Fiber w.2))
              (show (x₀, y₀) = (x₁, y₁) from Prod.ext hx hy)) (TensorProduct.map A B)) v =
          TensorProduct.map
            (Eq.mpr (congrArg (fun x ↦ E.Fiber (f z.1) →ₗ[ℂ] E.Fiber x) hx) A)
            (Eq.mpr (congrArg (fun y ↦ F.Fiber (k z.2) →ₗ[ℂ] F.Fiber y) hy) B) v := by
      subst x₁
      subst y₁
      rfl
    exact htransport (f (g • z.1)) (g • f z.1) (k (g • z.2)) (g • k z.2)
      (heq g z.1) (keq g z.2) (ρE.linearMap g (f z.1)) (ρF.linearMap g (k z.2))
  have sum_comparison (f : C((X × Z), (Y × W)))
      (heq : ∀ (g : G) (w : (X × Z)), f (g • w) = g • f w)
      (J K : FiniteBundle (Y × W)) (ρJ : EquivariantStructure G J.Fiber)
      (ρK : EquivariantStructure G K.Fiber) :
      ∃ e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber,
        (∀ w v, e.linearEquiv w v = v) ∧
          e.IsEquivariant ((ρJ.sum ρK).pullback f heq)
            ((ρJ.pullback f heq).sum (ρK.pullback f heq)) := by
    exact ⟨sumPullbackIso f J K, (fun _ _ ↦ rfl),
      EquivariantStructure.sumPullbackIso_isEquivariant J K ρJ ρK f heq⟩
  have hcutoffX (J K : FiniteBundle Y) (a : CompactSupportTriple J.Fiber K.Fiber)
      (f : C(X, Y)) (hf : IsOpenEmbedding f) (hc : a.control ⊆ Set.range f) (ρ : C(Y, I)) (x : X) :
      (a.openRestrict f hf hc).cutoffLinearMap (ρ.comp f) x = a.cutoffLinearMap ρ (f x) ∧
        (a.openRestrict f hf hc).inverse.cutoffLinearMap (ρ.comp f) x =
          a.inverse.cutoffLinearMap ρ (f x) := by
    classical
    by_cases hx : f x ∈ a.control
    · constructor <;>
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.openRestrict,
          CompactSupportTriple.inverse, Set.mem_preimage, hx, dite_true]
    · have hb : (a.boundary.pullback f).linearEquiv ⟨x, hx⟩ =
          a.boundary.linearEquiv ⟨f x, hx⟩ := by
        apply LinearEquiv.ext
        intro v
        exact RelativeTriple.pullback_apply a.boundary f ⟨x, hx⟩ v
      constructor <;>
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.openRestrict,
          CompactSupportTriple.inverse, Set.mem_preimage, hx, dite_false]
      · change ((ρ (f x) : ℝ) : ℂ) •
          ((a.boundary.pullback f).linearEquiv ⟨x, hx⟩).toLinearMap = _
        rw [hb]
      · change ((ρ (f x) : ℝ) : ℂ) •
          ((a.boundary.pullback f).linearEquiv ⟨x, hx⟩).symm.toLinearMap = _
        rw [hb]
        rfl
  have hcutoffY (J K : FiniteBundle W) (a : CompactSupportTriple J.Fiber K.Fiber)
      (f : C(Z, W)) (hf : IsOpenEmbedding f) (hc : a.control ⊆ Set.range f) (ρ : C(W, I)) (x : Z) :
      (a.openRestrict f hf hc).cutoffLinearMap (ρ.comp f) x = a.cutoffLinearMap ρ (f x) ∧
        (a.openRestrict f hf hc).inverse.cutoffLinearMap (ρ.comp f) x =
          a.inverse.cutoffLinearMap ρ (f x) := by
    classical
    by_cases hx : f x ∈ a.control
    · constructor <;>
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.openRestrict,
          CompactSupportTriple.inverse, Set.mem_preimage, hx, dite_true]
    · have hb : (a.boundary.pullback f).linearEquiv ⟨x, hx⟩ =
          a.boundary.linearEquiv ⟨f x, hx⟩ := by
        apply LinearEquiv.ext
        intro v
        exact RelativeTriple.pullback_apply a.boundary f ⟨x, hx⟩ v
      constructor <;>
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.openRestrict,
          CompactSupportTriple.inverse, Set.mem_preimage, hx, dite_false]
      · change ((ρ (f x) : ℝ) : ℂ) •
          ((a.boundary.pullback f).linearEquiv ⟨x, hx⟩).toLinearMap = _
        rw [hb]
      · change ((ρ (f x) : ℝ) : ℂ) •
          ((a.boundary.pullback f).linearEquiv ⟨x, hx⟩).symm.toLinearMap = _
        rw [hb]
        rfl
  -- Choose actual ambient stable extensions for both original input classes.
  obtain ⟨a₀, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective a
  obtain ⟨b₀, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective b
  obtain ⟨a, hac, hastable⟩ := a₀.exists_openExtension f hf heq
  obtain ⟨b, hbc, hbstable⟩ := b₀.exists_openExtension k hk keq
  have haclass := EquivariantSupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic _ _ hastable
  have hbclass := EquivariantSupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic _ _ hbstable
  rw [← haclass, ← hbclass,
    equivariantSupportTripleKZeroOpenPushforward_class f hf heq a hac,
    equivariantSupportTripleKZeroOpenPushforward_class k hk keq b hbc]
  -- The entire enlarged compact windows remain inside the two specified open images.
  obtain ⟨U, hU, ha, _, L, hL, _, hLrange, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
    exists_invariant_time_cutoff_in_openImage f hf heq a.1.datum.control
      a.1.datum.isCompact_control hac
  obtain ⟨V, hV, hb, _, M, hM, _, hMrange, hMinv, τ, hτinv, hτzero, hτone⟩ :=
    exists_invariant_time_cutoff_in_openImage k hk keq b.1.datum.control
      b.1.datum.isCompact_control hbc
  have hLf : IsCompact (f ⁻¹' L) := hf.isEmbedding.isInducing.isCompact_preimage' hL hLrange
  have hMk : IsCompact (k ⁻¹' M) := hk.isEmbedding.isInducing.isCompact_preimage' hM hMrange
  let h := f.prodMap k
  have hheq (g : G) (z : X × Z) : h (g • z) = g • h z :=
    Prod.ext (heq g z.1) (keq g z.2)
  have hρinv' (g : G) (x : X) : (ρ.comp f) (g • x) = (ρ.comp f) x := by
    change ρ (f (g • x)) = ρ (f x)
    rw [heq g x, hρinv]
  have hτinv' (g : G) (y : Z) : (τ.comp k) (g • y) = (τ.comp k) y := by
    change τ (k (g • y)) = τ (k y)
    rw [keq g y, hτinv]
  have hLinv' (g : G) (x : X) : g • x ∈ f ⁻¹' L ↔ x ∈ f ⁻¹' L := by
    change f (g • x) ∈ L ↔ f x ∈ L
    rw [heq g x]
    exact hLinv g (f x)
  have hMinv' (g : G) (y : Z) : g • y ∈ k ⁻¹' M ↔ y ∈ k ⁻¹' M := by
    change k (g • y) ∈ M ↔ k y ∈ M
    rw [keq g y]
    exact hMinv g (k y)
  let c := supportedEquivariantExternalProductTriple a b
    ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
    hρinv hLinv hτinv hMinv
  let ap := a.openRestrict f hf heq hac
  let bp := b.openRestrict k hk keq hbc
  let d := supportedEquivariantExternalProductTriple ap bp
    (ρ.comp f) (f ⁻¹' U) (hU.preimage f.continuous) (Set.preimage_mono ha)
    (fun x hx ↦ hρzero (f x) hx) (f ⁻¹' L) hLf
    (fun x hx ↦ hρone (f x) hx)
    (τ.comp k) (k ⁻¹' V) (hV.preimage k.continuous) (Set.preimage_mono hb)
    (fun y hy ↦ hτzero (k y) hy) (k ⁻¹' M) hMk
    (fun y hy ↦ hτone (k y) hy) hρinv' hLinv' hτinv' hMinv'
  have hcrange : c.1.datum.control ⊆ Set.range h := by
    rintro ⟨y, w⟩ ⟨hy, hw⟩
    obtain ⟨x, rfl⟩ := hLrange hy
    obtain ⟨z, rfl⟩ := hMrange hw
    exact ⟨(x, z), rfl⟩
  let cp := c.openRestrict h (hf.prodMap hk) hheq hcrange
  have hsource : equivariantSupportKZeroExternalProduct ap.kZeroClass bp.kZeroClass =
      d.kZeroClass :=
    equivariantSupportKZeroExternalProduct_class ap bp
      (ρ.comp f) (f ⁻¹' U) (hU.preimage f.continuous) (Set.preimage_mono ha)
      (fun x hx ↦ hρzero (f x) hx) (f ⁻¹' L) hLf
      (fun x hx ↦ hρone (f x) hx)
      (τ.comp k) (k ⁻¹' V) (hV.preimage k.continuous) (Set.preimage_mono hb)
      (fun y hy ↦ hτzero (k y) hy) (k ⁻¹' M) hMk
      (fun y hy ↦ hτone (k y) hy) hρinv' hLinv' hτinv' hMinv'
  have hambient : equivariantSupportKZeroExternalProduct a.kZeroClass b.kZeroClass =
      c.kZeroClass :=
    equivariantSupportKZeroExternalProduct_class a b
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
  have hi : cp.IsIsomorphic d := by
    -- The comparison uses the same four tensor factors, and each map fixes its vector.
    let J₀ := (a.1.source.pullback ContinuousMap.fst).tensor
      (b.1.source.pullback ContinuousMap.snd)
    let J₁ := (a.1.target.pullback ContinuousMap.fst).tensor
      (b.1.target.pullback ContinuousMap.snd)
    let K₀ := (a.1.target.pullback ContinuousMap.fst).tensor
      (b.1.source.pullback ContinuousMap.snd)
    let K₁ := (a.1.source.pullback ContinuousMap.fst).tensor
      (b.1.target.pullback ContinuousMap.snd)
    let σ₀ := (a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
    let σ₁ := (a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
    let θ₀ := (a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
    let θ₁ := (a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
    obtain ⟨s, hs, hsG⟩ := sum_comparison h hheq J₀ J₁ σ₀ σ₁
    obtain ⟨t, ht, htG⟩ := sum_comparison h hheq K₀ K₁ θ₀ θ₁
    obtain ⟨e₀₀, he₀₀, he₀₀G⟩ := tensor_comparison f k heq keq
      a.1.source b.1.source a.2.sourceAction b.2.sourceAction
    obtain ⟨e₁₁, he₁₁, he₁₁G⟩ := tensor_comparison f k heq keq
      a.1.target b.1.target a.2.targetAction b.2.targetAction
    obtain ⟨e₁₀, he₁₀, he₁₀G⟩ := tensor_comparison f k heq keq
      a.1.target b.1.source a.2.targetAction b.2.sourceAction
    obtain ⟨e₀₁, he₀₁, he₀₁G⟩ := tensor_comparison f k heq keq
      a.1.source b.1.target a.2.sourceAction b.2.targetAction
    let u : Iso cp.1.source.Fiber d.1.source.Fiber := s.trans (e₀₀.sum e₁₁)
    let v : Iso cp.1.target.Fiber d.1.target.Fiber := t.trans (e₁₀.sum e₀₁)
    have hu (z : X × Z) (w : cp.1.source.Fiber z) : u.linearEquiv z w = w := by
      change (e₀₀.sum e₁₁).linearEquiv z (s.linearEquiv z w) = w
      rw [hs]
      exact Prod.ext (he₀₀ z w.1) (he₁₁ z w.2)
    have hv (z : X × Z) (w : cp.1.target.Fiber z) : v.linearEquiv z w = w := by
      change (e₁₀.sum e₀₁).linearEquiv z (t.linearEquiv z w) = w
      rw [ht]
      exact Prod.ext (he₁₀ z w.1) (he₀₁ z w.2)
    let C := Set.prod (f ⁻¹' L) (k ⁻¹' M)
    have hC : IsCompact C := hLf.prod hMk
    refine ⟨C, hC, fun g z ↦ and_congr (hLinv' g z.1) (hMinv' g z.2),
      Set.Subset.refl _, Set.Subset.refl _, u, v, ?_, ?_, ?_⟩
    · intro g z w
      exact (congrArg ((e₀₀.sum e₁₁).linearEquiv (g • z)) (hsG g z w)).trans
        (Prod.ext (he₀₀G g z (s.linearEquiv z w).1) (he₁₁G g z (s.linearEquiv z w).2))
    · intro g z w
      exact (congrArg ((e₁₀.sum e₀₁).linearEquiv (g • z)) (htG g z w)).trans
        (Prod.ext (he₁₀G g z (t.linearEquiv z w).1) (he₀₁G g z (t.linearEquiv z w).2))
    · -- All four pulled cutoff maps equal the old maps at the original product image.
      intro z w
      rw [hv, hu]
      have hl := cp.1.datum.enlarge_apply C hC (Set.Subset.refl _) z w
      have hp := RelativeTriple.pullback_apply c.1.datum.boundary h z w
      have hr := d.1.datum.enlarge_apply C hC (Set.Subset.refl _) z w
      apply (hl.trans hp).trans
      apply Eq.trans _ hr.symm
      change reciprocalTensorSymbol
        (a.1.datum.cutoffLinearMap ρ (f z.val.1))
        (a.1.datum.inverse.cutoffLinearMap ρ (f z.val.1))
        (b.1.datum.cutoffLinearMap τ (k z.val.2))
        (b.1.datum.inverse.cutoffLinearMap τ (k z.val.2)) w =
          reciprocalTensorSymbol
            ((a.1.datum.openRestrict f hf hac).cutoffLinearMap (ρ.comp f) z.val.1)
            ((a.1.datum.openRestrict f hf hac).inverse.cutoffLinearMap (ρ.comp f) z.val.1)
            ((b.1.datum.openRestrict k hk hbc).cutoffLinearMap (τ.comp k) z.val.2)
            ((b.1.datum.openRestrict k hk hbc).inverse.cutoffLinearMap (τ.comp k) z.val.2) w
      obtain ⟨ha₀, ha₁⟩ := hcutoffX a.1.source a.1.target a.1.datum f hf hac ρ z.val.1
      obtain ⟨hb₀, hb₁⟩ := hcutoffY b.1.source b.1.target b.1.datum k hk hbc τ z.val.2
      rw [ha₀, ha₁, hb₀, hb₁]
      rfl
  -- The same product triple has compact control in the product image, so its
  -- controlled-generator equation supplies the required covariant extension.
  have hclass := (equivariantSupportTripleKZero_generator_relations
    (G := G) (X := X × Z)).1 cp d hi
  change equivariantSupportTripleKZeroOpenPushforward h (hf.prodMap hk) hheq
    (equivariantSupportKZeroExternalProduct ap.kZeroClass bp.kZeroClass) =
      equivariantSupportKZeroExternalProduct a.kZeroClass b.kZeroClass
  rw [hsource, hambient, ← hclass]
  exact equivariantSupportTripleKZeroOpenPushforward_class h (hf.prodMap hk) hheq c hcrange

end

end AtiyahSinger.ComplexBundle
