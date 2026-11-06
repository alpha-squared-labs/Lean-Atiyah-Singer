/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedSupportKZero
public import AtiyahSinger.Topology.PrincipalBundlePullback
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Base change of the actual associated support map

Public module ID: M1547.

The lift from the associated bundle of the original principal pullback sends
[((x,p),y)] to [p,y]. It is the second coordinate of the existing associated
pullback comparison, with the same quotient and fiber-product topologies.
Proper base change makes this lift proper whenever the original base map is
proper, without a separation or compactness assumption on the acting group.

For compact Hausdorff principal bases and a locally compact Hausdorff fiber
space, the same equivariant support triple descends compatibly with that lift.
Both sides keep the original moving-fiber actions and the same boundary maps.
The compact control on the pulled principal bundle is exactly the inverse
image of the original associated control. The resulting equality holds for
the actual additive maps on the existing equivariant support presentation.

Sources: HU IV.6 Proposition 6.3, printed p.47 / PDF p.68, gives the associated
pullback comparison; SG III.13, pp.251--253, supplies the associated K-theory
route. Proper base change and its explicit varying-family support compatibility
are project supplements. No compactness of G/P, global section, change of
quotient topology, or equivariant analytic index is asserted. The proofs below establish
geometric properness and both original compact-support class comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle

variable {G P B X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [TopologicalSpace X]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [hP : IsPrincipalBundle G projection]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- The original associated pullback lift sends [((x,p),y)] to [p,y]. -/
def associatedBundlePullbackLift (f : C(X, B)) :
    C(AssociatedBundle G (PrincipalBundlePullback f projection) Y, AssociatedBundle G P Y) where
  toFun z :=
    (associatedBundlePullbackMap (G := G) (F := Y) (projection := projection) f z).1.2
  continuous_toFun :=
    (associatedBundlePullbackMap (G := G) (F := Y) (projection := projection) f).continuous
      |>.subtype_val.snd

/-- Properness of the original base map passes to the same associated pullback lift. -/
theorem isProperMap_associatedBundlePullbackLift (f : C(X, B)) (hf : IsProperMap f) :
    IsProperMap (associatedBundlePullbackLift (G := G) (Y := Y) (projection := projection) f) := by
  /- Stage 1: use the existing associatedBundlePullbackHomeomorph. Under
  this exact homeomorphism the lift is the second projection of the subtype
  of X times the original associated space cut out by f(x)=q(z), where q is
  the original continuous associated projection. No quotient is replaced.
  Stage 2: let an ultrafilter on this subtype have second coordinate tending
  to z. Its first coordinate, composed with f, tends to q(z), by the subtype
  equation and continuity of q. Properness of f supplies x with f(x)=q(z)
  and convergence of that first-coordinate ultrafilter to x.
  Stage 3: the two coordinate convergences give convergence to (x,z) in the
  product and then to its actual subtype point. The ultrafilter criterion
  proves the second projection proper. Compose with the same homeomorphism.
  This proves proper base change for the original topologies, without T2,
  local compactness, compactness of G/P, or a global principal section. -/
  -- Work on the original fiber-product subtype before composing with its quotient comparison.
  let q := associatedBundleProjection (F := Y) hP
  let W := AssociatedBundlePullback (G := G) (F := Y) (projection := projection) f
  have hsnd : IsProperMap (fun w : W ↦ w.val.2) := by
    apply isProperMap_iff_ultrafilter.mpr
    refine ⟨continuous_subtype_val.snd, ?_⟩
    intro U z hz
    -- The subtype equation turns convergence in the second coordinate into convergence under f.
    have hbase : Filter.Tendsto (fun w : W ↦ f w.val.1) U (nhds (q z)) := by
      apply ((q.continuous.tendsto z).comp hz).congr
      intro w
      exact w.property.symm
    have hfirst : Filter.Tendsto f (Ultrafilter.map (fun w : W ↦ w.val.1) U)
        (nhds (q z)) := by
      simpa only [Ultrafilter.coe_map, Filter.tendsto_map'_iff, Function.comp_def]
        using hbase
    obtain ⟨x, hx, hlimit⟩ := hf.ultrafilter_le_nhds_of_tendsto hfirst
    have hxlimit : Filter.Tendsto (fun w : W ↦ w.val.1) U (nhds x) := hlimit
    -- The two limits belong to the same fiber product, with exactly its existing topology.
    refine ⟨⟨(x, z), hx⟩, rfl, ?_⟩
    change Filter.Tendsto id U (nhds (⟨(x, z), hx⟩ : W))
    exact tendsto_subtype_rng.mpr (hxlimit.prodMk_nhds hz)
  exact hsnd.comp
    (associatedBundlePullbackHomeomorph (G := G) (F := Y) (projection := projection) f).isProperMap

variable [CompactSpace X] [T2Space X] [CompactSpace B] [T2Space B]
  [LocallyCompactSpace Y] [T2Space Y]

/-- The same equivariant triple descends compatibly with the actual principal base change. -/
theorem associatedSupportClass_baseChange (f : C(X, B))
    (a : EquivariantSupportBundleTriple G Y) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    associatedSupportClass
        (isPrincipalBundle_pullback (G := G) (projection := projection) f) a =
      compactSupportKZeroPullback
        (associatedBundlePullbackLift (G := G) (Y := Y) (projection := projection) f)
        (isProperMap_associatedBundlePullbackLift f f.continuous.isProperMap)
        (associatedSupportClass hP a) := by
  /- Stage 1: use exactly the source and target actions carried by a.
  On the original total quotients the vector lift sends
  [((x,p),(y,v))] to [p,(y,v)]. Together with the specified base lift this
  gives a map from each pulled-principal associated vector family to the
  native pullback of the original associated family. On a common p,y its
  representative coordinates are the identity on the same original E(y).
  Thus it is a fiberwise linear bijection for the already fixed algebra.
  Stage 2: principal charts and the existing associated pullback comparison
  identify this map and its inverse continuously in the original total
  topologies. The vector-family local charts retain the original local rank;
  no continuously chosen representatives or unrelated fiber isomorphisms occur.
  Stage 3: representative membership identifies the pulled-principal control
  exactly with the inverse image of the original associated control under
  the stated lift. This set is compact by the stated properness certificate.
  On its complement both boundaries send the same v to the original a(y)v,
  so the two original vector comparisons give a commuting boundary square.
  Stage 4: conjugate through these comparisons and the specified smallBundleIso
  witnesses, using the existing independence of small model. Apply the original
  CompactSupportTriple.compactSupportClass_pullback for this exact lift and
  inverse-image control. Compact X and Hausdorff B supply properness of f;
  neither the principal space P nor its acting group is made compact. -/
  classical
  let hQ := isPrincipalBundle_pullback (G := G) (projection := projection) f
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let := associatedBundle_t2Space (Y := Y) hQ
  let := associatedBundle_locallyCompactSpace (Y := Y) hQ
  let q := associatedBundlePullbackLift (G := G) (Y := Y) (projection := projection) f
  -- Compare the two actual associated vector quotients over the same base lift.
  have comparison (E : Y → Type)
      [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
      [TopologicalSpace (Bundle.TotalSpace Unit E)] [IsFiniteRank E]
      (σ : EquivariantStructure G E) :
      letI := associatedEquivariantFiberAddCommGroup hP σ
      letI := associatedEquivariantFiberModule hP σ
      letI := associatedEquivariantTotalTopology hP σ
      letI := associatedEquivariantFiberAddCommGroup hQ σ
      letI := associatedEquivariantFiberModule hQ σ
      letI := associatedEquivariantTotalTopology hQ σ
      ∃ u : Iso (AssociatedEquivariantFiber hQ σ)
          ((q : AssociatedBundle G (PrincipalBundlePullback f projection) Y →
            AssociatedBundle G P Y) *ᵖ (AssociatedEquivariantFiber hP σ)),
        ∀ (p : PrincipalBundlePullback f projection) (y : Y)
          {z : AssociatedBundle G (PrincipalBundlePullback f projection) Y}
          (hz : associatedBundleMk G (PrincipalBundlePullback f projection) Y p y = z)
          (v : E y),
          u.linearEquiv z (associatedEquivariantFiberMk hQ σ p y hz v) =
            associatedEquivariantFiberMk hP σ p.val.2 y (congrArg q hz) v := by
    let := associatedEquivariantFiberAddCommGroup hP σ
    let := associatedEquivariantFiberModule hP σ
    let := associatedEquivariantTotalTopology hP σ
    let := associatedEquivariantFiberAddCommGroup hQ σ
    let := associatedEquivariantFiberModule hQ σ
    let := associatedEquivariantTotalTopology hQ σ
    let := isFiniteRank_associatedEquivariant hP σ
    let := isFiniteRank_associatedEquivariant hQ σ
    let := isFiniteRank_pullback (E := AssociatedEquivariantFiber hP σ) q
    let : MulAction G (Bundle.TotalSpace Unit E) := σ.toMulAction
    let : ContinuousSMul G (Bundle.TotalSpace Unit E) := ⟨σ.continuous_action⟩
    let Q := associatedBundlePullbackLift (G := G) (Y := Bundle.TotalSpace Unit E)
      (projection := projection) f
    have hproj (w : AssociatedBundle G (PrincipalBundlePullback f projection)
        (Bundle.TotalSpace Unit E)) :
        associatedEquivariantProjection σ (Q w) =
          q (associatedEquivariantProjection σ w) := by
      induction w using Quotient.inductionOn with
      | h w => rfl
    let fiberMap (z : AssociatedBundle G (PrincipalBundlePullback f projection) Y)
        (v : AssociatedEquivariantFiber hQ σ z) :
        AssociatedEquivariantFiber hP σ (q z) :=
      ⟨Q v.val, (hproj v.val).trans (congrArg q v.property)⟩
    have hformula (p : PrincipalBundlePullback f projection) (y : Y)
        {z : AssociatedBundle G (PrincipalBundlePullback f projection) Y}
        (hz : associatedBundleMk G (PrincipalBundlePullback f projection) Y p y = z)
        (v : E y) :
        fiberMap z (associatedEquivariantFiberMk hQ σ p y hz v) =
          associatedEquivariantFiberMk hP σ p.val.2 y (congrArg q hz) v := rfl
    -- One common representative makes the exact map linear and bijective.
    have hlinear (z : AssociatedBundle G (PrincipalBundlePullback f projection) Y) :
        IsLinearMap ℂ (fiberMap z) := by
      let p := (Quotient.out z).1
      let y := (Quotient.out z).2
      have hz : associatedBundleMk G (PrincipalBundlePullback f projection) Y p y = z :=
        Quotient.out_eq z
      have hE := associatedEquivariantFiberMk_isLinear hQ σ p y hz
      have hF := associatedEquivariantFiberMk_isLinear hP σ p.val.2 y (congrArg q hz)
      have hsurj := (associatedEquivariantFiberMk_bijective hQ σ p y hz).2
      constructor
      · intro u v
        obtain ⟨u₀, rfl⟩ := hsurj u
        obtain ⟨v₀, rfl⟩ := hsurj v
        rw [← hE.map_add]
        exact (hformula p y hz (u₀ + v₀)).trans ((hF.map_add u₀ v₀).trans
          (congrArg₂ (· + ·) (hformula p y hz u₀).symm (hformula p y hz v₀).symm))
      · intro c v
        obtain ⟨v₀, rfl⟩ := hsurj v
        rw [← hE.map_smul]
        exact (hformula p y hz (c • v₀)).trans ((hF.map_smul c v₀).trans
          (congrArg (c • ·) (hformula p y hz v₀).symm))
    have hbij (z : AssociatedBundle G (PrincipalBundlePullback f projection) Y) :
        Function.Bijective (fiberMap z) := by
      let p := (Quotient.out z).1
      let y := (Quotient.out z).2
      have hz : associatedBundleMk G (PrincipalBundlePullback f projection) Y p y = z :=
        Quotient.out_eq z
      have hE := associatedEquivariantFiberMk_bijective hQ σ p y hz
      have hF := associatedEquivariantFiberMk_bijective hP σ p.val.2 y (congrArg q hz)
      constructor
      · intro u v huv
        obtain ⟨u₀, rfl⟩ := hE.2 u
        obtain ⟨v₀, rfl⟩ := hE.2 v
        have hv := (hformula p y hz u₀).symm.trans (huv.trans (hformula p y hz v₀))
        exact congrArg (associatedEquivariantFiberMk hQ σ p y hz) (hF.1 hv)
      · intro v
        obtain ⟨v₀, rfl⟩ := hF.2 v
        exact ⟨associatedEquivariantFiberMk hQ σ p y hz v₀, hformula p y hz v₀⟩
    -- The native pullback topology retains the source base and original total vector.
    let HE := associatedEquivariantTotalHomeomorph hQ σ
    let HF := associatedEquivariantTotalHomeomorph hP σ
    have hcontinuous : Continuous
        (fun w : Bundle.TotalSpace Unit (AssociatedEquivariantFiber hQ σ) ↦
          (⟨w.proj, fiberMap w.proj w.snd⟩ : Bundle.TotalSpace Unit
            ((q : AssociatedBundle G (PrincipalBundlePullback f projection) Y →
              AssociatedBundle G P Y) *ᵖ (AssociatedEquivariantFiber hP σ)))) := by
      apply (inducing_pullbackTotalSpaceEmbedding Unit
        (AssociatedEquivariantFiber hP σ) q).continuous_iff.mpr
      apply (continuous_proj (E := AssociatedEquivariantFiber hQ σ)).prodMk
      have hc := HF.symm.continuous_toFun.comp (Q.continuous.comp HE.continuous_toFun)
      apply hc.congr
      intro w
      apply HF.injective
      exact HF.apply_symm_apply (Q w.snd.val)
    let u : Hom (AssociatedEquivariantFiber hQ σ)
        ((q : AssociatedBundle G (PrincipalBundlePullback f projection) Y →
          AssociatedBundle G P Y) *ᵖ (AssociatedEquivariantFiber hP σ)) :=
      { linearMap z := IsLinearMap.mk' (fiberMap z) (hlinear z)
        continuous_total := hcontinuous }
    exact ⟨u.toIso hbij, hformula⟩

  let := associatedEquivariantFiberAddCommGroup hP a.2.sourceAction
  let := associatedEquivariantFiberModule hP a.2.sourceAction
  let := associatedEquivariantTotalTopology hP a.2.sourceAction
  let := isFiniteRank_associatedEquivariant hP a.2.sourceAction
  let := associatedEquivariantFiberAddCommGroup hP a.2.targetAction
  let := associatedEquivariantFiberModule hP a.2.targetAction
  let := associatedEquivariantTotalTopology hP a.2.targetAction
  let := isFiniteRank_associatedEquivariant hP a.2.targetAction
  let := associatedEquivariantFiberAddCommGroup hQ a.2.sourceAction
  let := associatedEquivariantFiberModule hQ a.2.sourceAction
  let := associatedEquivariantTotalTopology hQ a.2.sourceAction
  let := isFiniteRank_associatedEquivariant hQ a.2.sourceAction
  let := associatedEquivariantFiberAddCommGroup hQ a.2.targetAction
  let := associatedEquivariantFiberModule hQ a.2.targetAction
  let := associatedEquivariantTotalTopology hQ a.2.targetAction
  let := isFiniteRank_associatedEquivariant hQ a.2.targetAction
  let := isFiniteRank_pullback (E := AssociatedEquivariantFiber hP a.2.sourceAction) q
  let := isFiniteRank_pullback (E := AssociatedEquivariantFiber hP a.2.targetAction) q
  obtain ⟨U, hU⟩ := comparison a.1.source.Fiber a.2.sourceAction
  obtain ⟨V, hV⟩ := comparison a.1.target.Fiber a.2.targetAction
  let d := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
    a.2.isEquivariant
  let pa := associatedSupportTriple hQ a.1.datum a.2.sourceAction a.2.targetAction
    a.2.isEquivariant
  let hq : IsProperMap q := isProperMap_associatedBundlePullbackLift f f.continuous.isProperMap
  let pb := d.pullback q hq
  -- Invariance identifies exactly the inverse image of the original compact control.
  have hcontrol : pa.control = pb.control := by
    ext z
    induction z using Quotient.inductionOn with
    | h w =>
      exact (associatedControl_mk_mem_iff a.1.datum.control
        a.2.isEquivariant.invariant_control w.1 w.2).trans
          (associatedControl_mk_mem_iff a.1.datum.control
            a.2.isEquivariant.invariant_control w.1.val.2 w.2).symm
  let L := pa.control
  have hright : pb.control ⊆ L := hcontrol.symm.subset
  have boundarySource (p : PrincipalBundlePullback f projection)
      (y : (a.1.datum.controlᶜ : Set Y))
      {z : AssociatedBundle G (PrincipalBundlePullback f projection) Y}
      (hz : associatedBundleMk G (PrincipalBundlePullback f projection) Y p y = z)
      (hout : z ∈ pa.controlᶜ) (w : a.1.source.Fiber y) :
      pa.boundary.linearEquiv ⟨z, hout⟩
          (associatedEquivariantFiberMk hQ a.2.sourceAction p y hz w) =
        associatedEquivariantFiberMk hQ a.2.targetAction p y hz
          (a.1.datum.boundary.linearEquiv y w) := by
    cases hz
    exact associatedSupportBoundary_apply hQ a.1.datum a.2.sourceAction
      a.2.targetAction a.2.isEquivariant p y w
  have boundaryOriginal (p : P) (y : (a.1.datum.controlᶜ : Set Y))
      {z : AssociatedBundle G P Y} (hz : associatedBundleMk G P Y p y = z)
      (hout : z ∈ d.controlᶜ) (w : a.1.source.Fiber y) :
      d.boundary.linearEquiv ⟨z, hout⟩
          (associatedEquivariantFiberMk hP a.2.sourceAction p y hz w) =
        associatedEquivariantFiberMk hP a.2.targetAction p y hz
          (a.1.datum.boundary.linearEquiv y w) := by
    cases hz
    exact associatedSupportBoundary_apply hP a.1.datum a.2.sourceAction
      a.2.targetAction a.2.isEquivariant p y w
  -- The exterior square applies a.1.datum.boundary to the same original fiber vector.
  have hsquare (z : (Lᶜ : Set (AssociatedBundle G (PrincipalBundlePullback f projection) Y)))
      (w : AssociatedEquivariantFiber hQ a.2.sourceAction z) :
      V.linearEquiv z
          ((pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv z w) =
        (pb.enlarge L pa.isCompact_control hright).boundary.linearEquiv z
          (U.linearEquiv z w) := by
    let p := (Quotient.out z.val).1
    let y := (Quotient.out z.val).2
    have hz : associatedBundleMk G (PrincipalBundlePullback f projection) Y p y = z.val :=
      Quotient.out_eq z.val
    have hy : y ∈ a.1.datum.controlᶜ := by
      intro hy
      exact z.property (hz ▸ (associatedControl_mk_mem_iff a.1.datum.control
        a.2.isEquivariant.invariant_control p y).mpr hy)
    let ya : (a.1.datum.controlᶜ : Set Y) := ⟨y, hy⟩
    let zb : (pb.controlᶜ : Set (AssociatedBundle G (PrincipalBundlePullback f projection) Y)) :=
      ⟨z, fun h ↦ z.property (hright h)⟩
    let zd : (d.controlᶜ : Set (AssociatedBundle G P Y)) := ⟨q z, zb.property⟩
    obtain ⟨w₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective hQ a.2.sourceAction p y hz).2 w
    have hpa := boundarySource p ya hz z.property w₀
    have hda := boundaryOriginal p.val.2 ya (congrArg q hz) zd.property w₀
    have hpb := RelativeTriple.pullback_apply d.boundary q zb
      (associatedEquivariantFiberMk hP a.2.sourceAction p.val.2 y (congrArg q hz) w₀)
    rw [pa.enlarge_apply L pa.isCompact_control (Set.Subset.refl _) z _,
      pb.enlarge_apply L pa.isCompact_control hright z _]
    exact (congrArg (V.linearEquiv z) hpa).trans
      ((hV p y hz (a.1.datum.boundary.linearEquiv ya w₀)).trans
        (hda.symm.trans (hpb.symm.trans
          (congrArg (pb.boundary.linearEquiv zb) (hU p y hz w₀).symm))))
  -- Conjugate this exact square, then use the original small-model proper-pullback law.
  have htriple : (pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).congr U V =
      pb.enlarge L pa.isCompact_control hright := by
    change CompactSupportTriple.mk L pa.isCompact_control _ =
      CompactSupportTriple.mk L pa.isCompact_control _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro w
    change V.linearEquiv z
      ((pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv z
        (U.symm.linearEquiv z w)) =
      (pb.enlarge L pa.isCompact_control hright).boundary.linearEquiv z w
    exact (hsquare z (U.symm.linearEquiv z w)).trans
      (congrArg ((pb.enlarge L pa.isCompact_control hright).boundary.linearEquiv z)
        ((U.linearEquiv z).apply_symm_apply w))
  change pa.compactSupportClass = compactSupportKZeroPullback q hq d.compactSupportClass
  calc
    pa.compactSupportClass =
        (pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).compactSupportClass :=
      (pa.compactSupportClass_enlarge L pa.isCompact_control (Set.Subset.refl _)).symm
    _ =
        ((pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).congr U V).compactSupportClass :=
      ((pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).compactSupportClass_congr U V).symm
    _ = (pb.enlarge L pa.isCompact_control hright).compactSupportClass := congrArg _ htriple
    _ = pb.compactSupportClass := pb.compactSupportClass_enlarge L pa.isCompact_control hright
    _ = compactSupportKZeroPullback q hq d.compactSupportClass :=
      d.compactSupportClass_pullback q hq

/-- The actual associated support homomorphism commutes with the same proper base change. -/
theorem associatedSupportKZero_baseChange (f : C(X, B)) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    associatedSupportKZero
        (isPrincipalBundle_pullback (G := G) (projection := projection) f) =
      (compactSupportKZeroPullback
        (associatedBundlePullbackLift (G := G) (Y := Y) (projection := projection) f)
        (isProperMap_associatedBundlePullbackLift f f.continuous.isProperMap)).comp
        (associatedSupportKZero hP) := by
  /- Stage 1: evaluate the two additive homomorphisms at each original
  equivariant support-triple generator. Their prescribed generator formulas
  reduce the equality to associatedSupportClass_baseChange for that same a.
  Stage 2: use uniqueness in the original support-presentation universal
  property. Its isomorphism, direct-sum and arbitrary-bundle identity relations
  are unchanged. This yields equality on all original virtual classes, with
  the same principal pullback, actual lift and proper K pullback on the right. -/
  let hQ := isPrincipalBundle_pullback (G := G) (projection := projection) f
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let := associatedBundle_t2Space (Y := Y) hQ
  let := associatedBundle_locallyCompactSpace (Y := Y) hQ
  -- Evaluate the two original quotient homomorphisms on the same free generators.
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change associatedSupportKZero hQ a.kZeroClass =
    compactSupportKZeroPullback
      (associatedBundlePullbackLift (G := G) (Y := Y) (projection := projection) f)
      (isProperMap_associatedBundlePullbackLift f f.continuous.isProperMap)
      (associatedSupportKZero hP a.kZeroClass)
  rw [associatedSupportKZero_class, associatedSupportKZero_class]
  exact associatedSupportClass_baseChange f a

end AtiyahSinger
