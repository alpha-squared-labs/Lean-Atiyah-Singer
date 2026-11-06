/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedKZero
public import AtiyahSinger.Topology.AssociatedSupportKZero
public import AtiyahSinger.Topology.CompactSupportModule
public import AtiyahSinger.Topology.EquivariantRepresentationAction
public import AtiyahSinger.Topology.SupportTensorAction

/-!
# Representation coefficients under the actual associated support map

Public module ID: M1548.

The specified associated descent sends the full representation-ring action
to the existing ordinary K(B) action through the same associated representation
bundle. The action on the associated total base is the original graph action
along its original projection to B. That projection need not be proper.

Source: SG III.13, especially the associated representation construction
(13.17), with the tensor and graph product of Appendix C.1. The explicit
support-presentation compatibility is a project supplement. Both associated
constructions use the same principal point in each fiber. The tensor boundary
is identity tensor the original boundary; comparison with the existing product
uses a common compact enlargement and KA II.5.14 on a compact window. The
coefficient is not replaced by its dimension. No compactness of G or P, global
principal section, or equivariant analytic index statement is required.
The original same-point tensor comparison and both additive descents are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [CompactSpace B] [T2Space B] [LocallyCompactSpace Y] [T2Space Y]

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant associatedVectorFiberAddCommGroup
  associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology isFiniteRank_tensor isFiniteRank_pullback trivialTopology isFiniteRank_trivial

set_option maxHeartbeats 3200000 in

set_option backward.isDefEq.respectTransparency false in
/-- Associated descent carries the full representation coefficient to its associated K(B) class. -/
theorem associatedSupportKZero_smul (hP : IsPrincipalBundle G projection)
    (r : RepresentationGrothendieckGroup G) (a : EquivariantSupportTripleKZero G Y) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    associatedSupportKZero hP (r • a) =
      complexKZeroCompactSupportAction (associatedBundleProjection (F := Y) hP)
        (associatedRepresentationKZero hP r) (associatedSupportKZero hP a) := by
  /- Fix a representation ρ and an equivariant support triple b. At the same
  principal representative p, compare the descended ρ ⊗ E fiber with
  the descended E fiber tensored on the right by the pullback of its
  associated representation bundle. The formula swaps the two ordinary
  complex factors, so it introduces no grading sign.
  Covariance moves both vectors by the same orbit element. The explicit
  tensor/pullback maps on P × Y prove continuity before quotient descent;
  the finite-rank criterion supplies the inverse of this fiber equivalence.
  Apply the comparison to both bundles. Their original exterior formulas
  give a.congr u v = d.tensorRight W, with the same compact control.
  The existing compactSupportClass_tensorRight_pullback identity identifies
  this class with the absolute K(B) graph action along q. Properness of q
  itself is not required.
  Finally extend the generator identity through the support presentation
  and the representation presentation, using their additive quotient maps. -/

  classical
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let Z := AssociatedBundle G P Y
  let q := associatedBundleProjection (F := Y) hP
  let μ := equivariantSupportRepresentationAction (G := G) (X := Y)
  let P₀ := associatedSupportKZero (Y := Y) hP
  let R := associatedRepresentationKZero hP
  let ν := complexKZeroCompactSupportAction q
  let descend (b : EquivariantSupportBundleTriple G Y) :=
    associatedSupportTriple hP b.1.datum b.2.sourceAction b.2.targetAction b.2.isEquivariant
  -- The selected descended boundary retains its original value at every representative.
  have boundary (b : EquivariantSupportBundleTriple G Y) (p : P)
      (y : (b.1.datum.controlᶜ : Set Y)) {z : Z}
      (hz : associatedBundleMk G P Y p y = z) (hout : z ∈ (descend b).controlᶜ)
      (w : b.1.source.Fiber y) :
      (descend b).boundary.linearEquiv ⟨z, hout⟩
          (associatedEquivariantFiberMk hP b.2.sourceAction p y hz w) =
        associatedEquivariantFiberMk hP b.2.targetAction p y hz
          (b.1.datum.boundary.linearEquiv y w) := by
    cases hz
    exact associatedSupportBoundary_apply hP b.1.datum b.2.sourceAction b.2.targetAction
      b.2.isEquivariant p y w
  -- Phase 1: retain one actual representation and one original support triple.
  have hgen (ρ : FiniteContinuousRepresentation G) (b : EquivariantSupportBundleTriple G Y) :
      P₀ (μ (finiteRepresentationClass ρ) b.kZeroClass) =
        ν (R (finiteRepresentationClass ρ)) (P₀ b.kZeroClass) := by
    change associatedSupportKZero hP
        (equivariantSupportRepresentationAction (finiteRepresentationClass ρ) b.kZeroClass) =
      complexKZeroCompactSupportAction q
        (associatedRepresentationKZero hP (finiteRepresentationClass ρ))
        (associatedSupportKZero hP b.kZeroClass)
    rw [equivariantSupportRepresentationAction_finiteClass, associatedSupportKZero_class,
      associatedSupportKZero_class, associatedRepresentationKZero_finiteClass]
    let V := AssociatedVectorFiber hP ρ.representation
    let : IsFiniteRank V :=
      isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
    -- Compare the original tensor quotient with right tensoring by the same coefficient bundle.
    have comparison (J : FiniteBundle Y)
        (σ : EquivariantStructure G J.Fiber) :
        letI := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
        ∃ e : Iso
            (AssociatedEquivariantFiber hP
              ((EquivariantStructure.ofFiniteRepresentation ρ).tensor σ))
            (fun z : AssociatedBundle G P Y ↦ AssociatedEquivariantFiber hP σ z ⊗[ℂ]
              (((associatedBundleProjection (F := Y) hP : AssociatedBundle G P Y → B) *ᵖ
                (AssociatedVectorFiber hP ρ.representation)) z)),
          ∀ (p : P) (y : Y) {z : AssociatedBundle G P Y}
            (hz : associatedBundleMk G P Y p y = z) (u : Fin ρ.dimension → ℂ) (v : J.Fiber y),
            e.linearEquiv z (associatedEquivariantFiberMk hP
              ((EquivariantStructure.ofFiniteRepresentation ρ).tensor σ) p y hz (u ⊗ₜ[ℂ] v)) =
                associatedEquivariantFiberMk hP σ p y hz v ⊗ₜ[ℂ]
                  associatedVectorFiberMk hP ρ.representation p
                    (congrArg (associatedBundleProjection (F := Y) hP) hz) u := by
      classical
      let Z := AssociatedBundle G P Y
      let q := associatedBundleProjection (F := Y) hP
      let V := AssociatedVectorFiber hP ρ.representation
      let : IsFiniteRank V :=
        isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
      let τ : EquivariantStructure G ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber :=
        (EquivariantStructure.ofFiniteRepresentation ρ).tensor σ
      let A := AssociatedEquivariantFiber hP σ
      let T := AssociatedEquivariantFiber hP τ
      let W := (q : Z → B) *ᵖ V
      let mk (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z) :=
        LinearEquiv.ofBijective
          (IsLinearMap.mk' (associatedEquivariantFiberMk hP σ p y hz)
            (associatedEquivariantFiberMk_isLinear hP σ p y hz))
          (associatedEquivariantFiberMk_bijective hP σ p y hz)
      let mkT (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z) :=
        LinearEquiv.ofBijective
          (IsLinearMap.mk' (associatedEquivariantFiberMk hP τ p y hz)
            (associatedEquivariantFiberMk_isLinear hP τ p y hz))
          (associatedEquivariantFiberMk_bijective hP τ p y hz)
      have hp (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z) :
          projection p = q z := congrArg q hz
      let mkV (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z) :=
        associatedVectorFiberMkLinearEquiv hP ρ.representation p (hp p y hz)
      -- This pointwise choice is algebraic; the next formula removes it from the map.
      let c (z : Z) : T z ≃ₗ[ℂ] A z ⊗[ℂ] W z :=
        (mkT (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z)).symm.trans
          ((TensorProduct.comm ℂ _ _).trans
            (TensorProduct.congr
              (mk (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z))
              (mkV (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z))))
      have formula (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z)
          (u : Fin ρ.dimension → ℂ) (v : J.Fiber y) :
          c z (associatedEquivariantFiberMk hP τ p y hz (u ⊗ₜ[ℂ] v)) =
            associatedEquivariantFiberMk hP σ p y hz v ⊗ₜ[ℂ]
              associatedVectorFiberMk hP ρ.representation p (hp p y hz) u := by
        let : MulAction G (TotalSpace Unit J.Fiber) := σ.toMulAction
        let : MulAction G (TotalSpace Unit ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber) :=
          τ.toMulAction
        let : MulAction G (Fin ρ.dimension → ℂ) := associatedRepresentationAction ρ.representation
        -- One orbit element moves the two vectors and their common principal point simultaneously.
        obtain ⟨g, hg⟩ := Quotient.exact (hz.trans (Quotient.out_eq z).symm)
        have hprincipal : (Quotient.out z).1 = MulOpposite.op g • p := congrArg Prod.fst hg
        have hy : g⁻¹ • y = (Quotient.out z).2 := (congrArg Prod.snd hg).symm
        let v' := cast (congrArg J.Fiber hy) (σ.linearMap g⁻¹ y v)
        have hcast {y₀ y₁ : Y} (h : y₀ = y₁) (u : Fin ρ.dimension → ℂ)
            (w : J.Fiber y₀) :
            (⟨y₁, u ⊗ₜ[ℂ] cast (congrArg J.Fiber h) w⟩ :
              TotalSpace Unit ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber) =
              ⟨y₀, u ⊗ₜ[ℂ] w⟩ := by
          subst y₁
          rfl
        have hT : associatedEquivariantFiberMk hP τ p y hz (u ⊗ₜ[ℂ] v) =
            mkT (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z)
              (ρ.representation g⁻¹ u ⊗ₜ[ℂ] v') := by
          apply Subtype.ext
          apply Quotient.sound
          refine ⟨g, Prod.ext hprincipal ?_⟩
          change (⟨(Quotient.out z).2, ρ.representation g⁻¹ u ⊗ₜ[ℂ] v'⟩ :
            TotalSpace Unit ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber) =
              ⟨g⁻¹ • y,
                TensorProduct.map (ρ.representation g⁻¹).toLinearMap (σ.linearMap g⁻¹ y)
                  (u ⊗ₜ[ℂ] v)⟩
          rw [TensorProduct.map_tmul]
          exact hcast hy (ρ.representation g⁻¹ u) (σ.linearMap g⁻¹ y v)
        have hE : associatedEquivariantFiberMk hP σ p y hz v =
            mk (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z) v' := by
          apply Subtype.ext
          apply Quotient.sound
          exact ⟨g, Prod.ext hprincipal (TotalSpace.mk_cast (F := Unit) (E := J.Fiber)
            hy (σ.linearMap g⁻¹ y v))⟩
        have hV : associatedVectorFiberMk hP ρ.representation p (hp p y hz) u =
            mkV (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z)
              (ρ.representation g⁻¹ u) := by
          apply Subtype.ext
          apply Quotient.sound
          exact ⟨g, Prod.ext hprincipal rfl⟩
        rw [hT, hE, hV]
        change TensorProduct.congr _ _
          (TensorProduct.comm ℂ _ _ ((mkT _ _ _).symm ((mkT _ _ _) _))) = _
        rw [LinearEquiv.symm_apply_apply, TensorProduct.comm_tmul, TensorProduct.congr_tmul]
        rfl
      -- On P × Y use genuine tensor and pullback maps, before descending through the quotient.
      let s : C(P × Y, Y) := ContinuousMap.snd
      let m : C(P × Y, Z) := ⟨fun z ↦ associatedBundleMk G P Y z.1 z.2, continuous_quot_mk⟩
      let uV : Hom ((s : P × Y → Y) *ᵖ (FiniteBundle.trivial Y ρ.dimension).Fiber)
          ((m : P × Y → Z) *ᵖ W) :=
        { linearMap z := (mkV z.1 z.2 rfl).toLinearMap
          continuous_total := by
            let D := TotalSpace Unit
              ((s : P × Y → Y) *ᵖ (FiniteBundle.trivial Y ρ.dimension).Fiber)
            have hb : Continuous (fun z : D ↦ z.proj) :=
              Pullback.continuous_proj Unit _ s
            have ht : Continuous (fun z : TotalSpace Unit
                (FiniteBundle.trivial Y ρ.dimension).Fiber ↦ (z.proj, z.snd)) :=
              continuous_induced_dom
            have hv : Continuous (fun z : D ↦ z.snd) :=
              ht.snd.comp (Pullback.continuous_lift Unit _ s)
            have hmk : Continuous (fun z : P × (Fin ρ.dimension → ℂ) ↦
                (⟨projection z.1, associatedVectorFiberMk hP ρ.representation z.1 rfl z.2⟩ :
                  TotalSpace Unit V)) :=
              (associatedVectorTotalHomeomorph hP ρ.representation).symm.continuous.comp
                continuous_quot_mk
            rw [(inducing_pullbackTotalSpaceEmbedding Unit W (m : P × Y → Z)).continuous_iff]
            apply hb.prodMk
            rw [(inducing_pullbackTotalSpaceEmbedding Unit V (q : Z → B)).continuous_iff]
            exact (m.continuous.comp hb).prodMk (hmk.comp (hb.fst.prodMk hv)) }
      let uE : Hom ((s : P × Y → Y) *ᵖ J.Fiber) ((m : P × Y → Z) *ᵖ A) :=
        { linearMap z := (mk z.1 z.2 rfl).toLinearMap
          continuous_total := by
            let D := TotalSpace Unit ((s : P × Y → Y) *ᵖ J.Fiber)
            have hb : Continuous (fun z : D ↦ z.proj) :=
              Pullback.continuous_proj Unit _ s
            have hl : Continuous (fun z : D ↦ (⟨z.proj.2, z.snd⟩ : TotalSpace Unit J.Fiber)) :=
              Pullback.continuous_lift Unit _ s
            have hc := (associatedEquivariantTotalHomeomorph hP σ).symm.continuous.comp
              (continuous_quot_mk.comp (hb.fst.prodMk hl))
            rw [(inducing_pullbackTotalSpaceEmbedding Unit A (m : P × Y → Z)).continuous_iff]
            exact hb.prodMk hc }
      -- Interchange only ordinary complex factors; there is no graded sign.
      let flip : Hom (fun z : Z ↦ W z ⊗[ℂ] A z) (fun z : Z ↦ A z ⊗[ℂ] W z) :=
        { linearMap z := (TensorProduct.comm ℂ (W z) (A z)).toLinearMap
          continuous_total := by
            apply continuous_iSup_dom.mpr
            intro k
            apply continuous_coinduced_dom.mpr
            let D := TotalSpace Unit (fun z : Z ↦ (Fin k → W z) × (Fin k → A z))
            let D' := TotalSpace Unit (fun z : Z ↦ (Fin k → A z) × (Fin k → W z))
            let : TopologicalSpace D := TopologicalSpace.induced
              (fun z : D ↦ (z.proj,
                (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit W)),
                (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit A)))) inferInstance
            let : TopologicalSpace D' := TopologicalSpace.induced
              (fun z : D' ↦ (z.proj,
                (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
                (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit W)))) inferInstance
            have hd : Continuous (fun z : D ↦ (z.proj,
                (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit W)),
                (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit A)))) := continuous_induced_dom
            let swap (z : D) : D' := ⟨z.proj, z.snd.2, z.snd.1⟩
            have hs : Continuous swap :=
              continuous_induced_rng.mpr (hd.fst.prodMk (hd.snd.snd.prodMk hd.snd.fst))
            have hg : Continuous (fun z : D' ↦
                (⟨z.proj, ∑ i : Fin k, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
                  TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] W z))) :=
              continuous_iSup_rng (i := k) continuous_coinduced_rng
            apply (hg.comp hs).congr
            intro z
            simp only [Function.comp_apply, swap, map_sum]
            rfl }
      let liftMap := (flip.pullback m).comp
        ((pullbackTensorIso (E := W) (F := A) m).symm.toHom.comp
          ((uV.tensor uE).comp
            (pullbackTensorIso (E := (FiniteBundle.trivial Y ρ.dimension).Fiber)
              (F := J.Fiber) s).toHom))
      have liftFormula (p : P) (y : Y) (t : (Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber y) :
          liftMap.linearMap (p, y) t = c (associatedBundleMk G P Y p y)
            (associatedEquivariantFiberMk hP τ p y rfl t) := by
        change liftMap.linearMap (p, y) t = c (associatedBundleMk G P Y p y)
          (mkT p y rfl t)
        induction t using TensorProduct.inductionOn with
        | tmul u v => exact (formula p y rfl u v).symm
        | add t w ht hw => simp only [map_add, ht, hw]
      have hc : Continuous (fun d : P × TotalSpace Unit
            ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber ↦
          (⟨associatedBundleMk G P Y d.1 d.2.proj,
            c (associatedBundleMk G P Y d.1 d.2.proj)
              (associatedEquivariantFiberMk hP τ d.1 d.2.proj rfl d.2.snd)⟩ :
            TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] W z))) := by
        let D := P × TotalSpace Unit ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber
        let intoPullback (d : D) : TotalSpace Unit
            ((s : P × Y → Y) *ᵖ ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber) :=
          ⟨(d.1, d.2.proj), d.2.snd⟩
        have hi : Continuous intoPullback := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit
            ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber (s : P × Y → Y)).continuous_iff]
          exact (continuous_fst.prodMk ((continuous_proj (E :=
            ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber)).comp continuous_snd)).prodMk
              continuous_snd
        have hl := (Pullback.continuous_lift Unit
          (fun z : Z ↦ A z ⊗[ℂ] W z) (m : P × Y → Z)).comp
          (liftMap.continuous_total.comp hi)
        apply hl.congr
        intro d
        exact congrArg (fun w ↦
          (⟨associatedBundleMk G P Y d.1 d.2.proj, w⟩ :
            TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] W z))) (liftFormula d.1 d.2.proj d.2.snd)
      let a : Hom T (fun z : Z ↦ A z ⊗[ℂ] W z) :=
        { linearMap z := (c z).toLinearMap
          continuous_total := by
            -- The representative formula factors the continuous map through the original quotient.
            let : MulAction G
                (TotalSpace Unit ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber) :=
              τ.toMulAction
            let : ContinuousSMul G
                (TotalSpace Unit ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber) :=
              ⟨τ.continuous_action⟩
            let H := associatedEquivariantTotalHomeomorph hP τ
            have hquot : Continuous (fun z : AssociatedBundle G P
                (TotalSpace Unit ((FiniteBundle.trivial Y ρ.dimension).tensor J).Fiber) ↦
                (⟨(H.symm z).proj, c (H.symm z).proj (H.symm z).snd⟩ :
                  TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] W z))) := by
              apply isQuotientMap_quotient_mk'.continuous_iff.mpr
              exact hc
            apply (hquot.comp H.continuous).congr
            intro z
            exact congrArg (fun w : TotalSpace Unit T ↦
              (⟨w.proj, c w.proj w.snd⟩ :
                TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] W z))) (H.symm_apply_apply z) }
      -- The finite-rank inverse theorem applies to this same fiberwise equivalence.
      let e := a.toIso (fun z ↦ (c z).bijective)
      have he (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z)
          (u : Fin ρ.dimension → ℂ) (v : J.Fiber y) :
          e.linearEquiv z (associatedEquivariantFiberMk hP τ p y hz (u ⊗ₜ[ℂ] v)) =
            associatedEquivariantFiberMk hP σ p y hz v ⊗ₜ[ℂ]
              associatedVectorFiberMk hP ρ.representation p (hp p y hz) u :=
        formula p y hz u v
      exact ⟨e, he⟩
    obtain ⟨u, hu⟩ := comparison b.1.source b.2.sourceAction
    obtain ⟨v, hv⟩ := comparison b.1.target b.2.targetAction
    let a := descend (b.tensorRepresentation ρ)
    let d := descend b
    let W := (q : Z → B) *ᵖ V
    let dR := d.tensorRight W
    -- Phase 2: the same compact exterior carries exactly the original boundary square.
    have hsquare (z : (d.controlᶜ : Set Z))
        (w : AssociatedEquivariantFiber hP
          ((EquivariantStructure.ofFiniteRepresentation ρ).tensor b.2.sourceAction) z) :
        v.linearEquiv z (a.boundary.linearEquiv ⟨z.val, z.property⟩ w) =
          dR.boundary.linearEquiv ⟨z.val, z.property⟩ (u.linearEquiv z w) := by
      let p := (Quotient.out z.val).1
      let y := (Quotient.out z.val).2
      have hz : associatedBundleMk G P Y p y = z.val := Quotient.out_eq z.val
      have hy : y ∈ b.1.datum.controlᶜ := by
        intro hy
        apply z.property
        rw [← hz]
        exact (associatedControl_mk_mem_iff b.1.datum.control
          b.2.isEquivariant.invariant_control p y).mpr hy
      let y' : (b.1.datum.controlᶜ : Set Y) := ⟨y, hy⟩
      let τ := (EquivariantStructure.ofFiniteRepresentation ρ).tensor b.2.sourceAction
      let mkT := IsLinearMap.mk'
        (associatedEquivariantFiberMk hP τ p y hz)
        (associatedEquivariantFiberMk_isLinear hP τ p y hz)
      have hm : (v.linearEquiv z).toLinearMap.comp
            ((a.boundary.linearEquiv ⟨z.val, z.property⟩).toLinearMap.comp mkT) =
          (dR.boundary.linearEquiv ⟨z.val, z.property⟩).toLinearMap.comp
            ((u.linearEquiv z).toLinearMap.comp mkT) := by
        apply TensorProduct.ext'
        intro s w
        change v.linearEquiv z
            (a.boundary.linearEquiv ⟨z.val, z.property⟩
              (associatedEquivariantFiberMk hP τ p y hz (s ⊗ₜ[ℂ] w))) =
          dR.boundary.linearEquiv ⟨z.val, z.property⟩
            (u.linearEquiv z (associatedEquivariantFiberMk hP τ p y hz (s ⊗ₜ[ℂ] w)))
        have hl := boundary (b.tensorRepresentation ρ) p y' hz z.property (s ⊗ₜ[ℂ] w)
        have ht := RelativeTriple.tensorLeft_tmul
          (FiniteBundle.trivial Y ρ.dimension).Fiber b.1.datum.boundary y' s w
        have hinner : a.boundary.linearEquiv ⟨z.val, z.property⟩
              (associatedEquivariantFiberMk hP τ p y hz (s ⊗ₜ[ℂ] w)) =
            associatedEquivariantFiberMk hP
              ((EquivariantStructure.ofFiniteRepresentation ρ).tensor b.2.targetAction)
              p y hz (s ⊗ₜ[ℂ] b.1.datum.boundary.linearEquiv y' w) :=
          hl.trans (congrArg (associatedEquivariantFiberMk hP
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor b.2.targetAction)
            p y hz) ht)
        have hright : dR.boundary.linearEquiv ⟨z.val, z.property⟩
              (associatedEquivariantFiberMk hP b.2.sourceAction p y hz w ⊗ₜ[ℂ]
                associatedVectorFiberMk hP ρ.representation p (congrArg q hz) s) =
            d.boundary.linearEquiv z
                (associatedEquivariantFiberMk hP b.2.sourceAction p y hz w) ⊗ₜ[ℂ]
              associatedVectorFiberMk hP ρ.representation p (congrArg q hz) s :=
          TensorProduct.congr_tmul (d.boundary.linearEquiv z)
            (LinearEquiv.refl ℂ (W z)) _ _
        have hd := boundary b p y' hz z.property w
        calc
          _ = v.linearEquiv z (associatedEquivariantFiberMk hP
              ((EquivariantStructure.ofFiniteRepresentation ρ).tensor b.2.targetAction)
              p y hz (s ⊗ₜ[ℂ] b.1.datum.boundary.linearEquiv y' w)) :=
            congrArg (v.linearEquiv z) hinner
          _ = associatedEquivariantFiberMk hP b.2.targetAction p y hz
                (b.1.datum.boundary.linearEquiv y' w) ⊗ₜ[ℂ]
              associatedVectorFiberMk hP ρ.representation p (congrArg q hz) s :=
            hv p y hz s (b.1.datum.boundary.linearEquiv y' w)
          _ = d.boundary.linearEquiv z
                (associatedEquivariantFiberMk hP b.2.sourceAction p y hz w) ⊗ₜ[ℂ]
              associatedVectorFiberMk hP ρ.representation p (congrArg q hz) s :=
            congrArg (fun t ↦ t ⊗ₜ[ℂ]
              associatedVectorFiberMk hP ρ.representation p (congrArg q hz) s) hd.symm
          _ = dR.boundary.linearEquiv ⟨z.val, z.property⟩
              (associatedEquivariantFiberMk hP b.2.sourceAction p y hz w ⊗ₜ[ℂ]
                associatedVectorFiberMk hP ρ.representation p (congrArg q hz) s) :=
            hright.symm
          _ = _ := congrArg (dR.boundary.linearEquiv ⟨z.val, z.property⟩) (hu p y hz s w).symm
      obtain ⟨t, rfl⟩ := (associatedEquivariantFiberMk_bijective hP τ p y hz).2 w
      exact DFunLike.congr_fun hm t
    have heq : a.congr u v = dR := by
      change CompactSupportTriple.mk d.control _ _ = CompactSupportTriple.mk d.control _ _
      congr 1
      apply Iso.ext
      intro z
      apply LinearEquiv.ext
      intro w
      change v.linearEquiv z
          (a.boundary.linearEquiv ⟨z.val, z.property⟩ (u.symm.linearEquiv z w)) =
        dR.boundary.linearEquiv ⟨z.val, z.property⟩ w
      exact (hsquare z (u.symm.linearEquiv z w)).trans
        (congrArg (dR.boundary.linearEquiv ⟨z.val, z.property⟩)
          ((u.linearEquiv z).apply_symm_apply w))
    -- Phase 3: the established actual tensor formula supplies the specified graph action.
    calc
      associatedSupportClass hP (b.tensorRepresentation ρ) = a.compactSupportClass := rfl
      _ = (a.congr u v).compactSupportClass := (a.compactSupportClass_congr u v).symm
      _ = dR.compactSupportClass := congrArg CompactSupportTriple.compactSupportClass heq
      _ = complexKZeroCompactSupportAction q (ComplexBundle.kZeroClass V) d.compactSupportClass :=
        d.compactSupportClass_tensorRight_pullback V q
      _ = complexKZeroCompactSupportAction q (associatedKZeroClass hP ρ)
          (associatedSupportClass hP b) := rfl
  -- Phase 4: descend through the two original additive presentations.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      P₀.comp (μ (finiteRepresentationClass ρ)) =
        (ν (R (finiteRepresentationClass ρ))).comp P₀ := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact hgen ρ
  have h : P₀.comp (μ.flip a) = (ν.flip (P₀ a)).comp R.toAddMonoidHom := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    exact DFunLike.congr_fun (hρ ρ) a
  exact DFunLike.congr_fun h r

end AtiyahSinger
