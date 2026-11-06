/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Geometry.EquivariantRelativeCotangentRadial
public import AtiyahSinger.Topology.EquivariantCotangentBaseFlattening
public import AtiyahSinger.Geometry.InvariantCotangentMetric
public import AtiyahSinger.Topology.EquivariantBundleHomotopy
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import AtiyahSinger.Topology.SupportTripleTransport

import AtiyahSinger.Topology.RealBundleSupport

/-!
# Relative homogeneous representatives of the original equivariant support triple

Public module ID: M1803.

The actual zero-section bundle comparisons, an invariant base cutoff and the
relative radial homotopy produce a homogeneous projection-pullback triple.
Its control is the zero section over the specified compact base window, its
boundary is an actual base isomorphism off that window, and its class remains
the original equivariant support class.

This is the relative equivariant supplement to SG III.13 Lemma 13.3. Fiber
contraction compares bundles only; no support pullback along contraction or
finite CW assumption on an eventual common open source is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [hDim : FiniteDimensional ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [hG : IsManifold IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

include hDim hG hGC hGT hM hT hSC hC hAction

set_option maxHeartbeats 1000000 in
-- Retain the actual nested pullbacks throughout contraction and class transport.
/-- Relative homogeneous realization of a specified original equivariant support triple. -/
theorem exists_equivariant_relative_homogeneous_cotangent_representative :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ (a : EquivariantSupportBundleTriple G (CotangentTotalSpace (n := n) (M := M)))
      (K : Set M) (_hK : IsCompact K)
      (_hKi : ∀ (g : G) (x : M), g • x ∈ K ↔ x ∈ K)
      (_hcontrol : ∀ z ∈ a.1.datum.control, z.proj ∈ K)
      (ψ : C(M, ℝ)) (_hψzero : ∀ z ∈ a.1.datum.control, ψ z.proj = 0)
      (_hψone : ∀ x ∉ K, ψ x = 1)
      (_hψinv : ∀ (g : G) (x : M), ψ (g • x) = ψ x),
      ∃ E F : FiniteBundle M,
        ∃ (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber),
          ∃ τ : RelativeTriple E.Fiber F.Fiber Kᶜ,
          ∃ b : CompactSupportTriple
            ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
            ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
            ∃ hb : b.IsEquivariant
              (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
              (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)),
              b.control = cotangentZeroSection '' K ∧
              (∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
                ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ b.controlᶜ)
                  (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ b.controlᶜ),
                  b.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
                    b.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩) ∧
              (∀ (z : CotangentTotalSpace (n := n) (M := M)) (hz : z.proj ∉ K)
                (hbz : z ∈ b.controlᶜ),
                b.boundary.linearEquiv ⟨z, hbz⟩ = τ.linearEquiv ⟨z.proj, hz⟩) ∧
              (EquivariantSupportBundleTriple.ofBoundary
                (E.pullback cotangentProjection) (F.pullback cotangentProjection) b
                (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) hb).kZeroClass =
                  a.kZeroClass ∧
              ∃ (e : Iso a.1.source.Fiber
                  ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber))
                (f : Iso a.1.target.Fiber
                  ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber)),
                e.IsEquivariant a.2.sourceAction
                  (ρE.pullback cotangentProjection (fun _ _ ↦ rfl)) ∧
                f.IsEquivariant a.2.targetAction
                  (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) ∧
                ∃ d : CompactSupportTriple
                    ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
                    ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
                  d.IsEquivariant (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                    (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) ∧
                  ∃ H₀ : CompactSupportTriple.EquivariantHomotopy
                      (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                      (ρF.pullback cotangentProjection (fun _ _ ↦ rfl))
                      (a.1.datum.congr e f) d,
                  ∃ H₁ : CompactSupportTriple.EquivariantHomotopy
                      (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                      (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) d b,
                    (∀ z ∈ H₀.control, z.proj ∈ K) ∧
                    (∀ z ∈ H₁.control, z.proj ∈ K) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro a K hK hKi hcontrol ψ hψzero hψone hψinv
  let Z := CotangentTotalSpace (n := n) (M := M)
  let C := CotangentModel n
  let W := CotangentFiber (n := n) (M := M)
  let πV := cotangentProjection (n := n) (M := M)
  let z₀ : C(M, Z) := ⟨cotangentZeroSection, continuous_cotangentZeroSection⟩
  let : RealBundle.IsFiniteRank C W := RealBundle.isFiniteRank_of_vectorBundle C W
  let : SecondCountableTopology Z := RealBundle.secondCountableTopology_totalSpace C W
  let : ParacompactSpace Z := inferInstance
  have hz₀ (g : G) (x : M) : z₀ (g • x) = g • z₀ x := by
    rfl
  have hπ (g : G) (v : Z) : πV (g • v) = g • πV v := rfl
  have hcomp (g : G) (v : Z) : (z₀.comp πV) (g • v) = g • (z₀.comp πV) v :=
    (congrArg z₀ (hπ g v)).trans (hz₀ g (πV v))
  -- Only actual bundle pullbacks use the equivariant fiber contraction.
  -- This map is not asserted proper and does not induce a compact-support K pullback.
  let H : ContinuousMap.Homotopy (z₀.comp πV) (ContinuousMap.id Z) := {
    toFun p := ⟨p.2.proj, (p.1 : ℝ) • p.2.snd⟩
    continuous_toFun := (RealBundle.continuous_scaling C W).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    map_zero_left v := by change (⟨v.proj, (0 : ℝ) • v.snd⟩ : Z) = ⟨v.proj, 0⟩; simp
    map_one_left v := by change (⟨v.proj, (1 : ℝ) • v.snd⟩ : Z) = v; simp }
  have hH (t : unitInterval) (g : G) (v : Z) : H (t, g • v) = g • H (t, v) := by
    rfl
  have hcompare (P : FiniteBundle Z) (ρ : EquivariantStructure G P.Fiber) :
      ∃ e : Iso P.Fiber ((πV : Z → M) *ᵖ ((z₀ : M → Z) *ᵖ P.Fiber)),
        e.IsEquivariant ρ ((ρ.pullback z₀ hz₀).pullback πV hπ) := by
    obtain ⟨i, hi⟩ := ρ.exists_pullback_iso_of_homotopy (z₀.comp πV)
      (ContinuousMap.id Z) hcomp (fun _ _ ↦ rfl) H hH
    let c := pullbackCompIso (E := P.Fiber) z₀ πV
    let e := c.trans (i.trans (pullbackIdIso (E := P.Fiber)))
    have he : e.IsEquivariant ((ρ.pullback z₀ hz₀).pullback πV hπ) ρ := by
      intro g v w
      have hc := ρ.pullbackCompIso_isEquivariant z₀ hz₀ πV hπ g v w
      change c.linearEquiv (g • v) _ = (ρ.pullback (z₀.comp πV) hcomp).linearMap g v
        (c.linearEquiv v w) at hc
      have hh := hi g v (c.linearEquiv v w)
      change e.linearEquiv (g • v) _ = ρ.linearMap g v (e.linearEquiv v w)
      change (pullbackIdIso (E := P.Fiber)).linearEquiv (g • v)
        (i.linearEquiv (g • v) (c.linearEquiv (g • v) _)) =
        ρ.linearMap g v ((pullbackIdIso (E := P.Fiber)).linearEquiv v
          (i.linearEquiv v (c.linearEquiv v w)))
      rw [pullbackIdIso_apply, pullbackIdIso_apply, hc]
      exact hh
    refine ⟨e.symm, ?_⟩
    intro g v w
    apply (e.linearEquiv (g • v)).injective
    change e.linearEquiv (g • v) ((e.linearEquiv (g • v)).symm _) =
      e.linearEquiv (g • v) (((ρ.pullback z₀ hz₀).pullback πV hπ).linearMap g v
        ((e.linearEquiv v).symm w))
    rw [LinearEquiv.apply_symm_apply]
    exact (he g v ((e.linearEquiv v).symm w) |>.trans
      (congrArg (ρ.linearMap g v) ((e.linearEquiv v).apply_symm_apply w))).symm
  obtain ⟨e, he⟩ := hcompare a.1.source a.2.sourceAction
  obtain ⟨f, hf⟩ := hcompare a.1.target a.2.targetAction
  let E := a.1.source.pullback z₀
  let F := a.1.target.pullback z₀
  let ρE := a.2.sourceAction.pullback z₀ hz₀
  let ρF := a.2.targetAction.pullback z₀ hz₀
  let σE := ρE.pullback πV hπ
  let σF := ρF.pullback πV hπ
  let a' := a.1.datum.congr e f
  have heinv (g : G) (x : Z) (v : E.Fiber (πV x)) :
      (e.linearEquiv (g • x)).symm (σE.linearMap g x v) =
        a.2.sourceAction.linearMap g x ((e.linearEquiv x).symm v) := by
    apply (e.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (he g x ((e.linearEquiv x).symm v) |>.trans
      (congrArg (σE.linearMap g x) ((e.linearEquiv x).apply_symm_apply v))).symm
  have ha' : a'.IsEquivariant σE σF := by
    refine ⟨a.2.isEquivariant.invariant_control, ?_⟩
    intro g x v
    let gx : (a.1.datum.controlᶜ : Set Z) := ⟨g • x.val,
      fun h ↦ x.property ((a.2.isEquivariant.invariant_control g x.val).mp h)⟩
    change f.linearEquiv (g • x.val) (a.1.datum.boundary.linearEquiv gx
        ((e.linearEquiv (g • x.val)).symm (σE.linearMap g x.val v))) =
      σF.linearMap g x.val (f.linearEquiv x.val
        (a.1.datum.boundary.linearEquiv x ((e.linearEquiv x.val).symm v)))
    refine (congrArg (fun w : a.1.source.Fiber (g • x.val) ↦
      f.linearEquiv (g • x.val) (a.1.datum.boundary.linearEquiv gx w))
      (heinv g x.val v)).trans ?_
    exact (congrArg (f.linearEquiv (g • x.val))
      (a.2.isEquivariant.boundary_intertwines g x ((e.linearEquiv x.val).symm v))).trans
      (hf g x.val _)
  let A := EquivariantSupportBundleTriple.ofBoundary
    (E.pullback πV) (F.pullback πV) a' σE σF ha'
  have hA : A.kZeroClass = a.kZeroClass := by
    apply Eq.symm
    apply equivariantSupportTripleKZero_generator_relations.1 a A
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, Set.Subset.refl _, Set.Subset.refl _,
      e, f, he, hf, ?_⟩
    intro x v
    refine (congrArg (f.linearEquiv x.val)
      (a.1.datum.enlarge_apply a.1.datum.control a.1.datum.isCompact_control
        (Set.Subset.refl _) x v)).trans ?_
    refine Eq.trans ?_ (a'.enlarge_apply a.1.datum.control a.1.datum.isCompact_control
      (Set.Subset.refl _) x (e.linearEquiv x.val v)).symm
    change f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x v) =
      f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x
        ((e.linearEquiv x.val).symm (e.linearEquiv x.val v)))
    exact congrArg (fun w : a.1.source.Fiber x.val ↦
      f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x w))
      ((e.linearEquiv x.val).symm_apply_apply v).symm
  -- The original zero-fiber boundary gives an actual exterior base isomorphism.
  let PE := (πV : Z → M) *ᵖ E.Fiber
  let PF := (πV : Z → M) *ᵖ F.Fiber
  let iK : C((Kᶜ : Set M), M) := ⟨Subtype.val, continuous_subtype_val⟩
  let iC : C((a'.controlᶜ : Set Z), Z) := ⟨Subtype.val, continuous_subtype_val⟩
  let zK : C((Kᶜ : Set M), (a'.controlᶜ : Set Z)) :=
    ⟨fun x ↦ ⟨⟨x.val, 0⟩, fun hz ↦ x.property (hcontrol _ hz)⟩,
      (continuous_cotangentZeroSection.comp continuous_subtype_val).subtype_mk _⟩
  let τ : RelativeTriple E.Fiber F.Fiber Kᶜ := {
    linearEquiv x := a'.boundary.linearEquiv (zK x)
    continuous_total := by
      have hin : Continuous (fun w : TotalSpace Unit ((iK : _ → M) *ᵖ E.Fiber) ↦
          (⟨zK w.proj, w.snd⟩ : TotalSpace Unit ((iC : _ → Z) *ᵖ PE))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit PE iC).continuous_iff]
        refine (zK.continuous.comp (Pullback.continuous_proj Unit E.Fiber iK)).prodMk ?_
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber πV).continuous_iff]
        exact ((iC.continuous.comp zK.continuous).comp
          (Pullback.continuous_proj Unit E.Fiber iK)).prodMk
            (Pullback.continuous_lift Unit E.Fiber iK)
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber iK).continuous_iff]
      exact (Pullback.continuous_proj Unit E.Fiber iK).prodMk
        ((Pullback.continuous_lift Unit F.Fiber πV).comp
          ((Pullback.continuous_lift Unit PF iC).comp (a'.boundary.continuous_total.comp hin)))
    continuous_symm := by
      have hin : Continuous (fun w : TotalSpace Unit ((iK : _ → M) *ᵖ F.Fiber) ↦
          (⟨zK w.proj, w.snd⟩ : TotalSpace Unit ((iC : _ → Z) *ᵖ PF))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit PF iC).continuous_iff]
        refine (zK.continuous.comp (Pullback.continuous_proj Unit F.Fiber iK)).prodMk ?_
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber πV).continuous_iff]
        exact ((iC.continuous.comp zK.continuous).comp
          (Pullback.continuous_proj Unit F.Fiber iK)).prodMk
            (Pullback.continuous_lift Unit F.Fiber iK)
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber iK).continuous_iff]
      exact (Pullback.continuous_proj Unit F.Fiber iK).prodMk
        ((Pullback.continuous_lift Unit E.Fiber πV).comp
          ((Pullback.continuous_lift Unit PE iC).comp (a'.boundary.continuous_symm.comp hin))) }
  -- Flatten only fibers over bases outside the original projected control.
  obtain ⟨d, hd, hdcontrol, hdext, Hflat, hHflat⟩ :=
    exists_equivariant_cotangent_base_flattening IG E F ρE ρF a' ha'
      K hcontrol ψ hψzero hψone hψinv
  have hdK (z : Z) (hz : z ∈ d.control) : z.proj ∈ K :=
    hcontrol z (hdcontrol ▸ hz)
  have hdτ (z : Z) (hz : z.proj ∉ K) (hzcontrol : z ∈ d.controlᶜ) :
      d.boundary.linearEquiv ⟨z, hzcontrol⟩ = τ.linearEquiv ⟨z.proj, hz⟩ :=
    hdext z.proj hz z.snd hzcontrol
  -- Relative radial normalization retains the same exterior isomorphism and window.
  obtain ⟨b, hb, hzero, hhom, hext, Hrad, hHrad⟩ :=
    exists_equivariant_relative_radial_cotangent_representative IG E F ρE ρF d hd
      K hK hKi hdK τ hdτ
  refine ⟨E, F, ρE, ρF, τ, b, hb, hzero, hhom, hext, ?_, ?_⟩
  · exact (equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
      (E.pullback πV) (F.pullback πV) σE σF d b hd hb ⟨Hrad⟩).symm.trans
        ((equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
          (E.pullback πV) (F.pullback πV) σE σF a' d ha' hd ⟨Hflat⟩).symm.trans hA)
  · -- These controls permit restriction to the common open source before taking its class.
    refine ⟨e, f, he, hf, d, hd, Hflat, Hrad, ?_, hHrad⟩
    intro z hz
    exact hcontrol z (hHflat ▸ hz)

end AtiyahSinger
