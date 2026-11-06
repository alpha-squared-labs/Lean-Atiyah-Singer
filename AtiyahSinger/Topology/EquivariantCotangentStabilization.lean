/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Topology.EquivariantBundleEmbedding
public import AtiyahSinger.Topology.EquivariantBundleHomotopy
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero

import AtiyahSinger.Topology.RealBundleSupport
import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Equivariant stabilization over the original cotangent projection

Public module ID: M1777.

The fiber contraction compares a bundle on the cotangent space with the
pullback of its own zero-section restriction. These comparisons retain the
original action and will normalize stable equivariant symbol squares before
smoothing their stabilizers. The contraction is used only for bundles; no
proper compact-support pullback along it is asserted.

Source: bundle homotopy invariance and finite-representation stabilization,
as used in SG III.13 and Karoubi I.9.31. The explicit equivariant normalization
of the original stable square is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

set_option maxHeartbeats 1000000 in
-- The same original pullback topologies are retained throughout the contraction.
/-- A bundle over the cotangent space is equivariantly pulled back from its restriction
to the zero section. -/
theorem exists_equivariant_cotangent_zeroSection_iso :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ (P : FiniteBundle (CotangentTotalSpace (n := n) (M := M)))
      (ρ : EquivariantStructure G P.Fiber),
      ∃ e : Iso P.Fiber
          ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ
            ((cotangentZeroSection (n := n) (M := M)) *ᵖ P.Fiber)),
        e.IsEquivariant ρ
          ((ρ.pullback ⟨cotangentZeroSection, continuous_cotangentZeroSection⟩
            (fun _ _ ↦ rfl)).pullback cotangentProjection (fun _ _ ↦ rfl)) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro P ρ
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

variable [CompactSpace M]

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial

set_option maxHeartbeats 1600000 in
-- Stabilization retains the original bundle sums and their actual induced pullback topologies.
/-- Equal equivariant cotangent classes admit base stabilizers of constant,
possibly different ranks. -/
theorem exists_fixedRank_equivariant_cotangent_stabilizers :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ (a b : EquivariantSupportBundleTriple G (CotangentTotalSpace (n := n) (M := M)))
      (r s : ℕ),
      (∀ x : M, Module.finrank ℂ (a.1.source.Fiber (cotangentZeroSection x)) = r) →
      (∀ x : M, Module.finrank ℂ (b.1.source.Fiber (cotangentZeroSection x)) = s) →
      a.kZeroClass = b.kZeroClass →
      ∃ (C D : FiniteBundle M) (p q : ℕ),
        (∀ x, Module.finrank ℂ (C.Fiber x) = p) ∧
        (∀ x, Module.finrank ℂ (D.Fiber x) = q) ∧
        ∃ (σC : EquivariantStructure G C.Fiber) (σD : EquivariantStructure G D.Fiber),
          (a.sum (EquivariantSupportBundleTriple.identity (C.pullback cotangentProjection)
            (σC.pullback cotangentProjection (fun _ _ ↦ rfl)))).IsIsomorphic
          (b.sum (EquivariantSupportBundleTriple.identity (D.pullback cotangentProjection)
            (σD.pullback cotangentProjection (fun _ _ ↦ rfl)))) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro a b r s hr hs hab
  let Z := CotangentTotalSpace (n := n) (M := M)
  let πM := cotangentProjection (n := n) (M := M)
  let z₀ : C(M, Z) := ⟨cotangentZeroSection, continuous_cotangentZeroSection⟩
  let identity := EquivariantSupportBundleTriple.identity (G := G) (X := Z)
  let eqv := (EquivariantSupportBundleTriple.isIsomorphic_properties (G := G) (X := Z)).1
  have hsum := (EquivariantSupportBundleTriple.isIsomorphic_sum_enlarge
    (G := G) (X := Z)).1
  -- First retain the actual two original stabilizers and their global commuting square.
  obtain ⟨C₁, D₁, σ₁, τ₁, hstable⟩ := (a.kZeroClass_eq_iff_stable b).mp hab
  obtain ⟨iC, hiC⟩ := exists_equivariant_cotangent_zeroSection_iso IG C₁ σ₁
  obtain ⟨iD, hiD⟩ := exists_equivariant_cotangent_zeroSection_iso IG D₁ τ₁
  let C₀ := C₁.pullback z₀
  let D₀ := D₁.pullback z₀
  let σ₀ := σ₁.pullback z₀ (fun _ _ ↦ rfl)
  let τ₀ := τ₁.pullback z₀ (fun _ _ ↦ rfl)
  have hrank (x : M) : r + Module.finrank ℂ (C₀.Fiber x) =
      s + Module.finrank ℂ (D₀.Fiber x) := by
    obtain ⟨_, _, _, _, _, u, _, _, _, _⟩ := hstable
    let := finite_fiber (E := a.1.source.Fiber) (z₀ x)
    let := finite_fiber (E := b.1.source.Fiber) (z₀ x)
    let := finite_fiber (E := C₁.Fiber) (z₀ x)
    let := finite_fiber (E := D₁.Fiber) (z₀ x)
    have h := (u.linearEquiv (z₀ x)).finrank_eq
    change Module.finrank ℂ (a.1.source.Fiber (z₀ x) × C₁.Fiber (z₀ x)) =
      Module.finrank ℂ (b.1.source.Fiber (z₀ x) × D₁.Fiber (z₀ x)) at h
    have hA : Module.finrank ℂ (a.1.source.Fiber (z₀ x)) = r := hr x
    have hB : Module.finrank ℂ (b.1.source.Fiber (z₀ x)) = s := hs x
    change r + Module.finrank ℂ (C₁.Fiber (z₀ x)) =
      s + Module.finrank ℂ (D₁.Fiber (z₀ x))
    simpa only [Module.finrank_prod, hA, hB] using h
  -- One common complement and the same extra trivial summand make both ranks constant.
  obtain ⟨H₀, υ₀, ρ, eρ, _heρ⟩ := σ₀.exists_finiteRepresentation_complement
  let ρs : FiniteContinuousRepresentation G := {
    dimension := s
    representation := ContRepresentation.trivial ℂ G (Fin s → ℂ)
    continuous_action := continuous_snd }
  let H := H₀.sum (FiniteBundle.trivial M s)
  let υ := υ₀.sum (EquivariantStructure.ofFiniteRepresentation ρs)
  let C := C₀.sum H
  let D := D₀.sum H
  let σC := σ₀.sum υ
  let σD := τ₀.sum υ
  have hC (x : M) : Module.finrank ℂ (C.Fiber x) = ρ.dimension + s := by
    let := finite_fiber (E := C₀.Fiber) x
    let := finite_fiber (E := H₀.Fiber) x
    have he := (eρ.linearEquiv x).finrank_eq
    change Module.finrank ℂ (C₀.Fiber x × H₀.Fiber x) =
      Module.finrank ℂ (Fin ρ.dimension → ℂ) at he
    simp only [Module.finrank_prod, Module.finrank_fin_fun] at he
    change Module.finrank ℂ (C₀.Fiber x × (H₀.Fiber x × (Fin s → ℂ))) = _
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun]
    omega
  have hD (x : M) : Module.finrank ℂ (D.Fiber x) = ρ.dimension + r := by
    let := finite_fiber (E := C₀.Fiber) x
    let := finite_fiber (E := D₀.Fiber) x
    let := finite_fiber (E := H.Fiber) x
    have hC' := hC x
    change Module.finrank ℂ (C₀.Fiber x × H.Fiber x) = _ at hC'
    change Module.finrank ℂ (D₀.Fiber x × H.Fiber x) = _
    rw [Module.finrank_prod] at hC' ⊢
    have h := hrank x
    omega
  -- Compare pullback of a direct sum with the same pair of pulled-back fibers.
  let compare (J K : FiniteBundle M) :
      Iso ((J.sum K).pullback πM).Fiber ((J.pullback πM).sum (K.pullback πM)).Fiber := {
    linearEquiv z := LinearEquiv.refl ℂ (J.Fiber (πM z) × K.Fiber (πM z))
    continuous_total := by
      apply continuous_induced_rng.mpr
      apply Continuous.prodMk
      · rw [(inducing_pullbackTotalSpaceEmbedding Unit J.Fiber πM).continuous_iff]
        exact (Pullback.continuous_proj Unit (J.sum K).Fiber πM).prodMk
          (continuous_sum_fst.comp (Pullback.continuous_lift Unit (J.sum K).Fiber πM))
      · rw [(inducing_pullbackTotalSpaceEmbedding Unit K.Fiber πM).continuous_iff]
        exact (Pullback.continuous_proj Unit (J.sum K).Fiber πM).prodMk
          (continuous_sum_snd.comp (Pullback.continuous_lift Unit (J.sum K).Fiber πM))
    continuous_symm := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit (J.sum K).Fiber πM).continuous_iff]
      apply ((Pullback.continuous_proj Unit J.Fiber πM).comp continuous_sum_fst).prodMk
      apply continuous_induced_rng.mpr
      exact ((Pullback.continuous_lift Unit J.Fiber πM).comp continuous_sum_fst).prodMk
        ((Pullback.continuous_lift Unit K.Fiber πM).comp continuous_sum_snd) }
  let Hπ := H.pullback πM
  let υπ := υ.pullback πM (fun _ _ ↦ rfl)
  let jC := (iC.sum (Iso.refl Hπ.Fiber)).trans (compare C₀ H).symm
  let jD := (iD.sum (Iso.refl Hπ.Fiber)).trans (compare D₀ H).symm
  have hjC : jC.IsEquivariant (σ₁.sum υπ) (σC.pullback πM (fun _ _ ↦ rfl)) := by
    intro g x v
    exact Prod.ext (hiC g x v.1) rfl
  have hjD : jD.IsEquivariant (τ₁.sum υπ) (σD.pullback πM (fun _ _ ↦ rfl)) := by
    intro g x v
    exact Prod.ext (hiD g x v.1) rfl
  -- Regroup the two identity summands through the specified same equivariant comparison.
  have hcollect (a : EquivariantSupportBundleTriple G Z) (P H Q : FiniteBundle Z)
      (σP : EquivariantStructure G P.Fiber) (σH : EquivariantStructure G H.Fiber)
      (σQ : EquivariantStructure G Q.Fiber) (j : Iso (P.sum H).Fiber Q.Fiber)
      (hj : j.IsEquivariant (σP.sum σH) σQ) :
      ((a.sum (identity P σP)).sum (identity H σH)).IsIsomorphic
        (a.sum (identity Q σQ)) := by
    let u := (a.1.source.sumAssocIso P H).trans ((Iso.refl a.1.source.Fiber).sum j)
    let v := (a.1.target.sumAssocIso P H).trans ((Iso.refl a.1.target.Fiber).sum j)
    have hu (x : Z) (w : ((a.1.source.sum P).sum H).Fiber x) :
        u.linearEquiv x w = (w.1.1, j.linearEquiv x (w.1.2, w.2)) := by
      change ((Iso.refl a.1.source.Fiber).sum j).linearEquiv x
        ((a.1.source.sumAssocIso P H).linearEquiv x w) = _
      rw [FiniteBundle.sumAssocIso_apply]
      rfl
    have hv (x : Z) (w : ((a.1.target.sum P).sum H).Fiber x) :
        v.linearEquiv x w = (w.1.1, j.linearEquiv x (w.1.2, w.2)) := by
      change ((Iso.refl a.1.target.Fiber).sum j).linearEquiv x
        ((a.1.target.sumAssocIso P H).linearEquiv x w) = _
      rw [FiniteBundle.sumAssocIso_apply]
      rfl
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, ?_, ?_, u, v, ?_, ?_, ?_⟩
    · exact Set.union_subset (Set.union_subset Set.Subset.rfl (Set.empty_subset _))
        (Set.empty_subset _)
    · exact Set.union_subset Set.Subset.rfl (Set.empty_subset _)
    · intro g x w
      change u.linearEquiv (g • x)
          ((a.2.sourceAction.linearMap g x w.1.1, σP.linearMap g x w.1.2),
            σH.linearMap g x w.2) =
        (a.2.sourceAction.linearMap g x (u.linearEquiv x w).1,
          σQ.linearMap g x (u.linearEquiv x w).2)
      rw [hu (g • x), hu x w]
      exact Prod.ext rfl (hj g x (w.1.2, w.2))
    · intro g x w
      change v.linearEquiv (g • x)
          ((a.2.targetAction.linearMap g x w.1.1, σP.linearMap g x w.1.2),
            σH.linearMap g x w.2) =
        (a.2.targetAction.linearMap g x (v.linearEquiv x w).1,
          σQ.linearMap g x (v.linearEquiv x w).2)
      rw [hv (g • x), hv x w]
      exact Prod.ext rfl (hj g x (w.1.2, w.2))
    · intro x w
      simp only [EquivariantSupportBundleTriple.sum, identity,
        EquivariantSupportBundleTriple.identity, SupportBundleTriple.sum,
        SupportBundleTriple.identity, SupportBundleTriple.ofBoundary,
        CompactSupportTriple.sum, CompactSupportTriple.enlarge,
        Iso.restrictTo_apply, RelativeTriple.sum_apply, CompactSupportTriple.ofIso]
      simp only [hu x.val, hv x.val]
      rfl
  refine ⟨C, D, ρ.dimension + s, ρ.dimension + r, hC, hD, σC, σD, ?_⟩
  have hleft := hcollect a C₁ Hπ (C.pullback πM) σ₁ υπ
    (σC.pullback πM (fun _ _ ↦ rfl)) jC hjC
  have hright := hcollect b D₁ Hπ (D.pullback πM) τ₁ υπ
    (σD.pullback πM (fun _ _ ↦ rfl)) jD hjD
  exact eqv.trans (eqv.symm hleft)
    (eqv.trans (hsum _ _ _ _ hstable (eqv.refl (identity Hπ υπ))) hright)

end AtiyahSinger
