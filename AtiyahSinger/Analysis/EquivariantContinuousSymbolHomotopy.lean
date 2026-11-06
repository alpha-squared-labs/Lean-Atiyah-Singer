/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereHomotopy
public import AtiyahSinger.Analysis.EquivariantCosphereProjection
public import AtiyahSinger.Analysis.EquivariantHomogeneousAnalyticIndex
public import AtiyahSinger.Analysis.PuncturedSymbol
public import AtiyahSinger.Geometry.InvariantCotangentMetricOfCompactAction

/-!
# Continuous equivariant symbol homotopies on fixed original bundles

Public module ID: M0491.

A jointly continuous elliptic equivariant homotopy on the original punctured
cotangent bundle, between smooth homogeneous endpoints of one real degree,
admits a replacement continuous in the existing smooth homogeneous topology.
The replacement keeps both endpoints exact off zero and preserves the same
original bundles and group actions. The given intermediate symbols need not
be homogeneous. In degree zero this preserves the full canonical G-index.

Sources: SG III.7.10--7.11 for index homotopy invariance, III.9, pp.211--214,
for equivariant averaging, and III.13, pp.245--247, for radial homogeneous
representatives and the K-theory route. Relative equivariant approximation
with an explicit invertibility margin is a project supplement, recorded as
EHD-CONTINUOUS-HOMOTOPY-SOURCE. It is not a numbered theorem from the book.

The path theorem uses the same compact Lie-group setting as the canonical
index. Spatial differentiation of the Haar average gives a smooth invariant
cotangent metric without a finite-dimensional group-model hypothesis. A continuous
Haar projection in the original cosphere topology preserves the smooth core;
ordinary smooth density then supplies equivariant vertices in elliptic neighborhoods.
An average of arbitrary invertible maps is never assumed invertible.
The original zero-section values, empty bases, dimension zero and independent
ranks remain unrestricted. Both original homotopy statements are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hLie : LieGroup IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [hGM : MeasurableSpace G] [hGB : BorelSpace G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT2 hSC hC hE hF hLie hGC hGT hGM hGB hAction hσE hσF

attribute [local instance] homogeneousSymbolTopology

set_option maxHeartbeats 1600000 in
-- The local joinedness relation uses the equivariant smooth subspace and its full topology.
set_option linter.unusedSectionVars false in
/-- A continuous equivariant elliptic homotopy admits a relative smooth homogeneous path. -/
theorem exists_continuous_equivariant_homogeneous_path (m : ℝ)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (H : unitInterval → GlobalSymbolFunction (n := n) E F)
    (hH : IsContinuousOffZeroSymbolFamily (r := r) (q := q) H)
    (hHe : ∀ t, IsEllipticGlobalSymbol E F (H t))
    (hHg : ∀ (t : unitInterval) (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      ξ ≠ 0 → equivariantGlobalSymbolLinearMap IG σE σF g (H t) x ξ = H t x ξ)
    (h0 : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → H 0 x ξ = a.val x ξ)
    (h1 : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → H 1 x ξ = b.val x ξ) :
    ∃ K : unitInterval → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m,
      Continuous K ∧ (∀ t, IsEllipticGlobalSymbol E F (K t).val) ∧
        (∀ (t : unitInterval) (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
          ξ ≠ 0 →
            equivariantGlobalSymbolLinearMap IG σE σF g (K t).val x ξ = (K t).val x ξ) ∧
        (∀ (x : M) (ξ : CotangentFiber (n := n) x),
          ξ ≠ 0 → (K 0).val x ξ = a.val x ξ) ∧
        (∀ (x : M) (ξ : CotangentFiber (n := n) x),
          ξ ≠ 0 → (K 1).val x ξ = b.val x ξ) := by
  -- The neighborhood relation connects vertices in the equivariant smooth subspace.
  classical
  -- The average differentiates only spatial variables, so no group-model dimension is added.
  obtain ⟨h, hinner⟩ := exists_invariant_smoothCotangentMetric_of_compact_action
    (n := n) (M := M) (G := G) IG
  have hInv (g : G) (x : M) (ξ : CotangentFiber (n := n) x) :
      h.length (g • x) (cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g) ⟨x, ξ⟩).snd =
          h.length x ξ := congrArg Real.sqrt (hinner g x ξ ξ)
  let S₀ := smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) h
  let Eqv (c : CosphereSymbolFunction (E := E) (F := F) h) : Prop :=
    ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g (cosphereExtension h 0 c) x ξ =
        cosphereExtension h 0 c x ξ
  let S := {c : S₀ // Eqv c.val}
  let C := ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) h
  let : TopologicalSpace C := continuousCosphereSymbolTopology h
  let : TopologicalSpace S₀ := smoothCosphereSymbolTopology h
  let ι : S → C := fun c ↦ smoothCosphereToContinuous h c.val
  let W : Set S := {c | IsEllipticCosphereSymbol h c.val.val}
  let Hc (t : unitInterval) : C :=
    ⟨cosphereRestriction h (H t), (hH.slice t).cosphereRestriction h⟩
  have hc : Continuous Hc := (continuous_cosphere_iff h Hc).mpr
    (Continuous.comp hH (continuous_fst.prodMk
      (h.continuous_cosphereInclusion.comp continuous_snd)))
  have heH (t : unitInterval) : IsEllipticCosphereSymbol h (Hc t).val :=
    fun z ↦ hHe t z.val.proj z.val.snd (h.cosphere_ne_zero z)
  have hgH (t : unitInterval) : Eqv (Hc t).val :=
    equivariant_cosphereExtension_restriction IG σE σF h hInv 0 (H t) (hHg t)
  -- Equivariant smooth vertices are dense in the original compact-open section topology.
  have density (t : unitInterval) (U : Set C) (hU : IsOpen U) (ht : Hc t ∈ U) :
      ∃ c : S, ι c ∈ U := by
    obtain ⟨A, hA, hAg, hfix, hsm⟩ :=
      exists_continuous_equivariant_cosphere_projection IG σE σF hσE hσF h hInv
    have hneigh : IsOpen (A ⁻¹' U) := hU.preimage hA
    have ht' : Hc t ∈ A ⁻¹' U := by
      change A (Hc t) ∈ U
      rw [hfix (Hc t) (hgH t)]
      exact ht
    obtain ⟨c, hc⟩ := exists_smoothCosphere_mem h (Hc t) (A ⁻¹' U) hneigh ht'
    let d : S₀ := ⟨(A (smoothCosphereToContinuous h c)).val,
      hsm (smoothCosphereToContinuous h c) c.property⟩
    exact ⟨⟨d, hAg (smoothCosphereToContinuous h c)⟩, hc⟩
  -- Each affine segment stays in the specified equivariant subspace and all smooth seminorms.
  have segment (u v : S)
      (he : ∀ t : unitInterval,
        IsEllipticCosphereSymbol h (cosphereInterpolation h u.val.val v.val.val t)) :
      JoinedIn W u v := by
    let f₀ (t : unitInterval) : S₀ :=
      (((1 - (t : ℝ) : ℝ) : ℂ) • u.val) + (((t : ℝ) : ℂ) • v.val)
    have hf₀ : Continuous f₀ := by
      have hp := withSeminorms_homogeneousSymbolTopology (n := n) (r := r) (q := q) E F 0
      let := hp.isTopologicalAddGroup
      let := hp.continuousSMul
      rw [continuous_induced_rng]
      rw [show smoothCosphereExtension (r := r) (q := q) h 0 ∘ f₀ =
          fun t : unitInterval ↦
            (((1 - (t : ℝ) : ℝ) : ℂ) • smoothCosphereExtension h 0 u.val) +
            (((t : ℝ) : ℂ) • smoothCosphereExtension h 0 v.val) from ?_]
      · exact ((Complex.continuous_ofReal.comp
          (continuous_const.sub continuous_subtype_val)).smul continuous_const).add
            ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
      · funext t
        apply Subtype.ext
        change cosphereExtension h 0
          ((((1 - (t : ℝ) : ℝ) : ℂ) • u.val.val) + (((t : ℝ) : ℂ) • v.val.val)) = _
        rw [cosphereExtension_add, cosphereExtension_smul, cosphereExtension_smul]
        rfl
    have hfg (t : unitInterval) : Eqv (f₀ t).val := by
      intro g x ξ hξ
      change equivariantGlobalSymbolLinearMap IG σE σF g
        (cosphereExtension h 0
          ((((1 - (t : ℝ) : ℝ) : ℂ) • u.val.val) + (((t : ℝ) : ℂ) • v.val.val))) x ξ = _
      rw [cosphereExtension_add, cosphereExtension_smul, cosphereExtension_smul]
      rw [map_add, map_smul, map_smul]
      change (((1 - (t : ℝ) : ℝ) : ℂ) •
        equivariantGlobalSymbolLinearMap IG σE σF g (cosphereExtension h 0 u.val.val) x ξ) +
        (((t : ℝ) : ℂ) •
        equivariantGlobalSymbolLinearMap IG σE σF g (cosphereExtension h 0 v.val.val) x ξ) = _
      rw [u.property g x ξ hξ, v.property g x ξ hξ]
      change _ = cosphereExtension h 0
        ((((1 - (t : ℝ) : ℝ) : ℂ) • u.val.val) + (((t : ℝ) : ℂ) • v.val.val)) x ξ
      rw [cosphereExtension_add, cosphereExtension_smul, cosphereExtension_smul]
      rfl
    let f (t : unitInterval) : S := ⟨f₀ t, hfg t⟩
    have hf : Continuous f := hf₀.subtype_mk _
    refine ⟨{ toFun := f
              continuous_toFun := hf
              source' := ?_
              target' := ?_ }, ?_⟩
    · apply Subtype.ext
      simp [f, f₀]
    · apply Subtype.ext
      simp [f, f₀]
    · exact he
  -- The locally controlled relation composes using one common equivariant smooth vertex.
  let R (s t : unitInterval) : Prop :=
    ∃ U V : Set C, IsOpen U ∧ IsOpen V ∧ Hc s ∈ U ∧ Hc t ∈ V ∧
      ∀ u v : S, ι u ∈ U → ι v ∈ V → JoinedIn W u v
  have hlocal (s : unitInterval) : ∀ᶠ t in 𝓝 s, R s t := by
    obtain ⟨U, hU, hsU, hcontrol⟩ :=
      exists_elliptic_convex_neighborhood h (Hc s) (heH s)
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hsU)] with t ht
    refine ⟨U, U, hU, hU, hsU, ht, ?_⟩
    intro u v hu hv
    exact segment u v (hcontrol (ι u) hu (ι v) hv)
  have hsymm : Std.Symm R := ⟨by
    intro s t hst
    obtain ⟨U, V, hU, hV, hs, ht, hjoin⟩ := hst
    exact ⟨V, U, hV, hU, ht, hs, fun u v hu hv ↦ (hjoin v u hv hu).symm⟩⟩
  have htrans : IsTrans unitInterval R := ⟨by
    intro s t z hst htz
    obtain ⟨U, V, hU, hV, hs, htV, hjoin₁⟩ := hst
    obtain ⟨V', Z, hV', hZ, htV', hz, hjoin₂⟩ := htz
    obtain ⟨w, hw⟩ := density t (V ∩ V') (hV.inter hV') ⟨htV, htV'⟩
    refine ⟨U, Z, hU, hZ, hs, hz, ?_⟩
    intro u v hu hv
    exact (hjoin₁ u w hu hw.1).trans (hjoin₂ w v hw.2 hv)⟩
  let := hsymm
  obtain ⟨U, V, _, _, haU, hbV, hjoin⟩ :=
    PreconnectedSpace.induction₂ R hlocal htrans 0 1
  let a₀ := smoothCosphereRestriction (r := r) (q := q) h m a
  let b₀ := smoothCosphereRestriction (r := r) (q := q) h m b
  have h₀ : (Hc 0).val = a₀.val := by
    funext z
    exact h0 z.val.proj z.val.snd (h.cosphere_ne_zero z)
  have h₁ : (Hc 1).val = b₀.val := by
    funext z
    exact h1 z.val.proj z.val.snd (h.cosphere_ne_zero z)
  let a' : S := ⟨a₀, h₀ ▸ hgH 0⟩
  let b' : S := ⟨b₀, h₁ ▸ hgH 1⟩
  have ha' : ι a' ∈ U := by
    have h0' : Hc 0 = ι a' := Subtype.ext h₀
    rwa [h0'] at haU
  have hb' : ι b' ∈ V := by
    have h1' : Hc 1 = ι b' := Subtype.ext h₁
    rwa [h1'] at hbV
  let γ := (hjoin a' b' ha' hb').somePath
  let K (t : unitInterval) := smoothCosphereExtension h m (γ t).val
  refine ⟨K, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_smoothCosphereExtension h m).comp
      (continuous_subtype_val.comp γ.continuous)
  · intro t
    exact (isEllipticGlobalSymbol_cosphereExtension_iff h m (γ t).val.val).mpr
      ((hjoin a' b' ha' hb').somePath_mem t)
  · intro t
    have hgt := equivariant_cosphereExtension_restriction IG σE σF h hInv m
      (cosphereExtension h 0 (γ t).val.val) (γ t).property
    change ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g
        (cosphereExtension h m (γ t).val.val) x ξ =
          cosphereExtension h m (γ t).val.val x ξ
    simpa only [cosphereRestriction_extension] using hgt
  · intro x ξ hξ
    change cosphereExtension h m (γ 0).val.val x ξ = a.val x ξ
    rw [γ.source]
    exact cosphereExtension_restriction h m a.val a.property.2 x ξ hξ
  · intro x ξ hξ
    change cosphereExtension h m (γ 1).val.val x ξ = b.val x ξ
    rw [γ.target]
    exact cosphereExtension_restriction h m b.val b.property.2 x ξ hξ

include hBorel

/-- A jointly continuous equivariant elliptic homotopy preserves the full symbol index. -/
theorem equivariantHomogeneousAnalyticIndex_eq_of_continuous_homotopy
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (ha : IsEllipticGlobalSymbol E F a.val)
    (hb : IsEllipticGlobalSymbol E F b.val)
    (hag : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g a.val x ξ = a.val x ξ)
    (hbg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g b.val x ξ = b.val x ξ)
    (H : unitInterval → GlobalSymbolFunction (n := n) E F)
    (hH : IsContinuousOffZeroSymbolFamily (r := r) (q := q) H)
    (hHe : ∀ t, IsEllipticGlobalSymbol E F (H t))
    (hHg : ∀ (t : unitInterval) (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      ξ ≠ 0 → equivariantGlobalSymbolLinearMap IG σE σF g (H t) x ξ = H t x ξ)
    (h0 : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → H 0 x ξ = a.val x ξ)
    (h1 : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → H 1 x ξ = b.val x ξ) :
    equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF a ha hag =
      equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF b hb hbg := by
  classical
  obtain ⟨K, hK, hKe, hKg, hK0, hK1⟩ :=
    exists_continuous_equivariant_homogeneous_path IG σE σF hσE hσF 0 a b H hH hHe hHg h0 h1
  -- Fix one actual invariant geometry and regularization for every endpoint comparison.
  obtain ⟨μ, hμ, hμInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ
  obtain ⟨h, hInvariant⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, kInvariant⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q) (E := E) (F := F)
  have congr_index
      (s t : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
      (hs : IsEllipticGlobalSymbol E F s.val)
      (ht : IsEllipticGlobalSymbol E F t.val)
      (hsg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
      (htg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE σF g t.val x ξ = t.val x ξ)
      (hst : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → s.val x ξ = t.val x ξ) :
      equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hs hsg =
        equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF t ht htg := by
    let ps := R.regularizedSymbol 0 s.val s.property.1 s.property.2
    have hfixed (g : G) : equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF 0 g
        (globalPrincipalSymbolClass E F 0 ps) = globalPrincipalSymbolClass E F 0 ps :=
      (R.equivariant_regularizedSymbol_class_eq_iff IG σE σF hσE hσF R 0 s s g).mpr (hsg g)
    obtain ⟨P, hPg, hPclass⟩ :=
      PseudodifferentialOperator.exists_equivariant_principalSymbol (μ := μ)
        IG σE σF hσE hσF 0 (globalPrincipalSymbolClass E F 0 ps) hfixed
    have hP : P.IsElliptic := ⟨ps, hPclass,
      (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 s.val
        s.property.1 s.property.2).mpr hs⟩
    have hclasses := (R.regularizedSymbol_class_eq_iff R 0 s.val t.val
      s.property.1 s.property.2 t.property.1 t.property.2).mpr hst
    -- Both canonical values are evaluated on this same P, with the same action and metrics.
    exact (equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF s hs hsg
      μ hμ h k hInvariant kInvariant hμInvariant R P hPg hP hPclass).trans
        (equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF t ht htg
          μ hμ h k hInvariant kInvariant hμInvariant R P hPg hP
            (hPclass.trans hclasses)).symm
  exact (congr_index a (K 0) ha (hKe 0) hag (hKg 0)
    (fun x ξ hξ ↦ (hK0 x ξ hξ).symm)).trans
      ((equivariantHomogeneousAnalyticIndex_eq_of_homotopy IG σE σF hσE hσF
        K hK hKe hKg).trans (congr_index (K 1) b (hKe 1) hb (hKg 1) hbg hK1))

end AtiyahSinger
