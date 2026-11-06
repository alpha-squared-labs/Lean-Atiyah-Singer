/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereMetricChange

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.PathConnected

/-!
# Relative smoothing of continuous elliptic homotopies

Public module ID: M0416.

The standard homotopy relation uses actual jointly continuous invertible Hom
sections with prescribed endpoints. Compactness and smooth approximation then
produce a path continuous in the spatial C-infinity topology, keeping smooth
endpoints exact. Smoothness in the interval parameter is not claimed or needed.
This relative approximation argument fills an explicit project detail in the
application of SG III.7.10--7.11 to C-zero cosphere homotopies. It is not a newly
numbered lemma from the book. Relative smoothing uses local interpolation control
and smooth density, with connectedness composing the resulting smooth paths.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory
open scoped Manifold ContDiff ComplexConjugate Topology

set_option maxSynthPendingDepth 20


set_option linter.unusedSectionVars false

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
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- Homotopy through invertible sections of the pulled-back Hom bundle. -/
def EllipticCosphereHomotopic (a b : CosphereSymbolFunction (E := E) (F := F) g) : Prop :=
  ∃ H : unitInterval → CosphereSymbolFunction (E := E) (F := F) g,
    IsContinuousCosphereFamily (r := r) (q := q) g H ∧
      (∀ t, IsEllipticCosphereSymbol g (H t)) ∧ H 0 = a ∧ H 1 = b

/-- A homotopy certifies the stated property of its endpoint. -/
theorem EllipticCosphereHomotopic.continuous_left
    {a b : CosphereSymbolFunction (E := E) (F := F) g}
    (h : EllipticCosphereHomotopic (r := r) (q := q) g a b) : 
      IsContinuousCosphereSymbol (r := r) (q := q) g a := by
  /- Take the slice at parameter zero of a witnessing jointly continuous
  family, then use its first endpoint equation to recover the original section a. -/
  obtain ⟨H, hH, _, h₀, _⟩ := h
  rw [← h₀]
  exact Continuous.comp hH (continuous_const.prodMk continuous_id)

/-- A homotopy certifies the stated property of its endpoint. -/
theorem EllipticCosphereHomotopic.continuous_right
    {a b : CosphereSymbolFunction (E := E) (F := F) g}
    (h : EllipticCosphereHomotopic (r := r) (q := q) g a b) : 
      IsContinuousCosphereSymbol (r := r) (q := q) g b := by
  /- Take the slice at parameter one of the witnessing jointly continuous
  family. Its last endpoint equation identifies that continuous slice with b. -/
  obtain ⟨H, hH, _, _, h₁⟩ := h
  rw [← h₁]
  exact Continuous.comp hH (continuous_const.prodMk continuous_id)

/-- A homotopy certifies the stated property of its endpoint. -/
theorem EllipticCosphereHomotopic.elliptic_left
    {a b : CosphereSymbolFunction (E := E) (F := F) g}
    (h : EllipticCosphereHomotopic (r := r) (q := q) g a b) : IsEllipticCosphereSymbol g a := by
  /- Evaluate the universal ellipticity condition of a witnessing
  homotopy at zero and substitute the first endpoint equality. No compactness is needed. -/
  obtain ⟨H, _, hH, h₀, _⟩ := h
  rw [← h₀]
  exact hH 0

/-- A homotopy certifies the stated property of its endpoint. -/
theorem EllipticCosphereHomotopic.elliptic_right
    {a b : CosphereSymbolFunction (E := E) (F := F) g}
    (h : EllipticCosphereHomotopic (r := r) (q := q) g a b) : IsEllipticCosphereSymbol g b := by
  /- Evaluate ellipticity of the witnessing homotopy at one, then
  substitute its last endpoint equality. Invertibility is pointwise on the actual unit covectors. -/
  obtain ⟨H, _, hH, _, h₁⟩ := h
  rw [← h₁]
  exact hH 1

/-- The constant homotopy witnesses reflexivity for a continuous elliptic section. -/
theorem EllipticCosphereHomotopic.refl
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (hc : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (he : IsEllipticCosphereSymbol g a) : EllipticCosphereHomotopic (r := r) (q := q) g a a := by
  /- Choose the constant family with value a. Its joint continuity
  follows from hc, ellipticity is he at each parameter, and both endpoint equalities are exact. -/
  refine ⟨fun _ ↦ a, ?_, fun _ ↦ he, rfl, rfl⟩
  exact hc.comp continuous_snd

/-- Reversing the interval gives symmetry of elliptic homotopy. -/
theorem EllipticCosphereHomotopic.symm
    {a b : CosphereSymbolFunction (E := E) (F := F) g}
    (h : EllipticCosphereHomotopic (r := r) (q := q) g a b) : 
      EllipticCosphereHomotopic (r := r) (q := q) g b a := by
  /- Reparameterize a witnessing family by t mapped to one minus t.
  This continuous involution swaps zero and one and preserves pointwise invertibility. -/
  obtain ⟨H, hH, he, h₀, h₁⟩ := h
  refine ⟨fun t ↦ H (unitInterval.symm t), ?_, fun t ↦ he _, ?_, ?_⟩
  · exact Continuous.comp hH
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)
  · simpa only [unitInterval.symm_zero] using h₁
  · simpa only [unitInterval.symm_one] using h₀

/-- Concatenating at a common endpoint gives transitivity. -/
theorem EllipticCosphereHomotopic.trans
    {a b c : CosphereSymbolFunction (E := E) (F := F) g}
    (hab : EllipticCosphereHomotopic (r := r) (q := q) g a b)
      (hbc : EllipticCosphereHomotopic (r := r) (q := q) g b c) :
    EllipticCosphereHomotopic (r := r) (q := q) g a c := by
  /- Traverse the first path on the first half interval and the second
  on the second half, with linear reparameterizations. Their values agree at the
  midpoint b, so the closed-set pasting lemma gives joint continuity. Every slice
  belongs to one of the two elliptic paths. No differentiability at the join is needed. -/
  classical
  obtain ⟨H, hH, heH, hH₀, hH₁⟩ := hab
  obtain ⟨K, hK, heK, hK₀, hK₁⟩ := hbc
  let leftTime (t : unitInterval) : unitInterval :=
    Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))
  let rightTime (t : unitInterval) : unitInterval :=
    Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)
  let L (t : unitInterval) : CosphereSymbolFunction (E := E) (F := F) g :=
    if (t : ℝ) ≤ 1 / 2 then H (leftTime t) else K (rightTime t)
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · -- Closed-set pasting is applied to the actual total-space maps, with the same base.
    have hleft : Continuous leftTime :=
      continuous_projIcc.comp
        (continuous_const.mul continuous_subtype_val)
    have hright : Continuous rightTime :=
      continuous_projIcc.comp
        ((continuous_const.mul continuous_subtype_val).sub continuous_const)
    have h₁ := Continuous.comp hH ((hleft.comp continuous_fst).prodMk continuous_snd)
    have h₂ := Continuous.comp hK ((hright.comp continuous_fst).prodMk continuous_snd)
    have hpaste := h₁.if_le h₂ (continuous_subtype_val.comp continuous_fst)
      continuous_const (fun p hp ↦ by
        have ht : (p.1 : ℝ) = 1 / 2 := hp
        have hl : leftTime p.1 = 1 := by
          dsimp [leftTime]
          rw [ht]
          norm_num
        have hr : rightTime p.1 = 0 := by
          dsimp [rightTime]
          rw [ht]
          norm_num
        change cosphereSymbolTotal g (H (leftTime p.1)) p.2 =
          cosphereSymbolTotal g (K (rightTime p.1)) p.2
        rw [hl, hr, hH₁, hK₀])
    change Continuous (fun p : unitInterval × CosphereBundle g ↦
      cosphereSymbolTotal g (L p.1) p.2)
    apply hpaste.congr
    intro p
    dsimp [L, Function.comp_def]
    split_ifs <;> rfl
  · intro t
    dsimp [L]
    split_ifs
    · exact heH _
    · exact heK _
  · simpa [L, leftTime] using hH₀
  · dsimp [L]
    rw [ite_eq_right (by norm_num)]
    have hr : rightTime 1 = 1 := by
      dsimp [rightTime]
      norm_num
    rw [hr, hK₁]

/-- The auxiliary cotangent metric does not change the homotopy relation. -/
theorem ellipticCosphereHomotopic_metricTransport_iff
    (k : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a b : CosphereSymbolFunction (E := E) (F := F) g) :
    EllipticCosphereHomotopic (r := r) (q := q) k
      (cosphereMetricTransport g k m a) (cosphereMetricTransport g k m b) ↔
      EllipticCosphereHomotopic (r := r) (q := q) g a b := by
  /- Transport a witnessing family with the degree-m radial weight.
  Joint continuity and ellipticity are preserved. For the converse transport back;
  composition and self-transport identities recover both original endpoints exactly. -/
  have transport (g' k' : SmoothCotangentMetric (n := n) (M := M))
      (a' b' : CosphereSymbolFunction (E := E) (F := F) g')
      (h : EllipticCosphereHomotopic (r := r) (q := q) g' a' b') :
      EllipticCosphereHomotopic (r := r) (q := q) k'
        (cosphereMetricTransport g' k' m a') (cosphereMetricTransport g' k' m b') := by
    obtain ⟨H, hH, he, h₀, h₁⟩ := h
    refine ⟨fun t ↦ cosphereMetricTransport g' k' m (H t), ?_, ?_, ?_, ?_⟩
    · exact hH.metricTransport g' k' m H
    · intro t
      exact (isEllipticCosphereSymbol_metricTransport_iff g' k' m (H t)).mpr (he t)
    · exact congrArg (cosphereMetricTransport g' k' m) h₀
    · exact congrArg (cosphereMetricTransport g' k' m) h₁
  constructor
  · intro h
    have hback := transport k g _ _ h
    simpa only [cosphereMetricTransport_comp, cosphereMetricTransport_self] using hback
  · exact transport g k a b

attribute [local instance] smoothCosphereSymbolTopology homogeneousSymbolTopology

include hE hF in
/-- A continuous elliptic homotopy between smooth endpoints admits a relative smooth path. -/
theorem exists_continuous_smoothCosphere_path
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (a b : smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g)
    (hab : EllipticCosphereHomotopic (r := r) (q := q) g a.val b.val) :
    ∃ K : unitInterval → smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g,
      Continuous K ∧ (∀ t, IsEllipticCosphereSymbol g (K t).val) ∧ K 0 = a ∧ K 1 = b := by
  /- Affine interpolation joins any two smooth vertices whose images lie in a
  common elliptic control neighborhood. Along the original continuous path, define
  a relation between times by neighborhoods whose smooth vertices are joined.
  Local interpolation control makes this relation locally valid; smooth density
  supplies a middle vertex for transitivity. Connectedness of the interval then
  joins the exact smooth endpoints, yielding a path continuous in every spatial
  smooth seminorm. The original continuous path is replaced rather than upgraded. -/
  classical
  let S := smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g
  let C := ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g
  let : TopologicalSpace C := continuousCosphereSymbolTopology g
  let ι : S → C := smoothCosphereToContinuous g
  let W : Set S := {u | IsEllipticCosphereSymbol g u.val}
  -- Affine segments of smooth vertices are continuous in every spatial seminorm.
  have segment (u v : S)
      (he : ∀ t : unitInterval,
        IsEllipticCosphereSymbol g (cosphereInterpolation g u.val v.val t)) :
      JoinedIn W u v := by
    let f (t : unitInterval) : S :=
      (((1 - (t : ℝ) : ℝ) : ℂ) • u) + (((t : ℝ) : ℂ) • v)
    have hf : Continuous f := by
      have hp := withSeminorms_homogeneousSymbolTopology (n := n) (r := r) (q := q) E F 0
      let := hp.isTopologicalAddGroup
      let := hp.continuousSMul
      rw [continuous_induced_rng]
      rw [show smoothCosphereExtension (r := r) (q := q) g 0 ∘ f =
          fun t : unitInterval ↦
            (((1 - (t : ℝ) : ℝ) : ℂ) • smoothCosphereExtension g 0 u) +
            (((t : ℝ) : ℂ) • smoothCosphereExtension g 0 v) from ?_]
      · exact ((Complex.continuous_ofReal.comp
          (continuous_const.sub continuous_subtype_val)).smul continuous_const).add
            ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
      · funext t
        apply Subtype.ext
        change cosphereExtension g 0
          ((((1 - (t : ℝ) : ℝ) : ℂ) • u.val) + (((t : ℝ) : ℂ) • v.val)) = _
        rw [cosphereExtension_add, cosphereExtension_smul, cosphereExtension_smul]
        rfl
    refine ⟨{ toFun := f
              continuous_toFun := hf
              source' := ?_
              target' := ?_ }, ?_⟩
    · simp [f]
    · simp [f]
    · exact he
  obtain ⟨H, hH, heH, h₀, h₁⟩ := hab
  let Hc (t : unitInterval) : C :=
    ⟨H t, Continuous.comp hH (continuous_const.prodMk continuous_id)⟩
  have hc : Continuous Hc := (continuous_cosphere_iff g Hc).mpr hH
  /- A local-chain argument implements the finite-subdivision construction without
  choosing derivative-compatible subdivision points. Two times are related when
  suitable neighborhoods of their original values have all smooth vertices joined.
  Density supplies a common smooth middle vertex when two such relations compose. -/
  let R (s t : unitInterval) : Prop :=
    ∃ U V : Set C, IsOpen U ∧ IsOpen V ∧ Hc s ∈ U ∧ Hc t ∈ V ∧
      ∀ u v : S, ι u ∈ U → ι v ∈ V → JoinedIn W u v
  have hlocal (s : unitInterval) : ∀ᶠ t in 𝓝 s, R s t := by
    obtain ⟨U, hU, hsU, hcontrol⟩ :=
      exists_elliptic_convex_neighborhood g (Hc s) (heH s)
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hsU)] with t ht
    refine ⟨U, U, hU, hU, hsU, ht, ?_⟩
    intro u v hu hv
    exact segment u v (hcontrol (ι u) hu (ι v) hv)
  have hsymm : Std.Symm R := ⟨by
    intro s t h
    obtain ⟨U, V, hU, hV, hs, ht, hjoin⟩ := h
    exact ⟨V, U, hV, hU, ht, hs, fun u v hu hv ↦ (hjoin v u hv hu).symm⟩⟩
  have htrans : IsTrans unitInterval R := ⟨by
    intro s t z hst htz
    obtain ⟨U, V, hU, hV, hs, htV, hjoin₁⟩ := hst
    obtain ⟨V', Z, hV', hZ, htV', hz, hjoin₂⟩ := htz
    obtain ⟨w, hw⟩ := exists_smoothCosphere_mem g (Hc t) (V ∩ V')
      (hV.inter hV') ⟨htV, htV'⟩
    refine ⟨U, Z, hU, hZ, hs, hz, ?_⟩
    intro u v hu hv
    exact (hjoin₁ u w hu hw.1).trans (hjoin₂ w v hw.2 hv)⟩
  -- The connected interval has just one class for this locally valid relation.
  let := hsymm
  obtain ⟨U, V, _, _, haU, hbV, hjoin⟩ :=
    PreconnectedSpace.induction₂ R hlocal htrans 0 1
  have ha : ι a ∈ U := by
    have ha₀ : Hc 0 = ι a := Subtype.ext h₀
    rwa [ha₀] at haU
  have hb : ι b ∈ V := by
    have hb₁ : Hc 1 = ι b := Subtype.ext h₁
    rwa [hb₁] at hbV
  have hj := hjoin a b ha hb
  exact ⟨hj.somePath, hj.somePath.continuous, hj.somePath_mem,
    hj.somePath.source, hj.somePath.target⟩

include hE hF in
/-- For smooth endpoints continuous elliptic homotopy is equivalent to a smooth-space path. -/
theorem ellipticCosphereHomotopic_iff_exists_smooth_path
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (a b : smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g) :
    EllipticCosphereHomotopic (r := r) (q := q) g a.val b.val ↔
      ∃ K : unitInterval → smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g,
        Continuous K ∧ (∀ t, IsEllipticCosphereSymbol g (K t).val) ∧ K 0 = a ∧ K 1 = b := by
  /- Forward use the relative approximation theorem. Reverse take
  underlying functions of the smooth-space path and use joint continuity of smooth
  evaluation. Its invertibility and endpoint equations directly witness the homotopy. -/
  constructor
  · exact exists_continuous_smoothCosphere_path g a b
  · rintro ⟨K, hK, he, h₀, h₁⟩
    refine ⟨fun t ↦ (K t).val, ?_, he, ?_, ?_⟩
    · exact isContinuousCosphereFamily_of_continuous g K hK
    · exact congrArg Subtype.val h₀
    · exact congrArg Subtype.val h₁

include hE hF in
/-- A continuous elliptic section is elliptically homotopic to a smooth section. -/
theorem exists_smoothCosphere_homotopic
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (a : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g)
    (ha : IsEllipticCosphereSymbol g a.val) :
    ∃ b : smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g,
      EllipticCosphereHomotopic (r := r) (q := q) g a.val b.val := by
  /- Choose a neighborhood whose pairwise affine interpolations stay elliptic, and
  a smooth approximation inside it. Interpolation from a to that approximation is
  jointly continuous and elliptic throughout, with the exact requested endpoints. -/
  obtain ⟨U, hU, haU, hcontrol⟩ := exists_elliptic_convex_neighborhood g a ha
  obtain ⟨b, hb⟩ := exists_smoothCosphere_mem g a U hU haU
  -- The same approximant and the same control neighborhood give a single exact interpolation.
  refine ⟨b, cosphereInterpolation g a.val b.val, ?_, ?_, ?_, ?_⟩
  · exact isContinuousCosphereFamily_interpolation g a.val b.val a.property
      (IsSmoothCosphereSymbol.continuous g b.property)
  · exact hcontrol a haU (smoothCosphereToContinuous g b) hb
  · exact cosphereInterpolation_zero g a.val b.val
  · exact cosphereInterpolation_one g a.val b.val

include hE hF in
/-- A cosphere homotopy yields a homogeneous smooth-space path with the same off-zero endpoints. -/
theorem exists_continuous_homogeneous_path_of_cosphereHomotopic
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (m : ℝ) (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hab : EllipticCosphereHomotopic (r := r) (q := q) g (cosphereRestriction g a.val)
      (cosphereRestriction g b.val)) :
    ∃ K : unitInterval → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m,
      Continuous K ∧ (∀ t, IsEllipticGlobalSymbol E F (K t).val) ∧
        (∀ x ξ, ξ ≠ 0 → (K 0).val x ξ = a.val x ξ) ∧
        (∀ x ξ, ξ ≠ 0 → (K 1).val x ξ = b.val x ξ) := by
  /- Restrict the smooth homogeneous endpoints to the cosphere and
  apply relative smoothing. Extend the resulting path at the common real degree m,
  using continuity of smooth radial extension and equivalence of ellipticity.
  Homogeneous reconstruction identifies endpoint values off zero only. The original
  zero-section values need not agree with the canonical zero of the extension. -/
  let a₀ := smoothCosphereRestriction (r := r) (q := q) g m a
  let b₀ := smoothCosphereRestriction (r := r) (q := q) g m b
  obtain ⟨K, hK, he, h₀, h₁⟩ := exists_continuous_smoothCosphere_path g a₀ b₀ hab
  -- Extend precisely that path at the original common real degree.
  refine ⟨fun t ↦ smoothCosphereExtension (r := r) (q := q) g m (K t), ?_, ?_, ?_, ?_⟩
  · exact (continuous_smoothCosphereExtension g m).comp hK
  · intro t
    exact (isEllipticGlobalSymbol_cosphereExtension_iff g m (K t).val).mpr (he t)
  · intro x ξ hξ
    change cosphereExtension g m (K 0).val x ξ = a.val x ξ
    rw [h₀]
    exact cosphereExtension_restriction g m a.val a.property.2 x ξ hξ
  · intro x ξ hξ
    change cosphereExtension g m (K 1).val x ξ = b.val x ξ
    rw [h₁]
    exact cosphereExtension_restriction g m b.val b.property.2 x ξ hξ

end AtiyahSinger
