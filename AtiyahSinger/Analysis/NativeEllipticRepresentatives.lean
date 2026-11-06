/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasEllipticRepresentative
public import AtiyahSinger.Analysis.ContinuousEllipticSmoothing
public import AtiyahSinger.Analysis.EquivariantAtlasRealization
public import AtiyahSinger.Analysis.EquivariantSymbolHomotopy
public import AtiyahSinger.Geometry.FixedRankSmoothModel
public import AtiyahSinger.Topology.EquivariantFixedRankCotangentRepresentative
public import AtiyahSinger.Topology.FixedRankCotangentRepresentative

/-!
# Native elliptic representatives in positive cotangent dimension

Public module ID: M0808.

Positive dimension allows the same stabilizing complement on both sides of
an elliptic cotangent triple, hence fixed global fiber ranks without assuming
that the base is connected. Smooth replacement and radial extension retain
the original class while supplying the native bundles used by the associated
sphere index construction.

The equivariant version also retains its original smooth bundle actions and
full representation-valued K class. These native witnesses are compatible
with atlas conversion. Dimension zero requires the separate finite clopen
reduction and is not asserted here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

section Ordinary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

/-- Positive cotangent dimension supplies a native representative of the original K class. -/
theorem exists_smooth_elliptic_representative_of_pos (hn : 0 < n)
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) (m : ℝ) :
    ∃ E F : SmoothFiniteComplexBundle (n := n) M,
      ∃ a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber m,
      ∃ hi : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val,
        homogeneousSymbolKClass m a hi = u := by
  classical
  -- Stabilize the original two bundles by the same complement before smooth replacement.
  obtain ⟨E, F, r, hE, hF, a, ha, hhom, hclass⟩ :=
    exists_fixedRank_homogeneous_cotangent_representative hn u
  obtain ⟨V, _, ⟨e⟩⟩ := exists_smooth_model_of_rank (n := n) (E := E.Fiber) r hE
  obtain ⟨W, _, ⟨f⟩⟩ := exists_smooth_model_of_rank (n := n) (E := F.Fiber) r hF
  let := modelTopology (EuclideanSpace ℂ (Fin V.rank)) V.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin W.rank)) W.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin V.rank)) V.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin W.rank)) W.Fiber
  let πM := cotangentProjection (n := n) (M := M)
  let d := a.congr (e.pullback πM) (f.pullback πM)
  have hd : d.control = cotangentZeroSet := ha
  have hdRay (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ) (ht : 0 < t)
      (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ d.controlᶜ)
      (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ d.controlᶜ) :
      d.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
        d.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ := by
    apply LinearEquiv.ext
    intro v
    change f.linearEquiv x
      (a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ ((e.linearEquiv x).symm v)) =
      f.linearEquiv x
        (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ ((e.linearEquiv x).symm v))
    rw [hhom x ξ t ht hξ htξ]
    rfl
  -- Smooth the same transported boundary on the cosphere and extend with the requested degree.
  obtain ⟨b, hi, hb⟩ := exists_smooth_homogeneousSymbol_of_continuousTriple V W m d hd hdRay
  exact ⟨V, W, b, hi, hb.trans ((a.compactSupportClass_congr _ _).trans hclass)⟩

end Ordinary

section Equivariant

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

include hDim hLie hGC hGT hM hT hSC hC hAction

set_option maxHeartbeats 1600000 in
-- Normalize the common equivariant stabilization retaining the original K class.
/-- The original equivariant K class has native smooth elliptic data in positive dimension. -/
theorem exists_equivariant_smooth_elliptic_representative_of_pos (hn : 0 < n) (m : ℝ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ u : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      ∃ E F : SmoothFiniteComplexBundle (n := n) M,
        letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
        ∃ (σE : EquivariantStructure G E.Fiber) (σF : EquivariantStructure G F.Fiber),
          σE.IsSmooth (n := n) (r := E.rank) 𝓘(ℝ, VG) ∧
          σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
          ∃ a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
            E.Fiber F.Fiber m,
            ∃ hi : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val,
              ∃ he : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
                equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF g a.val x ξ = a.val x ξ,
                equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF m a hi he = u :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro u
  -- The common equivariant stabilization retains precisely the original class.
  obtain ⟨E₀, F₀, r, hrE, hrF, ρE, ρF, a, haEq, ha, _, hclass⟩ :=
    exists_fixedRank_equivariant_homogeneous_cotangent_representative
      𝓘(ℝ, VG) hn u
  obtain ⟨E, F, _, _, σE, σF, hσE, hσF, _e, _f, _he, _hf,
      _hc, s, hi, hseq, hbEq, _hH, hsame⟩ :=
    a.exists_equivariant_smooth_cotangent_replacement (VG := VG)
      E₀ F₀ r r hrE hrF ρE ρF ha haEq
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  -- A positive invariant radial factor changes degree while preserving equivariance.
  obtain ⟨g, hinner⟩ :=
    exists_invariant_smoothCotangentMetric (G := G) (n := n) (M := M) 𝓘(ℝ, VG)
  have hlength (h : G) (x : M) (ξ : CotangentFiber (n := n) x) :
      g.length (h • x) (h • (⟨x, ξ⟩ : CotangentTotalSpace)).snd = g.length x ξ :=
    congrArg Real.sqrt (hinner h x ξ ξ)
  let cs := smoothCosphereRestriction g 0 s
  let b := smoothCosphereExtension g m cs
  have hcs : IsEllipticCosphereSymbol g cs.val :=
    (isEllipticCosphereSymbol_restriction_iff g 0 s.val s.property.2).mpr hi
  have hbi : IsEllipticGlobalSymbol E.Fiber F.Fiber b.val :=
    (isEllipticGlobalSymbol_cosphereExtension_iff g m cs.val).mpr hcs
  have hformula (d : ℝ) (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      cosphereExtension g d cs.val x ξ =
        ((g.length x ξ ^ d : ℝ) : ℂ) • s.val x ξ := by
    have hzero := cosphereExtension_restriction g 0 s.val s.property.2 x ξ hξ
    rw [cosphereExtension_of_ne_zero g 0 _ x ξ hξ] at hzero
    simp only [Real.rpow_zero, Complex.ofReal_one, one_smul] at hzero
    rw [cosphereExtension_of_ne_zero g d _ x ξ hξ]
    exact congrArg (fun L : E.Fiber x →L[ℂ] F.Fiber x ↦
      ((g.length x ξ ^ d : ℝ) : ℂ) • L) hzero
  have hshift (d : ℝ) (h : G) (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF h
        (cosphereExtension g d cs.val) x ξ = cosphereExtension g d cs.val x ξ := by
    let z : CotangentTotalSpace (n := n) (M := M) := ⟨x, ξ⟩
    let inverseLift := cotangentDiffeomorphMap
      (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h).symm
    have hinverse : inverseLift z = h⁻¹ • z := by
      dsimp only [inverseLift]
      rw [Diffeomorph.smul_symm]
      rfl
    have hne : (inverseLift z).snd ≠ 0 := by
      rw [hinverse]
      exact fun hz ↦ hξ ((hbEq.invariant_control h⁻¹ z).mp hz)
    have hlen : g.length (h⁻¹ • x) (inverseLift z).snd = g.length x ξ := by
      rw [hinverse]
      exact hlength h⁻¹ x ξ
    let transport : ∀ {x y : M}, x = y → F.Fiber x →L[ℂ] F.Fiber y :=
      fun {x y} hxy ↦ by
        subst y
        exact ContinuousLinearMap.id ℂ (F.Fiber x)
    ext v
    change transport (smul_inv_smul h x)
      (σF.linearMap h (h⁻¹ • x)
        (cosphereExtension g d cs.val (h⁻¹ • x) (inverseLift z).snd
          (σE.linearMap h⁻¹ x v))) = cosphereExtension g d cs.val x ξ v
    erw [hformula d (h⁻¹ • x) (inverseLift z).snd hne, hformula d x ξ hξ]
    simp only [smul_apply, map_smul, hlen]
    exact congrArg (fun w : F.Fiber x ↦ ((g.length x ξ ^ d : ℝ) : ℂ) • w)
      (congrArg (fun L : E.Fiber x →L[ℂ] F.Fiber x ↦ L v) (hseq h x ξ hξ))
  have hbeq := hshift m
  -- The actual affine-degree family stays invertible and has one zero-section control.
  have hdegree : equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF m b hbi hbeq =
      equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF 0 s hi hseq := by
    apply equivariantHomogeneousSymbolKClass_eq_of_family 𝓘(ℝ, VG) σE σF m 0
      b s hbi hi hbeq hseq (cosphereDegreeFamily g m 0 cs.val)
      (isContinuousOffZeroSymbolFamily_degree g m 0 cs.val cs.property.continuous)
      (isEllipticGlobalSymbol_degree g m 0 cs.val hcs)
    · intro t h x ξ hξ
      exact hshift _ h x ξ hξ
    · intro x ξ _
      exact congrArg (fun L : GlobalSymbolFunction (n := n) E.Fiber F.Fiber ↦ L x ξ)
        (cosphereDegreeFamily_zero g m 0 cs.val)
    · intro x ξ hξ
      rw [cosphereDegreeFamily_one]
      exact cosphereExtension_restriction g 0 s.val s.property.2 x ξ hξ
  exact ⟨E, F, σE, σF, hσE, hσF, b, hbi, hbeq,
    hdegree.trans (hsame.symm.trans hclass)⟩

end Equivariant

end AtiyahSinger
