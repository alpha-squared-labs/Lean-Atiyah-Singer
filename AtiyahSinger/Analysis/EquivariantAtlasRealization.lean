/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasEllipticRepresentative
public import AtiyahSinger.Analysis.EquivariantAtlasOperator
public import AtiyahSinger.Analysis.EquivariantAtlasSymbol
public import AtiyahSinger.Analysis.EquivariantPiecewiseRealization

import AtiyahSinger.Analysis.EquivariantAtlasQuantization
import AtiyahSinger.Analysis.EquivariantSymbolHomotopy
import AtiyahSinger.Topology.EquivariantFixedRankCotangentRepresentative

/-!
# Global equivariant realization on locally varying-rank bundles

Public module ID: M0468.

E05: compact Lie groups acting smoothly on compact smooth manifolds admit
smooth homogeneous representatives of every original equivariant cotangent
K class, and equivariant quantization realizes those same symbols by actual
global atlas PDOs. The chosen smooth representative's bundles, actions and class
are retained in the operator realization. Neither connectedness, positive dimension,
a global common rank nor a prescribed trivialization is imposed.

Quantization uses smooth native retracts compatible with the prescribed
atlases. The same inclusion and projection operators recover the original
full principal class. An invariant cutoff is used only for the construction;
the existing two-metric comparison returns the supplied regularization metric.

Sources: SG III.9 pp.211--215 (smooth actions and conjugation averaging),
III.13 Lemma 13.3 and (13.7), pp.245--246 (symbol representation and realization);
ASI I section 2 (the equivariant support group). Equivariant smooth replacement
and the compatible native-retract reduction are project supplements.
Compact-base E05 does not settle the noncompact Schwartz-kernel support/excision
problems of UL03 or the later associated-bundle lifting theorem SG III.13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [MeasurableSpace G] [hGB : BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hMB : BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

include hDim hLie hGC hGT hGB hM hT hSC hC hMB hAction

/-- Equivariant quantization retains the specified invariant homogeneous atlas symbol. -/
theorem exists_equivariant_atlasPseudodifferentialOperator_of_homogeneousSymbol
    {E F : M → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)]
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (σE : EquivariantStructure G E) (σF : EquivariantStructure G F)
    (hσE : σE.IsSmoothAtlas 𝓘(ℝ, VG) A)
    (hσF : σF.IsSmoothAtlas 𝓘(ℝ, VG) B)
    (g : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ)
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a)
    (he : IsEquivariantAtlasSymbol 𝓘(ℝ, VG) σE σF a) :
    ∃ P : AtlasPseudodifferentialOperator A B m,
      P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF ∧
      P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
        (atlasRegularizedSymbol A B g m a hs hh) := by
  -- An invariant radial cutoff makes the same full symbol exactly equivariant.
  obtain ⟨k, hk⟩ := exists_invariant_smoothCotangentMetric (G := G) (n := n) (M := M)
    𝓘(ℝ, VG)
  have hlength (h : G) (x : M) (ξ : CotangentFiber (n := n) x) :
      k.length (h • x) (cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h)
        ⟨x, ξ⟩).snd = k.length x ξ := congrArg Real.sqrt (hk h x ξ ξ)
  let b := atlasRegularizedSymbol A B k m a hs hh
  have hb (h : G) (x : M) (ξ : CotangentFiber (n := n) x) (v : E x) :
      b.val (h • x) (cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h)
        ⟨x, ξ⟩).snd (σE.linearMap h x v) = σF.linearMap h x (b.val x ξ v) := by
    by_cases hξ : ξ = 0
    · -- The cutoff removes the unconstrained original value on the zero section.
      have hz : k.length x ξ = 0 := (k.length_eq_zero_iff x ξ).mpr hξ
      have hleft := (atlasRegularizedSymbolFunction_cutoff k a).1 (h • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h)
          ⟨x, ξ⟩).snd (by rw [hlength, hz]; norm_num)
      have hright := (atlasRegularizedSymbolFunction_cutoff k a).1 x ξ
        (by rw [hz]; norm_num)
      change atlasRegularizedSymbolFunction k a _ _ _ =
        σF.linearMap h x (atlasRegularizedSymbolFunction k a x ξ v)
      rw [hleft, hright, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
    · change ((highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1)
          (k.length (h • x) _)) : ℂ) • a (h • x) _ (σE.linearMap h x v)) = _
      rw [hlength, he h x ξ hξ v]
      exact (σF.linearMap h x).map_smul _ _ |>.symm
  obtain ⟨P, hP, hp⟩ := exists_equivariant_atlasPseudodifferentialOperator_of_fullSymbol
    A B σE σF hσE hσF m b hb
  refine ⟨P, hP, hp.trans ?_⟩
  -- Changing back to the supplied metric preserves precisely the original principal class.
  exact (atlasRegularizedSymbol_principalClass_eq_iff A B k g m a a hs hh hs hh).mpr
    (fun _ _ _ ↦ rfl)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
-- Preserve the K class through smooth replacement, radial degree change and atlas conversion.
/-- Every original equivariant cotangent K class has a global smooth atlas symbol. -/
theorem exists_equivariant_smooth_atlas_elliptic_representative (m : ℝ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ u : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      ∃ E F : FiniteBundle M,
      ∃ A : SmoothComplexBundleAtlas (n := n) E.Fiber,
      ∃ B : SmoothComplexBundleAtlas (n := n) F.Fiber,
      ∃ (σE : EquivariantStructure G E.Fiber) (σF : EquivariantStructure G F.Fiber),
        σE.IsSmoothAtlas 𝓘(ℝ, VG) A ∧ σF.IsSmoothAtlas 𝓘(ℝ, VG) B ∧
        ∃ a : AtlasSymbolFunction (n := n) E.Fiber F.Fiber,
        ∃ hs : IsSmoothOffZeroAtlasSymbol A B a,
        ∃ hh : IsHomogeneousAtlasSymbol m a,
        ∃ hi : IsEllipticAtlasSymbol a,
        ∃ he : IsEquivariantAtlasSymbol 𝓘(ℝ, VG) σE σF a,
          equivariantAtlasSymbolKClass 𝓘(ℝ, VG) E F A B σE σF a hs hi he = u :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro u
  by_cases hn : n = 0
  · -- The exterior is empty; keep the original two equivariant bundles without stabilizing.
    obtain ⟨E, F, σE, σF, a, haEq, ha, _, hclass⟩ :=
      exists_equivariant_homogeneous_cotangent_representative 𝓘(ℝ, VG) u
    obtain ⟨A₀, hA₀⟩ : ∃ A : SmoothComplexBundleAtlas.{0} (n := n) E.Fiber,
        σE.IsSmoothAtlas 𝓘(ℝ, VG) A := σE.exists_smoothAtlas (VG := VG) (n := n)
    obtain ⟨B₀, hB₀⟩ : ∃ B : SmoothComplexBundleAtlas.{0} (n := n) F.Fiber,
        σF.IsSmoothAtlas 𝓘(ℝ, VG) B := σF.exists_smoothAtlas (VG := VG) (n := n)
    let A : SmoothComplexBundleAtlas (n := n) E.Fiber := {
      Index := ULift A₀.Index
      rank i := A₀.rank i.down
      chart i := A₀.chart i.down
      covers x := by
        obtain ⟨i, hi⟩ := A₀.covers x
        exact ⟨⟨i⟩, hi⟩
      linear i := A₀.linear i.down
      contMDiffOn_coordChange i j := A₀.contMDiffOn_coordChange i.down j.down }
    let B : SmoothComplexBundleAtlas (n := n) F.Fiber := {
      Index := ULift B₀.Index
      rank i := B₀.rank i.down
      chart i := B₀.chart i.down
      covers x := by
        obtain ⟨i, hi⟩ := B₀.covers x
        exact ⟨⟨i⟩, hi⟩
      linear i := B₀.linear i.down
      contMDiffOn_coordChange i j := B₀.contMDiffOn_coordChange i.down j.down }
    have hA : σE.IsSmoothAtlas 𝓘(ℝ, VG) A := by
      intro i j k
      exact hA₀ i.down j.down k
    have hB : σF.IsSmoothAtlas 𝓘(ℝ, VG) B := by
      intro i j k
      exact hB₀ i.down j.down k
    let b : AtlasSymbolFunction (n := n) E.Fiber F.Fiber := 0
    have hs : IsSmoothOffZeroAtlasSymbol A B b := by
      intro c hc i j
      have he : (atlasSymbolChartDomain A B c i j ×ˢ
          {ξ : EuclideanSpace ℝ (Fin n) | ξ ≠ 0}) = ∅ := by
        subst n
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hz.2 (Subsingleton.elim _ _)
      rw [he]
      exact contDiffOn_empty
    have hh : IsHomogeneousAtlasSymbol m b := by
      intro x ξ hξ
      exact (hξ (cotangentFiber_eq_zero_of_dim_zero hn x ξ)).elim
    have hi : IsEllipticAtlasSymbol b := by
      intro x ξ hξ
      exact (hξ (cotangentFiber_eq_zero_of_dim_zero hn x ξ)).elim
    have he : IsEquivariantAtlasSymbol 𝓘(ℝ, VG) σE σF b := by
      intro g x ξ hξ
      exact (hξ (cotangentFiber_eq_zero_of_dim_zero hn x ξ)).elim
    refine ⟨E, F, A, B, σE, σF, hA, hB, b, hs, hh, hi, he, ?_⟩
    have htriple : atlasEllipticSymbolTriple A B b hs hi = a := by
      rcases a with ⟨K, hK, α⟩
      dsimp only at ha
      subst K
      change CompactSupportTriple.mk cotangentZeroSet _ _ =
        CompactSupportTriple.mk cotangentZeroSet _ _
      congr 1
      apply Iso.ext
      intro z
      exact (z.property (cotangentFiber_eq_zero_of_dim_zero hn z.val.proj z.val.snd)).elim
    -- The exact boundary equality retains both original actions before passing to K theory.
    convert hclass using 1
    unfold equivariantAtlasSymbolKClass equivariantAtlasSymbolTriple
    congr 2
  · -- One common equivariant complement gives fixed rank without changing the original class.
    obtain ⟨E₀, F₀, r, hrE, hrF, ρE, ρF, a, haEq, ha, _, hclass⟩ :=
      exists_fixedRank_equivariant_homogeneous_cotangent_representative
        𝓘(ℝ, VG) (Nat.pos_of_ne_zero hn) u
    obtain ⟨E, F, _, _, σE, σF, hσE, hσF, e, f, he, hf,
        hc, s, hi, hseq, hbEq, hH, hsame⟩ :=
      a.exists_equivariant_smooth_cotangent_replacement (VG := VG)
        E₀ F₀ r r hrE hrF ρE ρF ha haEq
    let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    -- A positive invariant radial factor changes degree off zero while preserving equivariance.
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
    -- The affine-degree family stays invertible off zero and uses one zero-section control.
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
    let A₁ := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
    let B₁ := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
    let A₀ := A₁.finiteSubatlas
    let B₀ := B₁.finiteSubatlas
    let A : SmoothComplexBundleAtlas (n := n) E.Fiber := {
      Index := ULift A₀.Index
      rank i := A₀.rank i.down
      chart i := A₀.chart i.down
      covers x := by
        obtain ⟨i, hi⟩ := A₀.covers x
        exact ⟨⟨i⟩, hi⟩
      linear i := A₀.linear i.down
      contMDiffOn_coordChange i j := A₀.contMDiffOn_coordChange i.down j.down }
    let B : SmoothComplexBundleAtlas (n := n) F.Fiber := {
      Index := ULift B₀.Index
      rank i := B₀.rank i.down
      chart i := B₀.chart i.down
      covers x := by
        obtain ⟨i, hi⟩ := B₀.covers x
        exact ⟨⟨i⟩, hi⟩
      linear i := B₀.linear i.down
      contMDiffOn_coordChange i j := B₀.contMDiffOn_coordChange i.down j.down }
    have hA : σE.IsSmoothAtlas 𝓘(ℝ, VG) A := by
      intro i j k
      exact σE.isSmoothAtlas_native 𝓘(ℝ, VG) hσE _ _ k
    have hB : σF.IsSmoothAtlas 𝓘(ℝ, VG) B := by
      intro i j k
      exact σF.isSmoothAtlas_native 𝓘(ℝ, VG) hσF _ _ k
    let b' := nativeAtlasSymbolFunction b.val
    have hprops := nativeAtlasSymbolFunction_homogeneous_properties m b.val
      b.property.1 b.property.2 hbi
    have hs : IsSmoothOffZeroAtlasSymbol A B b' := by
      intro c hc i j
      exact hprops.1 c hc _ _
    have he' : IsEquivariantAtlasSymbol 𝓘(ℝ, VG) σE σF b' := by
      intro h x ξ hξ v
      have heq := ellipticSymbolTriple_isEquivariant 𝓘(ℝ, VG) σE σF
        b.val b.property.1.continuous hbi hbeq
      let z : PuncturedCotangentBundle (n := n) (M := M) := ⟨⟨x, ξ⟩, hξ⟩
      let hz : PuncturedCotangentBundle (n := n) (M := M) :=
        ⟨h • z.val, fun hzero ↦ z.property ((heq.invariant_control h z.val).mp hzero)⟩
      exact (ellipticSymbolTriple_boundary_apply b.val b.property.1.continuous hbi hz _).symm.trans
        ((heq.boundary_intertwines h z v).trans
          (congrArg (σF.linearMap h x)
            (ellipticSymbolTriple_boundary_apply b.val b.property.1.continuous hbi z v)))
    refine ⟨FiniteBundle.ofFamily E.Fiber, FiniteBundle.ofFamily F.Fiber,
      A, B, σE, σF, hA, hB, b', hs, hprops.2.1, hprops.2.2, he', ?_⟩
    -- Native-to-atlas conversion preserves every boundary vector and the two pulled actions.
    calc
      equivariantAtlasSymbolKClass 𝓘(ℝ, VG)
          (FiniteBundle.ofFamily E.Fiber) (FiniteBundle.ofFamily F.Fiber)
          A B σE σF b' hs hprops.2.2 he' =
          equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF m b hbi hbeq := by
        have htriple : atlasEllipticSymbolTriple A B b' hs hprops.2.2 =
            ellipticSymbolTriple b.val b.property.1.continuous hbi := by
          change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
            CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
          congr 1
          apply Iso.ext
          intro z
          apply LinearEquiv.ext
          intro v
          exact (ellipticSymbolBoundary_apply b.val b.property.1.continuous hbi z v).symm
        unfold equivariantAtlasSymbolKClass equivariantAtlasSymbolTriple
          equivariantHomogeneousSymbolKClass
        congr 2
      _ = equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF 0 s hi hseq := hdegree
      _ = u := hsame.symm.trans hclass

/-- A single global equivariant atlas PDO realizes every original equivariant cotangent class. -/
theorem exists_equivariant_atlas_elliptic_pseudodifferential_representative
    (g : SmoothCotangentMetric (n := n) (M := M)) (m : ℝ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ u : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      ∃ E F : FiniteBundle M,
      ∃ A : SmoothComplexBundleAtlas (n := n) E.Fiber,
      ∃ B : SmoothComplexBundleAtlas (n := n) F.Fiber,
      ∃ (σE : EquivariantStructure G E.Fiber) (σF : EquivariantStructure G F.Fiber),
      ∃ hσE : σE.IsSmoothAtlas 𝓘(ℝ, VG) A,
      ∃ hσF : σF.IsSmoothAtlas 𝓘(ℝ, VG) B,
      ∃ a : AtlasSymbolFunction (n := n) E.Fiber F.Fiber,
      ∃ hs : IsSmoothOffZeroAtlasSymbol A B a,
      ∃ hh : IsHomogeneousAtlasSymbol m a,
      ∃ hi : IsEllipticAtlasSymbol a,
      ∃ he : IsEquivariantAtlasSymbol 𝓘(ℝ, VG) σE σF a,
      ∃ P : AtlasPseudodifferentialOperator A B m,
        P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF ∧
        P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
          (atlasRegularizedSymbol A B g m a hs hh) ∧
        equivariantAtlasSymbolKClass 𝓘(ℝ, VG) E F A B σE σF a hs hi he = u := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro u
  -- Retain exactly the symbol, both actions and both bundles of the original K representative.
  obtain ⟨E, F, A, B, σE, σF, hσE, hσF, a, hs, hh, hi, he, hclass⟩ :=
    exists_equivariant_smooth_atlas_elliptic_representative (G := G) (VG := VG) m u
  obtain ⟨P, hP, hp⟩ :=
    exists_equivariant_atlasPseudodifferentialOperator_of_homogeneousSymbol
      A B σE σF hσE hσF g m a hs hh he
  exact ⟨E, F, A, B, σE, σF, hσE, hσF, a, hs, hh, hi, he, P, hP, hp, hclass⟩

end AtiyahSinger
