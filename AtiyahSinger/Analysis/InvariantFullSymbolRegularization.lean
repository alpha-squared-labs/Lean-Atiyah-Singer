/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Analysis.EquivariantFullSymbolCovariance
public import AtiyahSinger.Analysis.EquivariantSymbolKClass
public import AtiyahSinger.Analysis.GlobalFullSymbolEllipticity

/-!
# Invariant full regularization of the same homogeneous symbol

Public module ID: M0762.

The supplied invariant cotangent metric defines a scalar cutoff on the
original native homogeneous symbol. The resulting full symbol is invariant
at every covector, including zero, agrees with the given field beyond unit
metric length, and represents its original principal class. No invariant
quantization presentation is selected or assumed.

This supplies the actual fixed full symbol used by the associated-sphere
cutoff construction. Its later quantization may differ by the retained
lower-order operator; that difference is not assumed smoothing.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in

/-- Invariant radial regularization keeps the original homogeneous tail and principal class. -/
theorem exists_invariant_fullSymbol_regularization (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val)
    (he : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ = a.val x ξ)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hg : ∀ (h : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (h • x) (cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h)
          ⟨x, ξ⟩).snd = g.length x ξ) :
    ∃ b : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
      (∀ x ξ, b.val x ξ =
        (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ) •
          a.val x ξ) ∧
      (∀ h : G, equivariantGlobalSymbolLinearMap IG σ τ h b.val = b.val) ∧
      (∀ x ξ, 1 ≤ g.length x ξ → b.val x ξ = a.val x ξ) ∧
      IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val ∧
      ∀ R : QuantizationPresentation (n := n) (r := r) (q := q) E F,
        globalPrincipalSymbolClass E F m b = globalPrincipalSymbolClass E F m
          (R.regularizedSymbol m a.val a.property.1 a.property.2) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  let p : GlobalSymbolFunction (n := n) E F := fun x ξ ↦
    (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (g.length x ξ)) : ℂ) • a.val x ξ
  have hprops := nativeAtlasSymbolFunction_homogeneous_properties m a.val
    a.property.1 a.property.2 hi
  let aReg := atlasRegularizedSymbol A B g m (nativeAtlasSymbolFunction a.val)
    hprops.1 hprops.2.1
  have hp : IsGlobalSymbol (n := n) (r := r) (q := q) E F m p :=
    (isAtlasGlobalSymbol_native_iff m p).mp aReg.property
  let b : globalSymbolSpace (n := n) (r := r) (q := q) E F m := ⟨p, hp⟩
  have hzero (x : M) (ξ : CotangentFiber (n := n) x) (hξ : g.length x ξ ≤ 1 / 2) :
      b.val x ξ = 0 := by
    ext v
    exact LinearMap.congr_fun
      ((atlasRegularizedSymbolFunction_cutoff g (nativeAtlasSymbolFunction a.val)).1 x ξ hξ) v
  have hhigh (x : M) (ξ : CotangentFiber (n := n) x) (hξ : 1 ≤ g.length x ξ) :
      b.val x ξ = a.val x ξ := by
    ext v
    exact LinearMap.congr_fun
      ((atlasRegularizedSymbolFunction_cutoff g (nativeAtlasSymbolFunction a.val)).2 x ξ hξ) v
  -- The original homogeneous boundary provides the moving-fiber square away from zero.
  have hcov (h : G) (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) (v : E x) :
      a.val (h • x) (cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h)
          ⟨x, ξ⟩).snd (σ.linearMap h x v) =
          τ.linearMap h x (a.val x ξ v) := by
    let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    have htr := ellipticSymbolTriple_isEquivariant IG σ τ
      a.val a.property.1.continuous hi he
    let z : PuncturedCotangentBundle (n := n) (M := M) := ⟨⟨x, ξ⟩, hξ⟩
    let hz : PuncturedCotangentBundle (n := n) (M := M) :=
      ⟨h • z.val, fun hzero ↦ z.property ((htr.invariant_control h z.val).mp hzero)⟩
    exact (ellipticSymbolTriple_boundary_apply a.val a.property.1.continuous hi hz _).symm.trans
      ((htr.boundary_intertwines h z v).trans
        (congrArg (τ.linearMap h x)
          (ellipticSymbolTriple_boundary_apply a.val a.property.1.continuous hi z v)))
  have hfixed : ∀ h : G, equivariantGlobalSymbolLinearMap IG σ τ h b.val = b.val := by
    have hfix := (equivariantGlobalSymbolLinearMap_eq_iff_forall IG σ τ b.val).mpr (by
      intro h x ξ v
      by_cases hξ : ξ = 0
      · have hz : g.length x ξ = 0 := (g.length_eq_zero_iff x ξ).mpr hξ
        have hleft := hzero (h • x) (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h) ⟨x, ξ⟩).snd
          (by rw [hg, hz]; norm_num)
        have hright := hzero x ξ (by rw [hz]; norm_num)
        erw [hleft, hright]
        simp only [zero_apply, map_zero]
      · change ((highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1)
            (g.length (h • x) _)) : ℂ) • a.val (h • x) _ (σ.linearMap h x v)) = _
        rw [hg, hcov h x ξ hξ v]
        exact (τ.linearMap h x).map_smul _ _ |>.symm)
    intro h
    funext x ξ
    exact hfix h x ξ
  -- The scalar cutoff and every original presentation differ by an actual lower-order symbol.
  have hclass (R : QuantizationPresentation (n := n) (r := r) (q := q) E F) :
      globalPrincipalSymbolClass E F m b = globalPrincipalSymbolClass E F m
        (R.regularizedSymbol m a.val a.property.1 a.property.2) := by
    have hcompare := atlasRegularizedSymbol_principalClass_native
      g R m a.val a.property.1 a.property.2 hi
    have hd := (atlasGlobalPrincipalSymbolClass_eq_iff A B m aReg
      (nativeAtlasGlobalSymbol m (R.regularizedSymbol m a.val a.property.1 a.property.2))).mp
        hcompare
    exact (globalPrincipalSymbolClass_eq_iff E F m b
      (R.regularizedSymbol m a.val a.property.1 a.property.2)).mpr
        ((isAtlasGlobalSymbol_native_iff (m - 1) (p - R.regularizedSymbolFunction a.val)).mp hd)
  obtain ⟨R⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := q) (E := E) (F := F)
  have hell : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val :=
    (isEllipticFullGlobalSymbol_iff_of_class_eq b _ (hclass R)).mpr
      ((isEllipticFullGlobalSymbol_regularizedSymbol_iff R m a.val
        a.property.1 a.property.2).mpr hi)
  exact ⟨b, fun _ _ ↦ rfl, hfixed, hhigh, hell, hclass⟩

end AtiyahSinger
