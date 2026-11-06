/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleIsoEllipticity
public import AtiyahSinger.Analysis.AtlasFullSymbolKClassTransport
public import AtiyahSinger.Analysis.AtlasNativePrincipalConjugate
public import AtiyahSinger.Analysis.FullSymbolAnalyticIndex
public import AtiyahSinger.Geometry.AtlasNativeModel

/-!
# The original atlas full-symbol index on compatible native bundle models

Public module ID: M2311.

The prescribed constant-rank atlases produce native models and smooth bundle
isomorphisms internally. The existing full-principal conjugation theorem keeps
the original operator, its complete symbol, both smooth section maps and its
index in one tuple. These very bundle isomorphisms also identify the original
full-symbol compact-support K class with that of the same native symbol.

The native evaluation from M2310 then computes the original atlas operator's
index. No homogeneous representative, auxiliary cotangent metric, prescribed
native model, inverse estimate or desired index equality is a premise. The
constant-rank condition is used only to produce these native models; the next
componentwise assembly uses this theorem on the original clopen rank pieces.

Sources: SG III.13.2 and (13.1), with the explicit atlas/native model comparison
as a project supplement. SG means H. Blaine Lawson, Jr. and Marie-Louise
Michelsohn, *Spin Geometry* (Princeton University Press, 1989). The source
operator and symbol are general full symbols, rather than the classical proof
subclass introduced in SG (13.5).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
/-- Compatible native models evaluate the same general full symbol of the original atlas PDO. -/
theorem AtlasPseudodifferentialOperator.analyticIndexOfComponents_fullSymbolKClass_of_constant_rank
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
    (r q : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r)
    (hq : ∀ x, Module.finrank ℂ (F x) = q)
    (a : atlasGlobalSymbolSpace A B m)
    (ha : IsEllipticFullAtlasSymbol A B m a.val)
    (hP : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m a) :
    analyticIndexOfComponents μ (atlasFullSymbolKClass A B a ha) = P.toLinearMap.index := by
  classical
  /- Produce compatible native models from these very prescribed atlases.
  Their smooth forward and inverse maps keep the original fiber universes. -/
  obtain ⟨N₀, _, hN₀⟩ := A.exists_native_model_with_atlasMaps r hr
  obtain ⟨N₁, _, hN₁⟩ := B.exists_native_model_with_atlasMaps q hq
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  obtain ⟨e, he, hei⟩ := hN₀
  obtain ⟨f, hf, hfi⟩ := hN₁
  let C := nativeSmoothComplexBundleAtlas (n := n) (r := N₀.rank) N₀.Fiber
  let D := nativeSmoothComplexBundleAtlas (n := n) (r := N₁.rank) N₁.Fiber
  /- One existing conjugation tuple transports the arbitrary full a and the
  actual P action, with the same e/f and the exact original smooth index. -/
  obtain ⟨pn, Pn, hvalue, _haction, hprincipal, hindex⟩ :=
    P.exists_native_conjugate_principalSymbol (μ := μ) a hP N₀ N₁
      e f he hei hf hfi
  have hnativeValue : (nativeAtlasGlobalSymbol m pn).val =
      fun x ξ ↦ (f.toHom.linearMap x).comp
        ((a.val x ξ).comp (e.symm.toHom.linearMap x)) := by
    funext x ξ
    exact hvalue x ξ
  -- Full ellipticity uses precisely these smooth inverse factors and original frames.
  have haNative : IsEllipticFullAtlasSymbol C D m (nativeAtlasGlobalSymbol m pn).val := by
    rw [hnativeValue]
    exact ha.bundleIso e f he hfi
  have hpn : IsEllipticFullGlobalSymbol (r := N₀.rank) (q := N₁.rank)
      N₀.Fiber N₁.Fiber m pn.val :=
    (isEllipticFullAtlasSymbol_native_iff m pn.val).mp haNative
  have hiPn : Pn.IsElliptic := ⟨pn, hprincipal, hpn⟩
  /- The same boundary square identifies the actual K class. Its native
  comparison forgets only the continuity certificate of that same pn. -/
  have hclass : atlasFullSymbolKClass A B a ha = fullSymbolKClass pn hpn := by
    calc
      atlasFullSymbolKClass A B a ha =
          atlasFullSymbolKClass C D (nativeAtlasGlobalSymbol m pn) haNative := by
        apply atlasFullSymbolKClass_eq_of_bundleIso e f a (nativeAtlasGlobalSymbol m pn)
          ha haNative
        intro x ξ v
        have h := LinearMap.congr_fun (hvalue x ξ) (e.linearEquiv x v)
        change pn.val x ξ (e.linearEquiv x v) =
          f.linearEquiv x (a.val x ξ ((e.linearEquiv x).symm (e.linearEquiv x v))) at h
        rw [LinearEquiv.symm_apply_apply] at h
        exact h.symm
      _ = fullSymbolKClass pn hpn := atlasFullSymbolKClass_native pn hpn
  -- Evaluate the same original native action and return through its retained index equality.
  have hPnClass : Pn.fullSymbolKClass hiPn = fullSymbolKClass pn hpn :=
    Pn.fullSymbolKClass_eq_of_principalSymbol_eq hiPn pn hprincipal hpn
  calc
    analyticIndexOfComponents μ (atlasFullSymbolKClass A B a ha) =
        analyticIndexOfComponents μ (fullSymbolKClass pn hpn) :=
      congrArg (analyticIndexOfComponents μ) hclass
    _ = analyticIndexOfComponents μ (Pn.fullSymbolKClass hiPn) :=
      congrArg (analyticIndexOfComponents μ) hPnClass.symm
    _ = Pn.toLinearMap.index := Pn.analyticIndexOfComponents_fullSymbolKClass hiPn
    _ = P.toLinearMap.index := hindex

end AtiyahSinger
