/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolKClassHomotopy
public import AtiyahSinger.Analysis.AtlasFullSymbolParametrix

/-!
# The intrinsic full-symbol class of an original elliptic atlas operator

Public module ID: M2313.

The original ellipticity predicate supplies a complete representative of the
actual principal quotient. M2299 constructs its genuine compact-support K class
on the original cotangent pullbacks. M2301 proves independence of the complete
representative, so the class below is exactly that of every prescribed elliptic
representative of the same original operator.

The atlases, fiber vectors and locally varying ranks remain unchanged. The
compact control and its metric are produced by the existing class construction.

Sources: SG III.13, formula (13.1), and I.9.26, with the original finite-atlas
construction as a project supplement. SG means H. Blaine Lawson, Jr. and
Marie-Louise Michelsohn, *Spin Geometry* (Princeton University Press, 1989).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

namespace AtlasPseudodifferentialOperator

variable {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)

/-- The standard symbol K class supplied by the original operator's full ellipticity. -/
def fullSymbolKClass (hi : P.IsElliptic) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  atlasFullSymbolKClass A B (Classical.choose hi) (Classical.choose_spec hi).2

/-- Every complete elliptic representative of this same principal quotient gives that class. -/
theorem fullSymbolKClass_eq_of_principalSymbol_eq (hi : P.IsElliptic)
    (a : atlasGlobalSymbolSpace A B m)
    (hPa : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m a)
    (ha : IsEllipticFullAtlasSymbol A B m a.val) :
    P.fullSymbolKClass hi = atlasFullSymbolKClass A B a ha := by
  -- Compare the two actual representatives in their original principal quotient.
  exact atlasFullSymbolKClass_eq_of_principalClass_eq A B (Classical.choose hi) a
    (Classical.choose_spec hi).2 ha ((Classical.choose_spec hi).1.symm.trans hPa)

end AtlasPseudodifferentialOperator

end AtiyahSinger
