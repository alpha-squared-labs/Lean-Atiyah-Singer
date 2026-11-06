/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Geometry.AtlasFrame

/-!
# Global symbols on bundles of locally varying finite rank

Public module ID: M0244.

D05: SG III.3, Definition 3.18, pp.187-188, in the standard finite-rank atlas
formulation. Symbols act on the original fibers. Their local expressions use
the given actual source and target frames, whose ranks are independent and may
vary between components. Continuous linear maps occur only between the finite
Euclidean coordinate spaces; no norm is imposed on an original bundle fiber.

The principal carrier is the actual quotient by one lower order. This does not
select a homogeneous representative or impose a polyhomogeneous expansion.
SG's weak homogeneous-symbol convention is imposed separately where needed.
The atlas formulation introduces no compactness, density, global rank bound,
connection, exponential map, or support condition on an operator kernel.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]

/-- Actual complex-linear Hom families over the original real cotangent fibers. -/
abbrev AtlasSymbolFunction : Type _ :=
  ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) → (E x →ₗ[ℂ] F x)

variable {E F} [TopologicalSpace (TotalSpace Unit E)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- The common region of a manifold chart and the two specified atlas frames. -/
def atlasSymbolChartDomain (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (i : A.Index) (j : B.Index) : Set (EuclideanSpace ℝ (Fin n)) :=
  c.target ∩ c.symm ⁻¹' (A.chart i).baseSet ∩ c.symm ⁻¹' (B.chart j).baseSet

open scoped Classical in
/-- Actual coordinate expression, extended by zero outside the common frame domains. -/
def atlasGlobalSymbolInChart (p : AtlasSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (i : A.Index) (j : B.Index) : SymbolFunction n (A.rank i) (B.rank j) :=
  fun z η ↦
    if h : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet then
      let input := (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toLinearEquiv.trans
        (A.frameLinearEquiv i (c.symm z) h.1).symm
      let output := (B.frameLinearEquiv j (c.symm z) h.2).trans
        (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.toLinearEquiv
      LinearMap.toContinuousLinearMap
        (output.toLinearMap.comp
          ((p (c.symm z) (covectorFromChart c (c.symm z) η)).comp input.toLinearMap))
    else 0

/-- The standard order-m symbol estimates in every valid base chart and atlas-frame pair. -/
def IsAtlasGlobalSymbol (m : ℝ) (p : AtlasSymbolFunction (n := n) E F) : Prop :=
  ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M → ∀ (i : A.Index) (j : B.Index),
      IsSymbol (atlasSymbolChartDomain A B c i j) m
        (atlasGlobalSymbolInChart A B p c i j)

/-- Grouped module-closure certificate for the actual atlas symbol carrier. -/
theorem isAtlasGlobalSymbol_closure (m : ℝ) :
    IsAtlasGlobalSymbol A B m 0 ∧
      (∀ p q : AtlasSymbolFunction (n := n) E F,
        IsAtlasGlobalSymbol A B m p → IsAtlasGlobalSymbol A B m q →
          IsAtlasGlobalSymbol A B m (p + q)) ∧
      (∀ (a : ℂ) (p : AtlasSymbolFunction (n := n) E F),
        IsAtlasGlobalSymbol A B m p → IsAtlasGlobalSymbol A B m (a • p)) := by
  /- On each common chart/frame domain, the linear frame maps preserve
  zero, sums and complex scalar multiplication. The coordinate region is
  open because the inverse base chart is continuous on its open target
  and both frame base sets are open. Apply local symbol-space closure.
  The same linearity identities hold for the zero extensions off the
  frame domains. -/
  classical
  -- Coordinate regions are open even though the original fibers have no chosen norm.
  have hopen (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (i : A.Index) (j : B.Index) : IsOpen (atlasSymbolChartDomain A B c i j) := by
    simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      c.continuousOn_symm.isOpen_inter_preimage c.open_target
        ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
  refine ⟨?_, ?_, ?_⟩
  · intro c hc i j
    have hz : atlasGlobalSymbolInChart A B 0 c i j = 0 := by
      ext z η v
      simp [atlasGlobalSymbolInChart]
    rw [hz]
    exact isSymbol_zero _ m
  · intro p q hp hq c hc i j
    have hadd : atlasGlobalSymbolInChart A B (p + q) c i j =
        atlasGlobalSymbolInChart A B p c i j + atlasGlobalSymbolInChart A B q c i j := by
      ext z η v
      by_cases h : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, h]
      · simp [atlasGlobalSymbolInChart, h]
    rw [hadd]
    exact (hp c hc i j).add (hopen c i j) (hq c hc i j)
  · intro a p hp c hc i j
    have hsmul : atlasGlobalSymbolInChart A B (a • p) c i j =
        a • atlasGlobalSymbolInChart A B p c i j := by
      ext z η v
      by_cases h : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, h]
      · simp [atlasGlobalSymbolInChart, h]
    rw [hsmul]
    exact (hp c hc i j).smul (hopen c i j) a

/-- The symbol order filtration is increasing, with the original Hom family unchanged. -/
theorem IsAtlasGlobalSymbol.mono {m l : ℝ} (hml : m ≤ l)
    {p : AtlasSymbolFunction (n := n) E F} (hp : IsAtlasGlobalSymbol A B m p) :
    IsAtlasGlobalSymbol A B l p := by
  /- In every local expression the standard weight is at least one. Increasing
  the order weakens all derivative estimates, while the actual smooth function
  and its source and target coordinate spaces remain unchanged. -/
  intro c hc i j
  exact (hp c hc i j).mono hml

/-- The actual complex submodule of order-m atlas symbols on the original fibers. -/
def atlasGlobalSymbolSpace (m : ℝ) : Submodule ℂ (AtlasSymbolFunction (n := n) E F) where
  carrier := {p | IsAtlasGlobalSymbol A B m p}
  zero_mem' := (isAtlasGlobalSymbol_closure A B m).1
  add_mem' := fun hp hq ↦ (isAtlasGlobalSymbol_closure A B m).2.1 _ _ hp hq
  smul_mem' := fun a p hp ↦ (isAtlasGlobalSymbol_closure A B m).2.2 a p hp

/-- Symbols of one lower order, as a submodule of the order-m atlas symbol module. -/
def lowerOrderAtlasGlobalSymbols (m : ℝ) : Submodule ℂ (atlasGlobalSymbolSpace A B m) :=
  (atlasGlobalSymbolSpace A B (m - 1)).comap (atlasGlobalSymbolSpace A B m).subtype

/-- The principal-symbol quotient for the given actual variable-rank bundle atlases. -/
abbrev AtlasGlobalPrincipalSymbolSpace (m : ℝ) : Type _ :=
  atlasGlobalSymbolSpace A B m ⧸ lowerOrderAtlasGlobalSymbols A B m

/-- The canonical complex-linear quotient map, with no homogeneous representative chosen. -/
def atlasGlobalPrincipalSymbolClass (m : ℝ) :
    atlasGlobalSymbolSpace A B m →ₗ[ℂ] AtlasGlobalPrincipalSymbolSpace A B m :=
  (lowerOrderAtlasGlobalSymbols A B m).mkQ

/-- Two principal classes agree exactly when their actual difference has one lower order. -/
theorem atlasGlobalPrincipalSymbolClass_eq_iff (m : ℝ)
    (p q : atlasGlobalSymbolSpace A B m) :
    atlasGlobalPrincipalSymbolClass A B m p = atlasGlobalPrincipalSymbolClass A B m q ↔
      IsAtlasGlobalSymbol A B (m - 1) (p.val - q.val) := by
  /- Quotient equality is membership of p-q in the denominator. Its comap along
  the original symbol subtype tests precisely the order-(m-1) estimates on the
  same original Hom-valued difference. No homogeneous representative or actual
  operator is involved, including when the base dimension is zero. -/
  exact Submodule.Quotient.eq (lowerOrderAtlasGlobalSymbols A B m)

end AtiyahSinger
