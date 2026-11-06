/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalEllipticSymbol
public import AtiyahSinger.Geometry.CosphereBundle

/-!
# Actual Hom sections over the cosphere

Public module ID: M0421.

Cosphere symbols are maps between the original E and F fibers, over the same
base point as the unit covector. Continuity is tested in mathlib's Hom bundle
total space, not in an unrelated product of fiber norms. Restriction and radial
extension are explicit formulas. The extension assigns zero on the zero section,
which is irrelevant to positive homogeneity. Sources: SG III.3, III.7.10--7.11;
radial details and degree-changing identities are project deductions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

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

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- A section of Hom(π*E, π*F) over the metric cosphere, with regularity separate. -/
abbrev CosphereSymbolFunction : Type _ :=
  ∀ z : CosphereBundle g, E z.val.proj →L[ℂ] F z.val.proj

/-- The underlying Hom total-space map of a cosphere symbol. -/
def cosphereSymbolTotal (a : CosphereSymbolFunction (E := E) (F := F) g) :
    CosphereBundle g → TotalSpace
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) (fun x ↦ E x →L[ℂ] F x) :=
  fun z ↦ ⟨z.val.proj, a z⟩

/-- Continuity as a section of the actual pulled-back Hom bundle. -/
def IsContinuousCosphereSymbol (a : CosphereSymbolFunction (E := E) (F := F) g) : Prop :=
  Continuous (cosphereSymbolTotal (r := r) (q := q) g a)

/-- Restriction of genuine cotangent Hom data to unit covectors. -/
def cosphereRestriction (a : GlobalSymbolFunction (n := n) E F) :
    CosphereSymbolFunction (E := E) (F := F) g :=
  fun z ↦ a z.val.proj z.val.snd

/-- Positive homogeneous radial extension with the zero value fixed at zero. -/
def cosphereExtension (m : ℝ) (a : CosphereSymbolFunction (E := E) (F := F) g) :
    GlobalSymbolFunction (n := n) E F := by
  classical
  exact fun x ξ ↦ if hξ : ξ = 0 then 0 else
    ((g.length x ξ ^ m : ℝ) : ℂ) • a (g.radial ⟨⟨x, ξ⟩, hξ⟩)

/-- Radial extension vanishes on the zero section. -/
theorem cosphereExtension_zero_covector (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) (x : M) :
    cosphereExtension g m a x 0 = 0 := by
  /- Evaluate the explicitly chosen zero branch of the formula. The
  real power at zero is never used, so negative and zero degrees are also covered. -/
  simp [cosphereExtension]

/-- Away from zero the extension has its stated radial formula. -/
theorem cosphereExtension_of_ne_zero (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
    cosphereExtension g m a x ξ =
      ((g.length x ξ ^ m : ℝ) : ℂ) • a (g.radial ⟨⟨x, ξ⟩, hξ⟩) := by
  /- Use the nonzero branch of the definition. Both sides use the same
  base point and normalized covector; proof irrelevance identifies nonzero certificates. -/
  classical
  exact dite_eq_right hξ

/-- Restriction recovers the original cosphere section at any real degree. -/
theorem cosphereRestriction_extension (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereRestriction g (cosphereExtension g m a) = a := by
  /- Unit covectors are nonzero, have length one, and normalize to
  themselves. The scalar one to any real degree equals one; apply function extensionality. -/
  funext z
  -- Fix the base point before simplifying the dependent Hom fiber.
  obtain ⟨⟨x, ξ⟩, hunit⟩ := z
  have hξ := g.cosphere_ne_zero ⟨⟨x, ξ⟩, hunit⟩
  change cosphereExtension g m a x ξ = a ⟨⟨x, ξ⟩, hunit⟩
  rw [cosphereExtension_of_ne_zero g m a x ξ hξ]
  -- Unit length eliminates the homogeneous factor, and normalization fixes ξ.
  simp only [hunit, Real.one_rpow, Complex.ofReal_one, one_smul]
  let b : {η : CotangentFiber (n := n) x // g.length x η = 1} →
      (E x →L[ℂ] F x) := fun η ↦ a ⟨⟨x, η.val⟩, η.property⟩
  change b ⟨g.normalize x ξ, g.length_normalize x ξ hξ⟩ = b ⟨ξ, hunit⟩
  congr 1
  exact Subtype.ext (g.normalize_of_length_eq_one x ξ hunit)

/-- Radial extension is injective, even on an empty cosphere. -/
theorem cosphereExtension_injective (m : ℝ) :
    Function.Injective (cosphereExtension (E := E) (F := F) g m) := by
  /- Apply cosphereRestriction to an equality of extensions. Its left
  inverse identity recovers the two sections. The argument requires no point of the cosphere. -/
  intro a b hab
  have hre := congrArg (cosphereRestriction g) hab
  simpa only [cosphereRestriction_extension] using hre

/-- The extension has the prescribed positive real homogeneity. -/
theorem isHomogeneousGlobalSymbol_cosphereExtension (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    IsHomogeneousGlobalSymbol E F m (cosphereExtension g m a) := by
  /- At a nonzero covector and positive scalar, normalization is
  unchanged and length scales by that scalar. Positive real power of the product
  factors as t^m times length^m, giving the claimed complex scalar multiplication. -/
  intro x ξ hξ t ht
  have htξ : t • ξ ≠ 0 := smul_ne_zero ht.ne' hξ
  -- Positive scaling changes the length but preserves the actual normalized covector.
  rw [cosphereExtension_of_ne_zero g m a x _ htξ,
    cosphereExtension_of_ne_zero g m a x ξ hξ]
  -- Real powers of positive products factor, with the same complex scalar action.
  rw [g.length_smul, abs_of_pos ht, Real.mul_rpow ht.le (g.length_pos x ξ hξ).le]
  let b : {η : CotangentFiber (n := n) x // g.length x η = 1} →
      (E x →L[ℂ] F x) := fun η ↦ a ⟨⟨x, η.val⟩, η.property⟩
  change (((t ^ m * g.length x ξ ^ m : ℝ) : ℂ) •
      b ⟨g.normalize x (t • ξ), g.length_normalize x (t • ξ) htξ⟩) =
    ((t ^ m : ℝ) : ℂ) • ((g.length x ξ ^ m : ℝ) : ℂ) •
      b ⟨g.normalize x ξ, g.length_normalize x ξ hξ⟩
  rw [Complex.ofReal_mul, mul_smul]
  congr 2
  exact congrArg b (Subtype.ext (g.normalize_pos_smul x ξ t ht))

/-- Restriction determines homogeneous data away from zero. -/
theorem cosphereExtension_restriction (m : ℝ) (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsHomogeneousGlobalSymbol E F m a)
    (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
    cosphereExtension g m (cosphereRestriction g a) x ξ = a x ξ := by
  /- Write ξ as its positive length times its normalized direction.
  Apply degree-m homogeneity at that nonzero direction. This claims equality only
  off zero because the original symbol may have arbitrary zero-section values. -/
  rw [cosphereExtension_of_ne_zero g m (cosphereRestriction g a) x ξ hξ]
  -- Apply homogeneity at the unit direction with the original positive length.
  have hnormalize := g.normalize_ne_zero x ξ hξ
  have hreconstruct := ha x (g.normalize x ξ) hnormalize (g.length x ξ)
    (g.length_pos x ξ hξ)
  rw [g.length_smul_normalize x ξ] at hreconstruct
  exact hreconstruct.symm

/-- Two homogeneous symbols agree off zero exactly when their restrictions agree. -/
theorem cosphereRestriction_eq_iff (m : ℝ) (a b : GlobalSymbolFunction (n := n) E F)
    (ha : IsHomogeneousGlobalSymbol E F m a)
    (hb : IsHomogeneousGlobalSymbol E F m b) :
    cosphereRestriction g a = cosphereRestriction g b ↔
      ∀ x ξ, ξ ≠ 0 → a x ξ = b x ξ := by
  /- An equality on unit covectors propagates by positive homogeneous
  rescaling to every nonzero covector. The reverse implication restricts an off-zero
  equality to unit covectors. Values at zero remain deliberately unconstrained. -/
  constructor
  · intro hab x ξ hξ
    -- Reconstruction propagates the unit-covector equality to every nonzero fiber.
    calc
      a x ξ = cosphereExtension g m (cosphereRestriction g a) x ξ :=
        (cosphereExtension_restriction g m a ha x ξ hξ).symm
      _ = cosphereExtension g m (cosphereRestriction g b) x ξ := by rw [hab]
      _ = b x ξ := cosphereExtension_restriction g m b hb x ξ hξ
  · intro hab
    funext z
    exact hab z.val.proj z.val.snd (g.cosphere_ne_zero z)

/-- Extension is additive. -/
theorem cosphereExtension_add (m : ℝ)
    (a b : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereExtension g m (a + b) = cosphereExtension g m a + cosphereExtension g m b := by
  /- Away from zero distribute the common real-power scalar over the
  fiberwise sum. At zero all terms use the explicit zero branch, so equality holds globally. -/
  funext x ξ
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [Pi.add_apply, cosphereExtension_zero_covector, add_zero]
  · simp only [Pi.add_apply, cosphereExtension_of_ne_zero g m _ x ξ hξ, smul_add]
    rfl

/-- Extension respects complex scalar multiplication. -/
theorem cosphereExtension_smul (m : ℝ) (c : ℂ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereExtension g m (c • a) = c • cosphereExtension g m a := by
  /- Complex scalar multiplication commutes with the real-power scalar
  in each Hom fiber. Treat zero separately and use function extensionality at all covectors. -/
  funext x ξ
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [Pi.smul_apply, cosphereExtension_zero_covector, smul_zero]
  · simp only [Pi.smul_apply, cosphereExtension_of_ne_zero g m _ x ξ hξ]
    change ((g.length x ξ ^ m : ℝ) : ℂ) •
      (c • (a (g.radial ⟨⟨x, ξ⟩, hξ⟩) : E x →L[ℂ] F x)) =
      c • (((g.length x ξ ^ m : ℝ) : ℂ) •
        (a (g.radial ⟨⟨x, ξ⟩, hξ⟩) : E x →L[ℂ] F x))
    exact smul_comm _ _ _

/-- Restriction is additive. -/
theorem cosphereRestriction_add (a b : GlobalSymbolFunction (n := n) E F) :
    cosphereRestriction g (a + b) = cosphereRestriction g a + cosphereRestriction g b := by
  /- Restriction is evaluation at the same base and unit covector in
  both summands. The pointwise addition on dependent functions therefore gives the identity. -/
  rfl

/-- Restriction respects complex scalars. -/
theorem cosphereRestriction_smul (c : ℂ) (a : GlobalSymbolFunction (n := n) E F) :
    cosphereRestriction g (c • a) = c • cosphereRestriction g a := by
  /- Evaluate both sides on a unit covector. Pointwise scalar action
  on the original Hom family agrees with pointwise scalar action on its restriction. -/
  rfl

/-- Radial extension packaged as its actual complex-linear map. -/
def cosphereExtensionLinearMap (m : ℝ) :
    CosphereSymbolFunction (E := E) (F := F) g →ₗ[ℂ] GlobalSymbolFunction (n := n) E F :=
  { toFun := cosphereExtension g m
    map_add' := cosphereExtension_add g m
    map_smul' := cosphereExtension_smul g m }

/-- Restriction packaged as its actual complex-linear map. -/
def cosphereRestrictionLinearMap :
    GlobalSymbolFunction (n := n) E F →ₗ[ℂ] CosphereSymbolFunction (E := E) (F := F) g :=
  { toFun := cosphereRestriction g
    map_add' := cosphereRestriction_add g
    map_smul' := cosphereRestriction_smul g }

end AtiyahSinger
