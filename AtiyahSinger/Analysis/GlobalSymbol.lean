/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FrameChange
public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Analysis.SymbolLocality
public import AtiyahSinger.Analysis.SymbolQuotient
public import AtiyahSinger.Geometry.FrameTransition

/-!
# Global Hom-valued symbols and their principal quotient

Public module ID: M0677.

SG Definition 3.18 and the carrier of Theorem 3.19, pp.187-188.
A symbol is an actual family over real cotangent fibers, valued in complex-linear
maps E_x -> F_x. Smoothness and estimates are tested in manifold and bundle charts.
This is the section model of Hom(π*E, π*F); it does not select a homogeneous function
or assume an operator with that symbol. The principal space is the actual quotient
S^m(E,F)/S^(m-1)(E,F). No metric, density or compactness is needed for these carriers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15


set_option linter.unusedSectionVars false

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Pull a coordinate covector back by the derivative of the manifold chart. -/
def covectorFromChart (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (x : M)
    (η : EuclideanSpace ℝ (Fin n)) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ :=
  (innerSL ℝ η).comp
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c x)

/-- Reading coordinates after pulling back a covector recovers its coordinate vector. -/
theorem covectorInChart_covectorFromChart
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (x : M) (hx : x ∈ c.source)
    (η : EuclideanSpace ℝ (Fin n)) :
    covectorInChart c x (covectorFromChart c x η) = η := by
  /- Differentiate c ∘ c.symm = id on the chart target. The two derivatives cancel
  at x and c x. Evaluating the resulting coordinate functional on each standard
  basis vector recovers each component of η, including the zero-dimensional case. -/
  -- The derivatives of a chart and its inverse cancel on the chart target.
  have hderiv := (mdifferentiable_of_mem_atlas
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hc).comp_symm_deriv (c.map_source hx)
  rw [c.left_inv hx] at hderiv
  ext j
  change inner ℝ η ((mfderiv _ _ c x)
    ((mfderiv _ _ c.symm (c x)) (EuclideanSpace.single j 1))) = η j
  have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) ↦ L (EuclideanSpace.single j 1)) hderiv
  change (mfderiv _ _ c x) ((mfderiv _ _ c.symm (c x))
    (EuclideanSpace.single j 1)) = EuclideanSpace.single j 1 at h
  rw [h]
  simp [EuclideanSpace.inner_single_right]

/-- Pulling back the coordinate components of a genuine covector recovers that covector. -/
theorem covectorFromChart_covectorInChart
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (x : M) (hx : x ∈ c.source)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    covectorFromChart c x (covectorInChart c x ξ) = ξ := by
  /- The coordinates specify the functional ξ ∘ D(c.symm) on every standard basis
  vector. Thus innerSL applied to those coordinates is precisely that functional.
  Compose with Dc and use the derivative of c.symm ∘ c = id on the source. -/
  -- The coordinate vector represents the covector pulled back to the Euclidean model.
  have hcoord : innerSL ℝ (covectorInChart c x ξ) =
      ξ.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm (c x)) := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro j
    simp [covectorInChart, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right]
    rfl
  -- Composing with the forward derivative recovers the original covector.
  ext v
  have hinverse := congrArg (fun L : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x
      →L[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x ↦ L v)
    ((mdifferentiable_of_mem_atlas
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hc).symm_comp_deriv hx)
  change (mfderiv _ _ c.symm (c x)) ((mfderiv _ _ c x) v) = v at hinverse
  calc
    covectorFromChart c x (covectorInChart c x ξ) v =
        ξ ((mfderiv _ _ c.symm (c x)) ((mfderiv _ _ c x) v)) :=
      DFunLike.congr_fun hcoord ((mfderiv _ _ c x) v)
    _ = ξ v := congrArg ξ hinverse

variable (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- Actual Hom-valued functions on the cotangent fibers; regularity is imposed separately. -/
abbrev GlobalSymbolFunction : Type _ :=
  ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) → (E x →L[ℂ] F x)

/-- The coordinate region where the base chart and both bundle frames are valid. -/
def symbolChartDomain (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  c.target ∩ c.symm ⁻¹' e.baseSet ∩ c.symm ⁻¹' f.baseSet

/-- The common coordinate/frame region is open. -/
theorem isOpen_symbolChartDomain
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F)) :
    IsOpen (symbolChartDomain E F c e f) := by
  /- Both frame base sets are open. The inverse chart is continuous on its open
  target, so their inverse images intersected with that target are open. Intersect
  these two open regions; no smoothness or compactness assumption is needed. -/
  -- Restriction to the chart target makes the inverse-chart preimage open.
  simpa only [symbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
    c.isOpen_inter_preimage_symm (e.open_baseSet.inter f.open_baseSet)

/-- Coordinate expression of a genuine symbol, using Dc to pull back the frequency covector. -/
def globalSymbolInChart (p : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] : SymbolFunction n r q :=
  fun z η ↦ (f.continuousLinearMapAt ℂ (c.symm z)).comp
    ((p (c.symm z) (covectorFromChart c (c.symm z) η)).comp (e.symmL ℂ (c.symm z)))

/-- Coordinate expressions preserve sums of actual fiber maps. -/
theorem globalSymbolInChart_add (p p' : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    globalSymbolInChart E F (p + p') c e f =
      globalSymbolInChart E F p c e f + globalSymbolInChart E F p' c e f := by
  /- Evaluate at z,η and at a model input vector. Composition of continuous linear
  maps distributes over the sum in the middle factor. This is a pointwise algebraic
  identity, even where the totalized frame maps are outside their valid base sets. -/
  -- The same two frame maps act on both summands at every coordinate point.
  ext z η v
  simp [globalSymbolInChart]

/-- Coordinate expressions preserve complex scalar multiplication, with no conjugation. -/
theorem globalSymbolInChart_smul (a : ℂ) (p : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    globalSymbolInChart E F (a • p) c e f = a • globalSymbolInChart E F p c e f := by
  /- The two fixed frame maps are complex-linear. Move the scalar through the
  output frame and use the pointwise scalar action on the symbol family. Neither
  adjoint nor dualization occurs, so the scalar is not complex-conjugated. -/
  -- Both frame maps are complex-linear, so no scalar conjugation occurs.
  ext z η v
  simp [globalSymbolInChart]

/-- In any valid chart, the local expression recovers the original map at a genuine covector. -/
theorem globalSymbolInChart_covectorInChart
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (p : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (x : M) (hx : x ∈ c.source)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    globalSymbolInChart E F p c e f (c x) (covectorInChart c x ξ) =
      (f.continuousLinearMapAt ℂ x).comp ((p x ξ).comp (e.symmL ℂ x)) := by
  /- Use c.symm(c x)=x, transporting the dependent cotangent fiber along this
  equality. The preceding inverse-covector identity then recovers ξ. The two
  remaining factors are exactly the original output frame and inverse input frame. -/
  -- First return to the original base point, then use the inverse cotangent coordinate map.
  unfold globalSymbolInChart
  rw [c.left_inv hx, covectorFromChart_covectorInChart c hc x hx ξ]

/-- SG 3.18: real smoothness and order-m estimates in every valid local presentation. -/
def IsGlobalSymbol (m : ℝ) (p : GlobalSymbolFunction (n := n) E F) : Prop :=
  ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E))
        (f : Trivialization (EuclideanSpace ℂ (Fin q))
          (π (EuclideanSpace ℂ (Fin q)) F))
        [MemTrivializationAtlas e] [MemTrivializationAtlas f],
        IsSymbol (symbolChartDomain E F c e f) m (globalSymbolInChart E F p c e f)

/-- The zero Hom section has every real symbol order. -/
theorem isGlobalSymbol_zero (m : ℝ) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m 0 := by
  /- Each coordinate expression is the zero matrix function, because composition
  with a zero middle map is zero. Apply the local zero-symbol theorem in each
  coordinate/frame overlap. There is no choice of global representative here. -/
  -- Every coordinate map has a zero middle factor.
  intro c hc e f he hf
  have hz : globalSymbolInChart E F 0 c e f = 0 := by
    ext z η v
    simp [globalSymbolInChart]
  rw [hz]
  exact isSymbol_zero _ m

variable {E F}

/-- Addition preserves the order of genuine global symbols. -/
theorem IsGlobalSymbol.add {m : ℝ} {p p' : GlobalSymbolFunction (n := n) E F}
    (hp : IsGlobalSymbol (n := n) (r := r) (q := q) E F m p)
    (hp' : IsGlobalSymbol (n := n) (r := r) (q := q) E F m p') :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m (p + p') := by
  /- Fix arbitrary chart and frames. Their common coordinate region is open.
  The coordinate sum formula identifies the expression with a sum of local
  order-m symbols; use the local addition estimate and then quantify over all charts. -/
  -- The same chart and pair of frames are used for both summands.
  intro c hc e f he hf
  rw [globalSymbolInChart_add]
  exact (hp c hc e f).add (isOpen_symbolChartDomain E F c e f) (hp' c hc e f)

/-- Complex scalar multiplication preserves the global symbol order. -/
theorem IsGlobalSymbol.smul {m : ℝ} (a : ℂ) {p : GlobalSymbolFunction (n := n) E F}
    (hp : IsGlobalSymbol (n := n) (r := r) (q := q) E F m p) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m (a • p) := by
  /- In each open coordinate/frame region, the expression is a times the original
  local symbol by globalSymbolInChart_smul. Apply the local scalar estimate with
  the factor norm(a), retaining real smoothness and all frequency derivative orders. -/
  intro c hc e f he hf
  rw [globalSymbolInChart_smul]
  exact (hp c hc e f).smul (isOpen_symbolChartDomain E F c e f) a

/-- Global symbols form an increasing filtration by their real order bounds. -/
theorem IsGlobalSymbol.mono {m l : ℝ} (hml : m ≤ l)
    {p : GlobalSymbolFunction (n := n) E F}
    (hp : IsGlobalSymbol (n := n) (r := r) (q := q) E F m p) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F l p := by
  /- In every chart, use the local order monotonicity estimate. The weight is at
  least one, so increasing its exponent weakens the bound at all frequencies.
  The actual symbol section and its smoothness are unchanged. -/
  intro c hc e f he hf
  exact (hp c hc e f).mono hml

variable (E F)

/-- The actual complex submodule of global Hom-valued symbols of order m. -/
def globalSymbolSpace (m : ℝ) : Submodule ℂ (GlobalSymbolFunction (n := n) E F) where
  carrier := {p | IsGlobalSymbol (r := r) (q := q) E F m p}
  zero_mem' := isGlobalSymbol_zero E F m
  add_mem' := fun hp hp' ↦ hp.add hp'
  smul_mem' := fun a _ hp ↦ hp.smul a

/-- Global symbols of order m-1, viewed inside the order-m symbol module. -/
def lowerOrderGlobalSymbols (m : ℝ) :
    Submodule ℂ (globalSymbolSpace (n := n) (r := r) (q := q) E F m) :=
  (globalSymbolSpace (n := n) (r := r) (q := q) E F (m - 1)).comap
    (globalSymbolSpace (n := n) (r := r) (q := q) E F m).subtype

/-- The standard global principal-symbol quotient, not a homogeneous representative. -/
abbrev GlobalPrincipalSymbolSpace (m : ℝ) : Type _ :=
  globalSymbolSpace (n := n) (r := r) (q := q) E F m ⧸
    lowerOrderGlobalSymbols (n := n) (r := r) (q := q) E F m

/-- The canonical complex-linear class map of the actual global symbol quotient. -/
def globalPrincipalSymbolClass (m : ℝ) :
    globalSymbolSpace (n := n) (r := r) (q := q) E F m →ₗ[ℂ]
      GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m :=
  (lowerOrderGlobalSymbols (n := n) (r := r) (q := q) E F m).mkQ

/-- Equality of global principal classes is exactly one lower order of their difference. -/
theorem globalPrincipalSymbolClass_eq_iff (m : ℝ)
    (p p' : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolClass E F m p = globalPrincipalSymbolClass E F m p' ↔
      IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1) (p.val - p'.val) := by
  /- The quotient equality criterion says p-p' belongs to the denominator.
  Unfold its comap along the subtype map: membership is precisely the order-(m-1)
  estimates on the actual difference of the two global Hom sections. -/
  -- The denominator tests the same actual Hom-valued difference.
  exact Submodule.Quotient.eq (lowerOrderGlobalSymbols E F m)

/-- A global principal class is zero precisely when its representative has lower order. -/
theorem globalPrincipalSymbolClass_eq_zero_iff (m : ℝ)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolClass E F m p = 0 ↔
      IsGlobalSymbol (n := n) (r := r) (q := q) E F (m - 1) p.val := by
  /- The kernel of the canonical quotient projection is the denominator submodule.
  Its defining comap tests the original symbol family. This criterion does not
  identify zero principal class with a smoothing symbol of every order. -/
  exact Submodule.Quotient.mk_eq_zero (p := lowerOrderGlobalSymbols E F m)

/-- Every global principal class has an actual order-m symbol representative. -/
theorem globalPrincipalSymbolClass_surjective (m : ℝ) :
    Function.Surjective (globalPrincipalSymbolClass (n := n) (r := r) (q := q) E F m) := by
  /- This is surjectivity of the quotient projection of a module by a submodule.
  It selects only a representative in S^m, with no promise of homogeneity and no
  associated pseudodifferential operator. Quantization is a separate construction. -/
  exact (lowerOrderGlobalSymbols (n := n) (r := r) (q := q) E F m).mkQ_surjective

/-- A global symbol expressed as an element of the existing local symbol module. -/
def globalSymbolInChartSpace (m : ℝ)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    symbolSpace (symbolChartDomain E F c e f) (isOpen_symbolChartDomain E F c e f) m r q :=
  ⟨globalSymbolInChart E F p.val c e f, p.property c hc e f⟩

/-- The global quotient is detected by the actual local principal quotients in all charts. -/
theorem globalPrincipalSymbolClass_eq_iff_local (m : ℝ)
    (p p' : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolClass E F m p = globalPrincipalSymbolClass E F m p' ↔
      ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
        (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E))
        (f : Trivialization (EuclideanSpace ℂ (Fin q))
          (π (EuclideanSpace ℂ (Fin q)) F))
        [MemTrivializationAtlas e] [MemTrivializationAtlas f],
        principalSymbolClass _ (isOpen_symbolChartDomain E F c e f) m r q
            (globalSymbolInChartSpace E F m p c hc e f) =
          principalSymbolClass _ (isOpen_symbolChartDomain E F c e f) m r q
            (globalSymbolInChartSpace E F m p' c hc e f) := by
  /- Global equality is the order-(m-1) condition on the difference in every chart.
  Coordinates preserve differences by their additivity and complex linearity.
  The local quotient equality criterion turns exactly these conditions into the
  displayed equalities. Both directions concern existing quotient carriers. -/
  -- A single linear coordinate map preserves the difference before taking its local quotient.
  rw [globalPrincipalSymbolClass_eq_iff]
  have hsub (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π _ E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π _ F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      globalSymbolInChart E F (p.val - p'.val) c e f =
        globalSymbolInChart E F p.val c e f - globalSymbolInChart E F p'.val c e f := by
    ext z η v
    simp [globalSymbolInChart]
  simp only [principalSymbolClass_eq_iff, globalSymbolInChartSpace, IsGlobalSymbol, hsub]

/-- Genuine symbol sections obey the exact cotangent/Hom transition law. -/
theorem globalSymbolInChart_transition
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (p : GlobalSymbolFunction (n := n) E F)
    (c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hc' : c' ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f f' : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f']
    (x : M) (hx : x ∈ c.source) (hx' : x ∈ c'.source)
    (he : x ∈ e.baseSet ∩ e'.baseSet) (hf : x ∈ f.baseSet ∩ f'.baseSet)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    globalSymbolInChart E F p c' e' f' (c' x) (covectorInChart c' x ξ) =
      (f.coordChangeL ℂ f' x).toContinuousLinearMap.comp
        ((globalSymbolInChart E F p c e f (c x) (covectorInChart c x ξ)).comp
          (e.coordChangeL ℂ e' x).symm.toContinuousLinearMap) := by
  /- Stage 1: both covector-coordinate identities recover the same actual ξ in
  T*_x M, although its coordinate vector changes with the inverse chart derivative.
  Stage 2: apply homInFrames_coordChange to p(x,ξ). The output uses the forward
  transition and the input its inverse. This is exact for a given Hom section;
  full quantization symbols of one operator only have this law modulo lower order. -/
  -- Recover the same covector on both sides, then change only the two actual frames.
  rw [globalSymbolInChart_covectorInChart E F p c' hc' e' f' x hx' ξ,
    globalSymbolInChart_covectorInChart E F p c hc e f x hx ξ]
  exact homInFrames_coordChange E F e e' f f' x he hf (p x ξ)

/-- SG 3.18 can be checked in any covering smooth system of charts and frames. -/
theorem isGlobalSymbol_iff_of_cover
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [IsSmoothComplexBundle (n := n) (r := r) E]
    [IsSmoothComplexBundle (n := n) (r := q) F]
    {ι : Type*} (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : ∀ j, c j ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : ι → Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : ι → Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [∀ j, MemTrivializationAtlas (e j)] [∀ j, MemTrivializationAtlas (f j)]
    (hcover : ∀ x : M, ∃ j, x ∈ (c j).source ∩ (e j).baseSet ∩ (f j).baseSet)
    (m : ℝ) (p : GlobalSymbolFunction (n := n) E F) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m p ↔ ∀ j,
      IsSymbol (symbolChartDomain E F (c j) (e j) (f j)) m
        (globalSymbolInChart E F p (c j) (e j) (f j)) := by
  /- Forward: specialize the definition to each member of the covering family.
  Reverse, Stage 1: the transition law expresses an arbitrary chart symbol using
  a covering chart, a smooth invertible cotangent-linear frequency substitution,
  and smooth frame matrices. On relatively compact overlap neighborhoods the
  matrix derivatives and the frequency substitution and its inverse are bounded.
  Each spatial derivative of the frequency substitution contributes one ξ factor
  and one frequency derivative of p, preserving S^m_(1,0) order.
  Stage 2: a compact coordinate set is covered by finitely many such neighborhoods.
  Combine their estimates for each derivative order. Smoothness is local as well.
  Thus every chart has the required estimates, without compactness of the whole base. -/
  classical
  constructor
  · intro hp j
    exact hp (c j) (hc j) (e j) (f j)
  intro hp d hd e' f' _ _
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let U := symbolChartDomain E F d e' f'
  let pnew := globalSymbolInChart E F p d e' f'
  have hU : IsOpen U := isOpen_symbolChartDomain E F d e' f'
  -- Equality on an open spatial set identifies every original mixed derivative there.
  have congrSymbol {V : Set X} (hV : IsOpen V) (a b : SymbolFunction n r q)
      (ha : IsSymbol V m a) (hab : ∀ x ∈ V, ∀ ξ, a x ξ = b x ξ) :
      IsSymbol V m b := by
    refine ⟨ha.1.congr (fun z hz ↦ (hab z.1 hz.1 z.2).symm), ?_⟩
    intro C hCV hC i j
    obtain ⟨B, hB, hbound⟩ := ha.2 C hCV hC i j
    refine ⟨B, hB, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) := by
      filter_upwards [hV.mem_nhds (hCV hx)] with y hy
      rw [funext (hab y hy)]
    have hder := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← hder]
    exact hbound x hx ξ
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  -- Each point uses a member of the actual covering atlas, on an open overlap.
  apply IsSymbol.of_locally hU
  intro z hz
  obtain ⟨j, hj⟩ := hcover (d.symm z)
  let D := (c j).source ∩ (e j).baseSet ∩ (f j).baseSet
  have hD : IsOpen D := ((c j).open_source.inter (e j).open_baseSet).inter
    (f j).open_baseSet
  let V := U ∩ d.symm ⁻¹' D
  have hV : IsOpen V :=
    (d.continuousOn_symm.mono (fun y hy ↦ hy.1.1)).isOpen_inter_preimage hU hD
  have hzV : z ∈ V := ⟨hz, hj⟩
  let S := symbolChartDomain E F (c j) (e j) (f j)
  have hS : IsOpen S := isOpen_symbolChartDomain E F (c j) (e j) (f j)
  let t₀ : OpenPartialHomeomorph X X := (c j).symm.trans d
  let t : OpenPartialHomeomorph X X := t₀.restrOpen S hS
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) (hc j)
  have ht₀ : ContDiffOn ℝ ∞ t₀ t₀.source := by
    intro y hy
    exact (((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1)).contDiffAt).contDiffWithinAt
  have hts₀ : ContDiffOn ℝ ∞ t₀.symm t₀.target := by
    intro y hy
    exact (((contMDiffAt_of_mem_maximalAtlas hcM hy.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1)).contDiffAt).contDiffWithinAt
  have ht : ContDiffOn ℝ ∞ t t.source := ht₀.mono Set.inter_subset_left
  have hts : ContDiffOn ℝ ∞ t.symm t.target := hts₀.mono Set.inter_subset_left
  have h_old (y : X) (hy : y ∈ V) : (c j) (d.symm y) ∈ S := by
    refine ⟨⟨(c j).map_source hy.2.1.1, ?_⟩, ?_⟩
    · change (c j).symm ((c j) (d.symm y)) ∈ (e j).baseSet
      simpa only [(c j).left_inv hy.2.1.1] using hy.2.1.2
    · change (c j).symm ((c j) (d.symm y)) ∈ (f j).baseSet
      simpa only [(c j).left_inv hy.2.1.1] using hy.2.2
  have hVt : V ⊆ t.target := fun y hy ↦
    ⟨⟨hy.1.1.1, hy.2.1.1⟩, h_old y hy⟩
  let p₀ := globalSymbolInChart E F p (c j) (e j) (f j)
  have hpt : IsSymbol V m (cotangentSymbol t p₀) :=
    (isSymbol_cotangentSymbol t ht hts m p₀
      ((hp j).restrict Set.inter_subset_right)).restrict hVt
  let A : X → (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    fun y ↦ ((f j).coordChangeL ℂ f' (d.symm y)).toContinuousLinearMap
  let B : X → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    fun y ↦ ((e j).coordChangeL ℂ e' (d.symm y)).symm.toContinuousLinearMap
  have hdV : ContMDiffOn I I ∞ d.symm V := by
    intro y hy
    exact (contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1.1.1).contMDiffWithinAt
  have hA : ContDiffOn ℝ ∞ A V := contDiffOn_coordChangeL_comp F
    (f j) f' V d.symm hdV (fun y hy ↦ ⟨hy.2.2, hy.1.2⟩)
  have hB : ContDiffOn ℝ ∞ B V := contDiffOn_symm_coordChangeL_comp E
    (e j) e' V d.symm hdV (fun y hy ↦ ⟨hy.2.1.2, hy.1.1.2⟩)
  refine ⟨V, hV, hzV, Set.inter_subset_left,
    congrSymbol hV _ pnew (isSymbol_matrixSymbol V hV m _ hpt A B hA hB) ?_⟩
  intro y hy η
  -- Both sides are the same covector and Hom map in the prescribed two frames.
  have hfreq : covectorInChart (c j) (d.symm y)
      (covectorFromChart d (d.symm y) η) =
        (fderiv ℝ t (t.symm y)).adjoint η := by
    have hsource := hy.2.1.1
    have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) ((c j) (d.symm y))
      (by
        simpa only [(c j).left_inv hsource] using
          (contMDiffAt_of_mem_maximalAtlas hdM
            (d.map_target hy.1.1.1)).mdifferentiableAt (by simp))
      ((contMDiffAt_symm_of_mem_maximalAtlas hcM
        ((c j).map_source hsource)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hcomp
    dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
    rw [(c j).left_inv hsource] at hcomp
    have htcomp : fderiv ℝ t (t.symm y) =
        (mfderiv I I d (d.symm y)).comp
          (mfderiv I I (c j).symm ((c j) (d.symm y))) := hcomp
    ext a
    change inner ℝ η ((mfderiv I I d (d.symm y))
        ((mfderiv I I (c j).symm ((c j) (d.symm y)))
          (EuclideanSpace.single a 1))) =
      ((fderiv ℝ t (t.symm y)).adjoint η) a
    have hadj := (fderiv ℝ t (t.symm y)).adjoint_inner_left
      (EuclideanSpace.single a 1) η
    calc
      _ = inner ℝ η ((fderiv ℝ t (t.symm y)) (EuclideanSpace.single a 1)) := by
        rw [htcomp]
        rfl
      _ = inner ℝ ((fderiv ℝ t (t.symm y)).adjoint η)
          (EuclideanSpace.single a 1) := hadj.symm
      _ = _ := by
        simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) a 1
          ((fderiv ℝ t (t.symm y)).adjoint η)
  have hchange := globalSymbolInChart_transition E F p (c j) d
    (hc j) hd (e j) e' (f j) f' (d.symm y)
    hy.2.1.1 (d.map_target hy.1.1.1) ⟨hy.2.1.2, hy.1.1.2⟩ ⟨hy.2.2, hy.1.2⟩
    (covectorFromChart d (d.symm y) η)
  rw [covectorInChart_covectorFromChart d hd (d.symm y) (d.map_target hy.1.1.1) η,
    d.right_inv hy.1.1.1, hfreq] at hchange
  exact hchange.symm

end AtiyahSinger
