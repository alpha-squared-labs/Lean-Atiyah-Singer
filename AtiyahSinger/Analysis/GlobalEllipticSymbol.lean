/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol
public import AtiyahSinger.Analysis.GlobalSymbolComposition
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Inverting elliptic homogeneous principal data

Public module ID: M0669.

Invert Hom-valued principal data on nonzero cotangent fibers. Off-zero
invertibility is the ellipticity condition for homogeneous principal data;
it is not a sufficient definition of ellipticity for arbitrary full S^m symbols.
Real smoothness, positive homogeneity, and ellipticity are separate hypotheses.
The inverse is mathlib's totalized inverse, with source and target bundles reversed.
Fixed regularizations give pointwise inverse products modulo every symbol order.
Operator remainders use the composition calculus in EllipticParametrix.
References: SG III.4.2--4.4 and Remark 4.7.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [hFE : FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [hVE : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [hFF : FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [hVF : VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- The fiberwise identity, constant in the cotangent variable. -/
def globalSymbolId : GlobalSymbolFunction (n := n) E E :=
  fun x _ ↦ ContinuousLinearMap.id ℂ (E x)

/-- Invertibility off zero, used with homogeneous principal data rather than full symbols. -/
def IsEllipticGlobalSymbol (a : GlobalSymbolFunction (n := n) E F) : Prop :=
  ∀ x : M, ∀ ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ,
    ξ ≠ 0 → Function.Bijective (a x ξ)

variable {E F}

/-- The actual pointwise continuous-linear inverse, totalized by zero when not invertible. -/
def globalSymbolInverse (a : GlobalSymbolFunction (n := n) E F) :
    GlobalSymbolFunction (n := n) F E := fun x ξ ↦ (a x ξ).inverse

include hFE hVE hFF hVF in
/-- In finite-rank bundle fibers, bijectivity supplies a continuous inverse. -/
theorem IsEllipticGlobalSymbol.isInvertible {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsEllipticGlobalSymbol E F a) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    (a x ξ).IsInvertible := by
  /- Bundle trivializations make both fibers finite-dimensional over ℂ.
  Bijectivity from ha gives a linear equivalence; its inverse is continuous
  because its domain is finite-dimensional. No fiber metric beyond the existing
  normed topology, compact base, or equality of model ranks is imposed. -/
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  exact ⟨(LinearEquiv.ofBijective (a x ξ).toLinearMap (ha x ξ hξ)).toContinuousLinearEquiv,
    rfl⟩

/-- Valid frame changes take the inverse matrix to the inverse coordinate matrix. -/
theorem globalSymbolInChart_globalSymbolInverse
    (a : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (z η : EuclideanSpace ℝ (Fin n)) (hz : z ∈ symbolChartDomain E F c e f) :
    globalSymbolInChart F E (globalSymbolInverse a) c f e z η =
      (globalSymbolInChart E F a c e f z η).inverse := by
  /- Both frames are linear homeomorphisms at c.symm z. Inversion reverses
  their order: (f a e⁻¹)⁻¹=e a⁻¹ f⁻¹. This remains true for the totalized
  inverse, since composition with isomorphisms preserves failure of invertibility.
  The same actual covector is used on both sides; no inverse chart derivative is needed. -/
  -- Replace each valid frame by its actual continuous linear equivalence.
  have he := e.coe_continuousLinearEquivAt_eq' (R := ℂ) hz.1.2
  have hes := e.symm_continuousLinearEquivAt_eq' (R := ℂ) hz.1.2
  have hf := f.coe_continuousLinearEquivAt_eq' (R := ℂ) hz.2
  have hfs := f.symm_continuousLinearEquivAt_eq' (R := ℂ) hz.2
  unfold globalSymbolInChart globalSymbolInverse
  rw [← he, ← hes, ← hf, ← hfs]
  -- Totalized inversion commutes with frame equivalences even for singular maps.
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

/-- The inverse has the negative homogeneity degree, with positive real scaling only. -/
theorem IsHomogeneousGlobalSymbol.inverse {m : ℝ}
    {a : GlobalSymbolFunction (n := n) E F} (ha : IsHomogeneousGlobalSymbol E F m a) :
    IsHomogeneousGlobalSymbol F E (-m) (globalSymbolInverse a) := by
  /- Apply ha at a nonzero covector. The scalar t^m is positive for t>0,
  and inversion of its complex scalar multiple multiplies the inverse by t^(-m).
  For a noninvertible fiber map both totalized inverses are zero. Thus ellipticity
  is not needed for this algebraic homogeneity identity. -/
  intro x ξ hξ t ht
  change (a x (t • ξ)).inverse = ((t ^ (-m) : ℝ) : ℂ) • (a x ξ).inverse
  rw [ha x ξ hξ t ht]
  -- Positive real powers act by a genuine scalar equivalence on the output fiber.
  let w : ℂ := (t ^ m : ℝ)
  have hw : w ≠ 0 := by
    dsimp [w]
    exact_mod_cast (Real.rpow_pos_of_pos ht m).ne'
  let e : F x ≃L[ℂ] F x :=
    (Units.mk0 w hw) • ContinuousLinearEquiv.refl ℂ (F x)
  have hscale : w • a x ξ = (e : F x →L[ℂ] F x).comp (a x ξ) := by
    ext v
    rfl
  rw [hscale, ContinuousLinearMap.inverse_equiv_comp]
  rw [Real.rpow_neg ht.le, Complex.ofReal_inv]
  ext v
  simp [e, w]

include hFE hVE hFF hVF in
/-- Inversion preserves ellipticity while reversing the two actual bundle fibers. -/
theorem IsEllipticGlobalSymbol.inverse {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsEllipticGlobalSymbol E F a) :
    IsEllipticGlobalSymbol F E (globalSymbolInverse a) := by
  /- At each nonzero covector, ha.isInvertible gives a continuous linear
  equivalence. Its inverse is again a continuous linear equivalence, so its
  underlying fiber map is bijective. Nothing is required at the zero covector. -/
  intro x ξ hξ
  exact ((ha.isInvertible (r := r) (q := q) x ξ hξ).inverse).bijective

include hFE hVE hFF hVF in
/-- Composing the inverse after the principal map gives the input-fiber identity. -/
theorem globalSymbolInverse_comp {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsEllipticGlobalSymbol E F a) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    globalSymbolComp (globalSymbolInverse a) a x ξ = globalSymbolId E x ξ := by
  /- Use ha.isInvertible at this nonzero covector. The inverse_comp_self law
  identifies the actual composite on E_x with its identity. This is a fiberwise
  product identity and does not assert an exact identity of quantized operators. -/
  exact (ha.isInvertible (r := r) (q := q) x ξ hξ).inverse_comp_self

include hFE hVE hFF hVF in
/-- Composing the principal map after its inverse gives the output-fiber identity. -/
theorem globalSymbol_comp_inverse {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsEllipticGlobalSymbol E F a) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) (hξ : ξ ≠ 0) :
    globalSymbolComp a (globalSymbolInverse a) x ξ = globalSymbolId F x ξ := by
  /- The same fiberwise continuous equivalence now gives self_comp_inverse
  on F_x. The two identities use different bundles and remain separately usable
  even though invertibility forces matching dimensions on any nonzero fiber. -/
  exact (ha.isInvertible (r := r) (q := q) x ξ hξ).self_comp_inverse

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM in
/-- A smooth elliptic principal symbol has a smooth inverse off the zero section. -/
theorem isSmoothOffZeroGlobalSymbol_inverse (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (he : IsEllipticGlobalSymbol E F a) :
    IsSmoothOffZeroGlobalSymbol (n := n) (r := q) (q := r) F E (globalSymbolInverse a) := by
  /- In a valid chart, a nonzero coordinate covector pulls back to a nonzero
  actual covector; this uses the smooth inverse chart derivative. Ellipticity
  therefore gives invertible coordinate maps throughout the punctured domain.
  Apply smoothness of inversion there to hs and use the frame inverse formula.
  Different model ranks require no chosen identification: inversion maps Hom(E,F)
  into Hom(F,E) on the open set of continuous linear equivalences. -/
  intro c hc f e _ _
  let U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0}
  let A := Function.uncurry (globalSymbolInChart E F a c e f)
  -- Ellipticity is transported through the same source and target frame equivalences.
  have hinv (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (hp : p ∈ U) : (A p).IsInvertible := by
    have hξ : covectorFromChart c (c.symm p.1) p.2 ≠ 0 := by
      intro hzero
      have hcoord := covectorInChart_covectorFromChart c hc (c.symm p.1)
        (c.map_target hp.1.1.1) p.2
      rw [hzero] at hcoord
      have hz : covectorInChart c (c.symm p.1) 0 = 0 := by ext j; rfl
      exact hp.2 (hcoord.symm.trans hz)
    change ((f.continuousLinearMapAt ℂ (c.symm p.1)).comp
      ((a (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2)).comp
        (e.symmL ℂ (c.symm p.1)))).IsInvertible
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) hp.1.2,
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) hp.1.1.2]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      ((he.isInvertible (r := r) (q := q) _ _ hξ).comp
        ContinuousLinearMap.isInvertible_equiv)
  -- Complex-analytic inversion is in particular real smooth on this open invertible locus.
  have hi : ContDiffOn ℝ ∞ (fun p ↦ (A p).inverse) U := by
    intro p hp
    exact ((hinv p hp).contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ |>.comp_contDiffWithinAt
      p (hs c hc e f p hp)
  have hdomain : symbolChartDomain F E c f e ×ˢ {ξ | ξ ≠ 0} = U := by
    ext p
    simp only [U, symbolChartDomain, Set.mem_prod, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  rw [hdomain]
  apply hi.congr
  intro p hp
  exact globalSymbolInChart_globalSymbolInverse a c e f p.1 p.2 hp.1

variable [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hE in
/-- The fiberwise identity is a global symbol of order zero. -/
theorem isGlobalSymbol_globalSymbolId :
    IsGlobalSymbol (n := n) (r := r) (q := r) E E 0 (globalSymbolId E) := by
  /- In two possibly different atlas frames, the identity is their smooth
  transition matrix, independent of frequency. Its spatial derivatives are
  bounded on each compact subset, while positive frequency derivatives vanish.
  The zero-order weight is one. No compactness of the full base is needed. -/
  classical
  intro c hc e f _ _
  let U := symbolChartDomain E E c e f
  let p : EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    fun z ↦ (f.continuousLinearMapAt ℂ (c.symm z)).comp (e.symmL ℂ (c.symm z))
  have hU : IsOpen U := isOpen_symbolChartDomain E E c e f
  -- The two original frames express the identity by their forward transition.
  have hp : ContDiffOn ℝ ∞ p U := by
    have hcSmooth := contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) hc)
    have htransition := contDiffOn_coordChangeL_comp E e f U c.symm
      (hcSmooth.mono (fun z hz ↦ hz.1.1)) (fun z hz ↦ ⟨hz.1.2, hz.2⟩)
    apply htransition.congr
    intro z hz
    ext v
    simp only [p, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [f.continuousLinearMapAt_apply_of_mem ℂ hz.2, e.symmL_apply hz.1.2,
      e.coordChangeL_apply f ⟨hz.1.2, hz.2⟩]
  have hcoordinates : globalSymbolInChart E E (globalSymbolId E) c e f =
      fun z _ ↦ p z := by
    funext z ξ
    simp only [globalSymbolInChart, globalSymbolId, ContinuousLinearMap.id_comp, p]
  rw [hcoordinates]
  refine ⟨?_, ?_⟩
  · intro z hz
    exact ((hp.contDiffAt (hU.mem_nhds hz.1)).comp z contDiffAt_fst).contDiffWithinAt
  · intro K hKU hK i j
    cases j with
    | zero =>
      -- Every spatial derivative is bounded on this original compact coordinate set.
      let L := (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))).symm
      have hLp : ContDiffOn ℝ ∞ (fun z ↦ L (p z)) U :=
        L.contDiff.comp_contDiffOn hp
      have hderiv : ContinuousOn (fun z ↦
          ‖iteratedFDeriv ℝ i (fun y ↦ L (p y)) z‖) K :=
        ((ContinuousOn.continuousOn_iteratedFDeriv hLp hU (by simp)).mono hKU).norm
      obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hderiv).bddAbove
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro x hx ξ
      simp only [symbolDerivative, iteratedFDeriv_zero_eq_comp, Function.comp_def,
        Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
      exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    | succ j =>
      -- The original coordinate matrix is constant in frequency, so these derivatives vanish.
      refine ⟨0, le_rfl, ?_⟩
      intro x hx ξ
      simp [symbolDerivative, iteratedFDeriv_succ_const]

/-- The actual identity section packaged in the order-zero symbol module. -/
def globalIdentitySymbol : globalSymbolSpace (n := n) (r := r) (q := r) E E 0 :=
  ⟨globalSymbolId E, isGlobalSymbol_globalSymbolId⟩

variable [hT : T2Space M]
  (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
  (B : QuantizationPresentation (n := n) (r := q) (q := r) F E)

include hM hT hE hF in
/-- Regularized inverse and principal data multiply to the identity modulo every symbol order. -/
theorem isGlobalSymbol_inverse_regularized_comp_sub_id (m l : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a) :
    IsGlobalSymbol (n := n) (r := r) (q := r) E E l
      (globalSymbolComp (B.regularizedSymbolFunction (globalSymbolInverse a))
        (A.regularizedSymbolFunction a) - globalSymbolId E) := by
  /- The two regularizations are smooth symbols, using smoothness and negative
  homogeneity of the inverse. On every compact coordinate set, both recover
  their original data beyond a common radius; their product is then the identity.
  Enlarge the compact set within the chart before differentiating, so the difference
  vanishes at high frequencies on a neighborhood. Bounded-frequency derivative
  estimates give every real order l. This is pointwise symbol multiplication. -/
  classical
  have hsInv := isSmoothOffZeroGlobalSymbol_inverse a hs he
  have hhInv := hh.inverse
  have hA := A.isGlobalSymbol_regularizedSymbolFunction m a hs hh
  have hB := B.isGlobalSymbol_regularizedSymbolFunction (-m) (globalSymbolInverse a)
    hsInv hhInv
  intro c hc e f _ _
  let U := symbolChartDomain E E c e f
  let p := globalSymbolInChart E E
    (globalSymbolComp (B.regularizedSymbolFunction (globalSymbolInverse a))
      (A.regularizedSymbolFunction a) - globalSymbolId E) c e f
  have hU : IsOpen U := isOpen_symbolChartDomain E E c e f
  have hsplit : p =
      globalSymbolInChart E E
        (globalSymbolComp (B.regularizedSymbolFunction (globalSymbolInverse a))
          (A.regularizedSymbolFunction a)) c e f -
        globalSymbolInChart E E (globalSymbolId E) c e f := by
    ext z η v
    simp [p, globalSymbolInChart]
  -- Both specified regularizations are smooth; no quantized composition is used.
  have hp : ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ Set.univ) := by
    rw [hsplit]
    exact ((hB.globalSymbolComp hA) c hc e f).1.sub
      ((isGlobalSymbol_globalSymbolId (E := E) (r := r)) c hc e f).1
  change IsSymbol U l p
  refine ⟨hp, ?_⟩
  intro K hKU hK i j
  -- Work in smaller compact neighborhoods carrying one genuine intermediate F-frame.
  have hlocal (z : U) : ∃ N : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact N ∧ z.val ∈ interior N ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ N, ∀ η, ‖symbolDerivative p i j x η‖ ≤
          C * (1 + ‖η‖) ^ (l - (j : ℝ)) := by
    let g := trivializationAt (EuclideanSpace ℂ (Fin q)) F (c.symm z.val)
    let V := symbolChartDomain E F c e g ∩ symbolChartDomain F E c g f
    have hg : c.symm z.val ∈ g.baseSet := mem_baseSet_trivializationAt _ _ _
    have hV : IsOpen V := (isOpen_symbolChartDomain E F c e g).inter
      (isOpen_symbolChartDomain F E c g f)
    have hzV : z.val ∈ V :=
      ⟨⟨⟨z.property.1.1, z.property.1.2⟩, hg⟩,
        ⟨⟨z.property.1.1, hg⟩, z.property.2⟩⟩
    have hVU : V ⊆ U := fun y hy ↦ ⟨⟨hy.1.1.1, hy.1.1.2⟩, hy.2.2⟩
    obtain ⟨L, hL, hzL, hLV⟩ := exists_compact_subset hV hzV
    obtain ⟨N, hN, hzN, hNL⟩ := exists_compact_subset isOpen_interior hzL
    obtain ⟨RA, hRA, hrecoverA⟩ :=
      A.regularizedSymbolFunction_eq_inChart_at_high_frequency a c hc e g L hL
        (hLV.trans Set.inter_subset_left)
    obtain ⟨RB, hRB, hrecoverB⟩ :=
      B.regularizedSymbolFunction_eq_inChart_at_high_frequency (globalSymbolInverse a)
        c hc g f L hL (hLV.trans Set.inter_subset_right)
    -- Enlarge before differentiating: the high-frequency error vanishes on interior L.
    have hsupp : ∀ y ∈ interior L, ∀ η, max RA RB ≤ ‖η‖ → p y η = 0 := by
      intro y hy η hη
      have hyV := hLV (interior_subset hy)
      have hηne : η ≠ 0 := norm_pos_iff.mp
        (hRA.trans_le ((le_max_left RA RB).trans hη))
      have hξne : covectorFromChart c (c.symm y) η ≠ 0 := by
        intro hzero
        have hrecover := covectorInChart_covectorFromChart c hc (c.symm y)
          (c.map_target hyV.1.1.1) η
        rw [hzero] at hrecover
        apply hηne
        apply (WithLp.ext_iff 2).mpr
        funext k
        have hk := congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v k) hrecover
        change (0 : ℝ) = η k at hk
        exact hk.symm
      rw [hsplit]
      simp only [Pi.sub_apply]
      rw [globalSymbolInChart_globalSymbolComp _ _ c e g f y η hyV.1.2]
      simp only [symbolComp]
      rw [hrecoverB y (interior_subset hy) η ((le_max_right RA RB).trans hη),
        hrecoverA y (interior_subset hy) η ((le_max_left RA RB).trans hη)]
      change symbolComp (globalSymbolInChart F E (globalSymbolInverse a) c g f)
          (globalSymbolInChart E F a c e g) y η -
        globalSymbolInChart E E (globalSymbolId E) c e f y η = 0
      rw [← globalSymbolInChart_globalSymbolComp (globalSymbolInverse a) a
        c e g f y η hyV.1.2]
      unfold globalSymbolInChart
      rw [globalSymbolInverse_comp (r := r) (q := q) he (c.symm y)
        (covectorFromChart c (c.symm y) η) hξne, sub_self]
    have hint : interior L ⊆ U := (interior_subset.trans hLV).trans hVU
    have hsmoothing := isSmoothingSymbol_of_frequency_support isOpen_interior p (max RA RB)
      (hp.mono (Set.prod_mono hint subset_rfl)) hsupp l
    obtain ⟨C, hC, hbound⟩ := hsmoothing.2 N hNL hN i j
    exact ⟨N, hN, hzN, C, hC, hbound⟩
  choose N hN hzN C hC hbound using hlocal
  -- A finite subcover gives one estimate on the original compact set, for this real order.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (N z))
    (fun _ ↦ isOpen_interior) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzN ⟨x, hKU hx⟩⟩)
  refine ⟨∑ z ∈ t, C z, Finset.sum_nonneg (fun z _ ↦ hC z), ?_⟩
  intro x hx η
  obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
  apply (hbound z x (interior_subset hxz) η).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  exact Finset.single_le_sum (fun z _ ↦ hC z) hzt

include hM hT hE hF in
/-- The opposite regularized product also equals its own fiber identity modulo every order. -/
theorem isGlobalSymbol_regularized_comp_inverse_sub_id (m l : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (he : IsEllipticGlobalSymbol E F a) :
    IsGlobalSymbol (n := n) (r := q) (q := q) F F l
      (globalSymbolComp (A.regularizedSymbolFunction a)
        (B.regularizedSymbolFunction (globalSymbolInverse a)) - globalSymbolId F) := by
  /- Use the same compact-neighborhood and high-frequency recovery argument,
  now with the opposite product a a⁻¹ on F_x. All derivatives of the error are
  supported in a locally bounded frequency region, which yields any prescribed
  real order. Quantized operator remainders still require the composition calculus. -/
  -- Reverse the same two presentations and apply the proved input-fiber estimate to a⁻¹.
  have hsInv := isSmoothOffZeroGlobalSymbol_inverse a hs he
  have herror := isGlobalSymbol_inverse_regularized_comp_sub_id (A := B) (B := A)
    (-m) l (globalSymbolInverse a) hsInv hh.inverse (he.inverse (r := r) (q := q))
  -- Inversion is involutive off zero; the original regularization suppresses zero values.
  have hback : A.regularizedSymbolFunction (globalSymbolInverse (globalSymbolInverse a)) =
      A.regularizedSymbolFunction a := by
    apply A.regularizedSymbolFunction_congr
    intro x ξ hξ
    exact (he.isInvertible (r := r) (q := q) x ξ hξ).inverse_inverse
  rw [hback] at herror
  exact herror

end AtiyahSinger
