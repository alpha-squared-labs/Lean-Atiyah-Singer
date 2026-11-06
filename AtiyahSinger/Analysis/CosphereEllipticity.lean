/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereContinuousTopology

/-!
# Ellipticity on the cosphere

Public module ID: M0414.

Ellipticity means bijectivity on every unit covector. It is equivalent to
invertibility of any positive homogeneous extension at every nonzero covector.
The compact-open topology provides open invertibility and local convex control
without a global continuity assumption on the original fiber norms.
References: SG III.4.2--4.4 and III.7.10--7.11; the cosphere and approximation
interfaces are project deductions. No full-symbol ellipticity is redefined.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory
open scoped Manifold ContDiff ComplexConjugate Topology

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [hFE : FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [hVE : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [hFF : FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [hVF : VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- The usual ellipticity condition on unit cotangent vectors. -/
def IsEllipticCosphereSymbol (a : CosphereSymbolFunction (E := E) (F := F) g) : Prop :=
  ∀ z : CosphereBundle g, Function.Bijective (a z)

/-- The actual pointwise inverse Hom section, totalized by zero. -/
def cosphereSymbolInverse (a : CosphereSymbolFunction (E := E) (F := F) g) :
    CosphereSymbolFunction (E := F) (F := E) g :=
  fun z ↦ (a z).inverse

/-- An elliptic restriction detects invertibility at every nonzero covector. -/
theorem isEllipticCosphereSymbol_restriction_iff (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F) (ha : IsHomogeneousGlobalSymbol E F m a) :
    IsEllipticCosphereSymbol g (cosphereRestriction g a) ↔ IsEllipticGlobalSymbol E F a := by
  /- Any nonzero covector is its positive length times its unit direction.
  Homogeneity expresses the corresponding Hom map as a nonzero scalar multiple
  of its unit value, and such scalar multiplication preserves bijectivity. -/
  constructor
  · intro he x ξ hξ
    -- Radial reconstruction changes the unit value only by a nonzero scalar.
    rw [← cosphereExtension_restriction g m a ha x ξ hξ,
      cosphereExtension_of_ne_zero g m _ x ξ hξ]
    have hw : ((g.length x ξ ^ m : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (g.length_pos x ξ hξ) m).ne'
    exact (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr hw)).comp
      (he (g.radial ⟨⟨x, ξ⟩, hξ⟩))
  · intro he z
    exact he z.val.proj z.val.snd (g.cosphere_ne_zero z)

/-- The radial extension is elliptic exactly when its cosphere data are elliptic. -/
theorem isEllipticGlobalSymbol_cosphereExtension_iff (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    IsEllipticGlobalSymbol E F (cosphereExtension g m a) ↔ IsEllipticCosphereSymbol g a := by
  /- Use homogeneity of the extension and its exact restriction formula.
  Positive lengths have nonzero real powers for every real degree, including negative degrees. -/
  -- The extension has the original degree, and restriction recovers the same section.
  have h := isEllipticCosphereSymbol_restriction_iff g m (cosphereExtension g m a)
    (isHomogeneousGlobalSymbol_cosphereExtension g m a)
  rw [cosphereRestriction_extension] at h
  exact h.symm

include hFE hVE hFF hVF in
/-- An elliptic fiber inverse is a genuine inverse in the input fiber. -/
theorem cosphereSymbolInverse_comp
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsEllipticCosphereSymbol g a) (z : CosphereBundle g) :
    (cosphereSymbolInverse g a z).comp (a z) = ContinuousLinearMap.id ℂ (E z.val.proj) := by
  /- The bundle fibers are finite-dimensional, so a bijective continuous
  linear map has a continuous inverse. The totalized inverse agrees with it, and
  inverse followed by the original map is the identity on the input fiber. -/
  -- Finite rank makes the inverse of the given bijection continuous.
  let : FiniteDimensional ℂ (E z.val.proj) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E z.val.proj
  let : FiniteDimensional ℂ (F z.val.proj) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F z.val.proj
  have hi : (a z).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (a z).toLinearMap (ha z)).toContinuousLinearEquiv, rfl⟩
  exact hi.inverse_comp_self

include hFE hVE hFF hVF in
/-- An elliptic fiber inverse is a genuine inverse in the output fiber. -/
theorem cosphereSymbol_comp_inverse
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsEllipticCosphereSymbol g a) (z : CosphereBundle g) :
    (a z).comp (cosphereSymbolInverse g a z) = ContinuousLinearMap.id ℂ (F z.val.proj) := by
  /- The same finite-dimensional continuous inverse now gives the
  opposite composition identity on F. The two identities intentionally have different fibers. -/
  -- The opposite composition acts on the actual output fiber.
  let : FiniteDimensional ℂ (E z.val.proj) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E z.val.proj
  let : FiniteDimensional ℂ (F z.val.proj) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F z.val.proj
  have hi : (a z).IsInvertible :=
    ⟨(LinearEquiv.ofBijective (a z).toLinearMap (ha z)).toContinuousLinearEquiv, rfl⟩
  exact hi.self_comp_inverse

include hFE hVE hFF hVF in
/-- Pointwise inversion preserves ellipticity. -/
theorem IsEllipticCosphereSymbol.inverse
    {a : CosphereSymbolFunction (E := E) (F := F) g} (ha : IsEllipticCosphereSymbol g a) :
    IsEllipticCosphereSymbol g (cosphereSymbolInverse g a) := by
  /- At every unit covector the original map is a continuous linear
  equivalence by finite dimension. Its inverse is again bijective, with the bundles reversed. -/
  intro z
  -- The two established identities provide inverse functions on the original fibers.
  have hleft := cosphereSymbolInverse_comp (r := r) (q := q) g a ha z
  have hright := cosphereSymbol_comp_inverse (r := r) (q := q) g a ha z
  exact ⟨fun x y h ↦ by
    have hx := DFunLike.congr_fun hright x
    have hy := DFunLike.congr_fun hright y
    change a z (cosphereSymbolInverse g a z x) = x at hx
    change a z (cosphereSymbolInverse g a z y) = y at hy
    exact hx.symm.trans ((congrArg (a z) h).trans hy),
    fun x ↦ ⟨a z x, DFunLike.congr_fun hleft x⟩⟩

/-- Inversion of a continuous elliptic cosphere section is continuous. -/
theorem isContinuousCosphereSymbol_inverse
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (hc : IsContinuousCosphereSymbol (r := r) (q := q) g a)
    (he : IsEllipticCosphereSymbol g a) :
    IsContinuousCosphereSymbol (r := q) (q := r) g (cosphereSymbolInverse g a) := by
  /- In valid bundle frames use continuity of inversion on invertible
  finite-dimensional Hom maps. Frame changes interchange source and target in the
  inverse formula. Ellipticity keeps the section in this open invertible locus. -/
  classical
  change Continuous (cosphereSymbolTotal (r := q) (q := r) g (cosphereSymbolInverse g a))
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z₀.val.proj
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z₀.val.proj
  have hsource := (continuousAt_hom_bundle (RingHom.id ℂ)
    (cosphereSymbolTotal (r := r) (q := q) g a) (x₀ := z₀)).mp hc.continuousAt
  have hbase := hsource.1
  let A (z : CosphereBundle g) := (f.continuousLinearMapAt ℂ z.val.proj).comp
    ((a z).comp (e.symmL ℂ z.val.proj))
  have hi : (A z₀).IsInvertible := by
    let : FiniteDimensional ℂ (E z₀.val.proj) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E z₀.val.proj
    let : FiniteDimensional ℂ (F z₀.val.proj) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F z₀.val.proj
    have ha : (a z₀).IsInvertible :=
      ⟨(LinearEquiv.ofBijective (a z₀).toLinearMap (he z₀)).toContinuousLinearEquiv, rfl⟩
    dsimp [A]
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ)
      (mem_baseSet_trivializationAt _ _ _),
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ)
        (mem_baseSet_trivializationAt _ _ _)]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (ha.comp ContinuousLinearMap.isInvertible_equiv)
  -- Invert the continuous coordinate map, then return to the original moving fibers.
  have hinverse := (hi.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hsource.2
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hbase, hinverse.congr_of_eventuallyEq ?_⟩
  filter_upwards [hbase.preimage_mem_nhds (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)),
    hbase.preimage_mem_nhds (f.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _))] with z hez hfz
  change (e.continuousLinearMapAt ℂ z.val.proj).comp
    ((a z).inverse.comp (f.symmL ℂ z.val.proj)) = (A z).inverse
  change z.val.proj ∈ e.baseSet at hez
  change z.val.proj ∈ f.baseSet at hfz
  dsimp [A]
  rw [← e.coe_continuousLinearEquivAt_eq' (R := ℂ) hez,
    ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) hez,
    ← f.coe_continuousLinearEquivAt_eq' (R := ℂ) hfz,
    ← f.symm_continuousLinearEquivAt_eq' (R := ℂ) hfz]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

/-- Inversion of a smooth elliptic cosphere section is smooth. -/
theorem isSmoothCosphereSymbol_inverse
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (hs : IsSmoothCosphereSymbol (r := r) (q := q) g a)
    (he : IsEllipticCosphereSymbol g a) :
    IsSmoothCosphereSymbol (r := q) (q := r) g (cosphereSymbolInverse g a) := by
  /- The degree-zero radial extension of the inverse is the inverse of
  the degree-zero extension off zero. Use smooth inversion on the elliptic locus
  and the proved global smooth inverse theorem. The chosen zero values agree as well. -/
  -- The degree-zero extension is elliptic on precisely the same nonzero covectors.
  have hext := (isEllipticGlobalSymbol_cosphereExtension_iff g 0 a).mpr he
  have hglobal := isSmoothOffZeroGlobalSymbol_inverse (cosphereExtension g 0 a) hs hext
  have heq : cosphereExtension g 0 (cosphereSymbolInverse g a) =
      globalSymbolInverse (cosphereExtension g 0 a) := by
    funext x ξ
    by_cases hξ : ξ = 0
    · subst ξ
      simp [cosphereExtension_zero_covector, globalSymbolInverse]
    · simp [cosphereExtension, hξ, cosphereSymbolInverse, globalSymbolInverse]
      rfl
  change IsSmoothOffZeroGlobalSymbol F E (cosphereExtension g 0 (cosphereSymbolInverse g a))
  rw [heq]
  exact hglobal

/-- Inverse radial extensions have the negative degree. -/
theorem cosphereExtension_inverse (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereExtension g (-m) (cosphereSymbolInverse g a) =
      globalSymbolInverse (cosphereExtension g m a) := by
  /- Away from zero the real-power scalar is nonzero, and the inverse
  scalar is length^(-m). Totalized inversion obeys this also for a noninvertible
  fiber map. At zero both sides are zero; ellipticity is not required for this identity. -/
  classical
  funext x ξ
  by_cases hξ : ξ = 0
  · subst ξ
    simp [cosphereExtension_zero_covector, globalSymbolInverse]
  · -- A nonzero scalar is a continuous equivalence, also for singular Hom maps.
    rw [cosphereExtension_of_ne_zero g (-m) _ x ξ hξ]
    change _ = (cosphereExtension g m a x ξ).inverse
    rw [cosphereExtension_of_ne_zero g m a x ξ hξ]
    let w : ℂ := (g.length x ξ ^ m : ℝ)
    have hw : w ≠ 0 := by
      dsimp [w]
      exact_mod_cast (Real.rpow_pos_of_pos (g.length_pos x ξ hξ) m).ne'
    let e : F x ≃L[ℂ] F x :=
      (Units.mk0 w hw) • ContinuousLinearEquiv.refl ℂ (F x)
    have hscale : w • a (g.radial ⟨⟨x, ξ⟩, hξ⟩) =
        (e : F x →L[ℂ] F x).comp (a (g.radial ⟨⟨x, ξ⟩, hξ⟩)) := by
      ext v
      rfl
    change ((g.length x ξ ^ (-m) : ℝ) : ℂ) •
      (a (g.radial ⟨⟨x, ξ⟩, hξ⟩)).inverse = (w • a (g.radial ⟨⟨x, ξ⟩, hξ⟩)).inverse
    rw [hscale]
    erw [ContinuousLinearMap.inverse_equiv_comp]
    rw [Real.rpow_neg (g.length_pos x ξ hξ).le, Complex.ofReal_inv]
    ext v
    change F x at v
    change w⁻¹ • (a (g.radial ⟨⟨x, ξ⟩, hξ⟩)).inverse v =
      (a (g.radial ⟨⟨x, ξ⟩, hξ⟩)).inverse (e.symm v)
    have heval : e.symm v = w⁻¹ • v := by simp [e]
    rw [heval]
    exact (ContinuousLinearMap.map_smul _ _ _).symm

attribute [local instance] continuousCosphereSymbolTopology

/-- Elliptic continuous cosphere sections form an open subset on a compact base. -/
theorem isOpen_isEllipticCosphereSymbol [T2Space M] [CompactSpace M] :
    IsOpen {a : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g |
      IsEllipticCosphereSymbol g a.val} := by
  /- In each original Hom frame, invertible fiber maps form an open set. Returning
  through the frame identities proves that the invertible maps form an open subset
  of the Hom total space. Compactness of the cosphere makes the condition that a
  continuous map has its whole range in this subset open. Pull it back along the
  section inclusion to obtain openness in the actual compact-open topology. -/
  classical
  let H := TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (fun x ↦ E x →L[ℂ] F x)
  let V : Set H := {z | Function.Bijective z.snd}
  -- Invertibility is open in each original Hom frame, without global fiber norms.
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z₀ hz₀
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z₀.proj
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z₀.proj
    let A (z : H) := (f.continuousLinearMapAt ℂ z.proj).comp
      (z.snd.comp (e.symmL ℂ z.proj))
    have hsource := (continuousAt_hom_bundle (RingHom.id ℂ)
      (fun z : H ↦ z) (x₀ := z₀)).mp continuousAt_id
    have hbase : ContinuousAt (fun z : H ↦ z.proj) z₀ := hsource.1
    have hA : ContinuousAt A z₀ := hsource.2
    have hi₀ : (A z₀).IsInvertible := by
      let : FiniteDimensional ℂ (E z₀.proj) :=
        VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E z₀.proj
      let : FiniteDimensional ℂ (F z₀.proj) :=
        VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F z₀.proj
      have hi : z₀.snd.IsInvertible :=
        ⟨(LinearEquiv.ofBijective z₀.snd.toLinearMap hz₀).toContinuousLinearEquiv, rfl⟩
      dsimp [A]
      rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ)
        (mem_baseSet_trivializationAt _ _ _),
        ← e.symm_continuousLinearEquivAt_eq' (R := ℂ)
          (mem_baseSet_trivializationAt _ _ _)]
      exact ContinuousLinearMap.isInvertible_equiv.comp
        (hi.comp ContinuousLinearMap.isInvertible_equiv)
    have hnear := hA.preimage_mem_nhds
      (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hi₀)
    filter_upwards [hnear,
      hbase.preimage_mem_nhds (e.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt _ _ _)),
      hbase.preimage_mem_nhds (f.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt _ _ _))] with z hz hez hfz
    change (A z).IsInvertible at hz
    change z.proj ∈ e.baseSet at hez
    change z.proj ∈ f.baseSet at hfz
    dsimp [A] at hz
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) hfz,
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) hez,
      ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv] at hz
    exact hz.bijective
  -- Compactness turns this open target condition into an open section condition.
  let : CompactSpace (CosphereBundle g) := g.compactSpace_cosphere
  have hmaps := ContinuousMap.isOpen_setOfPred_range_subset
    (X := CosphereBundle g) hV
  have hinc : Continuous (continuousCosphereSymbolMap (r := r) (q := q)
      (E := E) (F := F) g) := continuous_induced_dom
  convert hmaps.preimage hinc using 1
  ext a
  change (∀ z, Function.Bijective (a.val z)) ↔
    Set.range (continuousCosphereSymbolMap (r := r) (q := q) g a) ⊆ V
  simp only [Set.range_subset_iff, V]
  rfl

/-- Nearby continuous sections can be joined inside the elliptic locus. -/
theorem exists_elliptic_convex_neighborhood [T2Space M] [CompactSpace M]
    (a : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g)
    (ha : IsEllipticCosphereSymbol g a.val) :
    ∃ U : Set (ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g),
      IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U, ∀ c ∈ U, ∀ t : unitInterval,
        IsEllipticCosphereSymbol g (cosphereInterpolation g b.val c.val t) := by
  /- Joint continuity of affine interpolation and compactness of its interval
  parameter give a common neighborhood of (a,a) whose paths stay elliptic. An open
  product neighborhood then supplies one neighborhood for both endpoints. The
  conclusion requires pairwise paths to stay in the elliptic locus, and does not
  assert that this chosen neighborhood itself is convex. No smooth bundle
  structure or continuous variation of the original fiber norms is assumed. -/
  classical
  let S := ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g
  let P := (S × S) × unitInterval
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := fun x ↦ E x →L[ℂ] F x
  -- Native finite-dimensional cotangent coordinates give local compactness for evaluation.
  let : LocallyCompactSpace (ModelProd (EuclideanSpace ℝ (Fin n)) (CotangentModel n)) :=
    inferInstanceAs (LocallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × CotangentModel n))
  let : LocallyCompactSpace (CotangentTotalSpace (n := n) (M := M)) :=
    ChartedSpace.locallyCompactSpace
      (ModelProd (EuclideanSpace ℝ (Fin n)) (CotangentModel n)) _
  let : LocallyCompactSpace (CosphereBundle g) := g.isClosed_cosphere.locallyCompactSpace
  have hinc : Continuous (continuousCosphereSymbolMap (r := r) (q := q)
      (E := E) (F := F) g) := continuous_induced_dom
  have heval : Continuous (fun p : S × CosphereBundle g ↦
      cosphereSymbolTotal (r := r) (q := q) g p.1.val p.2) :=
    continuous_eval.comp
      ((hinc.comp continuous_fst).prodMk continuous_snd)
  -- Both endpoints and the interval parameter vary jointly in the same Hom fiber.
  have hfamily : Continuous (fun p : P × CosphereBundle g ↦
      cosphereSymbolTotal (r := r) (q := q) g
        (cosphereInterpolation g p.1.1.1.val p.1.1.2.val p.1.2) p.2) := by
    have hb : Continuous (fun p : P × CosphereBundle g ↦
        cosphereSymbolTotal (r := r) (q := q) g p.1.1.1.val p.2) := heval.comp
      (((continuous_fst.comp continuous_fst).comp continuous_fst).prodMk continuous_snd)
    have hc : Continuous (fun p : P × CosphereBundle g ↦
        cosphereSymbolTotal (r := r) (q := q) g p.1.1.2.val p.2) := heval.comp
      (((continuous_snd.comp continuous_fst).comp continuous_fst).prodMk continuous_snd)
    have hl : Continuous (fun p : P × CosphereBundle g ↦
        ((1 - (p.1.2 : ℝ) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_const.sub (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
    have hr : Continuous (fun p : P × CosphereBundle g ↦ ((p.1.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    apply continuous_iff_continuousAt.mpr
    intro p
    let e := trivializationAt H V p.2.val.proj
    have h₁ := (FiberBundle.continuousAt_totalSpace H _).mp (hb.continuousAt (x := p))
    have h₂ := (FiberBundle.continuousAt_totalSpace H _).mp (hc.continuousAt (x := p))
    apply (FiberBundle.continuousAt_totalSpace H _).mpr
    refine ⟨h₁.1, ?_⟩
    apply ((hl.continuousAt.smul h₁.2).add
      (hr.continuousAt.smul h₂.2)).congr_of_eventuallyEq
    filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt H V p.2.val.proj))] with y hy
    exact ((e.linear ℂ hy).1 _ _).trans
      (congrArg₂ (· + ·) ((e.linear ℂ hy).2 _ _) ((e.linear ℂ hy).2 _ _))
  let f : P → S := fun p ↦
    ⟨cosphereInterpolation g p.1.1.val p.1.2.val p.2,
      hfamily.comp (continuous_const.prodMk continuous_id)⟩
  have hf : Continuous f := by
    rw [continuous_induced_rng]
    exact ContinuousMap.continuous_of_continuous_uncurry
      (continuousCosphereSymbolMap (r := r) (q := q) g ∘ f) hfamily
  have hdiag (t : unitInterval) : f ((a, a), t) = a := by
    apply Subtype.ext
    change ((1 - (t : ℝ) : ℝ) : ℂ) • a.val + ((t : ℝ) : ℂ) • a.val = a.val
    rw [← add_smul, ← Complex.ofReal_add]
    simp
  -- Compactness of the parameter interval gives one endpoint neighborhood for every time.
  let W : Set P := {p | IsEllipticCosphereSymbol g (f p).val}
  have hW : IsOpen W := (isOpen_isEllipticCosphereSymbol g).preimage hf
  have hnear : ∀ᶠ p : S × S in 𝓝 (a, a), ∀ t : unitInterval,
      IsEllipticCosphereSymbol g (f (p, t)).val := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (X := S × S) (Y := unitInterval) (x₀ := (a, a))
      (P := fun p t ↦ IsEllipticCosphereSymbol g (f (p, t)).val) ?_
    · simpa only [Set.mem_univ, forall_true_left] using h
    · intro t _
      apply hW.mem_nhds
      change IsEllipticCosphereSymbol g (f ((a, a), t)).val
      rw [hdiag]
      exact ha
  -- Intersect the two open endpoint neighborhoods so any pair in the result is admissible.
  obtain ⟨U, V, hU, haU, hV, haV, hUV⟩ := mem_nhds_prod_iff'.mp hnear
  refine ⟨U ∩ V, hU.inter hV, ⟨haU, haV⟩, ?_⟩
  intro b hb c hc t
  exact hUV (show (b, c) ∈ U ×ˢ V from ⟨hb.1, hc.2⟩) t

variable
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hE hF in
/-- Every continuous elliptic section has a nearby smooth elliptic representative. -/
theorem exists_smooth_elliptic_near [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (a : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g)
    (ha : IsEllipticCosphereSymbol g a.val)
    (U : Set (ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g))
    (hU : IsOpen U) (haU : a ∈ U) :
    ∃ b : smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g,
      smoothCosphereToContinuous (r := r) (q := q) g b ∈ U ∧ IsEllipticCosphereSymbol g b.val := by
  /- Intersect the requested neighborhood with the open elliptic locus.
  It still contains a. Smooth density supplies a section in the intersection,
  simultaneously preserving the requested closeness and pointwise invertibility. -/
  obtain ⟨b, hb⟩ := exists_smoothCosphere_mem g a
    (U ∩ {c | IsEllipticCosphereSymbol g c.val})
    (hU.inter (isOpen_isEllipticCosphereSymbol g)) ⟨haU, ha⟩
  -- The same smooth section satisfies both membership conditions in the intersection.
  exact ⟨b, hb.1, hb.2⟩

end AtiyahSinger
