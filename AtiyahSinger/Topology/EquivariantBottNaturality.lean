/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactRepresentationAveraging
public import AtiyahSinger.Topology.EquivariantBottRestriction
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality

/-!
# Bott classes for arbitrary finite continuous complex representations

Public module ID: M1757.

The original exterior class is natural under complex linear equivariant
homeomorphisms, even when they do not preserve the supplied Hermitian metrics.
The proof compares those actual metrics on the same exterior carrier through
their positive convex path, with the singleton zero as common compact control.

For a general normed complex representation, invariant coordinates are obtained
by the existing Haar averaging construction. The conjugated action is literally
`e (g • e.symm w)`. The Bott class on the original base is the existing proper
pullback of the original exterior class in those coordinates. Its comparison
with every unitary model makes the result independent of coordinates and metric.
In particular no inner product is installed on a supremum-norm coordinate space.

ASI I, pp.493--496, equation (2.7), applies to any finite complex representation
of a compact Lie group. The explicit coordinate transport and metric comparison
are standard expansions of that construction. These statements do not use an
index normalization or the index theorem. The invariant-coordinate existence is
proved below, as are metric naturality, coordinate independence and group restriction.
The independent Bott bijectivity theorem remains open.
The action adapters below are implementation data, not separate mathematical nodes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Hermitian

variable {V W : Type}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [DistribMulAction G V] [SMulCommClass G ℂ V] [ContinuousSMul G V]
  [DistribMulAction G W] [SMulCommClass G ℂ W] [ContinuousSMul G W]

set_option maxHeartbeats 800000 in

open Bundle in
/-- Complex linear equivariant transport preserves the original Bott class for any two
invariant Hermitian metrics; the transport need not be an isometry. -/
theorem equivariantExteriorBottClass_natural
    (hV : ∀ (g : G) (x y : V), inner ℂ (g • x) (g • y) = inner ℂ x y)
    (hW : ∀ (g : G) (x y : W), inner ℂ (g • x) (g • y) = inner ℂ x y)
    (e : V ≃L[ℂ] W) (he : ∀ (g : G) (x : V), e (g • x) = g • e x) :
    equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ he e.toHomeomorph.isProperMap
        (equivariantExteriorBottClass hW) = equivariantExteriorBottClass hV := by
  /- Stage 1: pull the W metric back by the specified e. The exterior map of e
  identifies the pulled W parity bundles and boundary with the V exterior
  construction for precisely that pulled metric. It preserves the zero control
  and intertwines the given actions by he, without assuming that e is unitary.
  Stage 2: interpolate the original V metric and this pulled metric by their
  positive real convex combination. On the fixed exterior algebra the contraction
  depends continuously on this form. Wedge minus contraction has square
  -h_t(v,v), strictly negative off zero for every t in the closed unit interval.
  The inverse is the same boundary divided by -h_t(v,v), jointly continuous there.
  Both metrics are invariant, hence the entire path is equivariant with the
  same parity actions and the one compact control {0}. Stage 3: choose a norm
  radial time cutoff, zero near the origin and one outside a ball. The V norm
  is invariant by hV, so the ratio of the path boundary and initial boundary
  defines a global equivariant target isomorphism, extended by the identity
  near zero. Outside the ball it is the endpoint ratio. Apply the original
  isomorphism relation after enlarging the control, and the proper-pullback
  generator formula. This explicit invariant cutoff avoids the compact-group
  premise of the generic homotopy theorem. Dimension zero is included, and
  Bott bijectivity is not used. -/
  classical
  let := exteriorAlgebraNormedAddCommGroup V
  let := exteriorAlgebraNormedSpace V
  let := exteriorAlgebraNormedAddCommGroup W
  let := exteriorAlgebraNormedSpace W
  let PV (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let PW (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i
  let Fm := ExteriorAlgebra.map e.toLinearMap
  let Gm := ExteriorAlgebra.map e.symm.toLinearMap
  -- The actual exterior maps preserve parity and are inverse on vector generators.
  have hparityF (i : ZMod 2) (a : ExteriorAlgebra ℂ V)
      (ha : a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i) :
      Fm a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i := by
    have hrange : (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ V))).map
        Fm.toLinearMap ≤ LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ W)) := by
      rintro _ ⟨x, ⟨v, rfl⟩, rfl⟩
      exact ⟨e v, (ExteriorAlgebra.map_apply_ι e.toLinearMap v).symm⟩
    have hp : (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i).map
        Fm.toLinearMap ≤ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i := by
      simp only [CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
      exact iSup_mono (fun n ↦ pow_le_pow_left' hrange n.val)
    exact (Submodule.map_le_iff_le_comap.mp hp) ha
  have hparityG (i : ZMod 2) (b : ExteriorAlgebra ℂ W)
      (hb : b ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i) :
      Gm b ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i := by
    have hrange : (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ W))).map
        Gm.toLinearMap ≤ LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ V)) := by
      rintro _ ⟨x, ⟨w, rfl⟩, rfl⟩
      exact ⟨e.symm w, (ExteriorAlgebra.map_apply_ι e.symm.toLinearMap w).symm⟩
    have hp : (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i).map
        Gm.toLinearMap ≤ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i := by
      simp only [CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
      exact iSup_mono (fun n ↦ pow_le_pow_left' hrange n.val)
    exact (Submodule.map_le_iff_le_comap.mp hp) hb
  have hGF : Gm.comp Fm = AlgHom.id ℂ (ExteriorAlgebra ℂ V) := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [Fm, Gm]
  have hFG : Fm.comp Gm = AlgHom.id ℂ (ExteriorAlgebra ℂ W) := by
    apply ExteriorAlgebra.hom_ext
    ext w
    simp [Fm, Gm]
  let L (i : ZMod 2) : PV i ≃ₗ[ℂ] PW i :=
    { toFun := fun a ↦ ⟨Fm a.val, hparityF i a.val a.property⟩
      invFun := fun b ↦ ⟨Gm b.val, hparityG i b.val b.property⟩
      left_inv := fun a ↦ Subtype.ext (AlgHom.congr_fun hGF a.val)
      right_inv := fun b ↦ Subtype.ext (AlgHom.congr_fun hFG b.val)
      map_add' := fun a b ↦ Subtype.ext (map_add Fm a.val b.val)
      map_smul' := fun c a ↦ Subtype.ext (map_smul Fm c a.val) }
  -- Naturality of contraction retains the actual pulled covector.
  have hcontract (v : V) (a : ExteriorAlgebra ℂ V) :
      contraction (e v) (Fm a) =
        Fm (CliffordAlgebra.contractLeft ((innerₛₗ ℂ (e v)).comp e.toLinearMap) a) := by
    induction a using CliffordAlgebra.left_induction with
    | algebraMap r => simp [contraction, CliffordAlgebra.contractLeft_algebraMap]
    | add a b ha hb => simp only [map_add, ha, hb]
    | ι_mul a w ha =>
      change CliffordAlgebra.contractLeft (innerₛₗ ℂ (e v))
        (Fm (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w * a)) = _
      rw [map_mul, ExteriorAlgebra.map_apply_ι,
        CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul,
        map_sub, map_smul, map_mul, ExteriorAlgebra.map_apply_ι]
      change inner ℂ (e v) (e w) • Fm a -
        ExteriorAlgebra.ι ℂ (e w) * contraction (e v) (Fm a) =
          inner ℂ (e v) (e w) • Fm a - ExteriorAlgebra.ι ℂ (e w) *
            Fm (CliffordAlgebra.contractLeft ((innerₛₗ ℂ (e v)).comp e.toLinearMap) a)
      rw [ha]
  let B (v : V) (i : ZMod 2) : PV i →ₗ[ℂ] PV (i + 1) :=
    ((L (i + 1)).symm.toLinearMap.comp (cliffordSymbolParity (e v) i)).comp
      (L i).toLinearMap
  let C (t : unitInterval) (v : V) (i : ZMod 2) : PV i →ₗ[ℂ] PV (i + 1) :=
    (1 - (t : ℂ)) • cliffordSymbolParity v i + (t : ℂ) • B v i
  let d (t : unitInterval) (v : V) : Module.Dual ℂ V :=
    (1 - (t : ℂ)) • innerₛₗ ℂ v +
      (t : ℂ) • ((innerₛₗ ℂ (e v)).comp e.toLinearMap)
  let c (t : unitInterval) (v : V) : Module.End ℂ (ExteriorAlgebra ℂ V) :=
    exteriorMultiplication v - CliffordAlgebra.contractLeft (d t v)
  have hB (v : V) (i : ZMod 2) (a : PV i) :
      (B v i a : ExteriorAlgebra ℂ V) =
        exteriorMultiplication v a.val -
          CliffordAlgebra.contractLeft ((innerₛₗ ℂ (e v)).comp e.toLinearMap) a.val := by
    change Gm (cliffordSymbol (e v) (Fm a.val)) = _
    change Gm (ExteriorAlgebra.ι ℂ (e v) * Fm a.val - contraction (e v) (Fm a.val)) = _
    have hw : ExteriorAlgebra.ι ℂ (e v) = Fm (ExteriorAlgebra.ι ℂ v) :=
      (ExteriorAlgebra.map_apply_ι e.toLinearMap v).symm
    rw [hcontract, hw, ← map_mul Fm, ← map_sub Fm]
    exact AlgHom.congr_fun hGF _
  have hC (t : unitInterval) (v : V) (i : ZMod 2) (a : PV i) :
      (C t v i a : ExteriorAlgebra ℂ V) = c t v a.val := by
    change (1 - (t : ℂ)) • cliffordSymbol v a.val + (t : ℂ) • (B v i a).val = _
    rw [hB]
    change _ = exteriorMultiplication v a.val -
      CliffordAlgebra.contractLeft
        ((1 - (t : ℂ)) • innerₛₗ ℂ v +
          (t : ℂ) • ((innerₛₗ ℂ (e v)).comp e.toLinearMap)) a.val
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      cliffordSymbol, LinearMap.sub_apply, contraction, smul_sub]
    simp only [sub_smul, one_smul]
    abel
  have hcsquare (t : unitInterval) (v : V) (a : ExteriorAlgebra ℂ V) :
      c t v (c t v a) = -(d t v v) • a := by
    change ExteriorAlgebra.ι ℂ v *
        (ExteriorAlgebra.ι ℂ v * a - CliffordAlgebra.contractLeft (d t v) a) -
      CliffordAlgebra.contractLeft (d t v)
        (ExteriorAlgebra.ι ℂ v * a - CliffordAlgebra.contractLeft (d t v) a) = _
    rw [mul_sub, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, map_sub,
      CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_contractLeft]
    simp only [zero_sub, sub_zero, neg_smul]
    abel
  have hdpos (t : unitInterval) (v : V) (hv : v ≠ 0) :
      0 < (1 - (t : ℝ)) * ‖v‖ ^ 2 + (t : ℝ) * ‖e v‖ ^ 2 := by
    have hx : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hy : 0 < ‖e v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (e.map_ne_zero_iff.mpr hv))
    by_cases ht : (t : ℝ) = 0
    · simp only [ht, sub_zero, one_mul, zero_mul, add_zero]
      exact hx
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr t.property.2) hx.le)
        (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) hy)
  have hdne (t : unitInterval) (v : V) (hv : v ≠ 0) : d t v v ≠ 0 := by
    change (1 - (t : ℂ)) * inner ℂ v v + (t : ℂ) * inner ℂ (e v) (e v) ≠ 0
    intro h
    have hreal := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.zero_re, zero_mul, sub_zero] at hreal
    have h₁ : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    have h₂ : (inner ℂ (e v) (e v)).re = ‖e v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [h₁, h₂] at hreal
    have hpositive := hdpos t v hv
    linarith
  have hCb (t : unitInterval) (v : V) (hv : v ≠ 0) (i : ZMod 2) :
      Function.Bijective (C t v i) := by
    have hinv (a : ExteriorAlgebra ℂ V) :
        -(d t v v)⁻¹ • c t v (c t v a) = a := by
      rw [hcsquare, smul_smul, neg_mul_neg, inv_mul_cancel₀ (hdne t v hv), one_smul]
    constructor
    · intro a b hab
      apply Subtype.ext
      have h := congrArg (fun z : PV (i + 1) ↦ -(d t v v)⁻¹ • c t v z.val) hab
      simpa only [hC, hinv] using h
    · intro b
      have hi : (i + 1) + 1 = i := by
        rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
      let a : PV i := ⟨-(d t v v)⁻¹ • (C t v (i + 1) b).val, by
        have hm := (C t v (i + 1) b).property
        have hm' : (C t v (i + 1) b).val ∈ PV i := by
          simpa only [hi] using hm
        exact (CliffordAlgebra.evenOdd _ _).smul_mem _ hm'⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      rw [hC]
      change c t v (-(d t v v)⁻¹ • (C t v (i + 1) b).val) = b.val
      rw [hC, map_smul, hinv]
  -- The two endpoint actions, hence their convex interpolation, are equivariant.
  have hL (g : G) (i : ZMod 2) (a : PV i) :
      L i (exteriorParityAction g i a) = exteriorParityAction g i (L i a) := by
    have hh : Fm.comp (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g)) =
        (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ W g)).comp Fm := by
      apply ExteriorAlgebra.hom_ext
      ext v
      simp only [Fm, AlgHom.comp_toLinearMap, LinearMap.coe_comp, AlgHom.coe_toLinearMap,
        Function.comp_apply, ExteriorAlgebra.map_apply_ι, DistribSMul.toLinearMap_apply]
      exact congrArg (ExteriorAlgebra.ι ℂ) (he g v)
    exact Subtype.ext (AlgHom.congr_fun hh a.val)
  have hBaction (g : G) (v : V) (i : ZMod 2) (a : PV i) :
      B (g • v) i (exteriorParityAction g i a) =
        exteriorParityAction g (i + 1) (B v i a) := by
    apply (L (i + 1)).injective
    change L (i + 1) ((L (i + 1)).symm
      (cliffordSymbolParity (e (g • v)) i (L i (exteriorParityAction g i a)))) = _
    rw [(L (i + 1)).apply_symm_apply, hL, he, hL]
    change cliffordSymbolParity (g • e v) i (exteriorParityAction g i (L i a)) =
      exteriorParityAction g (i + 1)
        (L (i + 1) ((L (i + 1)).symm (cliffordSymbolParity (e v) i (L i a))))
    rw [(L (i + 1)).apply_symm_apply]
    exact LinearMap.congr_fun (cliffordSymbolParity_equivariant hW g (e v) i) (L i a)
  have hCaction (t : unitInterval) (g : G) (v : V) (i : ZMod 2) (a : PV i) :
      C t (g • v) i (exteriorParityAction g i a) =
        exteriorParityAction g (i + 1) (C t v i a) := by
    dsimp only [C, LinearMap.add_apply, LinearMap.smul_apply]
    have hvv := LinearMap.congr_fun (cliffordSymbolParity_equivariant hV g v i) a
    change cliffordSymbolParity (g • v) i (exteriorParityAction g i a) =
      exteriorParityAction g (i + 1) (cliffordSymbolParity v i a) at hvv
    rw [hBaction, hvv, map_add, map_smul, map_smul]
  have hCcontinuous (i : ZMod 2) :
      Continuous (fun p : (unitInterval × V) × PV i ↦ C p.1.1 p.1.2 i p.2) := by
    have hLcont : Continuous (L i) := (L i).toLinearMap.continuous_of_finiteDimensional
    have hLi : Continuous (L (i + 1)).symm :=
      (L (i + 1)).symm.toLinearMap.continuous_of_finiteDimensional
    have hinput : Continuous (fun p : V × PV i ↦ (e p.1, L i p.2)) :=
      (e.continuous.comp continuous_fst).prodMk (hLcont.comp continuous_snd)
    have hcliff := (continuous_cliffordSymbolParity (V := W) i).comp hinput
    have hBcont : Continuous (fun p : V × PV i ↦ B p.1 i p.2) := by
      have hh := hLi.comp hcliff
      apply hh.congr
      intro p
      rfl
    have ht : Continuous (fun p : (unitInterval × V) × PV i ↦ (p.1.1 : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst.fst)
    have hinputV : Continuous (fun p : (unitInterval × V) × PV i ↦ (p.1.2, p.2)) :=
      continuous_fst.snd.prodMk continuous_snd
    have hcv := (continuous_cliffordSymbolParity (V := V) i).comp hinputV
    have hh := (((continuous_const (y := (1 : ℂ))).sub ht).smul hcv).add
      (ht.smul (hBcont.comp hinputV))
    apply hh.congr
    intro p
    rfl
  have hCzero (v : V) (i : ZMod 2) : C 0 v i = cliffordSymbolParity v i := by
    simp [C]
  have hCone (v : V) (i : ZMod 2) : C 1 v i = B v i := by
    simp [C]
  have hnorm (g : G) (v : V) : ‖g • v‖ = ‖v‖ := by
    have h := congrArg Complex.re (hV g v v)
    have h₁ : (inner ℂ (g • v) (g • v)).re = ‖g • v‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    have h₂ : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [h₁, h₂] at h
    nlinarith [norm_nonneg (g • v), norm_nonneg v]
  -- Radial time is zero near the origin and one outside one compact invariant ball.
  let ρ : C(V, unitInterval) :=
    ⟨fun v ↦ Set.projIcc 0 1 zero_le_one (‖v‖ - 1),
      continuous_projIcc.comp (continuous_norm.sub continuous_const)⟩
  have hρzero (v : V) (hv : ‖v‖ < 1) : ρ v = 0 := by
    apply projIcc_eq_zero.mpr
    linarith
  have hρone (v : V) (hv : 2 < ‖v‖) : ρ v = 1 := by
    apply projIcc_eq_one.mpr
    linarith
  have hρaction (g : G) (v : V) : ρ (g • v) = ρ v := by
    change Set.projIcc 0 1 zero_le_one (‖g • v‖ - 1) = _
    rw [hnorm]
    rfl
  let T (v : V) : PV 1 ≃ₗ[ℂ] PV 1 :=
    if hv : v = 0 then LinearEquiv.refl ℂ (PV 1) else
      (cliffordSymbolParityEquiv v hv 0).symm.trans
        (LinearEquiv.ofBijective (C (ρ v) v 0) (hCb (ρ v) v hv 0))
  have hTzero (v : V) (hv : ‖v‖ < 1) (a : PV 1) : T v a = a := by
    dsimp only [T]
    split_ifs with h
    · rfl
    · change C (ρ v) v 0 ((cliffordSymbolParityEquiv v h 0).symm a) = a
      rw [hρzero v hv, hCzero]
      exact (cliffordSymbolParityEquiv v h 0).apply_symm_apply a
  have hTcont : Continuous (fun p : V × PV 1 ↦ T p.1 p.2) := by
    have hout : ContinuousOn (fun p : V × PV 1 ↦ T p.1 p.2)
        {p | p.1 ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      let v : {p : V × PV 1 // p.1 ≠ 0} → {x : V // x ≠ 0} :=
        fun p ↦ ⟨p.val.1, p.property⟩
      have hv : Continuous v := (continuous_fst.comp continuous_subtype_val).subtype_mk _
      have hinv := (continuous_cliffordSymbolParityEquiv_symm 0).comp
        (hv.prodMk (continuous_snd.comp continuous_subtype_val))
      exact (hCcontinuous 0).comp
        (((ρ.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
          (continuous_fst.comp continuous_subtype_val)).prodMk hinv) |>.congr
          (fun p ↦ by
            change C (ρ p.val.1) p.val.1 0
              ((cliffordSymbolParityEquiv p.val.1 p.property 0).symm p.val.2) = T p.val.1 p.val.2
            dsimp only [T]
            rw [dite_eq_right p.property]
            rfl)
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hp : ‖p.1‖ < 1
    · apply continuous_snd.continuousAt.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_fst.norm continuous_const).mem_nhds hp] with q hq
      exact hTzero q.1 hq q.2
    · have hn : p.1 ≠ 0 := by
        intro hz
        apply hp
        simp [hz]
      exact hout.continuousAt ((isOpen_ne.preimage continuous_fst).mem_nhds hn)
  have hTaction (g : G) (v : V) (a : PV 1) :
      T (g • v) (exteriorParityAction g 1 a) = exteriorParityAction g 1 (T v a) := by
    by_cases hv : v = 0
    · subst v
      simp only [smul_zero, T, dite_eq_left rfl, LinearEquiv.refl_apply]
    · have hgv : g • v ≠ 0 := (DistribMulAction.toLinearEquiv ℂ V g).map_ne_zero_iff.mpr hv
      have hi : (cliffordSymbolParityEquiv (g • v) hgv 0).symm
          (exteriorParityAction g 1 a) =
            exteriorParityAction g 0 ((cliffordSymbolParityEquiv v hv 0).symm a) := by
        apply (cliffordSymbolParityEquiv (g • v) hgv 0).injective
        rw [LinearEquiv.apply_symm_apply]
        have hh := LinearMap.congr_fun (cliffordSymbolParity_equivariant hV g v 0)
          ((cliffordSymbolParityEquiv v hv 0).symm a)
        change cliffordSymbolParity (g • v) 0
          (exteriorParityAction g 0 ((cliffordSymbolParityEquiv v hv 0).symm a)) =
            exteriorParityAction g 1
              (cliffordSymbolParityEquiv v hv 0 ((cliffordSymbolParityEquiv v hv 0).symm a))
          at hh
        rw [LinearEquiv.apply_symm_apply] at hh
        exact hh.symm
      dsimp only [T]
      rw [dite_eq_right hv, dite_eq_right hgv]
      change C (ρ (g • v)) (g • v) 0
        ((cliffordSymbolParityEquiv (g • v) hgv 0).symm (exteriorParityAction g 1 a)) =
          exteriorParityAction g 1 (C (ρ v) v 0 ((cliffordSymbolParityEquiv v hv 0).symm a))
      rw [hρaction, hi, hCaction]
      rfl
  let f : C(V, W) := ⟨e, e.continuous⟩
  let hf : IsProperMap f := e.toHomeomorph.isProperMap
  -- Package the original linear equivalences as actual maps of the pulled trivial bundles.
  let mkIso (i : ZMod 2) (q : V → PV i ≃ₗ[ℂ] PW i)
      (hq : Continuous (fun p : V × PV i ↦ q p.1 p.2)) :
      letI := modelTopology (PV i) (Bundle.Trivial V (PV i))
      letI := modelTopology (PW i) (Bundle.Trivial W (PW i))
      Iso (Bundle.Trivial V (PV i)) ((f : V → W) *ᵖ (Bundle.Trivial W (PW i))) := by
    let := modelTopology (PV i) (Bundle.Trivial V (PV i))
    let := modelTopology (PW i) (Bundle.Trivial W (PW i))
    let := isFiniteRank_model (PV i) (Bundle.Trivial V (PV i))
    let := isFiniteRank_model (PW i) (Bundle.Trivial W (PW i))
    let := isFiniteRank_pullback (E := Bundle.Trivial W (PW i)) f
    let rV : TotalSpace Unit (Bundle.Trivial V (PV i)) ≃ₜ V × PV i :=
      (unitTotalHomeomorph (PV i) (Bundle.Trivial V (PV i))).trans
        (Bundle.Trivial.homeomorphProd V (PV i))
    let rW : TotalSpace Unit (Bundle.Trivial W (PW i)) ≃ₜ W × PW i :=
      (unitTotalHomeomorph (PW i) (Bundle.Trivial W (PW i))).trans
        (Bundle.Trivial.homeomorphProd W (PW i))
    let qHom : Hom (Bundle.Trivial V (PV i))
        ((f : V → W) *ᵖ (Bundle.Trivial W (PW i))) :=
      { linearMap := fun x ↦ (q x).toLinearMap
        continuous_total := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial W (PW i))
            f).continuous_iff]
          exact rV.continuous.fst.prodMk (rW.symm.continuous.comp
            ((f.continuous.comp rV.continuous.fst).prodMk (hq.comp rV.continuous))) }
    exact qHom.toIso (fun x ↦ (q x).bijective)
  let := modelTopology (PV 0) (Bundle.Trivial V (PV 0))
  let := modelTopology (PV 1) (Bundle.Trivial V (PV 1))
  let := modelTopology (PW 0) (Bundle.Trivial W (PW 0))
  let := modelTopology (PW 1) (Bundle.Trivial W (PW 1))
  let j₀ := mkIso 0 (fun _ ↦ L 0)
    ((L 0).toContinuousLinearEquiv.continuous.comp continuous_snd)
  let j₁ := mkIso 1 (fun v ↦ (T v).trans (L 1))
    ((L 1).toContinuousLinearEquiv.continuous.comp hTcont)
  let a := equivariantExteriorBottTriple hV
  let b := (equivariantExteriorBottTriple hW).pullback f he hf
  have hj₀ : j₀.IsEquivariant a.2.sourceAction b.2.sourceAction := by
    intro g v w
    change L 0 (exteriorParityAction g 0 w) = _
    have htransport {x y : W} (hxy : x = y) (w : PW 0) :
        Eq.mpr (congrArg (fun z ↦ Bundle.Trivial W (PW 0) (f v) →ₗ[ℂ]
          Bundle.Trivial W (PW 0) z) hxy) (exteriorParityAction g 0) w =
          exteriorParityAction g 0 w := by
      subst y
      rfl
    exact (hL g 0 w).trans (htransport (he g v) (L 0 w)).symm
  have hj₁ : j₁.IsEquivariant a.2.targetAction b.2.targetAction := by
    intro g v w
    change L 1 (T (g • v) (exteriorParityAction g 1 w)) = _
    have htransport {x y : W} (hxy : x = y) (w : PW 1) :
        Eq.mpr (congrArg (fun z ↦ Bundle.Trivial W (PW 1) (f v) →ₗ[ℂ]
          Bundle.Trivial W (PW 1) z) hxy) (exteriorParityAction g 1) w =
          exteriorParityAction g 1 w := by
      subst y
      rfl
    exact (congrArg (L 1) (hTaction g v w)).trans
      ((hL g 1 (T v w)).trans (htransport (he g v) (L 1 (T v w))).symm)
  let := FiniteDimensional.proper ℂ V
  let K : Set V := Metric.closedBall 0 2
  have hK : IsCompact K := isCompact_closedBall 0 2
  have hKinv (g : G) (v : V) : g • v ∈ K ↔ v ∈ K := by
    change dist (g • v) 0 ≤ 2 ↔ dist v 0 ≤ 2
    rw [dist_zero_right, dist_zero_right, hnorm]
  have ha : a.1.datum.control ⊆ K := by
    intro v hv
    change v ∈ ({0} : Set V) at hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact Metric.mem_closedBall_self (by norm_num)
  have hb : b.1.datum.control ⊆ K := by
    intro v hv
    change e v ∈ ({0} : Set W) at hv
    have hv₀ : v = 0 := e.map_eq_zero_iff.mp hv
    subst v
    exact Metric.mem_closedBall_self (by norm_num)
  have hab : a.IsIsomorphic b := by
    refine ⟨K, hK, hKinv, ha, hb, j₀, j₁, hj₀, hj₁, ?_⟩
    intro x w
    change PV 0 at w
    have hx : 2 < ‖x.val‖ := by
      have hh := x.property
      change ¬dist x.val 0 ≤ 2 at hh
      simpa only [dist_zero_right, not_le] using hh
    have hx₀ : x.val ≠ 0 := by
      intro hz
      norm_num [hz] at hx
    change L 1 (T x.val
      (((exteriorBottTriple V).enlarge K hK ha).boundary.linearEquiv x w)) =
        (((exteriorBottTriple W).pullback f hf).enlarge K hK hb).boundary.linearEquiv x
          (L 0 w)
    have hl := (exteriorBottTriple V).enlarge_apply K hK ha x w
    have hr := ((exteriorBottTriple W).pullback f hf).enlarge_apply K hK hb x (L 0 w)
    refine (congrArg (fun z : PV 1 ↦ L 1 (T x.val z)) hl).trans (Eq.trans ?_ hr.symm)
    change L 1 (T x.val (cliffordSymbolParityEquiv x.val hx₀ 0 w)) =
      ((exteriorBottTriple W).boundary.pullback f).linearEquiv _ (L 0 w)
    have hp := RelativeTriple.pullback_apply (exteriorBottTriple W).boundary f
      ⟨x.val, fun h ↦ x.property (hb h)⟩ (L 0 w)
    refine Eq.trans ?_ hp.symm
    dsimp only [T]
    rw [dite_eq_right hx₀]
    change L 1 (C (ρ x.val) x.val 0
      ((cliffordSymbolParityEquiv x.val hx₀ 0).symm
        (cliffordSymbolParityEquiv x.val hx₀ 0 w))) =
          cliffordSymbolParity (e x.val) 0 (L 0 w)
    rw [LinearEquiv.symm_apply_apply, hρone x.val hx, hCone]
    exact (L 1).apply_symm_apply _
  -- Descend the same equivariant global square through the original presentation relation.
  change equivariantSupportTripleKZeroPullback f he hf
    (equivariantExteriorBottTriple hW).kZeroClass = a.kZeroClass
  rw [equivariantSupportTripleKZeroPullback_apply]
  exact (equivariantSupportTripleKZero_generator_relations.1 a b hab).symm

end Hermitian

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V]
  [ContinuousSMul G V]

section CoordinateAction

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Transport the original linear action by this specified continuous linear equivalence. -/
@[reducible]
def bottCoordinateAction (e : V ≃L[ℂ] W) : DistribMulAction G W where
  smul g w := e (g • e.symm w)
  one_smul w := by
    change e ((1 : G) • e.symm w) = w
    rw [one_smul, e.apply_symm_apply]
  mul_smul g h w := by
    change e ((g * h) • e.symm w) = e (g • e.symm (e (h • e.symm w)))
    rw [e.symm_apply_apply, mul_smul]
  smul_zero g := by
    change e (g • e.symm 0) = 0
    rw [map_zero, smul_zero, map_zero]
  smul_add g w z := by
    change e (g • e.symm (w + z)) = e (g • e.symm w) + e (g • e.symm z)
    rw [map_add, smul_add, map_add]

set_option linter.defProp false in
-- An explicit local instance value keeps the chosen coordinate map out of global instance search.
/-- The transported action commutes with the unchanged complex scalar multiplication. -/
@[reducible]
def bottCoordinate_smulCommClass (e : V ≃L[ℂ] W) :
    letI := bottCoordinateAction (G := G) e
    SMulCommClass G ℂ W := by
  let := bottCoordinateAction (G := G) e
  refine ⟨fun g c w ↦ ?_⟩
  change e (g • e.symm (c • w)) = c • e (g • e.symm w)
  simp only [map_smul, smul_comm g c]

set_option linter.defProp false in
-- This certificate is installed only for the particular coordinate map used in the construction.
/-- Joint continuity of the same conjugated action in the original norm topologies. -/
@[reducible]
def bottCoordinate_continuousSMul (e : V ≃L[ℂ] W) :
    letI := bottCoordinateAction (G := G) e
    ContinuousSMul G W := by
  let := bottCoordinateAction (G := G) e
  refine ⟨?_⟩
  change Continuous (fun p : G × W ↦ e (p.1 • e.symm p.2))
  exact e.continuous.comp (continuous_fst.smul (e.symm.continuous.comp continuous_snd))

end CoordinateAction

variable [hCompact : CompactSpace G] [hHausdorff : T2Space G]

include hCompact hHausdorff in
/-- Every finite continuous complex action has invariant coordinates on a genuine
Euclidean space, without changing the original norm on its source. -/
theorem exists_unitaryBottCoordinates :
    ∃ e : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)),
      ∀ (g : G) (x y : V), inner ℂ (e (g • x)) (e (g • y)) = inner ℂ (e x) (e y) := by
  /- Stage 1: a finite basis gives a continuous linear equivalence from V to
  the stated Euclidean space. Conjugate the original action by this actual map;
  its continuous linear operators form a ContRepresentation, and joint continuity
  follows from the original action and the two continuous coordinate maps.
  Stage 2: equip G locally with its Borel measurable structure and apply
  exists_unitary_coordinates to this Euclidean representation. Its pairing
  formula and averagedHermitianPairing_invariant give exactly the displayed
  invariance. Compose the two continuous linear equivalences. No compatibility
  between an inner product and the original norm of V was required. The empty
  basis and the original rank-zero action are included. -/
  classical
  let W := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  -- First use ordinary finite-dimensional coordinates without changing the norm on V.
  let e₀ : V ≃L[ℂ] W := ContinuousLinearEquiv.ofFinrankEq (by simp [W])
  let := bottCoordinateAction (G := G) e₀
  let := bottCoordinate_smulCommClass (G := G) e₀
  let := bottCoordinate_continuousSMul (G := G) e₀
  let ρ : ContRepresentation ℂ G W := .ofMonoidHom
    { toFun := fun g ↦ (DistribSMul.toLinearMap ℂ W g).toContinuousLinearMap
      map_one' := by
        apply ContinuousLinearMap.ext
        intro w
        exact one_smul G w
      map_mul' := by
        intro g h
        apply ContinuousLinearMap.ext
        intro w
        exact mul_smul g h w }
  have hρ : Continuous (fun p : G × W ↦ ρ p.1 p.2) := continuous_smul
  -- Average the original conjugated action in its Euclidean model, using Borel Haar measure.
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  have hdim : Module.finrank ℂ W = Module.finrank ℂ V := by simp [W]
  obtain ⟨u, hpair, _⟩ := exists_unitary_coordinates ρ hρ
  let q : EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) ≃ₗᵢ[ℂ] W :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr hdim)
  refine ⟨(e₀.trans u).trans q.toContinuousLinearEquiv, ?_⟩
  intro g x y
  -- The returned map retains V's original topology and intertwines this same actual action.
  have hx : e₀ (g • x) = ρ g (e₀ x) := by
    change e₀ (g • x) = e₀ (g • e₀.symm (e₀ x))
    rw [e₀.symm_apply_apply]
  have hy : e₀ (g • y) = ρ g (e₀ y) := by
    change e₀ (g • y) = e₀ (g • e₀.symm (e₀ y))
    rw [e₀.symm_apply_apply]
  change inner ℂ (q (u (e₀ (g • x)))) (q (u (e₀ (g • y)))) =
    inner ℂ (q (u (e₀ x))) (q (u (e₀ y)))
  rw [q.inner_map_map, q.inner_map_map, hx, hy, hpair,
    averagedHermitianPairing_invariant ρ hρ, hpair]

/-- One invariant coordinate map supplied by the same existence theorem. -/
def unitaryBottCoordinates : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  Classical.choose (exists_unitaryBottCoordinates (G := G) (V := V))

/-- The Bott class of the original representation, obtained by actual proper coordinate
pullback of the existing exterior Bott class. -/
def equivariantRepresentationBottClass : EquivariantSupportTripleKZero G V := by
  let e := unitaryBottCoordinates (G := G) (V := V)
  letI := bottCoordinateAction (G := G) e
  letI := bottCoordinate_smulCommClass (G := G) e
  letI := bottCoordinate_continuousSMul (G := G) e
  have hU : ∀ (g : G) (x y : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))),
      inner ℂ (g • x) (g • y) = inner ℂ x y := by
    intro g x y
    change inner ℂ (e (g • e.symm x)) (e (g • e.symm y)) = inner ℂ x y
    have h := Classical.choose_spec (exists_unitaryBottCoordinates (G := G) (V := V))
      g (e.symm x) (e.symm y)
    change inner ℂ (e (g • e.symm x)) (e (g • e.symm y)) =
      inner ℂ (e (e.symm x)) (e (e.symm y)) at h
    simpa only [e.apply_symm_apply] using h
  have he : ∀ (g : G) (x : V), e (g • x) = g • e x := by
    intro g x
    change e (g • x) = e (g • e.symm (e x))
    rw [e.symm_apply_apply]
  exact equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ he
    e.toHomeomorph.isProperMap (equivariantExteriorBottClass hU)

/-- Every invariant Hermitian model gives the same class on the original representation. -/
theorem equivariantRepresentationBottClass_eq_pullback
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [DistribMulAction G W] [SMulCommClass G ℂ W] [ContinuousSMul G W]
    (hW : ∀ (g : G) (x y : W), inner ℂ (g • x) (g • y) = inner ℂ x y)
    (e : V ≃L[ℂ] W) (he : ∀ (g : G) (x : V), e (g • x) = g • e x) :
    equivariantRepresentationBottClass (G := G) (V := V) =
      equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ he e.toHomeomorph.isProperMap
        (equivariantExteriorBottClass hW) := by
  /- Stage 1: compare e with the exact unitaryBottCoordinates selected in the
  definition. Their composite is a complex continuous linear equivariant
  equivalence between the two actual unitary models. It need not be an isometry.
  Stage 2: equivariantExteriorBottClass_natural identifies the two generators
  for their supplied metrics. Apply proper-pullback composition with the
  original coordinate map; both routes preserve the original base action and
  singleton-zero control. This proves independence of all coordinate and metric
  choices, not merely equality after forgetting the G action. -/
  classical
  -- Keep exactly the invariant coordinates selected by the original definition.
  let U := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let u : V ≃L[ℂ] U := unitaryBottCoordinates (G := G) (V := V)
  let := bottCoordinateAction (G := G) u
  let := bottCoordinate_smulCommClass (G := G) u
  let := bottCoordinate_continuousSMul (G := G) u
  have hU (g : G) (x y : U) : inner ℂ (g • x) (g • y) = inner ℂ x y := by
    change inner ℂ (u (g • u.symm x)) (u (g • u.symm y)) = inner ℂ x y
    have h := Classical.choose_spec (exists_unitaryBottCoordinates (G := G) (V := V))
      g (u.symm x) (u.symm y)
    change inner ℂ (u (g • u.symm x)) (u (g • u.symm y)) =
      inner ℂ (u (u.symm x)) (u (u.symm y)) at h
    simpa only [u.apply_symm_apply] using h
  have hu (g : G) (x : V) : u (g • x) = g • u x := by
    change u (g • x) = u (g • u.symm (u x))
    rw [u.symm_apply_apply]
  let q : U ≃L[ℂ] W := u.symm.trans e
  have hq (g : G) (x : U) : q (g • x) = g • q x := by
    change e (u.symm (u (g • u.symm x))) = g • e (u.symm x)
    rw [u.symm_apply_apply, he]
  have hnatural := equivariantExteriorBottClass_natural hU hW q hq
  -- Compose the same proper pullbacks; their composite is the supplied map e.
  let f : C(V, U) := ⟨u, u.continuous⟩
  let k : C(U, W) := ⟨q, q.continuous⟩
  have hkf : k.comp f = (⟨e, e.continuous⟩ : C(V, W)) := by
    ext x
    exact congrArg e (u.symm_apply_apply x)
  change equivariantSupportTripleKZeroPullback f hu u.toHomeomorph.isProperMap
    (equivariantExteriorBottClass hU) = _
  rw [← hnatural]
  have hcomp := equivariantSupportTripleKZeroPullback_comp k f hq hu
    q.toHomeomorph.isProperMap u.toHomeomorph.isProperMap
  have hvalue := congrArg (fun F ↦ F (equivariantExteriorBottClass hW)) hcomp.symm
  change equivariantSupportTripleKZeroPullback f hu u.toHomeomorph.isProperMap
    (equivariantSupportTripleKZeroPullback k hq q.toHomeomorph.isProperMap
      (equivariantExteriorBottClass hW)) = _ at hvalue
  simpa only [hkf] using hvalue

section UnitaryRecovery

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] [DistribMulAction G W] [SMulCommClass G ℂ W]
  [ContinuousSMul G W]

/-- On a unitary representation the general construction recovers the same original class. -/
theorem equivariantRepresentationBottClass_eq_exterior
    (hW : ∀ (g : G) (x y : W), inner ℂ (g • x) (g • y) = inner ℂ x y) :
    equivariantRepresentationBottClass (G := G) (V := W) =
      equivariantExteriorBottClass hW := by
  /- Apply the arbitrary-model comparison with the identity continuous linear
  equivalence of W and its actual action. Proper pullback by the identity is
  the original identity homomorphism. No new generator or metric is selected. -/
  -- Use the supplied metric itself as the comparison model and simplify identity pullback.
  have h := equivariantRepresentationBottClass_eq_pullback hW
    (ContinuousLinearEquiv.refl ℂ W) (fun _ _ ↦ rfl)
  change equivariantRepresentationBottClass (G := G) (V := W) =
    equivariantSupportTripleKZeroPullback (ContinuousMap.id W)
      (fun _ _ ↦ rfl) isProperMap_id (equivariantExteriorBottClass hW) at h
  rw [equivariantSupportTripleKZeroPullback_id] at h
  exact h

end UnitaryRecovery

/-- Multiplication by the coordinate-independent class in the original support group. -/
def equivariantRepresentationBottLinearMap :
    RepresentationGrothendieckGroup G →ₗ[RepresentationGrothendieckGroup G]
      EquivariantSupportTripleKZero G V where
  toFun r := r • equivariantRepresentationBottClass (G := G) (V := V)
  map_add' r s := add_smul r s _
  map_smul' r s := mul_smul r s _

/-
This full Bott extension is retained as inactive source documentation. The current
AB01 scope requires the coordinate-independent class and its compatibility maps,
which are proved independently of this general bijectivity statement.

section BottTheorem

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [hFinite : FiniteDimensional ℝ EG] [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [hLie : LieGroup IG ∞ G]

include hFinite hLie in
/-- Independent equivariant Bott periodicity for the original arbitrary finite representation. -/
theorem equivariantRepresentationBottLinearMap_bijective :
    Function.Bijective (equivariantRepresentationBottLinearMap (G := G) (V := V))
  /- Stage 1: use the same invariant coordinates and conjugated unitary action
  as in the definition of the original-base class. The existing independent
  equivariantBottLinearMap_bijective applies to precisely that unitary model.
  Stage 2: proper pullback along this equivariant homeomorphism is invertible,
  with inverse the pullback along its actual inverse. Its R(G)-linearity is
  equivariantSupportTripleKZeroPullback_smul. The composite forward map is
  therefore exactly multiplication by the original-base class defined above.
  Transport the independent inverse identities; no analytic index or sphere
  normalization enters. The independent Bott proof itself remains omitted. -/

end BottTheorem
-/

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [hHCompact : CompactSpace H] [hHHausdorff : T2Space H]

include hHCompact hHHausdorff in
/-- Group restriction preserves the general class, independently of the two averaging choices. -/
theorem equivariantRepresentationBottClass_restrict (φ : H →ₜ* G) :
    letI : DistribMulAction H V := DistribMulAction.compHom V φ.toMonoidHom
    letI : SMulCommClass H ℂ V := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
    letI : ContinuousSMul H V := MulAction.continuousSMul_compHom φ.continuous
    equivariantSupportTripleKZeroRestrict φ
        (equivariantRepresentationBottClass (G := G) (V := V)) =
      equivariantRepresentationBottClass (G := H) (V := V) := by
  /- Stage 1: retain the coordinates chosen for G and restrict that actual
  unitary action through phi. The same map is an equivariant unitary model
  for the original H action, even though H's own averaging may choose another.
  Stage 2: apply the existing restriction/proper-pullback square and the
  same-triple equivariantExteriorBottClass_restrict equation. The general
  arbitrary-model comparison then identifies the result with H's class.
  No injectivity or surjectivity of phi, or Lie structure, is used. -/
  classical
  let : DistribMulAction H V := DistribMulAction.compHom V φ.toMonoidHom
  let : SMulCommClass H ℂ V := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
  let : ContinuousSMul H V := MulAction.continuousSMul_compHom φ.continuous
  -- Retain G's chosen coordinates and their actual conjugated action when restricting.
  let U := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let u : V ≃L[ℂ] U := unitaryBottCoordinates (G := G) (V := V)
  let := bottCoordinateAction (G := G) u
  let := bottCoordinate_smulCommClass (G := G) u
  let := bottCoordinate_continuousSMul (G := G) u
  have hU (g : G) (x y : U) : inner ℂ (g • x) (g • y) = inner ℂ x y := by
    change inner ℂ (u (g • u.symm x)) (u (g • u.symm y)) = inner ℂ x y
    have h := Classical.choose_spec (exists_unitaryBottCoordinates (G := G) (V := V))
      g (u.symm x) (u.symm y)
    change inner ℂ (u (g • u.symm x)) (u (g • u.symm y)) =
      inner ℂ (u (u.symm x)) (u (u.symm y)) at h
    simpa only [u.apply_symm_apply] using h
  have hu (g : G) (x : V) : u (g • x) = g • u x := by
    change u (g • x) = u (g • u.symm (u x))
    rw [u.symm_apply_apply]
  let : DistribMulAction H U := DistribMulAction.compHom U φ.toMonoidHom
  let : SMulCommClass H ℂ U := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
  let : ContinuousSMul H U := MulAction.continuousSMul_compHom φ.continuous
  have hG := equivariantRepresentationBottClass_eq_pullback (G := G) hU u hu
  have hH := equivariantRepresentationBottClass_eq_pullback (G := H)
    (fun h x y ↦ hU (φ h) x y) u (fun h x ↦ hu (φ h) x)
  let f : C(V, U) := ⟨u, u.continuous⟩
  -- The original restriction square keeps this map and this exterior class throughout.
  have hsquare := equivariantSupportTripleKZeroRestrict_pullback φ f hu
    u.toHomeomorph.isProperMap
  have hvalue := congrArg (fun F ↦ F (equivariantExteriorBottClass hU)) hsquare
  change equivariantSupportTripleKZeroRestrict φ
      (equivariantSupportTripleKZeroPullback f hu u.toHomeomorph.isProperMap
        (equivariantExteriorBottClass hU)) =
    equivariantSupportTripleKZeroPullback f (fun h x ↦ hu (φ h) x) u.toHomeomorph.isProperMap
      (equivariantSupportTripleKZeroRestrict φ (equivariantExteriorBottClass hU)) at hvalue
  rw [equivariantExteriorBottClass_restrict hU φ] at hvalue
  rw [hG]
  exact hvalue.trans hH.symm

end AtiyahSinger
