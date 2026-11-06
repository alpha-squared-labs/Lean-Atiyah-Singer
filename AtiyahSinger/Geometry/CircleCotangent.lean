/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Geometry.Manifold.Instances.Sphere

import AtiyahSinger.Geometry.TangentMusical
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Oriented coordinates on the actual circle cotangent bundle

Public module ID: M1122.

AR02 uses the original `Circle` manifold and its angular vector field, obtained
by differentiating `t ↦ x * Circle.exp t`. Evaluating an original covector on
this vector gives its real coefficient. The resulting trivialization retains
the original cotangent topology; no product topology is imposed on the bundle.

The point tube is an explicit open embedding of the complex plane. Its real
coordinate is the angular base coordinate and its imaginary coordinate is the
cotangent coefficient. The angle `2 * arctan (u / 2)` has derivative one at zero,
so this tube uses the normal-then-vertical normalization of the existing tangent
pushforward. Multiplication by `I` acts on these coordinates as `(u,v) ↦ (-v,u)`.

Source: Atiyah--Singer I, section 8, pp.525--526 and Figure 3. The global angular
trivialization and this particular normalized tube are explicit project
constructions implementing the source's coordinates `x + iξ`. Their proofs use
the original angular derivative and bundle topology throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

/-- The positive angular tangent vector, using the derivative of the actual rotation curve. -/
def circleAngularTangent (x : Circle) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) x := by
  -- Use the canonical tangent vector 1 on ℝ and identify the curve's value at zero with x.
  simpa only [Circle.exp_zero, mul_one] using
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      (fun t : ℝ ↦ x * Circle.exp t) 0
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)

/-- The real coefficient of an original circle covector in the positive angular frame. -/
def circleCovectorCoordinate (x : Circle) (ξ : CotangentFiber (n := 1) x) : ℝ :=
  ξ (circleAngularTangent x)

/-- Angular evaluation gives a homeomorphism of the original cotangent bundle with a cylinder. -/
theorem exists_circleCotangentTrivialization :
    ∃ e : CotangentTotalSpace (n := 1) (M := Circle) ≃ₜ Circle × ℝ,
      ∀ z, e z = (z.proj, circleCovectorCoordinate z.proj z.snd) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
  -- Differentiate rotation jointly in the base point and the angular parameter.
  have hs : ContMDiff I I.tangent ∞
      (fun x : Circle ↦ (⟨x, circleAngularTangent x⟩ : TangentBundle I Circle)) := by
    let f (p : Circle × ℝ) := p.1 * Circle.exp p.2
    have hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ f :=
      contMDiff_fst.mul (contMDiff_circleExp.comp contMDiff_snd)
    have hv : ContMDiff I (I.prod 𝓘(ℝ, ℝ)).tangent ∞
        (fun x : Circle ↦ (⟨(x, 0), (0, 1)⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (Circle × ℝ))) := by
      exact contMDiff_equivTangentBundleProd_symm.comp
        ((contMDiff_zeroSection (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin 1))
          (E := TangentSpace I) (IB := I)).prodMk
          (contMDiff_const (c := (⟨0, (NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1⟩ :
            TangentBundle 𝓘(ℝ, ℝ) ℝ))))
    have hsm := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hv
    apply hsm.congr
    intro x
    apply Bundle.TotalSpace.ext (by simp [f])
    apply heq_of_eq
    change circleAngularTangent x = mfderiv (I.prod 𝓘(ℝ, ℝ)) I f (x, 0) (0, 1)
    have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
        (fun t : ℝ ↦ (x, t)) 0 := mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hder := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := I.prod 𝓘(ℝ, ℝ)) (I'' := I)
      0 (hf.mdifferentiableAt (by simp)) hcurve
    have hderv := congrArg (fun L ↦ L (1 : ℝ)) hder
    have hp := mfderiv_prodMk (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
      (f := fun _ : ℝ ↦ x) (g := fun t : ℝ ↦ t) (x := 0)
      mdifferentiableAt_const mdifferentiableAt_id
    rw [hp] at hderv
    change mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ ↦ x * Circle.exp t) 0 (1 : ℝ) =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) I f (x, 0)
        ((mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ ↦ x) 0 (1 : ℝ),
          mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ t) 0 (1 : ℝ))) at hderv
    have hid : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ t) 0 (1 : ℝ) = (1 : ℝ) := by
      erw [mfderiv_id]
      rfl
    have hc : mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ ↦ x) 0 (1 : ℝ) = 0 := by
      rw [mfderiv_const]
      rfl
    rw [hc, hid] at hderv
    have hcast : circleAngularTangent x =
        mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ ↦ x * Circle.exp t) 0 (1 : ℝ) := by
      simp only [circleAngularTangent]
      rfl
    exact hcast.trans hderv
  -- The ambient derivative is x * I, so the original angular tangent never vanishes.
  have hn (x : Circle) : circleAngularTangent x ≠ 0 := by
    let f (t : ℝ) := x * Circle.exp t
    have hfs : ContMDiff 𝓘(ℝ, ℝ) I ∞ f := contMDiff_const.mul contMDiff_circleExp
    have hf := hfs.mdifferentiableAt (x := 0) (by simp)
    let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
    have hcs : ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun z : Circle ↦ (z : ℂ)) :=
      contMDiff_coe_sphere
    have hc := hcs.mdifferentiableAt (x := x) (by simp)
    have hzero : f 0 = x := by simp [f]
    have hcomp := mfderiv_comp_of_eq (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℂ))
      (x := 0) hc hf hzero
    have hreal : HasDerivAt (fun t : ℝ ↦ (f t : ℂ)) ((x : ℂ) * Complex.I) 0 := by
      simpa [f, Circle.coe_exp] using
        (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const Complex.I).cexp.const_mul (x : ℂ))
    have hamb : mfderiv I 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) x
        (circleAngularTangent x) = (x : ℂ) * Complex.I := by
      have hv := congrArg (fun L ↦ L (1 : ℝ)) hcomp
      have hv' := hreal.hasFDerivAt.fderiv
      have hcast : circleAngularTangent x = mfderiv 𝓘(ℝ, ℝ) I f 0 (1 : ℝ) := by
        simp only [circleAngularTangent]
        rfl
      rw [hcast]
      have hvleft : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ((fun z : Circle ↦ (z : ℂ)) ∘ f) 0 (1 : ℝ) =
          (x : ℂ) * Complex.I := by
        rw [mfderiv_eq_fderiv]
        change fderiv ℝ (fun t : ℝ ↦ (f t : ℂ)) 0 (1 : ℝ) = _
        rw [hv']
        simp
      rw [hvleft] at hv
      change (x : ℂ) * Complex.I =
        mfderiv I 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) (f 0)
          (mfderiv 𝓘(ℝ, ℝ) I f 0 (1 : ℝ)) at hv
      rw [hzero] at hv
      exact hv.symm
    intro hz
    rw [hz, map_zero] at hamb
    exact mul_ne_zero x.coe_ne_zero Complex.I_ne_zero hamb.symm
  -- An auxiliary metric constructs the inverse; the forward map remains angular evaluation.
  obtain ⟨g⟩ := SmoothTangentMetric.nonempty (n := 1) (M := Circle)
  let q (x : Circle) : ℝ := g.inner x (circleAngularTangent x) (circleAngularTangent x)
  have hq (x : Circle) : q x ≠ 0 := ne_of_gt (g.pos x _ (hn x))
  have ha : Continuous (fun x : Circle ↦
      (⟨x, circleAngularTangent x⟩ : TangentBundle I Circle)) := hs.continuous
  have hb : Continuous (fun x : Circle ↦
      (⟨x, g.inner x (circleAngularTangent x)⟩ : CotangentTotalSpace (n := 1))) :=
    g.isHomeomorph_flatMap.continuous.comp ha
  have hqcont : Continuous q := by
    exact ((Bundle.Trivial.homeomorphProd Circle ℝ).continuous.snd).comp
      (hb.clm_bundle_apply ha)
  let inverseMap (p : Circle × ℝ) : CotangentTotalSpace (n := 1) (M := Circle) :=
    ⟨p.1, (p.2 / q p.1) • g.inner p.1 (circleAngularTangent p.1)⟩
  have hforward : Continuous (fun z : CotangentTotalSpace (n := 1) (M := Circle) ↦
      (z.proj, circleCovectorCoordinate z.proj z.snd)) := by
    have hproj := FiberBundle.continuous_proj (CotangentModel 1)
      (CotangentFiber (n := 1) (M := Circle))
    have heval : Continuous (fun z : CotangentTotalSpace (n := 1) (M := Circle) ↦
        (⟨z.proj, z.snd (circleAngularTangent z.proj)⟩ :
          Bundle.TotalSpace ℝ (Bundle.Trivial Circle ℝ))) :=
      continuous_id.clm_bundle_apply (ha.comp hproj)
    exact hproj.prodMk (((Bundle.Trivial.homeomorphProd Circle ℝ).continuous.snd).comp heval)
  -- Verify inverse continuity in the native cotangent charts, without changing their topology.
  have hinverse : Continuous inverseMap := by
    apply continuous_iff_continuousAt.mpr
    intro p
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuousAt_fst, ?_⟩
    let e := trivializationAt (CotangentModel 1) (CotangentFiber (n := 1) (M := Circle)) p.1
    have hc : ContinuousAt (fun y : Circle ↦
        (e ⟨y, g.inner y (circleAngularTangent y)⟩).2) p.1 :=
      (FiberBundle.continuousAt_totalSpace (CotangentModel 1) _).mp hb.continuousAt |>.2
    have hscaled := (continuousAt_snd.div (hqcont.continuousAt.comp continuousAt_fst)
      (hq p.1)).smul (hc.comp continuousAt_fst)
    apply hscaled.congr_of_eventuallyEq
    have he : ∀ᶠ y : Circle × ℝ in 𝓝 p, y.1 ∈ e.baseSet :=
      continuousAt_fst.preimage_mem_nhds
        (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ p.1))
    filter_upwards [he] with y hy
    exact ((e.linear ℝ hy).map_smul (y.2 / q y.1)
      (g.inner y.1 (circleAngularTangent y.1)))
  -- In one dimension the angular vector spans; the metric normalization cancels exactly.
  have hspan (x : Circle) (v : TangentSpace I x) :
      ∃ c : ℝ, c • circleAngularTangent x = v := by
    apply (finrank_eq_one_iff_of_nonzero' (circleAngularTangent x) (hn x)).mp ?_ v
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1
    simp
  refine ⟨{
    toFun := fun z ↦ (z.proj, circleCovectorCoordinate z.proj z.snd)
    invFun := inverseMap
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := hforward
    continuous_invFun := hinverse }, fun _ ↦ rfl⟩
  · rintro ⟨x, ξ⟩
    dsimp only [inverseMap]
    apply Bundle.TotalSpace.ext (by rfl)
    apply heq_of_eq
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨c, rfl⟩ := hspan x v
    change ((ξ (circleAngularTangent x) / q x) •
      g.inner x (circleAngularTangent x)) (c • circleAngularTangent x) =
        ξ (c • circleAngularTangent x)
    simp only [smul_apply, map_smul, smul_eq_mul]
    change c * ((ξ (circleAngularTangent x) / q x) * q x) =
      c * ξ (circleAngularTangent x)
    rw [div_mul_cancel₀ _ (hq x)]
  · rintro ⟨x, c⟩
    dsimp only [inverseMap]
    apply Prod.ext (by rfl)
    change ((c / q x) • g.inner x (circleAngularTangent x)) (circleAngularTangent x) = c
    change (c / q x) * q x = c
    exact div_mul_cancel₀ c (hq x)

/-- The specified angular trivialization, selected with its full evaluation formula. -/
def circleCotangentTrivialization :
    CotangentTotalSpace (n := 1) (M := Circle) ≃ₜ Circle × ℝ :=
  exists_circleCotangentTrivialization.choose

/-- The angular trivialization retains the base and evaluates the actual covector. -/
theorem circleCotangentTrivialization_apply
    (z : CotangentTotalSpace (n := 1) (M := Circle)) :
    circleCotangentTrivialization z = (z.proj, circleCovectorCoordinate z.proj z.snd) := by
  -- The chosen witness carries the same angular evaluation formula.
  exact exists_circleCotangentTrivialization.choose_spec z

/-- A circle covector vanishes exactly when its angular coefficient vanishes. -/
theorem circleCovectorCoordinate_eq_zero_iff (x : Circle)
    (ξ : CotangentFiber (n := 1) x) : circleCovectorCoordinate x ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro hξ
    -- Compare the original covector and zero under the same injective homeomorphism.
    have hpair : circleCotangentTrivialization (⟨x, ξ⟩ : CotangentTotalSpace (n := 1)) =
        circleCotangentTrivialization (⟨x, 0⟩ : CotangentTotalSpace (n := 1)) := by
      rw [circleCotangentTrivialization_apply, circleCotangentTrivialization_apply]
      change (x, circleCovectorCoordinate x ξ) = (x, 0)
      rw [hξ]
    have hz := circleCotangentTrivialization.injective hpair
    exact Bundle.TotalSpace.mk_injective x hz
  · rintro rfl
    rfl

/-- A normalized point tube, with real base displacement followed by imaginary covector. -/
def circlePointCotangentTube (a : Circle) (z : ℂ) :
    CotangentTotalSpace (n := 1) (M := Circle) :=
  circleCotangentTrivialization.symm
    (a * Circle.exp (2 * Real.arctan (z.re / 2)), z.im)

/-- The explicit point tube is open and injective in the original cotangent topology. -/
theorem isOpenEmbedding_circlePointCotangentTube (a : Circle) :
    IsOpenEmbedding (circlePointCotangentTube a) := by
  -- The normalized angle is an open embedding into the interval (-π, π).
  let θ : ℝ → ℝ := fun u ↦ 2 * Real.arctan (u / 2)
  have hdiv : IsOpenEmbedding (fun u : ℝ ↦ u / 2) := by
    convert (Homeomorph.mulLeft₀ (1 / 2 : ℝ) (by norm_num)).isOpenEmbedding using 1
    ext u
    change u / 2 = (1 / 2) * u
    ring
  have hatan : IsOpenEmbedding Real.arctan :=
    Real.tanPartialHomeomorph.symm.isOpenEmbedding rfl
  have hθ : IsOpenEmbedding θ :=
    (Homeomorph.mulLeft₀ (2 : ℝ) (by norm_num)).isOpenEmbedding.comp (hatan.comp hdiv)
  have hθrange (u : ℝ) : θ u ∈ Set.Ico (-Real.pi) Real.pi := by
    obtain ⟨hl, hu⟩ := Real.arctan_mem_Ioo (u / 2)
    constructor <;> dsimp [θ] <;> linarith
  -- Exponentiation is open, and its period cannot identify two angles in this range.
  have hexp : IsOpenEmbedding (fun u : ℝ ↦ Circle.exp (θ u)) := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact Circle.exp.continuous.comp hθ.continuous
    · intro u v huv
      apply hθ.injective
      exact Circle.exp_injOn_Ico (by linarith) (hθrange u) (hθrange v) huv
    · exact isLocalHomeomorph_circleExp.isOpenMap.comp hθ.isOpenMap
  have harc : IsOpenEmbedding (fun u : ℝ ↦ a * Circle.exp (θ u)) :=
    (Homeomorph.mulLeft a).isOpenEmbedding.comp hexp
  -- Use the original angular trivialization and real/imaginary coordinates in that order.
  have hcylinder : IsOpenEmbedding (fun z : ℂ ↦ (a * Circle.exp (θ z.re), z.im)) := by
    have hp := harc.prodMap (IsOpenEmbedding.id (X := ℝ))
    have hc := hp.comp Complex.equivRealProdCLM.toHomeomorph.isOpenEmbedding
    exact hc
  change IsOpenEmbedding (circleCotangentTrivialization.symm ∘
    (fun z : ℂ ↦ (a * Circle.exp (θ z.re), z.im)))
  exact circleCotangentTrivialization.symm.isOpenEmbedding.comp hcylinder

end AtiyahSinger
