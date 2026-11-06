/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedHodgeOperator
public import AtiyahSinger.Geometry.HodgeNaturality
public import AtiyahSinger.Geometry.SphereDeRham

/-!
# The round sphere metric and the actual action on graded forms

Public module ID: M1433.

The round metric is induced by the differential of the original sphere inclusion
into the actual Euclidean product. Its orthogonal invariance uses the specified
diagonal block action, including the unchanged last coordinate. The natural left
action on forms is inverse pullback in every homogeneous degree. Its restrictions
to the original even and odd subspaces intertwine the actual positive d + delta.

SG III.9, pp.211--212, explicitly uses the isometry action and the parity-changing
de Rham operator to define the equivariant Euler index. III.13.7 uses this sphere
action. The explicit native tangent metric construction is a standard supplement;
no abstract cohomology representation is substituted for a smooth-form action.
The degreewise inverse-pullback identities supply the laws of this same
action on the original total-form direct sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ContinuousLinearMap

open scoped DirectSum Manifold ContDiff InnerProductSpace

-- Nested original direct sums and parity submodules retain their standard instances.
set_option maxSynthPendingDepth 25

/-- The actual sphere inclusion induces the smooth round tangent metric. -/
theorem exists_orthogonalSphereRoundMetric (r : ℕ) :
    ∃ g : SmoothTangentMetric (n := r) (M := OrthogonalSphere r),
      ∀ (x : OrthogonalSphere r) (v w : TangentSpace (𝓡 r) x),
        g.inner x v w =
          @inner ℝ (OrthogonalSphereAmbient r) inferInstance
            (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r)
              (fun y : OrthogonalSphere r ↦ y.val) x v)
            (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r)
              (fun y : OrthogonalSphere r ↦ y.val) x w) := by
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  let S := OrthogonalSphere r
  let J := 𝓡 r
  let T := TangentSpace J (M := S)
  let (x : S) : IsNormableSpace ℝ (T x) :=
    (VectorBundle.continuousLinearEquivAt ℝ V T x).isNormableSpace
  let D (x : S) : T x →L[ℝ] W :=
    mfderiv J 𝓘(ℝ, W) (fun y : S ↦ y.val) x
  let q (x : S) : T x →L[ℝ] T x →L[ℝ] ℝ :=
    (innerSL ℝ : W →L[ℝ] W →L[ℝ] ℝ).bilinearComp (D x) (D x)
  have hD (x : S) : Function.Injective (D x) := by
    convert! injective_mvfderiv_subtypeVal_sphere x
  -- Pull back the ambient form by the actual injective sphere differential.
  refine ⟨{ inner := q
            symm := fun x v w ↦ real_inner_comm (D x w) (D x v)
            pos := ?_
            isVonNBounded := ?_
            contMDiff := ?_ }, fun x v w ↦ rfl⟩
  · intro x v hv
    change 0 < inner ℝ (D x v) (D x v)
    apply real_inner_self_pos.mpr
    exact fun h ↦ hv ((hD x) (by simpa using h))
  · intro x
    -- Identify the fiber with its actual finite-dimensional image, without changing topology.
    let : FiniteDimensional ℝ (T x) :=
      LinearEquiv.finiteDimensional
        (VectorBundle.continuousLinearEquivAt ℝ V T x).symm.toLinearEquiv
    let e : T x ≃L[ℝ] (D x).range :=
      (LinearEquiv.ofInjective (D x).toLinearMap (hD x)).toContinuousLinearEquiv
    have hball : Bornology.IsVonNBounded ℝ (Metric.ball (0 : (D x).range) 1) :=
      NormedSpace.isVonNBounded_ball ℝ _ _
    apply (hball.image e.symm.toContinuousLinearMap).subset
    intro v hv
    refine ⟨e v, ?_, e.symm_apply_apply v⟩
    rw [Metric.mem_ball, dist_zero_right]
    change ‖D x v‖ < 1
    change inner ℝ (D x v) (D x v) < 1 at hv
    rw [real_inner_self_eq_norm_sq] at hv
    nlinarith [norm_nonneg (D x v)]
  · intro x₀
    -- In native tangent coordinates, this is the smooth derivative Gram form.
    rw [contMDiffAt_section]
    let L (x : S) : V →L[ℝ] W :=
      inTangentCoordinates J 𝓘(ℝ, W) id (fun y : S ↦ y.val) D x₀ x
    have hL : ContMDiffAt J 𝓘(ℝ, V →L[ℝ] W) ∞ L x₀ :=
      (contMDiff_coe_sphere (n := r) (m := ∞) x₀).mfderiv_const (by simp)
    let Q : W →L[ℝ] W →L[ℝ] ℝ := innerSL ℝ
    have hQL : ContMDiffAt J 𝓘(ℝ, V →L[ℝ] W →L[ℝ] ℝ) ∞
        (fun x : S ↦ Q.comp (L x)) x₀ :=
      (contMDiffAt_const (c := Q)).clm_comp hL
    have hPre : ContMDiffAt J 𝓘(ℝ, (W →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ) ∞
        (fun x : S ↦ (L x).precomp ℝ) x₀ := hL.clm_precomp
    have hGram : ContMDiffAt J 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ) ∞
        (fun x : S ↦ (L x).precomp ℝ |>.comp
          (Q.comp (L x))) x₀ :=
      hPre.clm_comp hQL
    apply hGram.congr_of_eventuallyEq
    filter_upwards [(trivializationAt V T x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V T x₀)] with x hx
    ext v w
    rw [hom_trivializationAt_apply,
      inCoordinates_apply_eq₂ hx hx (by simp)]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      bilinearComp_apply, coe_innerSL_apply, LinearMap.id_coe, id_eq, inTangentCoordinates,
      inCoordinates, TangentBundle.continuousLinearMapAt_model_space, comp_apply,
      precomp_apply, q, L]
    change inner ℝ (D x ((trivializationAt V T x₀).symm x v))
        (D x ((trivializationAt V T x₀).symm x w)) =
      inner ℝ (D x ((trivializationAt V T x₀).symmL ℝ x v))
        (D x ((trivializationAt V T x₀).symmL ℝ x w))
    rw [(trivializationAt V T x₀).symmL_apply hx,
      (trivializationAt V T x₀).symmL_apply hx]

/-- The round metric on the original sphere, fixed by the ambient inclusion formula. -/
def orthogonalSphereRoundMetric (r : ℕ) :
    SmoothTangentMetric (n := r) (M := OrthogonalSphere r) :=
  (exists_orthogonalSphereRoundMetric r).choose

/-- The chosen round metric is the ambient inner product on actual tangent derivatives. -/
theorem orthogonalSphereRoundMetric_inner (r : ℕ) (x : OrthogonalSphere r)
    (v w : TangentSpace (𝓡 r) x) :
    (orthogonalSphereRoundMetric r).inner x v w =
      @inner ℝ (OrthogonalSphereAmbient r) inferInstance
        (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r)
          (fun y : OrthogonalSphere r ↦ y.val) x v)
        (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r)
          (fun y : OrthogonalSphere r ↦ y.val) x w) := by
  -- Use the same metric selected by the original existence witness.
  exact (exists_orthogonalSphereRoundMetric r).choose_spec x v w

/-- The specified diagonal orthogonal action preserves the actual round metric. -/
theorem orthogonalSphereRoundMetric_invariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
    (v w : TangentSpace (𝓡 r) x) :
    (orthogonalSphereRoundMetric r).inner (orthogonalSphereDiffeomorph r A x)
        (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x v)
        (mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x w) =
      (orthogonalSphereRoundMetric r).inner x v w := by
  -- Differentiate the exact ambient equivariance identity for the original block action.
  let ι : OrthogonalSphere r → OrthogonalSphereAmbient r := fun y ↦ y.val
  let D := orthogonalSphereDiffeomorph r A
  let L := (orthogonalSphereBlockIsometry r A).toContinuousLinearEquiv
  have hι : MDifferentiable (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)
  have hD : MDifferentiable (𝓡 r) (𝓡 r) D := D.mdifferentiable (by simp)
  have hcomm : ι ∘ D = L ∘ ι := rfl
  have hchain (u : TangentSpace (𝓡 r) x) :
      mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι (D x)
          (mfderiv (𝓡 r) (𝓡 r) D x u) =
        L (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι x u) := by
    rw [← mfderiv_comp_apply x (hι (D x)) (hD x) u, hcomm,
      mfderiv_comp_apply x L.mdifferentiableAt (hι x) u,
      ContinuousLinearEquiv.mfderiv_eq]
    rfl
  -- The same ambient linear isometry preserves the two transported tangent vectors.
  rw [orthogonalSphereRoundMetric_inner, orthogonalSphereRoundMetric_inner]
  change @inner ℝ (OrthogonalSphereAmbient r) inferInstance
    (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι (D x)
      (mfderiv (𝓡 r) (𝓡 r) D x v))
    (mfderiv (𝓡 r) 𝓘(ℝ, OrthogonalSphereAmbient r) ι (D x)
      (mfderiv (𝓡 r) (𝓡 r) D x w)) = _
  rw [hchain v, hchain w]
  exact (orthogonalSphereBlockIsometry r A).inner_map_map _ _

/-- Inverse pullback acts on every original homogeneous form, preserving its degree. -/
def orthogonalSphereTotalFormAction (r : ℕ) (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    TotalSmoothDifferentialForm (n := r) (OrthogonalSphere r) →ₗ[ℂ]
      TotalSmoothDifferentialForm (n := r) (OrthogonalSphere r) :=
  DirectSum.lmap (fun p ↦ smoothFormPullback
    (fun x : OrthogonalSphere r ↦ A⁻¹ • x) (contMDiff_orthogonalSphere_smul r A⁻¹) p)

/-- Functorial inverse pullback supplies the laws of one natural action on total forms. -/
theorem orthogonalSphereTotalFormAction_laws (r : ℕ) :
    orthogonalSphereTotalFormAction r 1 = LinearMap.id ∧
    ∀ A B : Matrix.orthogonalGroup (Fin r) ℝ,
      orthogonalSphereTotalFormAction r (A * B) =
        (orthogonalSphereTotalFormAction r A).comp (orthogonalSphereTotalFormAction r B) := by
  /- Stage 1: on each homogeneous form, the actual tangent formula makes
  pullback by the identity the identity. Stage 2: the chain rule shows that
  pullback reverses composition. Group inversion reverses multiplication,
  so their combination is a left action. Extend these degreewise identities
  to the original direct sum; finite support is preserved because no degree
  changes. These laws certify the specified map, not an arbitrary action. -/
  classical
  let S := OrthogonalSphere r
  let J := 𝓡 r
  -- The original pointwise pullback formula fixes every homogeneous form under the identity.
  have hid (p : ℕ) (form : SmoothDifferentialForm (n := r) S p) :
      smoothFormPullback (n := r) (m := r) (fun x : S ↦ x) contMDiff_id p form = form := by
    apply Subtype.ext
    funext x
    rw [smoothFormPullback_apply]
    change (form.val x).compContinuousLinearMap (mfderiv J J (_root_.id : S → S) x) = _
    rw [mfderiv_id]
    rfl
  -- The same tangent chain rule reverses composition before any direct-sum construction.
  have hcomp (f g : S → S) (hf : ContMDiff J J ∞ f) (hg : ContMDiff J J ∞ g)
      (p : ℕ) (form : SmoothDifferentialForm (n := r) S p) :
      smoothFormPullback (g ∘ f) (hg.comp hf) p form =
        smoothFormPullback f hf p (smoothFormPullback g hg p form) := by
    apply Subtype.ext
    funext x
    rw [smoothFormPullback_apply, smoothFormPullback_apply, smoothFormPullback_apply]
    rw [mfderiv_comp x ((hg.mdifferentiable (by simp)) (f x))
      ((hf.mdifferentiable (by simp)) x)]
    rfl
  constructor
  · apply LinearMap.ext
    intro form
    apply DFinsupp.ext
    intro p
    change smoothFormPullback _ _ p (form p) = form p
    simpa only [inv_one, one_smul] using hid p (form p)
  · intro A B
    apply LinearMap.ext
    intro form
    apply DFinsupp.ext
    intro p
    change smoothFormPullback _ _ p (form p) =
      smoothFormPullback _ _ p (smoothFormPullback _ _ p (form p))
    -- Inversion reverses the group product, cancelling the reversal in pullback.
    simpa only [mul_inv_rev, mul_smul, Function.comp_def] using
      hcomp (fun x : S ↦ A⁻¹ • x) (fun x : S ↦ B⁻¹ • x)
        (contMDiff_orthogonalSphere_smul r A⁻¹)
        (contMDiff_orthogonalSphere_smul r B⁻¹) p (form p)

/-- The original natural representation on total smooth sphere forms. -/
def orthogonalSphereTotalFormRepresentation (r : ℕ) :
    Representation ℂ (Matrix.orthogonalGroup (Fin r) ℝ)
      (TotalSmoothDifferentialForm (n := r) (OrthogonalSphere r)) where
  toFun := orthogonalSphereTotalFormAction r
  map_one' := (orthogonalSphereTotalFormAction_laws r).1
  map_mul' := (orthogonalSphereTotalFormAction_laws r).2

/-- Restriction of the same inverse-pullback action to actual even smooth forms. -/
def orthogonalSphereEvenFormRepresentation (r : ℕ) :
    Representation ℂ (Matrix.orthogonalGroup (Fin r) ℝ)
      (evenSmoothDifferentialForms (n := r) (M := OrthogonalSphere r)) where
  toFun A := (orthogonalSphereTotalFormAction r A).restrict (by
    intro form hform p hp
    change smoothFormPullback _ _ p (form p) = 0
    rw [hform p hp, map_zero])
  map_one' := by
    apply LinearMap.ext
    intro form
    apply Subtype.ext
    exact congrArg (fun f ↦ f form.val) (orthogonalSphereTotalFormAction_laws r).1
  map_mul' A B := by
    apply LinearMap.ext
    intro form
    apply Subtype.ext
    exact congrArg (fun f ↦ f form.val) ((orthogonalSphereTotalFormAction_laws r).2 A B)

/-- Restriction of the same inverse-pullback action to actual odd smooth forms. -/
def orthogonalSphereOddFormRepresentation (r : ℕ) :
    Representation ℂ (Matrix.orthogonalGroup (Fin r) ℝ)
      (oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r)) where
  toFun A := (orthogonalSphereTotalFormAction r A).restrict (by
    intro form hform p hp
    change smoothFormPullback _ _ p (form p) = 0
    rw [hform p hp, map_zero])
  map_one' := by
    apply LinearMap.ext
    intro form
    apply Subtype.ext
    exact congrArg (fun f ↦ f form.val) (orthogonalSphereTotalFormAction_laws r).1
  map_mul' A B := by
    apply LinearMap.ext
    intro form
    apply Subtype.ext
    exact congrArg (fun f ↦ f form.val) ((orthogonalSphereTotalFormAction_laws r).2 A B)

/-- The actual round positive de Rham operator intertwines the original parity actions. -/
theorem positiveHodgeDirac_orthogonalSphere_equivariant (r : ℕ)
    (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    (positiveHodgeDirac (orthogonalSphereRoundMetric r)).comp
        (orthogonalSphereEvenFormRepresentation r A) =
      (orthogonalSphereOddFormRepresentation r A).comp
        (positiveHodgeDirac (orthogonalSphereRoundMetric r)) := by
  /- Stage 1: exterior differentiation commutes with the original inverse
  pullback. The same sphere diffeomorphism preserves the round metric, so
  metric codifferential naturality applies to that inverse diffeomorphism
  with precisely this metric and its own volume density. Stage 2: sum the
  degreewise identities in the actual direct sum and restrict the common
  parity-changing operator to the original even and odd submodules. -/
  classical
  -- Both degreewise operators commute with this exact inverse group pullback.
  let g := orthogonalSphereRoundMetric r
  let e := orthogonalSphereDiffeomorph r A⁻¹
  have hd (p : ℕ) (form : SmoothDifferentialForm (n := r) (OrthogonalSphere r) p) :
      smoothFormExteriorDerivative p (smoothFormPullback e e.contMDiff p form) =
        smoothFormPullback e e.contMDiff (p + 1) (smoothFormExteriorDerivative p form) :=
    LinearMap.congr_fun (smoothFormExteriorDerivative_pullback e e.contMDiff p) form
  have hδ (p : ℕ) (form : SmoothDifferentialForm (n := r) (OrthogonalSphere r) (p + 1)) :
      smoothFormCodifferential g p (smoothFormPullback e e.contMDiff (p + 1) form) =
        smoothFormPullback e e.contMDiff p (smoothFormCodifferential g p form) :=
    LinearMap.congr_fun (smoothFormCodifferential_pullback g g e
      (orthogonalSphereRoundMetric_invariant r A⁻¹) p) form
  -- Every natural-number summand contributes its original adjacent degrees.
  have htotal : (totalFormHodgeDirac g).comp (orthogonalSphereTotalFormAction r A) =
      (orthogonalSphereTotalFormAction r A).comp (totalFormHodgeDirac g) := by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro form
    cases p with
    | zero =>
      simp only [LinearMap.comp_apply, orthogonalSphereTotalFormAction, DirectSum.lmap_lof,
        totalFormHodgeDirac, LinearMap.add_apply, totalFormExteriorDerivative,
        totalFormCodifferential, DirectSum.toModule_lof, LinearMap.zero_apply, add_zero]
      exact congrArg (DirectSum.lof ℂ ℕ _ 1) (hd 0 form)
    | succ p =>
      simp only [LinearMap.comp_apply, orthogonalSphereTotalFormAction, DirectSum.lmap_lof,
        totalFormHodgeDirac, LinearMap.add_apply, totalFormExteriorDerivative,
        totalFormCodifferential, DirectSum.toModule_lof, map_add]
      exact congrArg₂ (fun u v ↦ DirectSum.lof ℂ ℕ _ (p + 1 + 1) u +
        DirectSum.lof ℂ ℕ _ p v) (hd (p + 1) form) (hδ p form)
  -- Restrict the same total identity to the original parity subspaces.
  apply LinearMap.ext
  intro form
  apply Subtype.ext
  exact LinearMap.congr_fun htotal form.val

end AtiyahSinger
