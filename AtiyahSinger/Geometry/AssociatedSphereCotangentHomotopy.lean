/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereCotangentSplitting

/-!
# Proper homotopy of the inverse associated cotangent realizations

Public module ID: M1071.

Two supplied smooth horizontal lifts give inverse cotangent realizations from
the actual upstairs cotangent bundle to the same pulled associated quotient.
The path below is fixed by convex interpolation of the horizontal lift and
the original cotangent splitting formulas. The common vertical comparison is
recovered from the exact representative formulas of the two realizations.

This is the geometric choice-independence needed before SG III.13 (13.16).
The compact-support K-theory transport uses these inverse maps. The existing
proper homotopy of the inverse generic splittings has the opposite direction;
an arbitrary proper homotopy cannot simply be inverted.

No compactness, separation, paracompactness, or metric choice is required once
the two smooth lifts are supplied. Properness of the entire time-dependent map
comes from an explicit homeomorphism of cylinders and compactness of time.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff unitInterval

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent verticalTangentTopology

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "Y" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "Q" => PrincipalBundlePullback (cotangentProjection (n := n) (M := B)) projection
local notation "C" => fun z : Z ↦ TangentSpace 𝓘(ℝ, E × R) z →L[ℝ] ℝ
local notation "q" => smoothAssociatedSphereProjection S

/-- The actual convex path, using the fixed canonical comparison recovered at the first lift. -/
def associatedSphereCotangentInverseHomotopyMap
    (H₀ H₁ : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift q) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    unitInterval × TotalSpace ((E × R) →L[ℝ] ℝ) C → AssociatedBundle G Q Y := by
  letI := S.toIsPrincipalBundle
  letI := associatedSphereChartedSpace S
  letI := associatedSphereIsManifold S
  letI := verticalTangentFiberBundle q (associatedSphereProjection_isSubmersion S)
  letI := verticalTangentVectorBundle q (associatedSphereProjection_isSubmersion S)
  letI := verticalTangentContMDiffVectorBundle q (associatedSphereProjection_isSubmersion S)
  intro p
  -- Interpolate only the supplied lift; the actual vertical restriction remains fixed.
  exact (associatedSphereCotangentHomeomorph S H₀).symm
    ((H₀.cotangentSplitHomeomorph q (associatedSphereProjection_isSubmersion S)).symm
      ⟨p.2.proj,
        p.2.snd.comp ((1 - (p.1 : ℝ)) • H₀.lift p.2.proj + (p.1 : ℝ) • H₁.lift p.2.proj),
        verticalCotangentRestriction q p.2.proj p.2.snd⟩)

set_option maxHeartbeats 2000000 in
-- Compare the entire time cylinders and then identify the original quotient endpoints.
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
open Function Set Topology in
/-- The specified convex path is a proper homotopy between the exact inverse realizations. -/
theorem exists_associatedSphereCotangentInverse_properHomotopy
    (H₀ H₁ : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift q) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    ∃ H : ContinuousMap.Homotopy
        (⟨(associatedSphereCotangentHomeomorph S H₀).symm,
          (associatedSphereCotangentHomeomorph S H₀).symm.continuous⟩ :
          C(TotalSpace ((E × R) →L[ℝ] ℝ) C, AssociatedBundle G Q Y))
        (⟨(associatedSphereCotangentHomeomorph S H₁).symm,
          (associatedSphereCotangentHomeomorph S H₁).symm.continuous⟩ :
          C(TotalSpace ((E × R) →L[ℝ] ℝ) C, AssociatedBundle G Q Y)),
      (∀ p, H p = associatedSphereCotangentInverseHomotopyMap S H₀ H₁ p) ∧
        IsProperMap H := by
  /- Stage 1: for a right inverse h of the original differential dq,
  split_h(xi)=(xi after h, xi restricted to ker dq) is a linear
  isomorphism. Its inverse sends (alpha,beta) to the covector
  w |-> alpha(dq(w)) + beta(w-h(dq(w))), with the latter argument in
  ker dq. Check both inverse identities on the original fibers.
  Stage 2: interpolate h_t=(1-t)h_0+t*h_1. The weights sum to one,
  so dq after h_t is identity. Both splitting formulas are affine
  in t; native bundle charts give joint continuity in time and point.
  Stage 3: retaining time makes (t,xi) |-> (t,split_t(xi)) a
  homeomorphism of the actual cylinders, using the continuous inverse
  from Stage 2.
  Stage 4: let e_i be the specified associated realizations. Their
  representative formulas give split_0 after e_0 = split_1 after e_1:
  both preserve the original base covector and canonical vertical
  covector. This common homeomorphism c has inverse e_0.symm after
  split_0.symm. The displayed path is c.symm after split_t, giving
  exactly e_0.symm and e_1.symm at its endpoints.
  Finally compose the cylinder homeomorphism with id times c.symm
  and forget time. Projection from the compact unit interval is
  proper, so the entire homotopy is proper. This uses joint cylinder
  continuity, not just properness of individual time slices. It
  asserts no properness of q or a vector-bundle projection and needs
  no compactness or separation of the base. The earlier homotopy
  in the reverse direction is not inverted. -/
  classical
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let hq := associatedSphereProjection_isSubmersion S
  let V := VerticalTangentModel (E × R) E
  let W := VerticalCotangentFiber («E» := E × R) (F := E) (q : Z → B)
  let Bc := ((q : Z → B) *ᵖ (fun b : B ↦ TangentSpace (𝓡 n) b →L[ℝ] ℝ))
  -- Native bundle charts make affine combinations jointly continuous without compact bases.
  have continuous_combination {B₀ : Type _} {Ct : Type _} {F₀ : Type _}
      [TopologicalSpace B₀] [TopologicalSpace Ct]
      [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
      {V₀ : B₀ → Type _} [∀ b, AddCommGroup (V₀ b)] [∀ b, Module ℝ (V₀ b)]
      [∀ b, TopologicalSpace (V₀ b)] [TopologicalSpace (TotalSpace F₀ V₀)]
      [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
      (b : Ct → B₀) (u v : ∀ x, V₀ (b x)) (a c : Ct → ℝ)
      (hu : Continuous (fun x ↦ (⟨b x, u x⟩ : TotalSpace F₀ V₀)))
      (hv : Continuous (fun x ↦ (⟨b x, v x⟩ : TotalSpace F₀ V₀)))
      (ha : Continuous a) (hc : Continuous c) :
      Continuous (fun x ↦ (⟨b x, a x • u x + c x • v x⟩ : TotalSpace F₀ V₀)) := by
    have hb : Continuous b := (FiberBundle.continuous_proj F₀ V₀).comp hu
    rw [continuous_iff_continuousAt]
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    let e := trivializationAt F₀ V₀ (b x)
    have hu' := ((FiberBundle.continuousAt_totalSpace F₀ _ (x₀ := x)).mp hu.continuousAt).2
    have hv' := ((FiberBundle.continuousAt_totalSpace F₀ _ (x₀ := x)).mp hv.continuousAt).2
    have hn : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
      hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F₀ V₀ (b x)))
    apply ((ha.continuousAt.smul hu').add (hc.continuousAt.smul hv')).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    change (e ⟨b y, a y • u y + c y • v y⟩).2 =
      a y • (e ⟨b y, u y⟩).2 + c y • (e ⟨b y, v y⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hy, map_add, map_smul]
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let Ct := TotalSpace ((E × R) →L[ℝ] ℝ) C
  let Split := TotalSpace ((E →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (Bc ×ᵇ W)
  let K := VerticalTangentFiber 𝓘(ℝ, E × R) 𝓘(ℝ, E) q
  let (x : Z) : AddCommGroup (Bc x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, E) (q x) →L[ℝ] ℝ)
    infer_instance
  let (x : Z) : Module ℝ (Bc x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, E) (q x) →L[ℝ] ℝ)
    infer_instance
  -- Stage 1: the inverse formula is determined by the original differential and lift.
  let D (x : Z) := mfderiv 𝓘(ℝ, E × R) 𝓘(ℝ, E) q x
  let a (h : ∀ x : Z, TangentSpace 𝓘(ℝ, E) (q x) →L[ℝ] TangentSpace 𝓘(ℝ, E × R) x)
      (x : Z) (ξ : C x) : Bc x × W x :=
    (ξ.comp (h x), verticalCotangentRestriction («E» := (E × R)) (F := E) q x ξ)
  let vertProj (h : ∀ x : Z, TangentSpace 𝓘(ℝ, E) (q x) →L[ℝ] TangentSpace 𝓘(ℝ, E × R) x)
      (hr : ∀ x, RightInverse (h x) (D x)) (x : Z) :
      TangentSpace 𝓘(ℝ, E × R) x →L[ℝ] K x :=
    (ContinuousLinearMap.id ℝ _ - (h x).comp (D x)).codRestrict
      (LinearMap.ker (D x).toLinearMap) (by
        intro w
        change D x (w - h x (D x w)) = 0
        rw [map_sub, hr x, sub_self])
  let b (h : ∀ x : Z, TangentSpace 𝓘(ℝ, E) (q x) →L[ℝ] TangentSpace 𝓘(ℝ, E × R) x)
      (hr : ∀ x, RightInverse (h x) (D x)) (x : Z) (v : Bc x × W x) : C x :=
    (show TangentSpace 𝓘(ℝ, E) (q x) →L[ℝ] ℝ from v.1).comp (D x) +
      v.2.comp (vertProj h hr x)
  have hleft (h : ∀ x : Z, TangentSpace 𝓘(ℝ, E) (q x) →L[ℝ] TangentSpace 𝓘(ℝ, E × R) x)
      (hr : ∀ x, RightInverse (h x) (D x)) (x : Z) :
      LeftInverse (b h hr x) (a h x) := by
    intro ξ
    ext w
    change ξ (h x (D x w)) + ξ (w - h x (D x w)) = ξ w
    rw [map_sub]
    ring
  have hright (h : ∀ x : Z, TangentSpace 𝓘(ℝ, E) (q x) →L[ℝ] TangentSpace 𝓘(ℝ, E × R) x)
      (hr : ∀ x, RightInverse (h x) (D x)) (x : Z) :
      RightInverse (b h hr x) (a h x) := by
    intro v
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro w
      change (show E →L[ℝ] ℝ from v.1) (D x (h x w)) +
        v.2 (vertProj h hr x (h x w)) = (show E →L[ℝ] ℝ from v.1) w
      have hp : vertProj h hr x (h x w) = 0 := by
        apply Subtype.ext
        change h x w - h x (D x (h x w)) = 0
        rw [hr x, sub_self]
      rw [hr x, hp, v.2.map_zero, add_zero]
    · ext w
      change (show E →L[ℝ] ℝ from v.1) (D x w.val) + v.2 (vertProj h hr x w.val) = v.2 w
      have hp : vertProj h hr x w.val = w := by
        apply Subtype.ext
        change w.val - h x (D x w.val) = w.val
        rw [show D x w.val = 0 from w.property, map_zero, sub_zero]
      rw [show D x w.val = 0 from w.property, map_zero, zero_add, hp]
  let e₀ : Ct ≃ₜ Split := H₀.cotangentSplitHomeomorph q hq
  let e₁ : Ct ≃ₜ Split := H₁.cotangentSplitHomeomorph q hq
  have he (Hlift : SmoothHorizontalLift q) (z : Ct) :
      Hlift.cotangentSplitHomeomorph q hq z = (⟨z.proj, a Hlift.lift z.proj z.snd⟩ : Split) :=
    (SmoothHorizontalLift.exists_cotangentSplitHomeomorph q hq Hlift).choose_spec.1 z
  have heinv (Hlift : SmoothHorizontalLift q) (z : Split) :
      (Hlift.cotangentSplitHomeomorph q hq).symm z =
        (⟨z.proj, b Hlift.lift Hlift.right_inv z.proj z.snd⟩ : Ct) := by
    apply (Hlift.cotangentSplitHomeomorph q hq).injective
    rw [Homeomorph.apply_symm_apply, he]
    exact (congrArg (fun v ↦ (⟨z.proj, v⟩ : Split))
      (hright Hlift.lift Hlift.right_inv z.proj z.snd)).symm
  -- Stage 2: interpolate the supplied right inverses without introducing a new choice.
  let L (t : ℝ) (x : Z) := (1 - t) • H₀.lift x + t • H₁.lift x
  have hL (t : ℝ) (x : Z) : RightInverse (L t x) (D x) := by
    intro v
    change D x ((1 - t) • H₀.lift x v + t • H₁.lift x v) = v
    rw [map_add, map_smul, map_smul, H₀.right_inv x, H₁.right_inv x]
    module
  have ha (t : ℝ) (x : Z) (ξ : C x) :
      a (L t) x ξ = (1 - t) • a H₀.lift x ξ + t • a H₁.lift x ξ := by
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro w
      change ξ ((1 - t) • H₀.lift x w + t • H₁.lift x w) =
        (1 - t) * ξ (H₀.lift x w) + t * ξ (H₁.lift x w)
      simp only [map_add, map_smul, smul_eq_mul]
    · change verticalCotangentRestriction («E» := (E × R)) (F := E) q x ξ =
        (1 - t) • verticalCotangentRestriction («E» := (E × R)) (F := E) q x ξ +
        t • verticalCotangentRestriction («E» := (E × R)) (F := E) q x ξ
      module
  have hb (t : ℝ) (x : Z) (v : Bc x × W x) :
      b (L t) (hL t) x v =
        (1 - t) • b H₀.lift H₀.right_inv x v + t • b H₁.lift H₁.right_inv x v := by
    have hp : vertProj (L t) (hL t) x =
        (1 - t) • vertProj H₀.lift H₀.right_inv x + t • vertProj H₁.lift H₁.right_inv x := by
      ext w
      change w - ((1 - t) • H₀.lift x (D x w) + t • H₁.lift x (D x w)) =
        (1 - t) • (w - H₀.lift x (D x w)) + t • (w - H₁.lift x (D x w))
      module
    ext w
    change (show E →L[ℝ] ℝ from v.1) (D x w) + v.2 (vertProj (L t) (hL t) x w) =
      (1 - t) * ((show E →L[ℝ] ℝ from v.1) (D x w) +
        v.2 (vertProj H₀.lift H₀.right_inv x w)) +
      t * ((show E →L[ℝ] ℝ from v.1) (D x w) + v.2 (vertProj H₁.lift H₁.right_inv x w))
    rw [hp]
    simp only [add_apply, smul_apply,
      map_add, map_smul, smul_eq_mul]
    ring
  let forward : I × Ct → Split := fun p ↦ ⟨p.2.proj, a (L p.1) p.2.proj p.2.snd⟩
  let back : I × Split → Ct := fun p ↦ ⟨p.2.proj, b (L p.1) (hL p.1) p.2.proj p.2.snd⟩
  have hcA : Continuous forward := by
    have hc₀ : Continuous (fun p : I × Ct ↦
        (⟨p.2.proj, a H₀.lift p.2.proj p.2.snd⟩ : Split)) :=
      (e₀.continuous.comp continuous_snd).congr (fun p ↦ he H₀ p.2)
    have hc₁ : Continuous (fun p : I × Ct ↦
        (⟨p.2.proj, a H₁.lift p.2.proj p.2.snd⟩ : Split)) :=
      (e₁.continuous.comp continuous_snd).congr (fun p ↦ he H₁ p.2)
    exact (continuous_combination (F₀ := (E →L[ℝ] ℝ) × (V →L[ℝ] ℝ))
      (V₀ := Bc ×ᵇ W) (fun p : I × Ct ↦ p.2.proj)
      (fun p ↦ a H₀.lift p.2.proj p.2.snd) (fun p ↦ a H₁.lift p.2.proj p.2.snd)
      (fun p ↦ 1 - (p.1 : ℝ)) (fun p ↦ (p.1 : ℝ)) hc₀ hc₁
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      (continuous_subtype_val.comp continuous_fst)).congr
        (fun p ↦ congrArg (fun v ↦ (⟨p.2.proj, v⟩ : Split)) (ha p.1 p.2.proj p.2.snd).symm)
  have hcQ : Continuous back := by
    have hc₀ : Continuous (fun p : I × Split ↦
        (⟨p.2.proj, b H₀.lift H₀.right_inv p.2.proj p.2.snd⟩ : Ct)) :=
      (e₀.symm.continuous.comp continuous_snd).congr (fun p ↦ heinv H₀ p.2)
    have hc₁ : Continuous (fun p : I × Split ↦
        (⟨p.2.proj, b H₁.lift H₁.right_inv p.2.proj p.2.snd⟩ : Ct)) :=
      (e₁.symm.continuous.comp continuous_snd).congr (fun p ↦ heinv H₁ p.2)
    exact (continuous_combination (F₀ := (E × R) →L[ℝ] ℝ) (V₀ := C)
      (fun p : I × Split ↦ p.2.proj)
      (fun p ↦ b H₀.lift H₀.right_inv p.2.proj p.2.snd)
      (fun p ↦ b H₁.lift H₁.right_inv p.2.proj p.2.snd)
      (fun p ↦ 1 - (p.1 : ℝ)) (fun p ↦ (p.1 : ℝ)) hc₀ hc₁
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      (continuous_subtype_val.comp continuous_fst)).congr
        (fun p ↦ congrArg (fun v ↦ (⟨p.2.proj, v⟩ : Ct)) (hb p.1 p.2.proj p.2.snd).symm)
  -- Stage 3: retain time to obtain a homeomorphism of the entire cylinders.
  let e : (I × Split) ≃ₜ (I × Ct) :=
    { toFun := fun p ↦ (p.1, back p)
      invFun := fun p ↦ (p.1, forward p)
      left_inv := by
        intro p
        apply Prod.ext
        · rfl
        · exact congrArg (fun v ↦ (⟨p.2.proj, v⟩ : Split))
            (hright (L p.1) (hL p.1) p.2.proj p.2.snd)
      right_inv := by
        intro p
        apply Prod.ext
        · rfl
        · exact congrArg (fun v ↦ (⟨p.2.proj, v⟩ : Ct))
            (hleft (L p.1) (hL p.1) p.2.proj p.2.snd)
      continuous_toFun := continuous_fst.prodMk hcQ
      continuous_invFun := continuous_fst.prodMk hcA }
  -- Stage 4: both original realizations recover the same canonical comparison.
  let a₀ := associatedSphereCotangentHomeomorph S H₀
  let a₁ := associatedSphereCotangentHomeomorph S H₁
  have hcommon (u : AssociatedBundle G Q Y) : e₀ (a₀ u) = e₁ (a₁ u) := by
    induction u using Quotient.inductionOn with
    | h z =>
      have h₀ := (exists_associatedSphereCotangentHomeomorph S H₀).choose_spec z.1 z.2
      have h₁ := (exists_associatedSphereCotangentHomeomorph S H₁).choose_spec z.1 z.2
      change e₀ (a₀ (associatedBundleMk G Q Y z.1 z.2)) =
        e₁ (a₁ (associatedBundleMk G Q Y z.1 z.2))
      change a₀ (associatedBundleMk G Q Y z.1 z.2) = _ at h₀
      change a₁ (associatedBundleMk G Q Y z.1 z.2) = _ at h₁
      rw [h₀, h₁]
      exact (e₀.apply_symm_apply _).trans (e₁.apply_symm_apply _).symm
  let c : AssociatedBundle G Q Y ≃ₜ Split := a₀.trans e₀
  have hendpoint (z : Ct) : c.symm (e₁ z) = a₁.symm z := by
    apply c.injective
    rw [c.apply_symm_apply]
    change e₁ z = e₀ (a₀ (a₁.symm z))
    rw [hcommon, a₁.apply_symm_apply]
  let homotopy : ContinuousMap.Homotopy
      (⟨a₀.symm, a₀.symm.continuous⟩ : C(Ct, AssociatedBundle G Q Y))
      (⟨a₁.symm, a₁.symm.continuous⟩ : C(Ct, AssociatedBundle G Q Y)) :=
    { toFun := fun p ↦ c.symm (forward p)
      continuous_toFun := c.symm.continuous.comp hcA
      map_zero_left := by
        intro z
        have hL0 : L (0 : ℝ) = H₀.lift := by
          funext x
          simp [L]
        change c.symm (⟨z.proj, a (L 0) z.proj z.snd⟩ : Split) = a₀.symm z
        rw [hL0, ← he H₀ z]
        change a₀.symm (e₀.symm (e₀ z)) = a₀.symm z
        rw [e₀.symm_apply_apply]
      map_one_left := by
        intro z
        have hL1 : L (1 : ℝ) = H₁.lift := by
          funext x
          simp [L]
        change c.symm (⟨z.proj, a (L 1) z.proj z.snd⟩ : Split) = a₁.symm z
        rw [hL1, ← he H₁ z]
        exact hendpoint z }
  refine ⟨homotopy, ?_, ?_⟩
  · intro p
    rfl
  -- Keeping time gives e.symm; only forgetting the compact time coordinate uses properness.
  exact c.symm.isProperMap.comp
    ((isProperMap_snd_of_compactSpace («X» := I) («Y» := Split)).comp e.symm.isProperMap)

end AtiyahSinger
