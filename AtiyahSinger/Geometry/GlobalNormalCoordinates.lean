/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TubularNeighborhood
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Normal coordinates for a globally straightened embedding

Public module ID: M1259.

Global complementary coordinates identify the actual quotient normal with the
complementary vector space. The identification uses the derivative of the same
ambient coordinates and the original quotient map. Its smoothness is proved
in the selected normal atlas, rather than by substituting a new normal bundle.
These coordinates supply the ordered complementary-coordinate model for Euclidean
stabilization and its tangent embedding.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [FiniteDimensional ℝ G] in
/-- Global complementary coordinates trivialize the original smooth normal quotient,
with their precise derivative formula on every representative. -/
theorem exists_global_normal_coordinates
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (a : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)
    (b : N ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F)
    (c : F ≃L[ℝ] E × G) (hstraight : ∀ x, b (f x) = c.symm (a x, 0)) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∃ e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ] G,
      (∀ (x : M) (w : F),
        e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ w) =
          (c (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b (f x) w)).2) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) ↦
          (z.proj, e z.proj z.snd)) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
        (fun z : M × G ↦
          (⟨z.1, (e z.1).symm z.2⟩ :
            TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))) := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let D (x : M) : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  let A (x : M) : E ≃L[ℝ] E := a.mfderivToContinuousLinearEquiv (by simp) x
  let B (x : M) : F ≃L[ℝ] F := b.mfderivToContinuousLinearEquiv (by simp) (f x)
  have hA (x : M) : (A x).toContinuousLinearMap = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) a x :=
    a.mfderivToContinuousLinearEquiv_coe (by simp)
  have hB (x : M) : (B x).toContinuousLinearMap = mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b (f x) :=
    b.mfderivToContinuousLinearEquiv_coe (by simp)
  let L : E →L[ℝ] F := c.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E G)
  have hL (x : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) L x = L :=
    L.hasFDerivAt.hasMFDerivAt.mfderiv
  have hchain (x : M) : (B x).toContinuousLinearMap.comp (D x) =
      L.comp (A x).toContinuousLinearMap := by
    have heq : (b : N → F) ∘ f = L ∘ a := funext hstraight
    have hevent : ((b : N → F) ∘ f) =ᶠ[𝓝 x] L ∘ a :=
      Filter.Eventually.of_forall (congrFun heq)
    have hd := Filter.EventuallyEq.mfderiv_eq hevent (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    rw [mfderiv_comp x (b.contMDiff.mdifferentiable (by simp) (f x))
      (f.contMDiff.mdifferentiable (by simp) x),
      mfderiv_comp x ((L.contDiff : ContDiff ℝ ∞ L).contMDiff.mdifferentiable (by simp) (a x))
        (a.contMDiff.mdifferentiable (by simp) x), hL] at hd
    rw [hB, hA]
    simpa only [tangentSpaceCast, ContinuousLinearMap.id_comp] using! hd
  let P (x : M) : F →L[ℝ] G :=
    (ContinuousLinearMap.snd ℝ E G).comp (c.toContinuousLinearMap.comp (B x).toContinuousLinearMap)
  have hPD (x : M) (v : E) : P x (D x v) = 0 := by
    have h := congrArg (fun k : E →L[ℝ] F ↦ k v) (hchain x)
    change B x (D x v) = c.symm (A x v, 0) at h
    change (c (B x (D x v))).2 = 0
    rw [h, c.apply_symm_apply]
  have hker (x : M) (w : F) (hw : P x w = 0) :
      w ∈ LinearMap.range (D x).toLinearMap := by
    refine ⟨(A x).symm (c (B x w)).1, ?_⟩
    apply (B x).injective
    have h := congrArg (fun k : E →L[ℝ] F ↦ k ((A x).symm (c (B x w)).1)) (hchain x)
    change B x (D x ((A x).symm (c (B x w)).1)) =
      c.symm (A x ((A x).symm (c (B x w)).1), 0) at h
    change B x (D x ((A x).symm (c (B x w)).1)) = B x w
    rw [h, (A x).apply_symm_apply]
    apply c.injective
    rw [c.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rfl
    · exact hw.symm
  let Q (x : M) : F →L[ℝ] V x := (LinearMap.range (D x).toLinearMap).mkQL
  let p (x : M) : V x →L[ℝ] G :=
    (LinearMap.range (D x).toLinearMap).liftQL (P x) (by
      rintro _ ⟨v, rfl⟩
      exact hPD x v)
  have hp (x : M) (w : F) : p x (Q x w) = P x w := rfl
  have hpbij (x : M) : Function.Bijective (p x) := by
    constructor
    · apply (injective_iff_map_eq_zero (p x)).mpr
      intro v hv
      obtain ⟨w, rfl⟩ := (LinearMap.range (D x).toLinearMap).mkQ_surjective v
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hker x w hv)
    · intro w
      refine ⟨Q x ((B x).symm (c.symm (0, w))), ?_⟩
      rw [hp]
      change (c (B x ((B x).symm (c.symm (0, w))))).2 = w
      rw [(B x).apply_symm_apply, c.apply_symm_apply]
  let e (x : M) : V x ≃L[ℝ] G :=
    (LinearEquiv.ofBijective (p x).toLinearMap (hpbij x)).toContinuousLinearEquiv
  have he (x : M) (w : F) : e x (Q x w) = P x w := hp x w
  let : T2Space M := a.toHomeomorph.isEmbedding.t2Space
  let : ParacompactSpace M := a.toHomeomorph.isClosedEmbedding.paracompactSpace
  let W := (f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))
  obtain ⟨s, hs, hQs⟩ := exists_smooth_normal_rightInverse f hf
  -- A smooth lift through the original quotient tests the forward normal coordinates.
  have hlift : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, F).tangent) ∞
      (fun z : TotalSpace F W ↦ (⟨f z.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, F) N)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj W), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        id z from contMDiffAt_id)).2
  have hbderiv : ContMDiff (𝓘(ℝ, F).tangent) 𝓘(ℝ, F) ∞
      (fun z : TangentBundle 𝓘(ℝ, F) N ↦
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b z.proj z.snd) :=
    (contMDiff_snd_tangentBundle_modelSpace F 𝓘(ℝ, F)).comp
      (b.contMDiff.contMDiff_tangentMap (m := ∞) (by simp))
  have hforward : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, G) ∞
      (fun z : TotalSpace (NormalModel E F) V ↦ P z.proj (s z.proj z.snd)) := by
    have h := (ContinuousLinearMap.snd ℝ E G).contDiff.contMDiff.comp
      (c.contDiff.contMDiff.comp (hbderiv.comp (hlift.comp hs)))
    apply h.congr
    intro z
    change (c ((B z.proj).toContinuousLinearMap (s z.proj z.snd))).2 = _
    rw [hB]
    rfl
  have hev (x : M) (v : V x) : e x v = P x (s x v) := by
    calc
      e x v = e x (Q x (s x v)) := congrArg (e x) (hQs x v).symm
      _ = P x (s x v) := he x (s x v)
  let B' (x : M) : F →L[ℝ] F := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b.symm (b (f x))
  have hBB (x : M) : (B x).toContinuousLinearMap.comp (B' x) =
      ContinuousLinearMap.id ℝ F := by
    have h := mfderiv_comp (b (f x))
      (b.contMDiff.mdifferentiable (by simp) (b.symm (b (f x))))
      (b.symm.contMDiff.mdifferentiable (by simp) (b (f x)))
    rw [show ((b : N → F) ∘ b.symm) = id from funext b.apply_symm_apply,
      mfderiv_id, b.symm_apply_apply] at h
    rw [hB]
    exact h.symm
  have hinv (x : M) (w : G) : Q x (B' x (c.symm (0, w))) = (e x).symm w := by
    apply (e x).injective
    rw [(e x).apply_symm_apply, he]
    change (c ((B x).toContinuousLinearMap (B' x (c.symm (0, w))))).2 = w
    have h := congrArg (fun k : F →L[ℝ] F ↦ k (c.symm (0, w))) (hBB x)
    change B x (B' x (c.symm (0, w))) = c.symm (0, w) at h
    change (c (B x (B' x (c.symm (0, w))))).2 = w
    rw [h, c.apply_symm_apply]
  -- Differentiate the same inverse ambient coordinates to obtain the smooth inverse lift.
  have hinput : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, F).tangent) ∞
      (fun z : M × G ↦
        (⟨b (f z.1), c.symm (0, z.2)⟩ : TangentBundle 𝓘(ℝ, F) F)) := by
    have hcoord : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) ∞
        (fun z : M × G ↦ (b (f z.1), c.symm (0, z.2))) :=
      (b.contMDiff.comp (f.contMDiff.comp contMDiff_fst)).prodMk
        (c.symm.contDiff.contMDiff.comp
          ((ContinuousLinearMap.inr ℝ E G).contDiff.contMDiff.comp contMDiff_snd))
    have hsymm : ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (𝓘(ℝ, F).tangent) ∞
        (fun z : F × F ↦ (⟨z.1, z.2⟩ : TangentBundle 𝓘(ℝ, F) F)) := by
      rw [chartedSpaceSelf_prod]
      exact
        (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, F)) (n := ∞))
    exact hsymm.comp hcoord
  have hraw := (b.symm.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hinput
  have hraw' : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, F).tangent) ∞
      (fun z : M × G ↦
        (⟨f z.1, B' z.1 (c.symm (0, z.2))⟩ : TangentBundle 𝓘(ℝ, F) N)) := by
    apply hraw.congr
    intro z
    dsimp only [Function.comp_apply, tangentMap]
    rw [b.symm_apply_apply]
    rfl
  have hback : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
      (fun z : M × G ↦ (⟨z.1, B' z.1 (c.symm (0, z.2))⟩ : TotalSpace F W)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_fst, ?_⟩
    have h := (Bundle.contMDiffAt_totalSpace.mp (hraw' z)).2
    exact h
  have hinverse := (smoothNormalQuotientMap f hf).contMDiff.comp hback
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x w
    change e x (Q x w) = _
    rw [he]
    change (c ((B x).toContinuousLinearMap w)).2 = _
    rw [hB]
    rfl
  · apply ((contMDiff_proj V).prodMk hforward).congr
    intro z
    exact Prod.ext rfl (hev z.proj z.snd)
  · apply hinverse.congr
    intro z
    change (⟨z.1, (e z.1).symm z.2⟩ : TotalSpace (NormalModel E F) V) =
      ⟨z.1, Q z.1 (B' z.1 (c.symm (0, z.2)))⟩
    exact congrArg (TotalSpace.mk z.1) (hinv z.1 z.2).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [FiniteDimensional ℝ G] in
/-- Global complementary coordinates give a normalized tube onto the whole ambient manifold.
The tube uses exactly the supplied normal coordinates, including their derivative normalization. -/
theorem exists_global_normal_tube
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (a : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)
    (b : N ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F)
    (c : F ≃L[ℝ] E × G) (hstraight : ∀ x, b (f x) = c.symm (a x, 0)) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∀ e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ] G,
      (∀ (x : M) (w : F),
        e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ w) =
          (c (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b (f x) w)).2) →
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) ↦
          (z.proj, e z.proj z.snd)) →
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
        (fun z : M × G ↦ (⟨z.1, (e z.1).symm z.2⟩ :
          TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))) →
      ∃ T : TubularNeighborhood f hf,
        ∀ z, T.totalMap f hf z = b.symm (c.symm (a z.proj, e z.proj z.snd)) := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  intro e he hforward hinverse
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let NB := TotalSpace (NormalModel E F) V
  -- Compose the actual normal trivialization with the same global ambient coordinates.
  let τ (z : NB) : N := b.symm (c.symm (a z.proj, e z.proj z.snd))
  let ι (y : N) : NB :=
    ⟨a.symm (c (b y)).1, (e (a.symm (c (b y)).1)).symm (c (b y)).2⟩
  have hleft (z : NB) : ι (τ z) = z := by
    have hbase : a.symm (c (b (τ z))).1 = z.proj := by simp [τ]
    have hfiber : (c (b (τ z))).2 = e z.proj z.snd := by simp [τ]
    dsimp only [ι]
    rw [hfiber, hbase, (e z.proj).symm_apply_apply]
  have hright (y : N) : τ (ι y) = y := by
    simp only [τ, ι, a.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
      Prod.mk.eta, c.symm_apply_apply, b.symm_apply_apply]
  have hτ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F) ∞ τ := by
    have h := (a.contMDiff.comp contMDiff_fst).prodMk
      (show ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, G) ∞
        (fun z : M × G ↦ z.2) from contMDiff_snd)
    have h' := h.comp hforward
    have h'' : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, E × G) ∞
        (fun z : NB ↦ (a z.proj, e z.proj z.snd)) := by
      rw [modelWithCornersSelf_prod]
      rw [chartedSpaceSelf_prod] at h'
      exact h'
    exact b.symm.contMDiff.comp (c.symm.contDiff.contMDiff.comp h'')
  have hι : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞ ι := by
    have hcoords := c.contDiff.contMDiff.comp b.contMDiff
    have h := (a.symm.contMDiff.comp
      ((ContinuousLinearMap.fst ℝ E G).contDiff.contMDiff.comp hcoords)).prodMk
      ((ContinuousLinearMap.snd ℝ E G).contDiff.contMDiff.comp hcoords)
    exact hinverse.comp h
  let U : TopologicalSpace.Opens N := ⟨Set.univ, isOpen_univ⟩
  let D : Diffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F) NB U ∞ :=
    { toFun := fun z ↦ ⟨τ z, Set.mem_univ _⟩
      invFun := fun y ↦ ι y.val
      left_inv := hleft
      right_inv := fun y ↦ Subtype.ext (hright y.val)
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff U _).mp hτ
      contMDiff_invFun := hι.comp (contMDiff_subtype_val (U := U)) }
  have hzero (x : M) : (D ⟨x, 0⟩ : N) = f x := by
    change b.symm (c.symm (a x, e x 0)) = f x
    rw [(e x).map_zero, ← hstraight, b.symm_apply_apply]
  refine ⟨{ target := U, diffeomorph := D, map_zero := hzero, normal_deriv := ?_ },
    fun _ ↦ rfl⟩
  -- Differentiate a fiber curve; its quotient derivative is fixed by the supplied coordinates.
  intro x
  dsimp only
  let e₀ := (trivializationAt (NormalModel E F) V x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt (NormalModel E F) V x)
  let L : NormalModel E F →L[ℝ] G :=
    (e x).toContinuousLinearMap.comp e₀.symm.toContinuousLinearMap
  let γ (w : NormalModel E F) : F := c.symm (a x, L w)
  let d : NormalModel E F →L[ℝ] F :=
    c.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inr ℝ E G).comp L)
  have hγ : HasFDerivAt γ d 0 := by
    exact c.symm.toContinuousLinearMap.hasFDerivAt.comp 0
      ((hasFDerivAt_const (a x) (0 : NormalModel E F)).prodMk L.hasFDerivAt)
  have hγzero : γ 0 = b (f x) := by simp [γ, hstraight]
  have hB := (b.symm.contMDiff.mdifferentiable (by simp) (γ 0)).hasMFDerivAt
  have hcomp := hB.comp 0 hγ.hasMFDerivAt
  have hBB : (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b (f x)).comp
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b.symm (b (f x))) =
        ContinuousLinearMap.id ℝ F := by
    have h := mfderiv_comp (b (f x))
      (b.contMDiff.mdifferentiable (by simp) (b.symm (b (f x))))
      (b.symm.contMDiff.mdifferentiable (by simp) (b (f x)))
    rw [show ((b : N → F) ∘ b.symm) = id from funext b.apply_symm_apply,
      mfderiv_id, b.symm_apply_apply] at h
    exact h.symm
  intro v
  change (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
    (mfderiv 𝓘(ℝ, NormalModel E F) 𝓘(ℝ, F) (b.symm ∘ γ) 0 v) = e₀.symm v
  rw [hcomp.mfderiv, hγzero]
  apply (e x).injective
  rw [he]
  have h := congrArg (fun k : F →L[ℝ] F ↦ k (d v)) hBB
  change (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b (f x))
    ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b.symm (b (f x))) (d v)) = d v at h
  change (c ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b (f x))
    ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) b.symm (b (f x))) (d v)))).2 = e x (e₀.symm v)
  rw [h]
  change (c (c.symm (0, L v))).2 = e x (e₀.symm v)
  rw [c.apply_symm_apply]
  rfl

end AtiyahSinger
