/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantEllipticSymbolRestriction
public import AtiyahSinger.Analysis.EquivariantIndexRestriction
public import AtiyahSinger.Topology.EquivariantActionTransport
public import AtiyahSinger.Topology.EquivariantRestriction

/-!
# Restriction of the full equivariant analytic index

Public module ID: M0464.

Restriction along a smooth continuous group homomorphism commutes with the
full analytic index on every original cotangent support K class. The induced
base action is literally MulAction.compHom. The native cotangent lift of that
action is identified with restriction of the original cotangent action by an
actual equality of the base diffeomorphisms and their inverse differentials.
The native-carrier adaptation transports the existing K restriction map.

Sources: SG III.9, Definition 9.3, pp.211--212, gives the actual
kernel-minus-cokernel representation index. SG III.13 (13.7)--(13.8),
pp.246--247, gives the ordinary symbol-class index construction. The exact
full arbitrary-class restriction statement is a project supplement;
no exact independent source has been identified. Its proof retains the actual
operator and both representations, then uses the same invariant clopen family
on both sides.

Both groups have the standard finite-dimensional Lie models required by the
existing index construction. No injectivity or surjectivity of the group
homomorphism, invariant connected component, nonempty base, or positive base
dimension is assumed. Smoothness of the homomorphism is supplied explicitly;
no automatic-smoothness theorem is silently invoked. The comparison checks
the same support triples, actual native actions and defect representations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff BigOperators

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G]
  {VH H : Type*} [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [LieGroup 𝓘(ℝ, VH) ∞ H]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

/-- The original group restriction, transported to the native restricted cotangent lift. -/
def equivariantCotangentKZeroRestrict (φ : H →ₜ* G)
    (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, VG) ∞ φ) :
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →+
      EquivariantSupportTripleKZero H (CotangentTotalSpace (n := n) (M := M)) := by
  letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
  letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  -- Compare the actual base diffeomorphisms before transporting their inverse differentials.
  have hLift : smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH) =
      MulAction.compHom (CotangentTotalSpace (n := n) (M := M)) φ.toMonoidHom := by
    apply MulAction.ext
    funext h z
    have he : Diffeomorph.smul (M := M) 𝓘(ℝ, VH)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h =
        Diffeomorph.smul (M := M) 𝓘(ℝ, VG)
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (φ h) := by
      apply Diffeomorph.ext
      intro x
      rfl
    exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) he
  -- Transport the dependent quotient type together with its continuity certificate.
  have transport (a b : MulAction H (CotangentTotalSpace (n := n) (M := M)))
      (ha : letI := a
        ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)))
      (hb : letI := b
        ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)))
      (hab : a = b) :
      (letI := a
       letI := ha
       EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →+
         EquivariantSupportTripleKZero H (CotangentTotalSpace (n := n) (M := M))) →
      (letI := b
       letI := hb
       EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) →+
         EquivariantSupportTripleKZero H (CotangentTotalSpace (n := n) (M := M))) := by
    cases hab
    exact id
  letI := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  letI := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  letI : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  -- The value remains the original quotient homomorphism, transported only along hLift.
  exact transport _ _ (MulAction.continuousSMul_compHom φ.continuous)
    inferInstance hLift.symm
    (equivariantSupportTripleKZeroRestrict
      (X := CotangentTotalSpace (n := n) (M := M)) φ)


/-- Restricting the original symbol class retains its actual symbol and native cotangent lift. -/
theorem EquivariantEllipticSymbolData.kClass_restrict [CompactSpace M]
    (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G))
    (φ : H →ₜ* G) (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, VG) ∞ φ) :
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    equivariantCotangentKZeroRestrict (n := n) (M := M) φ hφ a.kClass =
      (a.restrict φ hφ).kClass := by
  let := modelTopology (EuclideanSpace ℂ (Fin a.source.rank)) a.source.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin a.target.rank)) a.target.Fiber
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  let AG := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := AG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let CG : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := CG
  let AH := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let := AH
  let := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let CH : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := CH
  let AR : MulAction H (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.compHom (CotangentTotalSpace (n := n) (M := M)) φ.toMonoidHom
  let CR : letI := AR; ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom φ.continuous
  -- The inverse differentials come from the identical base diffeomorphisms.
  have he (h : H) : Diffeomorph.smul (M := M) 𝓘(ℝ, VH)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h =
      Diffeomorph.smul (M := M) 𝓘(ℝ, VG)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (φ h) := by
    apply Diffeomorph.ext
    intro x
    rfl
  have hLift : AH = AR := by
    apply MulAction.ext
    funext h z
    exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) (he h)
  have hmap : equivariantCotangentKZeroRestrict (n := n) (M := M) φ hφ =
      (kActionTransport AR AH CR CH hLift.symm).comp
        (equivariantSupportTripleKZeroRestrict
          (X := CotangentTotalSpace (n := n) (M := M)) φ) := by
    unfold equivariantCotangentKZeroRestrict
    exact transport_hom_eq_comp AR AH CR CH hLift.symm _
  -- Transport the same raw support triple and compare both actual total-space actions.
  rw [hmap, AddMonoidHom.comp_apply]
  unfold EquivariantEllipticSymbolData.kClass equivariantHomogeneousSymbolKClass
  rw [equivariantSupportTripleKZeroRestrict_apply]
  apply kActionTransport_generator
  · apply MulAction.ext
    funext h z
    change (⟨cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (φ h))
        z.proj, a.sourceAction.linearMap (φ h) z.proj.proj z.snd⟩ :
          TotalSpace Unit ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ a.source.Fiber)) =
      ⟨cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h)
        z.proj, a.sourceAction.linearMap (φ h) z.proj.proj z.snd⟩
    have hξ := congrArg
      (fun w : CotangentTotalSpace (n := n) (M := M) ↦
        (show CotangentModel n from w.snd))
      (congrArg (fun e ↦ cotangentDiffeomorphMap e z.proj) (he h).symm)
    exact congrArg (fun ξ : CotangentFiber (n := n) (φ h • z.proj.proj) ↦
      (⟨⟨φ h • z.proj.proj, ξ⟩, a.sourceAction.linearMap (φ h) z.proj.proj z.snd⟩ :
        TotalSpace Unit ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ a.source.Fiber))) hξ
  · apply MulAction.ext
    funext h z
    change (⟨cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (φ h))
        z.proj, a.targetAction.linearMap (φ h) z.proj.proj z.snd⟩ :
          TotalSpace Unit ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ a.target.Fiber)) =
      ⟨cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h)
        z.proj, a.targetAction.linearMap (φ h) z.proj.proj z.snd⟩
    have hξ := congrArg
      (fun w : CotangentTotalSpace (n := n) (M := M) ↦
        (show CotangentModel n from w.snd))
      (congrArg (fun e ↦ cotangentDiffeomorphMap e z.proj) (he h).symm)
    exact congrArg (fun ξ : CotangentFiber (n := n) (φ h • z.proj.proj) ↦
      (⟨⟨φ h • z.proj.proj, ξ⟩, a.targetAction.linearMap (φ h) z.proj.proj z.snd⟩ :
        TotalSpace Unit ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ a.target.Fiber))) hξ

set_option maxHeartbeats 800000 in
-- Compare four native cotangent actions and the dependent quotients simultaneously.
/-- The original group restriction commutes with a proper map between native cotangent lifts. -/
theorem equivariantCotangentKZeroRestrict_pullback
    (φ : H →ₜ* G) (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, VG) ∞ φ)
    {m : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G N] :
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    letI : MulAction H N := MulAction.compHom N φ.toMonoidHom
    letI : ContinuousSMul H N := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N :=
      MulAction.contMDiffSMul_compHom hφ
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := m) (G := G) (M := N) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := m) (G := G) (M := N) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
    letI := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
    ∀ (f : C(CotangentTotalSpace (n := m) (M := N),
        CotangentTotalSpace (n := n) (M := M)))
      (hfG : ∀ (g : G) (y : CotangentTotalSpace (n := m) (M := N)), f (g • y) = g • f y)
      (hfH : ∀ (h : H) (y : CotangentTotalSpace (n := m) (M := N)), f (h • y) = h • f y)
      (hf : IsProperMap f),
      (equivariantCotangentKZeroRestrict (n := m) (M := N) φ hφ).comp
        (equivariantSupportTripleKZeroPullback f hfG hf) =
      (equivariantSupportTripleKZeroPullback f hfH hf).comp
        (equivariantCotangentKZeroRestrict (n := n) (M := M) φ hφ) := by
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
  let : MulAction H N := MulAction.compHom N φ.toMonoidHom
  let : ContinuousSMul H N := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N :=
      MulAction.contMDiffSMul_compHom hφ
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := m) (G := G) (M := N) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := m) (G := G) (M := N) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
  let := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
  intro f hfG hfH hf
  -- Compare the native lifts on both bases using their actual base diffeomorphisms.
  let AM := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let CM : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) := inferInstance
  let RM : MulAction H (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.compHom (CotangentTotalSpace (n := n) (M := M)) φ.toMonoidHom
  let DM : letI := RM; ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom φ.continuous
  have hLiftM : AM = RM := by
    apply MulAction.ext
    funext h z
    have he : Diffeomorph.smul (M := M) 𝓘(ℝ, VH)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h =
        Diffeomorph.smul (M := M) 𝓘(ℝ, VG)
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (φ h) := by
      apply Diffeomorph.ext
      intro x
      rfl
    exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) he
  have hmapM : equivariantCotangentKZeroRestrict (n := n) (M := M) φ hφ =
      (kActionTransport RM AM DM CM hLiftM.symm).comp
        (equivariantSupportTripleKZeroRestrict
          (X := CotangentTotalSpace (n := n) (M := M)) φ) := by
    unfold equivariantCotangentKZeroRestrict
    exact transport_hom_eq_comp RM AM DM CM hLiftM.symm _
  let AN := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let CN : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) := inferInstance
  let RN : MulAction H (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.compHom (CotangentTotalSpace (n := m) (M := N)) φ.toMonoidHom
  let DN : letI := RN; ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.continuousSMul_compHom φ.continuous
  have hLiftN : AN = RN := by
    apply MulAction.ext
    funext h z
    have he : Diffeomorph.smul (M := N) 𝓘(ℝ, VH)
        𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ h =
        Diffeomorph.smul (M := N) 𝓘(ℝ, VG)
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (φ h) := by
      apply Diffeomorph.ext
      intro x
      rfl
    exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) he
  have hmapN : equivariantCotangentKZeroRestrict (n := m) (M := N) φ hφ =
      (kActionTransport RN AN DN CN hLiftN.symm).comp
        (equivariantSupportTripleKZeroRestrict
          (X := CotangentTotalSpace (n := m) (M := N)) φ) := by
    unfold equivariantCotangentKZeroRestrict
    exact transport_hom_eq_comp RN AN DN CN hLiftN.symm _
  -- The original raw restriction square and transport square use exactly the same pullback.
  have hraw := equivariantSupportTripleKZeroRestrict_pullback φ f hfG hf
  have htransport := kActionTransport_pullback RM AM RN AN DM CM DN CN
    hLiftM.symm hLiftN.symm f (fun h y ↦ hfG (φ h) y) hfH hf
  rw [hmapM, hmapN]
  apply AddMonoidHom.ext
  intro x
  have hrawx := DFunLike.congr_fun hraw x
  have htransportx := DFunLike.congr_fun htransport
    (equivariantSupportTripleKZeroRestrict
      (X := CotangentTotalSpace (n := n) (M := M)) φ x)
  simp only [AddMonoidHom.comp_apply] at hrawx htransportx ⊢
  exact (congrArg (kActionTransport RN AN DN CN hLiftN.symm) hrawx).trans htransportx

variable [FiniteDimensional ℝ VG] [FiniteDimensional ℝ VH]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option maxHeartbeats 1600000 in
-- Assemble both native group actions over the same variable-rank finite clopen family.
/-- Restriction of the group commutes with the full index on every original cotangent K class. -/
theorem representationRestriction_equivariantAnalyticIndexMap (φ : H →ₜ* G)
    (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, VG) ∞ φ) :
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    (representationRestriction φ).comp
        (equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G)) =
      (equivariantAnalyticIndexMap (n := n) (M := M) (VG := VH) (G := H)).comp
        (equivariantCotangentKZeroRestrict (n := n) (M := M) φ hφ) := by
  classical
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := M) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  apply AddMonoidHom.ext
  intro x
  -- Use the same invariant clopen pieces, bundles and symbols after restricting the group.
  obtain ⟨b, hb⟩ := exists_equivariantClopenSymbolFamily
    (n := n) (M := M) (VG := VG) x
  let P := b.partition
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (n := n) (VG := VG)
  let := P.compactSpace
  let Q : EquivariantClopenPartition (G := H) (M := M) := {
    size := P.size
    piece := P.piece
    isClosed := P.isClosed
    disjoint := P.disjoint
    cover := P.cover
    invariant := fun i h y ↦ P.invariant i (φ h) y
    mulAction := fun i ↦ MulAction.compHom (P.piece i) φ.toMonoidHom
    equivariant := fun i h y ↦ P.equivariant i (φ h) y }
  let := Q.mulAction
  let := Q.continuousSMul
  let := Q.contMDiffSMul (n := n) (VG := VH)
  let c : EquivariantClopenSymbolFamily (n := n) (M := M) (VG := VH) (G := H) :=
    ⟨Q, fun i ↦ (b.symbols i).restrict φ hφ⟩
  let ΦG := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) P.piece P.isClosed
    P.equivariant P.disjoint P.cover
  let ΦH := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VH) Q.piece Q.isClosed
    Q.equivariant Q.disjoint Q.cover
  have hfamily : c.kClass = equivariantCotangentKZeroRestrict φ hφ b.kClass := by
    apply ΦH.injective
    funext i
    let f : C(CotangentTotalSpace (n := n) (M := P.piece i),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion (P.piece i),
        (isOpenEmbedding_cotangentOpenInclusion (P.piece i)).continuous⟩
    have hf : IsProperMap f :=
      isProperMap_cotangentOpenInclusion (P.piece i) (P.isClosed i)
    let := smoothCotangentMulAction (n := n) (G := G) (M := P.piece i) 𝓘(ℝ, VG)
    let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := P.piece i) 𝓘(ℝ, VG)
    let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let := smoothCotangentMulAction (n := n) (G := H) (M := Q.piece i) 𝓘(ℝ, VH)
    let := contMDiffSMul_smoothCotangent (n := n) (G := H) (M := Q.piece i) 𝓘(ℝ, VH)
    let : ContinuousSMul H (CotangentTotalSpace (n := n) (M := Q.piece i)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    have hfG : ∀ (g : G) y, f (g • y) = g • f y :=
      cotangentOpenInclusion_smul 𝓘(ℝ, VG) (P.piece i) (P.equivariant i)
    have hfH : ∀ (h : H) y, f (h • y) = h • f y :=
      cotangentOpenInclusion_smul 𝓘(ℝ, VH) (Q.piece i) (Q.equivariant i)
    have hG : (b.symbols i).kClass = equivariantSupportTripleKZeroPullback f hfG hf
        b.kClass := by
      change (b.symbols i).kClass = ΦG (ΦG.symm (fun j ↦ (b.symbols j).kClass)) i
      rw [ΦG.apply_symm_apply]
    have hH : ΦH c.kClass i = (c.symbols i).kClass := by
      change ΦH (ΦH.symm (fun j ↦ (c.symbols j).kClass)) i = (c.symbols i).kClass
      rw [ΦH.apply_symm_apply]
    -- The original restriction map commutes with these very same proper cotangent inclusions.
    have hsquare := DFunLike.congr_fun
      (equivariantCotangentKZeroRestrict_pullback φ hφ f hfG hfH hf) b.kClass
    simp only [AddMonoidHom.comp_apply] at hsquare
    rw [← hG, EquivariantEllipticSymbolData.kClass_restrict] at hsquare
    exact hH.trans hsquare
  have hG := equivariantAnalyticIndexMap_clopen (n := n) (M := M) (VG := VG) (G := G)
    P.size P.piece P.isClosed P.disjoint P.cover P.mulAction P.continuousSMul
    (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
    (fun i ↦ (b.symbols i).source) (fun i ↦ (b.symbols i).target)
    (fun i ↦ (b.symbols i).sourceAction) (fun i ↦ (b.symbols i).targetAction)
    (fun i ↦ (b.symbols i).source_smooth) (fun i ↦ (b.symbols i).target_smooth)
    (fun i ↦ (b.symbols i).symbol) (fun i ↦ (b.symbols i).elliptic)
    (fun i ↦ (b.symbols i).equivariant)
  have hH := equivariantAnalyticIndexMap_clopen (n := n) (M := M) (VG := VH) (G := H)
    Q.size Q.piece Q.isClosed Q.disjoint Q.cover Q.mulAction Q.continuousSMul
    (Q.contMDiffSMul (n := n) (VG := VH)) Q.equivariant Q.compactSpace
    (fun i ↦ (c.symbols i).source) (fun i ↦ (c.symbols i).target)
    (fun i ↦ (c.symbols i).sourceAction) (fun i ↦ (c.symbols i).targetAction)
    (fun i ↦ (c.symbols i).source_smooth) (fun i ↦ (c.symbols i).target_smooth)
    (fun i ↦ (c.symbols i).symbol) (fun i ↦ (c.symbols i).elliptic)
    (fun i ↦ (c.symbols i).equivariant)
  change equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) b.kClass = b.index at hG
  change equivariantAnalyticIndexMap (n := n) (VG := VH) (G := H) c.kClass = c.index at hH
  change representationRestriction φ
      (equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) x) =
    equivariantAnalyticIndexMap (n := n) (VG := VH) (G := H)
      (equivariantCotangentKZeroRestrict φ hφ x)
  rw [← hb, hG, ← hfamily, hH]
  change representationRestriction φ (∑ i, (b.symbols i).index) =
    ∑ i, ((b.symbols i).restrict φ hφ).index
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- Each same realization restricts its actual kernel and quotient-cokernel representations.
  exact (b.symbols i).index_restrict φ hφ

end AtiyahSinger
