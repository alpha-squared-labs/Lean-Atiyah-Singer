/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothRiemannianMetric
public import AtiyahSinger.Geometry.TangentCharacteristicClasses
public import AtiyahSinger.Topology.BundleCompactSupportCharacter
public import AtiyahSinger.Topology.BundleSphereCohomologyComparison
public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.CompactSupportCohomologyHomeomorph
public import AtiyahSinger.Topology.ComplexBundleCohomologyVanishing
public import AtiyahSinger.Topology.ComplexificationPullbackTopology
public import AtiyahSinger.Topology.ComplexifiedNormalPullback
public import AtiyahSinger.Topology.HermitianSupportedThom
public import AtiyahSinger.Topology.InverseTodd
public import AtiyahSinger.Topology.SupportedComplexCohomologyThom
public import AtiyahSinger.Topology.SupportedThomCharacterCompactification

/-!
# The supported Thom character on the original normal pullback over TM

Public module ID: M2211.

C04 / T02. Lawson--Michelsohn, Spin Geometry, p.255, explicitly extends
(12.9) to K_c(TX) before (13.20), although TX is noncompact. The input here
is that original supported class, and the Thom operator is exactly the one
used by tangentEmbeddingPushforwardWith. The cohomological integral uses
the same complex bundle, Hermitian metric and canonical complex orientation.

The one-point comparison is asserted only for the actual complexified normal
pullback of an immersion of compact M into Euclidean space. Its total space
is homeomorphic to the real bundle TM plus two copies of the original normal
bundle over compact M. This geometry supplies compact disks and the radial
contraction at infinity. No comparison for arbitrary locally compact spaces
is assumed, and no compactness of TM or properness of its projection is used.

Sources: SG III.12, (12.9)--(12.11), pp.241--242, and III.13, p.255 before
(13.20). The singular-support comparison is the project supplement already
used in BundleCompactSupportCharacter, transported along the original
real/imaginary identification. The sign (-1)^(r+j-i) retains SG's exterior
symbol convention; ordinary inverse Todd acts on the supported base character.
Rank zero and the empty base are included. The fiber-integral formula uses the actual
fiberwise sphere compactification and the same supported open-extension maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle Topology
open scoped Bundle ContDiff Manifold TensorProduct

set_option maxSynthPendingDepth 30


attribute [local instance 2000] NormedField.toNormedCommRing Real.normedCommRing

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {n N : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "W" => EuclideanSpace ℝ (Fin N)
local notation "TM" => TangentBundle 𝓘(ℝ, V) M

variable (f : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) M (EuclideanSpace ℝ (Fin N)) ∞)
  (hf : Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)

set_option maxHeartbeats 600000 in
-- Normalize the original double normal atlas and its one-point cohomology comparison.
/-- The actual one-point comparison for the double normal total space over compact M. -/
theorem compactSupportCohomologyToOnePoint_normal_bijective
    (R : Type) [CommRing R] (k : ℕ) :
    letI := isFiniteRank_complexifiedNormalPullback f hf
    Function.Bijective
      (compactSupportCohomologyToOnePoint R
        (TotalSpace Unit (ComplexifiedNormalPullback f)) k) := by
  /- Stage 1: use the original normal atlas supplied by hf. The actual
  complexificationDoubleTotalHomeomorph separates real and imaginary
  normal vectors over each z=(x,v) in TM. Reassociate the two pullbacks
  to identify the total space with the real bundle TM + normal + normal
  over the original compact Hausdorff M. All original total topologies
  and vectors are retained; no tangent-normal splitting is required.
  Stage 2: choose a continuous metric on this finite-rank real bundle
  over compact M. Its closed disks are compact and cofinal among compact
  supports. Outside a positive disk, radial expansion contracts the
  infinity neighborhood to the same singleton infinity, including joint
  continuity at time one. This is exactly the geometric argument of
  compactSupportCohomologyToOnePoint_bundle_bijective. If the entire real
  sum has rank zero, its total space is compact and infinity is isolated;
  zero normal rank alone still leaves the tangent factor.
  Stage 3: excision and the relative long exact sequence identify that
  comparison with an isomorphism. Transport the actual support colimit
  and relative pair through the above homeomorphism and its onePointCongr,
  using compactSupportCohomologyHomeomorphPullback_toOnePoint. This proves
  bijectivity of the displayed map itself, not an unspecified equivalence.
  The comparison needs only compact M; its TM base may be noncompact. -/
  classical
  let := isFiniteRank_complexifiedNormalPullback f hf
  let T := TangentSpace 𝓘(ℝ, V) (M := M)
  let ν := NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f
  let Q := NormalModel V W
  let p : C(TM, M) := ⟨π V T, FiberBundle.continuous_proj V T⟩
  let P := (p : TM → M) *ᵖ ν
  let : ∀ z, AddCommGroup (P z) := fun z ↦ inferInstanceAs (AddCommGroup (ν (p z)))
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := FiberBundle.pullback (F := Q) (E := ν) p
  let := VectorBundle.pullback (𝕜 := ℝ) (F := Q) (E := ν) p
  let S := T ×ᵇ (ν ×ᵇ ν)
  let F := V × (Q × Q)
  let A := TotalSpace F S
  let D := TotalSpace (Q × Q) (P ×ᵇ P)
  let Y := TotalSpace Unit (ComplexifiedNormalPullback f)
  -- Reassociate only the base point and the original three real vectors.
  let a : D ≃ₜ A :=
    { toFun := fun z ↦ ⟨z.proj.proj, z.proj.snd, z.snd.1, z.snd.2⟩
      invFun := fun z ↦ ⟨⟨z.proj, z.snd.1⟩, z.snd.2.1, z.snd.2.2⟩
      left_inv := by rintro ⟨⟨x, v⟩, u, w⟩; rfl
      right_inv := by rintro ⟨x, v, u, w⟩; rfl
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag Q P Q P).continuous
        have hT := (Pullback.continuous_proj Q ν p).comp hd.fst
        have h₁ := (Pullback.continuous_lift Q ν p).comp hd.fst
        have h₂ := (Pullback.continuous_lift Q ν p).comp hd.snd
        apply (FiberBundle.Prod.isInducing_diag V T (Q × Q) (ν ×ᵇ ν)).continuous_iff.mpr
        exact hT.prodMk ((FiberBundle.Prod.isInducing_diag Q ν Q ν).continuous_iff.mpr
          (h₁.prodMk h₂))
      continuous_invFun := by
        have ha := (FiberBundle.Prod.isInducing_diag V T (Q × Q) (ν ×ᵇ ν)).continuous
        have hν := (FiberBundle.Prod.isInducing_diag Q ν Q ν).continuous.comp ha.snd
        apply (FiberBundle.Prod.isInducing_diag Q P Q P).continuous_iff.mpr
        exact ((inducing_pullbackTotalSpaceEmbedding Q ν p).continuous_iff.mpr
          (ha.fst.prodMk hν.fst)).prodMk
            ((inducing_pullbackTotalSpaceEmbedding Q ν p).continuous_iff.mpr
              (ha.fst.prodMk hν.snd)) }
  let d : Y ≃ₜ D := complexificationDoubleTotalHomeomorph Q P
  let e : A ≃ₜ Y := (d.trans a).symm
  -- A native smooth metric exists on this same real bundle over the compact base.
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (EB := V) F S
  let : RiemannianBundle S := ⟨g.toRiemannianMetric⟩
  let : ∀ x, NormedAddCommGroup (S x) := fun x ↦ inferInstance
  let : ∀ x, InnerProductSpace ℝ (S x) := fun x ↦ inferInstance
  let : IsContinuousRiemannianBundle F S :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : T2Space A := t2Space_fiberBundleTotal F S
  let : LocallyCompactSpace A := locallyCompactSpace_fiberBundleTotal F S
  have hnative : Function.Bijective (compactSupportCohomologyToOnePoint R A k) := by
    -- The original metric-disk proof works with this finite-dimensional native model F.
    apply compactSupportCohomologyToOnePoint_bijective_of_contractible_complements R
    intro K
    have hnorm : Continuous (fun v : A ↦ ‖v.snd‖) :=
      Poincare.VectorBundle.continuous_fiber_norm
    obtain ⟨b, hb⟩ := K.isCompact.bddAbove_image hnorm.continuousOn
    let t : ℝ := max b 1
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hdisk : IsCompact {v : A | ‖v.snd‖ ≤ t} := by
      simpa using Poincare.VectorBundle.isCompact_disk_over
        (F := F) (E := S) (K := Set.univ) isCompact_univ t
    refine ⟨⟨{v | ‖v.snd‖ ≤ t}, hdisk⟩, ?_, ?_⟩
    · intro v hv
      exact (hb (Set.mem_image_of_mem _ hv)).trans (le_max_left _ _)
    · exact contractibleSpace_bundleInfinityNeighborhood F S t ht
  let p := compactSupportCohomologyHomeomorphPullback R e k
  have hp : Function.Bijective p := compactSupportCohomologyHomeomorphPullback_bijective R e k
  -- The extended homeomorphism is an isomorphism on both members of the singleton pair.
  let eInf := e.onePointCongr
  let f : C(OnePoint A, OnePoint Y) := ⟨eInf, eInf.continuous⟩
  have hf : Set.MapsTo f ({OnePoint.infty} : Set (OnePoint A))
      ({OnePoint.infty} : Set (OnePoint Y)) := by
    rintro z rfl
    rfl
  let es : ({OnePoint.infty} : Set (OnePoint A)) ≃ₜ ({OnePoint.infty} : Set (OnePoint Y)) :=
    eInf.subtype (fun z ↦ by
      change z = OnePoint.infty ↔ eInf z = OnePoint.infty
      constructor
      · rintro rfl
        rfl
      · intro hz
        exact eInf.injective (hz.trans (show eInf OnePoint.infty = OnePoint.infty from rfl).symm))
  have : IsIso (TopCat.ofHom f) := by
    change IsIso (TopCat.isoOfHomeo
      (X := TopCat.of (OnePoint A)) (Y := TopCat.of (OnePoint Y)) eInf).hom
    infer_instance
  have : IsIso (TopCat.ofHom (⟨es, es.continuous⟩ : C(_, _))) := by
    change IsIso (TopCat.isoOfHomeo
      (X := TopCat.of ({OnePoint.infty} : Set (OnePoint A)))
      (Y := TopCat.of ({OnePoint.infty} : Set (OnePoint Y))) es).hom
    infer_instance
  have : IsIso (relativeSingularChainsMap R f hf) := by
    change IsIso (Limits.cokernel.map _ _
      ((singularChainsFunctor R).map (TopCat.ofHom (⟨es, es.continuous⟩ : C(_, _))))
      ((singularChainsFunctor R).map (TopCat.ofHom f)) (by
        simp only [singularSubspaceChains, ← CategoryTheory.Functor.map_comp]
        rfl))
    infer_instance
  let q := relativeSingularCohomologyPullback R f hf k
  have : IsIso q := by
    change IsIso ((singularCochainDualFunctor R ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) k).map
        (relativeSingularChainsMap R f hf).op)
    infer_instance
  have hq : Function.Bijective q := (ConcreteCategory.isIso_iff_bijective q).mp inferInstance
  have hsquare (a : compactSupportCohomology R Y k) :
      compactSupportCohomologyToOnePoint R A k (p a) =
        q (compactSupportCohomologyToOnePoint R Y k a) :=
    compactSupportCohomologyHomeomorphPullback_toOnePoint R e k a
  -- Transport bijectivity through this actual comparison square.
  constructor
  · intro a b hab
    apply hp.injective
    apply hnative.injective
    exact (hsquare a).trans ((congrArg q hab).trans (hsquare b).symm)
  · intro b
    obtain ⟨x, hx⟩ := hnative.surjective (q b)
    obtain ⟨a, ha⟩ := hp.surjective x
    refine ⟨a, hq.injective ?_⟩
    exact (hsquare a).symm.trans ((congrArg _ ha).trans hx)


/-- The original reduced character lifted by the exact normal-total comparison. -/
def normalCompactSupportChernCharacterComponent (k : ℕ) :
    letI := isFiniteRank_complexifiedNormalPullback f hf
    CompactSupportKZero (TotalSpace Unit (ComplexifiedNormalPullback f)) →+
      compactSupportCohomology ℚ (TotalSpace Unit (ComplexifiedNormalPullback f)) (2 * k) := by
  letI := isFiniteRank_complexifiedNormalPullback f hf
  -- Invert the independently specified comparison, not the desired Thom-character formula.
  exact (LinearEquiv.ofBijective
    (compactSupportCohomologyToOnePoint ℚ
      (TotalSpace Unit (ComplexifiedNormalPullback f)) (2 * k)).hom
    (compactSupportCohomologyToOnePoint_normal_bijective f hf ℚ (2 * k))).symm.toAddMonoidHom.comp
      (reducedChernCharacterComponent
        (OnePoint.infty : OnePoint (TotalSpace Unit (ComplexifiedNormalPullback f))) k)

/-- The normal-total supported character maps to the reduced character of the same K class. -/
theorem normalCompactSupportChernCharacterComponent_toOnePoint (k : ℕ) :
    letI := isFiniteRank_complexifiedNormalPullback f hf
    ∀ a : CompactSupportKZero (TotalSpace Unit (ComplexifiedNormalPullback f)),
      compactSupportCohomologyToOnePoint ℚ
          (TotalSpace Unit (ComplexifiedNormalPullback f)) (2 * k)
          (normalCompactSupportChernCharacterComponent f hf k a) =
        reducedChernCharacterComponent
          (OnePoint.infty : OnePoint (TotalSpace Unit (ComplexifiedNormalPullback f))) k a := by
  /- Apply the forward map of the very LinearEquiv used in the definition
  to its inverse. The cancellation leaves the original reduced class a,
  on the same one-point pair and in the same degree. The independent
  comparison theorem, rather than a Thom formula premise, supplies the inverse. -/
  let := isFiniteRank_complexifiedNormalPullback f hf
  intro a
  let e := LinearEquiv.ofBijective
    (compactSupportCohomologyToOnePoint ℚ
      (TotalSpace Unit (ComplexifiedNormalPullback f)) (2 * k)).hom
    (compactSupportCohomologyToOnePoint_normal_bijective f hf ℚ (2 * k))
  exact e.apply_symm_apply _

/-- The supported normal Thom character has no component below its complex Thom rank. -/
theorem normalCompactSupportChernCharacter_supportedThom_eq_zero_of_lt
    (h : ContinuousHermitianMetric (ComplexifiedNormalPullback f)) (r : ℕ)
    (hr : ∀ z : TM, Module.finrank ℂ (ComplexifiedNormalPullback f z) = r)
    (u : CompactSupportKZero TM) (k : ℕ) (hk : k < r) :
    letI := isFiniteRank_complexifiedNormalPullback f hf
    normalCompactSupportChernCharacterComponent f hf k (h.supportedThomHom u) = 0 := by
  /- Retain the original normal pullback, metric and rank certificate.
  The native real model has rank 2*r and its complex orientation gives
  vanishing compact-support cohomology below that rank, also over the
  noncompact Hausdorff tangent base. Transport by the actual total-space
  homeomorphism makes the target group a subsingleton. Thus the original
  supported character is zero without any forget-support inference. -/
  let := isFiniteRank_complexifiedNormalPullback f hf
  let := h.compactSupportCohomology_subsingleton_below_complex_rank r hr (2 * k)
    (by omega)
  exact Subsingleton.elim _ _

/-- SG p.255: (12.9)--(12.11) for the original K_c(TM) coefficients of the normal Thom map. -/
theorem supportedIntegral_normalChernCharacter_supportedThom
    (g : SmoothTangentMetric (n := n) (M := M))
    (h : ContinuousHermitianMetric (ComplexifiedNormalPullback f)) (r : ℕ)
    (hr : ∀ z : TM, Module.finrank ℂ (ComplexifiedNormalPullback f z) = r)
    (u : CompactSupportKZero TM) (j : ℕ) :
    letI := isFiniteRank_complexifiedNormalPullback f hf
    h.supportedComplexCohomologyThomIntegral r hr (2 * j)
        ((eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace Unit (ComplexifiedNormalPullback f))
                (2 * (r + j)) ≅
              compactSupportCohomology ℚ (TotalSpace Unit (ComplexifiedNormalPullback f))
                (2 * j + 2 * r)).hom
          (normalCompactSupportChernCharacterComponent f hf (r + j)
            (h.supportedThomHom u))) =
      ∑ i : Fin (j + 1),
        (-1 : ℚ) ^ (r + (j - i.val)) •
          (eqToIso (by congr 1; omega) :
              compactSupportCohomology ℚ TM (2 * (j - i.val) + 2 * i.val) ≅
                compactSupportCohomology ℚ TM (2 * j)).hom
            (compactSupportCohomologyAction ℚ TM (2 * (j - i.val)) (2 * i.val)
              (inverseToddClassComponent (ComplexifiedNormalPullback f) h (j - i.val))
              (g.tangentCompactSupportChernCharacterComponent i.val u)) := by
  /- Extend the original normal bundle over the actual fiberwise sphere of TM.
  The sphere's infinity section has a retraction, and its cofinal disk complements
  retract onto that section. Thus its ordinary cohomology detects the original
  base compact-support classes. Open-extension naturality compares the original
  K-Thom symbol, supported character and specified cohomological inverse before
  the compact-base formula is pulled back through this genuine detector. -/
  classical
  let := isFiniteRank_complexifiedNormalPullback f hf
  let T := TangentSpace 𝓘(ℝ, V) (M := M)
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, V) ∞ V T :=
    ⟨⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩⟩
  let S := SphereCompactification n T
  let : CompactSpace S := compactSpace_sphereCompactification (EB := V) n T
  let : T2Space S := inferInstance
  let p : C(TM, M) := ⟨π V T, FiberBundle.continuous_proj V T⟩
  let pS : C(S, M) := sphereCompactificationProjection n T
  let i : C(TM, S) := sphereCompactificationInclusion (EB := V) n T
  have hi : IsOpenEmbedding i := isOpenEmbedding_sphereCompactificationInclusion (EB := V) n T
  have hproj : pS.comp i = p := by
    let := orthogonalFrameTopology n T
    let := continuousSMul_orthogonalSphere n
    let := continuousSMul_orthogonalFrame n T 𝓘(ℝ, V)
    let atlas := smoothOrthogonalFrameAtlas n T 𝓘(ℝ, V)
    let := associatedSphereChartedSpace atlas
    apply ContinuousMap.ext
    intro z
    exact congrArg (fun w : TotalSpace V T × ℝ ↦ w.1.proj)
      ((frameSphereStereographic_spec (EB := V) n T).2.2.2.1 z)
  -- The extended fibers are the same tensor complexification of the original normal vectors.
  let ν := NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f
  let Q := NormalModel V W
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := FiberBundle.pullback (F := Q) (E := ν) p
  let := VectorBundle.pullback (𝕜 := ℝ) (F := Q) (E := ν) p
  let C : M → Type := fun x ↦ ℂ ⊗[ℝ] ν x
  let := complexificationTopology Q ν
  let : IsFiniteRank C := isFiniteRank_complexification Q ν
  let Fbar := (pS : S → M) *ᵖ C
  let := isFiniteRank_pullback (E := C) pS
  let hbar : ContinuousHermitianMetric Fbar := (nonempty_continuousHermitianMetric Fbar).some
  have hrbar (z : S) : Module.finrank ℂ (Fbar z) = r := hr (⟨pS z, 0⟩ : TM)
  let PC := (p : TM → M) *ᵖ C
  have htop : complexificationTopology Q ((p : TM → M) *ᵖ ν) =
      (inferInstance : TopologicalSpace (TotalSpace Unit PC)) :=
    complexificationTopology_pullback Q ν p
  let e₀ : ComplexBundle.Iso (ComplexifiedNormalPullback f) PC := by
    change @ComplexBundle.Iso TM (ComplexifiedNormalPullback f) PC _ _ _ _
      (complexificationTopology Q ((p : TM → M) *ᵖ ν)) _
    rw [htop]
    exact ComplexBundle.Iso.refl PC
  have hmapIso (a b : C(TM, M)) (hab : a = b) :
      ComplexBundle.Iso ((a : TM → M) *ᵖ C) ((b : TM → M) *ᵖ C) := by
    subst b
    exact ComplexBundle.Iso.refl _
  let e : ComplexBundle.Iso (ComplexifiedNormalPullback f) ((i : TM → S) *ᵖ Fbar) :=
    e₀.trans ((hmapIso p (pS.comp i) hproj.symm).trans (pullbackCompIso (E := C) pS i).symm)
  -- This detector is proved from the same original sphere, not from forgetting a disk boundary.
  have hdetect : Function.Injective (fun a : compactSupportCohomology ℚ TM (2 * j) ↦
      compactSupportCohomologyToOrdinary ℚ S (2 * j)
        (compactSupportCohomologyOpenExtension ℚ i hi (2 * j) a)) := by
    intro a b hab
    apply compactSupportCohomologyToSphere_toOrdinary_injective (EB := V) n T ℚ (2 * j)
    exact (compactSupportCohomologyToCompactification_toOrdinary ℚ i hi (2 * j) a).trans
      (hab.trans (compactSupportCohomologyToCompactification_toOrdinary ℚ i hi (2 * j) b).symm)
  exact h.supportedIntegral_chernCharacter_of_compactification hbar r hr hrbar i hi e
    (fun k ↦ g.tangentCompactSupportChernCharacterComponent k)
    (fun k ↦ normalCompactSupportChernCharacterComponent f hf k)
    (fun k a ↦ g.tangentCompactSupportChernCharacterComponent_toOnePoint k a)
    (fun k a ↦ normalCompactSupportChernCharacterComponent_toOnePoint f hf k a) u j hdetect

end AtiyahSinger
