/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleComplement
public import AtiyahSinger.Topology.KZeroStabilization
public import AtiyahSinger.Topology.ProjectiveKZero

/-!
# Geometric bundle classes in the existing algebraic model of K⁰

Public module ID: M1588.

D07/K01/KB01. A class is the class of an actual idempotent presentation of E.
Independence, direct sum, pullback and actual homotopy invariance are proved below.
The stable-isomorphism characterization uses the effective common-summand criterion.
SG I.9.1 and I.9.7-9.9 supply the geometric group-completion and complement route;
Serre-Swan compares it to the existing quotient of finite idempotent matrices.
Relative triples, compact supports, ring products and graded groups are not added here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

attribute [local instance] sectionModule
attribute [local instance] IdempotentMatrix.fiberTotalSpaceTopology
attribute [local instance] IdempotentMatrix.isFiniteRank_fiber
attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial
attribute [local instance] isFiniteRank_pullback

variable [IsFiniteRank E] [IsFiniteRank F] [CompactSpace X] [T2Space X]

/-- The K⁰ class of the given continuous finite-rank complex bundle. -/
def kZeroClass (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] : ComplexKZero X :=
  AtiyahSinger.kZeroClass C(X, ℂ) (idempotentPresentation (E := E))

/-- Any actual image-bundle presentation computes the same geometric class. -/
theorem kZeroClass_eq_of_presentation (p : IdempotentMatrix C(X, ℂ))
    (e : Iso E (fun x ↦ p.fiber x)) :
    kZeroClass E = AtiyahSinger.kZeroClass C(X, ℂ) p := by
  /- Taking sections of e and of the chosen presentation identifies the two image
  modules. The existing rectangular-matrix equivalence theorem turns that module
  isomorphism into an equivalence of idempotents, whose classes agree in the quotient. -/
  -- Compare the same two image modules through their original bundle presentations.
  let q := idempotentPresentation (E := E)
  let a : q.image ≃ₗ[C(X, ℂ)] p.image :=
    q.imageSectionEquiv.trans ((presentationIso (E := E)).symm.sectionLinearEquiv.trans
      (e.sectionLinearEquiv.trans p.imageSectionEquiv.symm))
  exact AtiyahSinger.kZeroClass_eq_of_isEquivalent q p
    ((IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv q p).mpr ⟨a⟩)

/-- Isomorphic continuous bundles have equal K⁰ classes. -/
theorem kZeroClass_eq_of_iso (e : Iso E F) : kZeroClass E = kZeroClass F := by
  /- Compose e with the chosen image presentation of F. It is also a presentation
  of E. Independence of the presentation then identifies both geometric classes with
  the class of the same idempotent matrix. -/
  -- Present both bundles by the same chosen image of F.
  exact kZeroClass_eq_of_presentation (idempotentPresentation (E := F))
    (e.trans (presentationIso (E := F)))

/-- The class of the actual image bundle is the original matrix class. -/
theorem kZeroClass_image (p : IdempotentMatrix C(X, ℂ)) :
    kZeroClass (fun x ↦ p.fiber x) = AtiyahSinger.kZeroClass C(X, ℂ) p := by
  /- The identity bundle isomorphism exhibits p itself as a presentation of its
  image bundle. Apply the presentation-independence theorem to that actual identity map. -/
  exact kZeroClass_eq_of_presentation p (Iso.refl _)

/-- The class of a trivial rank-n bundle is the class of the identity idempotent. -/
theorem kZeroClass_trivial (n : ℕ) :
    kZeroClass (Bundle.Trivial X (Fin n → ℂ)) =
      AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) n) := by
  /- The image of the identity matrix is the entire finite coordinate space.
  Its subspace total topology agrees with the trivial product topology. The identity
  coordinates therefore give a bundle presentation by this identity idempotent. -/
  -- The specified identity image is the whole free module, also when n = 0.
  let p := IdempotentMatrix.identity C(X, ℂ) n
  have hp : p.image = ⊤ := by
    change (Matrix.mulVecLin (1 : Matrix (Fin n) (Fin n) C(X, ℂ))).range = ⊤
    rw [Matrix.mulVecLin_one, LinearMap.range_id]
  let a := (trivialSectionEquiv (X := X) n).symm.trans
    ((LinearEquiv.ofTop p.image hp).symm.trans p.imageSectionEquiv)
  exact kZeroClass_eq_of_presentation p (isoOfSectionEquiv a)

/-- Direct sum of actual bundles becomes addition in the existing quotient. -/
theorem kZeroClass_sum : kZeroClass (E ×ᵇ F) = kZeroClass E + kZeroClass F := by
  /- The chosen presentations identify the geometric classes of E,
  F and E⊕F with their projective section-module classes. The original
  sumSectionEquiv identifies sections of E⊕F with the product of the two
  section modules. Projective-class invariance and product additivity then
  give the displayed geometric direct-sum formula. -/
  let := finite_continuousSections E
  let := projective_continuousSections E
  let := finite_continuousSections F
  let := projective_continuousSections F
  let := finite_continuousSections (E ×ᵇ F)
  let := projective_continuousSections (E ×ᵇ F)
  -- Compare the three specified presentations with their actual section modules.
  have hE : kZeroClass E = projectiveModuleKZeroClass C(X, ℂ) (continuousSections E) := by
    let p := idempotentPresentation (E := E)
    let := p.finite_image
    let := p.projective_image
    obtain ⟨e⟩ := presentation_sections (E := E)
    exact (projectiveModuleKZeroClass_image p).symm.trans
      (projectiveModuleKZeroClass_eq_of_linearEquiv e.symm)
  have hF : kZeroClass F = projectiveModuleKZeroClass C(X, ℂ) (continuousSections F) := by
    let p := idempotentPresentation (E := F)
    let := p.finite_image
    let := p.projective_image
    obtain ⟨e⟩ := presentation_sections (E := F)
    exact (projectiveModuleKZeroClass_image p).symm.trans
      (projectiveModuleKZeroClass_eq_of_linearEquiv e.symm)
  have hEF : kZeroClass (E ×ᵇ F) =
      projectiveModuleKZeroClass C(X, ℂ) (continuousSections (E ×ᵇ F)) := by
    let p := idempotentPresentation (E := E ×ᵇ F)
    let := p.finite_image
    let := p.projective_image
    obtain ⟨e⟩ := presentation_sections (E := E ×ᵇ F)
    exact (projectiveModuleKZeroClass_image p).symm.trans
      (projectiveModuleKZeroClass_eq_of_linearEquiv e.symm)
  -- The actual section splitting is C(X,ℂ)-linear and uses the original sum topology.
  rw [hEF, hE, hF]
  exact (projectiveModuleKZeroClass_eq_of_linearEquiv
    (sumSectionEquiv (E := E) (F := F)).symm).trans
      (projectiveModuleKZeroClass_prod (continuousSections E) (continuousSections F))

/-- The zero-dimensional trivial bundle represents zero. -/
theorem kZeroClass_trivial_zero : kZeroClass (Bundle.Trivial X (Fin 0 → ℂ)) = 0 := by
  /- The zero-dimensional free module is its own direct sum with itself. Its
  generator therefore equals twice itself by the direct-sum relation, and cancellation
  in the quotient group gives zero. Apply the trivial-bundle class formula. -/
  rw [kZeroClass_trivial]
  let p := IdempotentMatrix.identity C(X, ℂ) 0
  have hblock : p.blockSum p = p := by
    dsimp only [IdempotentMatrix.blockSum, IdempotentMatrix.identity, p]
    congr 1
    ext i
    exact Fin.elim0 i
  have h := AtiyahSinger.kZeroClass_blockSum p p
  rw [hblock] at h
  exact add_left_cancel (show AtiyahSinger.kZeroClass C(X, ℂ) p +
      AtiyahSinger.kZeroClass C(X, ℂ) p = AtiyahSinger.kZeroClass C(X, ℂ) p + 0 by
    simpa only [add_zero] using h.symm)

/-- Complementary image bundles add to the ambient trivial-bundle class. -/
theorem kZeroClass_complement (p : IdempotentMatrix C(X, ℂ)) :
    kZeroClass (fun x ↦ p.fiber x) + kZeroClass (fun x ↦ p.complement.fiber x) =
      kZeroClass (Bundle.Trivial X (Fin p.size → ℂ)) := by
  /- First replace the sum of classes by the class of the direct-sum bundle.
  The concrete addition isomorphism p.complementIso identifies that bundle with the
  displayed trivial bundle. Isomorphism invariance gives the equality. -/
  rw [← kZeroClass_sum]
  exact kZeroClass_eq_of_iso p.complementIso

/-- The chosen complementary bundle supplies the geometric complement formula. -/
theorem kZeroClass_presentation_complement :
    kZeroClass E +
      kZeroClass (fun x ↦ (idempotentPresentation (E := E)).complement.fiber x) =
    kZeroClass (Bundle.Trivial X (Fin (idempotentPresentation (E := E)).size → ℂ)) := by
  /- Use the actual complement isomorphism of E constructed from its presentation.
  Direct-sum additivity and isomorphism invariance give the formula with precisely
  the same presentation size and complementary image bundle. -/
  rw [← kZeroClass_sum]
  exact kZeroClass_eq_of_iso (Classical.choice
    (nonempty_presentation_complement_iso (E := E)))

/-- Rank at a point of the geometric class is the dimension of the actual fiber. -/
theorem rankAt_kZeroClass (x : X) :
    complexKZeroRankAt x (kZeroClass E) = (Module.finrank ℂ (E x) : ℤ) := by
  /- Evaluation of the presentation matrix at x computes the rank of its image.
  The presentation bundle isomorphism identifies that image with E(x). Invariance of
  finite-dimensional rank gives the displayed value, without assuming connectedness. -/
  -- Evaluation computes the same image fiber as the chosen presentation.
  change kZeroRank ℂ (kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
    (AtiyahSinger.kZeroClass C(X, ℂ) (idempotentPresentation (E := E)))) = _
  rw [kZeroMap_class, kZeroRank_class]
  congr 1
  exact ((presentationIso (E := E)).linearEquiv x).finrank_eq.symm

/-- An isomorphism of section modules gives equal geometric classes. -/
theorem kZeroClass_eq_of_sectionEquiv
    (e : continuousSections E ≃ₗ[C(X, ℂ)] continuousSections F) :
    kZeroClass E = kZeroClass F := by
  /- Full faithfulness lifts e to an actual continuous bundle isomorphism.
  Its forward map is characterized on section values; isomorphism invariance of
  the geometric class then proves equality in the existing quotient. -/
  exact kZeroClass_eq_of_iso (isoOfSectionEquiv e)

/-- Equality of bundle classes is exactly stabilization by a common trivial bundle. -/
theorem kZeroClass_eq_iff_stable_iso :
    kZeroClass E = kZeroClass F ↔
      ∃ n : ℕ, Nonempty (Iso (E ×ᵇ Bundle.Trivial X (Fin n → ℂ))
        (F ×ᵇ Bundle.Trivial X (Fin n → ℂ))) := by
  /- The group-completion relation first gives a common finite projective summand.
  Realize it as a bundle via Serre-Swan and add its complement, turning that common
  summand into one finite trivial bundle. Conversely a stable isomorphism equates
  sums of classes, and cancellation removes the common trivial class. This is stable
  isomorphism, not an assertion that an unstabilized bundle isomorphism follows. -/
  constructor
  · intro h
    let p := idempotentPresentation (E := E)
    let q := idempotentPresentation (E := F)
    obtain ⟨r, ⟨e⟩⟩ := (AtiyahSinger.kZeroClass_eq_iff_exists_stable_image_equiv p q).mp h
    obtain ⟨eE⟩ := presentation_sections (E := E)
    obtain ⟨eF⟩ := presentation_sections (E := F)
    -- The actual complement of the same common summand gives one specified free module.
    let c : (r.image × r.complement.image) ≃ₗ[C(X, ℂ)] (Fin r.size → C(X, ℂ)) :=
      (r.imageSectionEquiv.prodCongr r.complement.imageSectionEquiv).trans
        ((sumSectionEquiv (E := fun x ↦ r.fiber x)
          (F := fun x ↦ r.complement.fiber x)).trans
            (r.complementIso.sectionLinearEquiv.trans (trivialSectionEquiv r.size).symm))
    -- Add that complement to both sides of the extracted, actual module equivalence.
    let a : (p.image × (Fin r.size → C(X, ℂ))) ≃ₗ[C(X, ℂ)]
        (q.image × (Fin r.size → C(X, ℂ))) :=
      ((LinearEquiv.refl C(X, ℂ) p.image).prodCongr c.symm).trans
        ((LinearEquiv.prodAssoc C(X, ℂ) p.image r.image r.complement.image).symm.trans
          ((e.prodCongr (LinearEquiv.refl C(X, ℂ) r.complement.image)).trans
            ((LinearEquiv.prodAssoc C(X, ℂ) q.image r.image r.complement.image).trans
              ((LinearEquiv.refl C(X, ℂ) q.image).prodCongr c))))
    let aE := (sumSectionEquiv (E := E)
      (F := Bundle.Trivial X (Fin r.size → ℂ))).symm.trans
        (eE.prodCongr (trivialSectionEquiv r.size).symm)
    let aF := (sumSectionEquiv (E := F)
      (F := Bundle.Trivial X (Fin r.size → ℂ))).symm.trans
        (eF.prodCongr (trivialSectionEquiv r.size).symm)
    -- Full faithfulness lifts this same stabilized section equivalence to the original bundles.
    exact ⟨r.size, ⟨isoOfSectionEquiv (aE.trans (a.trans aF.symm))⟩⟩
  · rintro ⟨n, ⟨e⟩⟩
    have h := kZeroClass_eq_of_iso e
    rw [kZeroClass_sum, kZeroClass_sum] at h
    exact add_right_cancel h

/-- Every element has the geometric form of an image bundle minus a trivial bundle. -/
theorem exists_class_sub_trivial (a : ComplexKZero X) :
    ∃ p : IdempotentMatrix C(X, ℂ), ∃ n : ℕ,
      a = kZeroClass (fun x ↦ p.fiber x) - kZeroClass (Bundle.Trivial X (Fin n → ℂ)) := by
  /- Use the quotient generators and block-sum relation to express a as [p]-[q].
  Add image(1-q) to both terms. The denominator becomes the trivial bundle of size
  q.size, while the numerator is the image of the block sum p ⊕ (1-q). This is the
  image-bundle realization of SG I.9.7 and the final assertion of I.9.9. -/
  -- The original block relation supplies addition of image and trivial classes.
  have hblock (p q : IdempotentMatrix C(X, ℂ)) :
      kZeroClass (fun x ↦ (p.blockSum q).fiber x) =
        kZeroClass (fun x ↦ p.fiber x) + kZeroClass (fun x ↦ q.fiber x) := by
    simp only [kZeroClass_image, AtiyahSinger.kZeroClass_blockSum]
  have hfree (m n : ℕ) :
      kZeroClass (Bundle.Trivial X (Fin (m + n) → ℂ)) =
        kZeroClass (Bundle.Trivial X (Fin m → ℂ)) +
          kZeroClass (Bundle.Trivial X (Fin n → ℂ)) := by
    have hmatrix : (IdempotentMatrix.identity C(X, ℂ) m).blockSum
        (IdempotentMatrix.identity C(X, ℂ) n) =
          IdempotentMatrix.identity C(X, ℂ) (m + n) := by
      dsimp only [IdempotentMatrix.blockSum, IdempotentMatrix.identity]
      congr 1
      simp [IdempotentMatrix.blockMatrix, Matrix.fromBlocks_one]
    simp only [kZeroClass_trivial]
    rw [← hmatrix, AtiyahSinger.kZeroClass_blockSum]
  -- Descend finite additive generation through the same free-group quotient.
  refine Quotient.inductionOn a ?_
  intro z
  change ∃ p : IdempotentMatrix C(X, ℂ), ∃ n : ℕ,
    (QuotientAddGroup.mk' (kZeroRelations C(X, ℂ))) z =
      kZeroClass (fun x ↦ p.fiber x) - kZeroClass (Bundle.Trivial X (Fin n → ℂ))
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
    refine ⟨IdempotentMatrix.identity C(X, ℂ) 0, 0, ?_⟩
    simp only [map_zero, kZeroClass_image, kZeroClass_trivial, sub_self]
  | of p =>
    refine ⟨p, 0, ?_⟩
    simp only [kZeroClass_trivial_zero, sub_zero, kZeroClass_image]
    rfl
  | neg z hz =>
    obtain ⟨p, n, hp⟩ := hz
    refine ⟨(IdempotentMatrix.identity C(X, ℂ) n).blockSum p.complement, p.size, ?_⟩
    rw [map_neg, hp, hblock,
      kZeroClass_image (IdempotentMatrix.identity C(X, ℂ) n), ← kZeroClass_trivial]
    -- Replace the negative image by its actual complement in the same ambient trivial bundle.
    have hcomp := kZeroClass_complement p
    rw [← hcomp]
    abel
  | add z w hz hw =>
    obtain ⟨p, m, hp⟩ := hz
    obtain ⟨q, n, hq⟩ := hw
    refine ⟨p.blockSum q, m + n, ?_⟩
    rw [map_add, hp, hq, hblock, hfree]
    abel

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  {V : Y → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module ℂ (V y)]
  [TopologicalSpace (TotalSpace Unit V)] [IsFiniteRank V]

omit [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y] in
/-- Pullback of an image retains exactly its original ambient coordinates and topology. -/
private theorem nonempty_pullback_image_iso (p : IdempotentMatrix C(Y, ℂ))
    (f : C(X, Y)) :
    Nonempty (Iso ((f : X → Y) *ᵖ (fun y ↦ p.fiber y))
      (fun x ↦ (p.map (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom).fiber x)) := by
  -- Evaluation after precomposition gives literally the same complex projection matrix.
  let q := p.map (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom
  let e : Iso ((f : X → Y) *ᵖ (fun y ↦ p.fiber y)) (fun x ↦ q.fiber x) := {
    linearEquiv := fun x ↦ LinearEquiv.refl ℂ (p.fiber (f x))
    continuous_total := by
      apply continuous_induced_rng.mpr
      have hcoords : Continuous (fun z : TotalSpace Unit (fun y ↦ p.fiber y) ↦
          z.snd.val) := by
        have hp : Continuous (fun z : TotalSpace Unit (fun y ↦ p.fiber y) ↦
            (z.proj, z.snd.val)) := continuous_induced_dom
        exact continuous_snd.comp hp
      exact (Pullback.continuous_proj Unit (fun y ↦ p.fiber y) f).prodMk
        (hcoords.comp (Pullback.continuous_lift Unit (fun y ↦ p.fiber y) f))
    continuous_symm := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit (fun y ↦ p.fiber y) f).continuous_iff]
      have hq : Continuous (fun z : TotalSpace Unit (fun x ↦ q.fiber x) ↦
          (z.proj, z.snd.val)) := continuous_induced_dom
      apply (continuous_fst.comp hq).prodMk
      apply continuous_induced_rng.mpr
      exact (f.continuous.comp (continuous_fst.comp hq)).prodMk (continuous_snd.comp hq) }
  exact ⟨e⟩

/-- Pullback of the actual bundle agrees with precomposition on matrix classes. -/
theorem kZeroClass_pullback (f : C(X, Y)) :
    kZeroClass ((f : X → Y) *ᵖ V) = complexKZeroPullback f (kZeroClass V) := by
  /- Pull back a chosen image presentation of V. Evaluation identifies its fiber
  at x with the image of the matrix whose entries are composed with f. Both total
  topologies are induced by x and the same ambient coordinate vector, giving an
  actual bundle isomorphism. Apply the class formula for the specified ring map. -/
  let p := idempotentPresentation (E := V)
  obtain ⟨e⟩ := nonempty_pullback_image_iso p f
  -- Pull back the same chosen presentation, then compare its genuine image topology.
  change kZeroClass ((f : X → Y) *ᵖ V) =
    kZeroMap (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom
      (AtiyahSinger.kZeroClass C(Y, ℂ) p)
  rw [kZeroMap_class]
  exact kZeroClass_eq_of_presentation (p.map (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom)
    (((presentationIso (E := V)).pullback f).trans e)

open scoped Matrix Matrix.Norms.Operator unitInterval in
/-- Homotopic maps of compact Hausdorff spaces yield isomorphic pullback bundles. -/
theorem nonempty_pullback_iso_of_homotopy (f g : C(X, Y)) (H : ContinuousMap.Homotopy f g) :
    Nonempty (Iso ((f : X → Y) *ᵖ V) ((g : X → Y) *ᵖ V)) := by
  /- Present V as an idempotent image bundle on Y. Substitution along H gives a
  norm-continuous idempotent path over C(X,ℂ); compactness of X is essential for
  uniform continuity here. Subdivide the interval and use the explicit near-identity
  intertwiners to identify successive image bundles. Compose these actual isomorphisms
  and the endpoint presentation pullbacks. This does not use equality of K-classes
  to infer unstabilized isomorphism, which would be invalid in general. -/
  let p := idempotentPresentation (E := V)
  let p₀ := p.map (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom
  let p₁ := p.map (ContinuousMap.compRightAlgHom ℂ ℂ g).toRingHom
  have hequiv : p₀.IsEquivalent p₁ := by
    -- Currying the actual joint homotopy gives continuous functions in the uniform topology.
    let entry (i j : Fin p.size) : C(I, C(X, ℂ)) :=
      ((p.matrix i j).comp H.toContinuousMap).curry
    let P : C(I, Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) :=
      ⟨fun t i j ↦ entry i j t, continuous_pi fun i ↦
        continuous_pi fun j ↦ (entry i j).continuous⟩
    have hP (t : I) : P t * P t = P t := by
      exact (p.map (ContinuousMap.compRightAlgHom ℂ ℂ (H.curry t)).toRingHom).mul_self
    have hP₀ : P 0 = (p.map (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom).matrix := by
      ext i j x
      change p.matrix i j (H (0, x)) = p.matrix i j (f x)
      rw [H.apply_zero]
    have hP₁ : P 1 = (p.map (ContinuousMap.compRightAlgHom ℂ ℂ g).toRingHom).matrix := by
      ext i j x
      change p.matrix i j (H (1, x)) = p.matrix i j (g x)
      rw [H.apply_one]
    -- The Banach-algebra homotopy theorem gives a unit conjugating the same endpoint matrices.
    have : CompleteSpace (Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) :=
      inferInstanceAs (CompleteSpace (Fin p.size → Fin p.size → C(X, ℂ)))
    obtain ⟨u, hu⟩ := exists_unit_conjugating_idempotent_path P hP
    refine ⟨P 0 * (↑(u⁻¹) : Matrix _ _ _), (u : Matrix _ _ _) * P 0, ?_, ?_, ?_, ?_⟩
    · rw [← hP₀]
      calc
        P 0 * ↑u⁻¹ * (↑u * P 0) = (P 0 * ↑u⁻¹ * ↑u) * P 0 := (mul_assoc _ _ _).symm
        _ = P 0 * P 0 := by rw [Units.inv_mul_cancel_right]
        _ = P 0 := hP 0
    · rw [← hP₁]
      calc
        ↑u * P 0 * (P 0 * ↑u⁻¹) = ↑u * (P 0 * P 0) * ↑u⁻¹ := by
          simp only [mul_assoc]
        _ = ↑u * P 0 * ↑u⁻¹ := by rw [hP 0]
        _ = P 1 := hu.symm
    · rw [← hP₀]
      change P 0 * (P 0 * (↑u⁻¹ : Matrix (Fin p.size) (Fin p.size) C(X, ℂ))) =
        P 0 * (↑u⁻¹ : Matrix (Fin p.size) (Fin p.size) C(X, ℂ))
      rw [← mul_assoc, hP 0]
    · rw [← hP₁]
      change P 1 * ((u : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) * P 0) =
        (u : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) * P 0
      calc
        P 1 * (↑u * P 0) = (↑u * P 0 * ↑u⁻¹) * (↑u * P 0) :=
          congrArg (fun a : Matrix (Fin p.size) (Fin p.size) C(X, ℂ) ↦
            a * ((u : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) * P 0)) hu
        _ =
            (↑u * P 0 * ↑u⁻¹ * ↑u) * P 0 := (mul_assoc _ _ _).symm
        _ = ↑u * P 0 * P 0 := by rw [Units.inv_mul_cancel_right]
        _ = ↑u * P 0 := by rw [mul_assoc, hP 0]
  -- These rectangular witnesses identify actual image modules, not only their classes.
  obtain ⟨a⟩ := (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv p₀ p₁).mp hequiv
  let e : Iso (fun x ↦ p₀.fiber x) (fun x ↦ p₁.fiber x) :=
    isoOfSectionEquiv (p₀.imageSectionEquiv.symm.trans (a.trans p₁.imageSectionEquiv))
  obtain ⟨e₀⟩ := nonempty_pullback_image_iso p f
  obtain ⟨e₁⟩ := nonempty_pullback_image_iso p g
  -- Keep the same original bundle presentation at both ends of the supplied homotopy.
  exact ⟨(((presentationIso (E := V)).pullback f).trans e₀).trans
    (e.trans (((presentationIso (E := V)).pullback g).trans e₁).symm)⟩

/-- Geometric bundle classes agree along the same homotopy. -/
theorem kZeroClass_pullback_eq_of_homotopy (f g : C(X, Y))
    (H : ContinuousMap.Homotopy f g) :
    kZeroClass ((f : X → Y) *ᵖ V) = kZeroClass ((g : X → Y) *ᵖ V) := by
  /- The preceding homotopy argument gives an actual isomorphism of the endpoint
  pullback bundles. Apply isomorphism invariance of their classes. Equivalently,
  naturality and the existing algebraic K⁰ homotopy invariance give the same equality. -/
  exact kZeroClass_eq_of_iso (Classical.choice
    (nonempty_pullback_iso_of_homotopy (V := V) f g H))

end AtiyahSinger.ComplexBundle
