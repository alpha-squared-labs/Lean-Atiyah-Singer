/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SerreSwanMaps

/-!
# Idempotent complements and the compact bundle embedding theorem

Public module ID: M1574.

D07/K01/KB01. Complement means image of 1-p; it is not asserted to be orthogonal
unless p is self-adjoint. Actual addition identifies image(p) ⊕ image(1-p) with
the trivial bundle. SG I.9.8 and I.9.9 use an orthogonal complement of a finite
embedding; the algebraic complement here gives the same existence conclusion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle


end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.IdempotentMatrix

open Bundle

variable {R : Type*} [CommRing R] (p : IdempotentMatrix R)

/-- The complementary matrix of an idempotent is idempotent. -/
theorem complementMatrix_mul_self : (1 - p.matrix) * (1 - p.matrix) = 1 - p.matrix := by
  /- Expand the product by distributivity, replace p squared by p, and collect
  terms. This calculation uses the given projection identity and does not require a metric. -/
  noncomm_ring [p.mul_self]

/-- The standard complementary idempotent, with the same ambient free module. -/
@[reducible]
def complement : IdempotentMatrix R where
  size := p.size
  matrix := 1 - p.matrix
  mul_self := p.complementMatrix_mul_self

/-- The two projections annihilate each other. -/
theorem matrix_mul_complement : p.matrix * p.complement.matrix = 0 := by
  /- Expand p(1-p) as p-p squared. The given idempotence identity makes the two
  terms equal, so their difference is zero in the matrix ring. -/
  change p.matrix * (1 - p.matrix) = 0
  rw [mul_sub, mul_one, p.mul_self, sub_self]

/-- The complement annihilates the original projection in the reverse order. -/
theorem complement_mul_matrix : p.complement.matrix * p.matrix = 0 := by
  /- Expand (1-p)p as p-p squared and substitute the projection identity.
  The result is the zero endomorphism of the original finite free module. -/
  change (1 - p.matrix) * p.matrix = 0
  rw [sub_mul, one_mul, p.mul_self, sub_self]

/-- Complementation is involutive on actual idempotent matrices. -/
theorem complement_complement : p.complement.complement = p := by
  /- The ambient size is unchanged, and the matrix is 1-(1-p), which equals p.
  After this matrix equality the two idempotence certificates agree by proof irrelevance. -/
  cases p with
  | mk n A h =>
    simp only [complement]
    congr 1
    abel

/-- Entrywise base change commutes with taking the complement. -/
theorem complement_map {S : Type*} [CommRing S] (φ : R →+* S) :
    (p.complement).map φ = (p.map φ).complement := by
  /- A unital ring homomorphism sends the identity matrix to identity and preserves
  subtraction entrywise. Thus both sides have the same size and the same matrix. -/
  cases p with
  | mk n A h =>
    simp only [complement, map, map_sub, map_one]
    rfl

variable {X : Type*} [TopologicalSpace X]

attribute [local instance] fiberTotalSpaceTopology isFiniteRank_fiber
attribute [local instance] ComplexBundle.trivialTopology ComplexBundle.isFiniteRank_trivial
attribute [local instance] ComplexBundle.sumTopology ComplexBundle.isFiniteRank_sum

variable (q : IdempotentMatrix C(X, ℂ))

/-- The inclusion of an image bundle into its ambient trivial bundle is continuous. -/
theorem continuous_fiber_inclusion :
    Continuous (fun z : TotalSpace Unit (fun x ↦ q.fiber x) ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit (Bundle.Trivial X (Fin q.size → ℂ)))) := by
  /- Both total-space topologies are induced from X times the same finite coordinate
  space, and the displayed inclusion retains those coordinates. Continuity follows
  directly from the defining induced topology of the image bundle. -/
  apply continuous_induced_rng.mpr
  exact (continuous_induced_dom : Continuous
    (fun z : TotalSpace Unit (fun x ↦ q.fiber x) ↦ (z.proj, z.snd.val)))

/-- The specified ambient inclusion of the idempotent image bundle. -/
def fiberInclusion : ComplexBundle.Hom (fun x ↦ q.fiber x)
    (Bundle.Trivial X (Fin q.size → ℂ)) where
  linearMap x := (q.fiber x).subtype
  continuous_total := q.continuous_fiber_inclusion

/-- Addition of the complementary fiber images is continuous on total spaces. -/
theorem continuous_complement_addition :
    Continuous (fun z : TotalSpace Unit
      ((fun x ↦ q.fiber x) ×ᵇ (fun x ↦ q.complement.fiber x)) ↦
      (⟨z.proj, z.snd.1.val + z.snd.2.val⟩ :
        TotalSpace Unit (Bundle.Trivial X (Fin q.size → ℂ)))) := by
  /- The two coordinate vectors depend continuously on the input through the
  direct-sum topology and the image inclusions. Addition in the fixed finite complex
  vector space is continuous, and the base point remains unchanged. -/
  -- Read both original image coordinates through the original direct-sum projections.
  have hleft : Continuous (fun z : TotalSpace Unit
      ((fun x ↦ q.fiber x) ×ᵇ (fun x ↦ q.complement.fiber x)) ↦
      (z.proj, z.snd.1.val)) :=
    (continuous_induced_dom : Continuous
      (fun z : TotalSpace Unit (fun x ↦ q.fiber x) ↦ (z.proj, z.snd.val))).comp
      ComplexBundle.continuous_sum_fst
  have hright : Continuous (fun z : TotalSpace Unit
      ((fun x ↦ q.fiber x) ×ᵇ (fun x ↦ q.complement.fiber x)) ↦
      (z.proj, z.snd.2.val)) :=
    (continuous_induced_dom : Continuous
      (fun z : TotalSpace Unit (fun x ↦ q.complement.fiber x) ↦ (z.proj, z.snd.val))).comp
      ComplexBundle.continuous_sum_snd
  apply continuous_induced_rng.mpr
  exact hleft.fst.prodMk (hleft.snd.add hright.snd)

/-- The actual addition map from complementary image bundles to the ambient trivial bundle. -/
def complementAddition : ComplexBundle.Hom
    ((fun x ↦ q.fiber x) ×ᵇ (fun x ↦ q.complement.fiber x))
    (Bundle.Trivial X (Fin q.size → ℂ)) where
  linearMap x := (q.fiber x).subtype.coprod (q.complement.fiber x).subtype
  continuous_total := q.continuous_complement_addition

open scoped Matrix in
/-- The actual addition map is bijective on each fiber. -/
theorem complementAddition_bijective (x : X) :
    Function.Bijective (q.complementAddition.linearMap x) := by
  /- At x the inverse sends v to (q(x)v,(1-q(x))v). These vectors lie in the
  respective images. Their sum is v. Conversely each projection fixes its own image
  and annihilates the other, proving that this inverse also recovers both summands. -/
  classical
  let A : Matrix (Fin q.size) (Fin q.size) ℂ :=
    (q.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix
  let B : Matrix (Fin q.size) (Fin q.size) ℂ :=
    (q.complement.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix
  have hAA : A * A = A := (q.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  have hBB : B * B = B :=
    (q.complement.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  have hB : B = 1 - A := by
    change (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix (1 - q.matrix) =
      1 - (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix q.matrix
    rw [map_sub, map_one]
  have hAB : A * B = 0 := by rw [hB, mul_sub, mul_one, hAA, sub_self]
  have hBA : B * A = 0 := by rw [hB, sub_mul, one_mul, hAA, sub_self]
  -- Each projection fixes its actual image and kills the complementary image.
  have hAfix (v : q.fiber x) : A *ᵥ v.val = v.val := by
    obtain ⟨u, hu⟩ : ∃ u : Fin q.size → ℂ, A *ᵥ u = v.val := v.property
    rw [← hu, Matrix.mulVec_mulVec, hAA]
  have hBfix (v : q.complement.fiber x) : B *ᵥ v.val = v.val := by
    obtain ⟨u, hu⟩ : ∃ u : Fin q.size → ℂ, B *ᵥ u = v.val := v.property
    rw [← hu, Matrix.mulVec_mulVec, hBB]
  have hAzero (v : q.complement.fiber x) : A *ᵥ v.val = 0 := by
    obtain ⟨u, hu⟩ : ∃ u : Fin q.size → ℂ, B *ᵥ u = v.val := v.property
    rw [← hu, Matrix.mulVec_mulVec, hAB, Matrix.zero_mulVec]
  have hBzero (v : q.fiber x) : B *ᵥ v.val = 0 := by
    obtain ⟨u, hu⟩ : ∃ u : Fin q.size → ℂ, A *ᵥ u = v.val := v.property
    rw [← hu, Matrix.mulVec_mulVec, hBA, Matrix.zero_mulVec]
  let inverse (v : Fin q.size → ℂ) : q.fiber x × q.complement.fiber x :=
    (⟨A *ᵥ v, ⟨v, rfl⟩⟩, ⟨B *ᵥ v, ⟨v, rfl⟩⟩)
  have hleft : Function.LeftInverse inverse (q.complementAddition.linearMap x) := by
    intro v
    apply Prod.ext
    · apply Subtype.ext
      change A *ᵥ (v.1.val + v.2.val) = v.1.val
      rw [Matrix.mulVec_add, hAfix, hAzero, add_zero]
    · apply Subtype.ext
      change B *ᵥ (v.1.val + v.2.val) = v.2.val
      rw [Matrix.mulVec_add, hBzero, hBfix, zero_add]
  have hright : Function.RightInverse inverse (q.complementAddition.linearMap x) := by
    intro v
    change A *ᵥ v + B *ᵥ v = v
    rw [← Matrix.add_mulVec, hB]
    have hsum : A + (1 - A) = 1 := by abel
    rw [hsum, Matrix.one_mulVec]
  exact ⟨hleft.injective, hright.surjective⟩

/-- The specified complement isomorphism, whose forward map is actual addition. -/
def complementIso : ComplexBundle.Iso
    ((fun x ↦ q.fiber x) ×ᵇ (fun x ↦ q.complement.fiber x))
    (Bundle.Trivial X (Fin q.size → ℂ)) :=
  q.complementAddition.toIso q.complementAddition_bijective

/-- The complement isomorphism adds the two original coordinate vectors. -/
theorem complementIso_apply (x : X) (v : q.fiber x) (w : q.complement.fiber x) :
    q.complementIso.linearEquiv x (v, w) = v.val + w.val := by
  /- The isomorphism was made from the concrete addition bundle map using its
  fiberwise bijectivity theorem. This does not change its forward function, which is addition. -/
  rfl

end AtiyahSinger.IdempotentMatrix

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [hE : IsFiniteRank E] [hC : CompactSpace X] [hT : T2Space X]

attribute [local instance] IdempotentMatrix.fiberTotalSpaceTopology
attribute [local instance] IdempotentMatrix.isFiniteRank_fiber
attribute [local instance] trivialTopology isFiniteRank_trivial sumTopology isFiniteRank_sum

include hE hC hT

/-- SG I.9.8: a finite-rank bundle embeds fiberwise in a finite trivial bundle. -/
theorem exists_fiberwise_injective_trivial_map :
    ∃ n : ℕ, ∃ f : Hom E (Bundle.Trivial X (Fin n → ℂ)),
      ∀ x, Function.Injective (f.linearMap x) := by
  /- Reuse the actual image presentation already constructed by the closed
  Serre-Swan correspondence, whose finite splitting comes from a partition of
  unity on the original local charts. Compose its bundle isomorphism with the
  image's actual inclusion into the same finite trivial bundle. Both maps are
  continuous, and each fiber map is injective. This proves the existence statement
  of SG I.9.8 without choosing a second presentation or a new global rank. -/
  -- Retain one actual image presentation through the inclusion into its ambient trivial bundle.
  let p := idempotentPresentation (E := E)
  let e : Iso E (fun x ↦ p.fiber x) := presentationIso
  refine ⟨p.size, p.fiberInclusion.comp e.toHom, ?_⟩
  intro x
  exact Subtype.val_injective.comp (e.linearEquiv x).injective

/-- An explicit idempotent image supplies a complementary bundle to E. -/
theorem nonempty_presentation_complement_iso :
    Nonempty (Iso (E ×ᵇ (fun x ↦ (idempotentPresentation (E := E)).complement.fiber x))
      (Bundle.Trivial X (Fin (idempotentPresentation (E := E)).size → ℂ))) := by
  /- Take the direct sum of presentationIso with the identity on the complementary
  image bundle. Compose with the addition isomorphism for p and 1-p. This produces
  the required actual bundle isomorphism, using the same chosen p throughout. -/
  -- The direct sum and addition use precisely the idempotent already named in the statement.
  let p := idempotentPresentation (E := E)
  exact ⟨((presentationIso (E := E)).sum
    (Iso.refl (fun x ↦ p.complement.fiber x))).trans p.complementIso⟩

/-- SG I.9.9: E admits a finite-rank continuous complement in a trivial bundle. -/
theorem exists_complement_bundle :
    ∃ p : IdempotentMatrix C(X, ℂ),
      Nonempty (Iso (E ×ᵇ (fun x ↦ p.complement.fiber x))
        (Bundle.Trivial X (Fin p.size → ℂ))) := by
  /- SG takes the orthogonal complement of the finite embedding in the standard
  Hermitian trivial bundle. In the idempotent presentation take instead image(1-p);
  the actual addition isomorphism supplies the same existence statement. This
  algebraic complement is not claimed to be orthogonal without self-adjointness. -/
  exact ⟨idempotentPresentation (E := E), nonempty_presentation_complement_iso (E := E)⟩

end AtiyahSinger.ComplexBundle
