/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteContinuousRepresentation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.RepresentationTheory.Character

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Haar projections for finite continuous representations

Public module ID: M0006.

The normalized Haar average of the actual action is the projection onto its
invariant vectors. Commuting the finite-dimensional trace with this integral
computes the invariant dimension. Applied to a Hom representation, this is
the compact-group replacement for a finite-group character sum.

These standard averaging facts support the independent character-detection
argument for the original continuous representation ring. They do not assume
an irreducible classification or a finite underlying group.
-/

@[expose] public noncomputable section

universe u

namespace AtiyahSinger

open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

/-- Normalized Haar averaging projects onto the original invariant subspace. -/
theorem isProj_integral_representation (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    LinearMap.IsProj ρ.toRepresentation.invariants
      (∫ g : G, ρ g ∂μ).toLinearMap := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hc : Continuous (fun g : G ↦ ρ g) := by
    apply continuous_clm_apply.mpr
    intro v
    exact hρ.comp (continuous_id.prodMk continuous_const)
  have hint : Integrable (fun g : G ↦ ρ g) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hv (v : E) : Integrable (fun g : G ↦ ρ g v) μ :=
    (hρ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  constructor
  · -- Left invariance puts each averaged vector in the same original fixed subspace.
    intro v g
    change ρ g ((∫ h : G, ρ h ∂μ) v) = (∫ h : G, ρ h ∂μ) v
    rw [ContinuousLinearMap.integral_apply hint]
    rw [← (ρ g).integral_comp_comm (hv v)]
    simpa only [← mul_apply_eq_comp, ← map_mul] using
      integral_mul_left_eq_self (μ := μ) (fun h : G ↦ ρ h v) g
  · -- A fixed vector is a constant integrand and the measure has total mass one.
    intro v hv
    change (∫ g : G, ρ g ∂μ) v = v
    rw [ContinuousLinearMap.integral_apply hint]
    have heq : (fun g : G ↦ ρ g v) = fun _ ↦ v := funext hv
    rw [heq]
    simp

/-- The integral of the character is the complex dimension of the original fixed subspace. -/
theorem integral_character_eq_finrank_invariants (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    ∫ g : G, ρ.toRepresentation.character g ∂μ =
      (Module.finrank ℂ ρ.toRepresentation.invariants : ℂ) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hc : Continuous (fun g : G ↦ ρ g) := by
    apply continuous_clm_apply.mpr
    intro v
    exact hρ.comp (continuous_id.prodMk continuous_const)
  have hint : Integrable (fun g : G ↦ ρ g) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let tr : (E →L[ℂ] E) →L[ℂ] ℂ :=
    (LinearMap.trace ℂ E ∘ₗ ContinuousLinearMap.coeLM ℂ).toContinuousLinearMap
  calc
    _ = tr (∫ g : G, ρ g ∂μ) := tr.integral_comp_comm hint
    _ = _ := (isProj_integral_representation μ ρ hρ).trace

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The standard Hom action on the native space of continuous linear maps. -/
def continuousLinearMapRepresentation (ρ : ContRepresentation ℂ G E)
    (σ : ContRepresentation ℂ G F) : ContRepresentation ℂ G (E →L[ℂ] F) :=
  .ofMonoidHom {
    toFun g := ({
      toFun L := σ g ∘L L ∘L ρ g⁻¹
      map_add' L K := by simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
      map_smul' c L := by
        simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
          RingHom.id_apply] } : (E →L[ℂ] F) →ₗ[ℂ] (E →L[ℂ] F)).toContinuousLinearMap
    map_one' := by
      ext L x
      simp
    map_mul' g h := by
      ext L x
      simp [map_mul, mul_inv_rev, mul_apply_eq_comp] }

include μ in
/-- Equal compact-group characters force a nonzero intertwiner from a nonzero representation. -/
theorem exists_ne_zero_intertwining_of_character_eq (ρ : ContRepresentation ℂ G E)
    (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hchar : ρ.toRepresentation.character = σ.toRepresentation.character) [Nontrivial E] :
    ∃ L : E →L[ℂ] F, L ≠ 0 ∧ ∀ (g : G) (v : E), L (ρ g v) = σ g (L v) := by
  classical
  -- Conjugation is the same algebraic Hom representation in continuous coordinates.
  let τ := continuousLinearMapRepresentation ρ σ
  let ε := continuousLinearMapRepresentation ρ ρ
  have hcont {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W]
      [FiniteDimensional ℂ W] (κ : ContRepresentation ℂ G W)
      (hκ : Continuous (fun p : G × W ↦ κ p.1 p.2)) :
      Continuous (fun p : G × (E →L[ℂ] W) ↦
        continuousLinearMapRepresentation ρ κ p.1 p.2) := by
    have hρ' : Continuous (fun g : G ↦ ρ g) := continuous_clm_apply.mpr fun v ↦
      hρ.comp (continuous_id.prodMk continuous_const)
    have hκ' : Continuous (fun g : G ↦ κ g) := continuous_clm_apply.mpr fun v ↦
      hκ.comp (continuous_id.prodMk continuous_const)
    exact (hκ'.comp continuous_fst).clm_comp
      (continuous_snd.clm_comp (hρ'.comp continuous_fst.inv))
  have htrace {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W]
      [FiniteDimensional ℂ W] (κ : ContRepresentation ℂ G W) (g : G) :
      (continuousLinearMapRepresentation ρ κ).toRepresentation.character g =
        ρ.toRepresentation.character g⁻¹ * κ.toRepresentation.character g := by
    let e : (E →ₗ[ℂ] W) ≃ₗ[ℂ] (E →L[ℂ] W) := LinearMap.toContinuousLinearMap
    let d : Representation.Equiv (Representation.linHom ρ.toRepresentation κ.toRepresentation)
        (continuousLinearMapRepresentation ρ κ).toRepresentation :=
      Representation.Equiv.mk e (by intro h; ext L x; rfl)
    exact (congrFun (Representation.char_iso d) g).symm.trans
      (Representation.char_linHom _ _ g)
  -- Both averages have the same trace. The endomorphism average fixes the identity.
  have hdim : Module.finrank ℂ τ.toRepresentation.invariants =
      Module.finrank ℂ ε.toRepresentation.invariants := by
    apply Nat.cast_injective (R := ℂ)
    rw [← integral_character_eq_finrank_invariants μ τ (hcont σ hσ),
      ← integral_character_eq_finrank_invariants μ ε (hcont ρ hρ)]
    apply integral_congr_ae
    filter_upwards [] with g
    rw [htrace, htrace, hchar]
  let identity : ε.toRepresentation.invariants := ⟨ContinuousLinearMap.id ℂ E, by
    intro g
    ext v
    change ρ g (ρ g⁻¹ v) = v
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl⟩
  have hid : identity ≠ 0 := by
    intro h
    have hzero : (ContinuousLinearMap.id ℂ E) = 0 := congrArg Subtype.val h
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    exact hv (DFunLike.congr_fun hzero v)
  have hpos : 0 < Module.finrank ℂ τ.toRepresentation.invariants := by
    rw [hdim]
    let : Nontrivial ε.toRepresentation.invariants := nontrivial_of_ne identity 0 hid
    exact Module.finrank_pos
  let : Nontrivial τ.toRepresentation.invariants := Module.finrank_pos_iff.mp hpos
  obtain ⟨L, hL⟩ := exists_ne (0 : τ.toRepresentation.invariants)
  refine ⟨L.val, fun h ↦ hL (Subtype.ext h), ?_⟩
  intro g v
  have h := DFunLike.congr_fun (L.property g) (ρ g v)
  change σ g (L.val (ρ g⁻¹ (ρ g v))) = L.val (ρ g v) at h
  rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one] at h
  exact h.symm

include μ in
/-- An injective map of finite compact-group representations has an equivariant retraction. -/
theorem exists_intertwining_leftInverse (ρ : ContRepresentation ℂ G E)
    (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (i : F →L[ℂ] E) (hinj : Function.Injective i)
    (hi : ∀ (g : G) (v : F), i (σ g v) = ρ g (i v)) :
    ∃ p : E →L[ℂ] F, (∀ v : F, p (i v) = v) ∧
      ∀ (g : G) (v : E), p (ρ g v) = σ g (p v) := by
  classical
  let : CompleteSpace F := FiniteDimensional.complete ℂ F
  obtain ⟨p₀, hp₀⟩ :=
    i.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let p₀' : E →L[ℂ] F := p₀.toContinuousLinearMap
  have hleft (v : F) : p₀' (i v) = v := DFunLike.congr_fun hp₀ v
  let τ := continuousLinearMapRepresentation ρ σ
  have hρ' : Continuous (fun g : G ↦ ρ g) := continuous_clm_apply.mpr fun v ↦
    hρ.comp (continuous_id.prodMk continuous_const)
  have hσ' : Continuous (fun g : G ↦ σ g) := continuous_clm_apply.mpr fun v ↦
    hσ.comp (continuous_id.prodMk continuous_const)
  have hτ : Continuous (fun p : G × (E →L[ℂ] F) ↦ τ p.1 p.2) :=
    (hσ'.comp continuous_fst).clm_comp
      (continuous_snd.clm_comp (hρ'.comp continuous_fst.inv))
  have hint : Integrable (fun g : G ↦ τ g) μ :=
    (continuous_clm_apply.mpr (fun L ↦
      hτ.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint₀ : Integrable (fun g : G ↦ τ g p₀') μ :=
    (hτ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let p : E →L[ℂ] F := (∫ g : G, τ g ∂μ) p₀'
  have hfix := (isProj_integral_representation μ τ hτ).map_mem p₀'
  refine ⟨p, ?_, ?_⟩
  · -- Every conjugate of the initial retraction still fixes the specified embedded copy.
    intro v
    change (∫ g : G, τ g ∂μ) p₀' (i v) = v
    rw [ContinuousLinearMap.integral_apply hint, ContinuousLinearMap.integral_apply hint₀]
    have hvalue (g : G) : τ g p₀' (i v) = v := by
      change σ g (p₀' (ρ g⁻¹ (i v))) = v
      rw [← hi, hleft, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one]
      rfl
    simp [hvalue]
  · -- Being fixed by the Hom action is exactly equivariance of this same retraction.
    intro g v
    have h := DFunLike.congr_fun (hfix g) (ρ g v)
    change σ g (p (ρ g⁻¹ (ρ g v))) = p (ρ g v) at h
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one] at h
    exact h.symm

/-- Restrict the original continuous fiber maps to a specified invariant submodule. -/
def continuousSubmoduleRepresentation (ρ : ContRepresentation ℂ G E) (N : Submodule ℂ E)
    (hN : ∀ (g : G) (v : E), v ∈ N → ρ g v ∈ N) : ContRepresentation ℂ G N :=
  .ofMonoidHom {
    toFun g := (ρ g).restrict (fun v hv ↦ hN g v hv)
    map_one' := by ext v; simp
    map_mul' g h := by ext v; simp [map_mul, mul_apply_eq_comp] }

include μ in
/-- Every invariant submodule of a finite compact-group representation has an invariant complement.
-/
theorem exists_invariant_complement (ρ : ContRepresentation ℂ G E)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (N : Submodule ℂ E) (hN : ∀ (g : G) (v : E), v ∈ N → ρ g v ∈ N) :
    ∃ C : Submodule ℂ E, IsCompl N C ∧ ∀ (g : G) (v : E), v ∈ C → ρ g v ∈ C := by
  let σ := continuousSubmoduleRepresentation ρ N hN
  have hσ : Continuous (fun p : G × N ↦ σ p.1 p.2) :=
    (hρ.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  obtain ⟨p, hp, heq⟩ := exists_intertwining_leftInverse μ ρ σ hρ hσ N.subtypeL
    Subtype.val_injective (fun _ _ ↦ rfl)
  have hfix (v : N) : p.toLinearMap v = v := hp v
  have hcompl : IsCompl N p.ker := LinearMap.isCompl_of_proj hfix
  refine ⟨p.ker, hcompl, ?_⟩
  intro g v hv
  change p (ρ g v) = 0
  rw [heq, show p v = 0 from hv, map_zero]

end AtiyahSinger
