/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ThomTensorSymbol
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Reciprocal cutoff normalization for iterated Thom symbols

Public module ID: M2245.

The second supported Thom operator uses a cutoff times the first symbol and
its actual inverse. This is generally different from the first symbol and
its negative reverse block. Positive interpolation of their two coefficients
keeps the tensor symbol invertible on one compact exterior. The affine
boundary criterion packages this interpolation on the original bundle models.

These normalization lemmas are used by the supported direct-sum comparison
in `ThomDirectSum`, following Karoubi IV.1.7--1.10. Neither compactness of
the base nor properness of a bundle projection is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped TensorProduct unitInterval

/-- Positive reciprocal normalization preserves the invertibility of the tensor boundary. -/
theorem thomTensorSymbol_cutoff_homotopy_bijective
    {E F V : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (d : E →ₗ[ℂ] F) (d' : F →ₗ[ℂ] E) (A : ℝ) (ψ t : I) (v : V)
    (hA : 0 ≤ A)
    (hd : d'.comp d = (A : ℂ) • LinearMap.id)
    (hd' : d.comp d' = (A : ℂ) • LinearMap.id)
    (hpositive : 0 < (ψ : ℝ) * A + ‖v‖ ^ 2) :
    Function.Bijective (thomTensorSymbol
      ((((1 - (t : ℝ)) * (ψ : ℝ) + t : ℝ) : ℂ) • d)
      ((((1 - (t : ℝ)) * ((ψ : ℝ) / A) + t : ℝ) : ℂ) • d') v) := by
  let α : ℝ := (1 - (t : ℝ)) * ψ + t
  let β : ℝ := (1 - (t : ℝ)) * ((ψ : ℝ) / A) + t
  have ht : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have hα : 0 ≤ α := add_nonneg (mul_nonneg ht ψ.property.1) t.property.1
  have hβ : 0 ≤ β := add_nonneg (mul_nonneg ht (div_nonneg ψ.property.1 hA)) t.property.1
  have hscale : 0 ≤ α * β * A := mul_nonneg (mul_nonneg hα hβ) hA
  -- On the zero exterior fiber the cutoff and the original scalar are both positive.
  have hn : α * β * A + ‖v‖ ^ 2 ≠ 0 := by
    by_cases hv : v = 0
    · have hp : 0 < (ψ : ℝ) * A := by simpa [hv] using hpositive
      have hpair : 0 < (ψ : ℝ) ∧ 0 < A :=
        (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2])
      have hAp : 0 < A := hpair.2
      have hψ : 0 < (ψ : ℝ) := hpair.1
      have convex_pos (x : ℝ) (hx : 0 < x) : 0 < (1 - (t : ℝ)) * x + t := by
        by_cases hzero : (t : ℝ) = 0
        · simpa [hzero] using hx
        · exact add_pos_of_nonneg_of_pos (mul_nonneg ht (le_of_lt hx))
            (lt_of_le_of_ne t.property.1 (Ne.symm hzero))
      have hαp : 0 < α := convex_pos _ hψ
      have hβp : 0 < β := convex_pos _ (div_pos hψ hAp)
      exact ne_of_gt (add_pos_of_pos_of_nonneg (mul_pos (mul_pos hαp hβp) hAp)
        (sq_nonneg _))
    · exact ne_of_gt (add_pos_of_nonneg_of_pos hscale
        (sq_pos_of_pos (norm_pos_iff.mpr hv)))
  -- The same two reciprocal identities give an explicit inverse throughout the interval.
  have h₀ : ((β : ℂ) • d').comp ((α : ℂ) • d) =
      (((Real.sqrt (α * β * A)) ^ 2 : ℝ) : ℂ) • (LinearMap.id : E →ₗ[ℂ] E) := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hd, Real.sq_sqrt hscale]
    ext x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    push_cast
    ring_nf
  have h₁ : ((α : ℂ) • d).comp ((β : ℂ) • d') =
      (((Real.sqrt (α * β * A)) ^ 2 : ℝ) : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hd', Real.sq_sqrt hscale]
    ext x
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    push_cast
    ring_nf
  have hn' : (Real.sqrt (α * β * A)) ^ 2 + ‖v‖ ^ 2 ≠ 0 := by
    rwa [Real.sq_sqrt hscale]
  exact (thomTensorSymbolEquiv ((α : ℂ) • d) ((β : ℂ) • d')
    (Real.sqrt (α * β * A)) v
    (by simpa only [Complex.ofReal_pow] using h₀)
    (by simpa only [Complex.ofReal_pow] using h₁) hn').bijective

namespace ComplexBundle

variable {X : Type*} [TopologicalSpace X]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

/-- An everywhere invertible affine boundary family gives a homotopy on the same compact control.
This criterion is used for reciprocal normalization while retaining the actual endpoint triples. -/
theorem CompactSupportTriple.homotopic_of_bijective_affine
    (a b : CompactSupportTriple E F) (K : Set X) (hK : IsCompact K)
    (ha : a.control ⊆ K) (hb : b.control ⊆ K)
    (hbij : ∀ (t : I) (x : (Kᶜ : Set X)), Function.Bijective
      ((((1 - (t : ℝ) : ℝ) : ℂ)) •
          ((a.enlarge K hK ha).boundary.linearEquiv x).toLinearMap +
        ((t : ℝ) : ℂ) • ((b.enlarge K hK hb).boundary.linearEquiv x).toLinearMap)) :
    a.Homotopic b := by
  let e₀ := (a.enlarge K hK ha).boundary
  let e₁ := (b.enlarge K hK hb).boundary
  let q : C(I × (Kᶜ : Set X), (Kᶜ : Set X)) := ContinuousMap.snd
  let S := (q : I × (Kᶜ : Set X) → (Kᶜ : Set X)) *ᵖ (Restrict E Kᶜ)
  let T := (q : I × (Kᶜ : Set X) → (Kᶜ : Set X)) *ᵖ (Restrict F Kᶜ)
  let : IsFiniteRank (Restrict E Kᶜ) := isFiniteRank_restrict _
  let : IsFiniteRank (Restrict F Kᶜ) := isFiniteRank_restrict _
  let : IsFiniteRank S := isFiniteRank_pullback q
  let : IsFiniteRank T := isFiniteRank_pullback q
  let f₀ : Hom S T := e₀.toHom.pullback q
  let f₁ : Hom S T := e₁.toHom.pullback q
  let r : C(I × (Kᶜ : Set X), ℂ) :=
    ⟨fun z ↦ ((1 - (z.1 : ℝ) : ℝ) : ℂ),
      Complex.continuous_ofReal.comp
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst))⟩
  let s : C(I × (Kᶜ : Set X), ℂ) :=
    ⟨fun z ↦ ((z.1 : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)⟩
  -- Original endpoint continuity gives joint continuity of this same affine family.
  let f : Hom S T :=
    { linearMap z := r z • f₀.linearMap z + s z • f₁.linearMap z
      continuous_total := by
        let p : C(TotalSpace Unit S, I × (Kᶜ : Set X)) := ⟨π Unit S, continuous_proj⟩
        let := isFiniteRank_pullback (E := T) p
        have hf₀ : Continuous (fun z : TotalSpace Unit S ↦
            (⟨z, f₀.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ T))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit T p).continuous_iff]
          exact continuous_id.prodMk f₀.continuous_total
        have hf₁ : Continuous (fun z : TotalSpace Unit S ↦
            (⟨z, f₁.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ T))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit T p).continuous_iff]
          exact continuous_id.prodMk f₁.continuous_total
        exact (Pullback.continuous_lift Unit T p).comp
          (continuous_add_section (p *ᵖ T) _ _
            (continuous_smul_section _ (r.comp p) _ hf₀)
            (continuous_smul_section _ (s.comp p) _ hf₁)) }
  -- Finite-rank inverse continuity supplies the full-cylinder bundle isomorphism.
  refine ⟨K, hK, ha, hb,
    ⟨{ iso := f.toIso (fun z ↦ hbij z.1 z.2), map_zero := ?_, map_one := ?_ }⟩⟩
  · intro z v
    change r (0, z) • e₀.linearEquiv z v + s (0, z) • e₁.linearEquiv z v = _
    simp [r, s, e₀]
  · intro z v
    change r (1, z) • e₀.linearEquiv z v + s (1, z) • e₁.linearEquiv z v = _
    simp [r, s, e₁]

end ComplexBundle

end AtiyahSinger
