/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Smooth.Basic
import Hironaka.Algebra.Local.Coords
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.Field

/-!
# A coefficient field of the completion

Kollár identifies `Ô_{p,X}` with `k(p)⟦x₁, …, xₙ⟧` [Kol07, Definition 55]; the first step is a
*coefficient field*: a subfield `k' ⊆ R̂` mapping isomorphically onto the residue field
`K = R̂/𝔪R̂ = R/𝔪`.  Kollár obtains it for `K/k` finite by Hensel's lemma; the route taken here,
valid for every residue field of characteristic zero, uses formal smoothness: in characteristic
zero every field extension `K/ℚ` is separably generated, hence formally smooth over `ℚ`
(`Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable` applied to a transcendence
basis; [Sta, Tag 0322]), and a formally smooth algebra lifts along the surjection `R̂ → R̂/𝔪R̂` of
the `𝔪R̂`-adically complete ring `R̂`
(`Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`).  The lift `K → R̂` of the
identification `K = R/𝔪 ≅ R̂/𝔪R̂` is the coefficient field.

This confines the route to regular local rings containing `ℚ` (`[Algebra ℚ R]`), the
equicharacteristic-zero case of the sources.  The Cohen structure theorem itself
(`Hironaka/Algebra/Local/CohenMap.lean`, `Cohen.lean`, `CohenIso.lean`) is stated for an arbitrary
coefficient field, `IsCoefficientAlgebra R` below, because the completed chart map
(`Hironaka/Algebra/Local/ChartCompletion.lean`) needs it for the coefficient field of the chart's
local ring transported from that of `R̂`; the `ℚ`-hypothesis is used only to produce one
(`coefficientField`).
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

/-- A field of characteristic zero is formally smooth over `ℚ`, being separably generated
([Sta, Tag 0322]): algebraic extensions in characteristic zero are separable. -/
theorem formallySmooth_rat_of_field (K : Type*) [Field K] [Algebra ℚ K] :
    Algebra.FormallySmooth ℚ K := by
  have : FaithfulSMul ℚ K :=
    (faithfulSMul_iff_algebraMap_injective ℚ K).mpr (algebraMap ℚ K).injective
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' ℚ K
  have : Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range v)) K := hv.isAlgebraic_field
  have : CharZero (IntermediateField.adjoin ℚ (Set.range v)) :=
    (algebraMap (IntermediateField.adjoin ℚ (Set.range v)) K).charZero
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hv.1

section Completion

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

local notation "R̂" => AdicCompletion (maximalIdeal R) R

/-- The residue field of `R̂` is that of `R`, as a ring isomorphism. -/
noncomputable def residueFieldEquiv : ResidueField R ≃+* ResidueField R̂ :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R R̂))
    (AdicCompletion.residueField_map_bijective R)

/-- A *coefficient field* of `R̂` (Kollár's "field of representatives", [Kol07, Definition 55]) is
a subfield mapping isomorphically onto the residue field `K = R̂/𝔪R̂ = R/𝔪`.  Here it is a
`K`-algebra structure on `R̂` which is a section of the residue map (any such structure; one
exists for `ℚ ⊆ R`, `coefficientField` below).  The Cohen structure theorem is stated for an
arbitrary coefficient field because the completed chart map needs it for the coefficient field
of `R'_{𝔪'}` transported from that of `R̂`. -/
abbrev IsCoefficientAlgebra [Algebra (ResidueField R) R̂] : Prop :=
  ∀ k, residue R̂ (algebraMap (ResidueField R) R̂ k) = residueFieldEquiv R k

/-- Every element of `R̂` is a constant from the coefficient field plus an element of `𝔪R̂`:
`R̂ = σ(K) + 𝔪R̂`, for any coefficient field. -/
theorem sub_algebraMap_mem_maximalIdeal [Algebra (ResidueField R) R̂]
    (hι : IsCoefficientAlgebra R) (y : R̂) :
    y - algebraMap (ResidueField R) R̂ ((residueFieldEquiv R).symm (residue R̂ y)) ∈
      maximalIdeal R̂ := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  change residue R̂ y =
    residue R̂ (algebraMap (ResidueField R) R̂ ((residueFieldEquiv R).symm (residue R̂ y)))
  rw [hι, RingEquiv.apply_symm_apply]

variable [Algebra ℚ R]

/-- A coefficient field of `R̂` exists — a ring map `K → R̂` from the residue field which is a
section of the residue map `R̂ → R̂/𝔪R̂ = K` — when `R` contains `ℚ`. -/
theorem exists_coefficientField :
    ∃ σ : ResidueField R →+* R̂, ∀ k, residue R̂ (σ k) = residueFieldEquiv R k := by
  have := formallySmooth_rat_of_field (ResidueField R)
  let f : ResidueField R →ₐ[ℚ] R̂ ⧸ maximalIdeal R̂ :=
    { toRingHom := (residueFieldEquiv R : ResidueField R →+* ResidueField R̂)
      commutes' := fun q => RingHom.map_rat_algebraMap _ q }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
    (R := ℚ) (A := ResidueField R) (S := R̂) (I := maximalIdeal R̂) f
  refine ⟨g.toRingHom, fun k => ?_⟩
  have h := congrArg (fun φ => φ k) hg
  exact h

/-- A chosen coefficient field `σ : K → R̂`. -/
noncomputable def coefficientField : ResidueField R →+* R̂ :=
  Classical.choose (exists_coefficientField R)

theorem residue_coefficientField (k : ResidueField R) :
    residue R̂ (coefficientField R k) = residueFieldEquiv R k :=
  Classical.choose_spec (exists_coefficientField R) k

/-- Every element of `R̂` is a constant from the coefficient field plus an element of `𝔪R̂`:
`R̂ = σ(K) + 𝔪R̂`. -/
theorem sub_coefficientField_mem_maximalIdeal (y : R̂) :
    y - coefficientField R ((residueFieldEquiv R).symm (residue R̂ y)) ∈ maximalIdeal R̂ := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  change residue R̂ y = residue R̂ (coefficientField R ((residueFieldEquiv R).symm (residue R̂ y)))
  rw [residue_coefficientField, RingEquiv.apply_symm_apply]

end Completion

end IsLocalRing
