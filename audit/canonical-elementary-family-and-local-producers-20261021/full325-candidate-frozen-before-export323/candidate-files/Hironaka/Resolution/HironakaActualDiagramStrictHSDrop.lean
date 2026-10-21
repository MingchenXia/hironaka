/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalStandardMonomialHS

/-!
# Actual initial-diagram additions force finite strict HS progress

The actual diagram inclusion is an explicit natural premise. Whole normalized
ideal equality alone is not asserted to supply it or a vertex-order criterion.
Blueprint: `hironaka-actual-diagram-strict-hs-drop-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualDiagramStrictHSDrop
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualFormalStandardMonomialHS HironakaActualOriginalFormalHSTransfer
  HironakaActualOriginalFormalTaylor HironakaHolomorphicJetMonomialSpan HironakaHolomorphicPointJets
variable {n : ℕ}

/-- A literal bounded diagram identity gives an actual equivalence of the
finite original standard-monomial indices, hence the same true HS value. -/
theorem genuineFormalHilbertSamuelValue_eq_of_bounded_diagram_eq
    (I J : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ)
    (h : ∀ β : Fin n →₀ ℕ, normalExponentDegree β ≤ ℓ →
      (β ∈ actualInitialDiagram MonomialOrder.degLex I ↔ β ∈ actualInitialDiagram MonomialOrder.degLex J)) :
    genuineFormalHilbertSamuelValue n I ℓ = genuineFormalHilbertSamuelValue n J ℓ := by
  let E : actualStandardIndex n I (ℓ+1) ≃ actualStandardIndex n J (ℓ+1) :=
    { toFun := fun a => ⟨a.val,fun ha => a.property ((h a.val.val (by have := a.val.property; omega)).mpr ha)⟩
      invFun := fun a => ⟨a.val,fun ha => a.property ((h a.val.val (by have := a.val.property; omega)).mp ha)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [genuineFormalHilbertSamuelValue_eq_card_standardIndex,
    genuineFormalHilbertSamuelValue_eq_card_standardIndex]
  exact Fintype.card_congr E

/-- A true extra initial exponent gives an explicit strict original finite-jet value drop. -/
theorem genuineFormalHilbertSamuelValue_strict_lt_of_new_diagram_exponent
    (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (hsub : actualInitialDiagram MonomialOrder.degLex I ⊆ actualInitialDiagram MonomialOrder.degLex J)
    (β : Fin n →₀ ℕ) (hβJ : β ∈ actualInitialDiagram MonomialOrder.degLex J)
    (hβI : β ∉ actualInitialDiagram MonomialOrder.degLex I) :
    genuineFormalHilbertSamuelValue n J (normalExponentDegree β) <
      genuineFormalHilbertSamuelValue n I (normalExponentDegree β) := by
  let f : actualStandardIndex n J (normalExponentDegree β+1) →
      actualStandardIndex n I (normalExponentDegree β+1) :=
    fun a => ⟨a.val,fun ha => a.property (hsub ha)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : actualStandardIndex n I (normalExponentDegree β+1) => x.val) hab
  have hnsurj : ¬ Function.Surjective f := by
    intro hsurj
    let b : actualStandardIndex n I (normalExponentDegree β+1) := ⟨⟨β,Nat.lt_succ_self _⟩,hβI⟩
    obtain ⟨a,ha⟩ := hsurj b
    have he : a.val.val=β := congrArg (fun x => x.val.val) ha
    exact a.property (he.symm ▸ hβJ)
  rw [genuineFormalHilbertSamuelValue_eq_card_standardIndex,
    genuineFormalHilbertSamuelValue_eq_card_standardIndex]
  exact Fintype.card_lt_of_injective_not_surjective f hinj hnsurj

/-- The least genuine added degree is internally a first strict profile drop. -/
theorem exists_first_hilbertSamuel_drop_of_diagram_ne
    (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (hsub : actualInitialDiagram MonomialOrder.degLex I ⊆ actualInitialDiagram MonomialOrder.degLex J)
    (hne : actualInitialDiagram MonomialOrder.degLex I ≠ actualInitialDiagram MonomialOrder.degLex J) :
    ∃ d : ℕ, (∀ ℓ < d, genuineFormalHilbertSamuelValue n J ℓ = genuineFormalHilbertSamuelValue n I ℓ) ∧
      genuineFormalHilbertSamuelValue n J d < genuineFormalHilbertSamuelValue n I d := by
  have hex : ∃ d : ℕ, ∃ β : Fin n →₀ ℕ,
      β ∈ actualInitialDiagram MonomialOrder.degLex J ∧ β ∉ actualInitialDiagram MonomialOrder.degLex I ∧
      normalExponentDegree β=d := by
    have hd : ∃ β, β ∈ actualInitialDiagram MonomialOrder.degLex J ∧
        β ∉ actualInitialDiagram MonomialOrder.degLex I := by
      by_contra h
      apply hne
      exact Set.Subset.antisymm hsub (fun β hβ => by
        by_contra hβI
        exact h ⟨β,hβ,hβI⟩)
    obtain ⟨β,hβJ,hβI⟩ := hd
    exact ⟨_,β,hβJ,hβI,rfl⟩
  let d := Nat.find hex
  obtain ⟨β,hβJ,hβI,hdeg⟩ := Nat.find_spec hex
  refine ⟨d,?_,?_⟩
  · intro ℓ hℓ
    symm
    apply genuineFormalHilbertSamuelValue_eq_of_bounded_diagram_eq I J ℓ
    intro γ hγ
    refine ⟨fun h => hsub h,?_⟩
    intro hγJ
    by_contra hγI
    have hlt : normalExponentDegree γ < Nat.find hex := by change normalExponentDegree γ<d; omega
    exact Nat.find_min hex hlt ⟨γ,hγJ,hγI,rfl⟩
  · have h := genuineFormalHilbertSamuelValue_strict_lt_of_new_diagram_exponent I J hsub β hβJ hβI
    rw [hdeg] at h
    exact h

/-- With the explicit actual diagram inclusion, equality of ALL genuine values
is equivalent to equality of the WHOLE actual diagrams. -/
theorem genuineFormalHilbertSamuelValue_eq_iff_diagram_eq_of_subset
    (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (hsub : actualInitialDiagram MonomialOrder.degLex I ⊆ actualInitialDiagram MonomialOrder.degLex J) :
    (∀ ℓ, genuineFormalHilbertSamuelValue n J ℓ = genuineFormalHilbertSamuelValue n I ℓ) ↔
      actualInitialDiagram MonomialOrder.degLex I = actualInitialDiagram MonomialOrder.degLex J := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨d,_hprev,hlt⟩ := exists_first_hilbertSamuel_drop_of_diagram_ne I J hsub hne
    rw [h d] at hlt
    exact (lt_irrefl _ hlt)
  · intro he ℓ
    symm
    exact genuineFormalHilbertSamuelValue_eq_of_bounded_diagram_eq I J ℓ (fun β _ => by rw [he])

/-- The same true added exponent forces strict decrease for the ORIGINAL
analytic ideals through their literal WHOLE Taylor extensions. -/
theorem hilbertSamuelValue_strict_lt_of_new_taylor_diagram_exponent
    (A B : Ideal (HolGerm (ComplexModel (0+n))))
    (hsub : actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom A) ⊆
      actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom B))
    (β : Fin n →₀ ℕ)
    (hβB : β ∈ actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom B))
    (hβA : β ∉ actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom A)) :
    hilbertSamuelValue B (normalExponentDegree β) < hilbertSamuelValue A (normalExponentDegree β) := by
  rw [hilbertSamuelValue_eq_genuine_formal_extension,hilbertSamuelValue_eq_genuine_formal_extension]
  exact genuineFormalHilbertSamuelValue_strict_lt_of_new_diagram_exponent _ _ hsub β hβB hβA

/-- Full original analytic profile rigidity is a genuine whole-diagram criterion,
under the disclosed actual Taylor diagram inclusion. -/
theorem hilbertSamuelValue_eq_iff_taylor_diagram_eq_of_subset
    (A B : Ideal (HolGerm (ComplexModel (0+n))))
    (hsub : actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom A) ⊆
      actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom B)) :
    (∀ ℓ, hilbertSamuelValue B ℓ = hilbertSamuelValue A ℓ) ↔
      actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom A) =
      actualInitialDiagram MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom B) := by
  simp only [hilbertSamuelValue_eq_genuine_formal_extension]
  exact genuineFormalHilbertSamuelValue_eq_iff_diagram_eq_of_subset _ _ hsub

end
end Hironaka.HironakaActualDiagramStrictHSDrop
