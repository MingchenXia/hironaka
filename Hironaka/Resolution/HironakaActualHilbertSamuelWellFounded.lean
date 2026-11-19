import Hironaka.Resolution.HironakaActualFormalStandardMonomialHS
import Hironaka.Resolution.HironakaUpwardDiagramWellQuasiOrder
import Mathlib.Order.WellQuasiOrder

/-! The pointwise termination order of genuine entire Hilbert--Samuel profiles.
Actual initial diagrams, genuine standard-monomial cardinalities and the
proved upward-diagram well quasi order produce the order unconditionally. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHilbertSamuelWellFounded
noncomputable section
open HolGerm HironakaHolomorphicPointJets
  HironakaActualOriginalFormalTaylor HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
  HironakaUpwardDiagramWellQuasiOrder

variable {n : ℕ}

/-- The actual initial diagram in the literal finite-function exponent model. -/
def actualDiagram (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Diagram n :=
  ⟨{a | Finsupp.equivFunOnFinite.symm a ∈ actualInitialDiagram MonomialOrder.degLex I}, by
    intro a b hab ha
    apply actualInitialDiagram_upper MonomialOrder.degLex I _ _ ha
    intro i
    exact hab i⟩

/-- Reverse inclusion of the genuine diagrams gives the pointwise original
HS inequality by the identity map on EVERY bounded standard exponent. -/
theorem actual_hilbertSamuel_le_of_diagram_subset
    (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (h : (actualDiagram J).val ⊆ (actualDiagram I).val) :
    genuineFormalHilbertSamuelValue n I ≤ genuineFormalHilbertSamuelValue n J := by
  have hsub : actualInitialDiagram MonomialOrder.degLex J ⊆
      actualInitialDiagram MonomialOrder.degLex I := by
    intro a ha
    have hm : Finsupp.equivFunOnFinite a ∈ (actualDiagram J).val := by
      simpa only [actualDiagram, mem_ofPred_eq, Equiv.symm_apply_apply] using ha
    have hi := h hm
    simpa only [actualDiagram, mem_ofPred_eq, Equiv.symm_apply_apply] using hi
  intro ℓ
  let f : actualStandardIndex n I (ℓ+1) → actualStandardIndex n J (ℓ+1) :=
    fun a => ⟨a.val, fun ha => a.property (hsub ha)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun c : actualStandardIndex n J (ℓ+1) => c.val) hab
  rw [genuineFormalHilbertSamuelValue_eq_card_standardIndex,
    genuineFormalHilbertSamuelValue_eq_card_standardIndex]
  exact Fintype.card_le_of_injective f hf

/-- Only profiles realized by an ACTUAL whole formal ideal occur in this type. -/
abbrev ActualHilbertSamuelProfile (n : ℕ) :=
  {H : ℕ → ℕ // ∃ I : Ideal (MvPowerSeries (Fin n) ℂ),
    H = genuineFormalHilbertSamuelValue n I}

/-- The ACTUAL realizable entire formal profiles are well quasi ordered by
the pointwise order; no caller supplies an order or diagram certificate. -/
theorem actual_hilbertSamuel_wellQuasiOrdered (n : ℕ) :
    WellQuasiOrdered ((· ≤ ·) : ActualHilbertSamuelProfile n → ActualHilbertSamuelProfile n → Prop) := by
  intro H
  choose I hI using fun j => (H j).property
  obtain ⟨i,j,hij,hsub⟩ := upward_diagram_wellQuasiOrdered n (fun j => actualDiagram (I j))
  refine ⟨i,j,hij,?_⟩
  change (H i).val ≤ (H j).val
  rw [hI i,hI j]
  exact actual_hilbertSamuel_le_of_diagram_subset (I i) (I j) hsub

/-- Strict pointwise descent of ACTUAL full profiles is well founded. -/
theorem actual_hilbertSamuel_wellFounded (n : ℕ) :
    WellFoundedLT (ActualHilbertSamuelProfile n) := by
  let : WellQuasiOrderedLE (ActualHilbertSamuelProfile n) :=
    ⟨actual_hilbertSamuel_wellQuasiOrdered n⟩
  infer_instance

/-- The EXISTING analytic profile is realized by the WHOLE actual Taylor
extension, with the same values at every order. -/
theorem analytic_hilbertSamuel_realizable (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ K : Ideal (MvPowerSeries (Fin n) ℂ),
      hilbertSamuelValue I = genuineFormalHilbertSamuelValue n K := by
  have h : ∀ J : Ideal (HolGerm (ComplexModel (0+n))),
      ∃ K : Ideal (MvPowerSeries (Fin n) ℂ),
        hilbertSamuelValue J = genuineFormalHilbertSamuelValue n K := by
    intro J
    exact ⟨_,funext (hilbertSamuelValue_eq_genuine_formal_extension n J)⟩
  rw [Nat.zero_add] at h
  exact h I

/-- No actual sequence of formal ideals has infinitely strictly decreasing
ENTIRE original profiles in the pointwise order. -/
theorem no_strictAnti_actual_hilbertSamuel (I : ℕ → Ideal (MvPowerSeries (Fin n) ℂ)) :
    ¬ StrictAnti (fun j => genuineFormalHilbertSamuelValue n (I j)) := by
  intro hanti
  let H : ℕ → ActualHilbertSamuelProfile n :=
    fun j => ⟨genuineFormalHilbertSamuelValue n (I j),I j,rfl⟩
  obtain ⟨i,j,hij,hle⟩ := actual_hilbertSamuel_wellQuasiOrdered n H
  exact (hanti hij).not_ge hle

/-- The SAME no-descent statement for genuine analytic ideals follows by
their whole original Taylor extensions, at EVERY original order. -/
theorem no_strictAnti_analytic_hilbertSamuel (I : ℕ → Ideal (HolGerm (ComplexModel n))) :
    ¬ StrictAnti (fun j => hilbertSamuelValue (I j)) := by
  choose K hK using fun j => analytic_hilbertSamuel_realizable (I j)
  intro hanti
  apply no_strictAnti_actual_hilbertSamuel K
  simpa only [←hK] using hanti

end
end Hironaka.HironakaActualHilbertSamuelWellFounded
