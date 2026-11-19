import Hironaka.Algebra.PluckerQuotTransitionPrincipalPivot
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maximal

/-!
# SAME actual original quotient has a finite principal pivot cover

The actual original selected-column maps are retained. Their invertibility
is produced, together with the original unit-ideal span and exact rank.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w

variable {A : Type u} [CommRing A]
  {M : Type v} [AddCommGroup M] [Module A M]
  [Module.FinitePresentation A M] [Module.Flat A M]
  {E : Type w} [Fintype E] [DecidableEq E]

/-- SAME actual original quotient has finitely many principal unit-ideal generators on which ORIGINAL rank-r column subfamilies give actual native bijective maps. -/
theorem originalQuotient_exists_finitePrincipalPivotCover (q : (E → A) →ₗ[A] M)
    (hq : Function.Surjective q) (r : ℕ)
    (hr : ∀ p, Module.rankAtStalk (R := A) M p = r) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ g ∈ s, ∃ (I : Type w) (_ : Finite I) (a : I ↪ E),
        Nat.card I = r ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers g)
          (Finsupp.linearCombination A (fun i : I => q (Pi.single (a i) (1 : A))))) := by
  classical
  let G : Set A := {g | ∃ (I : Type w) (_ : Finite I) (a : I ↪ E),
    Nat.card I = r ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers g)
      (Finsupp.linearCombination A (fun i : I => q (Pi.single (a i) (1 : A)))))}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span G) h
    let p : PrimeSpectrum A := ⟨m, hm.isPrime⟩
    obtain ⟨I, hI, a, g, hg, hcard, hgc⟩ := originalQuotient_exists_principalPivot q hq p
    have hgG : g ∈ G := ⟨I, hI, a, hcard.trans (hr p), hgc⟩
    exact hg (hle (Ideal.subset_span hgG))
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite G).mp hG
  exact ⟨s, hspan, fun g hg => hs hg⟩

end Hironaka.Algebra.PluckerQuotTransition
