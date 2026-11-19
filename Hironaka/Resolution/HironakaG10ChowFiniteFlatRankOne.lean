import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite flat algebras of generic rank one

The algebraic step of the Chow-side lemma `chow:flat-bimeromorphic-iso`
(blueprint `hironaka-g10-chowside-flat-iso.tex`): a finite flat algebra whose rank
is `1` at a generization of every maximal ideal has bijective structure map.  In the
geometric application the base ring is the local ring of the target at a point, the
algebra is the stalk of the direct image (finite by the finite mapping theorem), and
rank one at a generic point comes from the isomorphism over a dense open set.

The rank is Mathlib's `Module.rankAtStalk`; constancy of the rank along
specializations of a finite flat module and the characterization of bijectivity by
constant rank one are Mathlib's (`Module.rankAtStalk_eq_of_le_of_finite_of_flat`,
`Module.algebraMap_bijective_iff_rankAtStalk`).

Main declarations:

* `rankAtStalk_eq_one_of_generic` — rank one everywhere from rank one at a generization
  of every maximal ideal.
* `algebraMap_bijective_of_generic_rankAtStalk_eq_one` — the bijectivity statement.
* `algebraMap_bijective_of_isLocalRing_of_finrank_eq_one` — local base, finite flat,
  rank one.
* `algebraMap_bijective_of_free_of_finrank_eq_one` — free of rank one.
* `algebraMap_bijective_of_isLocalRing_of_localizedModule_equiv` — local base, finite
  flat, and the localization at one prime is free of rank one.
-/

set_option autoImplicit false

open Module

namespace Hironaka.HironakaG10ChowFiniteFlatRankOne

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

section FiniteFlat

variable [Module.Flat R S] [Module.Finite R S]

/-- **Rank one spreads by specialization.**  If a finite flat algebra has rank `1` at a
generization of every maximal ideal, it has rank `1` at every prime. -/
theorem rankAtStalk_eq_one_of_generic
    (h : ∀ m : Ideal R, m.IsMaximal →
      ∃ P : PrimeSpectrum R, P.asIdeal ≤ m ∧ rankAtStalk (R := R) S P = 1) :
    rankAtStalk (R := R) S = 1 := by
  funext q
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  obtain ⟨P, hPm, hP⟩ := h m hm
  have hq : rankAtStalk (R := R) S q = rankAtStalk (R := R) S ⟨m, hm.isPrime⟩ :=
    rankAtStalk_eq_of_le_of_finite_of_flat (R := R) S (p := q) (q := ⟨m, hm.isPrime⟩) hqm
  have hPr : rankAtStalk (R := R) S P = rankAtStalk (R := R) S ⟨m, hm.isPrime⟩ :=
    rankAtStalk_eq_of_le_of_finite_of_flat (R := R) S (p := P) (q := ⟨m, hm.isPrime⟩) hPm
  rw [Pi.one_apply, hq, ← hPr, hP]

/-- **Finite flat, generically of rank one ⇒ isomorphism.**  If a finite flat `R`-algebra
`S` has rank `1` at a generization of every maximal ideal of `R`, then `R → S` is
bijective. -/
theorem algebraMap_bijective_of_generic_rankAtStalk_eq_one
    (h : ∀ m : Ideal R, m.IsMaximal →
      ∃ P : PrimeSpectrum R, P.asIdeal ≤ m ∧ rankAtStalk (R := R) S P = 1) :
    Function.Bijective (algebraMap R S) :=
  Module.algebraMap_bijective_of_rankAtStalk (rankAtStalk_eq_one_of_generic h)

/-- Over a local ring, rank one at one prime suffices. -/
theorem algebraMap_bijective_of_isLocalRing_of_rankAtStalk_eq_one [IsLocalRing R]
    (P : PrimeSpectrum R) (hP : rankAtStalk (R := R) S P = 1) :
    Function.Bijective (algebraMap R S) := by
  refine algebraMap_bijective_of_generic_rankAtStalk_eq_one fun m hm => ⟨P, ?_, hP⟩
  rw [IsLocalRing.eq_maximalIdeal hm]
  exact IsLocalRing.le_maximalIdeal P.isPrime.ne_top

/-- Over a local ring, a finite flat algebra of `finrank` one has bijective structure map
(it is free, by `Module.free_of_flat_of_isLocalRing`). -/
theorem algebraMap_bijective_of_isLocalRing_of_finrank_eq_one [IsLocalRing R]
    (h : Module.finrank R S = 1) : Function.Bijective (algebraMap R S) := by
  have : Module.Free R S := Module.free_of_flat_of_isLocalRing
  refine Module.algebraMap_bijective_of_rankAtStalk ?_
  rw [rankAtStalk_eq_finrank_of_free, h]
  rfl

/-- Over a local ring, a finite flat algebra whose localization at one prime `P` is free
of rank one over `R_P` has bijective structure map. -/
theorem algebraMap_bijective_of_isLocalRing_of_localizedModule_equiv [IsLocalRing R]
    (P : Ideal R) [P.IsPrime]
    (e : LocalizedModule P.primeCompl S ≃ₗ[Localization.AtPrime P] Localization.AtPrime P) :
    Function.Bijective (algebraMap R S) := by
  refine algebraMap_bijective_of_isLocalRing_of_rankAtStalk_eq_one ⟨P, inferInstance⟩ ?_
  change Module.finrank (Localization.AtPrime P) (LocalizedModule P.primeCompl S) = 1
  rw [e.finrank_eq, Module.finrank_self]

end FiniteFlat

/-- **Free of rank one ⇒ isomorphism.**  If `S` is a free `R`-module of rank one, then the
structure map `R → S` is bijective. -/
theorem algebraMap_bijective_of_free_of_finrank_eq_one [Nontrivial R] [Module.Free R S]
    [Module.Finite R S] (h : Module.finrank R S = 1) : Function.Bijective (algebraMap R S) := by
  have : Module.Flat R S := inferInstance
  refine Module.algebraMap_bijective_of_rankAtStalk ?_
  rw [rankAtStalk_eq_finrank_of_free, h]
  rfl

/-- The structure map of a free algebra of rank one, as a ring isomorphism. -/
noncomputable def ringEquivOfFreeOfFinrankEqOne [Nontrivial R] [Module.Free R S]
    [Module.Finite R S] (h : Module.finrank R S = 1) : R ≃+* S :=
  RingEquiv.ofBijective (algebraMap R S) (algebraMap_bijective_of_free_of_finrank_eq_one h)

end Hironaka.HironakaG10ChowFiniteFlatRankOne
