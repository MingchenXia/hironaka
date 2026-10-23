import DeJongAlterations.StableModification.Valuation.Composition
import DeJongAlterations.StableModification.RiemannZariski.Scheme
import DeJongAlterations.StableModification.ValuationRing.FibreDimension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Composite valuations centred on a chain of points

Let `R` be a local ring, `𝔭 ⊂ R` a prime and `g : R → L` a ring homomorphism to a field whose
kernel is contained in `𝔭`. Then there are valuation rings `W ⊆ A` of `L` such that `W` dominates
`R` and `A` dominates `R_𝔭`; `W` is composed from `A` and a valuation ring of `κ(A)`. For an
integral scheme `T` with function field `K ⊆ L` and a specialization `t ⤳ s`, this gives a
valuation ring `W` of `L` and a morphism `Spec W → T` extending `Spec L → Spec K → T` that sends
the closed point of `Spec W` to `s` and the prime `𝔪_A ∩ W` to `t`: the centre map of `W` passes
through the chain `η ⤳ t ⤳ s`.

This is Temkin's composition of valuations (*Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), Lemma 2.1.4 `composlem`, `semi-stable.tex` lines 1955–1983) in the
form needed for specialization arguments on the base: points of `RZ_{K^s}(S)` (lines 3312–3316)
whose centre map passes through a given chain. Temkin's own proof of the constructibility in
Lemma 5.1(ii) (lines 3282–3310) uses EGA IV 9.7; in the route followed here the
specialization-closedness of the non-stable locus is instead deduced from the valuation-ring case
along such composite valuations. The composition itself is `Valuation.compose` of
`Valuation/Composition.lean`. Blueprint chapter `sm-valuation-geometry.tex`, node
`lem:sm-composite-chain`.

## Main results

* `exists_valuationSubring_dominating`: a valuation ring dominating the image of a local ring,
  in terms of nonunits.
* `exists_valuationSubring_le_centre`: the algebraic statement, with `W = compose A B`.
* `exists_ofScheme_centre_chain`: for an integral scheme `T`, a specialization `t ⤳ s` and a
  field `L` over the function field of `T`, a point `V ∈ RZ_L(T)` with an extension
  `Spec V → T` mapping the closed point to `s` and some point to `t`.
-/

noncomputable section

open IsLocalRing

universe u

namespace DeJongAlterations.StableModification.ValuationRing

open DeJongAlterations.StableModification.Valuation
  (compose compose_le mem_compose valuation_compose_lt_one_iff)

section Algebra

variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]

/-- A ring homomorphism from a local ring to a field factors through a valuation ring of the
field dominating the source (`exists_valuationSubring_dominates`), in terms of nonunits. -/
theorem exists_valuationSubring_dominating {R' : Type*} [CommRing R'] [IsLocalRing R']
    {F : Type*} [Field F] (g : R' →+* F) :
    ∃ W : ValuationSubring F, (∀ r, g r ∈ W) ∧ ∀ r, g r ∈ W.nonunits ↔ r ∈ maximalIdeal R' := by
  obtain ⟨W, hle, hlt⟩ := exists_valuationSubring_dominates g
  exact ⟨W, fun r ↦ (W.valuation_le_one_iff _).mp (hle r),
    fun r ↦ (ValuationSubring.mem_nonunits_iff W).trans (hlt r)⟩

/-- **Composite valuations centred on a chain** (Temkin, Lemma 2.1.4). Let `R` be a local ring,
`𝔭` a prime of `R` and `g : R → L` a ring homomorphism to a field with `ker g ⊆ 𝔭`. There are
valuation rings `W ⊆ A` of `L` such that `W` contains `g(R)` with centre the maximal ideal of
`R`, `A` has centre `𝔭` on `R`, and `W` is composed from `A` and a valuation ring of `κ(A)`. -/
theorem exists_valuationSubring_le_centre (g : R →+* L) (p : Ideal R) [p.IsPrime]
    (hp : RingHom.ker g ≤ p) :
    ∃ (A : ValuationSubring L) (B : ValuationSubring (ResidueField A)),
      (∀ r, g r ∈ compose A B) ∧
        (∀ r, g r ∈ (compose A B).nonunits ↔ r ∈ maximalIdeal R) ∧
          ∀ r, g r ∈ A.nonunits ↔ r ∈ p := by
  -- `A` dominates `R_𝔭`
  have hu : ∀ y : p.primeCompl, IsUnit (g y) := by
    rintro ⟨y, hy⟩
    refine IsUnit.mk0 _ fun h0 ↦ hy (hp h0)
  let gp : Localization.AtPrime p →+* L := IsLocalization.lift (M := p.primeCompl) hu
  have hgp : ∀ r : R, gp (algebraMap R (Localization.AtPrime p) r) = g r :=
    IsLocalization.lift_eq hu
  obtain ⟨A, hA, hAc⟩ := exists_valuationSubring_dominating gp
  have hgA : ∀ r, g r ∈ A := fun r ↦ hgp r ▸ hA _
  have hAp : ∀ r, g r ∈ A.nonunits ↔ r ∈ p := by
    intro r
    rw [← hgp, hAc, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p]
  -- `B` dominates the image of `R` in `κ(A)`
  let gA : R →+* ResidueField A := (residue A).comp (g.codRestrict A.toSubring hgA)
  obtain ⟨B, hB, hBc⟩ := exists_valuationSubring_dominating gA
  refine ⟨A, B, fun r ↦ mem_compose.mpr ⟨hgA r, hB r⟩, fun r ↦ ?_, hAp⟩
  have hval := valuation_compose_lt_one_iff A B (⟨g r, hgA r⟩ : A)
  rw [← hBc, ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff]
  exact hval

end Algebra

section Scheme

open AlgebraicGeometry CategoryTheory

variable {T : Scheme.{u}} [IsIntegral T]

/-- **Composite valuations centred on a chain of points.** Let `T` be an integral scheme with
function field `K`, let `L` be a field extension of `K`, `η : Spec L → T` the induced morphism and
`t ⤳ s` a specialization in `T`. There is a valuation ring `V` of `L` with a morphism
`φ : Spec V → T` extending `η` (so `V ∈ RZ_L(T)`) which maps the closed point of `Spec V` to `s`
and some point of `Spec V` to `t`. -/
theorem exists_ofScheme_centre_chain (L : Type u) [Field L] [Algebra T.functionField L]
    {t s : T} (hts : t ⤳ s) :
    ∃ (V : RiemannZariskiSpace L) (φ : Spec (.of V.valuationSubring) ⟶ T),
      RiemannZariskiSpace.toSpecValuationSubring V ≫ φ =
          Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
            T.fromSpecStalk (genericPoint T) ∧
        φ (RiemannZariskiSpace.specClosedPoint V) = s ∧ ∃ P, φ P = t := by
  -- the prime of `𝒪_{T,s}` corresponding to `t`
  obtain ⟨q, hq⟩ : t ∈ Set.range (T.fromSpecStalk s) := by
    rw [Scheme.range_fromSpecStalk]
    exact hts
  have hgen : genericPoint T ⤳ s := genericPoint_specializes s
  let g : T.presheaf.stalk s →+* L :=
    (algebraMap T.functionField L).comp (algebraMap (T.presheaf.stalk s) T.functionField)
  have hg : Function.Injective g :=
    (algebraMap T.functionField L).injective.comp
      (IsFractionRing.injective (T.presheaf.stalk s) T.functionField)
  have hker : RingHom.ker g ≤ q.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot g).mp hg]
    exact bot_le
  have hqp : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨A, B, hW, hWc, hAc⟩ := exists_valuationSubring_le_centre g q.asIdeal hker
  set W := compose A B with hWdef
  let V : RiemannZariskiSpace L := ⟨W⟩
  let ψ : T.presheaf.stalk s →+* W := g.codRestrict W.toSubring hW
  have hψloc : IsLocalHom ψ := by
    refine ⟨fun r hr ↦ ?_⟩
    by_contra hnu
    have : g r ∈ W.nonunits := (hWc r).mpr ((mem_maximalIdeal r).mpr hnu)
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ψ r)).mp this hr
  let φ : Spec (.of V.valuationSubring) ⟶ T :=
    Spec.map (CommRingCat.ofHom ψ) ≫ T.fromSpecStalk s
  -- the prime `𝔪_A ∩ W` of `W`
  let P : Ideal W := (maximalIdeal A).comap
    ((Subring.inclusion (compose_le A B)) : W →+* A)
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨V, φ, ?_, ?_, ⟨⟨P, hPprime⟩, ?_⟩⟩
  · -- `φ` extends `η`
    have hcomp : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap W L) =
        T.presheaf.stalkSpecializes hgen ≫ CommRingCat.ofHom (algebraMap T.functionField L) := by
      ext r
      rfl
    have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen
    calc RiemannZariskiSpace.toSpecValuationSubring V ≫ φ
        = Spec.map (CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap W L)) ≫
            T.fromSpecStalk s := by
          rw [Spec.map_comp, Category.assoc]
      _ = Spec.map (T.presheaf.stalkSpecializes hgen ≫
            CommRingCat.ofHom (algebraMap T.functionField L)) ≫ T.fromSpecStalk s := by
          rw [hcomp]
      _ = _ := by
          erw [Spec.map_comp, Category.assoc, h2]
          rfl
  · -- the closed point goes to `s`
    change T.fromSpecStalk s (Spec.map (CommRingCat.ofHom ψ) (closedPoint W)) = s
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  · -- the prime `𝔪_A ∩ W` goes to `t`
    change T.fromSpecStalk s (Spec.map (CommRingCat.ofHom ψ) ⟨P, hPprime⟩) = t
    rw [← hq]
    congr 1
    apply PrimeSpectrum.ext
    ext r
    change ψ r ∈ P ↔ r ∈ q.asIdeal
    rw [← hAc r]
    change (⟨g r, compose_le A B (hW r)⟩ : A) ∈ maximalIdeal A ↔ _
    rw [← ValuationSubring.coe_mem_nonunits_iff]

end Scheme

end DeJongAlterations.StableModification.ValuationRing
