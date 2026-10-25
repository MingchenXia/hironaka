import DeJongAlterations.StableModification.Blowups.SeparationCharts
import DeJongAlterations.Geometry.CurveCompactificationRestriction
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Strictly semi-stable curves over a normal base are normal

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of
Proposition 4.3.1 (`cofinprop`, `semi-stable.tex` lines 2963–2966) uses the "normality of
semi-stable `S`-curves with smooth generic fiber" (Proposition 3.5.2). For *strictly* semi-stable
curves, which is all that the cofinality statement needs, normality is elementary: a strictly
semi-stable curve is étale-locally `Spec A[T]` or `Spec A[u,v]/(uv - a)` over an open
`Spec A ⊆ S`; both are normal over an integrally closed domain `A` when `a ≠ 0`
(`Curves.isNormalScheme_of_etale_smoothModel`, `Curves.isNormalScheme_of_etale_nodeModel`), and
étale over normal is normal. For `a = 0` an integral curve cannot meet the origin of the chart
(`Blowups.node_param_ne_zero`), and off the origin the node is étale over `𝔸¹_A`
(`Blowups.hasSmoothChart_of_node`). Blueprint `lem:sm-strictly-semistable-normal`
(`sm-local-uniformization.tex`).

## Main results

* `isDomain_isIntegrallyClosed_stalk_of_isOpenImmersion`: the stalks of `X` at points of an open
  `j : Y ⟶ X` with `Y` normal are integrally closed domains.
* `isDomain_isIntegrallyClosed_of_isOpenImmersion`: if `Spec A` is an open subscheme of an
  integral normal scheme, `A` is an integrally closed domain.
* `isNormalScheme_of_isStrictlySemistable`: **an integral strictly semi-stable curve over an
  integral normal scheme is normal**; `isNormalScheme_of_isStrictlySemistable_spec` for
  `S = Spec R`, `R` an integrally closed domain (e.g. a valuation ring).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Polynomial

universe u

namespace DeJongAlterations.StableModification.LocalUniformization

open Curves Blowups Algebra.NodeBlowupChart

/-- The stalk of `X` at a point of an open immersion `j : Y ⟶ X` with `Y` normal is an integrally
closed domain. -/
theorem isDomain_isIntegrallyClosed_stalk_of_isOpenImmersion {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (hY : IsNormalScheme Y) (y : Y) :
    IsDomain (X.presheaf.stalk (j y)) ∧ IsIntegrallyClosed (X.presheaf.stalk (j y)) := by
  let := (hY y).1
  let := (hY y).2
  let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain e.toRingHom e.injective, IsIntegrallyClosed.of_equiv e.symm⟩

/-- **An open affine of an integral normal scheme has an integrally closed domain as ring of
functions.** -/
theorem isDomain_isIntegrallyClosed_of_isOpenImmersion {S : Scheme.{u}} [IsIntegral S]
    (hS : IsNormalScheme S) {A : Type u} [CommRing A] [Nontrivial A]
    (ι : Spec (.of A) ⟶ S) [IsOpenImmersion ι] : IsDomain A ∧ IsIntegrallyClosed A := by
  have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion ι
  have hA : IsDomain A := (affine_isIntegral_iff (.of A)).mp inferInstance
  refine ⟨hA, ?_⟩
  have hn : IsNormalScheme (Spec (.of A)) :=
    Geometry.CurveCompactification.isNormalScheme_of_isOpenImmersion ι hS
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP ↦ ?_
  let p : PrimeSpectrum A := ⟨P, hP.isPrime⟩
  let : Algebra A ((Spec (.of A)).presheaf.stalk p) := StructureSheaf.stalkAlgebra A p
  let : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk p) P :=
    StructureSheaf.IsLocalization.to_stalk A p
  let := (hn p).2
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl ((Spec (.of A)).presheaf.stalk p)
      (Localization.AtPrime P)).toRingEquiv

/-- **Integral strictly semi-stable curves over an integral normal base are normal**
(`lem:sm-strictly-semistable-normal`; the strictly semi-stable case of Temkin's
Proposition 3.5.2, used in the proof of Proposition 4.3.1, T:2966). -/
theorem isNormalScheme_of_isStrictlySemistable {S C : Scheme.{u}} [IsIntegral S]
    (hS : IsNormalScheme S) [IsIntegral C] {g : C ⟶ S} {D : C.IdealSheafData}
    (hC : IsStrictlySemistable g D) : IsNormalScheme C := by
  intro x
  obtain ⟨U, hxU, A, _, ι, _, h, hh, hcase⟩ := hC x
  have : Nonempty U.toScheme := ⟨⟨x, hxU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : Nontrivial A := by
    by_contra hA
    rw [not_nontrivial_iff_subsingleton] at hA
    have : IsEmpty (PrimeSpectrum A) := PrimeSpectrum.isEmpty_iff_subsingleton.mpr hA
    exact @IsEmpty.false (PrimeSpectrum A) this (h ⟨x, hxU⟩)
  obtain ⟨hA, hAic⟩ := isDomain_isIntegrallyClosed_of_isOpenImmersion hS ι
  have hx : x = U.ι ⟨x, hxU⟩ := rfl
  rcases hcase with ⟨e, he, -, -⟩ | ⟨a, e, he, hea, -⟩
  · rw [hx]
    exact isDomain_isIntegrallyClosed_stalk_of_isOpenImmersion U.ι
      (isNormalScheme_of_etale_smoothModel A e) _
  · by_cases h0 : coordinate a 0 ∈ (e ⟨x, hxU⟩).asIdeal
    · by_cases h1 : coordinate a 1 ∈ (e ⟨x, hxU⟩).asIdeal
      · have : IsDomain (U.toScheme.presheaf.stalk ⟨x, hxU⟩) := by
          exact AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral
            (X := U.toScheme)
        have ha : a ≠ 0 := node_param_ne_zero a e ⟨x, hxU⟩ h0 h1
        rw [hx]
        exact isDomain_isIntegrallyClosed_stalk_of_isOpenImmersion U.ι
          (isNormalScheme_of_etale_nodeModel ha e) _
      · obtain ⟨Y, j, _, e', _, ⟨y, hy⟩, -⟩ :=
          hasSmoothChart_of_node h (𝟙 _) a e (by rw [hea, Category.id_comp]) ⟨x, hxU⟩ 1 h1
        have hxy : x = (j ≫ U.ι) y := by
          rw [Scheme.Hom.comp_apply, hy]
          rfl
        rw [hxy]
        exact isDomain_isIntegrallyClosed_stalk_of_isOpenImmersion (j ≫ U.ι)
          (isNormalScheme_of_etale_smoothModel A e') _
    · obtain ⟨Y, j, _, e', _, ⟨y, hy⟩, -⟩ :=
        hasSmoothChart_of_node h (𝟙 _) a e (by rw [hea, Category.id_comp]) ⟨x, hxU⟩ 0 h0
      have hxy : x = (j ≫ U.ι) y := by
        rw [Scheme.Hom.comp_apply, hy]
        rfl
      rw [hxy]
      exact isDomain_isIntegrallyClosed_stalk_of_isOpenImmersion (j ≫ U.ι)
        (isNormalScheme_of_etale_smoothModel A e') _

/-- **Integral strictly semi-stable curves over an integrally closed domain are normal**; this
applies to every valuation ring `R` (`lem:sm-strictly-semistable-normal`). -/
theorem isNormalScheme_of_isStrictlySemistable_spec {R : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] {C : Scheme.{u}} [IsIntegral C] {g : C ⟶ Spec (.of R)}
    {D : C.IdealSheafData} (hC : IsStrictlySemistable g D) : IsNormalScheme C :=
  isNormalScheme_of_isStrictlySemistable (isNormalScheme_spec R) hC

end DeJongAlterations.StableModification.LocalUniformization
