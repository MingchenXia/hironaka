/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import DeJongAlterations.StableModification.CurvesField.AmpleAffine

/-!
# Quasi-finiteness around a fibre

Blueprint `sm-projectivity-relative.tex`, `lem:sm-ltg-nonconstant` (PLAN-OM3 §3 step 4). Three
inputs of the finiteness step of the local-to-global theorem:

* (`quasiFiniteAt_of_finite`) a morphism locally of finite type is quasi-finite at every point
  of a finite fibre (the fibre is a finite scheme of finite type over a field, hence discrete);
* (`finite_preimage_of_separating`) on a Noetherian space of dimension at most one, a continuous
  map `g` sending closed points to closed points has finite fibres if some set `D` respected by
  `g` contains every non-closed point and misses a specialization of each of them (the
  non-vanishing locus of a section with a zero on every one-dimensional component);
* (`exists_open_quasiFiniteAt`) for `Ψ` over a proper `β`, quasi-finiteness of `Ψ` at all points of
  the fibre over `y` spreads to the preimage of a neighbourhood of `y` (the quasi-finite locus is
  open, Mathlib's `Scheme.Hom.isOpen_quasiFiniteAt`, and `β` is closed).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism locally of finite type is quasi-finite at a point whose fibre is finite. -/
theorem quasiFiniteAt_of_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hfin : (f ⁻¹' {f x}).Finite) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hF : Finite (f.fiber (f x)) := by
    have := hfin.to_subtype
    exact Finite.of_equiv _ (f.fiberHomeo (f x)).symm.toEquiv
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyQuasiFinite (f.fiberToSpecResidueField (f x)) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have : IsLocallyArtinian (f.fiber (f x)) := IsLocallyArtinian.of_locallyQuasiFinite
    (f.fiberToSpecResidueField (f x))
  exact isOpen_discrete _

/-- **Finite fibres from a separating set** (the topological core of `lem:sm-ltg-nonconstant`): let
`T` be a Noetherian quasi-sober space without chains `x ⤳ y ⤳ z` of three distinct points and
`g : T → P` continuous, sending closed points to closed points. Let `D ⊆ T` be a set with
`g x = g x' → (x ∈ D ↔ x' ∈ D)` which contains every non-closed point and misses a specialization
of each of them. Then the fibres of `g` are finite. -/
theorem finite_preimage_of_separating {T P : Type*} [TopologicalSpace T] [TopologicalSpace P]
    [QuasiSober T] [NoetherianSpace T] (hdim : ∀ x y z : T, x ⤳ y → y ⤳ z → x = y ∨ y = z)
    (g : T → P) (hg : Continuous g)
    (hcl : ∀ x, IsClosed ({x} : Set T) → IsClosed ({g x} : Set P)) (D : Set T)
    (hD : ∀ x x', g x = g x' → (x ∈ D ↔ x' ∈ D))
    (hgen : ∀ η, ¬ IsClosed ({η} : Set T) → η ∈ D)
    (hzero : ∀ η, ¬ IsClosed ({η} : Set T) → ∃ z, η ⤳ z ∧ z ∉ D) (q : P) :
    (g ⁻¹' {q}).Finite := by
  by_cases hq : ∃ x ∈ g ⁻¹' {q}, IsClosed ({x} : Set T)
  · obtain ⟨x₀, hx₀, hx₀cl⟩ := hq
    have hqcl : IsClosed ({q} : Set P) := by
      have := hcl x₀ hx₀cl
      rwa [show g x₀ = q from hx₀] at this
    have hK : IsClosed (g ⁻¹' {q}) := hqcl.preimage hg
    refine CurvesField.Ample.finite_of_forall_isClosed_singleton hK fun η hη => ?_
    by_contra hηcl
    obtain ⟨z, hηz, hz⟩ := hzero η hηcl
    have hzK : z ∈ g ⁻¹' {q} := hηz.mem_closed hK hη
    have : g η = g z := (show g η = q from hη).trans (show g z = q from hzK).symm
    exact hz ((hD η z this).mp (hgen η hηcl))
  · push Not at hq
    exact (CurvesField.Ample.finite_setOf_not_isClosed hdim).subset fun x hx => hq x hx

/-- **The quasi-finite locus around a fibre**: if `Ψ : X ⟶ P` (locally of finite type) is
quasi-finite at every point of the fibre of a proper `β : X ⟶ Y` over `y`, it is quasi-finite at
every point over a neighbourhood of `y`. -/
theorem exists_open_quasiFiniteAt {X Y P : Scheme.{u}} (β : X ⟶ Y) [IsProper β] (Ψ : X ⟶ P)
    [LocallyOfFiniteType Ψ] (y : Y) (h : ∀ x, β x = y → Ψ.QuasiFiniteAt x) :
    ∃ O : Y.Opens, y ∈ O ∧ ∀ x, β x ∈ O → Ψ.QuasiFiniteAt x := by
  have hC : IsClosed (β '' (Ψ.quasiFiniteLocus : Set X)ᶜ) :=
    β.isClosedMap _ Ψ.quasiFiniteLocus.isOpen.isClosed_compl
  refine ⟨⟨(β '' (Ψ.quasiFiniteLocus : Set X)ᶜ)ᶜ, hC.isOpen_compl⟩, ?_, fun x hx => ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (h x hxy)
  · by_contra hq
    exact hx ⟨x, hq, rfl⟩

end

end DeJongAlterations.StableModification.Projectivity
