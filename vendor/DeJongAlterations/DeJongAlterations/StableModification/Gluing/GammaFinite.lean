/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45A)
-/
import DeJongAlterations.StableModification.LocalUniformization.Cofinal
import DeJongAlterations.StableModification.LocalUniformization.Curve

/-!
# `Γ(C')` is finite for every modification of a curve over a valuation ring

Let `O` be a valuation ring of finite height of a field `K`, `φ : C → Spec O` an integral, flat,
quasi-compact relative curve locally of finite type, `L = K(C)`, and `f : C' → C` a modification.
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Lemma 4.2.2
(`gamlem`, `semi-stable.tex` lines 2904–2928) states that the sets `Γ(C')` (valuations of `L`
centred at points of `(C'/S)⁰`) and `Γ₀(C')` are finite when `C'` is **normal**: then every
`x' ∈ (C'/S)⁰` carries exactly one valuation. Temkin's proof of Proposition 4.3.1 (T:2961–2966)
and of Proposition 4.5.1 (T:3250–3252, "applying to them first Proposition cofinprop") applies the
finiteness to modifications which need not be normal (`ERRATA.md` T41, T62).

This file proves the finiteness for **every** modification (blueprint
`sm-gluing-semistable.tex`, `lem:sm-gamma-finite-projective`; the projectivity hypothesis of the
plan `PLAN-T5.md` node A3 turns out to be unnecessary). For `x' ∈ (C'/S)⁰`:

* `exists_section_transcendental`: there is a section `s` over an open `U ∋ x'` whose residue at
  `x'` is transcendental over `κ(φ f x')`;
* `isResidueTranscendental_of_isCentre`: for every valuation ring `V` of `L` centred at `x'`, the
  image `b ∈ L` of `s` lies in `V` and has residue transcendental over the residue field of
  `V ∩ K` (a Gauss valuation computation, with denominators cleared in the valuation ring `O`,
  `exists_mul_mem_of_forall_mem`);
* `comap_eq_of_isCentre`: all these `V` have the same trace `V ∩ K` (the localization of `O` at
  the prime below `x'`);
* hence they are among the finitely many valuation rings of the finite extension `L / K(b)` lying
  over the Gauss valuation (`LocalUniformization.Curve.finite_setOf_transcendental_residue`),
  `finite_setOf_isCentre`.

Since `(C'/S)⁰` is finite (`ValCurves.finite_fibreGenericSet`, no normality needed), `Γ(C')` and
`Γ₀(C')` are finite (`finite_gammaSet_of_flat`, `finite_gammaZeroSet_of_flat`), and Temkin's
cofinality Proposition 4.3.1 holds for all modifications
(`exists_dominates_isStrictlySemistable_of_isModification`), as Temkin states it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open scoped IntermediateField

universe u

namespace DeJongAlterations.StableModification.Gluing

open ValCurves RiemannZariskiSpace LocalUniformization LocalUniformization.Curve
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Centre

variable {L : Type u} [Field L] {X : Scheme.{u}} {η : Spec (.of L) ⟶ X}

/-- The image in `L` of the germ of a section under the local map at the closed point of an
extension `ψ : Spec V → X` of `η` is the section map of `η`. -/
theorem coe_stalkClosedPointTo_germ {V : RiemannZariskiSpace L}
    (ψ : Spec (.of V.valuationSubring) ⟶ X) (hψ : toSpecValuationSubring V ≫ ψ = η)
    {U : X.Opens} (hx : ψ (closedPoint V.valuationSubring) ∈ U) (hηU : η ⁻¹ᵁ U = ⊤)
    (r : Γ(X, U)) :
    (((Scheme.stalkClosedPointTo ψ).hom (X.presheaf.germ U _ hx r) : V.valuationSubring) : L) =
      sectionsToField η U hηU r := by
  have hψU : ψ ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem ψ hx
  rw [sectionsToField_eq_of_extension ψ hψ hψU hηU]
  have h1 : ψ.appLE U ⊤ hψU.ge ≫ (Scheme.ΓSpecIso (.of V.valuationSubring)).hom =
      X.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo ψ := by
    rw [Scheme.germ_stalkClosedPointTo, Scheme.Hom.appLE]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
    rfl
  rw [RingHom.comp_apply, h1]
  rfl

/-- **Centres and sections.** If `V` is centred at `x ∈ U` (with respect to `η`, which factors
through `U`), the section map `s_U : Γ(X, U) → L` takes values in `V`, and a section vanishes at
`x` iff its image lies in the maximal ideal of `V`. -/
theorem valuation_sectionsToField_of_isCentre {V : RiemannZariskiSpace L} {x : X}
    (h : IsCentre η V x) {U : X.Opens} (hx : x ∈ U) (hηU : η ⁻¹ᵁ U = ⊤) (r : Γ(X, U)) :
    V.valuationSubring.valuation (sectionsToField η U hηU r) ≤ 1 ∧
      (X.presheaf.germ U x hx r ∈ maximalIdeal (X.presheaf.stalk x) ↔
        V.valuationSubring.valuation (sectionsToField η U hηU r) < 1) := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  change ψ (closedPoint V.valuationSubring) ∈ U at hx
  change V.valuationSubring.valuation (sectionsToField η U hηU r) ≤ 1 ∧
    (X.presheaf.germ U (ψ (closedPoint V.valuationSubring)) hx r ∈
      maximalIdeal (X.presheaf.stalk (ψ (closedPoint V.valuationSubring))) ↔
        V.valuationSubring.valuation (sectionsToField η U hηU r) < 1)
  rw [← coe_stalkClosedPointTo_germ ψ hψ hx hηU r]
  refine ⟨V.valuationSubring.valuation_le_one _, ?_⟩
  rw [← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.maximalIdeal_comap
    (Scheme.stalkClosedPointTo ψ).hom, Ideal.mem_comap]

end Centre


section Base

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  {X : Scheme.{u}} {η : Spec (.of L) ⟶ X} (q : X ⟶ Spec (.of O))
  (hq : η ≫ q = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O.subtype)))
include hq

/-- Elements of `O` in the maximal ideal of a centre: `o ∈ q(x)` iff `v(o) < 1`. -/
theorem valuation_algebraMap_of_isCentre {V : RiemannZariskiSpace L} {x : X} (h : IsCentre η V x)
    (o : O) : V.valuationSubring.valuation (algebraMap K L o) ≤ 1 ∧
      (o ∈ (q x).asIdeal ↔ V.valuationSubring.valuation (algebraMap K L o) < 1) :=
  h.ringHom q _ hq o

/-- **The trace on `K` of a centre depends only on the centre**: two valuation rings of `L`
centred at the same point of an `O`-scheme have the same trace on `K` (both are the localization
of `O` at the prime `q(x)`). -/
theorem comap_eq_of_isCentre {V₁ V₂ : RiemannZariskiSpace L} {x : X} (h₁ : IsCentre η V₁ x)
    (h₂ : IsCentre η V₂ x) :
    V₁.valuationSubring.comap (algebraMap K L) = V₂.valuationSubring.comap (algebraMap K L) := by
  have key : ∀ {V : RiemannZariskiSpace L}, IsCentre η V x → ∀ c : K,
      c ∈ V.valuationSubring.comap (algebraMap K L) ↔
        (c ∈ O ∨ ∃ hc : c⁻¹ ∈ O, (⟨c⁻¹, hc⟩ : O) ∉ (q x).asIdeal) := by
    intro V hV c
    rw [ValuationSubring.mem_comap, ← V.valuationSubring.valuation_le_one_iff]
    constructor
    · intro hc
      by_cases hcO : c ∈ O
      · exact Or.inl hcO
      have hinv : c⁻¹ ∈ O := (O.mem_or_inv_mem c).resolve_left hcO
      refine Or.inr ⟨hinv, fun hmem ↦ ?_⟩
      have hlt := (valuation_algebraMap_of_isCentre q hq hV ⟨c⁻¹, hinv⟩).2.mp hmem
      have hc0 : c ≠ 0 := fun h0 ↦ hcO (h0 ▸ O.zero_mem)
      change V.valuationSubring.valuation (algebraMap K L c⁻¹) < 1 at hlt
      rw [map_inv₀, map_inv₀] at hlt
      have hpos : 0 < V.valuationSubring.valuation (algebraMap K L c) := by
        rw [zero_lt_iff]
        simpa using hc0
      have := (one_lt_inv₀ hpos).mpr (lt_of_le_of_ne hc ?_)
      · exact absurd hlt (not_lt.mpr this.le)
      · intro h1
        rw [h1, inv_one] at hlt
        exact lt_irrefl _ hlt
    · rintro (hcO | ⟨hinv, hnot⟩)
      · exact (valuation_algebraMap_of_isCentre q hq hV ⟨c, hcO⟩).1
      · have hge : ¬ V.valuationSubring.valuation (algebraMap K L c⁻¹) < 1 :=
          fun hlt ↦ hnot ((valuation_algebraMap_of_isCentre q hq hV ⟨c⁻¹, hinv⟩).2.mpr hlt)
        have hle : V.valuationSubring.valuation (algebraMap K L c⁻¹) ≤ 1 :=
          (valuation_algebraMap_of_isCentre q hq hV ⟨c⁻¹, hinv⟩).1
        have h1 : V.valuationSubring.valuation (algebraMap K L c⁻¹) = 1 :=
          le_antisymm hle (not_lt.mp hge)
        rw [map_inv₀, map_inv₀, inv_eq_one] at h1
        exact h1.le
  ext c
  rw [key h₁, key h₂]

end Base

section Clear

variable {K L : Type*} [Field K] [Field L] (f : K →+* L) (O : ValuationSubring K)
  (V : ValuationSubring L)

/-- **Clearing denominators over a valuation ring.** If `O ⊆ K` is a valuation ring whose image
lies in `V`, and `s ⊆ K` is a finite set whose image lies in `V`, some `d ∈ O` with `v_V(d) = 1`
has `d • s ⊆ O`. -/
theorem exists_mul_mem_of_forall_mem (hO : ∀ o ∈ O, f o ∈ V) (s : Finset K)
    (hs : ∀ c ∈ s, f c ∈ V) : ∃ d ∈ O, V.valuation (f d) = 1 ∧ ∀ c ∈ s, d * c ∈ O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, O.one_mem, by simp, fun c hc ↦ absurd hc (Finset.notMem_empty c)⟩
  | @insert c s _ ih =>
    obtain ⟨d, hdO, hd1, hds⟩ := ih fun c' hc' ↦ hs c' (Finset.mem_insert_of_mem hc')
    by_cases hcO : c ∈ O
    · refine ⟨d, hdO, hd1, fun c' hc' ↦ ?_⟩
      rcases Finset.mem_insert.mp hc' with rfl | hc'
      · exact mul_mem hdO hcO
      · exact hds c' hc'
    have hinv : c⁻¹ ∈ O := (O.mem_or_inv_mem c).resolve_left hcO
    have hc0 : c ≠ 0 := fun h0 ↦ hcO (h0 ▸ O.zero_mem)
    have hvc : V.valuation (f c) = 1 := by
      have h1 : V.valuation (f c) ≤ 1 := V.valuation_le_one_iff _ |>.mpr (hs c (Finset.mem_insert_self c s))
      have h2 : V.valuation (f c⁻¹) ≤ 1 := V.valuation_le_one_iff _ |>.mpr (hO _ hinv)
      rw [map_inv₀, map_inv₀] at h2
      have hpos : 0 < V.valuation (f c) := by
        rw [zero_lt_iff]
        simpa using hc0
      exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)
    refine ⟨d * c⁻¹, mul_mem hdO hinv, ?_, fun c' hc' ↦ ?_⟩
    · rw [map_mul, map_mul, hd1, map_inv₀, map_inv₀, hvc, inv_one, mul_one]
    · rcases Finset.mem_insert.mp hc' with rfl | hc'
      · rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]
        exact hdO
      · rw [mul_comm d, mul_assoc]
        exact mul_mem hinv (hds c' hc')

end Clear

section Residue

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  {X : Scheme.{u}}

/-- The ring map `O → Γ(X, U)` of an `O`-scheme `q : X → Spec O`. -/
def sectionsRingHom (q : X ⟶ Spec (.of O)) (U : X.Opens) : O →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of O)).inv ≫ q.appLE ⊤ U le_top).hom

/-- The section map of `η` restricted to `O` is the inclusion `O ⊆ K ⊆ L`. -/
theorem sectionsToField_comp_sectionsRingHom {η : Spec (.of L) ⟶ X} (q : X ⟶ Spec (.of O))
    (hq : η ≫ q = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O.subtype)))
    {U : X.Opens} (hηU : η ⁻¹ᵁ U = ⊤) :
    (sectionsToField η U hηU).comp (sectionsRingHom q U) = (algebraMap K L).comp O.subtype := by
  have h1 := sectionsToField_comp_appLE q hq (U := ⊤) (U' := U) le_top hηU rfl
  rw [Curve.sectionsToField_SpecMap_top] at h1
  calc (sectionsToField η U hηU).comp (sectionsRingHom q U)
      = ((sectionsToField η U hηU).comp (q.appLE ⊤ U le_top).hom).comp
          (Scheme.ΓSpecIso (.of O)).inv.hom := rfl
    _ = ((Scheme.ΓSpecIso (.of O)).inv ≫ (Scheme.ΓSpecIso (.of O)).hom ≫
          CommRingCat.ofHom ((algebraMap K L).comp O.subtype)).hom := by
        rw [h1]; rfl
    _ = _ := by rw [Iso.inv_hom_id_assoc]; rfl

/-- The germ at `x` of the image of `o ∈ O` has residue the image of `o` in `κ(q x)`. -/
theorem residue_germ_sectionsRingHom (q : X ⟶ Spec (.of O)) {U : X.Opens} {x : X}
    (hxU : x ∈ U) (o : O) :
    X.residue x (X.presheaf.germ U x hxU (sectionsRingHom q U o)) =
      q.residueFieldMap x ((Spec (.of O)).residue (q x) ((toStalk' (q x)).hom o)) := by
  have h1 : X.presheaf.germ U x hxU (sectionsRingHom q U o) =
      q.stalkMap x ((toStalk' (q x)).hom o) := by
    change X.presheaf.germ U x hxU ((q.app ⊤ ≫ X.presheaf.map (homOfLE _).op)
      ((Scheme.ΓSpecIso (.of O)).inv o)) = _
    rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
    change _ = q.stalkMap x ((Spec (.of O)).presheaf.germ ⊤ (q x) trivial
      ((Scheme.ΓSpecIso (.of O)).inv o))
    rw [Scheme.Hom.germ_stalkMap_apply]
  rw [h1, ← CommRingCat.comp_apply, ← Scheme.residue_residueFieldMap, CommRingCat.comp_apply]

/-- In the stalk of `Spec O` at `p`, the image of `o ∈ O` is in the maximal ideal iff `o ∈ p`. -/
theorem toStalk'_mem_maximalIdeal_iff (p : Spec (.of O)) (o : O) :
    (toStalk' p).hom o ∈ maximalIdeal ((Spec (.of O)).presheaf.stalk p) ↔ o ∈ p.asIdeal := by
  let : Algebra O ((Spec (.of O)).presheaf.stalk p) := StructureSheaf.stalkAlgebra O p
  have hS : IsLocalization.AtPrime ((Spec (.of O)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk O p
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ p.asIdeal o

/-- **A section with transcendental residue.** If `κ(x)` is transcendental over `κ(q x)`, there is
a section `s` over an open `U ∋ x` such that for every `p ∈ O[X]` with leading coefficient not in
`q(x)`, the germ of `p(s)` at `x` is a unit (the residue of `s` is transcendental over `κ(q x)`). -/
theorem exists_section_transcendental (q : X ⟶ Spec (.of O)) {x : X} (hx : fiberTrdeg q x ≠ 0) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (s : Γ(X, U)), ∀ p : O[X], p.leadingCoeff ∉ (q x).asIdeal →
      X.presheaf.germ U x hxU (p.eval₂ (sectionsRingHom q U) s) ∉
        maximalIdeal (X.presheaf.stalk x) := by
  let := (q.residueFieldMap x).hom.toAlgebra
  have hnalg : ¬ Algebra.IsAlgebraic ((Spec (.of O)).residueField (q x)) (X.residueField x) :=
    fun h ↦ hx (trdeg_eq_zero_iff.mpr h)
  rw [Algebra.isAlgebraic_def] at hnalg
  push Not at hnalg
  obtain ⟨tb, htb⟩ := hnalg
  obtain ⟨t₀, rfl⟩ := X.residue_surjective x tb
  obtain ⟨U, hxU, s, hs⟩ := X.presheaf.exists_germ_eq t₀
  refine ⟨U, hxU, s, fun p hp hmem ↦ htb ?_⟩
  let g : O →+* (Spec (.of O)).residueField (q x) :=
    ((Spec (.of O)).residue (q x)).hom.comp (toStalk' (q x)).hom
  refine ⟨p.map g, fun h0 ↦ hp ?_, ?_⟩
  · have h1 := congrArg (fun r ↦ r.coeff p.natDegree) h0
    simp only [coeff_map, coeff_zero] at h1
    rw [← toStalk'_mem_maximalIdeal_iff, ← residue_eq_zero_iff]
    exact h1
  · have h2 : (X.residue x).hom ((X.presheaf.germ U x hxU).hom
        (p.eval₂ (sectionsRingHom q U) s)) = 0 := (residue_eq_zero_iff _).mpr hmem
    rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂] at h2
    have hcomp : (algebraMap ((Spec (.of O)).residueField (q x)) (X.residueField x)).comp g =
        ((X.residue x).hom.comp (X.presheaf.germ U x hxU).hom).comp (sectionsRingHom q U) :=
      RingHom.ext fun o ↦ (residue_germ_sectionsRingHom q hxU o).symm
    rw [← hs, aeval_def, eval₂_map, hcomp]
    exact h2

end Residue

section Finite

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  {X : Scheme.{u}} {η : Spec (.of L) ⟶ X} (q : X ⟶ Spec (.of O))
  (hq : η ≫ q = Spec.map (CommRingCat.ofHom ((algebraMap K L).comp O.subtype)))
include hq

/-- **Gauss-type transcendence at a centre.** Let `V` be centred at `x ∈ U`, and `s ∈ Γ(X, U)` such
that `p(s)` is a unit at `x` for every `p ∈ O[X]` with leading coefficient outside `q(x)`. Then the
image `b` of `s` in `L` satisfies the residue-transcendence condition over `V ∩ K`: `v(p(b)) = 1`
for every monic `p` with coefficients in `V ∩ K`. -/
theorem isResidueTranscendental_of_isCentre {V : RiemannZariskiSpace L} {x : X}
    (hV : IsCentre η V x) {U : X.Opens} (hxU : x ∈ U) (hηU : η ⁻¹ᵁ U = ⊤) (s : Γ(X, U))
    (hs : ∀ p : O[X], p.leadingCoeff ∉ (q x).asIdeal →
      X.presheaf.germ U x hxU (p.eval₂ (sectionsRingHom q U) s) ∉
        maximalIdeal (X.presheaf.stalk x)) :
    IsResidueTranscendental (V.valuationSubring.comap (algebraMap K L)) V.valuationSubring
      (sectionsToField η U hηU s) := by
  classical
  intro p hp hcoef
  set b := sectionsToField η U hηU s
  have hOV : ∀ o ∈ O, algebraMap K L o ∈ V.valuationSubring := fun o ho ↦
    (V.valuationSubring.valuation_le_one_iff _).mp
      (valuation_algebraMap_of_isCentre q hq hV ⟨o, ho⟩).1
  obtain ⟨d, hdO, hd1, hds⟩ := exists_mul_mem_of_forall_mem (algebraMap K L) O V.valuationSubring
    hOV p.coeffs fun c hc ↦ by
      obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hc
      exact hcoef n
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd1
  -- lift `d • p` to `O[X]`
  have hlift : C d * p ∈ lifts (algebraMap O K) := by
    refine (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_
    rw [coeff_C_mul]
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by rw [hn, mul_zero, map_zero]⟩
    · exact ⟨⟨_, hds _ (coeff_mem_coeffs hn)⟩, rfl⟩
  obtain ⟨p₁, hp₁⟩ := (mem_lifts _).mp hlift
  have hlc : ((p₁.leadingCoeff : O) : K) = d := by
    have h1 := leadingCoeff_map_of_injective (f := algebraMap O K) Subtype.val_injective p₁
    rw [hp₁, leadingCoeff_mul, leadingCoeff_C, hp.leadingCoeff, mul_one] at h1
    exact h1.symm
  have hnot : p₁.leadingCoeff ∉ (q x).asIdeal := fun hmem ↦ by
    have hlt := (valuation_algebraMap_of_isCentre q hq hV _).2.mp hmem
    rw [hlc, hd1] at hlt
    exact lt_irrefl _ hlt
  have hcen := valuation_sectionsToField_of_isCentre hV hxU hηU (p₁.eval₂ (sectionsRingHom q U) s)
  have hv1 : V.valuationSubring.valuation
      (sectionsToField η U hηU (p₁.eval₂ (sectionsRingHom q U) s)) = 1 :=
    le_antisymm hcen.1 (not_lt.mp fun hlt ↦ hs p₁ hnot (hcen.2.mpr hlt))
  have heval : sectionsToField η U hηU (p₁.eval₂ (sectionsRingHom q U) s) =
      algebraMap K L d * aeval b p := by
    rw [Polynomial.hom_eval₂, sectionsToField_comp_sectionsRingHom q hq hηU]
    have h2 : aeval b (C d * p) = algebraMap K L d * aeval b p := by
      rw [map_mul, aeval_C]
    rw [← h2, ← hp₁, aeval_def, eval₂_map]
    rfl
  rw [heval, map_mul, hd1, one_mul] at hv1
  exact hv1

omit hq in
/-- A transcendental element of `L` over `K`, when `L/K` is finitely generated of transcendence
degree at most one, has `L` finite over `K(b)`. -/
theorem finiteDimensional_adjoin_of_trdeg_le_one (hfg : (⊤ : IntermediateField K L).FG)
    (htr : Algebra.trdeg K L ≤ 1) {b : L} (hb : Transcendental K b) :
    FiniteDimensional K⟮b⟯ L := by
  have hind : AlgebraicIndependent K (fun _ : Unit ↦ b) :=
    algebraicIndependent_unique_type_iff.mpr hb
  have hbasis : IsTranscendenceBasis K (fun _ : Unit ↦ b) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simpa using htr)
  have := hbasis.isAlgebraic
  rw [Set.range_const, ← IntermediateField.isAlgebraic_adjoin_iff_top] at this
  exact Valuation.DVRCoordinate.finiteDimensional_adjoin_of_transcendental hfg

/-- **Finitely many valuations centred at a point of positive fibre dimension.** Let `L/K` be
finitely generated of transcendence degree at most one, `O ⊆ K` a valuation ring, `X` an integral
`O`-scheme and `η : Spec L → X` a point over `O ⊆ K ⊆ L` hitting the generic point. For every
`x ∈ X` with `κ(x)` transcendental over `κ(q x)`, only finitely many valuation rings of `L` are
centred at `x`. -/
theorem finite_setOf_isCentre [IsIntegral X] (hη : ∀ z, η z = genericPoint X)
    (hfg : (⊤ : IntermediateField K L).FG) (htr : Algebra.trdeg K L ≤ 1) {x : X}
    (hx : fiberTrdeg q x ≠ 0) : {V : RiemannZariskiSpace L | IsCentre η V x}.Finite := by
  obtain ⟨U, hxU, s, hs⟩ := exists_section_transcendental q hx
  have hηU : η ⁻¹ᵁ U = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    change η z ∈ U
    rw [hη]
    exact genericPoint_mem_of_mem hxU
  set b := sectionsToField η U hηU s
  have htrans : ∀ V : RiemannZariskiSpace L, IsCentre η V x →
      HasTranscendentalResidue (K := K) V.valuationSubring b := fun V hV ↦
    (isResidueTranscendental_of_isCentre q hq hV hxU hηU s hs).hasTranscendentalResidue
      ((V.valuationSubring.valuation_le_one_iff _).mp
        (valuation_sectionsToField_of_isCentre hV hxU hηU s).1)
  rcases Set.eq_empty_or_nonempty {V : RiemannZariskiSpace L | IsCentre η V x} with he | ⟨V₀, hV₀⟩
  · rw [he]
    exact Set.finite_empty
  obtain ⟨hbV, hbtr⟩ := htrans V₀ hV₀
  have hb : Transcendental K b :=
    Valuation.MainUniformization.transcendental_of_transcendental_residue hbV hbtr
  have := finiteDimensional_adjoin_of_trdeg_le_one hfg htr hb
  refine Set.Finite.subset ((finite_setOf_transcendental_residue
    (V₀.valuationSubring.comap (algebraMap K L)) b).preimage
    fun _ _ _ _ h ↦ RiemannZariskiSpace.ext h) fun V hV ↦ ?_
  exact ⟨comap_eq_of_isCentre q hq hV hV₀, htrans V hV⟩

end Finite

section Gamma

variable {K : Type u} [Field K] {O : ValuationSubring K} {C C' : Scheme.{u}} [IsIntegral C]
  [IsIntegral C'] (φ : C ⟶ Spec (.of O)) [Flat φ] [LocallyOfFiniteType φ]

/-- `Γ(C')` over a single point: the valuations of `K(C)` centred at a point `x' ∈ (C'/S)⁰` of a
modification `C' → C` of a flat relative curve of finite type over `O` form a finite set. -/
theorem finite_setOf_isCentre_genericLift (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    (f : C' ⟶ C) [IsModification f] {x' : C'} (hx' : x' ∈ fibreGenericSet (f ≫ φ)) :
    {V : RiemannZariskiSpace C.functionField | IsCentre (genericLift f) V x'}.Finite := by
  let := functionFieldAlgebra φ
  have hq : genericLift f ≫ f ≫ φ = Spec.map (CommRingCat.ofHom
      ((algebraMap K C.functionField).comp O.subtype)) := by
    rw [← Category.assoc, genericLift_comp, genericPt_comp φ]
  have htr : Algebra.trdeg K C.functionField ≤ 1 := (trdeg_functionField_eq φ).le.trans hdim
  refine finite_setOf_isCentre (f ≫ φ) hq (genericLift_apply f) (fg_functionField φ) htr ?_
  rw [hx']
  exact one_ne_zero

/-- **`Γ(C')` is finite for every modification** (the T62/T41 fix, `lem:sm-gamma-finite`). Let
`O` be a valuation ring of finite height and `φ : C → Spec O` an integral, flat, quasi-compact
relative curve locally of finite type. For **every** modification `f : C' → C` (normal or not),
the set `Γ(C')` of valuations of `K(C)` centred at points of `(C'/S)⁰` is finite. Temkin's
Lemma 4.2.2 proves this for normal `C'` only (via `Γ(C') ≅ (C'/S)⁰`); here each point of
`(C'/S)⁰` carries finitely many valuations, by the Gauss valuation in a section with transcendental
residue and the finiteness of extensions to the finite extension `K(C)/K(b)`. -/
theorem finite_gammaSet_of_flat [Finite (PrimeSpectrum O)] [QuasiCompact φ]
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f] :
    (gammaSet (f ≫ φ) (genericLift f)).Finite := by
  have : Finite (Spec (.of O)) := inferInstanceAs (Finite (PrimeSpectrum O))
  have hfin := finite_fibreGenericSet (f ≫ φ) (fiberTrdeg_le_one φ hdim f)
  refine (hfin.biUnion fun x' hx' ↦ finite_setOf_isCentre_genericLift φ hdim f hx').subset ?_
  rintro V ⟨x', hx', hV⟩
  exact Set.mem_iUnion₂.mpr ⟨x', hx', hV⟩

/-- **`Γ₀(C')` is finite for every modification** (Temkin, Lemma 4.2.2, second assertion, without
normality; `lem:sm-gamma-finite`). -/
theorem finite_gammaZeroSet_of_flat [Finite (PrimeSpectrum O)] [QuasiCompact φ]
    (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) (f : C' ⟶ C) [IsModification f] :
    (gammaZeroSet (f ≫ φ) (genericLift f) (genericPt C)).Finite :=
  (finite_gammaSet_of_flat φ hdim f).subset (gammaZeroSet_subset _ _ _)

end Gamma

section Cofinal

variable {K : Type u} [Field K] [IsSepClosed K] {O : ValuationSubring K} [Finite (PrimeSpectrum O)]

/-- **Temkin, Proposition 4.3.1 for all modifications** (`cofinprop`; the T41/T62 fix,
`thm:sm-cofinal-all`): for an integral, quasi-compact, separated, strictly semi-stable relative
curve `C` over a valuation ring `O` of finite height with separably closed fraction field, every
modification `C' → C` is dominated by a strictly semi-stable modification of `C`. -/
theorem exists_dominates_isStrictlySemistable_of_isModification {C : Scheme.{u}} [IsIntegral C]
    [CompactSpace C] [C.IsSeparated] (φ : C ⟶ Spec (.of O))
    (hC : Curves.IsStrictlySemistable φ ⊤) (hdim : fiberTrdeg φ (genericPoint C) ≤ 1)
    {C' : Scheme.{u}} [IsIntegral C'] (f' : C' ⟶ C) [IsModification f'] :
    ∃ (C'' : Scheme.{u}) (_ : IsIntegral C'') (f'' : C'' ⟶ C) (_ : IsModification f''),
      Curves.IsStrictlySemistable (f'' ≫ φ) ⊤ ∧ ∃ g : C'' ⟶ C', g ≫ f' = f'' := by
  have : DeJong.IsNodalCurve φ := hC.isNodalCurve
  have : QuasiCompact φ := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹_›
  exact exists_dominates_isStrictlySemistable_of_finite φ hC hdim f'
    (finite_gammaZeroSet_of_flat φ hdim f')

end Cofinal

end DeJongAlterations.StableModification.Gluing
