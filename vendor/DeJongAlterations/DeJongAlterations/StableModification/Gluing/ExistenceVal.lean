/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane T45E)
-/
import DeJongAlterations.StableModification.Gluing.MarksNodal
import DeJongAlterations.StableModification.BlowDown.Unconditional
import DeJongAlterations.StableModification.Projectivity.ValuationProj
import DeJongAlterations.StableModification.Global.Spread
import DeJongAlterations.StableModification.LocalUniformization.GlobalField
import DeJongAlterations.Geometry.SteinGenericFiber

/-!
# Existence of stable modifications over valuation rings

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`),
Proposition 4.5.1 (`sepclosprop`, T:3233–3266), existence part, in the form of `PLAN-T5.md` §2.2
steps 1–10 (nodes V1, V2): over a valuation ring `W` of finite height and equal characteristic
whose fraction field `K` is algebraically closed, every curve `φ : C → Spec W` in the situation
`Global.IsValuationCurve` (integral, flat, finitely presented and projective, smooth over the
generic point, with flat marks `D` and semi-stable generic pair) has a stable, numerically
stable η-modification projective over `W`: this is `Global.ValuationStableExistence`.

The proof:

1. **The generic fibre.** As `Spec W` is finite, the generic fibre `C_η` is an open subscheme
   of `C` (`isOpenImmersion_fiberι_genericPoint`); it is a nodal curve over `κ(η) = K` which is
   smooth at every point, hence normal (`isIntegrallyClosed_stalk_of_generic`), of dimension one
   (`topologicalKrullDim_fiber_genericPoint`), so that `trdeg K(C)/K = 1`
   (`fiberTrdeg_genericPoint_eq_one`, by the dimension formula of the generic fibre).
2. **The marks.** `K` being algebraically closed, the generic marks are finitely many sections
   `σ k` of `φ` (`StableVal.exists_sections_of_etale_genericMarks`, Temkin T:3025–3027).
3. **A nodal model with separated marks** (steps 1–8, `StableVal.exists_marked_nodal_modification`):
   `X → N → C`, `X` nodal over `W` and locally projective over the normalized refinement `N`
   (projective over `W`), with pairwise disjoint lifted sections `σX k` through smooth points.
4. **Projectivity** (node V1, Temkin Thm 1.1 at the valuation level, `thm:sm-val-proj`): `X` is
   projective over `W`, by lane OM3F's
   `Projectivity.Valuation.isProjectiveOver_of_valuationSubring` applied to `X → N → Spec W`.
5. **The semi-stable stage**: `X → C` is an η-modification (it is an isomorphism over the
   normal generic fibre, `StableVal.isIso_restrict_genericOpen`), the marks `⋂ₖ ker σX k` are the
   transported marks (`Global.eq_genericMarksClosure_of_forall`) and form a semi-stable pair
   (`StableVal.isSemistablePair_iInf_ker`).
6. **The stable blow-down** (node V2 with Temkin Prop. 4.4.6, T:3188–3229, lanes T44B, T44F,
   T44E):
   `BlowDown.Unconditional.exists_isStableModification_of_isSemistableStage_of_isProjectiveOver`
   gives a stable, numerically stable η-modification projective over `W`.

Steps 3–5 are carried out for an arbitrary modification `h : C' → C` with `C'` projective over
`W` in place of `C` (`exists_isSemistableStage_comp`): the semi-stable stage then factors through
`h`. With `h` the join of two stable modifications this is the semi-stable model dominating the
join used for uniqueness (`PLAN-T5.md` node V3, lane T45F).

## Hypotheses (results of lanes running in parallel)

The theorems take the following inputs as explicit hypotheses; nothing here asserts them.

* `ProjectiveSeparationAlgClosed` (lane T45D): `StableVal.ProjectiveSeparation R` for the
  valuation rings `R` of finite height and equal characteristic of algebraically closed fields
  (the weakest form consumed here).
* `BlowDown.ExcSpecialize.ClosureComponentLocal` (lane T44G).

The valuation-level projectivity theorem (lane OM3F) is integrated and used directly.

## Main results

* `exists_isSemistableStage_comp`: a projective semi-stable stage through a projective
  modification `h : C' → C`;
* `exists_stableModification_comp`: such a stage together with the stable modification it
  dominates;
* `exists_stableModification`: the existence over one valuation ring;
* `valuationStableExistence`: `Global.ValuationStableExistence` from the two hypotheses.

Blueprint: `sm-gluing-existence.tex`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Gluing.ExistenceVal

open DeJong (IsNodalCurve IsSmoothAt IsSemistablePair)
open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg)
open StableVal

set_option backward.isDefEq.respectTransparency false

section Hypotheses

/-- **Projective separation of marks over the valuation rings of Temkin's §4.5** (lane T45D;
`PLAN-T5.md` node A4, marks part; Temkin, Lemma 4.3.3 `divlem`, T:3019–3044, with projectivity
tracked). `StableVal.ProjectiveSeparation R` for every valuation ring `R` of finite height and
equal characteristic of an algebraically closed field. This is the form consumed by
`exists_stableModification`; it follows from `∀ R, ProjectiveSeparation R`. -/
def ProjectiveSeparationAlgClosed : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (R : ValuationSubring K) [Finite (PrimeSpectrum R)],
    (∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField R) p) → ProjectiveSeparation R

end Hypotheses

section GenericFibre

variable {V : Type u} [CommRing V] [IsDomain V] [Finite (PrimeSpectrum V)] {C : Scheme.{u}}
  (φ : C ⟶ Spec (.of V))

/-- **The generic fibre is open**: over a domain with finitely many primes, the generic point is
open with a field as stalk, so `C_η → C` is an open immersion. -/
theorem isOpenImmersion_fiberι_genericPoint :
    IsOpenImmersion (φ.fiberι (genericPoint (Spec (.of V)))) := by
  have hfield : IsField ((Spec (.of V)).presheaf.stalk (genericPoint (Spec (.of V)))) :=
    Field.toIsField (Spec (.of V)).functionField
  have : IsOpenImmersion ((Spec (.of V)).fromSpecResidueField (genericPoint (Spec (.of V)))) :=
    Limits.SpreadModification.isOpenImmersion_fromSpecResidueField _
      (Limits.SpreadModification.isOpen_singleton_genericPoint_of_finite (.of V)) hfield
  exact inferInstanceAs (IsOpenImmersion (pullback.fst φ
    ((Spec (.of V)).fromSpecResidueField (genericPoint (Spec (.of V))))))

omit [Finite (PrimeSpectrum V)] in
/-- Points of the generic fibre lie over the generic point. -/
theorem apply_fiberι_genericPoint (z : φ.fiber (genericPoint (Spec (.of V)))) :
    φ (φ.fiberι (genericPoint (Spec (.of V))) z) = genericPoint (Spec (.of V)) := by
  have : φ.fiberι (genericPoint (Spec (.of V))) z ∈
      Set.range (φ.fiberι (genericPoint (Spec (.of V)))) := ⟨z, rfl⟩
  rwa [Scheme.Hom.range_fiberι] at this

/-- **Normality along a smooth nodal generic fibre** (Temkin T:2966–2967 over a field): if the
generic fibre of `φ` is a nodal curve and `φ` is smooth at the points over the generic point,
the local rings of `C` at these points are integrally closed. -/
theorem isIntegrallyClosed_stalk_of_generic [LocallyOfFinitePresentation φ]
    (hnod : IsNodalCurve (φ.fiberToSpecResidueField (genericPoint (Spec (.of V)))))
    (hsm : ∀ x : C, φ x = genericPoint (Spec (.of V)) → IsSmoothAt φ x) (x : C)
    (hx : φ x = genericPoint (Spec (.of V))) : IsIntegrallyClosed (C.presheaf.stalk x) := by
  have := isOpenImmersion_fiberι_genericPoint φ
  have hxr : x ∈ Set.range (φ.fiberι (genericPoint (Spec (.of V)))) := by
    rw [Scheme.Hom.range_fiberι]
    exact hx
  obtain ⟨y, rfl⟩ := hxr
  have := hnod
  have hN : IsNormalScheme (φ.fiber (genericPoint (Spec (.of V)))) :=
    Curves.SemistableNormal.isNormalScheme_of_isNodalCurve_spec
      (R := (Spec (.of V)).residueField (genericPoint (Spec (.of V))))
      (φ.fiberToSpecResidueField (genericPoint (Spec (.of V)))) fun z _ ↦
        BlowDown.Domination.isSmoothAt_fiber_of_isSmoothAt φ _
          (hsm _ (apply_fiberι_genericPoint φ z))
  have := (hN y).2
  exact IsIntegrallyClosed.of_equiv
    (asIso ((φ.fiberι (genericPoint (Spec (.of V)))).stalkMap y)).commRingCatIsoToRingEquiv.symm

omit [Finite (PrimeSpectrum V)] in
/-- **The generic fibre is a curve**: if it is nodal, it has dimension one (it is nonempty, `φ`
being flat). -/
theorem topologicalKrullDim_fiber_genericPoint [IsIntegral C] [Flat φ]
    (hnod : IsNodalCurve (φ.fiberToSpecResidueField (genericPoint (Spec (.of V))))) :
    topologicalKrullDim (φ.fiber (genericPoint (Spec (.of V)))) = 1 := by
  set g := φ.fiberToSpecResidueField (genericPoint (Spec (.of V)))
  have hsub : Subsingleton (Spec ((Spec (.of V)).residueField (genericPoint (Spec (.of V))))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum _))
  obtain ⟨s⟩ : Nonempty (Spec ((Spec (.of V)).residueField (genericPoint (Spec (.of V))))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  have : Nonempty (φ.fiber (genericPoint (Spec (.of V)))) :=
    BlowDown.nonempty_fiber_genericPoint_of_flat φ
  have hpre : g ⁻¹' {s} = Set.univ := Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  let h : g.fiber s ≃ₜ φ.fiber (genericPoint (Spec (.of V))) :=
    (g.fiberHomeo s).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ _))
  have : Nonempty (g.fiber s) := ⟨h.symm (Classical.arbitrary _)⟩
  have := hnod
  rw [← IsHomeomorph.topologicalKrullDim_eq h h.isHomeomorph]
  exact le_antisymm (BlowDown.topologicalKrullDim_fiber_le_one_of_nodal g s)
    (BlowDown.one_le_topologicalKrullDim_fiber_of_nodal g s)

end GenericFibre

section Trdeg

variable {K : Type u} [Field K] {W : ValuationSubring K}
  {C : Scheme.{u}} [IsIntegral C] (φ : C ⟶ Spec (.of W)) [Flat φ] [LocallyOfFiniteType φ]

/-- **The relative dimension of a curve over a valuation ring**: if the generic fibre of the
flat `φ : C → Spec W` is a nodal curve, then `trdeg K(C)/K = 1` (Codex's dimension formula for
the generic fibre, `Geometry.SteinGenericFiber.exists_dimension_and_trdeg`, compared with the
fibre dimension of the generic point through `LocalUniformization.trdeg_functionField_eq`). -/
theorem fiberTrdeg_genericPoint_eq_one
    (hnod : IsNodalCurve (φ.fiberToSpecResidueField (genericPoint (Spec (.of W))))) :
    fiberTrdeg φ (genericPoint C) = 1 := by
  have := BlowDown.isDominant_of_flat φ
  obtain ⟨d, hd, htrF⟩ := Geometry.SteinGenericFiber.exists_dimension_and_trdeg φ
  have hd1 : d = 1 := by
    rw [topologicalKrullDim_fiber_genericPoint φ hnod] at hd
    exact_mod_cast hd.symm
  rw [← LocalUniformization.trdeg_functionField_eq φ]
  let : Algebra (Spec (.of W)).functionField C.functionField :=
    Geometry.FiniteBirationalNormal.functionFieldAlgebra φ
  let : Algebra K C.functionField := LocalUniformization.functionFieldAlgebra φ
  -- the stalk at the generic point is the fraction field `K`
  set p := genericPoint (Spec (.of W)) with hpdef
  let : Algebra W ((Spec (.of W)).presheaf.stalk p) := StructureSheaf.stalkAlgebra W p
  have hloc : IsLocalization.AtPrime ((Spec (.of W)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk W p
  have hp : p.asIdeal = ⊥ := by rw [hpdef, genericPoint_eq_bot_of_affine]; rfl
  have hunit : ∀ y : p.asIdeal.primeCompl, IsUnit (algebraMap W K y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := fun h ↦ hy (by rw [h]; exact zero_mem _)
    exact IsUnit.mk0 _ fun h ↦ hy0 (Subtype.ext (by simpa using h))
  let e : (Spec (.of W)).functionField →+* K :=
    IsLocalization.lift (M := p.asIdeal.primeCompl) (S := (Spec (.of W)).presheaf.stalk p) hunit
  have he : ∀ w : W, e (algebraMap W ((Spec (.of W)).presheaf.stalk p) w) = (w : K) :=
    fun w ↦ IsLocalization.lift_eq (M := p.asIdeal.primeCompl) hunit w
  let : Algebra (Spec (.of W)).functionField K := e.toAlgebra
  have hsurj : Function.Surjective e := by
    intro k
    by_cases hk : k ∈ W
    · exact ⟨_, he ⟨k, hk⟩⟩
    · have hk' : k⁻¹ ∈ W := (W.mem_or_inv_mem k).resolve_left hk
      refine ⟨(algebraMap W ((Spec (.of W)).presheaf.stalk p) ⟨k⁻¹, hk'⟩)⁻¹, ?_⟩
      rw [map_inv₀, he, inv_inv]
  have : Algebra.IsAlgebraic (Spec (.of W)).functionField K := ⟨fun k ↦ by
    obtain ⟨x, rfl⟩ := hsurj k
    exact isAlgebraic_algebraMap x⟩
  have : FaithfulSMul (Spec (.of W)).functionField K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr e.injective
  have : FaithfulSMul K C.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K C.functionField).injective
  have : FaithfulSMul (Spec (.of W)).functionField C.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (Spec (.of W)).functionField C.functionField).injective
  -- the scalar tower `κ(η) → K → K(C)`
  have hcomp : (Geometry.NormalizationInExtension.functionFieldMap φ).hom.comp
      (StructureSheaf.toStalk W p).hom = LocalUniformization.fieldMap φ := by
    have h1 : StructureSheaf.toStalk W p ≫ Geometry.NormalizationInExtension.functionFieldMap φ =
        Spec.preimage (ValCurves.genericPt C ≫ φ) := by
      have h2 : Spec.map (StructureSheaf.toStalk W p) = (Spec (.of W)).fromSpecStalk p :=
        (Spec.fromSpecStalk_eq' (.of W) p).symm
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, h2,
        Geometry.FiniteBirationalNormal.functionFieldMap_fromSpecStalk φ]
      rfl
    exact congrArg CommRingCat.Hom.hom h1
  have htower : IsScalarTower (Spec (.of W)).functionField K C.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine IsLocalization.ringHom_ext p.asIdeal.primeCompl
      (S := (Spec (.of W)).presheaf.stalk p) ?_
    change (Geometry.NormalizationInExtension.functionFieldMap φ).hom.comp
      (StructureSheaf.toStalk W p).hom = ((algebraMap K C.functionField).comp e).comp
        (algebraMap W ((Spec (.of W)).presheaf.stalk p))
    rw [hcomp, RingHom.comp_assoc, IsLocalization.lift_comp,
      ← LocalUniformization.functionFieldAlgebra_comp φ]
    rfl
  have hadd := trdeg_add_eq (Spec (.of W)).functionField K (A := C.functionField)
  rw [trdeg_eq_zero, zero_add] at hadd
  rw [hadd, htrF, hd1]
  rfl

end Trdeg

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {W : ValuationSubring K} [Finite (PrimeSpectrum W)]

omit [Finite (PrimeSpectrum W)] in
/-- The residue field of `Spec W` at the generic point is algebraically closed (it is `K`). -/
theorem isAlgClosed_residueField_pt₀ :
    IsAlgClosed ((Spec (.of W)).residueField (pt₀ (V := W))) := by
  have := BlowDown.NoClosedExc.isAlgClosed_residueField_of_isAlgClosed K (pt₀ (V := W))
  exact IsAlgClosed.of_ringEquiv _ _
    (Scheme.Spec.residueFieldIso (.of W) (pt₀ (V := W))).commRingCatIsoToRingEquiv.symm

/-- **A projective semi-stable stage dominating a projective modification** (Temkin, proof of
Proposition 4.5.1, T:3243–3266, steps up to the blow-down; `PLAN-T5.md` §2.2 steps 1–9, nodes
V1, V2). Let `K` be algebraically closed, `W ⊆ K` a valuation ring of finite height and equal
characteristic, `(φ : C → Spec W, D)` a curve in the situation of Temkin's §4.5
(`Global.IsValuationCurve`), and `h : C' → C` a modification with `C'` projective over `W`. Then
there is a semi-stable stage of `(C, D)` (`BlowDown.IsSemistableStage`: an integral normal
η-modification, projective over `W`, whose transported marks form a semi-stable pair) factoring
through `h`.

The construction: the generic fibre of `C` is a normal curve (`isIntegrallyClosed_stalk_of_generic`,
`fiberTrdeg_genericPoint_eq_one`), `h` is an isomorphism over it, the generic marks are finitely
many sections (`exists_sections_of_etale_genericMarks`) which lift to `C'`; the marked nodal model
`X → N → C'` of `exists_marked_nodal_modification` is projective over `N` by the valuation-level
projectivity theorem, hence projective over `W`
(`Projectivity.Valuation.isProjectiveOver_of_valuationSubring`), and the union of its disjoint
smooth lifted sections is the transported marks (`Global.eq_genericMarksClosure_of_forall`).

Input not proved here: `ProjectiveSeparation W` (lane T45D). -/
theorem exists_isSemistableStage_comp (hsepM : ProjectiveSeparation W)
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p)
    {C : Scheme.{u}} (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData)
    (hV : Global.IsValuationCurve φ D) {C' : Scheme.{u}} (h : C' ⟶ C) [IsModification h]
    (hC' : IsProjectiveOver (h ≫ φ)) :
    ∃ (X : Scheme.{u}) (g : X ⟶ C'), BlowDown.IsSemistableStage φ D (g ≫ h) := by
  classical
  have := hV.isIntegral
  have := hV.flat
  have := hV.locallyOfFinitePresentation
  have hC := hV.isProjectiveOver
  have : IsProper φ := hC.isProper
  have hnod : IsNodalCurve (φ.fiberToSpecResidueField (genericPoint (Spec (.of W)))) :=
    hV.genericPair.nodal
  have hnorm := isIntegrallyClosed_stalk_of_generic φ hnod hV.isSmoothAt_generic
  have htr := fiberTrdeg_genericPoint_eq_one φ hnod
  -- the curve `C'`: integral, proper and flat over `W`, normal along its generic fibre
  have hh : IsModification h := inferInstance
  have := hh.sourceIntegral
  have hgen' : (h ≫ φ) (genericPoint C') = (⊥ : PrimeSpectrum W) := by
    rw [Scheme.Hom.comp_apply, Geometry.NormalCurveModification.genericPoint_map h hh.birational]
    exact apply_genericPoint_eq_bot_of_flat φ
  have : Flat (h ≫ φ) := flat_of_apply_genericPoint_eq_bot (h ≫ φ) hgen'
  have : C'.IsSeparated := ⟨by rw [← terminal.comp_from (h ≫ φ)]; infer_instance⟩
  have : CompactSpace C' := BlowDown.compactSpace_of_quasiCompact (h ≫ φ)
  have htr' : fiberTrdeg (h ≫ φ) (genericPoint C') = 1 := by
    rw [ValCurves.fiberTrdeg_comp_genericPoint φ h, htr]
  have : IsIso (h ∣_ (φ ⁻¹ᵁ BlowDown.genericOpen W)) :=
    isIso_restrict_genericOpen φ hnorm htr.le h
  have hnorm' : ∀ x : C', (h ≫ φ) x = genericPoint (Spec (.of W)) →
      IsIntegrallyClosed (C'.presheaf.stalk x) := by
    intro x hx
    have hx' : φ (h x) = genericPoint (Spec (.of W)) := by
      rw [← Scheme.Hom.comp_apply]
      exact hx
    have hxU : h x ∈ φ ⁻¹ᵁ BlowDown.genericOpen W := by
      change φ (h x) ∈ (BlowDown.genericOpen W : Set _)
      rw [BlowDown.coe_genericOpen]
      exact hx'
    have := CurvesField.Genus.isIso_stalkMap_of_isIso_morphismRestrict h _ x hxU
    have := hnorm (h x) hx'
    exact IsIntegrallyClosed.of_equiv (asIso (h.stalkMap x)).commRingCatIsoToRingEquiv
  -- the generic marks are finitely many sections (Temkin T:3025–3027), lifted to `C'`
  have : IsAlgClosed ((Spec (.of W)).residueField (pt₀ (V := W))) := isAlgClosed_residueField_pt₀
  have he : Etale ((DeJong.fiberMarks φ D pt₀).subschemeι ≫ φ.fiberToSpecResidueField pt₀) := by
    have h := hV.genericPair.etale
    rwa [genericPoint_eq_pt₀] at h
  obtain ⟨n, σ, hσ, hinj₀, hmem⟩ := exists_sections_of_etale_genericMarks φ D he
  choose σ' hσ' using fun k ↦ exists_lift_section φ hnorm htr.le h (σ k) (hσ k)
  have hσ'sec : ∀ k, σ' k ≫ h ≫ φ = 𝟙 _ := fun k ↦ by rw [← Category.assoc, hσ', hσ]
  have hinj : Function.Injective fun k ↦ σ' k (genericPoint (Spec (.of W))) := by
    intro k l hkl
    apply hinj₀
    change σ k pt₀ = σ l pt₀
    rw [← hσ' k, ← hσ' l, ← genericPoint_eq_pt₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg h hkl
  -- the nodal model with separated marks (steps 1–8)
  obtain ⟨N, _, b, X, β, σX, hb, hβ, -, hNlfp, hNproj, hXnod, hXloc, hσX, hdisj, hsm⟩ :=
    exists_marked_nodal_modification hchar hsepM (h ≫ φ) htr' hnorm' σ' hσ'sec hinj
  have := hβ.sourceIntegral
  have : IsModification (β ≫ b) := IsModification.comp β b
  have : IsModification ((β ≫ b) ≫ h) := IsModification.comp (β ≫ b) h
  set f : X ⟶ C := (β ≫ b) ≫ h with hfdef
  have hfφ : f ≫ φ = β ≫ b ≫ h ≫ φ := by simp only [hfdef, Category.assoc]
  have hYproj : IsProjectiveOver (b ≫ h ≫ φ) := hNproj hC'
  -- `X → C` is an isomorphism over the generic fibre
  have : IsIso (f ∣_ (φ ⁻¹ᵁ BlowDown.genericOpen W)) := isIso_restrict_genericOpen φ hnorm htr.le f
  have hgenU : ∀ x : X, (β ≫ b ≫ h ≫ φ) x = genericPoint (Spec (.of W)) →
      f x ∈ φ ⁻¹ᵁ BlowDown.genericOpen W := fun x hx ↦ by
    change φ (f x) ∈ (BlowDown.genericOpen W : Set _)
    rw [BlowDown.coe_genericOpen, ← Scheme.Hom.comp_apply, hfφ]
    exact hx
  have hsmgen : ∀ x : X, (β ≫ b ≫ h ≫ φ) x = genericPoint (Spec (.of W)) →
      IsSmoothAt (β ≫ b ≫ h ≫ φ) x := by
    intro x hx
    have hφx : φ (f x) = genericPoint (Spec (.of W)) := by
      rw [← Scheme.Hom.comp_apply, hfφ]
      exact hx
    have h1 := isSmoothAt_of_mem_isomorphismOpen f φ (V := φ ⁻¹ᵁ BlowDown.genericOpen W)
      (hgenU x hx) (hV.isSmoothAt_generic _ hφx)
    rwa [hfφ] at h1
  -- projectivity of `X` over `W` (node V1, lane OM3F's `thm:sm-val-proj`)
  have := hXnod
  have : LocallyOfFinitePresentation (b ≫ h ≫ φ) := hNlfp
  have hXproj : IsProjectiveOver (β ≫ b ≫ h ≫ φ) :=
    Projectivity.Valuation.isProjectiveOver_of_valuationSubring W (b ≫ h ≫ φ) hYproj β hXloc
  -- the marks of `X`: a semi-stable pair
  have hσXf : ∀ k, σX k ≫ f = σ k := fun k ↦ by
    rw [hfdef, ← Category.assoc, hσX, hσ']
  have hσXsec : ∀ k, σX k ≫ β ≫ b ≫ h ≫ φ = 𝟙 _ := fun k ↦ by
    rw [← hfφ, ← Category.assoc, hσXf, hσ]
  set DX : X.IdealSheafData := ⨅ k, (σX k).ker with hDX
  have hpair : IsSemistablePair (β ≫ b ≫ h ≫ φ) DX :=
    isSemistablePair_iInf_ker σX hσXsec hdisj hsm
  -- `X → C` is an η-modification and `DX` are the transported marks
  have : IsNodalCurve (f ≫ φ) := by
    rw [hfφ]
    exact hXnod
  have hη : Curves.IsEtaModification f φ := Gluing.isEtaModification_of_isNodalCurve φ hnorm f
  have : IsIso (Curves.fiberMap f φ (genericPoint (Spec (.of W)))) := hη.isIso_fiberMap
  have : IsReduced (DeJong.fiberMarks φ D (genericPoint (Spec (.of W)))).subscheme :=
    @Global.isReduced_of_etale_field _ _ _ _ hV.genericPair.etale
  have : IsReduced ((DeJong.fiberMarks φ D (genericPoint (Spec (.of W)))).comap
      (Curves.fiberMap f φ (genericPoint (Spec (.of W))))).subscheme :=
    Global.isReduced_comap_of_isIso _ _
  have : Etale (DX.subschemeι ≫ f ≫ φ) := by
    rw [hfφ]
    exact hpair.etale
  have hmarks : DX = Curves.genericMarksClosure f φ D (genericPoint (Spec (.of W))) := by
    refine Global.eq_genericMarksClosure_of_forall f φ D DX fun x hx ↦ ?_
    rw [hfφ] at hx
    rw [hDX, support_iInf_ker' σX hσXsec]
    have hφx : φ (f x) = pt₀ := by
      rw [← genericPoint_eq_pt₀, ← Scheme.Hom.comp_apply, hfφ]
      exact hx
    rw [hmem _ hφx]
    constructor
    · intro hxk
      obtain ⟨k, t, rfl⟩ := Set.mem_iUnion.mp hxk
      have ht : t = pt₀ := by
        rw [← genericPoint_eq_pt₀, ← hx, ← Scheme.Hom.comp_apply, hσXsec]
        rfl
      refine ⟨k, ?_⟩
      rw [← Scheme.Hom.comp_apply, hσXf, ht]
    · rintro ⟨k, hk⟩
      have h1 : f (σX k pt₀) = f x := by
        rw [← Scheme.Hom.comp_apply, hσXf, hk]
      have h2 : f (σX k pt₀) ∈ φ ⁻¹ᵁ BlowDown.genericOpen W := by
        rw [h1]
        exact hgenU x hx
      exact Set.mem_iUnion.mpr ⟨k, pt₀, eq_of_isIso_restrict f _ h1 h2⟩
  -- the semi-stable stage
  have hpair' : IsSemistablePair (f ≫ φ)
      (Curves.genericMarksClosure f φ D (genericPoint (Spec (.of W)))) := by
    rw [← hmarks, hfφ]
    exact hpair
  have hfproj : IsProjectiveOver (f ≫ φ) := by
    rw [hfφ]
    exact hXproj
  refine ⟨X, β ≫ b, BlowDown.isSemistableStage_of_isSmoothAt_generic φ D f hη hpair' hfproj
    fun y hy ↦ ?_⟩
  have hy' : (β ≫ b ≫ h ≫ φ) y = genericPoint (Spec (.of W)) := by
    rw [genericPoint_eq_bot_of_affine, ← hfφ]
    exact PrimeSpectrum.ext hy
  rw [hfφ]
  exact hsmgen y hy'

/-- **A stable modification dominated by a semi-stable stage dominating a projective
modification** (Temkin, Proposition 4.5.1 existence, with Proposition 4.4.6, T:3188–3229, for the
blow-down; `PLAN-T5.md` §2.2 steps 1–10). In the situation of `exists_isSemistableStage_comp`
there are a semi-stable stage `g ≫ h : X → C` through `h` and a semi-stable stage `β : Y → C`
which is a stable and numerically stable modification of `(C, D)`, with a morphism `c : X → Y`
over `C` (the blow-down).

Inputs not proved here: `ProjectiveSeparation W` (lane T45D) and `ClosureComponentLocal`
(lane T44G). -/
theorem exists_stableModification_comp (hsepM : ProjectiveSeparation W)
    (hloc : BlowDown.ExcSpecialize.ClosureComponentLocal.{u})
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p)
    {C : Scheme.{u}} (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData)
    (hV : Global.IsValuationCurve φ D) {C' : Scheme.{u}} (h : C' ⟶ C) [IsModification h]
    (hC' : IsProjectiveOver (h ≫ φ)) :
    ∃ (X : Scheme.{u}) (g : X ⟶ C') (Y : Scheme.{u}) (β : Y ⟶ C) (c : X ⟶ Y),
      c ≫ β = g ≫ h ∧ BlowDown.IsSemistableStage φ D (g ≫ h) ∧
        BlowDown.IsSemistableStage φ D β ∧
        Curves.IsStableModification β φ D
          (Curves.genericMarksClosure β φ D (genericPoint (Spec (.of W)))) ∧
        Global.IsNumericallyStable β φ
          (Curves.genericMarksClosure β φ D (genericPoint (Spec (.of W)))) := by
  have := hV.isIntegral
  have := hV.flat
  have := hV.locallyOfFinitePresentation
  have hC := hV.isProjectiveOver
  have : IsProper φ := hC.isProper
  have htr := fiberTrdeg_genericPoint_eq_one φ hV.genericPair.nodal
  have halg : ∀ t : PrimeSpectrum W, IsAlgClosed t.asIdeal.ResidueField := fun t ↦
    BlowDown.NoClosedExc.isAlgClosed_residueField_of_isAlgClosed K t
  have hsep : ∀ P : PrimeSpectrum W, IsSepClosed (FractionRing (W ⧸ P.asIdeal)) := fun P ↦
    Cohomology.Connected.isSepClosed_fractionRing_quotient K P
  obtain ⟨X, g, hstage⟩ := exists_isSemistableStage_comp hsepM hchar φ D hV h hC'
  obtain ⟨Y, β, c, hc, hstage', hstable, hnum⟩ :=
    BlowDown.Unconditional.exists_isStableModification_of_isSemistableStage_of_isProjectiveOver
      φ D hloc hC hsep halg htr.le X (g ≫ h) hstage
  exact ⟨X, g, Y, β, c, hc, hstage, hstage', hstable, fun K' _ _ a ↦ hnum K' a⟩

/-- **Existence of a stable modification over a valuation ring** (Temkin, Proposition 4.5.1
`sepclosprop`, T:3233–3266, existence, with Thm 1.1 over `W`; `PLAN-T5.md` §2.2 steps 1–10, nodes
V1, V2). Let `K` be algebraically closed, `W ⊆ K` a valuation ring of finite height and equal
characteristic, and `(φ : C → Spec W, D)` a curve in the situation of Temkin's §4.5
(`Global.IsValuationCurve`). Then `(C, D)` has a stable, numerically stable η-modification
projective over `W` (`exists_stableModification_comp` with `h = 𝟙`).

Inputs not proved here: `ProjectiveSeparation W` (lane T45D) and `ClosureComponentLocal`
(lane T44G). -/
theorem exists_stableModification (hsepM : ProjectiveSeparation W)
    (hloc : BlowDown.ExcSpecialize.ClosureComponentLocal.{u})
    (hchar : ∃ p : ℕ, ExpChar K p ∧ ExpChar (IsLocalRing.ResidueField W) p)
    {C : Scheme.{u}} (φ : C ⟶ Spec (.of W)) (D : C.IdealSheafData)
    (hV : Global.IsValuationCurve φ D) :
    ∃ (C' : Scheme.{u}) (β : C' ⟶ C) (D' : C'.IdealSheafData),
      Curves.IsStableModification β φ D D' ∧ Global.IsNumericallyStable β φ D' ∧
        IsProjectiveOver (β ≫ φ) := by
  have := hV.isIntegral
  obtain ⟨-, -, Y, β, -, -, -, hstage, hstable, hnum⟩ :=
    exists_stableModification_comp hsepM hloc hchar φ D hV (𝟙 C)
      (by rw [Category.id_comp]; exact hV.isProjectiveOver)
  exact ⟨Y, β, _, hstable, hnum, hstage.isProjectiveOver⟩

end Main

section Statement

/-- **`Global.ValuationStableExistence`** (Temkin, Proposition 4.5.1, existence; `PLAN-T5.md`
§1.3, node V2), from projective separation of marks (lane T45D) and the étale-local part of the
closure-component lemma (lane T44G). -/
theorem valuationStableExistence (hsepM : ProjectiveSeparationAlgClosed.{u})
    (hloc : BlowDown.ExcSpecialize.ClosureComponentLocal.{u}) :
    Global.ValuationStableExistence.{u} := by
  intro K _ _ W _ hchar C φ D hV
  exact exists_stableModification (hsepM K W hchar) hloc hchar φ D hV

end Statement

end DeJongAlterations.StableModification.Gluing.ExistenceVal
