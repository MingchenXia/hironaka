/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeightTop
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeightClosure
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeightCharts

/-!
# Zariski's connectedness theorem for birational morphisms onto normal curves, finite height

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (T:3133): for a modification `f : C' → C` of a normal curve over a valuation ring and a
point `x`, "`Z = f⁻¹(x)` is connected because otherwise `C` is not normal at `x` by Zariski
connectedness theorem". Lane COH3D proved this over a valuation ring of height one and, in finite
height, when no other point of the modification locus specializes to `x`
(`Cohomology.ConnectedBirational`, blueprint `sm-cohomology-connected-birational.tex`). This file
removes that restriction (blueprint `sm-cohomology-connected-birational-height.tex`, following
remark `rem:sm-connbir-generizations`).

## Setting

`V` is a valuation ring with finitely many primes such that `Frac (V ⧸ 𝔭)` is separably closed for
every prime `𝔭` (Temkin's valuation rings of `K^s`), `pY : Y → Spec V` is of finite presentation,
quasi-compact and separated with `Y` integral, normal and of relative dimension at most one, and
`π : B → Y` is birational and projective relative to `pY` with `B` integral and flat over `V` and
projective over `V` (for instance `Y` projective over `V`).

## The argument

Let `Σ = center π` be the (finite) modification locus. By induction along the specialization
order of `Σ`, every fibre `π⁻¹(z)`, `z ∈ Σ`, is preconnected: with `Σ_z` the generizations of `z` in
`Σ`,
* `π⁻¹(Σ_z)` is preconnected (`isPreconnected_preimage_generizations`, two-chart Zariski
  connectedness on a neighbourhood of `z` in which `Σ_z` is cut out by finitely many functions);
* for `y ∈ Σ_z ∖ {z}`, `π⁻¹(y)` is preconnected by induction, hence so is
  `closure (π⁻¹(y)) ∩ π⁻¹(z)` (`isPreconnected_closure_preimage_inter_preimage`): it is the fibre
  over `pY z` of the closure of `π⁻¹(y)`, which is preconnected by the `S`-fibre form of Zariski's
  theorem over `V ⧸ pY(y)` (`isPreconnected_closure_inter_preimage`, lane COH3C);
* the topological gluing lemma `isPreconnected_preimage_singleton_of_closure` concludes.
Points outside `Σ` have one-point fibres.

## Main results

* `eq_of_specializes_of_mem_center`: points of the modification locus are closed in their fibres.
* `isPreconnected_closure_preimage_inter_preimage` (blueprint `lem:sm-connbirh-closure-fibre`).
* `isPreconnected_preimage_singleton` (blueprint `thm:sm-connbirh-main`): every fibre of `π` is
  preconnected, provided the points of `Σ` have infinite residue fields;
  `isConnected_preimage_singleton`: connected if the residue field of `V` is infinite.
* `infinite_residueField_of_infinite`: if the residue field of `V` is infinite, every point of a
  `V`-scheme has infinite residue field (this discharges the infinite residue field hypothesis of
  lane COH3D in Temkin's setting, where the residue field of `V` is algebraically closed).
* `isConnected_preimage_singleton_of_isProjectiveOver` (blueprint `cor:sm-connbirh-projective`):
  the form used in Temkin's Lemma 4.4.2, for `Y` projective over `V` with algebraically closed
  (or just infinite) residue field.
* `isConnected_preimage_singleton_of_heightOne_of_infinite` (blueprint
  `cor:sm-connbirh-height-one`): lane COH3D's height-one theorem with the infinite residue field
  hypothesis discharged.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight

open ConnectedBirational Geometry.ModificationCenter

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Residue

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **Infinite residue fields**: if the residue field of the valuation ring `V` is infinite, every
point of a `V`-scheme has infinite residue field. (Over a non-maximal prime `𝔭` the ring
`V ⧸ 𝔭` is a domain which is not a field, hence infinite.) -/
theorem infinite_residueField_of_infinite [Infinite (IsLocalRing.ResidueField V)] {Y : Scheme.{u}}
    (pY : Y ⟶ Spec (CommRingCat.of V)) (z : Y) : Infinite (Y.residueField z) := by
  set P := pY z
  have h1 : Infinite (V ⧸ P.asIdeal) := by
    by_cases hP : P.asIdeal = IsLocalRing.maximalIdeal V
    · rw [hP]
      exact ‹Infinite (IsLocalRing.ResidueField V)›
    · by_contra hfin
      rw [not_infinite_iff_finite] at hfin
      have hfield : IsField (V ⧸ P.asIdeal) := Finite.isField_of_domain _
      exact hP (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hfield))
  have h2 : Infinite P.asIdeal.ResidueField :=
    Infinite.of_injective _ (Ideal.injective_algebraMap_quotient_residueField P.asIdeal)
  have e : Function.Bijective (Scheme.Spec.residueFieldIso (CommRingCat.of V) P).hom :=
    ConcreteCategory.bijective_of_isIso _
  have h3 : Infinite ((Spec (CommRingCat.of V)).residueField P) := Infinite.of_surjective _ e.2
  exact Infinite.of_injective _ (pY.residueFieldMap z).hom.injective

end Residue

section ClosureFibre

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))
  [IsIntegral B] [IsIntegral Y]

/-- **Points of the modification locus are closed in their fibres**: for `t ∈ center π` (`π` a
modification of a normal relative curve) and a specialization `w` of `t` with `pY w = pY t`, we
have `w = t` (`t` is algebraic over `pY t`). -/
theorem eq_of_specializes_of_mem_center [IsSeparated pY] [IsModification π]
    (hY : IsNormalScheme Y) (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1)
    {t w : Y} (ht : t ∈ center π) (htw : t ⤳ w) (hpw : pY w = pY t) : w = t := by
  have halg : ValCurves.IsAlgebraicAt pY t :=
    (ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero pY t).mpr
      (ValCurves.fiberTrdeg_eq_zero_of_mem_center pY hY hcurve π ht)
  have hcl := ValCurves.isClosed_singleton_preimage_of_isAlgebraicAt pY rfl halg
  have hsp : (⟨t, rfl⟩ : pY ⁻¹' {pY t}) ⤳ ⟨w, hpw⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp htw
  have h := hsp.mem_closed hcl rfl
  exact congrArg Subtype.val h

/-- **The closure of a fibre over a specialization** (blueprint `lem:sm-connbirh-closure-fibre`).
In the setting of this file, let `y` be a point of the modification locus and `z` a
specialization of `y`. If `π⁻¹(y)` is preconnected, then so is `closure (π⁻¹(y)) ∩ π⁻¹(z)`. -/
theorem isPreconnected_closure_preimage_inter_preimage [Finite (PrimeSpectrum V)]
    [QuasiCompact pY] [IsSeparated pY] [LocallyOfFiniteType pY] [IsModification π]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    (hB : IsProjectiveOver (π ≫ pY)) (hY : IsNormalScheme Y)
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1) {y z : Y} (hy : y ∈ center π)
    (hyz : y ⤳ z) (hconn : _root_.IsPreconnected (π ⁻¹' {y})) :
    _root_.IsPreconnected (closure (π ⁻¹' {y}) ∩ π ⁻¹' {z}) := by
  classical
  have : Finite (Spec (CommRingCat.of V)) := inferInstanceAs (Finite (PrimeSpectrum V))
  have hfin : (center π : Set Y).Finite := ValCurves.finite_center pY hY hcurve π
  set F : Set B := π ⁻¹' {y} with hFdef
  have hFimg : ∀ w ∈ closure F, y ⤳ π w := by
    intro w hw
    have h := image_closure_subset_closure_image π.continuous ⟨w, hw, rfl⟩
    have hsub : π '' F ⊆ {y} := by
      rintro _ ⟨b, hb, rfl⟩
      exact hb
    exact specializes_iff_mem_closure.mpr (closure_mono hsub h)
  have hcomp : ∀ w : B, (π ≫ pY) w = pY (π w) := fun w => rfl
  have hFp : F ⊆ (π ≫ pY) ⁻¹' {pY y} := by
    intro b hb
    change (π ≫ pY) b = pY y
    rw [hcomp]
    exact congrArg pY hb
  have hFc : closure F ∩ (π ≫ pY) ⁻¹' {pY y} ⊆ F := by
    rintro w ⟨hw, hwp⟩
    exact eq_of_specializes_of_mem_center π pY hY hcurve hy (hFimg w hw) hwp
  have hL := isPreconnected_closure_inter_preimage hsep (π ≫ pY) hB (pY y) hFp hFc hconn (pY z)
  -- the points of the closure of `y` over `pY z`
  set T : Set Y := closure {y} ∩ pY ⁻¹' {pY z} with hTdef
  have hTS : T ⊆ center π := fun t ht =>
    closure_minimal (Set.singleton_subset_iff.mpr hy) (center π).isClosed ht.1
  have hTfin : T.Finite := hfin.subset hTS
  have hTt : ∀ t ∈ T, ∀ w, t ⤳ w → pY w = pY z → w = t := fun t ht w htw hw =>
    eq_of_specializes_of_mem_center π pY hY hcurve (hTS ht) htw (hw.trans ht.2.symm)
  have hzT : z ∈ T := ⟨specializes_iff_mem_closure.mp hyz, rfl⟩
  let C₁ : Set B := π ⁻¹' closure {z}
  let C₂ : Set B := π ⁻¹' (⋃ t ∈ T \ {z}, closure {t})
  have hC₁ : IsClosed C₁ := isClosed_closure.preimage π.continuous
  have hC₂ : IsClosed C₂ :=
    ((hTfin.subset Set.sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure).preimage
      π.continuous
  have hLC : closure F ∩ (π ≫ pY) ⁻¹' {pY z} ⊆ C₁ ∪ C₂ := by
    rintro w ⟨hw, hwp⟩
    have hwT : π w ∈ T := ⟨specializes_iff_mem_closure.mp (hFimg w hw), hwp⟩
    by_cases hwz : π w = z
    · left
      change π w ∈ closure {z}
      rw [hwz]
      exact subset_closure rfl
    · right
      exact Set.mem_iUnion₂.mpr ⟨π w, ⟨hwT, hwz⟩, subset_closure rfl⟩
  have hLd : (closure F ∩ (π ≫ pY) ⁻¹' {pY z}) ∩ (C₁ ∩ C₂) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun w ⟨⟨hw, hwp⟩, hw₁, hw₂⟩ => ?_
    obtain ⟨t, ⟨htT, htz⟩, hwt⟩ := Set.mem_iUnion₂.mp hw₂
    have h₁ : π w = z := hTt z hzT (π w) (specializes_iff_mem_closure.mpr hw₁) hwp
    have h₂ : π w = t := hTt t htT (π w) (specializes_iff_mem_closure.mpr hwt) hwp
    exact htz (h₂.symm.trans h₁)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hL) C₁ C₂ hC₁ hC₂ hLC hLd with h | h
  · have heq : closure F ∩ π ⁻¹' {z} = closure F ∩ (π ≫ pY) ⁻¹' {pY z} := by
      ext w
      constructor
      · rintro ⟨hw, hwz⟩
        refine ⟨hw, ?_⟩
        change (π ≫ pY) w = pY z
        rw [hcomp]
        exact congrArg pY hwz
      · rintro ⟨hw, hwp⟩
        exact ⟨hw, hTt z hzT (π w) (specializes_iff_mem_closure.mpr (h ⟨hw, hwp⟩)) hwp⟩
    rw [heq]
    exact hL
  · have heq : closure F ∩ π ⁻¹' {z} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun w ⟨hw, hwz⟩ => ?_
      have hwz' : π w = z := hwz
      have hwp : (π ≫ pY) w = pY z := by rw [hcomp, hwz']
      obtain ⟨t, ⟨htT, htz⟩, hwt⟩ := Set.mem_iUnion₂.mp (h ⟨hw, hwp⟩)
      have h₂ : π w = t := hTt t htT (π w) (specializes_iff_mem_closure.mpr hwt) (by rw [hwz'])
      exact htz (h₂.symm.trans hwz')
    rw [heq]
    exact isPreconnected_empty

end ClosureFibre

section Main

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))
  [IsIntegral B] [IsIntegral Y] [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)]

/-- **Zariski connectedness for a birational morphism onto a normal curve over a valuation ring
of finite height** (blueprint `thm:sm-connbirh-main`). Let `V` be a valuation ring with finitely
many primes such that `Frac (V ⧸ 𝔭)` is separably closed for every prime `𝔭`, `pY : Y → Spec V` of
finite presentation, quasi-compact and separated with `Y` integral, normal and of relative
dimension at most one, and `π : B → Y` birational and projective relative to `pY` with `B`
integral, flat and projective over `V`. If every point of the modification locus has infinite
residue field, every fibre `π⁻¹(z)` is preconnected. -/
theorem isPreconnected_preimage_singleton [Finite (PrimeSpectrum V)] [QuasiCompact pY]
    [IsSeparated pY]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    (hB : IsProjectiveOver (π ≫ pY)) (hπ : DeJong.IsRelativelyProjective pY π)
    (hY : IsNormalScheme Y) (hbir : Scheme.BirationalOver π (𝟙 Y))
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1)
    (hinf : ∀ w ∈ center π, Infinite (Y.residueField w)) (z : Y) :
    _root_.IsPreconnected (π ⁻¹' {z}) := by
  classical
  have := isModification_of_isRelativelyProjective π pY hπ hbir
  have : IsProper π := hπ.isProper
  have : Finite (Spec (CommRingCat.of V)) := inferInstanceAs (Finite (PrimeSpectrum V))
  have hfin : (center π : Set Y).Finite := ValCurves.finite_center pY hY hcurve π
  by_cases hz : z ∈ center π
  swap
  · -- `π` is an isomorphism over a neighbourhood of `z`
    have hzO : z ∈ isomorphismOpen π := by
      by_contra h
      exact hz h
    have : IsIso (π ∣_ isomorphismOpen π) := (le_isomorphismOpen_iff π _).mp le_rfl
    refine Set.Subsingleton.isPreconnected fun b hb b' hb' => ?_
    have hb₁ : π b = z := hb
    have hb₂ : π b' = z := hb'
    have hbO : π b ∈ isomorphismOpen π := hb₁ ▸ hzO
    have hb'O : π b' ∈ isomorphismOpen π := hb₂ ▸ hzO
    have h : (π ∣_ isomorphismOpen π) ⟨b, hbO⟩ = (π ∣_ isomorphismOpen π) ⟨b', hb'O⟩ :=
      Subtype.ext (by
        rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
        exact hb₁.trans hb₂.symm)
    exact congrArg Subtype.val ((π ∣_ isomorphismOpen π).homeomorph.injective h)
  -- induction on the number of generizations in the modification locus
  let G : Y → Set Y := fun w => {y | y ∈ center π ∧ y ⤳ w}
  have hGfin : ∀ w, (G w).Finite := fun w => hfin.subset fun y hy => hy.1
  suffices H : ∀ n : ℕ, ∀ w ∈ center π, (G w).ncard ≤ n → _root_.IsPreconnected (π ⁻¹' {w}) from
    H _ z hz le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hn
    have := hinf w hw
    refine isPreconnected_preimage_singleton_of_closure π.continuous π.isClosedMap (hGfin w)
      ⟨hw, specializes_rfl⟩ (fun v hv hwv => (hv.2.antisymm hwv).eq) (fun v hv => hv.2)
      (isPreconnected_preimage_generizations π pY hπ hY hbir hcurve w hw) ?_
    intro y hy hyw
    have hlt : (G y).ncard < (G w).ncard := by
      refine Set.ncard_lt_ncard ⟨fun v hv => ⟨hv.1, hv.2.trans hy.2⟩, fun hsub => hyw ?_⟩
        (hGfin w)
      have hwy := (hsub ⟨hw, specializes_rfl⟩).2
      exact (hy.2.antisymm hwy).eq
    exact isPreconnected_closure_preimage_inter_preimage π pY hsep hB hY hcurve hy.1 hy.2
      (ih _ (hlt.trans_le hn) y hy.1 le_rfl)

/-- **Zariski connectedness, connected form** (blueprint `thm:sm-connbirh-main`): if moreover the
residue field of `V` is infinite (e.g. algebraically closed), every fibre of `π` is connected. -/
theorem isConnected_preimage_singleton [Finite (PrimeSpectrum V)] [QuasiCompact pY]
    [IsSeparated pY] [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    (hB : IsProjectiveOver (π ≫ pY)) (hπ : DeJong.IsRelativelyProjective pY π)
    (hY : IsNormalScheme Y) (hbir : Scheme.BirationalOver π (𝟙 Y))
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1) (z : Y) :
    _root_.IsConnected (π ⁻¹' {z}) := by
  obtain ⟨b, hb⟩ := surjective_of_isRelativelyProjective π pY hπ hbir z
  exact ⟨⟨b, hb⟩, isPreconnected_preimage_singleton π pY hsep hB hπ hY hbir hcurve
    (fun w _ => infinite_residueField_of_infinite pY w) z⟩

/-- **Zariski connectedness for a projective normal curve** (blueprint
`cor:sm-connbirh-projective`; Temkin, proof of Lemma 4.4.2, T:3133): let `V` be a valuation ring
with finitely many primes, all `Frac (V ⧸ 𝔭)` separably closed and infinite (e.g. algebraically
closed) residue field, `pY : Y → Spec V` projective and of finite presentation with `Y` integral,
normal and of relative dimension at most one, and `π : B → Y` birational and projective relative to
`pY` with `B` integral and flat over `V`. Then every fibre of `π` is connected; in particular so is
`π⁻¹(x)` for every closed point `x` of the closed fibre. -/
theorem isConnected_preimage_singleton_of_isProjectiveOver [Finite (PrimeSpectrum V)]
    [Infinite (IsLocalRing.ResidueField V)]
    (hsep : ∀ p : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ p.asIdeal)))
    (hYp : IsProjectiveOver pY) (hπ : DeJong.IsRelativelyProjective pY π)
    (hY : IsNormalScheme Y) (hbir : Scheme.BirationalOver π (𝟙 Y))
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1) (z : Y) :
    _root_.IsConnected (π ⁻¹' {z}) := by
  have : IsProper pY := hYp.isProper
  exact isConnected_preimage_singleton π pY hsep
    (DeJong.IsRelativelyProjective.isProjectiveOver hYp hπ) hπ hY hbir hcurve z

/-- **Lane COH3D's height-one theorem without the residue field hypothesis** (blueprint
`cor:sm-connbirh-height-one`): over a valuation ring of height one with infinite residue field
(no projectivity or separable closedness needed), every fibre of `π` over a closed point is
connected (`ConnectedBirational.isConnected_preimage_singleton_of_heightOne`, whose hypothesis
`Infinite κ(x)` is supplied by `infinite_residueField_of_infinite`). -/
theorem isConnected_preimage_singleton_of_heightOne_of_infinite [QuasiCompact pY]
    [IsSeparated pY] [Infinite (IsLocalRing.ResidueField V)]
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y))
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1)
    (hV : ∀ P : Ideal V, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal V) (x : Y)
    (hx : IsClosed ({x} : Set Y)) : _root_.IsConnected (π ⁻¹' {x}) := by
  have := infinite_residueField_of_infinite pY x
  exact isConnected_preimage_singleton_of_heightOne π pY hπ hY hbir hcurve hV x hx

end Main

end

end DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight
