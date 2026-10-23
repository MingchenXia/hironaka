/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.Genus
import DeJongAlterations.StableModification.Cohomology.Connected
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeightClosure
import DeJongAlterations.StableModification.Valuation.SepClosed
import DeJongAlterations.StableModification.ValuationRing.FibreDimension
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField


/-!
# Closures of points of a projective scheme over a valuation ring

Let `V` be a valuation ring, `p : X → Spec V` (later: a projective nodal curve `C′`), `z ∈ X` with
image `s = p z` and `𝔭 = 𝔭_s`, and `W = V ⧸ 𝔭` (a valuation ring with fraction field `κ(s)`).
This file constructs the closure `Ȳ = closure {z}` with its reduced induced structure as a scheme
over `W` and proves the properties used by M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification/source/semi-stable.tex`,
cited `T:<line>`), proof of Lemma 4.4.4 (`emptylem`, T:3158–3176, in the corrected form of ERRATA
T57: blueprint `lem:sm-bd-closure-component`, `lem:sm-bd-exc-specialize`, chapter
`sm-blow-down-exceptional.tex`).

## Main definitions and results

* `closureScheme z`, `closureι z`: the reduced closure of `z`, an integral closed subscheme of `X`
  (`isIntegral_closureScheme`).
* `BaseRing p z = V ⧸ 𝔭`, `closureToBase p z : Ȳ → Spec W` with `Ȳ → Spec W → Spec V = Ȳ → X → Spec V`
  (`closureToBase_baseι`): **`Ȳ` lies over `W`**; it is projective over `W` if `X` is projective
  over `V` (`isProjectiveOver_closureToBase`) and **flat over `W`** (`flat_closureToBase`).
* `closureFibreι`: for a field point `φ : W → κ` over `a : Spec κ → Spec V`, the fibre `Ȳ_κ` is
  the base change of `Ȳ → X` to `X_a`, a closed subscheme of `X_a` with support `pr⁻¹(closure {z})`
  (`isPullback_closureFibreι`, `range_closureFibreι`).
* `residuePt t : Spec κ(t) → Spec V` (`κ(t) = Ideal.ResidueField`): the residue-field fibre
  `X_t = X ×_V κ(t)`, embedded onto `p⁻¹(t)` (`range_fst_residuePt`, `isEmbedding_fst_residuePt`);
  `isAlgClosed_residueField_of_ne_bot`: `κ(t)` is algebraically closed for `t ≠ 0` when
  `Frac V` is separably closed.
* `genericFibre p z`: the fibre of `Ȳ` over `κ(s) = Frac W`; it is an open subscheme of `Ȳ`, hence
  reduced, when `W` has finitely many primes (`isLocalization_away_of_finite`,
  `isReduced_genericFibre`); **a reduced closed subscheme of `X_s` with support
  `closure {z} ∩ X_s` is isomorphic to it** (`isIso_lift_genericFibreι`), so their Euler
  characteristics agree (`eulerChar_genericFibre_eq`).
* `fibreAt p z ht`: the fibre of `Ȳ` over a specialization `t` of `s`; **`χ(Ȳ_t) = χ(Ȳ_s)`**
  (`eulerChar_fibreAt_eq`, lane T44A's constancy of `χ` over the valuation ring `W`), and **the
  closure of `z` meets `X_t` in a connected set** (`isConnected_preimage_closure`, lane COH3C's
  Zariski connectedness over `W` for the irreducible `Ȳ`).

## Not formalized here

The étale-local part of `lem:sm-bd-closure-component` (that `Ȳ` is a nodal `W`-curve, that its
closed fibre is reduced, and the injections of boundary points and marks, Temkin's implicit claim
at T:3164–3166 checked through SS3's étale node charts) is stated as the hypothesis
`ExcSpecialize.ClosureComponentLocal` where it is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.BlowDown.ClosureComponent

universe u

open Cohomology Cohomology.ConnectedBirationalHeight

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Closure

variable {X : Scheme.{u}} (z : X)

/-- The ideal sheaf of the reduced closed subscheme structure on `closure {z}`. -/
def ideal : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {z}, isClosed_closure⟩

/-- The closure of `z` with its reduced induced structure. -/
abbrev closureScheme : Scheme.{u} := (ideal z).subscheme

/-- The closed immersion of the closure of `z`. -/
abbrev closureι : closureScheme z ⟶ X := (ideal z).subschemeι

/-- The reduced closure of `z` has image `closure {z}`. -/
theorem range_closureι : Set.range (closureι z) = closure {z} := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

instance isReduced_closureScheme : IsReduced (closureScheme z) :=
  Geometry.ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _

/-- `z` lies in the image of its reduced closure. -/
theorem mem_range_closureι : z ∈ Set.range (closureι z) := by
  rw [range_closureι]
  exact subset_closure rfl

/-- The point of the closure lying over `z` (its generic point). -/
def closurePt : closureScheme z := (mem_range_closureι z).choose

/-- `closurePt z` lies over `z`. -/
@[simp]
theorem closureι_closurePt : closureι z (closurePt z) = z :=
  (mem_range_closureι z).choose_spec

/-- Every point of the closure of `z` is a specialization of `closurePt z`. -/
theorem closurePt_specializes (t : closureScheme z) : closurePt z ⤳ t := by
  rw [← (closureι z).isClosedEmbedding.isInducing.specializes_iff, closureι_closurePt,
    specializes_iff_mem_closure, ← range_closureι]
  exact ⟨t, rfl⟩

instance irreducibleSpace_closureScheme : IrreducibleSpace (closureScheme z) := by
  rw [irreducibleSpace_def]
  have h : closure ({closurePt z} : Set (closureScheme z)) = Set.univ :=
    Set.eq_univ_of_forall fun t => specializes_iff_mem_closure.mp (closurePt_specializes z t)
  rw [Set.top_eq_univ, ← h]
  exact isIrreducible_singleton.closure

instance isIntegral_closureScheme : IsIntegral (closureScheme z) := by
  have : Nonempty (closureScheme z) := ⟨closurePt z⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- `closurePt z` is the generic point of the closure of `z`. -/
theorem dense_singleton_closurePt : Dense ({closurePt z} : Set (closureScheme z)) := by
  rw [dense_iff_closure_eq]
  exact Set.eq_univ_of_forall fun t => specializes_iff_mem_closure.mp (closurePt_specializes z t)

end Closure

section Valuation

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V)) (z : X)

/-- The prime `𝔭 = p(z)` of `V` below `z`. -/
abbrev basePrime : Ideal V := (p z).asIdeal

/-- The valuation ring `W = V ⧸ 𝔭` over which the closure of `z` lives. -/
abbrev BaseRing : Type u := V ⧸ basePrime p z

instance : IsDomain (BaseRing p z) := Ideal.Quotient.isDomain _

instance [IsDomain V] [ValuationRing V] : ValuationRing (BaseRing p z) :=
  Function.Surjective.valuationRing (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance [Finite (PrimeSpectrum V)] : Finite (PrimeSpectrum (BaseRing p z)) :=
  Finite.of_injective _ (PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective)

/-- The closed immersion `Spec W → Spec V`. -/
abbrev baseι : Spec (CommRingCat.of (BaseRing p z)) ⟶ Spec (CommRingCat.of V) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (basePrime p z)))

instance isClosedImmersion_baseι : IsClosedImmersion (baseι p z) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- `Spec W → Spec V` is injective. -/
theorem baseι_injective : Function.Injective (baseι p z) :=
  PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective

/-- The generic point of `Spec W` maps to `p z`. -/
theorem baseι_bot : baseι p z (⊥ : PrimeSpectrum (BaseRing p z)) = p z := by
  apply PrimeSpectrum.ext
  change Ideal.comap (Ideal.Quotient.mk (basePrime p z)) ⊥ = (p z).asIdeal
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

instance compactSpace_closureScheme [CompactSpace X] : CompactSpace (closureScheme z) :=
  (closureι z).isClosedEmbedding.compactSpace

/-- Every point of the closure of `z` lies over `V(𝔭)`, `𝔭 = 𝔭_{p z}`. -/
theorem le_asIdeal (t : closureScheme z) : basePrime p z ≤ (p (closureι z t)).asIdeal := by
  have hmem : closureι z t ∈ closure {z} := by
    rw [← range_closureι]
    exact ⟨t, rfl⟩
  have h : p z ⤳ p (closureι z t) :=
    (specializes_iff_mem_closure.mpr hmem).map p.continuous
  exact (PrimeSpectrum.le_iff_specializes _ _).mpr h

variable [CompactSpace X]

/-- The closure of `z` maps to `Spec W` compatibly with `X → Spec V`. -/
theorem exists_closureToBase : ∃ g : closureScheme z ⟶ Spec (CommRingCat.of (BaseRing p z)),
    g ≫ baseι p z = closureι z ≫ p :=
  exists_comp_eq_of_forall_le (closureι z ≫ p) (basePrime p z) (le_asIdeal p z)

/-- The structure morphism of the closure of `z` over `W = V ⧸ 𝔭`. -/
def closureToBase : closureScheme z ⟶ Spec (CommRingCat.of (BaseRing p z)) :=
  (exists_closureToBase p z).choose

/-- The structure map of the closure over `W` lifts `closure {z} → X → Spec V`. -/
@[reassoc (attr := simp)]
theorem closureToBase_baseι : closureToBase p z ≫ baseι p z = closureι z ≫ p :=
  (exists_closureToBase p z).choose_spec

/-- Pointwise form of `closureToBase_baseι`. -/
theorem baseι_closureToBase_apply (t : closureScheme z) :
    baseι p z (closureToBase p z t) = p (closureι z t) := by
  rw [← Scheme.Hom.comp_apply, closureToBase_baseι, Scheme.Hom.comp_apply]

/-- The generic point of the closure lies over the generic point of `Spec W`. -/
theorem closureToBase_closurePt : closureToBase p z (closurePt z) = (⊥ : PrimeSpectrum (BaseRing p z)) := by
  apply baseι_injective p z
  rw [baseι_closureToBase_apply, closureι_closurePt, baseι_bot]

/-- **The closure of `z` is projective over `W`** if `X` is projective over `V`. -/
theorem isProjectiveOver_closureToBase (hp : IsProjectiveOver p) :
    IsProjectiveOver (closureToBase p z) :=
  isProjectiveOver_of_comp_surjective _ Ideal.Quotient.mk_surjective (closureToBase p z)
    (by rw [closureToBase_baseι]; exact DeJong.IsProjectiveOver.comp_isClosedImmersion hp _)

instance flat_closureToBase [IsDomain V] [ValuationRing V] : Flat (closureToBase p z) := by
  refine flat_of_dense_preimage_bot (closureToBase p z) ?_
  refine (dense_singleton_closurePt z).mono ?_
  rintro _ rfl
  exact closureToBase_closurePt p z

end Valuation


section Fibre

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V)) (z : X)
  [CompactSpace X] {κ : Type u} [Field κ] (φ : BaseRing p z →+* κ)
  (a : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of V))
  (ha : Spec.map (CommRingCat.ofHom φ) ≫ baseι p z = a)

include ha

/-- The fibre of the closure of `z` over a field point `φ : W → κ` is a pullback over `V`. -/
theorem isPullback_closureFibre :
    IsPullback (pullback.fst (closureToBase p z) (Spec.map (CommRingCat.ofHom φ)))
      (pullback.snd (closureToBase p z) (Spec.map (CommRingCat.ofHom φ))) (closureι z ≫ p) a := by
  have H : IsPullback (pullback.fst (closureToBase p z) (Spec.map (CommRingCat.ofHom φ)))
      (pullback.snd (closureToBase p z) (Spec.map (CommRingCat.ofHom φ)))
      (closureToBase p z ≫ baseι p z) (Spec.map (CommRingCat.ofHom φ) ≫ baseι p z) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono (closureToBase p z)
      (Spec.map (CommRingCat.ofHom φ)) (baseι p z))
  rw [closureToBase_baseι, ha] at H
  exact H

/-- The closed immersion of the fibre of the closure of `z` over `φ` into the fibre of `X` over
the induced field point `a = φ ∘ (V → W)`. -/
def closureFibreι :
    pullback (closureToBase p z) (Spec.map (CommRingCat.ofHom φ)) ⟶ pullback p a :=
  pullback.lift (pullback.fst _ _ ≫ closureι z) (pullback.snd _ _)
    (by rw [Category.assoc, (isPullback_closureFibre p z φ a ha).w])

/-- The fibre of the closure maps to `X` through the closure. -/
@[reassoc (attr := simp)]
theorem closureFibreι_fst : closureFibreι p z φ a ha ≫ pullback.fst p a =
    pullback.fst _ _ ≫ closureι z :=
  pullback.lift_fst _ _ _

/-- The fibre of the closure lies over the field point. -/
@[reassoc (attr := simp)]
theorem closureFibreι_snd : closureFibreι p z φ a ha ≫ pullback.snd p a = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The fibre of the closure of `z` is the base change of the closed immersion `closure {z} → X`
to the fibre of `X`. -/
theorem isPullback_closureFibreι :
    IsPullback (closureFibreι p z φ a ha) (pullback.fst _ _) (pullback.fst p a) (closureι z) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p a) (h₂₂ := p) (v₁₃ := a) ?_
    (closureFibreι_fst p z φ a ha) (IsPullback.of_hasPullback p a).flip
  rw [closureFibreι_snd]
  exact (isPullback_closureFibre p z φ a ha).flip

instance isClosedImmersion_closureFibreι : IsClosedImmersion (closureFibreι p z φ a ha) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_closureFibreι p z φ a ha).flip inferInstance

/-- The fibre of the closure has support `pr⁻¹(closure {z})` in `X_a`. -/
theorem range_closureFibreι :
    Set.range (closureFibreι p z φ a ha) = pullback.fst p a ⁻¹' closure {z} := by
  have h := (isPullback_closureFibreι p z φ a ha).isoPullback_hom_fst
  rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (isPullback_closureFibreι p z φ a ha).isoPullback.hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst, range_closureι]

end Fibre



section ResiduePoint

variable {V : Type u} [CommRing V]

/-- The residue field point `Spec κ(t) → Spec V` of a prime `t`, with `κ(t) = Frac (V ⧸ t)`
(`Ideal.ResidueField`). -/
abbrev residuePt (t : PrimeSpectrum V) :
    Spec (CommRingCat.of t.asIdeal.ResidueField) ⟶ Spec (CommRingCat.of V) :=
  Spec.map (CommRingCat.ofHom (algebraMap V t.asIdeal.ResidueField))

/-- `residuePt t` is the residue field morphism of `Spec V` at `t`, up to the canonical isomorphism. -/
theorem residuePt_eq (t : PrimeSpectrum V) :
    residuePt t = Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of V) t).hom ≫
      (Spec (CommRingCat.of V)).fromSpecResidueField t := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

instance isPreimmersion_residuePt (t : PrimeSpectrum V) : IsPreimmersion (residuePt t) := by
  rw [residuePt_eq]
  infer_instance

/-- `Spec κ(t) → Spec V` maps its point to `t`. -/
theorem residuePt_apply (t : PrimeSpectrum V) (x : Spec (CommRingCat.of (t.asIdeal.ResidueField))) :
    residuePt t x = t := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V t.asIdeal.ResidueField) x.asIdeal = t.asIdeal
  have hx : x.asIdeal = ⊥ := by
    have := x.isPrime
    exact Ideal.eq_bot_of_prime x.asIdeal
  rw [hx, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

/-- The image of `Spec κ(t) → Spec V` is `{t}`. -/
theorem range_residuePt (t : PrimeSpectrum V) : Set.range (residuePt t) = {t} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact residuePt_apply t x
  · intro hy
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of t.asIdeal.ResidueField)) := inferInstance
    exact ⟨x, (residuePt_apply t x).trans hy.symm⟩

variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V)) (t : PrimeSpectrum V)

/-- The residue-field fibre `X_t` maps onto the set-theoretic fibre `p⁻¹(t)`. -/
theorem range_fst_residuePt : Set.range (pullback.fst p (residuePt t)) = p ⁻¹' {t} := by
  rw [Scheme.Pullback.range_fst, range_residuePt]

/-- The residue-field fibre `X_t → X` is an embedding. -/
theorem isEmbedding_fst_residuePt : IsEmbedding (pullback.fst p (residuePt t)) :=
  (pullback.fst p (residuePt t)).isEmbedding

end ResiduePoint


section AlgClosed

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]

/-- **The residue fields of the non-generic points of `Spec V` are algebraically closed** when the
fraction field of the valuation ring `V` is separably closed (Temkin T:2797–2799; lane VB's
`Valuation.isAlgClosed_residueField` for the valuation ring `V_t`). -/
theorem isAlgClosed_residueField_of_ne_bot
    (hsep : IsSepClosed (FractionRing (V ⧸ (⊥ : Ideal V)))) (t : PrimeSpectrum V)
    (ht : t.asIdeal ≠ ⊥) : IsAlgClosed t.asIdeal.ResidueField := by
  have : ValuationRing (Localization.AtPrime t.asIdeal) :=
    { toPreValuationRing := ValuationRing.preValuationRing_of_isLocalization t.asIdeal.primeCompl }
  have : IsSepClosed (FractionRing V) :=
    Cohomology.Connected.isSepClosed_of_ringEquiv
      (IsFractionRing.ringEquivOfRingEquiv (A := V ⧸ (⊥ : Ideal V)) (B := V)
        (K := FractionRing (V ⧸ (⊥ : Ideal V))) (L := FractionRing V) (RingEquiv.quotientBot V))
  have hR : ¬ IsField (Localization.AtPrime t.asIdeal) := by
    intro hF
    have hmax := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
    apply ht
    rw [← Localization.AtPrime.under_maximalIdeal (I := t.asIdeal), hmax, Ideal.under,
      Ideal.comap_bot_of_injective]
    exact IsLocalization.injective (Localization.AtPrime t.asIdeal) t.asIdeal.primeCompl_le_nonZeroDivisors
  exact Valuation.isAlgClosed_residueField (Localization.AtPrime t.asIdeal) (FractionRing V) hR

end AlgClosed

section Localization

variable {W : Type u} [CommRing W] [IsDomain W] [Finite (PrimeSpectrum W)]

/-- In a domain with finitely many primes some nonzero element lies in every nonzero prime. -/
theorem exists_ne_zero_forall_mem : ∃ a : W, a ≠ 0 ∧ ∀ P : PrimeSpectrum W, P.asIdeal ≠ ⊥ → a ∈ P.asIdeal := by
  classical
  have : Fintype {P : PrimeSpectrum W // P.asIdeal ≠ ⊥} := Fintype.ofFinite _
  have hP : ∀ P : {P : PrimeSpectrum W // P.asIdeal ≠ ⊥}, ∃ b ∈ P.1.asIdeal, b ≠ 0 :=
    fun P => Submodule.exists_mem_ne_zero_of_ne_bot P.2
  choose b hb hb0 using hP
  refine ⟨∏ P, b P, Finset.prod_ne_zero_iff.mpr fun P _ => hb0 P, fun P hP0 => ?_⟩
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem b (Finset.mem_univ ⟨P, hP0⟩)) (hb ⟨P, hP0⟩)

/-- Every nonzero element of a domain with finitely many primes divides a power of the element of
`exists_ne_zero_forall_mem`. -/
theorem dvd_pow_of_forall_mem {a : W} (ha : ∀ P : PrimeSpectrum W, P.asIdeal ≠ ⊥ → a ∈ P.asIdeal)
    {w : W} (hw : w ≠ 0) : ∃ n : ℕ, w ∣ a ^ n := by
  have hrad : a ∈ (Ideal.span {w}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    refine ha ⟨J, hJp⟩ fun h => hw ?_
    have : w ∈ J := hJ (Ideal.mem_span_singleton_self w)
    change J = ⊥ at h
    rw [h] at this
    exact this
  obtain ⟨n, hn⟩ := hrad
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

/-- **The fraction field of a domain with finitely many primes is a localization at one element.** -/
theorem isLocalization_away_of_finite (K : Type u) [Field K] [Algebra W K] [IsFractionRing W K]
    {a : W} (ha0 : a ≠ 0) (ha : ∀ P : PrimeSpectrum W, P.asIdeal ≠ ⊥ → a ∈ P.asIdeal) :
    IsLocalization.Away a K where
  map_units := by
    rintro ⟨y, n, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [map_pow]
    exact pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective W K)).mpr ha0)
  surj z := by
    obtain ⟨⟨x, d⟩, hxd⟩ := IsLocalization.surj (nonZeroDivisors W) z
    obtain ⟨n, c, hc⟩ := dvd_pow_of_forall_mem ha (nonZeroDivisors.ne_zero d.2)
    refine ⟨⟨x * c, ⟨a ^ n, n, rfl⟩⟩, ?_⟩
    simp only
    rw [hc, map_mul, map_mul, ← hxd, mul_assoc]
  exists_of_eq {x y} h := ⟨1, by rw [IsFractionRing.injective W K h]⟩

end Localization


section GenericFibre

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V)) (z : X)

/-- The residue field `κ(s)` of the point `s = p z` is the fraction field of `W = V ⧸ 𝔭`. -/
abbrev GenericField : Type u := (p z).asIdeal.ResidueField

/-- `Spec κ(s) → Spec W → Spec V` is the residue point of `s = p z`. -/
theorem specMap_algebraMap_baseι :
    Spec.map (CommRingCat.ofHom (algebraMap (BaseRing p z) (GenericField p z))) ≫ baseι p z =
      residuePt (p z) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable [Finite (PrimeSpectrum V)]

instance isOpenImmersion_specMap_genericField :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (BaseRing p z) (GenericField p z)))) := by
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_forall_mem (W := BaseRing p z)
  have := isLocalization_away_of_finite (GenericField p z) ha0 ha
  exact IsOpenImmersion.of_isLocalization a

variable [CompactSpace X]

instance isOpenImmersion_genericFibre_fst :
    IsOpenImmersion (pullback.fst (closureToBase p z)
      (Spec.map (CommRingCat.ofHom (algebraMap (BaseRing p z) (GenericField p z))))) :=
  inferInstance

/-- **The generic fibre of the closure of `z` over `W` is reduced** (an open subscheme of the
integral closure of `z`, as `Spec Frac W → Spec W` is an open immersion for `W` of finite
height). -/
instance isReduced_genericFibre :
    IsReduced (pullback (closureToBase p z)
      (Spec.map (CommRingCat.ofHom (algebraMap (BaseRing p z) (GenericField p z))))) :=
  isReduced_of_isOpenImmersion (pullback.fst _ _)

end GenericFibre


section Kernel

variable {P Y : Scheme.{u}}

/-- The kernel of a quasi-compact morphism out of a reduced scheme is radical. -/
theorem ker_radical_of_isReduced (f : P ⟶ Y) [QuasiCompact f] [IsReduced P] :
    f.ker.radical = f.ker := by
  refine le_antisymm (fun U => ?_) (Scheme.IdealSheafData.le_radical _)
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have hn' : x ^ n ∈ RingHom.ker (f.app U).hom := by rwa [← Scheme.Hom.ker_apply]
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  rw [RingHom.mem_ker, map_pow] at hn'
  exact IsReduced.eq_zero _ ⟨n, hn'⟩

/-- For a reduced source the kernel is the vanishing ideal of the closure of the image. -/
theorem ker_eq_vanishingIdeal_of_isReduced (f : P ⟶ Y) [QuasiCompact f] [IsReduced P] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range f), isClosed_closure⟩ := by
  rw [← ker_radical_of_isReduced, ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  ext1
  exact Scheme.Hom.support_ker f

/-- Closed immersions from reduced schemes with the same image have the same kernel. -/
theorem ker_eq_of_range_eq {P₁ P₂ : Scheme.{u}} (i₁ : P₁ ⟶ Y) (i₂ : P₂ ⟶ Y) [QuasiCompact i₁]
    [QuasiCompact i₂] [IsReduced P₁] [IsReduced P₂] (h : Set.range i₁ = Set.range i₂) :
    i₁.ker = i₂.ker := by
  rw [ker_eq_vanishingIdeal_of_isReduced, ker_eq_vanishingIdeal_of_isReduced]
  congr 2
  rw [h]

end Kernel


section GenericChi

variable {V : Type u} [CommRing V] [Finite (PrimeSpectrum V)] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of V)) (z : X) [CompactSpace X] [IsSeparated p]

instance isSeparated_closureToBase : IsSeparated (closureToBase p z) := by
  have : IsSeparated (closureToBase p z ≫ baseι p z) := by
    rw [closureToBase_baseι]; infer_instance
  exact IsSeparated.of_comp _ (baseι p z)

/-- The generic fibre of the closure of `z` over `W`, i.e. over `κ(s)`, `s = p z`. -/
abbrev genericFibre : Scheme.{u} :=
  pullback (closureToBase p z)
    (Spec.map (CommRingCat.ofHom (algebraMap (BaseRing p z) (GenericField p z))))

/-- The closed immersion of the generic fibre of the closure into the fibre `X_s`. -/
abbrev genericFibreι : genericFibre p z ⟶ pullback p (residuePt (p z)) :=
  closureFibreι p z _ _ (specMap_algebraMap_baseι p z)

instance isAffineHom_diagonal_genericFibre :
    IsAffineHom (pullback.diagonal (terminal.from (genericFibre p z))) :=
  BlowDown.isAffineHom_diagonal_of_isSeparated (bcSnd _ (closureToBase p z))

variable {P : Scheme.{u}} [IsReduced P] [CompactSpace P]
  [IsAffineHom (pullback.diagonal (terminal.from P))] (i : P ⟶ pullback p (residuePt (p z)))
  [IsClosedImmersion i] (hi : Set.range i = pullback.fst p (residuePt (p z)) ⁻¹' closure {z})

include hi in
/-- The generic fibre of the closure and `i` have the same kernel in `X_s`. -/
theorem ker_genericFibreι_eq : (genericFibreι p z).ker = i.ker :=
  ker_eq_of_range_eq _ _ (by rw [range_closureFibreι, hi])

include hi in
/-- **A reduced closed subscheme of `X_s` supported on `closure {z} ∩ X_s` is the generic fibre
of the closure of `z`.** -/
theorem isIso_lift_genericFibreι :
    IsIso (IsClosedImmersion.lift (genericFibreι p z) i (ker_genericFibreι_eq p z i hi).le) :=
  IsClosedImmersion.isIso_lift _ _ (ker_genericFibreι_eq p z i hi)

include hi in
/-- The Euler characteristic of the generic fibre of the closure of `z` is that of any reduced
closed subscheme of `X_s` with the same support. -/
theorem eulerChar_genericFibre_eq :
    CurvesField.Genus.eulerChar (genericFibre p z)
        (structureCoeff (bcSnd (algebraMap (BaseRing p z) (GenericField p z)) (closureToBase p z))) =
      CurvesField.Genus.eulerChar P (structureCoeff (i ≫ pullback.snd p (residuePt (p z)))) := by
  have := isIso_lift_genericFibreι p z i hi
  refine (BlowDown.eulerChar_eq_of_iso _ _
    (asIso (IsClosedImmersion.lift (genericFibreι p z) i (ker_genericFibreι_eq p z i hi).le)) ?_).symm
  have h := IsClosedImmersion.lift_fac (genericFibreι p z) i (ker_genericFibreι_eq p z i hi).le
  rw [asIso_hom, bcSnd, ← closureFibreι_snd p z _ _ (specMap_algebraMap_baseι p z),
    ← Category.assoc, h]

end GenericChi


section FibreAt

variable {V : Type u} [CommRing V] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V)) (z : X)
  {t : PrimeSpectrum V} (ht : p z ⤳ t)

/-- The field point `W = V ⧸ 𝔭 → κ(t)` of a specialization `t` of `p z`. -/
def fieldPt : BaseRing p z →+* t.asIdeal.ResidueField :=
  Ideal.Quotient.lift _ (algebraMap V t.asIdeal.ResidueField) fun _ ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr
      ((PrimeSpectrum.le_iff_specializes _ _).mpr ht ha)

include ht in
/-- `Spec κ(t) → Spec W → Spec V` is the residue point of `t`. -/
theorem specMap_fieldPt_baseι :
    Spec.map (CommRingCat.ofHom (fieldPt p z ht)) ≫ baseι p z = residuePt t := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable [CompactSpace X]

/-- The fibre of the closure of `z` over a specialization `t` of `p z`. -/
abbrev fibreAt : Scheme.{u} :=
  pullback (closureToBase p z) (Spec.map (CommRingCat.ofHom (fieldPt p z ht)))

/-- The closed immersion of the fibre of the closure of `z` over `t` into the fibre `X_t`. -/
abbrev fibreAtι : fibreAt p z ht ⟶ pullback p (residuePt t) :=
  closureFibreι p z _ _ (specMap_fieldPt_baseι p z ht)

/-- The fibre of the closure over `t` has support `pr⁻¹(closure {z})` in `X_t`. -/
theorem range_fibreAtι :
    Set.range (fibreAtι p z ht) = pullback.fst p (residuePt t) ⁻¹' closure {z} :=
  range_closureFibreι _ _ _ _ _

variable [IsSeparated p]

instance isAffineHom_diagonal_fibreAt :
    IsAffineHom (pullback.diagonal (terminal.from (fibreAt p z ht))) :=
  BlowDown.isAffineHom_diagonal_of_isSeparated (bcSnd _ (closureToBase p z))

variable [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]

/-- **Constancy of `χ` along the closure of `z`** (Temkin, proof of Lemma 4.4.4 via 4.4.2; lane
COH3A/T44A over the valuation ring `W = V ⧸ 𝔭`): the Euler characteristic of the fibre of the
closure of `z` over a specialization `t` of `s = p z` is that of its generic fibre. -/
theorem eulerChar_fibreAt_eq (hp : IsProjectiveOver p) :
    CurvesField.Genus.eulerChar (fibreAt p z ht)
        (structureCoeff (bcSnd (fieldPt p z ht) (closureToBase p z))) =
      CurvesField.Genus.eulerChar (genericFibre p z)
        (structureCoeff (bcSnd (algebraMap (BaseRing p z) (GenericField p z))
          (closureToBase p z))) := by
  obtain ⟨D⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver
    (isProjectiveOver_closureToBase p z hp)
  have := BlowDown.isAffineHom_diagonal_of_isSeparated (closureToBase p z)
  exact BlowDown.eulerChar_fibre_eq D (fun i => BlowDown.flat_sectionsModuleCat_unit _ (D.U i)) _ _

end FibreAt


section Connected

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Finite (PrimeSpectrum V)]
  {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of V)) (z : X) [CompactSpace X]
  {t : PrimeSpectrum V} (ht : p z ⤳ t)

/-- The point of `Spec W` corresponding to a specialization `t` of `p z`. -/
def basePt : Spec (CommRingCat.of (BaseRing p z)) :=
  Spec.map (CommRingCat.ofHom (fieldPt p z ht))
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of t.asIdeal.ResidueField))))

/-- `basePt p z ht` lies over `t`. -/
theorem baseι_basePt : baseι p z (basePt p z ht) = t := by
  rw [basePt, ← Scheme.Hom.comp_apply, specMap_fieldPt_baseι, residuePt_apply]

/-- The points of the closure of `z` over `t` are the image of the fibre of `closure {z} → Spec W`. -/
theorem closure_inter_preimage_eq :
    closure {z} ∩ p ⁻¹' {t} = closureι z '' (closureToBase p z ⁻¹' {basePt p z ht}) := by
  ext x
  constructor
  · rintro ⟨hx, hxt⟩
    rw [← range_closureι] at hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    apply baseι_injective p z
    rw [baseι_closureToBase_apply, baseι_basePt]
    exact hxt
  · rintro ⟨y, hy, rfl⟩
    refine ⟨range_closureι z ▸ ⟨y, rfl⟩, ?_⟩
    change p (closureι z y) = t
    rw [← baseι_closureToBase_apply, hy, baseι_basePt]

include ht in
/-- **The closure of `z` meets the fibre over every specialization `t` of `p z` in a connected
set** (lane COH3C's Zariski connectedness over `W = V ⧸ 𝔭` for the irreducible closure of `z`),
as a subset of the fibre scheme `X_t`. -/
theorem isConnected_preimage_closure
    (hsep : ∀ P : PrimeSpectrum V, IsSepClosed (FractionRing (V ⧸ P.asIdeal)))
    (hp : IsProjectiveOver p) :
    _root_.IsConnected (pullback.fst p (residuePt t) ⁻¹' closure {z}) := by
  have hsepW := isSepClosed_quotient hsep (basePrime p z)
  have hcon := Cohomology.Connected.isConnected_fiber_of_irreducibleSpace hsepW
    (closureToBase p z) (isProjectiveOver_closureToBase p z hp) (basePt p z ht)
  have himg : _root_.IsConnected (closure {z} ∩ p ⁻¹' {t}) := by
    rw [closure_inter_preimage_eq p z ht]
    exact hcon.image _ (closureι z).continuous.continuousOn
  have he := isEmbedding_fst_residuePt p t
  have hcl : pullback.fst p (residuePt t) '' (pullback.fst p (residuePt t) ⁻¹' closure {z}) =
      closure {z} ∩ p ⁻¹' {t} := by
    rw [Set.image_preimage_eq_inter_range, range_fst_residuePt]
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := himg.nonempty
    rw [← hcl] at hx
    obtain ⟨y, hy, -⟩ := hx
    exact ⟨y, hy⟩
  · rw [← he.isInducing.isPreconnected_image, hcl]
    exact himg.isPreconnected

end Connected

end DeJongAlterations.StableModification.BlowDown.ClosureComponent
