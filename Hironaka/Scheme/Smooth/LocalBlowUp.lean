/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Hironaka.Algebra.Local.ChartRing
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Algebra.Local.Chart
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership
import Hironaka.Scheme.BlowUp.FlatBaseChange
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Hironaka.Scheme.Smooth.ChartRing
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The local blow-up as a base change

Hauser defines the local blow-up of `X` along `Z` at `x' ∈ π⁻¹(x)` as the morphism of germs
`(X', x') → (X, x)` [Hau14, Definition 4.15], and as the localization `R → R[Ig⁻¹]_𝔭` of a chart of
the blow-up of the local ring `R = 𝒪_{X,x}` [Hau14, Definition 4.16]. The two agree because the
blow-up of `Spec 𝒪_{X,x}` along the stalk `I_x` of `Z` is the base change of `B_Z X` along
`Spec 𝒪_{X,x} → X` (`exists_isPullback_fromSpecStalk`; blow-ups commute with flat base change,
[Sta, Tag 0805], since `X.fromSpecStalk x` is flat, being a localization on an affine
neighbourhood (`flat_fromSpecStalk`), and the pullback of `Z` along it is the ideal sheaf of `I_x`
(`comap_fromSpecStalk_eq_specIdealSheaf`)). The file also relates the origin of the chart of `x_ρ`
of the local blow-up, `chartOrigin` of `Hironaka/Algebra/Local/Chart.lean`, to a point of `B_Z X`
over `x` whose stalk is the localization of the chart ring at the origin
(`exists_stalk_equiv_localization_chartOrigin_of_isIso`), granted that the stalks of the local
blow-up are those of `B_Z X` (proved in `Hironaka/Scheme/Smooth/LocalBlowUpStalk.lean`).

Used for the charts of the local blow-up (`LocalBlowUpChart.lean`) and for the order of an ideal
along the exceptional divisor (`Hironaka/Scheme/IdealSheaf/Order/ExceptionalOrder.lean`).
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

open AlgebraicGeometry Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- `Spec 𝒪_{X,x} → X` is flat: on an affine open `U ∋ x` it is `Spec` of the localization
`Γ(X, U) → 𝒪_{X,x}` followed by the open immersion `Spec Γ(X, U) ≅ U ⊆ X`. -/
theorem flat_fromSpecStalk (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [Flat.SpecMap_iff]
    let _ := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    have hflat : Module.Flat Γ(X, U) (X.presheaf.stalk x) :=
      IsLocalization.flat _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    exact RingHom.flat_algebraMap_iff.mpr hflat
  have : Flat hU.fromSpec := inferInstance
  exact Flat.comp _ _

/-- The pullback of `Z` along `Spec 𝒪_{X,x} → X` is the ideal sheaf of the stalk `I_x` of `Z`. -/
theorem comap_fromSpecStalk_eq_specIdealSheaf (Z : X.IdealSheafData) (x : X) :
    Z.comap (X.fromSpecStalk x) = specIdealSheaf (Z.stalkIdeal x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  have e : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
    intro y _
    have hy : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hy
    exact hy.mem_open U.2 hxU
  rw [Z.ideal_comap_of_le (X.fromSpecStalk x) ⟨U, hU⟩ ⟨⊤, isAffineOpen_top _⟩ e,
    specIdealSheaf_ideal_top, Scheme.IdealSheafData.stalkIdeal_eq_map_germ Z ⟨U, hU⟩ hxU,
    Ideal.map_map]
  congr 1
  change ((X.fromSpecStalk x).app U ≫
    (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE e).op).hom = _
  rw [Scheme.fromSpecStalk_app hxU, Category.assoc, Category.assoc, ← Functor.map_comp, ← op_comp,
    show homOfLE e ≫ homOfLE (le_top : X.fromSpecStalk x ⁻¹ᵁ U ≤ ⊤) = 𝟙 _ from
      Subsingleton.elim _ _,
    op_id, CategoryTheory.Functor.map_id, Category.comp_id, CommRingCat.hom_comp]
  rfl

/-- The blow-up of `Spec 𝒪_{X,x}` along the stalk `I_x` of `Z`, the affine blow-up of the local
ring, is the base change of `B_Z X` along `Spec 𝒪_{X,x} → X`: the local blow-up as a morphism of
germs ([Hau14, Definition 4.15]; [Sta, Tag 0805]). -/
theorem exists_isPullback_fromSpecStalk (Z : X.IdealSheafData) (x : X) :
    ∃ φ : affineBlowUp (Z.stalkIdeal x) ⟶ blowUp Z,
      IsPullback φ (affineBlowUp.π (Z.stalkIdeal x)) (blowUpπ Z) (X.fromSpecStalk x) := by
  have := flat_fromSpecStalk x
  have h₁ : IsBlowUp (Z.comap (X.fromSpecStalk x)) (affineBlowUp.π (Z.stalkIdeal x)) := by
    rw [comap_fromSpecStalk_eq_specIdealSheaf]
    exact affineBlowUp.isBlowUp _
  exact (blowUp.isBlowUp Z).exists_isPullback_of_flat (X.fromSpecStalk x) h₁

/-- Germs along a base change of `Spec 𝒪_{X,x} → X`: for `g = ψ ≫ X.fromSpecStalk x`, the stalk map
of `g` at `q` sends the germ of a section `s` at `g q` to `ψ^♯` of the germ at `ψ q` of the
"constant" `s_x ∈ 𝒪_{X,x} = Γ(Spec 𝒪_{X,x}, ⊤)` (Mathlib's `fromSpecStalk_app`). -/
theorem stalkMap_germ_eq_of_eq_comp_fromSpecStalk {Y : Scheme.{u}} (x : X)
    {ψ : Y ⟶ Spec (X.presheaf.stalk x)} (g : Y ⟶ X) (hg : g = ψ ≫ X.fromSpecStalk x) (q : Y)
    (V : X.Opens) (hxV : x ∈ V) (hV : g q ∈ V) (s : Γ(X, V)) :
    g.stalkMap q (X.presheaf.germ V (g q) hV s) =
      ψ.stalkMap q ((Spec (X.presheaf.stalk x)).presheaf.germ ⊤ (ψ q) trivial
        ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (X.presheaf.germ V x hxV s))) := by
  subst hg
  have hV' : X.fromSpecStalk x (ψ q) ∈ V := hV
  rw [Scheme.Hom.stalkMap_comp]
  change ψ.stalkMap q ((X.fromSpecStalk x).stalkMap (ψ q)
    (X.presheaf.germ V (X.fromSpecStalk x (ψ q)) hV' s)) = _
  congr 1
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.fromSpecStalk_app hxV, CommRingCat.comp_apply,
    CommRingCat.comp_apply]
  exact (Spec (X.presheaf.stalk x)).presheaf.germ_res_apply (homOfLE le_top) (ψ q) hV' _

/-- A point of `Spec S` lying over the maximal ideal of a local ring `R` is sent by `Spec` of
`R → S` to the closed point. -/
theorem Spec_map_eq_closedPoint {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S]
    (f : R →+* S) (p : Spec (CommRingCat.of S))
    (h : (PrimeSpectrum.asIdeal p).comap f = IsLocalRing.maximalIdeal R) :
    Spec.map (CommRingCat.ofHom f) p = IsLocalRing.closedPoint R := by
  rw [Spec.map_apply]
  exact PrimeSpectrum.ext h

section Origin

open IsLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ} (x : Fin n → R)
  (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)

include hx hn

/-- The ring-level data of the origin of the chart of `x_ρ` of the local blow-up: on the chart ring
`R[I/x_ρ] = chartRing x ρ` (`affineBlowUpAlgebra_span_eq_chartRing`), the origin
`𝔪' = chartOrigin x ρ` is a point of `Spec R[I/x_ρ]` lying over the closed point of `Spec R`
(`comap_chartOrigin`), and the localization of `R[I/x_ρ]` at it is `R'_{𝔪'}`, compatibly with the
maps from `R`. -/
theorem exists_point_chartOrigin {I : Ideal R} {r : ℕ} (hI : I = Ideal.span (x '' {i | i.val < r}))
    (ρ : Fin n) (hρ : ρ.val + 1 = r) (a : I) (ha : (a : R) = x ρ) [(chartOrigin x ρ).IsPrime] :
    ∃ p : Spec (CommRingCat.of (affineBlowUpAlgebra I a)),
      Spec.map (CommRingCat.ofHom (algebraMap R (affineBlowUpAlgebra I a))) p = closedPoint R ∧
      ∃ e : Localization.AtPrime (PrimeSpectrum.asIdeal p) (hp := PrimeSpectrum.isPrime p) ≃+*
          Localization.AtPrime (chartOrigin x ρ),
        ∀ c : R, e (algebraMap _ _ (algebraMap R (affineBlowUpAlgebra I a) c)) =
          algebraMap (chartRing x ρ) _ (algebraMap R (chartRing x ρ) c) := by
  classical
  obtain ⟨a, hmem⟩ := a
  dsimp only at ha ⊢
  subst ha
  have hset : {i : Fin n | i.val < r} = {i | i ≤ ρ} := by
    ext i
    change i.val < r ↔ i ≤ ρ
    rw [Fin.le_def, ← hρ]
    exact Nat.lt_succ_iff
  have hC : affineBlowUpAlgebra I (x ρ) = chartRing x ρ := by
    rw [hI, hset]
    exact affineBlowUpAlgebra_span_eq_chartRing x ρ
  generalize affineBlowUpAlgebra I (x ρ) = C at hC ⊢
  subst hC
  refine ⟨(⟨chartOrigin x ρ, inferInstance⟩ : PrimeSpectrum (chartRing x ρ)), ?_,
    RingEquiv.refl _, fun c => rfl⟩
  exact Spec_map_eq_closedPoint _ _ (comap_chartOrigin x ρ hx hn)

end Origin

section Bridge

open IsLocalRing

/-- Granted that the stalks of the local blow-up are those of `B_Z X` (the hypothesis `hiso`, proved
in `LocalBlowUpStalk.lean`): the origin of the chart of `y_ρ` of the local blow-up is a point `x'`
of `B_Z X` over `x` whose stalk is `Localization.AtPrime (chartOrigin y ρ)`, compatibly with `π^*`
on germs (Kollár's chart coordinates (60.2), [Kol07, Definition 60]; Hauser's local blow-up,
[Hau14, Definitions 4.15, 4.16]). -/
theorem exists_stalk_equiv_localization_chartOrigin_of_isIso (Z : X.IdealSheafData) {x : X}
    [IsRegularLocalRing (X.presheaf.stalk x)] {n r : ℕ} (y : Fin n → X.presheaf.stalk x)
    (hn : (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x))
    (hy : maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y))
    (hZ : Z.stalkIdeal x = Ideal.span (y '' {i | i.val < r})) (ρ : Fin n)
    (hρ : ρ.val + 1 = r) [(chartOrigin y ρ).IsPrime]
    (hiso : ∀ {Y B : Scheme.{u}} {φ : Y ⟶ B} {ψ : Y ⟶ Spec (X.presheaf.stalk x)} {π : B ⟶ X},
      IsPullback φ ψ π (X.fromSpecStalk x) → ∀ p : Y, IsIso (φ.stalkMap p)) :
    ∃ (x' : blowUp Z) (hx' : blowUpπ Z x' = x)
      (e : (blowUp Z).presheaf.stalk x' ≃+* Localization.AtPrime (chartOrigin y ρ)),
      ∀ (V : X.Opens) (hxV : x ∈ V) (s : Γ(X, V)),
        e ((blowUpπ Z).stalkMap x' (X.presheaf.germ V (blowUpπ Z x') (hx' ▸ hxV) s)) =
          algebraMap (chartRing y ρ) _ (algebraMap _ _ (X.presheaf.germ V x hxV s)) := by
  classical
  obtain ⟨φ, H⟩ := exists_isPullback_fromSpecStalk Z x
  have hmem : y ρ ∈ Z.stalkIdeal x :=
    hZ ▸ Ideal.subset_span ⟨ρ, show ρ.val < r by omega, rfl⟩
  obtain ⟨p, hp, e₂, he₂⟩ := exists_point_chartOrigin y hy hn hZ ρ hρ ⟨y ρ, hmem⟩ rfl
  let q := affineBlowUp.chart (Z.stalkIdeal x) ⟨y ρ, hmem⟩ p
  have hq_iso := hiso H q
  obtain ⟨e₁, he₁⟩ := exists_ringEquiv_stalk_chart (Z.stalkIdeal x) ⟨y ρ, hmem⟩ p
  let E : (blowUp Z).presheaf.stalk (φ q) ≃+* (affineBlowUp (Z.stalkIdeal x)).presheaf.stalk q :=
    RingEquiv.ofBijective (φ.stalkMap q).hom (ConcreteCategory.bijective_of_isIso _)
  have hw : ∀ t, blowUpπ Z (φ t) = X.fromSpecStalk x (affineBlowUp.π (Z.stalkIdeal x) t) := by
    intro t
    change (φ ≫ blowUpπ Z) t = (affineBlowUp.π (Z.stalkIdeal x) ≫ X.fromSpecStalk x) t
    rw [H.w]
  have hq : affineBlowUp.π (Z.stalkIdeal x) q = closedPoint (X.presheaf.stalk x) := by
    change (affineBlowUp.chart (Z.stalkIdeal x) ⟨y ρ, hmem⟩ ≫ affineBlowUp.π (Z.stalkIdeal x)) p =
      _
    rw [affineBlowUp.chart_π]
    exact hp
  have hx' : blowUpπ Z (φ q) = x := by rw [hw, hq, Scheme.fromSpecStalk_closedPoint]
  refine ⟨φ q, hx', (E.trans e₁).trans e₂, ?_⟩
  intro V hxV s
  have hV : blowUpπ Z (φ q) ∈ V := by
    rw [hx']
    exact hxV
  have hV' : (φ ≫ blowUpπ Z) q ∈ V := hV
  have hg := stalkMap_germ_eq_of_eq_comp_fromSpecStalk x (φ ≫ blowUpπ Z) H.w q V hxV hV' s
  have h1 : φ.stalkMap q ((blowUpπ Z).stalkMap (φ q)
        (X.presheaf.germ V (blowUpπ Z (φ q)) hV s)) =
      (φ ≫ blowUpπ Z).stalkMap q (X.presheaf.germ V ((φ ≫ blowUpπ Z) q) hV' s) := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have h2 := stalkMap_chart_stalkMap_π (Z.stalkIdeal x) ⟨y ρ, hmem⟩ p
    (X.presheaf.germ V x hxV s)
  have h3 := he₁ (algebraMap _ _ (X.presheaf.germ V x hxV s))
  have hinj := (ConcreteCategory.bijective_of_isIso
    ((affineBlowUp.chart (Z.stalkIdeal x) ⟨y ρ, hmem⟩).stalkMap p)).1
  have h4 : (affineBlowUp.π (Z.stalkIdeal x)).stalkMap q
        ((Spec (X.presheaf.stalk x)).presheaf.germ ⊤ (affineBlowUp.π (Z.stalkIdeal x) q) trivial
          ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (X.presheaf.germ V x hxV s))) =
      e₁.symm (algebraMap _ _ (algebraMap _ _ (X.presheaf.germ V x hxV s))) :=
    hinj (h2.trans h3.symm)
  have h5 : E ((blowUpπ Z).stalkMap (φ q) (X.presheaf.germ V (blowUpπ Z (φ q)) hV s)) =
      φ.stalkMap q ((blowUpπ Z).stalkMap (φ q)
        (X.presheaf.germ V (blowUpπ Z (φ q)) hV s)) := rfl
  -- `rw` along this chain times out (keyed matching against the stalk terms); compose the
  -- equalities explicitly instead.
  change ((E.trans e₁).trans e₂) ((blowUpπ Z).stalkMap (φ q)
      (X.presheaf.germ V (blowUpπ Z (φ q)) hV s)) =
    algebraMap (chartRing y ρ) _ (algebraMap _ _ (X.presheaf.germ V x hxV s))
  exact (RingEquiv.trans_apply _ _ _).trans ((congrArg e₂ (RingEquiv.trans_apply _ _ _)).trans
    ((congrArg (fun t => e₂ (e₁ t)) ((h5.trans h1).trans (hg.trans h4))).trans
      ((congrArg e₂ (e₁.apply_symm_apply _)).trans (he₂ _))))

end Bridge

end AlgebraicGeometry
