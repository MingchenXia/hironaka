import Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
import Hironaka.Resolution.HironakaG10HirFlatQuotient

/-!
# H3.4 (generic algebra): transporting fibre flatness along ring isomorphisms and point equalities

Lane G10H3, run 0081.  Generic lemmas used to read the canonical chart data of `fibreModel_of_canonical` in the native
stage setting (the native blowup is only isomorphic to the geometric one, `HironakaG10SbBlowupComparison.blowupIso`,
and the chart points equal the stage points only propositionally):

* `flat_quotMap_comp_equiv` — flatness of `quotMap φ (J e)` gives flatness of `quotMap (φ ∘ e) J` (`e` a ring iso
  of the source);
* `flat_quotMap_of_comp_equiv` — the converse transport;
* `flat_quotMap_of_equiv_comp` — flatness of `quotMap (e ∘ φ) J` gives flatness of `quotMap φ J` (`e` a ring iso of
  the target);
* `map_mk_maximalIdeal_le_jacobson` — in a quotient of a local ring the image of the maximal ideal lies in the Jacobson
  radical;
* stalk transports along point equalities (`eqToHom`), `fibreStalkMap` along an equality of source points.

No named input.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport

open Hironaka HironakaG10HirFlatQuotient Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease

section Algebra

variable {A A' R R' : Type*} [CommRing A] [CommRing A'] [CommRing R] [CommRing R']

/-- Flatness of the fibre map over `V(J e)` along `φ` gives flatness over `V(J)` along `φ ∘ e`. -/
theorem flat_quotMap_comp_equiv (e : A ≃+* A') (φ : A' →+* R) (J : Ideal A)
    (h : (quotMap φ (J.map e.toRingHom)).Flat) : (quotMap (φ.comp e.toRingHom) J).Flat := by
  have hmm : (J.map e.toRingHom).map φ = J.map (φ.comp e.toRingHom) := Ideal.map_map _ _
  let ε : A ⧸ J ≃+* A' ⧸ J.map e.toRingHom := Ideal.quotientEquiv J (J.map e.toRingHom) e rfl
  let ι : R ⧸ (J.map e.toRingHom).map φ ≃+* R ⧸ J.map (φ.comp e.toRingHom) := Ideal.quotEquivOfEq hmm
  have hfac : quotMap (φ.comp e.toRingHom) J =
      ι.toRingHom.comp ((quotMap φ (J.map e.toRingHom)).comp ε.toRingHom) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl
  rw [hfac]
  exact RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective ε.bijective) h)
    (RingHom.Flat.of_bijective ι.bijective)

/-- Conversely, flatness over `V(J)` along `φ ∘ e` gives flatness over `V(J e)` along `φ`. -/
theorem flat_quotMap_of_comp_equiv (e : A ≃+* A') (φ : A' →+* R) (J : Ideal A)
    (h : (quotMap (φ.comp e.toRingHom) J).Flat) : (quotMap φ (J.map e.toRingHom)).Flat := by
  have h1 : (J.map e.toRingHom).map e.symm.toRingHom = J := by
    rw [Ideal.map_map]
    have : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := RingHom.ext fun a => e.symm_apply_apply a
    rw [this, Ideal.map_id]
  have h2 : (φ.comp e.toRingHom).comp e.symm.toRingHom = φ :=
    RingHom.ext fun a => congrArg φ (e.apply_symm_apply a)
  rw [← h1] at h
  have h3 := flat_quotMap_comp_equiv e.symm (φ.comp e.toRingHom) (J.map e.toRingHom) h
  rwa [h2] at h3

/-- Flatness of the fibre map along `e ∘ φ` (`e` a ring iso of the target) gives flatness along `φ`. -/
theorem flat_quotMap_of_equiv_comp (e : R ≃+* R') (φ : A →+* R) (J : Ideal A)
    (h : (quotMap (e.toRingHom.comp φ) J).Flat) : (quotMap φ J).Flat := by
  have hJ : J.map (e.toRingHom.comp φ) = (J.map φ).map e.toRingHom := (Ideal.map_map _ _).symm
  let ε : R ⧸ J.map φ ≃+* R' ⧸ J.map (e.toRingHom.comp φ) :=
    Ideal.quotientEquiv (J.map φ) (J.map (e.toRingHom.comp φ)) e hJ
  have hfac : quotMap φ J = ε.symm.toRingHom.comp (quotMap (e.toRingHom.comp φ) J) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    exact (ε.symm_apply_apply (Ideal.Quotient.mk (J.map φ) (φ a))).symm
  rw [hfac]
  exact RingHom.Flat.comp h (RingHom.Flat.of_bijective ε.symm.bijective)

/-- In a quotient of a local ring the image of the maximal ideal lies in the Jacobson radical. -/
theorem map_mk_maximalIdeal_le_jacobson [IsLocalRing A] (I : Ideal A) :
    Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal A) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hu : IsUnit (a * b + 1) := by
    by_contra hn
    have h1 : a * b + 1 ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have h2 : a * b ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_right _ _ ha
    have h3 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      simpa using Ideal.sub_mem _ h1 h2
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  have := hu.map (Ideal.Quotient.mk I)
  simpa [map_add, map_mul, map_one] using this

/-- A ring map from a local ring through a local homomorphism into a quotient of a local ring sends the maximal
ideal into the Jacobson radical. -/
theorem map_maximalIdeal_le_jacobson [IsLocalRing A] [IsLocalRing A'] (φ : A →+* A') [IsLocalHom φ]
    (I : Ideal A') :
    Ideal.map ((Ideal.Quotient.mk I).comp φ) (IsLocalRing.maximalIdeal A) ≤ Ideal.jacobson ⊥ := by
  rw [← Ideal.map_map]
  refine le_trans (Ideal.map_mono ?_) (map_mk_maximalIdeal_le_jacobson I)
  rw [Ideal.map_le_iff_le_comap]
  exact fun a ha => map_nonunit φ a ha

end Algebra

section Stalks

variable {X : LocallyRingedSpace.{0}}

/-- Two stalk transports compose. -/
theorem eqToHom_eqToHom_apply {P₁ P₂ P₃ : X} (h₁ : P₁ = P₂) (h₂ : P₂ = P₃) (r : X.presheaf.stalk P₁) :
    (eqToHom (congrArg X.presheaf.stalk h₂)).hom ((eqToHom (congrArg X.presheaf.stalk h₁)).hom r) =
      (eqToHom (congrArg X.presheaf.stalk (h₁.trans h₂))).hom r := by
  subst h₁ h₂
  rfl

/-- A stalk transport is a ring isomorphism. -/
noncomputable def stalkEquivOfEq {P₁ P₂ : X} (h : P₁ = P₂) : X.presheaf.stalk P₂ ≃+* X.presheaf.stalk P₁ :=
  (eqToIso (congrArg X.presheaf.stalk h.symm)).commRingCatIsoToRingEquiv

theorem stalkEquivOfEq_apply {P₁ P₂ : X} (h : P₁ = P₂) (r : X.presheaf.stalk P₂) :
    stalkEquivOfEq h r = (eqToHom (congrArg X.presheaf.stalk h.symm)).hom r :=
  rfl

end Stalks

section Fibre

variable {X Y : SourceReducedComplexSpace}

/-- The fibre stalk map does not depend on the proof of the point equation. -/
theorem fibreStalkMap_congr (f : Y ⟶ X) {x : X.obj.left} {y y' : Y.obj.left} (hy : y = y')
    (h : f.hom.left.base y = x) (h' : f.hom.left.base y' = x) (J : Ideal (X.obj.left.presheaf.stalk x)) :
    (quotMap (fibreStalkMap f x y h) J).Flat ↔ (quotMap (fibreStalkMap f x y' h') J).Flat := by
  subst hy
  rfl

end Fibre

end Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport
