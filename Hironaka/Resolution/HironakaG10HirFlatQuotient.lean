import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Over

/-!
# Flatness of a ring map over a closed subscheme of the base (lane G10H, run 0080)

For a ring map `φ : A →+* B` and an ideal `J` of `A`, the *fibre map over `V(J)`* is the induced
map `A ⧸ J →+* B ⧸ J B` (`quotMap φ J`).  This module proves the two base-change facts used by the
germ form of Hironaka's flattener (Hironaka, *Flattening theorem in complex-analytic geometry*,
Amer. J. Math. 97 (1975), (1.14.2) p. 512, (2.4.2) p. 526):

* `flat_quotMap_of_le`: flatness over `V(J)` implies flatness over every smaller `V(K)`, `J ≤ K`
  (base change of a flat map along `A ⧸ J → A ⧸ K`; `B ⧸ K B ≅ (A ⧸ K) ⊗_{A ⧸ J} (B ⧸ J B)`);
* `flat_quotMap_bot_iff`: over the whole base (`J = ⊥`) it is flatness of `φ`;
* `flat_quotMap_of_isMaximal`: over a closed point (`J` maximal) it always holds.

Pure commutative algebra; no analytic input.
-/

set_option autoImplicit false

namespace Hironaka.HironakaG10HirFlatQuotient

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The fibre map `A ⧸ J →+* B ⧸ J B` of `φ` over `V(J)`. -/
abbrev quotMap (φ : A →+* B) (J : Ideal A) : A ⧸ J →+* B ⧸ J.map φ :=
  Ideal.quotientMap (J.map φ) φ Ideal.le_comap_map

/-- **Flatness over `V(J)` passes to `V(K)` for `J ≤ K`** (base change). -/
theorem flat_quotMap_of_le (φ : A →+* B) {J K : Ideal A} (hJK : J ≤ K)
    (h : (quotMap φ J).Flat) : (quotMap φ K).Flat := by
  let _ : Algebra (A ⧸ J) (B ⧸ J.map φ) := (quotMap φ J).toAlgebra
  have hfl : Module.Flat (A ⧸ J) (B ⧸ J.map φ) := h
  set I : Ideal (A ⧸ J) := K.map (Ideal.Quotient.mk J) with hI
  have h1 : Module.Flat ((A ⧸ J) ⧸ I)
      ((B ⧸ J.map φ) ⧸ I.map (algebraMap (A ⧸ J) (B ⧸ J.map φ))) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (B ⧸ J.map φ) I).toLinearEquiv
  have h2 : (algebraMap ((A ⧸ J) ⧸ I)
      ((B ⧸ J.map φ) ⧸ I.map (algebraMap (A ⧸ J) (B ⧸ J.map φ)))).Flat :=
    RingHom.flat_algebraMap_iff.2 h1
  have hcomp : (algebraMap (A ⧸ J) (B ⧸ J.map φ)).comp (Ideal.Quotient.mk J) =
      (Ideal.Quotient.mk (J.map φ)).comp φ := by
    ext a
    rfl
  have hIK : I.map (algebraMap (A ⧸ J) (B ⧸ J.map φ)) =
      (K.map φ).map (Ideal.Quotient.mk (J.map φ)) := by
    rw [hI, Ideal.map_map, Ideal.map_map, hcomp]
  let e₁ := DoubleQuot.quotQuotEquivQuotOfLE hJK
  let e₂ := (Ideal.quotEquivOfEq hIK).trans
    (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono (f := φ) hJK))
  have hsq : (quotMap φ K).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap _ _) := by
    refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext ?_)
    ext a
    rfl
  rw [← RingHom.Flat.comp_iff_of_bijective_right (g := e₁.toRingHom) e₁.bijective, hsq]
  exact RingHom.Flat.comp h2 (RingHom.Flat.of_bijective (f := e₂.toRingHom) e₂.bijective)

/-- The quotient map by the zero ideal is bijective. -/
theorem bijective_mk_of_eq_bot {I : Ideal A} (h : I = ⊥) :
    Function.Bijective (Ideal.Quotient.mk I) :=
  ⟨(RingHom.injective_iff_ker_eq_bot _).2 (by rw [Ideal.mk_ker, h]), Ideal.Quotient.mk_surjective⟩

/-- **Over the whole base the fibre map is `φ`.** -/
theorem flat_quotMap_bot_iff (φ : A →+* B) : (quotMap φ ⊥).Flat ↔ φ.Flat := by
  have hsq : (quotMap φ ⊥).comp (Ideal.Quotient.mk ⊥) = (Ideal.Quotient.mk _).comp φ := by
    ext a
    rfl
  rw [← RingHom.Flat.comp_iff_of_bijective_right (bijective_mk_of_eq_bot rfl), hsq,
    RingHom.Flat.comp_iff_of_bijective_left (bijective_mk_of_eq_bot Ideal.map_bot)]

/-- **Over a closed point every fibre map is flat** (a module over a field is free). -/
theorem flat_quotMap_of_isMaximal (φ : A →+* B) (J : Ideal A) [J.IsMaximal] :
    (quotMap φ J).Flat :=
  RingHom.Flat.of_isField (Ideal.Quotient.field J).toIsField _

/-- The fibre map of `(mk K) ∘ φ` over `V(J)` is the fibre map `A ⧸ J → B ⧸ (K + J B)`. -/
theorem flat_quotMap_mk_comp_iff (φ : A →+* B) (K : Ideal B) (J : Ideal A) :
    (quotMap ((Ideal.Quotient.mk K).comp φ) J).Flat ↔
      (Ideal.quotientMap (K ⊔ J.map φ) φ
        (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_right))).Flat := by
  have hJ : J.map ((Ideal.Quotient.mk K).comp φ) = (J.map φ).map (Ideal.Quotient.mk K) := by
    rw [Ideal.map_map]
  let e := (Ideal.quotEquivOfEq hJ).trans (DoubleQuot.quotQuotEquivQuotSup K (J.map φ))
  have hsq : e.toRingHom.comp (quotMap ((Ideal.Quotient.mk K).comp φ) J) =
      Ideal.quotientMap (K ⊔ J.map φ) φ
        (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_right)) := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    rfl
  rw [← hsq, RingHom.Flat.comp_iff_of_bijective_left (g := e.toRingHom) e.bijective]

/-! ### The flattener ideal of a ring map -/

/-- `I` is **the flattener ideal of `φ`**: `φ` is flat over the closed subscheme `V(J)` of the base
exactly when `I ≤ J`.  This is Hironaka's universal property (1.14.2) (p. 512) tested on the
closed-subspace germs of the base. -/
def IsFlattenerIdeal (φ : A →+* B) (I : Ideal A) : Prop :=
  ∀ J : Ideal A, (quotMap φ J).Flat ↔ I ≤ J

variable {φ : A →+* B} {I I' : Ideal A}

/-- The flattener ideal is unique. -/
theorem IsFlattenerIdeal.unique (h : IsFlattenerIdeal φ I) (h' : IsFlattenerIdeal φ I') :
    I = I' :=
  le_antisymm ((h I').1 ((h' I').2 le_rfl)) ((h' I).1 ((h I).2 le_rfl))

/-- `φ` is flat over its flattener. -/
theorem IsFlattenerIdeal.flat (h : IsFlattenerIdeal φ I) : (quotMap φ I).Flat :=
  (h I).2 le_rfl

/-- The flattener is the least ideal over which `φ` is flat. -/
theorem isFlattenerIdeal_iff_isLeast :
    IsFlattenerIdeal φ I ↔ IsLeast {J : Ideal A | (quotMap φ J).Flat} I :=
  ⟨fun h => ⟨h.flat, fun J hJ => (h J).1 hJ⟩,
    fun h _ => ⟨fun hJ => h.2 hJ, fun hIJ => flat_quotMap_of_le φ hIJ h.1⟩⟩

/-- The flattener lies in every maximal ideal (over a closed point everything is flat). -/
theorem IsFlattenerIdeal.le_of_isMaximal (h : IsFlattenerIdeal φ I) (J : Ideal A) [hJ : J.IsMaximal] :
    I ≤ J :=
  (h J).1 (flat_quotMap_of_isMaximal φ J)

/-- The flattener is `⊥` exactly when `φ` is flat. -/
theorem isFlattenerIdeal_bot_iff : IsFlattenerIdeal φ ⊥ ↔ φ.Flat := by
  rw [isFlattenerIdeal_iff_isLeast, ← flat_quotMap_bot_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => bot_le⟩⟩

/-- **Several maps out of the same base** (the points of a fibre): simultaneous flatness over
`V(J)` is containment of the SUM of the flatteners (Hironaka p. 527, `∏ E^x/J^x`). -/
theorem forall_flat_iff_iSup_le {ι : Type*} {B' : ι → Type*} [∀ i, CommRing (B' i)]
    (ψ : ∀ i, A →+* B' i) (P : ι → Ideal A) (hP : ∀ i, IsFlattenerIdeal (ψ i) (P i))
    (J : Ideal A) : (∀ i, (quotMap (ψ i) J).Flat) ↔ (⨆ i, P i) ≤ J := by
  rw [iSup_le_iff]
  exact forall_congr' fun i => hP i J

/-- Transport along an isomorphism of the target. -/
theorem IsFlattenerIdeal.ringEquiv_comp {B' : Type*} [CommRing B'] (h : IsFlattenerIdeal φ I)
    (e : B ≃+* B') : IsFlattenerIdeal (e.toRingHom.comp φ) I := by
  intro J
  have hJ : J.map (e.toRingHom.comp φ) = (J.map φ).map e.toRingHom := by
    rw [Ideal.map_map]
  let e' := Ideal.quotientEquiv (J.map φ) (J.map (e.toRingHom.comp φ)) e hJ
  have hsq : e'.toRingHom.comp (quotMap φ J) = quotMap (e.toRingHom.comp φ) J := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    rfl
  rw [← hsq, RingHom.Flat.comp_iff_of_bijective_left (g := e'.toRingHom) e'.bijective]
  exact h J

/-- Transport along an isomorphism of the base. -/
theorem IsFlattenerIdeal.comp_ringEquiv {A' : Type*} [CommRing A'] (h : IsFlattenerIdeal φ I)
    (e : A' ≃+* A) : IsFlattenerIdeal (φ.comp e.toRingHom) (I.comap e.toRingHom) := by
  intro J
  have hJ : J.map (φ.comp e.toRingHom) = (J.map e.toRingHom).map φ := by
    rw [Ideal.map_map]
  let e₁ := Ideal.quotientEquiv J (J.map e.toRingHom) e rfl
  let e₂ := Ideal.quotEquivOfEq hJ
  have hsq : e₂.symm.toRingHom.comp ((quotMap φ (J.map e.toRingHom)).comp e₁.toRingHom) =
      quotMap (φ.comp e.toRingHom) J := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    rfl
  rw [← hsq, RingHom.Flat.comp_iff_of_bijective_left (g := e₂.symm.toRingHom) e₂.symm.bijective,
    RingHom.Flat.comp_iff_of_bijective_right (g := e₁.toRingHom) e₁.bijective, h]
  exact (Ideal.comap_le_iff_le_map e.toRingHom e.bijective).symm

/-- Passing to a quotient `A ⧸ q` of the base through which `φ` factors (e.g. from the ambient
germ ring of a chart to the stalk of a closed subspace): the flattener is the image. -/
theorem IsFlattenerIdeal.quotient_base (h : IsFlattenerIdeal φ I) (q : Ideal A)
    (hq : ∀ a ∈ q, φ a = 0) :
    IsFlattenerIdeal (Ideal.Quotient.lift q φ hq) (I.map (Ideal.Quotient.mk q)) := by
  intro J'
  let J : Ideal A := J'.comap (Ideal.Quotient.mk q)
  have hqJ : q ≤ J := fun a ha => by
    show Ideal.Quotient.mk q a ∈ J'
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact J'.zero_mem
  have hJ' : J.map (Ideal.Quotient.mk q) = J' :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J'
  have hmap : J'.map (Ideal.Quotient.lift q φ hq) = J.map φ := by
    rw [← hJ', Ideal.map_map]
    rfl
  let e₁ := (Ideal.quotEquivOfEq hJ'.symm).trans (DoubleQuot.quotQuotEquivQuotOfLE hqJ)
  let e₂ := Ideal.quotEquivOfEq hmap
  have hsq : e₂.toRingHom.comp (quotMap (Ideal.Quotient.lift q φ hq) J') =
      (quotMap φ J).comp e₁.toRingHom := by
    refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext ?_)
    ext a
    rfl
  rw [← RingHom.Flat.comp_iff_of_bijective_left (g := e₂.toRingHom) e₂.bijective, hsq,
    RingHom.Flat.comp_iff_of_bijective_right (g := e₁.toRingHom) e₁.bijective, h,
    Ideal.map_le_iff_le_comap]

end Hironaka.HironakaG10HirFlatQuotient
