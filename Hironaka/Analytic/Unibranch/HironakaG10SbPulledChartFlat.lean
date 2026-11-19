import Hironaka.Analytic.Unibranch.HironakaG10SbStrictFlatAlgebra
import Hironaka.Analytic.Unibranch.HironakaG10SbQuotientFlat
import Hironaka.Analytic.Unibranch.HironakaG10SingularNativeChartFlattener
import Hironaka.Analytic.HolomorphicGermNoetherian

/-!
# Bridge BC1 at chart level: the pulled family over a singular new base, and (i), (G2) on charts

Lane G10SB, run 0081, bridge BC1 of `G10SB/G10-02-10a-pulled-family-route.md` (towards Hironaka's Lemma 4.4.5 (i) and
(G2), printed p. 537).  A relative chart `𝒪_{ℂ^d} → 𝒪_{ℂ^{d+t}} ⧸ K` of the old family, an analytic germ
`φ : (ℂ^e,0) → (ℂ^d,0)` (an ambient representative of the base change `σ`) and the ideal `I'` of the new base `X'`
in `ℂ^e` give the PULLED chart family `𝒪_{ℂ^e} ⧸ I' → 𝒪_{ℂ^{e+t}} ⧸ (K ∘ (φ × id) + I')` (the analytic fibre product
`Y ×_X X'`).

* `isFlattenerIdeal_quotientMap_base` — the flattener of the base change of a ring map to a quotient `A ⧸ q` of its
  base is the image of the flattener (algebra; generalizes TN's `IsFlattenerIdeal.quotient_base`);
* `isFlattenerIdeal_pulledChart` — **Hironaka Th. 2.5 at one point over a singular new base**: the flattener of the
  pulled chart family is the pulled canonical flattener of `K` (TN `isFlattenerIdeal_chartMap_baseChange`);
* `pulledChart_flat_of_le` — base change of flatness: if the old chart family is flat over `V(Ĩ)`, the pulled family
  is flat over every `V(J')` above the pulled `Ĩ`;
* `pulledChart_strict_flat` — **(i) on charts**: then the pulled family modulo the `G`-power torsion (the strict
  transform) is flat over `V(J')` when `G` is regular modulo `J'`;
* `pulledFlattener_le_of_strict_flat` — **(G2) core on charts**: if a quotient of the pulled family by an ideal inside
  `𝔞 ·` with `𝔞 ·` in the radical (same closed fibre) is flat over `V(J₁)`, the pulled flattener lies in `J₁`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Hironaka Hironaka
  HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaChowPresentationIndependentFlattener HironakaG10HirFlatQuotient HironakaG10HirChartFlattener
  HironakaActualAnalyticBaseChangeCoefficients
open Hironaka.Analytic.Unibranch.HironakaG10SingularNativeChartFlattener Hironaka.Analytic.Unibranch.HironakaG10SbQuotientFlat
  Hironaka.Analytic.Unibranch.HironakaG10SbStrictFlatAlgebra Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation

namespace Hironaka.Analytic.Unibranch.HironakaG10SbPulledChartFlat

noncomputable section

section Algebra

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **Base change to a quotient of the base.**  The flattener of `A ⧸ q → B ⧸ q B` is the image of the flattener
of `A → B`. -/
theorem isFlattenerIdeal_quotientMap_base {φ : A →+* B} {I : Ideal A} (h : IsFlattenerIdeal φ I)
    (q : Ideal A) :
    IsFlattenerIdeal (Ideal.quotientMap (q.map φ) φ Ideal.le_comap_map) (I.map (Ideal.Quotient.mk q)) := by
  intro J'
  have hsq : (Ideal.quotientMap (q.map φ) φ Ideal.le_comap_map).comp (Ideal.Quotient.mk q) =
      (RingEquiv.refl (B ⧸ q.map φ)).toRingHom.comp ((Ideal.Quotient.mk (q.map φ)).comp φ) :=
    RingHom.ext fun _ => rfl
  rw [quotMap_flat_iff_of_square _ (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective _
    (RingEquiv.refl _) hsq]
  have hq : q ≤ J'.comap (Ideal.Quotient.mk q) := fun a ha => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact J'.zero_mem
  rw [quotMap_mk_comp_flat_iff_of_le φ _ _ (Ideal.map_mono hq), h, Ideal.map_le_iff_le_comap]

/-- Flatness of `φ` over `V(J)` (the fibre map `A ⧸ J → B ⧸ J B` is flat), as a generic predicate. -/
abbrev FlatOver (φ : A →+* B) (J : Ideal A) : Prop := (quotMap φ J).Flat

end Algebra

variable (d t e : ℕ) (K : Ideal (HolGerm (ComplexModel (d+t))))
  (φ : ComplexModel e → ComplexModel d)
  (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
  (I' : Ideal (HolGerm (ComplexModel e)))

/-- The chart ideal of the pulled family `Y ×_X X'`: the relative chart ideal pulled along `φ × id`, plus the ideal
of the new base. -/
def pulledIdeal : Ideal (HolGerm (ComplexModel (e+t))) :=
  K.map (jointBasePullback d e t φ hφ hφ0).toRingHom ⊔ I'.map (tangentPullback e t).toRingHom

/-- The pulled chart family over the singular new base. -/
def pulledChartMap :
    HolGerm (ComplexModel e) ⧸ I' →+* HolGerm (ComplexModel (e+t)) ⧸ pulledIdeal d t e K φ hφ hφ0 I' :=
  singularChartMap e t I' (pulledIdeal d t e K φ hφ hφ0 I') le_sup_right

theorem pulledChartMap_mk (a : HolGerm (ComplexModel e)) :
    pulledChartMap d t e K φ hφ hφ0 I' (Ideal.Quotient.mk I' a) =
      Ideal.Quotient.mk (pulledIdeal d t e K φ hφ hφ0 I') (tangentPullback e t a) :=
  rfl

/-- The pulled canonical flattener over the new base. -/
def pulledFlattener : Ideal (HolGerm (ComplexModel e) ⧸ I') :=
  ((canonicalFlattenerIdeal d t K).map (compAlgHom φ hφ hφ0).toRingHom).map (Ideal.Quotient.mk I')

/-- **Hironaka Th. 2.5 at one point, over a singular new base.**  The flattener of the pulled chart family is the
pulled canonical flattener of the old chart. -/
theorem isFlattenerIdeal_pulledChart :
    IsFlattenerIdeal (pulledChartMap d t e K φ hφ hφ0 I') (pulledFlattener d t e K φ hφ hφ0 I') := by
  have h := isFlattenerIdeal_quotientMap_base (isFlattenerIdeal_chartMap_baseChange d t K e φ hφ hφ0) I'
  set Kφ := K.map (jointBasePullback d e t φ hφ hφ0).toRingHom with hKφ
  have hI : I'.map (chartMap e t Kφ) = (I'.map (tangentPullback e t).toRingHom).map (Ideal.Quotient.mk Kφ) := by
    rw [chartMap, ← Ideal.map_map]
  let ε := (Ideal.quotEquivOfEq hI).trans (DoubleQuot.quotQuotEquivQuotSup Kφ
    (I'.map (tangentPullback e t).toRingHom))
  have hcomp : ε.toRingHom.comp (Ideal.quotientMap (I'.map (chartMap e t Kφ)) (chartMap e t Kφ)
      Ideal.le_comap_map) = pulledChartMap d t e K φ hφ hφ0 I' := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    rfl
  rw [← hcomp]
  exact h.ringEquiv_comp ε

/-- **Base change of flatness** on charts: flatness of the old chart family over `V(Ĩ)` gives flatness of the pulled
family over every `V(J')` containing the pulled `Ĩ`. -/
theorem pulledChart_flat_of_le (Ĩ : Ideal (HolGerm (ComplexModel d)))
    (hĨ : canonicalFlattenerIdeal d t K ≤ Ĩ) (J' : Ideal (HolGerm (ComplexModel e) ⧸ I'))
    (hJ' : (Ĩ.map (compAlgHom φ hφ hφ0).toRingHom).map (Ideal.Quotient.mk I') ≤ J') :
    FlatOver (pulledChartMap d t e K φ hφ hφ0 I') J' :=
  (isFlattenerIdeal_pulledChart d t e K φ hφ hφ0 I' J').mpr
    ((Ideal.map_mono (Ideal.map_mono hĨ)).trans hJ')

/-- **Hironaka's (i) on charts.**  Under the hypotheses of `pulledChart_flat_of_le`, if `G` is regular modulo `J'`
then the strict transform (pulled family modulo its `G`-power torsion) is flat over `V(J')`. -/
theorem pulledChart_strict_flat (Ĩ : Ideal (HolGerm (ComplexModel d)))
    (hĨ : canonicalFlattenerIdeal d t K ≤ Ĩ) (J' : Ideal (HolGerm (ComplexModel e) ⧸ I'))
    (hJ' : (Ĩ.map (compAlgHom φ hφ hφ0).toRingHom).map (Ideal.Quotient.mk I') ≤ J')
    (G : HolGerm (ComplexModel e) ⧸ I') (hG : IsRegular (Ideal.Quotient.mk J' G)) :
    FlatOver ((Ideal.Quotient.mk (powerSat (⊥ : Ideal _)
      (pulledChartMap d t e K φ hφ hφ0 I' G))).comp (pulledChartMap d t e K φ hφ hφ0 I')) J' :=
  quotMap_strict_flat_of_total _ J' G hG (pulledChart_flat_of_le d t e K φ hφ hφ0 I' Ĩ hĨ J' hJ')

/-- **(G2) core on charts.**  If a quotient of the pulled family by an ideal `K'` with the same closed fibre
(`K' ≤ 𝔞 ·`, `𝔞 ·` in the Jacobson radical) is flat over `V(J₁)`, then the pulled flattener lies in `J₁`. -/
theorem pulledFlattener_le_of_strict_flat (K' : Ideal (HolGerm (ComplexModel (e+t)) ⧸ pulledIdeal d t e K φ hφ hφ0 I'))
    (𝔞 J₁ : Ideal (HolGerm (ComplexModel e) ⧸ I'))
    (hK' : K' ≤ 𝔞.map (pulledChartMap d t e K φ hφ hφ0 I'))
    (h𝔞 : 𝔞.map (pulledChartMap d t e K φ hφ hφ0 I') ≤ Ideal.jacobson ⊥)
    (hflat : FlatOver (B := (HolGerm (ComplexModel (e+t)) ⧸ pulledIdeal d t e K φ hφ hφ0 I') ⧸ K')
      ((Ideal.Quotient.mk K').comp (pulledChartMap d t e K φ hφ hφ0 I')) J₁) :
    pulledFlattener d t e K φ hφ hφ0 I' ≤ J₁ := by
  have : IsNoetherianRing (HolGerm (ComplexModel (e+t))) := isNoetherianRing_holGerm_euclidean (e+t)
  exact (isFlattenerIdeal_pulledChart d t e K φ hφ hφ0 I' J₁).mp
    (quotMap_total_flat_of_strict _ K' J₁ 𝔞 hK' h𝔞 hflat)

end

end Hironaka.Analytic.Unibranch.HironakaG10SbPulledChartFlat
