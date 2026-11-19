import Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation
import Hironaka.Resolution.HironakaG10HirFlatQuotient
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Nakayama

/-!
# The algebraic core of Hironaka's Lemma 4.4.5 (i): flatness passes from the total to the strict transform

Lane G10SB, run 0081, plan item G10-03-09.c (algebraic part; route `G10SB/G10-02-10a-pulled-family-route.md`).
Hironaka 1975, proof of Lemma 4.4.5, printed p. 537: "(F, f)/Z_p is flat … hence (F', f₁)/Z_p^* is also flat because
a base change preserves flatness. From these facts it follows that τ induces an isomorphism F'|Z_p^* ≅ F₁|Z_p^*."

Algebra: `φ : A →+* Q` (the total transform over the new base), `G ∈ A` (the exceptional generator) and an ideal `I`
of `A` (the strict transform `Z^*`) with `G` regular modulo `I`.  If `Q` is flat over `V(I)`, then

* `powerSat_bot_le_map` — the whole `G`-power torsion of `Q` lies in `I Q`;
* `quotMap_strict_flat_of_total` — the STRICT transform `Q ⧸ (G-torsion)` is flat over `V(I)`, and its fibre
  ring over `V(I)` is the total one (`strictFibreEquiv`).

Uses `Module.Flat.isSMulRegular_of_isRegular` (Mathlib).  No analytic input, no named input.
-/

set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10SbStrictFlatAlgebra

open Hironaka.HironakaG10HirFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation

noncomputable section

variable {A Q : Type*} [CommRing A] [CommRing Q]

/-- The `G`-power torsion of `Q` lies in `I Q` when `Q` is flat over `V(I)` and `G` is regular modulo `I`. -/
theorem powerSat_bot_le_map (φ : A →+* Q) (I : Ideal A) (G : A)
    (hG : IsRegular (Ideal.Quotient.mk I G)) (hflat : (quotMap φ I).Flat) :
    powerSat (⊥ : Ideal Q) (φ G) ≤ I.map φ := by
  intro q hq
  obtain ⟨m, hm⟩ := hq
  let _ : Algebra (A ⧸ I) (Q ⧸ I.map φ) := (quotMap φ I).toAlgebra
  have : Module.Flat (A ⧸ I) (Q ⧸ I.map φ) := hflat
  have hreg : IsSMulRegular (Q ⧸ I.map φ) ((Ideal.Quotient.mk I G) ^ m) :=
    Module.Flat.isSMulRegular_of_isRegular (hG.pow m)
  have h0 : (φ G) ^ m * q = 0 := (Submodule.mem_bot _).mp hm
  have h1 : Ideal.Quotient.mk (I.map φ) (φ G) ^ m * Ideal.Quotient.mk (I.map φ) q = 0 := by
    rw [← map_pow, ← map_mul, h0, map_zero]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hreg
  show (Ideal.Quotient.mk I G) ^ m • Ideal.Quotient.mk (I.map φ) q = (Ideal.Quotient.mk I G) ^ m • 0
  rw [smul_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow, Ideal.quotientMap_mk]
  exact h1

/-- Killing an ideal `K ≤ J Q` of the total ring does not change the fibre over `V(J)`: flatness over `V(J)` of
`Q ⧸ K` and of `Q` agree. -/
theorem quotMap_mk_comp_flat_iff_of_le (φ : A →+* Q) (K : Ideal Q) (J : Ideal A) (hKJ : K ≤ J.map φ) :
    (quotMap ((Ideal.Quotient.mk K).comp φ) J).Flat ↔ (quotMap φ J).Flat := by
  rw [flat_quotMap_mk_comp_iff]
  have heq : K ⊔ J.map φ = J.map φ := sup_eq_right.mpr hKJ
  let e := Ideal.quotEquivOfEq heq
  have hcomp : e.toRingHom.comp (Ideal.quotientMap (K ⊔ J.map φ) φ
      (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_right))) = quotMap φ J := by
    refine Ideal.Quotient.ringHom_ext ?_
    ext a
    rfl
  rw [← RingHom.Flat.comp_iff_of_bijective_left (g := e.toRingHom) e.bijective, hcomp]

/-- **Hironaka's Lemma 4.4.5 (i), algebraic core.**  If the total transform is flat over `V(I)` and the exceptional
generator is regular modulo `I`, the strict transform (total modulo `G`-power torsion) is flat over `V(I)`. -/
theorem quotMap_strict_flat_of_total (φ : A →+* Q) (I : Ideal A) (G : A)
    (hG : IsRegular (Ideal.Quotient.mk I G)) (hflat : (quotMap φ I).Flat) :
    (quotMap ((Ideal.Quotient.mk (powerSat (⊥ : Ideal Q) (φ G))).comp φ) I).Flat :=
  (quotMap_mk_comp_flat_iff_of_le φ _ I (powerSat_bot_le_map φ I G hG hflat)).mpr hflat

/-- Over `V(I)` the strict and the total transform have the same fibre ring. -/
def strictFibreEquiv (φ : A →+* Q) (I : Ideal A) (G : A)
    (hG : IsRegular (Ideal.Quotient.mk I G)) (hflat : (quotMap φ I).Flat) :
    (Q ⧸ (powerSat (⊥ : Ideal Q) (φ G) ⊔ I.map φ)) ≃+* Q ⧸ I.map φ :=
  Ideal.quotEquivOfEq (sup_eq_right.mpr (powerSat_bot_le_map φ I G hG hflat))

/-- **The kernel of a flat quotient dies modulo the base (Nakayama).**  Let `K` be an ideal of the total ring `Q`
lying in `𝔞 Q` with `𝔞 Q` in the Jacobson radical of `Q` (e.g. `𝔞` the maximal ideal of a local base, `φ` local:
the total and the reduced family have the same closed fibre).  If `Q ⧸ K` is flat over `V(J)`, then `K ≤ J Q`.
(Equational criterion: `K ≤ J Q + 𝔞 (K + J Q)`; then Nakayama.) -/
theorem le_map_of_flat_of_le [IsNoetherianRing Q] (φ : A →+* Q) (K : Ideal Q) (J 𝔞 : Ideal A)
    (hK : K ≤ 𝔞.map φ) (h𝔞 : 𝔞.map φ ≤ Ideal.jacobson ⊥)
    (hflat : (quotMap ((Ideal.Quotient.mk K).comp φ) J).Flat) : K ≤ J.map φ := by
  rw [flat_quotMap_mk_comp_iff] at hflat
  let _ : Algebra (A ⧸ J) (Q ⧸ (K ⊔ J.map φ)) := (Ideal.quotientMap (K ⊔ J.map φ) φ
    (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_right))).toAlgebra
  have : Module.Flat (A ⧸ J) (Q ⧸ (K ⊔ J.map φ)) := hflat
  have hsmul : ∀ (a : A) (q : Q), Ideal.Quotient.mk J a • Ideal.Quotient.mk (K ⊔ J.map φ) q =
      Ideal.Quotient.mk (K ⊔ J.map φ) (φ a * q) := by
    intro a q
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk, map_mul]
  have key : K ≤ J.map φ ⊔ (𝔞.map φ) • (K ⊔ J.map φ) := by
    intro k hk
    have hk' := hK hk
    rw [Ideal.map, Submodule.mem_span_set'] at hk'
    obtain ⟨n, f, g, hfg⟩ := hk'
    choose a ha hga using fun i => (g i).2
    have hrel : ∑ i, Ideal.Quotient.mk J (a i) • Ideal.Quotient.mk (K ⊔ J.map φ) (f i) = 0 := by
      have e : ∀ i, Ideal.Quotient.mk J (a i) • Ideal.Quotient.mk (K ⊔ J.map φ) (f i) =
          Ideal.Quotient.mk (K ⊔ J.map φ) (f i • (g i : Q)) := by
        intro i
        rw [hsmul, smul_eq_mul, hga i, mul_comm]
      rw [Finset.sum_congr rfl fun i _ => e i, ← map_sum, hfg, Ideal.Quotient.eq_zero_iff_mem]
      exact le_sup_left (a := K) hk
    obtain ⟨n', b, y, hy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
    beta_reduce at hy hb
    choose bt hbt using fun i j => Ideal.Quotient.mk_surjective (b i j)
    choose yt hyt using fun j => Ideal.Quotient.mk_surjective (y j)
    have hκ : ∀ i, f i - ∑ j, φ (bt i j) * yt j ∈ K ⊔ J.map φ := by
      intro i
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, hy i, sub_eq_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hbt i j, ← hyt j, hsmul]
    have hc : ∀ j, ∑ i, a i * bt i j ∈ J := by
      intro j
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_mul, hbt] using hb j
    have hswap : ∑ j, ∑ i, φ (a i) * φ (bt i j) * yt j = ∑ i, ∑ j, φ (bt i j) * yt j * φ (a i) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hdecomp : k = ∑ i, (f i - ∑ j, φ (bt i j) * yt j) * φ (a i) +
        ∑ j, φ (∑ i, a i * bt i j) * yt j := by
      rw [← hfg]
      have e1 : ∀ i, f i • (g i : Q) = f i * φ (a i) := fun i => by rw [smul_eq_mul, hga i]
      simp only [e1, sub_mul, Finset.sum_sub_distrib, map_sum, map_mul, Finset.sum_mul]
      rw [hswap]
      abel
    rw [hdecomp]
    refine Submodule.add_mem _ (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left ?_)
    · refine Submodule.sum_mem _ fun i _ => ?_
      rw [mul_comm, ← smul_eq_mul]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem φ (ha i)) (hκ i)
    · exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ (hc j))
  have hle : K ⊔ J.map φ ≤ J.map φ ⊔ (𝔞.map φ) • (K ⊔ J.map φ) := sup_le key le_sup_left
  exact le_sup_left.trans
    (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) h𝔞 hle)

/-- Local form of `le_map_of_flat_of_le`: over a local base with a local map to a noetherian local total ring, an
ideal `K ≤ 𝔪_A Q` with `Q ⧸ K` flat over `V(J)` lies in `J Q`. -/
theorem le_map_of_flat_local [IsLocalRing A] [IsLocalRing Q] [IsNoetherianRing Q] (φ : A →+* Q)
    [IsLocalHom φ] (K : Ideal Q) (J : Ideal A) (hK : K ≤ (IsLocalRing.maximalIdeal A).map φ)
    (hflat : (quotMap ((Ideal.Quotient.mk K).comp φ) J).Flat) : K ≤ J.map φ :=
  le_map_of_flat_of_le φ K J _ hK
    ((Ideal.map_le_iff_le_comap.mpr (show IsLocalRing.maximalIdeal A ≤ (IsLocalRing.maximalIdeal Q).comap φ
      from fun a ha => map_nonunit φ a ha)).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)) hflat

/-- **Hironaka's Lemma 4.4.5, the (G2) algebraic core.**  Under the hypotheses of `le_map_of_flat_of_le`
flatness of the reduced family `Q ⧸ K` over `V(J)` implies flatness of the total family `Q` over `V(J)`. -/
theorem quotMap_total_flat_of_strict [IsNoetherianRing Q] (φ : A →+* Q) (K : Ideal Q) (J 𝔞 : Ideal A)
    (hK : K ≤ 𝔞.map φ) (h𝔞 : 𝔞.map φ ≤ Ideal.jacobson ⊥)
    (hflat : (quotMap ((Ideal.Quotient.mk K).comp φ) J).Flat) : (quotMap φ J).Flat :=
  (quotMap_mk_comp_flat_iff_of_le φ K J (le_map_of_flat_of_le φ K J 𝔞 hK h𝔞 hflat)).mp hflat

end

end Hironaka.Analytic.Unibranch.HironakaG10SbStrictFlatAlgebra
