import TranscendentalNakamaye.Pending.CoefficientIdeal
import TranscendentalNakamaye.Pending.MarkedIdealEquivalence
import TranscendentalNakamaye.Pending.HomogenizedGlueingTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restriction of a marked ideal and of the coefficient ideal to a submanifold

Hironaka phase H3 (TN23-ENVELOPES); blueprint `mc:restrict-marked`, `mc:restrict-order`, `mc:restrict-step`,
`mc:restrict-tower`, `mc:coefficient-wequiv`, `mc:coefficient-restriction-support`,
`mc:coefficient-restriction-tower` (`blueprint/src/maximal-contact.tex`).  Sources: Włodarczyk 2005, §2.11, Lemmas
`le:cf` and `le:S`; in the analytic paper (GGT 2008, `wlodarczyk09-analytic-resolution`) Lemma 5.6.2,
Lemma 5.6.3 and Proposition 5.6.4.

For a marked ideal `𝔟 = (M, M, E, 𝔞, d)` and a set `S ⊆ M`, `withN 𝔟 S = (M, S, E, 𝔞, d)` is the restriction
`(𝔞, d)|_S` of Włodarczyk (the ideal `𝔞|_S` of `𝒪_S`, represented by `𝔞`).

* `cosupp_inter_subset_cosupp_withN` (GGT Lemma 5.6.3, first half of `le:cf`): the order does not drop under
  restriction, `cosupp(𝔟) ∩ S ⊆ cosupp(𝔟|_S)`.
* `geoTransform_withN_restrictEquiv` (`le:cf`, one blowup): for a closed submanifold `S` and an admissible centre
  `C ⊆ S`, the transform of `𝔟|_S` is restricted-equivalent to the restriction of the transform of `𝔟` to the strict
  transform `S'` of `S`: `σ^c((𝔞, d)|_S) = (σ^c(𝔞, d))|_{S'}`.  Proof: along `S'` both are the quotient of
  `Res_{S'} σ^*𝔞` by the exceptional ideal `(σ^*𝓘_C)^d`, which is invertible along `S'` and can be cancelled
  (`restrictLe_of_restrictLe_mul_mul`); no coordinates are needed.
* `restrict_tower` (`le:cf` along towers): every multiple test blow-up of `𝔟` whose centres lie in the strict
  transforms `S_i` of `S` (`CentresIn S T`) is one of `𝔟|_S`, and along it `[𝔟|_S]_i ≃ (𝔟_i)|_{S_i}`
  (restricted equivalence).
* `coeff_wEquiv` (**`le:coeff` as an equivalence**, GGT Lemma 5.6.2): `𝓒(𝔪) ≃ 𝔪` in the sense of
  `MarkedIdealEquivalence.WEquiv`.
* `cosupp_coeff_withN` (**`le:S`, the support**, GGT Proposition 5.6.4, first statement):
  `supp(𝔪) ∩ S = supp(𝓒(𝔪)|_S)` for EVERY set `S`.  The inclusion `⊇` is not the Taylor-coefficient argument of the
  source: the summand `(𝓓^{μ-1}𝔞, 1)` of `𝓒(𝔪)` already forces `𝓓^{μ-1}𝔞` to vanish at the point, and
  `cosupp(𝔞, μ) = V(𝓓^{μ-1}𝔞)` (Giraud--Villamayor, `OrderTaylor`).
* `coeff_restrict_tower` (**`le:S` (1) and half of (2)**): for a multiple test blow-up `T` of `𝔪` with centres in the
  strict transforms of a closed submanifold `S`, `T` is a multiple test blow-up of `𝓒(𝔪)|_S`, along it
  `[𝓒(𝔪)|_S]_T ≃ 𝓒(𝔪)_T|_{S_T}`, and `supp(𝔪_T) ∩ S_T ⊆ supp[𝓒(𝔪)|_S]_T`.

NOT done here: the reverse inclusion `supp[𝓒(𝔪)|_S]_T ⊆ supp(𝔪_T)` for `T` nonempty (`le:S` (2) in full and (3)).
At `T = refl` it is `cosupp_coeff_withN`; along towers the source tracks the Taylor coefficients of the transforms
in the normal coordinates of `S_i` through the monomial charts, which is not formalized yet.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.CoefficientIdealRestriction

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences GermIdealOrder DerivativeIdeal
  IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal
  HomogenizedGlueing HomogenizedGlueingTower MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal RestrictedIdealWeight BlowupStrictSubmanifold

noncomputable section

/-! ### Restriction of a marked ideal to a set -/

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **The restriction `(𝔞, d)|_S`** of a marked ideal to a set `S`: the same `E`, ideal and mark, with `N = S`
(the ideal `𝔞|_S` of `𝒪_S` is represented by the ambient ideal). -/
def withN (𝔟 : MarkedIdeal n M) (S : Set M) : MarkedIdeal n M where
  N := S
  E := 𝔟.E
  ideal := 𝔟.ideal
  d := 𝔟.d

@[simp] theorem withN_N (𝔟 : MarkedIdeal n M) (S : Set M) : (withN 𝔟 S).N = S := rfl
@[simp] theorem withN_E (𝔟 : MarkedIdeal n M) (S : Set M) : (withN 𝔟 S).E = 𝔟.E := rfl
@[simp] theorem withN_ideal (𝔟 : MarkedIdeal n M) (S : Set M) : (withN 𝔟 S).ideal = 𝔟.ideal := rfl
@[simp] theorem withN_d (𝔟 : MarkedIdeal n M) (S : Set M) : (withN 𝔟 S).d = 𝔟.d := rfl

theorem cosupp_withN (𝔟 : MarkedIdeal n M) (S : Set M) :
    (withN 𝔟 S).cosupp = cosupport n S 𝔟.ideal 𝔟.d := rfl

/-- **The order does not drop under restriction** (GGT Lemma 5.6.3): `cosupp(𝔞, d) ∩ S ⊆ cosupp(𝔞|_S, d)`. -/
theorem cosupport_univ_inter_subset (𝔞 : GermIdeal n M) (d : ℕ) (S : Set M) :
    cosupport n univ 𝔞 d ∩ S ⊆ cosupport n S 𝔞 d :=
  fun _ hx => ⟨hx.2, fun g hg => (hx.1.2 g hg).mono_set (subset_univ S)⟩

/-- **`supp(𝔟) ∩ S ⊆ supp(𝔟|_S)`** for `N = M` (GGT Lemma 5.6.3; Włodarczyk 2005 `le:cf`, first statement). -/
theorem cosupp_inter_subset_cosupp_withN {𝔟 : MarkedIdeal n M} (hN : 𝔟.N = univ) (S : Set M) :
    𝔟.cosupp ∩ S ⊆ (withN 𝔟 S).cosupp := by
  rw [cosupp_withN, MarkedIdeal.cosupp, hN]
  exact cosupport_univ_inter_subset _ _ S

variable [IsComplexManifold n M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M']

/-- **Włodarczyk `le:cf`, one blowup** (GGT Lemma 5.6.3 and the first display of the proof of Proposition 5.6.4):
for `𝔟 = (M, M, E, 𝔞, d)` with `𝔞` coherent, a closed submanifold `S`, and a centre `C` admissible for `𝔟` and for
`𝔟|_S` (so `C ⊆ S`), the transform of `𝔟|_S` is restricted-equivalent to the restriction of the transform of `𝔟`
to the strict transform `S'` of `S`: `σ^c((𝔞, d)|_S) = (σ^c(𝔞, d))|_{S'}`. -/
theorem geoTransform_withN_restrictEquiv {𝔟 : MarkedIdeal n M} (hN : 𝔟.N = univ) (h𝔟 : 𝔟.ideal.IsCoherent)
    {S : Set M} (hS : IsClosedSubmanifold n S) {C : Set M} {π : M' → M} (hπ : IsBlowupAlong n C π)
    (hC : 𝔟.IsAdmissibleCentre C) (hCS : (withN 𝔟 S).IsAdmissibleCentre C) :
    RestrictEquiv ((withN 𝔟 S).geoTransform C π)
      (withN (𝔟.geoTransform C π) (geoStrictTransform π C S)) := by
  have hNuniv : IsClosedSubmanifold n 𝔟.N := hN ▸ isClosedSubmanifold_univ
  have hs' : ((withN 𝔟 S).geoTransform C π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (𝔪 := withN 𝔟 S) hS h𝔟 hCS hπ
  have hc' : (𝔟.geoTransform C π).ideal.IsCoherent :=
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNuniv h𝔟 hC hπ
  obtain ⟨s1, s2⟩ := restrictLe_pullback_geoTransform (𝔪 := withN 𝔟 S) hS h𝔟 hCS hπ
  obtain ⟨c1, c2⟩ := restrictLe_pullback_geoTransform hNuniv h𝔟 hC hπ
  have hsub : geoStrictTransform π C S ⊆ (𝔟.geoTransform C π).N := by
    rw [geoTransform_N, hN, geoStrictTransform_univ hπ]
    exact subset_univ _
  have c1' := restrictLe_mono hsub c1
  have c2' := restrictLe_mono hsub c2
  have hinv := isInvertibleAlong_geoStrictTransform hπ S 𝔟.d
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · refine RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul hs' hc' hinv ?_
    rw [RestrictLeCalculus.mul_comm' ((withN 𝔟 S).geoTransform C π).ideal,
      RestrictLeCalculus.mul_comm' (withN (𝔟.geoTransform C π) (geoStrictTransform π C S)).ideal]
    exact RestrictLeCalculus.RestrictLe.trans s2 c1'
  · refine RestrictLeCalculus.restrictLe_of_restrictLe_mul_mul hc' hs' hinv ?_
    rw [RestrictLeCalculus.mul_comm' ((withN 𝔟 S).geoTransform C π).ideal,
      RestrictLeCalculus.mul_comm' (withN (𝔟.geoTransform C π) (geoStrictTransform π C S)).ideal]
    exact RestrictLeCalculus.RestrictLe.trans c2' s1

/-- **The support of the coefficient ideal restricted to any set lies in the support** (`N = M`, `𝔞` coherent,
`d ≥ 1`): `supp(𝓒(𝔪)|_A) ⊆ supp(𝔪)`.  Only the last summand `(𝓓^{d-1}𝔞, 1)` is used: on its support `𝓓^{d-1}𝔞`
vanishes at the point, and `supp(𝔞, d) = V(𝓓^{d-1}𝔞)` (Giraud--Villamayor). -/
theorem cosupport_coeff_subset {𝔪 : MarkedIdeal n M} (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) (A : Set M) :
    cosupport n A (coeffMarked 𝔪).ideal (coeffMarked 𝔪).d ⊆ 𝔪.cosupp := by
  have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x :=
    hol_of_isCoherent h𝔞
  set D : ℕ → ℕ := fun j => (derivMarked 𝔪 j).d with hD
  have hD1 : ∀ j < 𝔪.d, 1 ≤ D j := fun j hj => by simp only [hD, derivMarked_d]; omega
  set e := sumExp D 𝔪.d (𝔪.d - 1) with he
  have he1 : 1 ≤ e := one_le_sumExp hD1 _
  have hmark : (coeffMarked 𝔪).d = e := by
    have := mul_sumExp D (show 𝔪.d - 1 < 𝔪.d by omega)
    simp only [hD, derivMarked_d, show 𝔪.d - (𝔪.d - 1) = 1 by omega, one_mul] at this
    exact this.symm
  intro x hx
  have hJ : ∀ i < 𝔪.d, ∀ y g, (idealPow (derivMarked 𝔪 i).ideal (sumExp D 𝔪.d i)).mem y g →
      HolomorphicAt n g y := fun _ _ _ _ hg => holomorphicAt_of_mem_idealPow hg
  have hx' := (mem_cosupport_finSumIdeal hJ).mp hx
  have hlast := hx'.2 (𝔪.d - 1) (by omega)
  have hzero : x ∈ (iterDerivIdeal 𝔪.ideal (𝔪.d - 1)).zeroLocus := by
    intro g hg
    have hghol : HolomorphicAt n g x := holomorphicAt_of_mem_iterDerivIdeal hhol (𝔪.d - 1) x g hg
    have hpow : (idealPow (derivMarked 𝔪 (𝔪.d - 1)).ideal e).mem x (fun p => g p ^ e) :=
      OrderMultiplicativity.pow_mem_idealPow hg hghol e
    have hv := (hlast.2 _ hpow).mono (show 1 ≤ (coeffMarked 𝔪).d by rw [hmark]; exact he1)
    have h0 := (vanishesToOrderOn_one_iff hx'.1 (holomorphicAt_of_mem_idealPow hpow)).mp hv
    exact (pow_eq_zero_iff (by omega)).mp h0
  rw [← OrderTaylor.cosupport_succ_eq_zeroLocus_iterDerivIdeal hhol, Nat.sub_add_cancel hd] at hzero
  rw [MarkedIdeal.cosupp, hN]
  exact hzero

end OneSpace

/-! ### Along towers -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

/-- **The centres of `T` lie in the strict transforms of `A`.** -/
def CentresIn (A : Set X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => CentresIn A T ∧ C ⊆ strictAlong T A

@[simp] theorem centresIn_refl (A : Set X) : CentresIn A (BlowupTower.refl : BlowupTower X X) := trivial

theorem centresIn_step_iff (A : Set X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) : CentresIn A (.step T C π hπ) ↔ CentresIn A T ∧ C ⊆ strictAlong T A :=
  Iff.rfl

/-- The `N` of the transform of a restriction is the strict transform of the set. -/
theorem N_geoTransformAlong_withN (𝔟 : MarkedIdeal n X) (S : Set X) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (withN 𝔟 S) T).N = strictAlong T S :=
  N_geoTransformAlong (withN 𝔟 S) T

/-- **A multiple test blow-up of a restriction `𝔟|_S` has its centres in the strict transforms of `S`.** -/
theorem centresIn_of_isGeoTestTower_withN (𝔟 : MarkedIdeal n X) (S : Set X) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower (withN 𝔟 S) T → CentresIn S T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
      refine ⟨centresIn_of_isGeoTestTower_withN 𝔟 S T hT0, fun x hx => ?_⟩
      rw [← N_geoTransformAlong_withN 𝔟 S T]
      exact hC.subset_N hx

/-- **Włodarczyk `le:cf` along towers** (GGT Lemma 5.6.3 / Proposition 5.6.4 (1)): let `𝔟 = (X, X, E, 𝔞, d)` with
`𝔞` coherent and `S` a closed submanifold.  Every multiple test blow-up `T` of `𝔟` whose centres lie in the strict
transforms of `S` is a multiple test blow-up of `𝔟|_S`, and along it `[𝔟|_S]_T ≃ (𝔟_T)|_{S_T}` (restricted
equivalence); moreover `𝔟_T` keeps `N` the whole space, both transformed ideals stay coherent and `S_T` is a closed
submanifold. -/
theorem restrict_tower (𝔟 : MarkedIdeal n X) (hN : 𝔟.N = univ) (h𝔟 : 𝔟.ideal.IsCoherent) {S : Set X}
    (hS : IsClosedSubmanifold n S) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔟 T → CentresIn S T →
      IsGeoTestTower (withN 𝔟 S) T ∧ (geoTransformAlong 𝔟 T).N = univ ∧
      (geoTransformAlong 𝔟 T).ideal.IsCoherent ∧ IsClosedSubmanifold n (strictAlong T S) ∧
      (geoTransformAlong (withN 𝔟 S) T).ideal.IsCoherent ∧
      RestrictEquiv (geoTransformAlong (withN 𝔟 S) T) (withN (geoTransformAlong 𝔟 T) (strictAlong T S))
  | _, .refl => fun _ _ => ⟨trivial, hN, h𝔟, hS, h𝔟, RestrictEquiv.refl (𝔪 := withN 𝔟 S) h𝔟⟩
  | _, .step T C π hπ => fun hT hTS => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔟 T C π hπ).mp hT
      obtain ⟨hTS0, hCS⟩ := hTS
      obtain ⟨hsT, hNT, hcohT, hST, hcohs, hRE⟩ := restrict_tower 𝔟 hN h𝔟 hS T hT0 hTS0
      have hCw : (withN (geoTransformAlong 𝔟 T) (strictAlong T S)).IsAdmissibleCentre C :=
        ⟨hC.1, fun x hx => cosupp_inter_subset_cosupp_withN hNT _ ⟨hC.2.1 hx, hCS hx⟩, hC.2.2⟩
      have hCs : (geoTransformAlong (withN 𝔟 S) T).IsAdmissibleCentre C := hRE.isAdmissibleCentre_iff.mpr hCw
      have hNs : (geoTransformAlong (withN 𝔟 S) T).N = strictAlong T S := N_geoTransformAlong_withN 𝔟 S T
      have heq : (geoTransformAlong (withN 𝔟 S) T).geoTransform C π =
          (withN (geoTransformAlong 𝔟 T) (strictAlong T S)).geoTransform C π :=
        hRE.geoTransform_eq (hNs ▸ hST.1) hcohs hcohT hπ.contMDiff
      have hNuniv : IsClosedSubmanifold n (geoTransformAlong 𝔟 T).N := hNT ▸ isClosedSubmanifold_univ
      refine ⟨(isGeoTestTower_step_iff _ T C π hπ).mpr ⟨hsT, hCs⟩, geoTransform_N_eq_univ hNT hπ,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNuniv hcohT hC hπ,
        BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hST hCS,
        HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (hNs ▸ hST) hcohs hCs hπ, ?_⟩
      show RestrictEquiv ((geoTransformAlong (withN 𝔟 S) T).geoTransform C π)
        (withN ((geoTransformAlong 𝔟 T).geoTransform C π) (geoStrictTransform π C (strictAlong T S)))
      rw [heq]
      exact geoTransform_withN_restrictEquiv hNT hcohT hST hπ hC hCw

/-! ### The coefficient ideal restricted to a submanifold -/

/-- **Włodarczyk `le:coeff` as an equivalence** (GGT Lemma 5.6.2): `𝓒(𝔪) ≃ 𝔪` (`N = M`, `𝔞` coherent, `d ≥ 1`). -/
theorem coeff_wEquiv (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) :
    WEquiv (coeffMarked 𝔪) 𝔪 :=
  ⟨rfl, fun T => ⟨(coeff_tower 𝔪 hN h𝔞 hd T).1,
    fun hT => (coeff_tower 𝔪 hN h𝔞 hd T).2 ((coeff_tower 𝔪 hN h𝔞 hd T).1.mp hT)⟩⟩

theorem N_coeffMarked (𝔪 : MarkedIdeal n X) : (coeffMarked 𝔪).N = 𝔪.N := rfl

theorem isCoherent_coeffMarked {𝔪 : MarkedIdeal n X} (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) :
    (coeffMarked 𝔪).ideal.IsCoherent :=
  (isAmbientFamily_derivMarked hN h𝔞).isCoherent_msum

/-- **Włodarczyk `le:S`, the support** (GGT Proposition 5.6.4, first statement): for `𝔪 = (X, X, E, 𝔞, μ)` with
`𝔞` coherent and `μ ≥ 1`, and ANY set `S`, `supp(𝔪) ∩ S = supp(𝓒(𝔪)|_S)`. -/
theorem cosupp_coeff_withN (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (S : Set X) : (withN (coeffMarked 𝔪) S).cosupp = 𝔪.cosupp ∩ S := by
  refine Subset.antisymm (fun x hx => ⟨cosupport_coeff_subset hN h𝔞 hd S hx, hx.1⟩) ?_
  have h0 := (coeff_tower 𝔪 hN h𝔞 hd (BlowupTower.refl : BlowupTower X X)).2 trivial
  rw [geoTransformAlong_refl, geoTransformAlong_refl] at h0
  rw [← h0]
  exact cosupp_inter_subset_cosupp_withN (𝔟 := coeffMarked 𝔪) hN S

/-- **Włodarczyk `le:S` (1) and the inclusion `⊆` of (2)** (GGT Proposition 5.6.4 (1)--(2)): let
`𝔪 = (X, X, E, 𝔞, μ)` with `𝔞` coherent and `μ ≥ 1`, `S` a closed submanifold, and `T` a multiple test blow-up of
`𝔪` whose centres lie in the strict transforms of `S`.  Then `T` is a multiple test blow-up of `𝓒(𝔪)|_S`, along it
`[𝓒(𝔪)|_S]_T ≃ 𝓒(𝔪)_T|_{S_T}`, and `supp(𝔪_T) ∩ S_T ⊆ supp[𝓒(𝔪)|_S]_T`. -/
theorem coeff_restrict_tower (𝔪 : MarkedIdeal n X) (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    {S : Set X} (hS : IsClosedSubmanifold n S) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T)
    (hTS : CentresIn S T) :
    IsGeoTestTower (withN (coeffMarked 𝔪) S) T ∧
      RestrictEquiv (geoTransformAlong (withN (coeffMarked 𝔪) S) T)
        (withN (geoTransformAlong (coeffMarked 𝔪) T) (strictAlong T S)) ∧
      (geoTransformAlong 𝔪 T).cosupp ∩ strictAlong T S ⊆
        (geoTransformAlong (withN (coeffMarked 𝔪) S) T).cosupp := by
  obtain ⟨hiff, hcos⟩ := coeff_tower 𝔪 hN h𝔞 hd T
  have hTc : IsGeoTestTower (coeffMarked 𝔪) T := hiff.mpr hT
  obtain ⟨hsT, hNT, -, -, -, hRE⟩ :=
    restrict_tower (coeffMarked 𝔪) hN (isCoherent_coeffMarked hN h𝔞) hS T hTc hTS
  refine ⟨hsT, hRE, ?_⟩
  rw [hRE.cosupp_eq, ← hcos hT]
  exact cosupp_inter_subset_cosupp_withN hNT _

end Tower

end

end TranscendentalNakamaye.Pending.CoefficientIdealRestriction
