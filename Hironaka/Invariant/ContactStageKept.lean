import Hironaka.Resolution.HironakaG3UniverseHomCoeff
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Invariant.ContactRepresentative

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1b's restricted marked ideal with the divisor kept: transport, restriction, re-basing, representatives

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0113 / I-0977 C-0156, after the orchestrator's review of the Step 1
value function (3 October 2026, finding H1, accepted by TN-CLASSICAL on I-0981 C-0111): Step 1bb's lower marked ideal keeps
the divisor of `𝔍` (the original members are masked, not deleted), so the Step 1b inputs of properties (4'), (5), (6) and (7)
of `hir:centre-function` for the Step 1 value function (`hir:maximal-order-step`, `blueprint/src/hironaka.tex`) are needed
for that marked ideal.  Blueprint `mc:contact-stage-kept` (`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005
(arXiv `hiron.tex`), Step 1bb with `(E_p ∖ E)|_{V(u)_p}` read set-theoretically, and the lemma on the commutativity of the
resolution procedure in Step 1 with étale morphisms.

For `𝔍 = (X, N, E, 𝔞, d)`, `J̄ = 𝓒_N(𝓗_N(𝔍))` with the divisor `E`, a function `w`, a tower `T₀` and an open `W` of its last
stage, `contactMarkedKept 𝔍 w T₀ W = (𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(w))_{T₀}})|_W`, with the divisor of `J̄_{T₀}` (on Step 1bb's
masks the original members have empty traces).  Already available in this form: the domain
(`ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le`), the tails (`ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le`),
re-basing up to restricted equivalence (`ContactStageRebase.restrictEquiv_restrictedCoeffHomAlong_rebase`) and the change of
tangent direction (`StepOneTangentChange.inv_restrictedCoeffHom_eq_of_opens`).

## Main results

* `contactMarkedKept` (abbreviation);
* `barMarked_pullback`, `barMarked_pullback_val`: `J̄` commutes with biholomorphisms and with restriction to open sets;
* **`contactMarkedKept_isTowerIso`**, **`inv_contactMarkedKept_isTowerIso`** (property (6)): along an isomorphism of towers
  `T₀' ≅ T₀` over `Φ` (last-stage map `χ₀`), the marked ideal of `Φ^*𝔍` with `w ∘ Φ` on `W'` is the pullback of that of `𝔍` on
  `W = χ₀(W')`, and along an isomorphism of the tails `T₁' ≅ T₁` over `χ₀` the domain, canonical segments and values correspond
  (the tails restricted with `StepOneTangentChange.isTowerIso_restrictOpens`);
* **`contactMarkedKept_restrict`**, **`inv_contactMarkedKept_restrict`** (property (5)): for `U` open in the base and
  `W ⊆ T₀⁻¹U`, the marked ideal of `𝔍|_U` along `T₀|_U` on `W` (inside `T₀⁻¹U`), with domain, canonical segments, cosupports and
  values;
* **`contactMarkedKept_rebase`**, **`contactMarkedKept_rebase_nested`** (property (4') through re-basing): across steps empty over
  `W`, the marked ideal formed at the later stage lies in the domain with the same canonical segments and values, also on a later
  mask `W' ⊆ T⁻¹W` along the global tail (the first duplicates TN-CLASSICAL's `StepOneCompare.contactKept_rebase`, proved in
  parallel; see its docstring);
* **`restrictEquiv_contactMarkedKept`**, **`contactMarkedKept_representative`** (property (7)): for restricted-equivalent `𝔍 ≃ 𝔍'`
  and tangent directions equal on `N` over `W`, the two marked ideals are restricted-equivalent, with the same domain, canonical
  segments and values.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ContactStageKept

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  BlowupTowerIsomorphism ResolutionInvariantExt MaxLocusLocal RestrictEmptyTower StepOneTangentChange
  MarkedIdealOperationsAlong.MarkedIdeal
open HomogenizedGlueingTower (strictAlong)
open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The marked ideal -/

section Def

variable {X : CMfd.{u} n}

/-- **Step 1b's restricted marked ideal with the divisor kept**: for `J̄ = 𝓒_N(𝓗_N(𝔍))` (divisor `𝔍.E`), the coefficient ideal of
`J̄_{T₀}` along `N_{T₀}`, restricted to the strict transform of `N ∩ V(w)` and to the open `W` of the last stage of `T₀`. -/
abbrev contactMarkedKept (𝔍 : MarkedIdeal n X) (w : X → ℂ) {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (W : Opens Y) :
    MarkedIdeal n W :=
  MarkedIdeal.pullback (Subtype.val : W → Y)
    (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
      (strictAlong T₀ (𝔍.N ∩ {x | w x = 0})))

/-- The full-stage marked ideal behind `contactMarkedKept` has a coherent ideal along a multiple test blow-up of `J̄`. -/
theorem isCoherent_restrictedCoeff (𝔍 : MarkedIdeal n X) (h𝔞 : 𝔍.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔍.N)
    (w : X → ℂ) {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) :
    (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
      (strictAlong T₀ (𝔍.N ∩ {x | w x = 0}))).ideal.IsCoherent := by
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJN hJc T₀ hT₀
  exact isCoherent_coeffMarkedAlong hcT hNT

end Def

/-! ### Property (6): isomorphisms of towers -/

section Transport

variable {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {𝔍 : MarkedIdeal n X}

/-- **`J̄` commutes with biholomorphisms**: `𝓒(𝓗(Φ^*𝔍)) = Φ^*𝓒(𝓗(𝔍))` (coherent ideal, `N` a closed submanifold, `d ≥ 1`). -/
theorem barMarked_pullback (h𝔞 : 𝔍.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d) :
    coeffMarkedAlong (homMarkedAlong (MarkedIdeal.pullback Φ 𝔍)) =
      MarkedIdeal.pullback Φ (coeffMarkedAlong (homMarkedAlong 𝔍)) := by
  have _ := hd
  exact G3UniverseBarMarked.coeffHomMarked_pullback_diffeo Φ 𝔍 h𝔞 hN

variable {Y₀' Y₀ : CMfd.{u} n} {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
  {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀}

/-- **Step 1b's restricted marked ideal (divisor kept) along an isomorphism of towers** (property (6), marked ideals): for
`T₀' ≅ T₀` over `Φ : X' ≅ X` with last-stage map `χ₀`, `T₀` a multiple test blow-up of `J̄`, opens `W'`, `W` of the two last
stages and `ψ : W' ≅ W` agreeing with `χ₀`: `contactMarkedKept (Φ^*𝔍) (w ∘ Φ) T₀' W' = ψ^*(contactMarkedKept 𝔍 w T₀ W)`. -/
theorem contactMarkedKept_isTowerIso (h𝔞 : 𝔍.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d)
    (hiso : IsTowerIso Φ T₀' T₀ χ₀) (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) (w : X → ℂ)
    (W' : Opens Y₀') (W : Opens Y₀)
    (ψ : CMfd.of (n := n) W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) W)
    (hψ : ∀ q : W', ((ψ q : W) : Y₀) = χ₀ q) :
    contactMarkedKept (MarkedIdeal.pullback Φ 𝔍) (w ∘ Φ) T₀' W' =
      MarkedIdeal.pullback ψ (contactMarkedKept 𝔍 w T₀ W) := by
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hJd : 1 ≤ (coeffMarkedAlong (homMarkedAlong 𝔍)).d := one_le_coeffMarkedAlong_d _
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔞 hN w T₀ hT₀
  show MarkedIdeal.pullback (Subtype.val : W' → Y₀')
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong (MarkedIdeal.pullback Φ 𝔍))) T₀'))
        (strictAlong T₀' ((MarkedIdeal.pullback Φ 𝔍).N ∩ {x | (w ∘ Φ) x = 0}))) = _
  rw [barMarked_pullback Φ h𝔞 hN hd]
  have hA : (MarkedIdeal.pullback Φ 𝔍).N ∩ {x | (w ∘ Φ) x = 0} = Φ ⁻¹' (𝔍.N ∩ {x | w x = 0}) := rfl
  rw [hA, IsTowerIso.restrictedCoeff_eq Φ hJN hJc hJd hiso hT₀ (𝔍.N ∩ {x | w x = 0})]
  exact ContactMarkedCanonical.pullback_pullback_of_comp_eq hcoh χ₀.contMDiff contMDiff_subtype_val ψ.contMDiff
    contMDiff_subtype_val fun q => (hψ q).symm

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1b's values (divisor kept) along an isomorphism of towers** (property (6), values): let `T₀' ≅ T₀` over `Φ` with
last-stage map `χ₀` and `T₁' ≅ T₁` over `χ₀` (the split of an isomorphism `T₀'T₁' ≅ T₀T₁`), `T₀` a multiple test blow-up of
`J̄`, and `W'`, `W` opens of the stages with `q ∈ W' ↔ χ₀ q ∈ W`.  If `contactMarkedKept 𝔍 w T₀ W` lies in the domain of `R`
and `T₁|_W` is a canonical segment of it, then `contactMarkedKept (Φ^*𝔍) (w ∘ Φ) T₀' W'` lies in the domain, `T₁'|_{W'}` is a
canonical segment of it, and the values at corresponding points of the cosupports agree. -/
theorem inv_contactMarkedKept_isTowerIso (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d) (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) (w : X → ℂ) {W' : Opens Y₀'} {W : Opens Y₀}
    (hW : ∀ q, q ∈ W' ↔ χ₀ q ∈ W) {Z' Z : CMfd.{u} n} {T₁' : BlowupTower Y₀' Z'} {T₁ : BlowupTower Y₀ Z}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Z} (hχ : IsTowerIso χ₀ T₁' T₁ χ)
    (hdom : IsInvDomain k (contactMarkedKept 𝔍 w T₀ W))
    (hcan : IsCanonical (contactMarkedKept 𝔍 w T₀ W) (R.inv (contactMarkedKept 𝔍 w T₀ W)) (restrict W T₁)) :
    IsInvDomain k (contactMarkedKept (MarkedIdeal.pullback Φ 𝔍) (w ∘ Φ) T₀' W') ∧
      IsCanonical (contactMarkedKept (MarkedIdeal.pullback Φ 𝔍) (w ∘ Φ) T₀' W')
        (R.inv (contactMarkedKept (MarkedIdeal.pullback Φ 𝔍) (w ∘ Φ) T₀' W')) (restrict W' T₁') ∧
      ∀ (p : openPreimage T₁' W') (q : openPreimage T₁ W), (χ p : Z) = q →
        q ∈ (geoTransformAlong (contactMarkedKept 𝔍 w T₀ W) (restrict W T₁)).cosupp →
        R.inv (contactMarkedKept (MarkedIdeal.pullback Φ 𝔍) (w ∘ Φ) T₀' W') (restrict W' T₁') p =
          R.inv (contactMarkedKept 𝔍 w T₀ W) (restrict W T₁) q := by
  have hξ := isTowerIso_restrictOpens hW hχ (isTowerIso_mem_openPreimage_iff hχ hW)
  rw [contactMarkedKept_isTowerIso Φ h𝔞 hN hd hiso hT₀ w W' W (diffeoOpens χ₀ W' W hW) fun _ => rfl]
  refine ⟨InvDomainTowerAlong.isInvDomain_pullback _ hdom, isCanonical_of_isTowerIso R hdom _ hξ hcan,
    fun p q hpq hq => ?_⟩
  have hpq' : diffeoOpens χ (openPreimage T₁' W') (openPreimage T₁ W) (isTowerIso_mem_openPreimage_iff hχ hW) p = q :=
    Subtype.ext hpq
  have key := R.towerIso _ _ hdom _ _ _ hξ hcan p (by rw [hpq']; exact hq)
  rw [key, hpq']

end Transport

/-! ### Property (5): restriction to an open set of the base -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {𝔍 : MarkedIdeal n X}

/-- **`J̄` commutes with restriction to an open set**: `𝓒(𝓗(𝔍|_U)) = 𝓒(𝓗(𝔍))|_U`. -/
theorem barMarked_pullback_val (h𝔞 : 𝔍.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d) :
    coeffMarkedAlong (homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) =
      MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong (homMarkedAlong 𝔍)) := by
  rw [pullback_val_coeffMarkedAlong U (homMarkedAlong 𝔍) (isCoherent_homMarkedAlong h𝔞 hN) hN hd,
    pullback_val_homMarkedAlong U 𝔍 h𝔞 hN hd]

variable {Y₀ : CMfd.{u} n}

/-- **Step 1b's restricted marked ideal (divisor kept) on a restricted tower** (property (5), marked ideals): for `U` open in
the base, `T₀` a multiple test blow-up of `J̄` and `W ⊆ T₀⁻¹U` open, the marked ideal of `𝔍|_U` along `T₀|_U` with `w ∘ ι` on `W`
(seen inside `T₀⁻¹U`) is the transport along `nestedOpensDiffeo` of `contactMarkedKept 𝔍 w T₀ W`. -/
theorem contactMarkedKept_restrict (h𝔞 : 𝔍.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d)
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) (w : X → ℂ) {W : Opens Y₀}
    (hW : W ≤ openPreimage T₀ U) :
    contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) (restrict U T₀)
        (nestedOpens (openPreimage T₀ U) W) =
      MarkedIdeal.pullback (nestedOpensDiffeo (n := n) hW) (contactMarkedKept 𝔍 w T₀ W) := by
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hJd : 1 ≤ (coeffMarkedAlong (homMarkedAlong 𝔍)).d := one_le_coeffMarkedAlong_d _
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔞 hN w T₀ hT₀
  show MarkedIdeal.pullback (Subtype.val : nestedOpens (openPreimage T₀ U) W → openPreimage T₀ U)
      (withN (coeffMarkedAlong (geoTransformAlong
          (coeffMarkedAlong (homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))) (restrict U T₀)))
        (strictAlong (restrict U T₀)
          ((MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N ∩ {x | (w ∘ Subtype.val) x = 0}))) = _
  rw [barMarked_pullback_val U h𝔞 hN hd]
  have hA : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N ∩ {x | (w ∘ Subtype.val) x = 0} =
      (Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {x | w x = 0}) := rfl
  rw [hA, ContactCanonicalAlong.restrictedCoeff_geoTransformAlong_restrict U hJN hJc hJd T₀ hT₀ (𝔍.N ∩ {x | w x = 0})]
  exact pullback_val_pullback_val hcoh hW

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1b's values (divisor kept) on a restricted tower** (property (5), values): for `U` open in the base, a multiple test
blow-up `T₀` of `J̄`, `W ⊆ T₀⁻¹U` open and a tower `T₁` over the last stage of `T₀`: if `contactMarkedKept 𝔍 w T₀ W` lies in the
domain of `R` and `T₁|_W` is a canonical segment of it, then the marked ideal of `𝔍|_U` along `T₀|_U` with `w ∘ ι` on `W` lies
in the domain, the restriction to `W` of `T₁|_{T₀⁻¹U}` is a canonical segment of it, and at points with the same image the
cosupports correspond and the values agree. -/
theorem inv_contactMarkedKept_restrict (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d) (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) (w : X → ℂ) {W : Opens Y₀}
    (hW : W ≤ openPreimage T₀ U) (hdom : IsInvDomain k (contactMarkedKept 𝔍 w T₀ W)) {Z : CMfd.{u} n}
    (T₁ : BlowupTower Y₀ Z)
    (hcan : IsCanonical (contactMarkedKept 𝔍 w T₀ W) (R.inv (contactMarkedKept 𝔍 w T₀ W)) (restrict W T₁)) :
    IsInvDomain k (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) (restrict U T₀)
        (nestedOpens (openPreimage T₀ U) W)) ∧
      IsCanonical (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val)
          (restrict U T₀) (nestedOpens (openPreimage T₀ U) W))
        (R.inv (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val)
          (restrict U T₀) (nestedOpens (openPreimage T₀ U) W)))
        (restrict (nestedOpens (openPreimage T₀ U) W) (restrict (openPreimage T₀ U) T₁)) ∧
      ∀ (p : openPreimage (restrict (openPreimage T₀ U) T₁) (nestedOpens (openPreimage T₀ U) W))
        (q : openPreimage T₁ W), (((p : openPreimage T₁ (openPreimage T₀ U)) : Z)) = q →
        (p ∈ (geoTransformAlong (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val)
            (restrict U T₀) (nestedOpens (openPreimage T₀ U) W)) (restrict (nestedOpens (openPreimage T₀ U) W)
              (restrict (openPreimage T₀ U) T₁))).cosupp ↔
          q ∈ (geoTransformAlong (contactMarkedKept 𝔍 w T₀ W) (restrict W T₁)).cosupp) ∧
        (q ∈ (geoTransformAlong (contactMarkedKept 𝔍 w T₀ W) (restrict W T₁)).cosupp →
          R.inv (contactMarkedKept (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (w ∘ Subtype.val) (restrict U T₀)
              (nestedOpens (openPreimage T₀ U) W))
              (restrict (nestedOpens (openPreimage T₀ U) W) (restrict (openPreimage T₀ U) T₁)) p =
            R.inv (contactMarkedKept 𝔍 w T₀ W) (restrict W T₁) q) := by
  have hiso := isTowerIso_restrict_nestedOpens (X := Y₀) hW T₁
  have hTt := isGeoTestTower_of_isCanonical R hdom _ hcan
  have hcos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hW)
    hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent hiso hTt
  rw [contactMarkedKept_restrict U h𝔞 hN hd T₀ hT₀ w hW]
  refine ⟨InvDomainTowerAlong.isInvDomain_pullback _ hdom, isCanonical_of_isTowerIso R hdom _ hiso hcan,
    fun p q hpq => ?_⟩
  have hχ : nestedDiffeo (n := n) (openPreimage T₁ (openPreimage T₀ U))
      (openPreimage (restrict (openPreimage T₀ U) T₁) (nestedOpens (openPreimage T₀ U) W)) (openPreimage T₁ W)
      (mem_openPreimage_restrict_nestedOpens (openPreimage T₀ U) W T₁) (openPreimage_mono T₁ hW) p = q :=
    Subtype.ext hpq
  refine ⟨?_, fun hq => ?_⟩
  · rw [hcos, mem_preimage, hχ]
  · have key := R.towerIso (nestedOpensDiffeo (n := n) hW) _ hdom _ _ _ hiso hcan p (by rw [hχ]; exact hq)
    rw [key, hχ]

end Restrict

/-! ### Property (4'): re-basing across steps empty near the point -/

section Rebase

/-- **Cosupports on nested open sets**: for `V ⊆ A` open in `Y`, a marked ideal `𝔫` on `Y` with coherent ideal, and a tower `T₁`
over `Y` whose restrictions to `A` and to `V` are multiple test blow-ups of `𝔫|_A` and `𝔫|_V`, a point of the cosupport of
`𝔫|_V` along `T₁|_V` lies in the cosupport of `𝔫|_A` along `T₁|_A`. -/
theorem mem_cosupp_of_nested {Y Z : CMfd.{u} n} {𝔫 : MarkedIdeal n Y} (h𝔫 : 𝔫.ideal.IsCoherent) {A V : Opens Y}
    (hVA : V ≤ A) (T₁ : BlowupTower Y Z)
    (hNA : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : A → Y) 𝔫).N)
    (hcA : (MarkedIdeal.pullback (Subtype.val : A → Y) 𝔫).ideal.IsCoherent)
    (hNV : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).N)
    (hcV : (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫).ideal.IsCoherent)
    (hTA : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : A → Y) 𝔫) (restrict A T₁))
    (hTV : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫) (restrict V T₁)) (p : openPreimage T₁ V)
    (hp : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → Y) 𝔫) (restrict V T₁)).cosupp) :
    (⟨(p : Z), openPreimage_mono T₁ hVA p.2⟩ : openPreimage T₁ A) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : A → Y) 𝔫) (restrict A T₁)).cosupp := by
  have hiso := isTowerIso_restrict_nestedOpens (X := Y) hVA T₁
  have hc1 := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVA) hNV hcV hiso hTV
  rw [← pullback_val_pullback_val h𝔫 hVA] at hc1
  have hc2 := ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hNA hcA (nestedOpens A V) (restrict A T₁) hTA
  have hp' : (nestedDiffeo (n := n) (openPreimage T₁ A) (openPreimage (restrict A T₁) (nestedOpens A V))
      (openPreimage T₁ V) (mem_openPreimage_restrict_nestedOpens A V T₁) (openPreimage_mono T₁ hVA)).symm p ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : nestedOpens A V → A)
        (MarkedIdeal.pullback (Subtype.val : A → Y) 𝔫)) (restrict (nestedOpens A V) (restrict A T₁))).cosupp := by
    rw [hc1, mem_preimage, Diffeomorph.apply_symm_apply]
    exact hp
  rw [hc2] at hp'
  exact hp'

variable {X : CMfd.{u} n} {𝔍 : MarkedIdeal n X} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Step 1b's values (divisor kept) re-based across steps empty over `W`**: let `T₀ T` be a multiple test blow-up of `J̄`,
`u` a tangent direction of `(𝔍.ideal|_N, d)` on `U`, `W ⊆ T₀⁻¹U` open with the centres of `T` missing `W`.  If
`𝓢₀ = contactMarkedKept 𝔍 u T₀ W` lies in the domain of `R` and `T|_W T₁` is a canonical segment of it, then
`𝓢₁ = contactMarkedKept 𝔍 u (T₀ T) (T⁻¹W)` lies in the domain, `T₁` is a canonical segment of it, its transforms along `T₁` lie in
the domain, and the values of `𝓢₀` along `T|_W T₁` are those of `𝓢₁` along `T₁` on the cosupport.

Note: the same statement is TN-CLASSICAL's `StepOneCompare.contactKept_rebase` (154c4cbb), proved in parallel (its request to
drop this item, I-0981 C-0114, crossed with this module); kept under the standing rule that formalized content is not deleted.
Consumers may use either. -/
theorem contactMarkedKept_rebase (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T : BlowupTower Y₀ Y) (hT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T)) (W : Opens Y₀)
    (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U) (hW : CentresAvoid W T) (hdom : IsInvDomain k (contactMarkedKept 𝔍 u T₀ W))
    {Z : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) (openPreimage T W)) Z)
    (hcan : IsCanonical (contactMarkedKept 𝔍 u T₀ W) (R.inv (contactMarkedKept 𝔍 u T₀ W)) ((restrict W T).append T₁)) :
    IsInvDomain k (contactMarkedKept 𝔍 u (T₀.append T) (openPreimage T W)) ∧
      IsCanonical (contactMarkedKept 𝔍 u (T₀.append T) (openPreimage T W))
        (R.inv (contactMarkedKept 𝔍 u (T₀.append T) (openPreimage T W))) T₁ ∧
      IsInvDomain k (geoTransformAlong (contactMarkedKept 𝔍 u (T₀.append T) (openPreimage T W)) T₁) ∧
      ∀ z ∈ (geoTransformAlong (contactMarkedKept 𝔍 u T₀ W) ((restrict W T).append T₁)).cosupp,
        R.inv (contactMarkedKept 𝔍 u T₀ W) ((restrict W T).append T₁) z =
          R.inv (contactMarkedKept 𝔍 u (T₀.append T) (openPreimage T W)) T₁ z := by
  have he : IsEmptyTower (restrict W T) := (isEmptyTower_restrict_iff W T).mpr hW
  have hEq := ContactStageRebase.restrictEquiv_restrictedCoeffHomAlong_rebase 𝔍 hN h𝔞 hd U hu T₀ T hT W hWU hW
  have hcoh : (contactMarkedKept 𝔍 u (T₀.append T) (openPreimage T W)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff 𝔍 h𝔞 hN u (T₀.append T) hT)
  obtain ⟨h1, h2, h3⟩ := InvDomainRebase.inv_rebase (X := CMfd.of (n := n) W) R hdom (restrict W T) he hEq hcoh T₁ hcan
  exact ⟨h1, h2, isInvDomain_of_isCanonical R h1 T₁ h2, h3⟩

/-- **The re-based values on a later mask** (property (4') through re-basing, nested form): in the situation of
`contactMarkedKept_rebase`, with a global tail `T₁` over the last stage of `T₀ T` and `T|_W T₁|_W` (i.e. `(T T₁)|_W`) a canonical
segment of `𝓢₀ = contactMarkedKept 𝔍 u T₀ W`, for every open `W' ⊆ T⁻¹W` the marked ideal `contactMarkedKept 𝔍 u (T₀ T) W'` formed
at the later stage lies in the domain, `T₁|_{W'}` is a canonical segment of it, and at a point `p` of its cosupport its value is
that of `𝓢₀` along `(T T₁)|_W` at `p`. -/
theorem contactMarkedKept_rebase_nested (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔍.N) (hd : 1 ≤ 𝔍.d) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ Y Z : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T : BlowupTower Y₀ Y) (T₁ : BlowupTower Y Z)
    (hT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T)) (W : Opens Y₀)
    (hWU : (W : Set Y₀) ⊆ openPreimage T₀ U) (hW : CentresAvoid W T) (hdom : IsInvDomain k (contactMarkedKept 𝔍 u T₀ W))
    (hcan : IsCanonical (contactMarkedKept 𝔍 u T₀ W) (R.inv (contactMarkedKept 𝔍 u T₀ W)) (restrict W (T.append T₁)))
    {W' : Opens Y} (hW' : W' ≤ openPreimage T W) :
    IsInvDomain k (contactMarkedKept 𝔍 u (T₀.append T) W') ∧
      IsCanonical (contactMarkedKept 𝔍 u (T₀.append T) W') (R.inv (contactMarkedKept 𝔍 u (T₀.append T) W'))
        (restrict W' T₁) ∧
      ∀ (p : openPreimage T₁ W') (q : openPreimage (T.append T₁) W), (p : Z) = q →
        p ∈ (geoTransformAlong (contactMarkedKept 𝔍 u (T₀.append T) W') (restrict W' T₁)).cosupp →
        R.inv (contactMarkedKept 𝔍 u (T₀.append T) W') (restrict W' T₁) p =
          R.inv (contactMarkedKept 𝔍 u T₀ W) (restrict W (T.append T₁)) q := by
  -- `(T T₁)|_W ≅ T|_W · T₁|_{T⁻¹W}` over the identity
  have hiso := BlowupTowerIsoTail.isTowerIso_restrict_append W T T₁
  have hcoh₀ : (contactMarkedKept 𝔍 u T₀ W).ideal.IsCoherent := hdom.isWellFormed.isCoherent
  have hid : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞)
      (contactMarkedKept 𝔍 u T₀ W) = contactMarkedKept 𝔍 u T₀ W :=
    ContactCanonicalAlong.pullback_id _ hcoh₀
  have hcan' := isCanonical_of_isTowerIso R hdom _ hiso.symm hcan
  rw [show (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞).symm =
    Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞ from rfl, hid] at hcan'
  -- re-basing to the stage `T₀ T` on `T⁻¹W`
  obtain ⟨h1, h2, -, h4⟩ := contactMarkedKept_rebase R h𝔞 hN hd U hu T₀ T hT W hWU hW hdom _ hcan'
  -- shrinking to `W' ⊆ T⁻¹W`
  have hcoh₁ := isCoherent_restrictedCoeff 𝔍 h𝔞 hN u (T₀.append T) hT
  obtain ⟨h5, h6, h7⟩ := restrict_nestedOpens R hcoh₁ hW' h1 T₁ h2
  refine ⟨h5, h6, fun p q hpq hp => ?_⟩
  rw [h7 p hp]
  set r : openPreimage T₁ (openPreimage T W) := ⟨(p : Z), openPreimage_mono T₁ hW' p.2⟩ with hrdef
  -- `r` lies in the cosupport of `𝓢₁` along `T₁|_{T⁻¹W}`, hence in that of `𝓢₀` along `T|_W T₁|_{T⁻¹W}`
  have hr₁ : r ∈ (geoTransformAlong (contactMarkedKept 𝔍 u (T₀.append T) (openPreimage T W))
      (restrict (openPreimage T W) T₁)).cosupp :=
    mem_cosupp_of_nested hcoh₁ hW' T₁ h1.isWellFormed.isClosedSubmanifold_N h1.isWellFormed.isCoherent
      h5.isWellFormed.isClosedSubmanifold_N h5.isWellFormed.isCoherent (isGeoTestTower_of_isCanonical R h1 _ h2)
      (isGeoTestTower_of_isCanonical R h5 _ h6) p hp
  have hEq := ContactStageRebase.restrictEquiv_restrictedCoeffHomAlong_rebase 𝔍 hN h𝔞 hd U hu T₀ T hT W hWU hW
  have hTc := isGeoTestTower_of_isCanonical R hdom _ hcan'
  have hTW : IsGeoTestTower (contactMarkedKept 𝔍 u T₀ W) (restrict W T) :=
    ((isGeoTestTower_append_iff _ (restrict W T) (restrict (openPreimage T W) T₁)).mp hTc).1
  obtain ⟨hNT₀, hcT₀⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent (restrict W T) hTW
  have hWE := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hEq h1.isWellFormed.isClosedSubmanifold_N.1
    h1.isWellFormed.isCoherent hcT₀
  have hr₀ : r ∈ ((geoTransformAlong (contactMarkedKept 𝔍 u T₀ W)
      ((restrict W T).append (restrict (openPreimage T W) T₁))).cosupp : Set (openPreimage T₁ (openPreimage T W))) := by
    rw [geoTransformAlong_append, ← (hWE.2 _).2 (isGeoTestTower_of_isCanonical R h1 _ h2)]
    exact hr₁
  have key4 := h4 r hr₀
  -- `(T T₁)|_W ≅ T|_W · T₁|_{T⁻¹W}` carries `q` to `r`
  have hr : BlowupTowerIsoTail.opensCongr (n := n) (BlowupTowerIsoTail.openPreimage_append T T₁ W).symm q = r :=
    Subtype.ext hpq.symm
  have key6 := R.towerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) W) ∞) _ hdom _ _ _ hiso hcan'
    q (by rw [hr]; exact hr₀)
  rw [hid, hr] at key6
  rw [key6, key4]

end Rebase

/-! ### Property (7): representatives -/

section Representative

variable {X : CMfd.{u} n} {𝔍 𝔍' : MarkedIdeal n X}

/-- **Step 1b's restricted marked ideal (divisor kept) does not depend on the representative**: for restricted-equivalent
`𝔍 ≃ 𝔍'` (same `N`, `E`, `d`, and the same ideal on `N`) with coherent ideals, `u = w` on `N ∩ O` for an open `O`, a multiple
test blow-up `T₀` of `J̄ = 𝓒_N(𝓗_N(𝔍))` and `W ⊆ T₀⁻¹O` open: `contactMarkedKept 𝔍 u T₀ W ≃ contactMarkedKept 𝔍' w T₀ W`. -/
theorem restrictEquiv_contactMarkedKept (h𝔞 : 𝔍.ideal.IsCoherent) (h𝔞' : 𝔍'.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔍.N) (hEq : RestrictEquiv 𝔍 𝔍') {u w : X → ℂ} (O : Opens X)
    (huw : ∀ y ∈ O, y ∈ 𝔍.N → u y = w y) {Y : CMfd.{u} n} (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) (W : Opens Y)
    (hWO : (W : Set Y) ⊆ openPreimage T₀ O) :
    RestrictEquiv (contactMarkedKept 𝔍 u T₀ W) (contactMarkedKept 𝔍' w T₀ W) := by
  have hJ : RestrictEquiv (coeffMarkedAlong (homMarkedAlong 𝔍)) (coeffMarkedAlong (homMarkedAlong 𝔍')) :=
    ContactRepresentative.restrictEquiv_barMarked hEq hN h𝔞 h𝔞'
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hN' : IsClosedSubmanifold n 𝔍'.N := hEq.N_eq ▸ hN
  have hJc' : (coeffMarkedAlong (homMarkedAlong 𝔍')).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞' hN') hN'
  have hT₀' : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍')) T₀ :=
    ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJ hJN.1 hJc hJc').2 T₀).1.mp hT₀
  have hK := ContactCanonicalAlong.restrictEquiv_restrictedCoeff_geoTransformAlong hJ hJN.1 hJc hJc'
    (A := 𝔍.N ∩ {x | u x = 0}) (fun x hx => hx.1) T₀
  have hP := ContactRepresentative.restrictEquiv_pullback_val W hK (isCoherent_restrictedCoeff 𝔍 h𝔞 hN u T₀ hT₀)
    (by
      have h := isCoherent_restrictedCoeff 𝔍' h𝔞' hN' w T₀ hT₀'
      exact h)
  -- the hypersurfaces `N ∩ V(u)` and `N ∩ V(w)` have the same strict transform over `O`
  have hloc := ContactEquivalenceStage.strictAlong_inter_preimage_eq O.isOpen
    (A := 𝔍.N ∩ {x | u x = 0}) (B := 𝔍'.N ∩ {x | w x = 0}) (by
      rw [← hEq.N_eq]
      ext y
      show (y ∈ 𝔍.N ∧ u y = 0) ∧ y ∈ O ↔ (y ∈ 𝔍.N ∧ w y = 0) ∧ y ∈ O
      constructor
      · rintro ⟨⟨hyN, hy0⟩, hyO⟩
        exact ⟨⟨hyN, by rw [← huw y hyO hyN]; exact hy0⟩, hyO⟩
      · rintro ⟨⟨hyN, hy0⟩, hyO⟩
        exact ⟨⟨hyN, by rw [huw y hyO hyN]; exact hy0⟩, hyO⟩) T₀
  have hset : (Subtype.val : W → Y) ⁻¹' strictAlong T₀ (𝔍'.N ∩ {x | w x = 0}) =
      (Subtype.val : W → Y) ⁻¹' strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) := by
    ext p
    have hp : (p : Y) ∈ T₀.proj ⁻¹' (O : Set X) := hWO p.2
    constructor
    · intro h
      have h1 : (p : Y) ∈ strictAlong T₀ (𝔍'.N ∩ {x | w x = 0}) ∩ T₀.proj ⁻¹' (O : Set X) := ⟨h, hp⟩
      rw [← hloc] at h1
      exact h1.1
    · intro h
      have h1 : (p : Y) ∈ strictAlong T₀ (𝔍.N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' (O : Set X) := ⟨h, hp⟩
      rw [hloc] at h1
      exact h1.1
  show RestrictEquiv (MarkedIdeal.pullback (Subtype.val : W → Y)
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
        (strictAlong T₀ (𝔍.N ∩ {x | u x = 0}))))
    (MarkedIdeal.pullback (Subtype.val : W → Y)
      (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍')) T₀))
        (strictAlong T₀ (𝔍'.N ∩ {x | w x = 0}))))
  rw [ContactCanonicalAlong.pullback_withN, ContactCanonicalAlong.pullback_withN (Subtype.val : W → Y)
    (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍')) T₀)), hset,
    ← ContactCanonicalAlong.pullback_withN, ← ContactCanonicalAlong.pullback_withN]
  exact hP

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The values of Step 1b (divisor kept) do not depend on the representative**: in the situation of
`restrictEquiv_contactMarkedKept`, if `contactMarkedKept 𝔍 u T₀ W` lies in the domain of a resolution invariant `R`, so does
`contactMarkedKept 𝔍' w T₀ W`, the two have the same canonical segments, and along them `R` takes the same values on the
cosupport (property (7) of `R`). -/
theorem contactMarkedKept_representative (R : ResolutionInvariant.{u, v} n k Λ) (h𝔞 : 𝔍.ideal.IsCoherent)
    (h𝔞' : 𝔍'.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔍.N) (hEq : RestrictEquiv 𝔍 𝔍') {u w : X → ℂ}
    (O : Opens X) (huw : ∀ y ∈ O, y ∈ 𝔍.N → u y = w y) {Y : CMfd.{u} n} (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) (W : Opens Y)
    (hWO : (W : Set Y) ⊆ openPreimage T₀ O) (hdom : IsInvDomain k (contactMarkedKept 𝔍 u T₀ W)) :
    IsInvDomain k (contactMarkedKept 𝔍' w T₀ W) ∧
      ∀ {Z : CMfd.{u} n} (T₁ : BlowupTower (CMfd.of (n := n) W) Z),
        IsCanonical (contactMarkedKept 𝔍 u T₀ W) (R.inv (contactMarkedKept 𝔍 u T₀ W)) T₁ →
        IsCanonical (contactMarkedKept 𝔍' w T₀ W) (R.inv (contactMarkedKept 𝔍' w T₀ W)) T₁ ∧
        ∀ z ∈ (geoTransformAlong (contactMarkedKept 𝔍 u T₀ W) T₁).cosupp,
          R.inv (contactMarkedKept 𝔍 u T₀ W) T₁ z = R.inv (contactMarkedKept 𝔍' w T₀ W) T₁ z := by
  have hE := restrictEquiv_contactMarkedKept h𝔞 h𝔞' hN hEq O huw T₀ hT₀ W hWO
  have hc' : (contactMarkedKept 𝔍' w T₀ W).ideal.IsCoherent := by
    have hJ : RestrictEquiv (coeffMarkedAlong (homMarkedAlong 𝔍)) (coeffMarkedAlong (homMarkedAlong 𝔍')) :=
      ContactRepresentative.restrictEquiv_barMarked hEq hN h𝔞 h𝔞'
    have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
    have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
      isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
    have hN' : IsClosedSubmanifold n 𝔍'.N := hEq.N_eq ▸ hN
    have hJc' : (coeffMarkedAlong (homMarkedAlong 𝔍')).ideal.IsCoherent :=
      isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞' hN') hN'
    have hT₀' : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍')) T₀ :=
      ((MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJ hJN.1 hJc hJc').2 T₀).1.mp hT₀
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_restrictedCoeff 𝔍' h𝔞' hN' w T₀ hT₀')
  have hdom' := InvDomainRebase.isInvDomain_of_restrictEquiv hdom hE hc'
  refine ⟨hdom', fun T₁ hcan => ⟨InvDomainRebase.isCanonical_of_restrictEquiv R hdom hdom' hE T₁ hcan, fun z hz => ?_⟩⟩
  exact R.representative _ _ hdom hdom' hE T₁ hcan z hz

end Representative

end

end Hironaka.ContactStageKept
