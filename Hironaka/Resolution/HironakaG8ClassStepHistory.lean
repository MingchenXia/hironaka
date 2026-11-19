import Hironaka.Resolution.HironakaG8ClassStepBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Born exponents of the lower ideals are history-determined below the mark (G8C lane, run 0080, round 4; (B') plan module 10)

Blueprint: `hironaka-g8-class-step-history.tex`.  Notes: this lane's `RESIDUAL-COUNTEREXAMPLE.md` (§§1, 4) and `REPORT-r4.md`;
lane G11B's `FALLBACK-DECISION-ANALYSIS.md` (decision on I-1397: keep design D1, prove the residual by route R1).

For class-equivalent `A ≈ B`, the coefficient ideals on maximal contact `𝒞_W(A_∅)`, `𝒞_W(B_∅)` (lane G11B's `contactCoeffBM`, before
the transforms) are NOT equivalent near the original members, but they are once the original members are added to their boundary
(BM08 Cor 4.2 and `HironakaG8ClassStepCut.locEquiv_addE`: `𝒞_W(A_∅) + E ≈ A|_W ≈ B|_W ≈ 𝒞_W(B_∅) + E`).  The tests of the pair
are those of the version WITH the original members; the exponents are those of the version WITHOUT them (the lower divisor is the
born part).  Lane G8's P6 (`HironakaG8BornExponents`, `HironakaG8DomainExponents`) is redone with this split boundary, and with
the orders compared only below `2d` (born exponents below the mark `d` come from orders `< 2d` along the birth centres):

* `OrdAgreeBelowAt P Q x` ((O<) at a point: the cosupports of every mark `e ≤ 2d` agree at `x`), `ExpAgreeBelowAt P Q y`
  (`min(exp, d)` agree), `CaseT P x` (a member's ideal vanishes to order `≥ 2` along the carrier: lane G11B's Case T); plain
  definitions shared with lane G8B (Lemma M, Case N);
* `min_divExpAlong_eq_of_iff`, `expAgreeBelowAt_pullback_val_iff`, `expAgreeBelowAt_of_restrictEquiv`;
* `geoTransformAlong_addE` (+ `N_`, `ideal_`, `cosupp_`), `isGeoTestTower_of_addE`, `isSNCDivisor_geoTransformAlong`;
* **`expAgreeBelowAt_step_of_cosupport`** (one blowup, native domain), **`expAgreeBelowAt_geoTransform_of_split`** (one blowup at
  the domain points of well-formed marked ideals, no equivalence assumed), **`expAgreeBelowAt_geoTransformAlong_of_addE`** (along
  every test tower of `P + F`), `sameCarrierDim_geoTransformAlong_of_addE`, `ordAgreeBelowAt_stage`;
* **`expAgreeBelowAt_contactCoeffBM`**: the transformed coefficient ideals of `A` and `B` on maximal contact have the same boundary
  exponents below the mark at every cosupport point over `U_A ∩ U_B` (which MAY meet the original members);
* **`expAgreeBelowAt_lowerIdealBM_zero`**, `LowerExpResidualSucc`, **`lowerExpResidual_of_succ`**, `LowerExpResidualSuccStepBM`,
  **`lowerExpResidualStepBM_of_succ`**: the level-`0` case (r0) of `HironakaG8ClassStepResidual.LowerExpResidual` is proved;
  G11's input `LowerExpResidualStepBM n k` follows from the narrowed residual (case (r1), levels `s + 1`).

Every theorem from `ordAgreeBelowAt_stage` on takes the POINTWISE (O<) as an explicit hypothesis `hO` (two `LocWPEquiv` marked
ideals with an SNC boundary — not assumed transverse to the carriers —, closed submanifold carriers of the same dimension, coherent
ideals, the same mark: (O<) at every cosupport point where both are nonzero along their carriers).  It is TRUE (BM08 Thm 6.1 run
with point arcs and a restriction to a generic point of `D ∩ P`; `RESIDUAL-COUNTEREXAMPLE.md` §3) and is being proved by lanes
G8B (Lemma M, Case N) and G8C (Case T); it is not filed as a named input.

Sorry-free.  Universe `0` (as the P6 core).  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8ClassStepHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.DivisorExponentAlong Hironaka.HomogenizedIdealAlong
  Hironaka.MarkedIdealOperationsAlong
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.NormalCrossings Hironaka.GermIdealOrder
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalContact
  Hironaka.HironakaG8DomainExponents Hironaka.CoefficientIdealRestriction
  Hironaka.CoefficientIdealAlongRestrictionTower Hironaka.RestrictedIdealWeight
  Hironaka.BlowupStrictSubmanifold
open Hironaka.HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG8ClassStep (LowerPairs)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.HironakaG8ClassStepResidual (LowerExpResidual)

noncomputable section

universe u

variable {n : ℕ}

/-! ### Orders and exponents below the mark at a point -/

section Defs

variable {X : CMfd.{u} n}

/-- **(O<) at a point**: the orders of `P` and `Q` at `x` agree below `2 d` (stated through the cosupports of every mark
`e ≤ 2 d` at `x`).  The order comparison needed for born exponents BELOW the mark `d` (`RESIDUAL-COUNTEREXAMPLE.md` §1, lane
G11B's `FALLBACK-DECISION-ANALYSIS.md` §1).  A plain definition, not a named input. -/
def OrdAgreeBelowAt (P Q : MarkedIdeal n X) (x : X) : Prop :=
  ∀ e ≤ 2 * P.d, x ∈ cosupport n P.N P.ideal e ↔ x ∈ cosupport n Q.N Q.ideal e

/-- **Boundary exponents agree below the mark at a point**: `min(exp_H P, d) = min(exp_H Q, d)` for every member through the
point (the exponents agree whenever one of them is below the mark). -/
def ExpAgreeBelowAt (P Q : MarkedIdeal n X) (y : X) : Prop :=
  ∀ H ∈ P.E, y ∈ P.cosupp → y ∈ H →
    min (divExpAlong n P.N P.ideal H y) P.d = min (divExpAlong n Q.N Q.ideal H y) P.d

/-- **The tangent case at a point** (lane G11B's Case T): some member through `x` contains the tangent space of the carrier,
in order form: the ideal of the member vanishes to order `≥ 2` along the carrier at `x` (this includes `P.N ⊆ H`). -/
def CaseT (P : MarkedIdeal n X) (x : X) : Prop :=
  ∃ H ∈ P.E, x ∈ H ∧ x ∈ cosupport n P.N (vanishingIdeal (n := n) H) 2

end Defs

/-- **Truncated exponents from truncated divisibility**: if `𝓘_H^e`-divisibility along the two carriers agrees for every
`e ≤ K` near `x ∈ H` (both ideals nonzero along their carriers at `x`), the exponents agree after truncation at `K`. -/
theorem min_divExpAlong_eq_of_iff {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {N N' H : Set M} {I J : GermIdeal n M} {x : M} {r r' : M → M}
    (hr : IsLocalRetraction n N r x) (hr' : IsLocalRetraction n N' r' x) (hx : x ∈ H) (hne : IsNonzeroAlongAt N I x)
    (hne' : IsNonzeroAlongAt N' J x) (hI : ∀ x g, I.mem x g → HolomorphicAt n g x)
    (hJ : ∀ x g, J.mem x g → HolomorphicAt n g x) (K : ℕ)
    (h : ∀ e ≤ K, IsDivNearAlong n N I H e x ↔ IsDivNearAlong n N' J H e x) :
    min (divExpAlong n N I H x) K = min (divExpAlong n N' J H x) K := by
  have key : ∀ e ≤ K, (e ≤ divExpAlong n N I H x ↔ e ≤ divExpAlong n N' J H x) := fun e he =>
    (isDivNearAlong_iff_le_divExpAlong hr hx hne hI).symm.trans
      ((h e he).trans (isDivNearAlong_iff_le_divExpAlong hr' hx hne' hJ))
  have hle : ∀ {a b : ℕ}, (∀ e ≤ K, (e ≤ a ↔ e ≤ b)) → min b K ≤ min a K := fun {a b} hk =>
    le_min ((hk (min b K) (min_le_right _ _)).mpr (min_le_left _ _)) (min_le_right _ _)
  exact le_antisymm (hle fun e he => (key e he).symm) (hle key)

/-- **Truncated exponents at a point are local.** -/
theorem expAgreeBelowAt_pullback_val_iff {Y : CMfd.{u} n} {P Q : MarkedIdeal n Y}
    (hP : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x) (hQ : ∀ x g, Q.ideal.mem x g → HolomorphicAt n g x)
    (U : Opens Y) (p : U) :
    ExpAgreeBelowAt (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P)
        (MarkedIdeal.pullback (Subtype.val : U → Y) Q) p ↔ ExpAgreeBelowAt P Q p := by
  have hcosP : ∀ e, cosupport n ((Subtype.val : U → Y) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → Y) P.ideal) e = (Subtype.val : U → Y) ⁻¹' cosupport n P.N P.ideal e :=
    fun e => cosupp_pullback_val (⟨P.N, [], P.ideal, e⟩ : MarkedIdeal n Y) hP U
  have hcosQ : ∀ e, cosupport n ((Subtype.val : U → Y) ⁻¹' Q.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Q.ideal) e = (Subtype.val : U → Y) ⁻¹' cosupport n Q.N Q.ideal e :=
    fun e => cosupp_pullback_val (⟨Q.N, [], Q.ideal, e⟩ : MarkedIdeal n Y) hQ U
  have hmap : Filter.map (Subtype.val : U → Y) (𝓝 p) = 𝓝 (p : Y) :=
    map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (U : Set Y)) p.2 (U.isOpen.mem_nhds p.2)
  have hcos : p ∈ (MarkedIdeal.pullback (Subtype.val : U → Y) P).cosupp ↔ (p : Y) ∈ P.cosupp := by
    rw [cosupp_pullback_val P hP U]
    rfl
  have hexp : ∀ H : Set Y, divExpAlong n ((Subtype.val : U → Y) ⁻¹' P.N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) P.ideal) ((Subtype.val : U → Y) ⁻¹' H) p =
        divExpAlong n P.N P.ideal H p ∧
      divExpAlong n ((Subtype.val : U → Y) ⁻¹' Q.N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Q.ideal) ((Subtype.val : U → Y) ⁻¹' H) p =
        divExpAlong n Q.N Q.ideal H p := fun H =>
    ⟨MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosP hmap H,
      MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosQ hmap H⟩
  constructor
  · intro h H hH hp hpH
    have h1 : min (divExpAlong n ((Subtype.val : U → Y) ⁻¹' P.N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) P.ideal) ((Subtype.val : U → Y) ⁻¹' H) p) P.d =
      min (divExpAlong n ((Subtype.val : U → Y) ⁻¹' Q.N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Q.ideal) ((Subtype.val : U → Y) ⁻¹' H) p) P.d :=
      h _ (List.mem_map_of_mem hH) (hcos.mpr hp) hpH
    rw [(hexp H).1, (hexp H).2] at h1
    exact h1
  · intro h H' hH' hp hpH'
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    show min (divExpAlong n ((Subtype.val : U → Y) ⁻¹' P.N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) P.ideal) ((Subtype.val : U → Y) ⁻¹' H) p) P.d =
      min (divExpAlong n ((Subtype.val : U → Y) ⁻¹' Q.N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Q.ideal) ((Subtype.val : U → Y) ⁻¹' H) p) P.d
    rw [(hexp H).1, (hexp H).2]
    exact h H hH (hcos.mp hp) hpH'

/-- **Restricted equivalence does not change the truncated exponents.** -/
theorem expAgreeBelowAt_of_restrictEquiv {Y : CMfd.{u} n} {P P' Q Q' : MarkedIdeal n Y} (hP : RestrictEquiv P P')
    (hQ : RestrictEquiv Q Q') {y : Y} (h : ExpAgreeBelowAt P Q y) : ExpAgreeBelowAt P' Q' y := by
  intro H hH hy hyH
  rw [← divExpAlong_eq_of_restrictEquiv hP H y, ← divExpAlong_eq_of_restrictEquiv hQ H y, ← hP.d_eq]
  exact h H (hP.E_eq ▸ hH) (hP.cosupp_eq ▸ hy) hyH

/-! ### Added members along towers -/

section AddE

variable {X : CMfd.{0} n}

/-- **Members added in front of the boundary are carried along every tower**: the transform of `P` with `F` added is the
transform of `P` with the strict transforms of `F` added (same carrier, ideal and mark). -/
theorem geoTransformAlong_addE (P : MarkedIdeal n X) (F : List (Set X)) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), ∃ G : List (Set Y),
      geoTransformAlong { P with E := F ++ P.E } T =
        { geoTransformAlong P T with E := G ++ (geoTransformAlong P T).E }
  | _, .refl => ⟨F, rfl⟩
  | _, .step T C π hπ => by
    obtain ⟨G, hG⟩ := geoTransformAlong_addE P F T
    refine ⟨G.map (geoStrictTransform π C), ?_⟩
    rw [geoTransformAlong_step, geoTransformAlong_step, hG]
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
    show (G ++ (geoTransformAlong P T).E).map (geoStrictTransform π C) ++ [π ⁻¹' C] =
      G.map (geoStrictTransform π C) ++ ((geoTransformAlong P T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
    rw [List.map_append, List.append_assoc]

theorem N_geoTransformAlong_addE (P : MarkedIdeal n X) (F : List (Set X)) {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    (geoTransformAlong { P with E := F ++ P.E } T).N = (geoTransformAlong P T).N := by
  obtain ⟨G, hG⟩ := geoTransformAlong_addE P F T
  rw [hG]

theorem ideal_geoTransformAlong_addE (P : MarkedIdeal n X) (F : List (Set X)) {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    (geoTransformAlong { P with E := F ++ P.E } T).ideal = (geoTransformAlong P T).ideal := by
  obtain ⟨G, hG⟩ := geoTransformAlong_addE P F T
  rw [hG]

theorem cosupp_geoTransformAlong_addE (P : MarkedIdeal n X) (F : List (Set X)) {Y : CMfd.{0} n} (T : BlowupTower X Y) :
    (geoTransformAlong { P with E := F ++ P.E } T).cosupp = (geoTransformAlong P T).cosupp := by
  obtain ⟨G, hG⟩ := geoTransformAlong_addE P F T
  rw [hG]
  rfl

/-- **A test tower of `P` with added members is a test tower of `P`** (normal crossings with `F ++ E` give normal crossings
with `E`). -/
theorem isGeoTestTower_of_addE (P : MarkedIdeal n X) (F : List (Set X)) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower { P with E := F ++ P.E } T → IsGeoTestTower P T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
    refine (isGeoTestTower_step_iff P T C π hπ).mpr ⟨isGeoTestTower_of_addE P F T hTT, ?_⟩
    obtain ⟨G, hG⟩ := geoTransformAlong_addE P F T
    rw [hG] at hC
    exact ⟨hC.1, hC.2.1, HironakaG8ClassStepCut.hasNormalCrossings_of_append hC.2.2⟩

/-- **Along test towers the boundary stays simple normal crossings.** -/
theorem isSNCDivisor_geoTransformAlong {P : MarkedIdeal n X} (hP : IsSNCDivisor n P.E) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower P T → IsSNCDivisor n (geoTransformAlong P T).E
  | _, .refl, _ => hP
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff P T C π hπ).mp hT
    exact SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ
      (isSNCDivisor_geoTransformAlong hP T hTT) hC.2.2

end AddE

/-! ### One step in the native domain, from the cosupports on the centre -/

section OneStep

/-- **Truncated exponents after one admissible blowup, from the cosupports of the marks `≤ 2d` on the centre** (native
domain): the old members keep their exponents (strict transforms); the born member has exponent `divExpAlong(𝔞, C) − d`, and
the exponents along the centre agree after truncation at `2d` as soon as the cosupports of the marks `e ≤ 2d` agree on the
centre; so the born exponents agree after truncation at `d`. -/
theorem expAgreeBelowAt_step_of_cosupport {X Y Z : CMfd.{0} n} {P Q : MarkedIdeal n X} {kP kQ : ℕ}
    (hP : IsInvDomain kP P) (hQ : IsInvDomain kQ Q) (hd : Q.d = P.d) (T : BlowupTower X Y) (hT : IsGeoTestTower P T)
    (hTQ : IsGeoTestTower Q T) (hET : (geoTransformAlong Q T).E = (geoTransformAlong P T).E)
    {C : Set Y} (hC : (geoTransformAlong P T).IsAdmissibleCentre C) (hCQ : (geoTransformAlong Q T).IsAdmissibleCentre C)
    {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (hcosC : ∀ x ∈ C, ∀ e ≤ 2 * P.d, x ∈ cosupport n (geoTransformAlong P T).N (geoTransformAlong P T).ideal e ↔
      x ∈ cosupport n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal e)
    {z : Z} (hz : z ∈ (geoTransformAlong P (.step T C π hπ)).cosupp)
    (hzQ : z ∈ (geoTransformAlong Q (.step T C π hπ)).cosupp)
    (hexp : ExpAgreeBelowAt (geoTransformAlong P T) (geoTransformAlong Q T) (π z)) :
    ExpAgreeBelowAt (geoTransformAlong P (.step T C π hπ)) (geoTransformAlong Q (.step T C π hπ)) z := by
  have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP T hT
  have hdB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ T hTQ
  have hzN : z ∈ ((geoTransformAlong P T).geoTransform C π).N :=
    ((geoTransformAlong P T).geoTransform C π).cosupp_subset_N hz
  have hzNB : z ∈ ((geoTransformAlong Q T).geoTransform C π).N :=
    ((geoTransformAlong Q T).geoTransform C π).cosupp_subset_N hzQ
  have hholA : ∀ x g, (geoTransformAlong P T).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdA.isWellFormed.isCoherent hg
  have hholB : ∀ x g, (geoTransformAlong Q T).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdB.isWellFormed.isCoherent hg
  have hpz : π z ∈ (geoTransformAlong P T).cosupp :=
    CompanionReductionAlong.mem_cosupp_of_mem_cosupp_geoTransform_along hdA.isWellFormed.isClosedSubmanifold_N.1
      hholA hC hπ hz
  intro H hH _ hzH
  change H ∈ (geoTransformAlong P T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] at hH
  rcases List.mem_append.mp hH with hold | hborn
  · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hold
    obtain ⟨i, hi⟩ := List.get_of_mem hH₀
    obtain ⟨j, hj⟩ := List.get_of_mem (hET.symm ▸ hH₀ : H₀ ∈ (geoTransformAlong Q T).E)
    have hzi : z ∈ geoStrictTransform π C ((geoTransformAlong P T).E.get i) := by rw [hi]; exact hzH
    have hzj : z ∈ geoStrictTransform π C ((geoTransformAlong Q T).E.get j) := by rw [hj]; exact hzH
    have eA := HironakaActualOldDivisorExponentTransport.original_history_old_exponent P hP T hT hC hπ i hzN hzi
    have eB := HironakaActualOldDivisorExponentTransport.original_history_old_exponent Q hQ T hTQ hCQ hπ j hzNB hzj
    rw [hi] at eA
    rw [hj] at eB
    have hH₀c : IsClosed H₀ := hdA.isWellFormed.isSNCDivisor.1 H₀ hH₀
    have hpzH : π z ∈ H₀ := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hH₀c hzH
    show min (divExpAlong n ((geoTransformAlong P T).geoTransform C π).N ((geoTransformAlong P T).geoTransform C π).ideal
        (geoStrictTransform π C H₀) z) (geoTransformAlong P T).d =
      min (divExpAlong n ((geoTransformAlong Q T).geoTransform C π).N ((geoTransformAlong Q T).geoTransform C π).ideal
        (geoStrictTransform π C H₀) z) (geoTransformAlong P T).d
    rw [eA, eB]
    exact hexp H₀ hH₀ hpz hpzH
  · rw [List.mem_singleton] at hborn
    subst hborn
    have hpC : π z ∈ C := hzH
    have bA := HironakaActualPolymorphicBornExponent.original_history_born_exponent P hP T hT hC hπ hzN hpC
    have bB := HironakaActualPolymorphicBornExponent.original_history_born_exponent Q hQ T hTQ hCQ hπ hzNB hpC
    -- truncated exponents along the centre at `π z`
    have hpN : π z ∈ (geoTransformAlong P T).N := (geoTransformAlong P T).cosupp_subset_N (hC.2.1 hpC)
    have hpNB : π z ∈ (geoTransformAlong Q T).N := (geoTransformAlong Q T).cosupp_subset_N (hCQ.2.1 hpC)
    obtain ⟨kA, hkA⟩ := hdA.isWellFormed.isClosedSubmanifold_N.2 (π z) hpN
    obtain ⟨kB, hkB⟩ := hdB.isWellFormed.isClosedSubmanifold_N.2 (π z) hpNB
    obtain ⟨rA, hrA⟩ := exists_isLocalRetraction hkA
    obtain ⟨rB, hrB⟩ := exists_isLocalRetraction hkB
    have hmin := min_divExpAlong_eq_of_iff hrA hrB hpC (hdA.isNonzeroAlongAt (π z) hpN)
      (hdB.isNonzeroAlongAt (π z) hpNB) hholA hholB (2 * P.d) fun e he => by
        unfold IsDivNearAlong
        refine eventually_congr (Eventually.of_forall fun w => ?_)
        constructor
        · intro h _ hwC
          exact (hcosC w hwC e he).mp (h ((geoTransformAlong P T).cosupp_subset_N (hC.2.1 hwC)) hwC)
        · intro h _ hwC
          exact (hcosC w hwC e he).mpr (h ((geoTransformAlong Q T).cosupp_subset_N (hCQ.2.1 hwC)) hwC)
    show min (divExpAlong n ((geoTransformAlong P T).geoTransform C π).N ((geoTransformAlong P T).geoTransform C π).ideal
        (π ⁻¹' C) z) (geoTransformAlong P T).d =
      min (divExpAlong n ((geoTransformAlong Q T).geoTransform C π).N ((geoTransformAlong Q T).geoTransform C π).ideal
        (π ⁻¹' C) z) (geoTransformAlong P T).d
    rw [bA.2, bB.2, d_geoTransformAlong, hd]
    have h1 := bA.1
    have h2 := bB.1
    rw [hd] at h2
    omega

/-- **One step at the domain points of well-formed marked ideals, from the cosupports of every mark**: for well-formed `P`,
`Q` with the same mark `d ≥ 1`, the same divisor and the same cosupport, whose cosupports of every mark agree at the
cosupport points where both are nonzero along their carriers, and whose exponents agree there, the exponents of the
transforms along a common admissible blowup agree at every cosupport point where both transforms are nonzero along their
carriers.  No equivalence of `P` and `Q` is assumed (compare lane G8's
`HironakaG8DomainExponents.expAgreeAt_geoTransform_of_domain`, which assumes `LocWPEquiv P Q`). -/
theorem expAgreeBelowAt_geoTransform_of_split {Y Z : CMfd.{0} n} {P Q : MarkedIdeal n Y} (hwfP : P.IsWellFormed)
    (hwfQ : Q.IsWellFormed) (hdP : 1 ≤ P.d) (hd : Q.d = P.d) (hE : Q.E = P.E) (hcos : P.cosupp = Q.cosupp)
    (hord : ∀ x ∈ P.cosupp, IsNonzeroAlongAt P.N P.ideal x → IsNonzeroAlongAt Q.N Q.ideal x → OrdAgreeBelowAt P Q x)
    (hexp : ∀ x ∈ P.cosupp, IsNonzeroAlongAt P.N P.ideal x → IsNonzeroAlongAt Q.N Q.ideal x → ExpAgreeBelowAt P Q x)
    {C : Set Y} (hC : P.IsAdmissibleCentre C) {π : Z → Y} (hπ : IsBlowupAlong n C π) {z : Z}
    (hz : z ∈ (P.geoTransform C π).cosupp) (hzQ : z ∈ (Q.geoTransform C π).cosupp)
    (hzP : IsNonzeroAlongAt (P.geoTransform C π).N (P.geoTransform C π).ideal z)
    (hzQ' : IsNonzeroAlongAt (Q.geoTransform C π).N (Q.geoTransform C π).ideal z) :
    ExpAgreeBelowAt (P.geoTransform C π) (Q.geoTransform C π) z := by
  have hNP := hwfP.isClosedSubmanifold_N
  have hNQ := hwfQ.isClosedSubmanifold_N
  have hIP := hwfP.isCoherent
  have hIQ := hwfQ.isCoherent
  have hholP : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIP hg
  have hholQ : ∀ x g, Q.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIQ hg
  have hdQ : 1 ≤ Q.d := hd ▸ hdP
  have hCQ : Q.IsAdmissibleCentre C := (isAdmissibleCentre_congr hE.symm hcos C).mp hC
  -- the one-step tower
  let T₁ : BlowupTower Y Z := .step .refl C π hπ
  have hT₁ : IsGeoTestTower P T₁ := ⟨trivial, hC⟩
  have hT₁Q : IsGeoTestTower Q T₁ := ⟨trivial, hCQ⟩
  -- descent to `x = π z`
  have hx : π z ∈ P.cosupp :=
    CompanionReductionAlong.mem_cosupp_of_mem_cosupp_geoTransform_along hNP.1 hholP hC hπ hz
  have hxP : IsNonzeroAlongAt P.N P.ideal (π z) := isNonzeroAlongAt_of_geoTransform hπ P hNP hIP hC hzP
  have hxQ : IsNonzeroAlongAt Q.N Q.ideal (π z) := isNonzeroAlongAt_of_geoTransform hπ Q hNQ hIQ hCQ hzQ'
  -- the common domain open
  let G : Opens Y := domOpen P hNP ⊓ domOpen Q hNQ
  have hmemG : ∀ x ∈ P.cosupp, (x ∈ G ↔ IsNonzeroAlongAt P.N P.ideal x ∧ IsNonzeroAlongAt Q.N Q.ideal x) :=
    fun x hx' => and_congr (mem_domOpen_iff hNP hIP hdP (P.cosupp_subset_N hx'))
      (mem_domOpen_iff hNQ hIQ hdQ (Q.cosupp_subset_N (hcos ▸ hx')))
  have hxG : π z ∈ G := (hmemG _ hx).mpr ⟨hxP, hxQ⟩
  have hdomP := isInvDomain_pullback_val_of_le_domOpen hwfP hdP (G := G) inf_le_left
  have hdomQ := isInvDomain_pullback_val_of_le_domOpen hwfQ hdQ (G := G) inf_le_right
  have hTG := isGeoTestTower_restrict G hNP hIP T₁ hT₁
  have hTGQ := isGeoTestTower_restrict G hNQ hIQ T₁ hT₁Q
  have hzG : z ∈ openPreimage T₁ G := hxG
  have hP' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNP hIP hC hπ
  have hQ' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNQ hIQ hCQ hπ
  have hholP' : ∀ x g, (geoTransformAlong P T₁).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hP' hg
  have hholQ' : ∀ x g, (geoTransformAlong Q T₁).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hQ' hg
  have hcosG : ∀ e, cosupport n ((Subtype.val : G → Y) ⁻¹' P.N) (GermIdeal.pullback (m := n) (Subtype.val : G → Y) P.ideal) e =
      (Subtype.val : G → Y) ⁻¹' cosupport n P.N P.ideal e :=
    fun e => cosupp_pullback_val (⟨P.N, [], P.ideal, e⟩ : MarkedIdeal n Y) hholP G
  have hcosGQ : ∀ e, cosupport n ((Subtype.val : G → Y) ⁻¹' Q.N) (GermIdeal.pullback (m := n) (Subtype.val : G → Y) Q.ideal) e =
      (Subtype.val : G → Y) ⁻¹' cosupport n Q.N Q.ideal e :=
    fun e => cosupp_pullback_val (⟨Q.N, [], Q.ideal, e⟩ : MarkedIdeal n Y) hholQ G
  have key : ExpAgreeBelowAt (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G → Y) P) (restrict G T₁))
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G → Y) Q) (restrict G T₁)) ⟨z, hzG⟩ := by
    change IsGeoTestTower _ (.step (restrict G .refl) _ _ _) at hTG hTGQ
    obtain ⟨hT0, hCG⟩ := hTG
    obtain ⟨hT0Q, hCGQ⟩ := hTGQ
    have hzc : (⟨z, hzG⟩ : openPreimage T₁ G) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G → Y) P) (restrict G T₁)).cosupp := by
      rw [geoTransformAlong_restrict G hNP hIP T₁ hT₁, cosupp_pullback_val _ hholP' _]
      exact hz
    have hzcQ : (⟨z, hzG⟩ : openPreimage T₁ G) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : G → Y) Q) (restrict G T₁)).cosupp := by
      rw [geoTransformAlong_restrict G hNQ hIQ T₁ hT₁Q, cosupp_pullback_val _ hholQ' _]
      exact hzQ
    have hEG : (MarkedIdeal.pullback (Subtype.val : G → Y) Q).E = (MarkedIdeal.pullback (Subtype.val : G → Y) P).E := by
      show Q.E.map _ = P.E.map _
      rw [hE]
    refine expAgreeBelowAt_step_of_cosupport (X := CMfd.of (n := n) G) (P := MarkedIdeal.pullback (Subtype.val : G → Y) P)
      (Q := MarkedIdeal.pullback (Subtype.val : G → Y) Q) hdomP hdomQ hd (restrict G .refl) hT0 hT0Q hEG hCG hCGQ _ ?_
      hzc hzcQ ?_
    · intro x hxC e he
      have hxC' : (x : Y) ∈ C := hxC
      have hxc : (x : Y) ∈ P.cosupp := hC.2.1 hxC'
      obtain ⟨h1, h2⟩ := (hmemG _ hxc).mp x.2
      show x ∈ cosupport n ((Subtype.val : G → Y) ⁻¹' P.N) (GermIdeal.pullback (m := n) (Subtype.val : G → Y) P.ideal) e ↔
        x ∈ cosupport n ((Subtype.val : G → Y) ⁻¹' Q.N) (GermIdeal.pullback (m := n) (Subtype.val : G → Y) Q.ideal) e
      rw [hcosG e, hcosGQ e]
      exact hord _ hxc h1 h2 e he
    · exact (expAgreeBelowAt_pullback_val_iff hholP hholQ G ⟨π z, hxG⟩).mpr (hexp _ hx hxP hxQ)
  rw [geoTransformAlong_restrict G hNP hIP T₁ hT₁, geoTransformAlong_restrict G hNQ hIQ T₁ hT₁Q] at key
  exact (expAgreeBelowAt_pullback_val_iff hholP' hholQ' (openPreimage T₁ G) ⟨z, hzG⟩).mp key

end OneStep

/-! ### Along towers: the boundary split into the part used for the tests and the part carrying the exponents -/

section Tower

variable {X : CMfd.{0} n}

/-- **Born exponents along towers with a split boundary** (P6 without an equivalence of the two marked ideals themselves):
let `P`, `Q` be well-formed with the same mark `d ≥ 1` and the same divisor, and let `F` be further members such that `P` and
`Q` with `F` added are `WEquiv` (the TESTS: centres with normal crossings with `F` too).  If along every test tower of `P + F`
the cosupports of every mark of the two transforms agree at the cosupport points where both are nonzero along their carriers
(equal ORDERS there, e.g. from `OrdAgreeLocWP`), and the exponents agree initially at those points (e.g. `E = []`), then along
every test tower of `P + F` the exponents of `P_T` and `Q_T` agree at every cosupport point where both are nonzero along their
carriers. -/
theorem expAgreeBelowAt_geoTransformAlong_of_addE {P Q : MarkedIdeal n X} (F : List (Set X))
    (hwfP : P.IsWellFormed) (hwfQ : Q.IsWellFormed) (hdP : 1 ≤ P.d) (hd : Q.d = P.d) (hE : Q.E = P.E)
    (hW : WEquiv { P with E := F ++ P.E } { Q with E := F ++ P.E })
    (hord : ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower { P with E := F ++ P.E } T →
      ∀ y ∈ (geoTransformAlong P T).cosupp,
        IsNonzeroAlongAt (geoTransformAlong P T).N (geoTransformAlong P T).ideal y →
        IsNonzeroAlongAt (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal y →
        OrdAgreeBelowAt (geoTransformAlong P T) (geoTransformAlong Q T) y)
    (hexp : ∀ x ∈ P.cosupp, IsNonzeroAlongAt P.N P.ideal x → IsNonzeroAlongAt Q.N Q.ideal x → ExpAgreeBelowAt P Q x) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower { P with E := F ++ P.E } T →
      ∀ y ∈ (geoTransformAlong P T).cosupp,
        IsNonzeroAlongAt (geoTransformAlong P T).N (geoTransformAlong P T).ideal y →
        IsNonzeroAlongAt (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal y →
        ExpAgreeBelowAt (geoTransformAlong P T) (geoTransformAlong Q T) y
  | _, .refl, _ => hexp
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, -⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
    have ih := expAgreeBelowAt_geoTransformAlong_of_addE F hwfP hwfQ hdP hd hE hW hord hexp T hTT
    have hFQ : ({ Q with E := F ++ P.E } : MarkedIdeal n X) = { Q with E := F ++ Q.E } := by rw [hE]
    have hTP : IsGeoTestTower P T := isGeoTestTower_of_addE P F T hTT
    have hTQ' : IsGeoTestTower { Q with E := F ++ P.E } T := (hW.2 T).1.mp hTT
    have hTQ : IsGeoTestTower Q T := isGeoTestTower_of_addE Q F T (hFQ ▸ hTQ')
    have hcos : (geoTransformAlong P T).cosupp = (geoTransformAlong Q T).cosupp := by
      rw [← cosupp_geoTransformAlong_addE P F T, (hW.2 T).2 hTT, hFQ, cosupp_geoTransformAlong_addE Q F T]
    have hcos' : (geoTransformAlong P (.step T C π hπ)).cosupp = (geoTransformAlong Q (.step T C π hπ)).cosupp := by
      rw [← cosupp_geoTransformAlong_addE P F, (hW.2 (.step T C π hπ)).2 hT, hFQ, cosupp_geoTransformAlong_addE Q F]
    have hCP : (geoTransformAlong P T).IsAdmissibleCentre C :=
      ((isGeoTestTower_step_iff P T C π hπ).mp (isGeoTestTower_of_addE P F (.step T C π hπ) hT)).2
    have hET : (geoTransformAlong Q T).E = (geoTransformAlong P T).E :=
      MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE T
    intro y hy hyP hyQ
    exact expAgreeBelowAt_geoTransform_of_split (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfP T hTP)
      (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfQ T hTQ)
      (by rw [d_geoTransformAlong]; exact hdP) (by rw [d_geoTransformAlong, d_geoTransformAlong, hd]) hET hcos
      (hord T hTT) ih hCP hπ hy (hcos' ▸ hy) hyP hyQ


/-- **Carriers of the same dimension along the test towers of `P + F`** (one-step lemma `HironakaG8SpecialLoci.sameCarrierDim_geoTransform` at
every step; the cosupports agree by the `WEquiv` of `P + F` and `Q + F`). -/
theorem sameCarrierDim_geoTransformAlong_of_addE {P Q : MarkedIdeal n X} (F : List (Set X)) (hwfP : P.IsWellFormed)
    (hwfQ : Q.IsWellFormed) (hE : Q.E = P.E) (hW : WEquiv { P with E := F ++ P.E } { Q with E := F ++ P.E })
    (hdim : SameCarrierDim P Q) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower { P with E := F ++ P.E } T →
      SameCarrierDim (geoTransformAlong P T) (geoTransformAlong Q T)
  | _, .refl, _ => hdim
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, -⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
    have hFQ : ({ Q with E := F ++ P.E } : MarkedIdeal n X) = { Q with E := F ++ Q.E } := by rw [hE]
    have hTP : IsGeoTestTower P T := isGeoTestTower_of_addE P F T hTT
    have hTQ : IsGeoTestTower Q T := isGeoTestTower_of_addE Q F T (hFQ ▸ (hW.2 T).1.mp hTT)
    have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfP T hTP
    have hwB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfQ T hTQ
    have hcos : (geoTransformAlong P T).cosupp = (geoTransformAlong Q T).cosupp := by
      rw [← cosupp_geoTransformAlong_addE P F T, (hW.2 T).2 hTT, hFQ, cosupp_geoTransformAlong_addE Q F T]
    have hcos' : (geoTransformAlong P (.step T C π hπ)).cosupp = (geoTransformAlong Q (.step T C π hπ)).cosupp := by
      rw [← cosupp_geoTransformAlong_addE P F, (hW.2 (.step T C π hπ)).2 hT, hFQ, cosupp_geoTransformAlong_addE Q F]
    have hCP : (geoTransformAlong P T).IsAdmissibleCentre C :=
      ((isGeoTestTower_step_iff P T C π hπ).mp (isGeoTestTower_of_addE P F (.step T C π hπ) hT)).2
    have hCB : C ⊆ (geoTransformAlong Q T).N := fun c hc =>
      (geoTransformAlong Q T).cosupp_subset_N (hcos ▸ hCP.2.1 hc)
    exact HironakaG8SpecialLoci.sameCarrierDim_geoTransform hwA.isClosedSubmanifold_N hwB.isClosedSubmanifold_N
      (fun x g hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwA.isCoherent hg)
      (sameCarrierDim_geoTransformAlong_of_addE F hwfP hwfQ hE hW hdim T hTT) hCP hCB hπ hcos'

/-- **The order hypothesis of `expAgreeBelowAt_geoTransformAlong_of_addE` from the pointwise (O<)** (`hO`: for any two
`LocWPEquiv` marked ideals with an SNC boundary — not assumed transverse to the carriers —, closed submanifold carriers of the
same dimension, coherent ideals and the same mark, (O<) holds at every cosupport point where both are nonzero along their
carriers; lanes G8B (Lemma M, Case N) and G8C (Case T) prove it): if `P + F ≈ Q + F` with an SNC boundary, then at every stage
of every test tower of `P + F` the orders of the two transforms agree below `2d` at the cosupport points where both are nonzero
along their carriers. -/
theorem ordAgreeBelowAt_stage
    (hO : ∀ {Z : CMfd.{0} n} (P' Q' : MarkedIdeal n Z), LocWPEquiv P' Q' → IsClosedSubmanifold n P'.N →
      IsClosedSubmanifold n Q'.N → P'.ideal.IsCoherent → Q'.ideal.IsCoherent → IsSNCDivisor n P'.E → 1 ≤ P'.d →
      Q'.d = P'.d → SameCarrierDim P' Q' → ∀ x ∈ P'.cosupp, IsNonzeroAlongAt P'.N P'.ideal x →
        IsNonzeroAlongAt Q'.N Q'.ideal x → OrdAgreeBelowAt P' Q' x)
    {P Q : MarkedIdeal n X} (F : List (Set X))
    (hwfP : P.IsWellFormed) (hwfQ : Q.IsWellFormed) (hdP : 1 ≤ P.d) (hd : Q.d = P.d) (hE : Q.E = P.E)
    (hL : LocWPEquiv { P with E := F ++ P.E } { Q with E := F ++ P.E }) (hsnc : IsSNCDivisor n (F ++ P.E))
    (hdim : SameCarrierDim P Q) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower { P with E := F ++ P.E } T →
      ∀ y ∈ (geoTransformAlong P T).cosupp,
        IsNonzeroAlongAt (geoTransformAlong P T).N (geoTransformAlong P T).ideal y →
        IsNonzeroAlongAt (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal y →
        OrdAgreeBelowAt (geoTransformAlong P T) (geoTransformAlong Q T) y := by
  intro Y T hT y hy hyP hyQ
  have hW := hL.wEquiv
  have hFQ : ({ Q with E := F ++ P.E } : MarkedIdeal n X) = { Q with E := F ++ Q.E } := by rw [hE]
  have hTP : IsGeoTestTower P T := isGeoTestTower_of_addE P F T hT
  have hTQ : IsGeoTestTower Q T := isGeoTestTower_of_addE Q F T (hFQ ▸ (hW.2 T).1.mp hT)
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfP T hTP
  have hwB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfQ T hTQ
  have hLT := LocEquiv.geoTransformAlong hL T hT
  obtain ⟨G, hG⟩ := geoTransformAlong_addE P F T
  obtain ⟨G', hG'⟩ := geoTransformAlong_addE Q F T
  have hsncT := isSNCDivisor_geoTransformAlong (P := { P with E := F ++ P.E }) hsnc T hT
  rw [hG] at hLT hsncT
  rw [hFQ, hG'] at hLT
  have hdimT := sameCarrierDim_geoTransformAlong_of_addE F hwfP hwfQ hE hW hdim T hT
  exact hO _ _ hLT hwA.isClosedSubmanifold_N hwB.isClosedSubmanifold_N hwA.isCoherent hwB.isCoherent hsncT
    (show 1 ≤ (geoTransformAlong P T).d by rw [d_geoTransformAlong]; exact hdP)
    (show (geoTransformAlong Q T).d = (geoTransformAlong P T).d by rw [d_geoTransformAlong, d_geoTransformAlong, hd])
    hdimT y hy hyP hyQ

end Tower

/-! ### The coefficient ideals on maximal contact of two class-equivalent marked ideals -/

section Contact

variable {X : CMfd.{0} n}

/-- The coefficient ideal of `𝔍_∅` on a hypersurface of maximal contact, restricted to an open `W` inside the open set of the
tangent direction: well formed, and its carrier has dimension one less than that of `𝔍` (a copy of the private lemma of
`HironakaG8ClassStepResidual`). -/
private theorem contact_facts {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) {U : Set X} {w : X → ℂ}
    (hw : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w) (W : Opens X) (hWU : (W : Set X) ⊆ U) :
    (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | w x = 0}))).IsWellFormed ∧
      ∀ x ∈ (Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0}), ∃ k,
        RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' 𝔍.N) x k ∧
        RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0})) x (k - 1) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) := contMDiff_subtype_val
  have hwW := IsTangentDirectionAlong.mono_open hw W.isOpen hWU
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN W
  have hcU : (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞
  have hwU := isTangentDirectionAlong_pullback_val W hhol hwW
  have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) W)
    (𝔪 := MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)) hNU hcU hwU
  rw [preimage_val_contact_eq W] at h1
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hcohA := GermIdealPullbackCalculus.isCoherent_pullback hval hwfc.isCoherent
  refine ⟨⟨h1, hcohA, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold h1⟩, fun x hx => ?_⟩
  have hx' : x ∈ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N ∩
      {x : W | (w ∘ Subtype.val) x = 0} ∩ univ := by
    rw [preimage_val_contact_eq W]; exact hx
  obtain ⟨k, hk, hk'⟩ := IsTangentDirectionAlong.regularAtDim_contact
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcU) hNU hwU hx'
  rw [preimage_val_contact_eq W] at hk'
  exact ⟨k, hk, hk'⟩

/-- **The born exponents of the coefficient ideals on maximal contact are history-determined** (given `OrdAgreeLocWP`): for
class-equivalent `A ≈ B` (`LocWPEquiv`, the same mark and divisor, carriers of the same dimension on the cosupport) in the
domain, tangent directions `u_A` on `U_A`, `u_B` on `U_B`, an open `W ⊆ U_A ∩ U_B` (which MAY meet the original members) and a
test tower `T₀` of `A`, BM's transformed coefficient ideals `contactCoeffBM A u_A T₀` and `contactCoeffBM B u_B T₀` have the
same boundary exponents at every cosupport point over `W` at which both are nonzero along their carriers.  Proof: the base pair
`𝒞_W(A_∅)`, `𝒞_W(B_∅)` is not equivalent, but with the original members added it is (`𝒞_W(A_∅) + E ≈ A|_W ≈ B|_W ≈
𝒞_W(B_∅) + E`: BM08 Cor 4.2 and `locEquiv_addE`); `OrdAgreeLocWP` gives the orders at every stage, and
`expAgreeAt_geoTransformAlong_of_addE` the exponents. -/
theorem expAgreeBelowAt_contactCoeffBM
    (hO : ∀ {Z : CMfd.{0} n} (P' Q' : MarkedIdeal n Z), LocWPEquiv P' Q' → IsClosedSubmanifold n P'.N →
      IsClosedSubmanifold n Q'.N → P'.ideal.IsCoherent → Q'.ideal.IsCoherent → IsSNCDivisor n P'.E → 1 ≤ P'.d →
      Q'.d = P'.d → SameCarrierDim P' Q' → ∀ x ∈ P'.cosupp, IsNonzeroAlongAt P'.N P'.ideal x →
        IsNonzeroAlongAt Q'.N Q'.ideal x → OrdAgreeBelowAt P' Q' x)
    {k k' : ℕ} {A B : MarkedIdeal n X}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B) (h : LocWPEquiv A B) (hd : A.d = B.d) (hE : A.E = B.E)
    (hdim : SameCarrierDim A B) {UA UB : Set X} {uA uB : X → ℂ}
    (huA : IsTangentDirectionAlong A.N A.ideal A.d UA uA) (huB : IsTangentDirectionAlong B.N B.ideal B.d UB uB)
    (W : Opens X) (hWA : (W : Set X) ⊆ UA) (hWB : (W : Set X) ⊆ UB) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hTA : IsGeoTestTower A T₀) {p : Y₀} (hpW : p ∈ openPreimage T₀ W)
    (hpA : IsNonzeroAlongAt (contactCoeffBM A uA T₀).N (contactCoeffBM A uA T₀).ideal p)
    (hpB : IsNonzeroAlongAt (contactCoeffBM B uB T₀).N (contactCoeffBM B uB T₀).ideal p) :
    ExpAgreeBelowAt (contactCoeffBM A uA T₀) (contactCoeffBM B uB T₀) p := by
  have hTB : IsGeoTestTower B T₀ := ((LocEquiv.wEquiv h).2 T₀).1.mp hTA
  have hwAW : IsTangentDirectionAlong A.N A.ideal A.d (W : Set X) uA := IsTangentDirectionAlong.mono_open huA W.isOpen hWA
  have hwBW : IsTangentDirectionAlong B.N B.ideal B.d (W : Set X) uB := IsTangentDirectionAlong.mono_open huB W.isOpen hWB
  obtain ⟨hwfP, hregA⟩ := contact_facts hA.isWellFormed huA W hWA
  obtain ⟨hwfQ, hregB⟩ := contact_facts hB.isWellFormed huB W hWB
  set P := MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM A) (A.N ∩ {x | uA x = 0})) with hPdef
  set Q := MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM B) (B.N ∩ {x | uB x = 0})) with hQdef
  set F := (MarkedIdeal.pullback (Subtype.val : W → X) A).E with hFdef
  -- `𝒞_W(A_∅) ≈ A_∅|_W`, `𝒞_W(B_∅) ≈ B_∅|_W`, then add the original members
  have hcA : LocWPEquiv (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A)) P :=
    locWPEquiv_contact_open_along (emptyBoundary A) hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent
      hA.one_le_d W hwAW
  have hcB : LocWPEquiv (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B)) Q :=
    locWPEquiv_contact_open_along (emptyBoundary B) hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent
      hB.one_le_d W hwBW
  have hcAF := HironakaG8ClassStepCut.locEquiv_addE rfl hcA F
  have hcBF := HironakaG8ClassStepCut.locEquiv_addE rfl hcB F
  have hAW : ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A) with
      E := F ++ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A)).E } : MarkedIdeal n W) =
      MarkedIdeal.pullback (Subtype.val : W → X) A := by
    show ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A) with E := F ++ [] } : MarkedIdeal n W) = _
    rw [List.append_nil]
    rfl
  have hBW : ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B) with
      E := F ++ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B)).E } : MarkedIdeal n W) =
      MarkedIdeal.pullback (Subtype.val : W → X) B := by
    show ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B) with E := F ++ [] } : MarkedIdeal n W) = _
    rw [List.append_nil, hFdef]
    show ({ MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary B) with E := A.E.map _ } : MarkedIdeal n W) = _
    rw [hE]
    rfl
  rw [hAW] at hcAF
  rw [hBW] at hcBF
  have hrest := LocEquiv.restrict h W
  have hL : LocWPEquiv (X := CMfd.of (n := n) W) { P with E := F ++ P.E } { Q with E := F ++ P.E } :=
    hcAF.symm.trans (hrest.trans hcBF)
  -- the data of the base pair
  have hsnc : IsSNCDivisor n (F ++ P.E) := by
    show IsSNCDivisor n (F ++ [])
    rw [List.append_nil]
    exact (IsWellFormed.pullback_val hA.isWellFormed W).isSNCDivisor
  have hdP : 1 ≤ P.d := ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary A)
  have hdd : Q.d = P.d := by
    show (coeffEmptyBM B).d = (coeffEmptyBM A).d
    rw [coeffEmptyBM_d, coeffEmptyBM_d, hd]
  have hEQ : Q.E = P.E := rfl
  have hcosPQ : P.cosupp = Q.cosupp := hL.cosupp_eq_base
  have hdimPQ : SameCarrierDim (X := CMfd.of (n := n) W) P Q := by
    intro x hx j
    have hxA0 : x ∈ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A)).cosupp := hcA.cosupp_eq_base ▸ hx
    have hxA : (x : X) ∈ A.cosupp := by
      have h1 := cosupp_pullback_val (emptyBoundary A)
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA.isWellFormed.isCoherent) W
      rw [h1] at hxA0
      exact hxA0
    have hxB := hcosPQ ▸ hx
    obtain ⟨kA, hkA, hkSA⟩ := hregA x (MarkedIdeal.cosupp_subset_N _ hx)
    obtain ⟨kB, hkB, hkSB⟩ := hregB x (MarkedIdeal.cosupp_subset_N _ hxB)
    have hkA' : RegularAtDim (n := n) A.N (x : X) kA := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hkA
    have hkB' : RegularAtDim (n := n) B.N (x : X) kB := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hkB
    have hkk : kA = kB := RegularPointDimension.eq_of_regularAtDim ((hdim (x : X) hxA kA).mp hkA') hkB'
    show RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (A.N ∩ {y | uA y = 0})) x j ↔
      RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (B.N ∩ {y | uB y = 0})) x j
    constructor
    · intro hj
      rw [← RegularPointDimension.eq_of_regularAtDim hkSA hj, hkk]; exact hkSB
    · intro hj
      rw [← RegularPointDimension.eq_of_regularAtDim hkSB hj, ← hkk]; exact hkSA
  -- the restricted tower
  obtain ⟨-, hRE⟩ := restrictEquiv_stage_contactCoeffBM hA.isWellFormed hA.one_le_d W hwAW T₀ hTA
  obtain ⟨-, hRE'⟩ := restrictEquiv_stage_contactCoeffBM hB.isWellFormed hB.one_le_d W hwBW T₀ hTB
  have hTF : IsGeoTestTower (X := CMfd.of (n := n) W) { P with E := F ++ P.E } (restrict W T₀) :=
    (hcAF.wEquiv.2 _).1.mp (isGeoTestTower_restrict W hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent
      T₀ hTA)
  -- coherence of the two transformed coefficient ideals
  have hTc := HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d _
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A _ hTA)
  have hTcB := HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hB.isWellFormed hB.one_le_d _
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary B _ hTB)
  have hwfc := isWellFormed_coeffEmptyBM hA.isWellFormed
  have hwfcB := isWellFormed_coeffEmptyBM hB.isWellFormed
  obtain ⟨-, hcL⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N hwfc.isCoherent
    T₀ hTc
  obtain ⟨-, hcL'⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfcB.isClosedSubmanifold_N
    hwfcB.isCoherent T₀ hTcB
  have hholL : ∀ x g, (contactCoeffBM A uA T₀).ideal.mem x g → HolomorphicAt n g x := hol_of_isCoherent hcL
  have hholL' : ∀ x g, (contactCoeffBM B uB T₀).ideal.mem x g → HolomorphicAt n g x := hol_of_isCoherent hcL'
  -- localize at `p`
  rw [← expAgreeBelowAt_pullback_val_iff hholL hholL' (openPreimage T₀ W) ⟨p, hpW⟩]
  intro H hH hy hyH
  have hyA := hRE.cosupp_eq ▸ hy
  have hyAN := MarkedIdeal.cosupp_subset_N _ hyA
  have hcosT : (geoTransformAlong (X := CMfd.of (n := n) W) P (restrict W T₀)).cosupp =
      (geoTransformAlong (X := CMfd.of (n := n) W) Q (restrict W T₀)).cosupp := by
    rw [← cosupp_geoTransformAlong_addE (X := CMfd.of (n := n) W) P F, (hL.wEquiv.2 _).2 hTF]
    exact cosupp_geoTransformAlong_addE (X := CMfd.of (n := n) W) Q F _
  have hyBN := MarkedIdeal.cosupp_subset_N _ (hcosT ▸ hyA)
  have nzA := (isNonzeroAlongAt_iff_of_restrictEquiv hRE hyAN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL (openPreimage T₀ W) ⟨p, hpW⟩).mpr hpA)
  have nzB := (isNonzeroAlongAt_iff_of_restrictEquiv hRE' hyBN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL' (openPreimage T₀ W) ⟨p, hpW⟩).mpr hpB)
  have hkey := expAgreeBelowAt_geoTransformAlong_of_addE (X := CMfd.of (n := n) W) F hwfP hwfQ hdP hdd hEQ hL.wEquiv
    (ordAgreeBelowAt_stage (X := CMfd.of (n := n) W) hO F hwfP hwfQ hdP hdd hEQ hL hsnc hdimPQ)
    (fun x _ _ _ H hH => absurd hH List.not_mem_nil) (restrict W T₀) hTF _ hyA nzA nzB
  exact expAgreeBelowAt_of_restrictEquiv hRE hRE' hkey H hH hy hyH

end Contact

/-! ### The residual at level `0`, and the narrowed residual -/

section Residual

variable {X : CMfd.{0} n}

/-- **Level `0`, every point** (given the pointwise (O<)): the lower ideals of class-equivalent `A ≈ B` have the same boundary
exponents below the mark at every point of a common open of the level-`0` masks on which both restricted lower ideals lie in
the domain — including the points whose history enters the original divisor (the case (r0) of `LowerExpResidual`). -/
theorem expAgreeBelowAt_lowerIdealBM_zero
    (hO : ∀ {Z : CMfd.{0} n} (P' Q' : MarkedIdeal n Z), LocWPEquiv P' Q' → IsClosedSubmanifold n P'.N →
      IsClosedSubmanifold n Q'.N → P'.ideal.IsCoherent → Q'.ideal.IsCoherent → IsSNCDivisor n P'.E → 1 ≤ P'.d →
      Q'.d = P'.d → SameCarrierDim P' Q' → ∀ x ∈ P'.cosupp, IsNonzeroAlongAt P'.N P'.ideal x →
        IsNonzeroAlongAt Q'.N Q'.ideal x → OrdAgreeBelowAt P' Q' x)
    (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d) (h : LocWPEquiv A B)
    (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked A) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked A) T₀).cosupp)
    (O : Opens Y₀) (hOA : O ≤ maskBM A 0 T₀ y₀) (hOB : O ≤ maskBM B 0 T₀ y₀) {r r' : ℕ}
    (hdA : IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A 0 T₀ y₀)))
    (hdB : IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B 0 T₀ y₀)))
    {y : Y₀} (hyO : y ∈ O) :
    ExpAgreeBelowAt (lowerIdealBM A 0 T₀ y₀) (lowerIdealBM B 0 T₀ y₀) y := by
  have hWA : WEquiv (barMarked A) A := StepOneBridge.barMarked_wEquiv A hA
  have hWB : WEquiv (barMarked B) B := StepOneBridge.barMarked_wEquiv B hB
  have hW : WEquiv A B := LocEquiv.wEquiv h
  have hTA : IsGeoTestTower A T₀ := (hWA.2 T₀).1.mp hT₀
  have hTB : IsGeoTestTower B T₀ := (hW.2 T₀).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T₀ := (hWB.2 T₀).1.mpr hTB
  have hyA : y₀ ∈ (geoTransformAlong A T₀).cosupp := (hWA.2 T₀).2 hT₀ ▸ hy₀
  have hyB : y₀ ∈ (geoTransformAlong (barMarked B) T₀).cosupp := by
    rw [(hWB.2 T₀).2 hTJB, ← (hW.2 T₀).2 hTA]
    exact hyA
  obtain ⟨-, hwA⟩ := StepOneLowerDomain.tangentChoice_spec A
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp A hA.isWellFormed hA.one_le_d hmA T₀ hT₀ hy₀)
  obtain ⟨-, hwB⟩ := StepOneLowerDomain.tangentChoice_spec B
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp B hB.isWellFormed hB.one_le_d hmB T₀ hTJB hyB)
  let W : Opens X := ⟨(tangentChoice A (T₀.proj y₀)).1 ∩ (tangentChoice B (T₀.proj y₀)).1, hwA.isOpen.inter hwB.isOpen⟩
  have hcL := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ 0
  have hcL' := HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T₀ hTJB y₀ 0
  have hloc := HironakaG8ClassStepLower.locWPEquiv_lowerIdealBM_zero hn hA hB hmA hmB h hE T₀ hT₀ hy₀ O hOA hOB
  intro H hH hy hyH
  let p : O := ⟨y, hyO⟩
  have hpO : p ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A 0 T₀ y₀)).cosupp := by
    rw [cosupp_pullback_val _ (hol_of_isCoherent hcL) O]
    exact hy
  have hpO' := hloc.cosupp_eq_base ▸ hpO
  have nz1 : IsNonzeroAlongAt (lowerIdealBM A 0 T₀ y₀).N (lowerIdealBM A 0 T₀ y₀).ideal y :=
    (isNonzeroAlongAt_pullback_val_iff hcL O p).mp (hdA.isNonzeroAlongAt _ (MarkedIdeal.cosupp_subset_N _ hpO))
  have nz2 : IsNonzeroAlongAt (lowerIdealBM B 0 T₀ y₀).N (lowerIdealBM B 0 T₀ y₀).ideal y :=
    (isNonzeroAlongAt_pullback_val_iff hcL' O p).mp (hdB.isNonzeroAlongAt _ (MarkedIdeal.cosupp_subset_N _ hpO'))
  have hpW : y ∈ openPreimage T₀ W := ⟨(interior_subset (hOA hyO)).1, (interior_subset (hOB hyO)).1⟩
  exact expAgreeBelowAt_contactCoeffBM hO hA hB h hd hE hdim hwA hwB W (fun _ hx => hx.1) (fun _ hx => hx.2) T₀ hTA hpW
    nz1 nz2 H hH hy hyH

/-- **The narrowed residual** (levels `s + 1` only): `LowerExpResidual` without its level-`0` case (r0), which is proved
(`lowerExpResidual_of_succ`).  At the levels `s + 1` only the case (r1) is left: the exponent of the lower ideal of `A` along
`H` at `y` is below the mark and the `ℰ`-term is divisible by `𝓘_H` along one of the two carriers near `y`.  Not a named input:
an explicit hypothesis (lane G11B's plan: (r1) from the directrix (T), lanes G8B/G8C). -/
def LowerExpResidualSucc (A B : MarkedIdeal n X) : Prop :=
  ∀ {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀), IsGeoTestTower (barMarked A) T₀ →
    ∀ (s : ℕ) (y₀ : Y₀), y₀ ∈ (geoTransformAlong (barMarked A) T₀).cosupp → stepRegime A (s + 1) T₀ y₀ →
    ∀ (O : Opens Y₀), O ≤ maskBM A (s + 1) T₀ y₀ → O ≤ maskBM B (s + 1) T₀ y₀ → ∀ (r r' : ℕ),
      IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A (s + 1) T₀ y₀)) →
      IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B (s + 1) T₀ y₀)) →
      ∀ y ∈ O, ∀ H ∈ (lowerIdealBM A (s + 1) T₀ y₀).E, y ∈ (lowerIdealBM A (s + 1) T₀ y₀).cosupp → y ∈ H →
        ¬ IsDivNearAlong n (lowerIdealBM A (s + 1) T₀ y₀).N (lowerIdealBM A (s + 1) T₀ y₀).ideal H
          (lowerIdealBM A (s + 1) T₀ y₀).d y →
        (IsDivNearAlong n (lowerIdealBM A (s + 1) T₀ y₀).N
            (exceptionalTermBM (throughMembers A T₀ y₀) (coeffEmptyBM A).d) H 1 y ∨
          IsDivNearAlong n (lowerIdealBM B (s + 1) T₀ y₀).N
            (exceptionalTermBM (throughMembers A T₀ y₀) (coeffEmptyBM A).d) H 1 y) →
        divExpAlong n (lowerIdealBM A (s + 1) T₀ y₀).N (lowerIdealBM A (s + 1) T₀ y₀).ideal H y =
          divExpAlong n (lowerIdealBM B (s + 1) T₀ y₀).N (lowerIdealBM B (s + 1) T₀ y₀).ideal H y

/-- **The residual from the narrowed residual and the pointwise (O<)**: the level-`0` case (r0) of `LowerExpResidual` holds
(`expAgreeBelowAt_lowerIdealBM_zero`: below the mark the truncated agreement is equality). -/
theorem lowerExpResidual_of_succ
    (hO : ∀ {Z : CMfd.{0} n} (P' Q' : MarkedIdeal n Z), LocWPEquiv P' Q' → IsClosedSubmanifold n P'.N →
      IsClosedSubmanifold n Q'.N → P'.ideal.IsCoherent → Q'.ideal.IsCoherent → IsSNCDivisor n P'.E → 1 ≤ P'.d →
      Q'.d = P'.d → SameCarrierDim P' Q' → ∀ x ∈ P'.cosupp, IsNonzeroAlongAt P'.N P'.ideal x →
        IsNonzeroAlongAt Q'.N Q'.ideal x → OrdAgreeBelowAt P' Q' x)
    (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d) (h : LocWPEquiv A B)
    (hd : A.d = B.d) (hE : A.E = B.E) (hdim : SameCarrierDim A B) (hres : LowerExpResidualSucc A B) :
    LowerExpResidual A B := by
  intro Y₀ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB y hyO H hH hy hyH hbelow h0 hs
  cases s with
  | zero =>
    have hagree := expAgreeBelowAt_lowerIdealBM_zero hO hn hA hB hmA hmB h hd hE hdim T₀ hT₀ hy₀ O hOA hOB hdA hdB hyO
      H hH hy hyH
    have hcL := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ 0
    have hlt : divExpAlong n (lowerIdealBM A 0 T₀ y₀).N (lowerIdealBM A 0 T₀ y₀).ideal H y <
        (lowerIdealBM A 0 T₀ y₀).d := by
      by_contra hge
      push Not at hge
      exact hbelow ((isDivNearAlong_divExpAlong (hol_of_isCoherent hcL) y).mono hge)
    omega
  | succ s =>
    exact hres T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB y hyO H hH hy hyH hbelow (hs (Nat.succ_pos s))

/-- **The narrowed residual at level `k`** (`R`-free). -/
def LowerExpResidualSuccStepBM (n k : ℕ) : Prop :=
  ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
    IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
    A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerExpResidualSucc A B

/-- **G11's residual input from the narrowed residual and the pointwise (O<)**:
`LowerExpResidualSuccStepBM n k → HironakaG8ClassStepBridge.LowerExpResidualStepBM n k`. -/
theorem lowerExpResidualStepBM_of_succ
    (hO : ∀ {Z : CMfd.{0} n} (P' Q' : MarkedIdeal n Z), LocWPEquiv P' Q' → IsClosedSubmanifold n P'.N →
      IsClosedSubmanifold n Q'.N → P'.ideal.IsCoherent → Q'.ideal.IsCoherent → IsSNCDivisor n P'.E → 1 ≤ P'.d →
      Q'.d = P'.d → SameCarrierDim P' Q' → ∀ x ∈ P'.cosupp, IsNonzeroAlongAt P'.N P'.ideal x →
        IsNonzeroAlongAt Q'.N Q'.ideal x → OrdAgreeBelowAt P' Q' x)
    (hn : 0 < n) {k : ℕ} (h : LowerExpResidualSuccStepBM n k) : HironakaG8ClassStepBridge.LowerExpResidualStepBM n k :=
  fun A B hA hB hmA hmB hAB hd hE hdim h0 =>
    lowerExpResidual_of_succ hO hn hA hB hmA hmB hAB hd hE hdim (h A B hA hB hmA hmB hAB hd hE hdim h0)

end Residual

end

end Hironaka.HironakaG8ClassStepHistory
