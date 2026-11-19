import Hironaka.Resolution.HironakaG11InvBMMaskStep
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestrictionTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's lower family for the Step 1 skeleton (repair (B'), plan module 3)

Blueprint: `hironaka-g11-inv-bm-lower.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (module 3, design
decision D5) and `REPORT-r3.md` §5 item 1 (the definition).  Source: Bierstone--Milman 2008 (`references/bierstone-milman08-
functoriality`), §5 Step I, Cases A and B, and §7.2 Step I (read per point, "the values of the invariants at `x` equal their
values in year `q_k`").

Let `𝔍 = (X, N, E, 𝔞, d)` be a marked ideal (of maximal order in the intended use) and `𝔍_∅ = (X, N, ∅, 𝔞, d)` the same marked
ideal with the divisor forgotten.  At a point `y₀` of the stage `T₀` with base point `x₀ = T₀.proj y₀`, let
`w = (tangentChoice 𝔍 x₀).2` be the tangent direction chosen at `x₀` (a hypersurface of maximal contact `P = N ∩ V(w)` near
`x₀`, Bierstone--Milman's Corollary 4.1).  Bierstone--Milman's Case A coefficient ideal is
`𝒞_U(𝔍_∅) = (U, P, ∅, 𝒞_∅^{d-1}(𝔍_∅)|_P, d_𝒞)`; in Case B they use its TRANSFORMS `𝒞_{q_k}` at the start `q_k` of each phase,
plus the term `ℰ = ∏_{Λ ∈ Sub(E, s)} Σ_{H ∈ Λ} 𝓘_H^{d_𝒞}` built from the original members.  Here (per point):

* `emptyBoundary 𝔍 = 𝔍_∅`; `coeffEmptyBM 𝔍 = 𝓒_N(𝔍_∅)` (the standard coefficient ideal along `N`; with empty divisor the
  standard and logarithmic derivatives agree);
* **`contactCoeffBM 𝔍 w T₀`** `= (𝓒_N(𝔍_∅)_{T₀})|_{(N ∩ V(w))_{T₀}}`: the transform of the coefficient ideal along `T₀`,
  restricted to the strict transform of the hypersurface of maximal contact.  Along towers whose centres lie in the strict
  transforms of `P`, this is restricted-equivalent to the transform of `𝒞_U(𝔍_∅) = 𝓒_N(𝔍_∅)|_P` ("restriction commutes with
  controlled transforms along centres inside `P`": `CoefficientIdealAlongRestrictionTower.restrict_tower_along`, Włodarczyk's
  `le:cf`), i.e. it is Bierstone--Milman's `𝒞_{q_k}`; `contactCoeffBM_refl`: at the empty tower it is `𝓒_N(𝔍_∅)|_P`;
* `throughMembers 𝔍 T₀ y₀`: the original members (strict transforms of the members of `E`) through `y₀`;
  **`exceptionalTermBM S e`** `= Σ_{H ∈ S} 𝓘_H^e`;
* **`lowerIdealBM 𝔍 s T₀ y₀`**: `contactCoeffBM 𝔍 w T₀` at level `0`; at the levels `s + 1` the same carrier, divisor and mark,
  with ideal `𝒞 + ℰ_S`, `S` the original members through `y₀` (on the mask `maskBM 𝔍 (s+1) T₀ y₀` the original members
  missing `y₀` are absent, so Bierstone--Milman's product over `Λ ∈ Sub(E, s+1)` reduces to the factor `Λ = S`; for marked
  ideals of the same mark their sum is the sum of the ideals, Bierstone--Milman's Lemma 3.8);
* **`lowerBM 𝔍 : LowerFamilyG 𝔍 (maskBM 𝔍)`**: the pullbacks of `lowerIdealBM` to the masks `maskBM`;
* **`stepOneInvBM R 𝔍 = stepOneInvG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍)`**, the Step 1 value with Bierstone--Milman's lower family;
* the data of the lower marked ideals: `N`, `E` (the members born along `T₀`, restricted), `d` (`d_𝒞`), and the ideals.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMLower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HomogenizedIdealAlong Hironaka.CoefficientIdealRestriction
  Hironaka.IdealWeightPowers Hironaka.MarkedIdealBiholomorphism
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

/-! ### The ingredients -/

section Defs

variable {X : CMfd.{u} n}

/-- **The marked ideal with the divisor forgotten**: `𝔍_∅ = (X, N, ∅, 𝔞, d)` (Bierstone--Milman's `I_∅`). -/
def emptyBoundary (𝔍 : MarkedIdeal n X) : MarkedIdeal n X where
  N := 𝔍.N
  E := []
  ideal := 𝔍.ideal
  d := 𝔍.d

@[simp] theorem emptyBoundary_N (𝔍 : MarkedIdeal n X) : (emptyBoundary 𝔍).N = 𝔍.N := rfl
@[simp] theorem emptyBoundary_E (𝔍 : MarkedIdeal n X) : (emptyBoundary 𝔍).E = [] := rfl
@[simp] theorem emptyBoundary_ideal (𝔍 : MarkedIdeal n X) : (emptyBoundary 𝔍).ideal = 𝔍.ideal := rfl
@[simp] theorem emptyBoundary_d (𝔍 : MarkedIdeal n X) : (emptyBoundary 𝔍).d = 𝔍.d := rfl

/-- **The coefficient ideal of `𝔍_∅` along `N`**: `𝓒_N(𝔍_∅) = Σ_{i < d} (𝓓_N^i 𝔞, d - i)` with empty divisor. -/
def coeffEmptyBM (𝔍 : MarkedIdeal n X) : MarkedIdeal n X :=
  coeffMarkedAlong (emptyBoundary 𝔍)

@[simp] theorem coeffEmptyBM_N (𝔍 : MarkedIdeal n X) : (coeffEmptyBM 𝔍).N = 𝔍.N := rfl
@[simp] theorem coeffEmptyBM_E (𝔍 : MarkedIdeal n X) : (coeffEmptyBM 𝔍).E = [] := rfl

/-- **Bierstone--Milman's coefficient ideal on maximal contact, at the stage `T₀`**: the transform along `T₀` of the
coefficient ideal of `𝔍_∅`, restricted to the strict transform of the hypersurface `N ∩ V(w)`. -/
def contactCoeffBM (𝔍 : MarkedIdeal n X) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) : MarkedIdeal n Y₀ :=
  withN (geoTransformAlong (coeffEmptyBM 𝔍) T₀) (strictAlong T₀ (𝔍.N ∩ {x | w x = 0}))

@[simp] theorem contactCoeffBM_N (𝔍 : MarkedIdeal n X) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    (contactCoeffBM 𝔍 w T₀).N = strictAlong T₀ (𝔍.N ∩ {x | w x = 0}) := rfl

theorem contactCoeffBM_E (𝔍 : MarkedIdeal n X) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    (contactCoeffBM 𝔍 w T₀).E = (geoTransformAlong (coeffEmptyBM 𝔍) T₀).E := rfl

@[simp] theorem contactCoeffBM_d (𝔍 : MarkedIdeal n X) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    (contactCoeffBM 𝔍 w T₀).d = (coeffEmptyBM 𝔍).d := by
  rw [contactCoeffBM, withN_d, d_geoTransformAlong]

theorem contactCoeffBM_ideal (𝔍 : MarkedIdeal n X) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    (contactCoeffBM 𝔍 w T₀).ideal = (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal := rfl

/-- **At the empty tower**, `contactCoeffBM` is Bierstone--Milman's Case A coefficient ideal `𝓒_N(𝔍_∅)|_{N ∩ V(w)}`. -/
theorem contactCoeffBM_refl (𝔍 : MarkedIdeal n X) (w : X → ℂ) :
    contactCoeffBM 𝔍 w (BlowupTower.refl : BlowupTower X X) = withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | w x = 0}) := rfl

/-- **The divisor of `contactCoeffBM`: the members born along `T₀`** (one per blowup), the divisor of `𝔍_∅` being empty. -/
theorem length_E_contactCoeffBM (𝔍 : MarkedIdeal n X) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    (contactCoeffBM 𝔍 w T₀).E.length = T₀.length := by
  rw [contactCoeffBM_E, length_E_geoTransformAlong, coeffEmptyBM_E, List.length_nil, zero_add]

open Classical in
/-- **The original members through `y₀`** at the stage `T₀`. -/
def throughMembers (𝔍 : MarkedIdeal n X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) : List (Set Y₀) :=
  (origMembers 𝔍 T₀).filter fun H => decide (y₀ ∈ H)

theorem mem_throughMembers {𝔍 : MarkedIdeal n X} {Y₀ : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {y₀ : Y₀} {H : Set Y₀} :
    H ∈ throughMembers 𝔍 T₀ y₀ ↔ H ∈ origMembers 𝔍 T₀ ∧ y₀ ∈ H := by
  classical
  simp [throughMembers]

/-- **Bierstone--Milman's `ℰ`-term for the members `S`, mark `e`**: `Σ_{H ∈ S} 𝓘_H^e`. -/
def exceptionalTermBM {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] (S : List (Set M)) (e : ℕ) :
    GermIdeal n M :=
  finSumIdeal (fun i => idealPow (vanishingIdeal (n := n) (S.getD i ∅)) e) S.length

/-- **The lower ideal of Bierstone--Milman's family** at level `s` around `y₀`, on all of the stage `T₀`: the coefficient ideal
on maximal contact at level `0`; at the levels `s + 1` its sum with the `ℰ`-term of the original members through `y₀`
(same carrier, divisor and mark). -/
def lowerIdealBM (𝔍 : MarkedIdeal n X) (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    MarkedIdeal n Y₀ :=
  match s with
  | 0 => contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀
  | _ + 1 =>
    { N := (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).N
      E := (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).E
      ideal := sumIdeal (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).ideal
        (exceptionalTermBM (throughMembers 𝔍 T₀ y₀) (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).d)
      d := (contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀).d }

/-- **Bierstone--Milman's lower family**: the lower ideals, restricted to Bierstone--Milman's masks. -/
def lowerBM (𝔍 : MarkedIdeal n X) : LowerFamilyG 𝔍 (maskBM 𝔍) := fun s _ T₀ y₀ =>
  MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 s T₀ y₀ → _) (lowerIdealBM 𝔍 s T₀ y₀)

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The Step 1 value with Bierstone--Milman's lower family** (repair (B')). -/
abbrev stepOneInvBM (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (y : Y) : ℕ ×ₗ WithTop Λ :=
  stepOneInvG R 𝔍 (maskBM 𝔍) (lowerBM 𝔍) T y

end Defs

/-! ### The data of the lower ideals -/

section Data

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀)

theorem lowerIdealBM_zero : lowerIdealBM 𝔍 0 T₀ y₀ = contactCoeffBM 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀ := rfl

theorem lowerIdealBM_N (s : ℕ) :
    (lowerIdealBM 𝔍 s T₀ y₀).N = strictAlong T₀ (𝔍.N ∩ {x | (tangentChoice 𝔍 (T₀.proj y₀)).2 x = 0}) := by
  cases s <;> rfl

theorem lowerIdealBM_E (s : ℕ) :
    (lowerIdealBM 𝔍 s T₀ y₀).E = (geoTransformAlong (coeffEmptyBM 𝔍) T₀).E := by
  cases s <;> rfl

theorem lowerIdealBM_d (s : ℕ) : (lowerIdealBM 𝔍 s T₀ y₀).d = (coeffEmptyBM 𝔍).d := by
  cases s
  · exact contactCoeffBM_d 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀
  · exact contactCoeffBM_d 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀

theorem lowerIdealBM_succ_ideal (s : ℕ) :
    (lowerIdealBM 𝔍 (s + 1) T₀ y₀).ideal = sumIdeal (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal
      (exceptionalTermBM (throughMembers 𝔍 T₀ y₀) (coeffEmptyBM 𝔍).d) := by
  show sumIdeal _ (exceptionalTermBM _ (contactCoeffBM 𝔍 _ T₀).d) = _
  rw [contactCoeffBM_d]
  rfl

theorem lowerBM_eq (s : ℕ) :
    lowerBM 𝔍 s T₀ y₀ = MarkedIdeal.pullback (Subtype.val : maskBM 𝔍 s T₀ y₀ → Y₀) (lowerIdealBM 𝔍 s T₀ y₀) := rfl

theorem lowerBM_N (s : ℕ) :
    (lowerBM 𝔍 s T₀ y₀).N = (Subtype.val : maskBM 𝔍 s T₀ y₀ → Y₀) ⁻¹'
      strictAlong T₀ (𝔍.N ∩ {x | (tangentChoice 𝔍 (T₀.proj y₀)).2 x = 0}) := by
  show (Subtype.val : maskBM 𝔍 s T₀ y₀ → Y₀) ⁻¹' (lowerIdealBM 𝔍 s T₀ y₀).N = _
  rw [lowerIdealBM_N]

theorem lowerBM_E (s : ℕ) :
    (lowerBM 𝔍 s T₀ y₀).E = (geoTransformAlong (coeffEmptyBM 𝔍) T₀).E.map
      ((Subtype.val : maskBM 𝔍 s T₀ y₀ → Y₀) ⁻¹' ·) := by
  show (lowerIdealBM 𝔍 s T₀ y₀).E.map _ = _
  rw [lowerIdealBM_E]

theorem lowerBM_d (s : ℕ) : (lowerBM 𝔍 s T₀ y₀).d = (coeffEmptyBM 𝔍).d :=
  lowerIdealBM_d 𝔍 T₀ y₀ s

/-- The divisor of the lower ideals has one member for each blowup of `T₀` (all born members; none original). -/
theorem length_E_lowerBM (s : ℕ) : (lowerBM 𝔍 s T₀ y₀).E.length = T₀.length := by
  rw [lowerBM_E, List.length_map, length_E_geoTransformAlong, coeffEmptyBM_E, List.length_nil, zero_add]

/-- **The mark of the lower ideals**: the mark `d_𝒞 = d (d - 1) ⋯ 1` of the coefficient ideal of `𝔍_∅`. -/
theorem coeffEmptyBM_d : (coeffEmptyBM 𝔍).d = (Finset.range 𝔍.d).prod fun j => 𝔍.d - j :=
  rfl

end Data

end

end Hironaka.HironakaG11InvBMLower
