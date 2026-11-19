import Hironaka.Resolution.HironakaG11InvBMRepresentative
import Hironaka.Resolution.HironakaG11InvBMEmptyMember
import Hironaka.Invariant.StepOneEmptyPrefix

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Bierstone--Milman's lower ideals across an empty prefix (repair (B'), plan module 8, property (4'), part 1)

Blueprint: `hironaka-g11-pres-m8-empty-prefix.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c, and lane
G11B's release of property (4') to lane G11C (inbox I-1368, comment C-0002).  Source: Włodarczyk 2005 (arXiv `hiron.tex`), the
definition of extensions (isomorphisms inserted into a resolution); Bierstone--Milman 2008, §5 Step I (the lower ideals are
transforms of the coefficient ideal on a hypersurface of maximal contact, the divisor being the members born along the tower).

Let `P` be a tower with only empty centres and `𝔍_P` the transform of `𝔍` along it.  Bierstone--Milman's lower ideal of `𝔍`
formed at the stage `P H₀` with a tangent direction `u` (on `U`) and the lower ideal of `𝔍_P` formed at `H₀` with `u ∘ p_P`
have, over every open set `O` of the stage over `U`, the same carrier, mark and (up to restricted equivalence) ideal, and their
divisors differ by the `|P|` EMPTY members born along `P` (in front).

* `E_geoTransformAlong_split`: the divisor of a transform is the strict transform of the divisor followed by the members born
  along the tower (those of the transform of `(M, N, ∅, 𝔞, d)`);
* `restrictEquiv_coeffEmpty_geoTransformAlong_of_isEmptyTower`: `𝓒_N((𝔍_∅)_P) ≃ 𝓒_N(𝔍_∅)_P` for `P` empty;
* `lowF` (the lower ideal formed from a transform `G`, a carrier `A` and members `S`), `lowerIdealWBM_eq_lowF`;
* **`restrictEquiv_lowerIdealWBM_emptyPrefix`** (both levels): `{L₃ with E := L₁.E} ≃ L₁` and `L₁.E = Z ++ L₃.E` with `Z` empty
  members, for `L₁`, `L₃` the two lower ideals restricted to `O`;
* `isInvDomain_withE_of_sublist`: the domain passes to a sublist of the divisor;
* **`lowerValueG_emptyPrefix_of`** (both levels): if the lower ideal of `𝔍` at `P H₀` with any tangent direction `u`, restricted
  to an open `O` over `U`, lies in the domain of `R` with `T₁|_O` a canonical segment, then the lower value of `𝔍_P` at the split
  `(H₀, T₁)` is the value of `R` for it -- given the independence of the hypersurface of maximal contact for `𝔍_P`
  (`TangentIndepBM`) and the independence of empty members of the divisor (`EmptyMemberIndep`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11PresM8EmptyCore

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneValueMasked Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.BlowupTowerIsomorphism
  Hironaka.BlowupTowerIsoTail Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMCanonicalTail Hironaka.HironakaG11InvBMAdmissible
  Hironaka.HironakaG11InvBMTangentIndep Hironaka.HironakaG11InvBMNaturality
  Hironaka.HironakaG11InvBMEmptyMember
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.CoefficientIdealRestriction (withN)
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_step N_geoTransformAlong)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv hol_of_isCoherent)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant IsEmptyTower
  isGeoTestTower_of_isEmptyTower isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The divisor of a transform -/

section Divisor

variable {X : CMfd.{u} n}

/-- **The divisor of a transform**: the strict transforms of the members followed by the members born along the tower, which
are those of the transform of the marked ideal with empty divisor. -/
theorem E_geoTransformAlong_split (𝔪 : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong 𝔪 T).E =
        𝔪.E.map (strictAlong T) ++ (geoTransformAlong ({ 𝔪 with E := [] } : MarkedIdeal n X) T).E
  | _, .refl => by
      show 𝔪.E = 𝔪.E.map (strictAlong (BlowupTower.refl : BlowupTower X X)) ++ []
      rw [List.append_nil]
      exact (List.map_id' _).symm
  | _, .step T C π hπ => by
      rw [geoTransformAlong_step, geoTransformAlong_step, geoTransform_E, geoTransform_E,
        E_geoTransformAlong_split 𝔪 T, List.map_append, List.map_map, List.append_assoc]
      congr 1

/-- **The coefficient ideal of `𝔍_∅` across a tower with only empty centres**: `𝓒_N((𝔍_∅)_P) ≃ 𝓒_N(𝔍_∅)_P`. -/
theorem restrictEquiv_coeffEmpty_geoTransformAlong_of_isEmptyTower (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) :
    ∀ {Y : CMfd.{u} n} (P : BlowupTower X Y), IsEmptyTower P →
      RestrictEquiv (coeffMarkedAlong (geoTransformAlong (emptyBoundary 𝔍) P))
        (geoTransformAlong (coeffEmptyBM 𝔍) P)
  | _, .refl, _ => RestrictEquiv.refl (HironakaG11InvBMStage.isWellFormed_coeffEmptyBM h𝔍).isCoherent
  | _, .step P C π hπ, hP => by
      obtain ⟨hP, hC⟩ : IsEmptyTower P ∧ C = ∅ := hP
      subst hC
      have hB := HironakaG11InvBMStage.isWellFormed_emptyBoundary h𝔍
      have hPt : IsGeoTestTower (emptyBoundary 𝔍) P := isGeoTestTower_of_isEmptyTower _ P hP
      obtain ⟨hNP, hcP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hB.isClosedSubmanifold_N hB.isCoherent
        P hPt
      have hdP : 1 ≤ (geoTransformAlong (emptyBoundary 𝔍) P).d := by rw [d_geoTransformAlong]; exact hd
      have h1 := ContactCanonicalAlong.restrictEquiv_coeffMarkedAlong_geoTransform_empty
        (geoTransformAlong (emptyBoundary 𝔍) P) hNP hcP hdP hπ
      have ih := restrictEquiv_coeffEmpty_geoTransformAlong_of_isEmptyTower 𝔍 h𝔍 hd P hP
      have hA := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM h𝔍
      have hAP : IsGeoTestTower (coeffEmptyBM 𝔍) P := isGeoTestTower_of_isEmptyTower _ P hP
      obtain ⟨-, hcAP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hA.isClosedSubmanifold_N hA.isCoherent
        P hAP
      have hcC : (coeffMarkedAlong (geoTransformAlong (emptyBoundary 𝔍) P)).ideal.IsCoherent :=
        isCoherent_coeffMarkedAlong hcP hNP
      have heq := ih.geoTransform_eq hNP.1 hcC hcAP (C := ∅) hπ.contMDiff
      show RestrictEquiv (coeffMarkedAlong ((geoTransformAlong (emptyBoundary 𝔍) P).geoTransform ∅ π))
        ((geoTransformAlong (coeffEmptyBM 𝔍) P).geoTransform ∅ π)
      rw [← heq]
      exact h1

/-- **Restricted equivalence along a tower** (from the first blowup on the transforms are equal). -/
theorem restrictEquiv_geoTransformAlong {𝔪 𝔫 : MarkedIdeal n X} (h : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), (geoTransformAlong 𝔫 T).ideal.IsCoherent →
      RestrictEquiv (geoTransformAlong 𝔪 T) (geoTransformAlong 𝔫 T)
  | _, .refl, _ => h
  | _, .step T C π hπ, hc => by
      rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq h hN h𝔪 h𝔫 T C π hπ]
      exact RestrictEquiv.refl hc

end Divisor

/-! ### The lower ideals as functions of the transform, the carrier and the members -/

section LowF

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The lower ideal formed from a transformed coefficient ideal `G`, a carrier `A` and members `S`**: `G` with carrier `A`
at level `0`, its same-mark sum with the `ℰ`-term of `S` at the levels `s + 1`. -/
def lowF (s : ℕ) (G : MarkedIdeal n M) (A : Set M) (S : List (Set M)) : MarkedIdeal n M :=
  match s with
  | 0 => withN G A
  | _ + 1 => withExcBM (withN G A) S

theorem lowF_N (s : ℕ) (G : MarkedIdeal n M) (A : Set M) (S : List (Set M)) : (lowF s G A S).N = A := by
  cases s <;> rfl

theorem lowF_E (s : ℕ) (G : MarkedIdeal n M) (A : Set M) (S : List (Set M)) : (lowF s G A S).E = G.E := by
  cases s <;> rfl

theorem lowF_d (s : ℕ) (G : MarkedIdeal n M) (A : Set M) (S : List (Set M)) : (lowF s G A S).d = G.d := by
  cases s <;> rfl

theorem lowF_ideal_carrier (s : ℕ) (G : MarkedIdeal n M) (A A' : Set M) (S : List (Set M)) :
    (lowF s G A S).ideal = (lowF s G A' S).ideal := by
  cases s <;> rfl

theorem lowF_ideal_congr (s : ℕ) {G G' : MarkedIdeal n M} (hI : G.ideal = G'.ideal) (hd : G.d = G'.d) (A : Set M)
    (S : List (Set M)) : (lowF s G A S).ideal = (lowF s G' A S).ideal := by
  cases s with
  | zero => exact hI
  | succ s =>
    show sumIdeal G.ideal (exceptionalTermBM S G.d) = sumIdeal G'.ideal (exceptionalTermBM S G'.d)
    rw [hI, hd]

theorem isCoherent_lowF (s : ℕ) {G : MarkedIdeal n M} (hG : G.ideal.IsCoherent) (A : Set M) {S : List (Set M)}
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) : (lowF s G A S).ideal.IsCoherent := by
  cases s with
  | zero => exact hG
  | succ s =>
    exact RestrictedIdealExtension.isCoherent_sumIdeal hG
      (HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM hS _)

theorem restrictEquiv_lowF (s : ℕ) {G G' : MarkedIdeal n M} (h : RestrictEquiv G G') {A : Set M} (hA : A ⊆ G.N)
    (hG : G.ideal.IsCoherent) (hG' : G'.ideal.IsCoherent) {S : List (Set M)} (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    RestrictEquiv (lowF s G A S) (lowF s G' A S) := by
  have h0 := ContactCanonicalAlong.restrictEquiv_withN h hA
  cases s with
  | zero => exact h0
  | succ s => exact HironakaG11InvBMRepresentative.RestrictEquiv.withExcBM h0 hG hG' hS

end LowF

theorem lowerIdealWBM_eq_lowF {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (s : ℕ) (w : X → ℂ) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (S : List (Set Y₀)) :
    lowerIdealWBM 𝔍 s w T₀ S =
      lowF s (geoTransformAlong (coeffEmptyBM 𝔍) T₀) (strictAlong T₀ (𝔍.N ∩ {x | w x = 0})) S := by
  cases s <;> rfl

/-! ### The core comparison -/

section Core

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **Bierstone--Milman's lower ideals across an empty prefix** (both levels): for `P` with only empty centres, `P H₀` a
multiple test blow-up of `J̄`, a tangent direction `u` of `(𝔍.ideal|_N, d)` on the open `U`, an open `O` of the stage over `U` and
members `S` (closed submanifolds), let `L₁` be the lower ideal of `𝔍` at `P H₀` with `u` and `L₃` the one of `𝔍_P` at `H₀` with
`u ∘ p_P`, both restricted to `O`.  Then `L₃` with the divisor of `L₁` is restricted-equivalent to `L₁`, and the divisor of `L₁`
is that of `L₃` preceded by empty members. -/
theorem restrictEquiv_lowerIdealWBM_emptyPrefix (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) {Y₁ Y₀ : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) (H₀ : BlowupTower Y₁ Y₀)
    (hT : IsGeoTestTower (barMarked 𝔍) (P.append H₀)) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (O : Opens Y₀)
    (hO : (O : Set Y₀) ⊆ (P.append H₀).proj ⁻¹' (U : Set X)) (s : ℕ) (S : List (Set Y₀))
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    RestrictEquiv
      ({ MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S) with
          E := (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s u (P.append H₀) S)).E } :
        MarkedIdeal n O)
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s u (P.append H₀) S)) ∧
    ∃ Z : List (Set O), (∀ H ∈ Z, H = ∅) ∧
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s u (P.append H₀) S)).E =
        Z ++ (MarkedIdeal.pullback (Subtype.val : O → Y₀)
          (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S)).E := by
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  have hwfP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔍 P hPt
  have hdP : 1 ≤ (geoTransformAlong 𝔍 P).d := by rw [d_geoTransformAlong]; exact hd
  have hT₀ : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 P)) H₀ :=
    (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd P
      hP H₀).mpr hT
  -- the transformed coefficient ideals
  set C := coeffMarkedAlong (geoTransformAlong (emptyBoundary 𝔍) P) with hCdef
  set AP := geoTransformAlong (coeffEmptyBM 𝔍) P with hAPdef
  have hCA : RestrictEquiv C AP := restrictEquiv_coeffEmpty_geoTransformAlong_of_isEmptyTower 𝔍 h𝔍 hd P hP
  have hB := HironakaG11InvBMStage.isWellFormed_emptyBoundary h𝔍
  obtain ⟨hNBP, hcBP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hB.isClosedSubmanifold_N hB.isCoherent
    P (isGeoTestTower_of_isEmptyTower _ P hP)
  have hcC : C.ideal.IsCoherent := isCoherent_coeffMarkedAlong hcBP hNBP
  have hA := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM h𝔍
  obtain ⟨-, hcAP⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hA.isClosedSubmanifold_N hA.isCoherent
    P (isGeoTestTower_of_isEmptyTower _ P hP)
  have hBC : coeffEmptyBM (geoTransformAlong 𝔍 P) = ({ C with E := [] } : MarkedIdeal n Y₁) := by
    show coeffMarkedAlong (emptyBoundary (geoTransformAlong 𝔍 P)) =
      ({ coeffMarkedAlong (geoTransformAlong (emptyBoundary 𝔍) P) with E := [] } : MarkedIdeal n Y₁)
    rw [HironakaG11InvBMStage.geoTransformAlong_emptyBoundary]
    rfl
  -- coherence of the two transforms at the stage
  have hcG₁ : (geoTransformAlong AP H₀).ideal.IsCoherent := by
    rw [hAPdef, ← geoTransformAlong_append]
    exact isCoherent_contactCoeffBM 𝔍 h𝔍 hd u (P.append H₀) hT
  have hcG₃ : (geoTransformAlong (coeffEmptyBM (geoTransformAlong 𝔍 P)) H₀).ideal.IsCoherent :=
    isCoherent_contactCoeffBM (geoTransformAlong 𝔍 P) hwfP hdP (u ∘ P.proj) H₀ hT₀
  obtain ⟨hGN, hGI, hGd⟩ := DropMembers.geoTransformAlong_withE C [] H₀
  rw [← hBC] at hGN hGI hGd
  have hcGC : (geoTransformAlong C H₀).ideal.IsCoherent := hGI ▸ hcG₃
  have hG : RestrictEquiv (geoTransformAlong C H₀) (geoTransformAlong AP H₀) :=
    restrictEquiv_geoTransformAlong hCA hNBP.1 hcC hcAP H₀ hcG₁
  -- the carriers over `O`
  set S₁ : Set Y₀ := strictAlong (P.append H₀) (𝔍.N ∩ {x | u x = 0}) with hS₁def
  set S₃ : Set Y₀ := strictAlong H₀ ((geoTransformAlong 𝔍 P).N ∩ {y | (u ∘ P.proj) y = 0}) with hS₃def
  have hAO : (geoTransformAlong 𝔍 P).N ∩ {y | (u ∘ P.proj) y = 0} ∩ P.proj ⁻¹' (U : Set X) =
      strictAlong P (𝔍.N ∩ {x | u x = 0}) ∩ P.proj ⁻¹' (U : Set X) := by
    rw [(ContactEmptyPrefix.isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower 𝔍 h𝔍.isClosedSubmanifold_N
      h𝔍.isCoherent hu P hP).2, ContactEmptyPrefix.strictAlong_inter_zero_of_isEmptyTower 𝔍
      h𝔍.isClosedSubmanifold_N.1 h𝔍.isCoherent hu P hP]
  have hloc := ContactEquivalenceStage.strictAlong_inter_preimage_eq
    ((U.isOpen).preimage P.contMDiff_proj.continuous) hAO H₀
  have hset : (Subtype.val : O → Y₀) ⁻¹' S₃ = (Subtype.val : O → Y₀) ⁻¹' S₁ := by
    rw [hS₁def, MemberInterLocusAlong.strictAlong_append]
    ext p
    have hp : (p : Y₀) ∈ H₀.proj ⁻¹' (P.proj ⁻¹' (U : Set X)) := by
      have h := hO p.2
      rw [mem_preimage, BlowupTower.proj_append] at h
      exact h
    constructor
    · intro h
      have h1 : (p : Y₀) ∈ S₃ ∩ H₀.proj ⁻¹' (P.proj ⁻¹' (U : Set X)) := ⟨h, hp⟩
      rw [hS₃def, hloc] at h1
      exact h1.1
    · intro h
      have h1 : (p : Y₀) ∈ strictAlong H₀ (strictAlong P (𝔍.N ∩ {x | u x = 0})) ∩
          H₀.proj ⁻¹' (P.proj ⁻¹' (U : Set X)) := ⟨h, hp⟩
      rw [← hloc] at h1
      exact h1.1
  have hCN : C.N = (geoTransformAlong 𝔍 P).N := by
    show (geoTransformAlong (emptyBoundary 𝔍) P).N = (geoTransformAlong 𝔍 P).N
    rw [N_geoTransformAlong, N_geoTransformAlong]
    rfl
  have hS₃N : S₃ ⊆ (geoTransformAlong C H₀).N := by
    rw [N_geoTransformAlong, hCN]
    exact MemberInterTowerAlong.strictAlong_mono H₀ (fun x hx => hx.1)
  -- the comparison at the stage, then on `O`
  have hR := restrictEquiv_lowF s hG hS₃N hcGC hcG₁ hS
  have hRp := ContactRepresentative.restrictEquiv_pullback_val O hR (isCoherent_lowF s hcGC _ hS)
    (isCoherent_lowF s hcG₁ _ hS)
  have e₁ : MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s u (P.append H₀) S) =
      MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowF s (geoTransformAlong AP H₀) S₃ S) := by
    rw [lowerIdealWBM_eq_lowF, geoTransformAlong_append]
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_
    · show (Subtype.val : O → Y₀) ⁻¹' (lowF s (geoTransformAlong AP H₀) S₁ S).N =
        (Subtype.val : O → Y₀) ⁻¹' (lowF s (geoTransformAlong AP H₀) S₃ S).N
      rw [lowF_N, lowF_N, hset]
    · show (lowF s (geoTransformAlong AP H₀) S₁ S).E.map ((Subtype.val : O → Y₀) ⁻¹' ·) =
        (lowF s (geoTransformAlong AP H₀) S₃ S).E.map ((Subtype.val : O → Y₀) ⁻¹' ·)
      rw [lowF_E, lowF_E]
    · show GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (lowF s (geoTransformAlong AP H₀) S₁ S).ideal =
        GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (lowF s (geoTransformAlong AP H₀) S₃ S).ideal
      rw [lowF_ideal_carrier s _ S₁ S₃]
    · show (lowF s (geoTransformAlong AP H₀) S₁ S).d = (lowF s (geoTransformAlong AP H₀) S₃ S).d
      rw [lowF_d, lowF_d]
  have e₃ : ({ MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S) with
          E := (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s u (P.append H₀) S)).E } :
        MarkedIdeal n O) =
      MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowF s (geoTransformAlong C H₀) S₃ S) := by
    rw [e₁]
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ ?_
    · show (Subtype.val : O → Y₀) ⁻¹' (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S).N =
        (Subtype.val : O → Y₀) ⁻¹' (lowF s (geoTransformAlong C H₀) S₃ S).N
      rw [lowerIdealWBM_eq_lowF, lowF_N, lowF_N]
    · show (lowF s (geoTransformAlong AP H₀) S₃ S).E.map ((Subtype.val : O → Y₀) ⁻¹' ·) =
        (lowF s (geoTransformAlong C H₀) S₃ S).E.map ((Subtype.val : O → Y₀) ⁻¹' ·)
      rw [lowF_E, lowF_E, hG.E_eq]
    · show GermIdeal.pullback (m := n) (Subtype.val : O → Y₀)
          (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S).ideal =
        GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (lowF s (geoTransformAlong C H₀) S₃ S).ideal
      rw [lowerIdealWBM_eq_lowF, lowF_ideal_congr s hGI hGd]
    · show (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S).d =
        (lowF s (geoTransformAlong C H₀) S₃ S).d
      rw [lowerIdealWBM_eq_lowF, lowF_d, lowF_d, hGd]
  refine ⟨?_, ?_⟩
  · rw [e₃, e₁]
    exact hRp
  · -- the divisors
    refine ⟨((C.E.map (strictAlong H₀)).map ((Subtype.val : O → Y₀) ⁻¹' ·)), ?_, ?_⟩
    · intro H hH
      obtain ⟨H₁, hH₁, rfl⟩ := List.mem_map.mp hH
      obtain ⟨H₂, hH₂, rfl⟩ := List.mem_map.mp hH₁
      have h0 : H₂ = ∅ := StepOneEmptyPrefix.drop_E_geoTransformAlong_of_isEmptyTower (emptyBoundary 𝔍) P hP H₂
        (by rw [show (emptyBoundary 𝔍).E.length = 0 from rfl, List.drop_zero]; exact hH₂)
      rw [h0, StepOneEmptyPrefix.strictAlong_empty, preimage_empty]
    · rw [e₁]
      show (lowF s (geoTransformAlong AP H₀) S₃ S).E.map ((Subtype.val : O → Y₀) ⁻¹' ·) =
        (C.E.map (strictAlong H₀)).map ((Subtype.val : O → Y₀) ⁻¹' ·) ++
          (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ S).E.map ((Subtype.val : O → Y₀) ⁻¹' ·)
      rw [lowF_E, ← hG.E_eq, E_geoTransformAlong_split C H₀, ← hBC, lowerIdealWBM_eq_lowF, lowF_E, List.map_append]

end Core

/-! ### The domain passes to a sublist of the divisor -/

theorem isInvDomain_withE_of_sublist {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {k : ℕ} {𝔪 : MarkedIdeal n M} (h : IsInvDomain k 𝔪) {E' : List (Set M)}
    (hE : E'.Sublist 𝔪.E) : IsInvDomain k ({ 𝔪 with E := E' } : MarkedIdeal n M) :=
  ⟨NormalCrossingsComparison.isWellFormed_withE h.isWellFormed hE, h.dimLE, h.one_le_d, h.isNonzeroAlongAt⟩

/-! ### The lower value of `𝔍_P` through a lower ideal of `𝔍` -/

section Value

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **The original members through a point agree across an empty prefix** (the extra members are empty). -/
theorem throughMembers_emptyPrefix {Y₁ Y₀ : CMfd.{u} n} (P : BlowupTower X Y₁) (hP : IsEmptyTower P)
    (H₀ : BlowupTower Y₁ Y₀) (a : Y₀) :
    throughMembers (geoTransformAlong 𝔍 P) H₀ a = throughMembers 𝔍 (P.append H₀) a := by
  obtain ⟨L, hL, hE⟩ := StepOneEmptyPrefix.origMembers_emptyPrefix 𝔍 P hP H₀
  have h0 : ∀ H ∈ L, a ∉ H := fun H hH haH => by
    rw [hL H hH] at haH
    exact haH
  unfold throughMembers
  rw [hE, List.filter_append]
  exact List.append_right_eq_self.mpr (List.filter_eq_nil_iff.mpr fun H hH => by simpa using h0 H hH)

/-- **The lower value of `𝔍_P` through a lower ideal of `𝔍`** (both levels; `P` with only empty centres): let `P H₀ T₁` be a
multiple test blow-up of `J̄`, `z` a point with lower data for `𝔍_P` at level `s` at the split `(H₀, T₁)`, whose image `a` at
`P H₀` lies in `cosupp J̄_{P H₀}` with level `s`, `u` a tangent direction of `(𝔍.ideal|_N, d)` on the open `U`, and `O ∋ a` an
open set of the stage over `U` on which the lower ideal of `𝔍` formed at `P H₀` with `u` (and the original members through `a`)
lies in the domain of `R` with `T₁|_O` a canonical segment, `z` in the cosupport.  Given the independence of the hypersurface
of maximal contact for `𝔍_P` and of empty members of the divisor, the lower value of `𝔍_P` at `z` is the value of `R` for that
lower ideal along `T₁|_O`. -/
theorem lowerValueG_emptyPrefix_of (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n) {Y₁ Y₀ Z : CMfd.{u} n}
    (P : BlowupTower X Y₁) (hP : IsEmptyTower P) (hTIP : TangentIndepBM (geoTransformAlong 𝔍 P) R)
    (hEI : EmptyMemberIndep (k - 1) R.inv) (H₀ : BlowupTower Y₁ Y₀) (T₁ : BlowupTower Y₀ Z)
    (hT : IsGeoTestTower (barMarked 𝔍) ((P.append H₀).append T₁)) {s : ℕ} {z : Z}
    (ha : T₁.proj z ∈ (geoTransformAlong (barMarked 𝔍) (P.append H₀)).cosupp)
    (hl : level 𝔍 (P.append H₀) (T₁.proj z) = s)
    (hD' : LowerDataG R (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P)) (lowerBM (geoTransformAlong 𝔍 P)) s
      H₀ T₁ z)
    (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) (O : Opens Y₀)
    (hO : (O : Set Y₀) ⊆ (P.append H₀).proj ⁻¹' (U : Set X)) (hzO : T₁.proj z ∈ O)
    (hdom : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))))
    (hcan : IsCanonical (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z))))
      (R.inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z))))) (restrict O T₁))
    (hcos : (⟨z, hzO⟩ : openPreimage T₁ O) ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))) (restrict O T₁)).cosupp) :
    lowerValueG R (geoTransformAlong 𝔍 P) (maskBM (geoTransformAlong 𝔍 P)) (lowerBM (geoTransformAlong 𝔍 P)) s H₀ T₁ z =
      ((R.inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))) (restrict O T₁) ⟨z, hzO⟩ :
          Λ) : WithTop Λ) := by
  have hPt : IsGeoTestTower 𝔍 P := isGeoTestTower_of_isEmptyTower 𝔍 P hP
  have hwfP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔍 P hPt
  have hdP : 1 ≤ (geoTransformAlong 𝔍 P).d := by rw [d_geoTransformAlong]; exact hd
  obtain ⟨hT₀J, -⟩ := (isGeoTestTower_append_iff _ (P.append H₀) T₁).mp hT
  have hT₀ : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 P)) H₀ :=
    (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd P
      hP H₀).mpr hT₀J
  have hT' : IsGeoTestTower (barMarked (geoTransformAlong 𝔍 P)) (H₀.append T₁) :=
    (ContactEmptyPrefix.isGeoTestTower_barMarked_geoTransformAlong_iff 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd P
      hP _).mpr (by rw [← BlowupTower.append_assoc]; exact hT)
  have ha' : T₁.proj z ∈ (geoTransformAlong (barMarked (geoTransformAlong 𝔍 P)) H₀).cosupp := by
    rw [(StepOneEmptyPrefix.restrictEquiv_barMarked_append 𝔍 h𝔍 hd P hP H₀ hT₀J).cosupp_eq]
    exact ha
  have hl' : level (geoTransformAlong 𝔍 P) H₀ (T₁.proj z) = s := by
    rw [StepOneEmptyPrefix.level_emptyPrefix 𝔍 P hP H₀]
    exact hl
  -- the comparison of the lower ideals on `O`
  have hthr := throughMembers_emptyPrefix 𝔍 P hP H₀ (T₁.proj z)
  have hS := HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers 𝔍 h𝔍 hn (P.append H₀) hT₀J
    (T₁.proj z)
  obtain ⟨hRE, Zs, hZ, hE⟩ := restrictEquiv_lowerIdealWBM_emptyPrefix 𝔍 h𝔍 hd P hP H₀ hT₀J U hu O hO s _ hS
  have hcoh₃ : (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀
      (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))).ideal.IsCoherent := by
    have h := isCoherent_lowerIdealWBM (geoTransformAlong 𝔍 P) hwfP hdP hn s (u ∘ P.proj) H₀ hT₀ (T₁.proj z)
    rw [hthr] at h
    exact GermIdealPullbackCalculus.isCoherent_pullback (contMDiff_subtype_val (U := O)) h
  have hE₁₂ := InvDomainRebase.restrictEquiv_symm hRE
  have hdom₂ := InvDomainRebase.isInvDomain_of_restrictEquiv hdom hE₁₂ hcoh₃
  have hcan₂ := InvDomainRebase.isCanonical_of_restrictEquiv R hdom hdom₂ hE₁₂ _ hcan
  have v₁ := R.representative _ _ hdom hdom₂ hE₁₂ _ hcan ⟨z, hzO⟩ hcos
  have hcos₂ := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hE₁₂
    hdom.isWellFormed.isClosedSubmanifold_N.1 hdom.isWellFormed.isCoherent hcoh₃ (restrict O T₁)).1 ▸ hcos
  have hdom₃ : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))) := by
    refine isInvDomain_withE_of_sublist hdom₂ ?_
    dsimp only
    rw [hE]
    exact List.sublist_append_right _ _
  have hsame : SameUpToEmptyMembers (X := CMfd.of (n := n) O)
      ({ MarkedIdeal.pullback (Subtype.val : O → Y₀)
          (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z))) with
        E := (MarkedIdeal.pullback (Subtype.val : O → Y₀)
          (lowerIdealWBM 𝔍 s u (P.append H₀) (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))).E } :
        MarkedIdeal n (CMfd.of (n := n) O))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀ (throughMembers 𝔍 (P.append H₀) (T₁.proj z)))) := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    dsimp only
    rw [hE, List.filter_append, List.filter_eq_nil_iff.mpr (fun H hH => by simp [hZ H hH]), List.nil_append]
  obtain ⟨hcan₃, hv⟩ := hEI (X := CMfd.of (n := n) O) _ _ hdom₂ hdom₃ hsame (restrict O T₁) hcan₂
  have v₂ := hv ⟨z, hzO⟩ hcos₂
  -- the anchor for `𝔍_P` with the tangent direction `u ∘ p_P`
  have hu' : IsTangentDirectionAlong (geoTransformAlong 𝔍 P).N (geoTransformAlong 𝔍 P).ideal (geoTransformAlong 𝔍 P).d
      (P.proj ⁻¹' (U : Set X)) (u ∘ P.proj) := by
    rw [d_geoTransformAlong]
    exact (ContactEmptyPrefix.isTangentDirectionAlong_geoTransformAlong_of_isEmptyTower 𝔍 h𝔍.isClosedSubmanifold_N
      h𝔍.isCoherent hu P hP).1
  have hOU : (O : Set Y₀) ⊆ H₀.proj ⁻¹' (P.proj ⁻¹' (U : Set X)) := fun p hp => by
    have h := hO hp
    rw [mem_preimage, BlowupTower.proj_append] at h
    exact h
  have hdom₃' : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀
        (throughMembers (geoTransformAlong 𝔍 P) H₀ (T₁.proj z)))) := by
    rw [hthr]
    exact hdom₃
  have hcan₃' : IsCanonical (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀
        (throughMembers (geoTransformAlong 𝔍 P) H₀ (T₁.proj z))))
      (R.inv (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM (geoTransformAlong 𝔍 P) s (u ∘ P.proj) H₀
          (throughMembers (geoTransformAlong 𝔍 P) H₀ (T₁.proj z))))) (restrict O T₁) := by
    rw [hthr]
    exact hcan₃
  have key := lowerValueG_eq_of_tangent (geoTransformAlong 𝔍 P) R hTIP H₀ T₁ hT' ha' hl' hD' hu' O hOU hzO hdom₃'
    hcan₃'
  rw [key]
  congr 1
  rw [hthr]
  exact (v₁.trans v₂).symm

end Value


end

end Hironaka.HironakaG11PresM8EmptyCore
