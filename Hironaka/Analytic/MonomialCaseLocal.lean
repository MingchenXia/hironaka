import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Hironaka.Invariant.NonmonomialOrderZero
import Hironaka.Resolution.HironakaLocalPrincipalization

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolution of monomial marked ideals: compact cosupport, level sets on open sets

Blueprint `hir:monomial-case-local` (`blueprint/src/hironaka.tex`; TN.5, option (c) of I-1199: the design node
`hir:monomial-case` formalized as stated, with its item (1) corrected).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`),
the monomial case of Proposition `pr:resol`; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`); Bierstone--Milman
2003 (`bierstone-milman03-desingularization-algorithms`), Theorem 1.14.

`hir:monomial-case` states, for a well-formed monomial marked ideal `(M, N, E, 𝔞, d)` with `d ≥ 1` and its invariant `γ`:
(1) `γ` is upper semicontinuous on the cosupport, and on every open set on which `γ ≤ λ` the locus `{γ = λ}` is
`N ∩ ⋂_{H ∈ λ₃} H`, an admissible centre; (2) the drop after blowing up the maximum locus; (3) if the cosupport is compact,
the iterated blowup of the maximum locus reaches an empty cosupport; (4) invariance.  Items (2) and (4) and the compact-base
form of (3) were proved (`MonomialStepAlong`, `MonomialInvariantFunctorialAlong`).  New here:

* (3) for a **compact cosupport** in a manifold that need not be compact: the resolution driver of
  `ResolutionDriver.exists_isGeoResolution_of_wellFounded_invariant` with compact cosupports in place of a compact base
  (`exists_isGeoResolution_of_wellFounded_invariant_of_isCompact`); the cosupports along a multiple test blow-up stay compact
  because they lie over the original cosupport and tower projections are proper
  (`HironakaLocalPrincipalization.isProperMap_proj`);
* (1) **on an open set**: if `γ ≤ v` on the part of the cosupport over an open `W`, the points of the cosupport over `W` with
  `γ = v` form an admissible centre of `𝔪|_W` (`isAdmissibleCentre_gammaAlong_level`), and near each of its points the locus
  is `N ∩ ⋂_{i ∈ top(v)} E_i` (`MonomialCaseAlong.eventually_gammaAlong_eq_iff_mem_memberInter`).

The second half of (1), read globally on the open set, is false when members are disconnected (the exponent of a member is
only locally constant): for `M = N = ℂ²`, `H₁ = {z₁ = 0} ⊔ {z₁ = 1}`, `H₂ = {z₂ = 0}`, `𝔞 = (z₁² (z₁ - 1) z₂²)`, `d = 3`,
`γ ≤ γ(0, 0)` everywhere, but `(1, 0) ∈ H₁ ∩ H₂` has `γ₂(1, 0) = 3 < 4 = γ₂(0, 0)`.  The corrected statement is local, as
the proof of `hir:monomial-case` (1) is.

## Main results

* `isCompact_cosupp_geoTransformAlong`: along a multiple test blow-up the cosupport stays compact;
* `exists_isGeoResolution_of_wellFounded_invariant_of_isCompact`: the well-founded driver with compact cosupports;
* **`exists_isGeoResolution_of_monomialAlong_of_isCompact`**, `exists_isGeoResolution_of_monomial_of_isCompact`;
* `isMonomialAlong_pullback_val_of_isMonomialAlong`, `isNonzeroAlongAt_pullback_val`: restriction to open sets;
* **`isAdmissibleCentre_gammaAlong_level`**: item (1) on an open set.

Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.MonomialCaseLocal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong
  Hironaka.MonomialPartEtale Hironaka.GermIdealOrder
  Hironaka.DivisorExponentAlong Hironaka.BlowupTowers
  Hironaka.DerivativeIdealAlongEtale Hironaka.MonomialInvariant
  Hironaka.MonomialCaseAlong Hironaka.MonomialStepAlong
  Hironaka.MarkedIdealRestrictOpen Hironaka.RestrictedIdealWeight
open Hironaka.ResolutionDriver (maxLocus IsCanonicalSegment)
open Hironaka.ResolutionInvariantOrder (IsInvUSCOn)

noncomputable section

variable {n : ℕ}

/-! ### Compact cosupports along towers -/

section Compact

variable {X : CMfd.{u} n}

/-- **Along a multiple test blow-up the cosupport stays compact** (closed submanifold `N`, coherent ideal): it is closed and
lies over the original cosupport, whose preimage under the proper projection is compact. -/
theorem isCompact_cosupp_geoTransformAlong {𝔪 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hK : IsCompact 𝔪.cosupp) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) : IsCompact (geoTransformAlong 𝔪 T).cosupp := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T hT
  exact ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    (GiraudAlong.isClosed_cosupport_along hcT hNT _)
    (TransformOffCentre.cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T hT)

variable {Λ : Type v} [LinearOrder Λ]

/-- **The canonical resolution exists, by a well-founded drop, for compact cosupports** (the driver
`ResolutionDriver.exists_isGeoResolution_of_wellFounded_invariant` with compact cosupports along canonical segments in place
of a compact base): with values in a well-founded order, if along canonical segments the cosupports are compact, the
invariant is upper semicontinuous, its maximum locus is an admissible centre with empty interior, and after blowing up the
maximum locus the invariant at every point of the new cosupport is below the old maximum, then some canonical segment is a
resolution. -/
theorem exists_isGeoResolution_of_wellFounded_invariant_of_isCompact [WellFoundedLT Λ] (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)
    (hcpt : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      IsCompact (geoTransformAlong 𝔪 T).cosupp)
    (husc : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      IsInvUSCOn (inv T) (geoTransformAlong 𝔪 T).cosupp)
    (hadm : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty →
      (geoTransformAlong 𝔪 T).IsAdmissibleCentre (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) ∧
        interior (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) = ∅)
    (hdec : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      ∀ x₀ ∈ maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp,
      ∀ {Z : CMfd.{u} n} (π : Z → Y)
        (hπ : IsBlowupAlong n (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π),
      ∀ z ∈ (geoTransformAlong 𝔪
          (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ)).cosupp,
        inv (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ) z < inv T x₀) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T ∧ IsGeoResolution 𝔪 T := by
  have hmaxne : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T → IsGeoTestTower 𝔪 T →
      (geoTransformAlong 𝔪 T).cosupp.Nonempty → (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp).Nonempty := by
    intro Y T hPT hT hne
    obtain ⟨x, hx, hmax⟩ := (husc T hPT hT).exists_isMaxOn (hcpt T hPT hT) hne
    exact ⟨x, hx, hmax⟩
  -- strong induction on a bound `l` for the values on the cosupport
  suffices h : ∀ l : Λ, ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonicalSegment 𝔪 inv T →
      IsGeoTestTower 𝔪 T → (∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, inv T y ≤ l) →
      ∃ (Y' : CMfd.{u} n) (T' : BlowupTower X Y'), IsCanonicalSegment 𝔪 inv T' ∧ IsGeoResolution 𝔪 T' by
    by_cases hne : (geoTransformAlong 𝔪 (BlowupTower.refl : BlowupTower X X)).cosupp.Nonempty
    · obtain ⟨x₀, -, hmax⟩ := hmaxne (BlowupTower.refl : BlowupTower X X) trivial trivial hne
      exact h _ BlowupTower.refl trivial trivial fun y hy => hmax y hy
    · exact ⟨X, BlowupTower.refl, trivial, trivial, not_nonempty_iff_eq_empty.mp hne⟩
  intro l
  induction l using WellFoundedLT.induction with
  | _ l ih =>
  intro Y T hPT hT hl
  by_cases hne : (geoTransformAlong 𝔪 T).cosupp.Nonempty
  · obtain ⟨hC, hint⟩ := hadm T hPT hT hne
    obtain ⟨x₀, hx₀⟩ := hmaxne T hPT hT hne
    obtain ⟨Z, π, hπ⟩ := ResolutionDriver.exists_blowup _ hC.1 hint
    have hPT' : IsCanonicalSegment 𝔪 inv
        (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ) := ⟨hPT, ⟨x₀, hx₀⟩, rfl⟩
    have hT' : IsGeoTestTower 𝔪 (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ) :=
      (isGeoTestTower_step_iff 𝔪 T _ π hπ).mpr ⟨hT, hC⟩
    by_cases hne' : (geoTransformAlong 𝔪
        (BlowupTower.step T (maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) π hπ)).cosupp.Nonempty
    · obtain ⟨z₀, hz₀, hzmax⟩ := hmaxne _ hPT' hT' hne'
      have hlt := (hdec T hPT hT x₀ hx₀ π hπ z₀ hz₀).trans_le (hl x₀ hx₀.1)
      exact ih _ hlt _ hPT' hT' hzmax
    · exact ⟨_, _, hPT', hT', not_nonempty_iff_eq_empty.mp hne'⟩
  · exact ⟨Y, T, hPT, hT, not_nonempty_iff_eq_empty.mp hne⟩

end Compact

/-! ### Item (3): compact cosupport -/

section Resolution

variable {X : CMfd.{u} n}

/-- **Resolution of monomial marked ideals along a submanifold, compact cosupport** (`hir:monomial-case` (3), as stated):
for a well-formed marked ideal `(X, N, E, 𝔞, d)` with `d ≥ 1`, nonzero and monomial along `N`, whose cosupport is compact
(`X` need not be), iterating the blowup of the maximum locus of `γ` reaches an empty cosupport: some canonical segment of
`γ` is a resolution. -/
theorem exists_isGeoResolution_of_monomialAlong_of_isCompact (hn : 0 < n) (𝔪 : MarkedIdeal n X)
    (h𝔪 : 𝔪.IsWellFormed) (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y)
    (hmono : IsMonomialAlong n 𝔪.N 𝔪.ideal 𝔪.E) (hd : 1 ≤ 𝔪.d) (hK : IsCompact 𝔪.cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonicalSegment 𝔪 (fun {Y} T => towerInvAlong 𝔪 (Y := Y) T) T ∧ IsGeoResolution 𝔪 T := by
  have := wellFoundedLT_val
  refine exists_isGeoResolution_of_wellFounded_invariant_of_isCompact 𝔪
    (fun {Y} T => towerInvAlong 𝔪 (Y := Y) T) ?_ ?_ ?_ ?_
  · intro Y T _ hT
    exact isCompact_cosupp_geoTransformAlong h𝔪.isClosedSubmanifold_N h𝔪.isCoherent hK T hT
  · intro Y T hseg hT
    obtain ⟨hwf, hneT, -⟩ := invariants_canonicalSegment_along hn 𝔪 h𝔪 hne hmono T hseg hT
    exact isInvUSCOn_gammaAlong hn hwf.isClosedSubmanifold_N hwf.isSNCDivisor hwf.isTransverse hwf.isCoherent hneT
      (geoTransformAlong 𝔪 T).cosupp_subset_N
  · intro Y T hseg hT _
    obtain ⟨hwf, hneT, hmonoT⟩ := invariants_canonicalSegment_along hn 𝔪 h𝔪 hne hmono T hseg hT
    obtain ⟨hC, hint⟩ := isAdmissibleCentre_maxLocus_gammaAlong hn hwf.isClosedSubmanifold_N hwf.isSNCDivisor
      hwf.isTransverse hwf.isCoherent hneT (geoTransformAlong 𝔪 T) rfl rfl rfl hmonoT
    exact ⟨hC, hint (by rw [d_geoTransformAlong]; exact hd)⟩
  · intro Y T hseg hT x₀ hx₀ Z π hπ z hz
    obtain ⟨hwf, hneT, hmonoT⟩ := invariants_canonicalSegment_along hn 𝔪 h𝔪 hne hmono T hseg hT
    obtain ⟨-, -, -, -, -, hlt⟩ := monomial_step_along hn hwf hneT hmonoT hπ
    exact hlt x₀ hx₀ z hz

/-- **Resolution of monomial marked ideals, `N = M`, compact cosupport** (`hir:monomial-case` (3) for `N = M`, as
stated): for a well-formed marked ideal `(X, X, E, 𝔞, d)` with `d ≥ 1`, monomial and nonzero at every point, whose cosupport
is compact, some canonical segment of `γ` is a resolution. -/
theorem exists_isGeoResolution_of_monomial_of_isCompact (hn : 0 < n) (𝔪 : MarkedIdeal n X)
    (h𝔪 : 𝔪.IsWellFormed) (hN : 𝔪.N = univ) (h0 : ∀ y, DivisorExponent.IsNonzeroAt 𝔪.ideal y)
    (hmono : (MonomialPart.monomialPart n 𝔪.ideal 𝔪.E).Le 𝔪.ideal) (hd : 1 ≤ 𝔪.d) (hK : IsCompact 𝔪.cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonicalSegment 𝔪 (fun {Y} T => MonomialResolution.towerInv 𝔪 (Y := Y) T) T ∧ IsGeoResolution 𝔪 T := by
  have := wellFoundedLT_val
  refine exists_isGeoResolution_of_wellFounded_invariant_of_isCompact 𝔪
    (fun {Y} T => MonomialResolution.towerInv 𝔪 (Y := Y) T) ?_ ?_ ?_ ?_
  · intro Y T _ hT
    exact isCompact_cosupp_geoTransformAlong h𝔪.isClosedSubmanifold_N h𝔪.isCoherent hK T hT
  · intro Y T hseg hT
    obtain ⟨hwf, -, h0T, -⟩ := MonomialResolution.invariants_canonicalSegment hn 𝔪 h𝔪 hN h0 hmono T hseg hT
    exact MonomialCase.isInvUSCOn_gamma hn hwf.isSNCDivisor hwf.isCoherent h0T _ _
  · intro Y T hseg hT _
    obtain ⟨hwf, hNT, h0T, hmonoT⟩ := MonomialResolution.invariants_canonicalSegment hn 𝔪 h𝔪 hN h0 hmono T hseg hT
    obtain ⟨hC, hint⟩ := MonomialCase.isAdmissibleCentre_maxLocus_gamma hn (geoTransformAlong 𝔪 T) hNT
      hwf.isSNCDivisor hwf.isCoherent h0T hmonoT
    exact ⟨hC, hint (by rw [d_geoTransformAlong]; exact hd)⟩
  · intro Y T hseg hT x₀ hx₀ Z π hπ z hz
    obtain ⟨hwf, hNT, h0T, hmonoT⟩ := MonomialResolution.invariants_canonicalSegment hn 𝔪 h𝔪 hN h0 hmono T hseg hT
    obtain ⟨-, -, -, -, -, -, hlt⟩ := MonomialResolution.monomial_step hn (geoTransformAlong 𝔪 T) hwf hNT h0T hmonoT hπ
    exact hlt x₀ hx₀ z hz

end Resolution

/-! ### Item (1) on an open set -/

section Level

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A marked ideal monomial along `N` restricts to one monomial along `N ∩ W`** (coherent ideal, `W` open). -/
theorem isMonomialAlong_pullback_val_of_isMonomialAlong {𝔪 : MarkedIdeal n M} (h𝔞 : 𝔪.ideal.IsCoherent)
    (hmono : IsMonomialAlong n 𝔪.N 𝔪.ideal 𝔪.E) (W : Opens M) :
    IsMonomialAlong n (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N
      (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).E := by
  have hloc : ∀ y : W, ∃ ψ : M → W, IsLocalInverseAt n (Subtype.val : W → M) ψ y :=
    fun y => ⟨openInv W y, isLocalInverseAt_val W y⟩
  have hle : RestrictLe (𝔪.N ∩ (W : Set M)) (monomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E) 𝔪.ideal :=
    fun y hy g hg => CodimOneCentreAlong.isInSpanOnAt_subset inter_subset_left (hmono y hy.1 g hg)
  have h1 := RestrictLeCalculus.restrictLe_pullback (f := (Subtype.val : W → M)) contMDiff_subtype_val
    (V := 𝔪.N ∩ (W : Set M)) (W := (Subtype.val : W → M) ⁻¹' 𝔪.N) (fun y hy => ⟨hy, y.2⟩) h𝔞 hle
  unfold IsMonomialAlong
  show RestrictLe ((Subtype.val : W → M) ⁻¹' 𝔪.N)
    (monomialPartAlong n ((Subtype.val : W → M) ⁻¹' 𝔪.N) (GermIdeal.pullback (m := n) (Subtype.val : W → M) 𝔪.ideal)
      (𝔪.E.map ((Subtype.val : W → M) ⁻¹' ·))) (GermIdeal.pullback (m := n) (Subtype.val : W → M) 𝔪.ideal)
  rw [← pullback_monomialPartAlong hloc
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)]
  exact h1

/-- **Nonvanishing along `N` restricts to open sets.** -/
theorem isNonzeroAlongAt_pullback_val {𝔪 : MarkedIdeal n M} (h𝔞 : 𝔪.ideal.IsCoherent)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (W : Opens M) :
    ∀ p ∈ (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N,
      IsNonzeroAlongAt (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N
        (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).ideal p := fun p hp => by
  obtain ⟨g, hg, hfreq⟩ := hne (p : M) hp
  refine ⟨g ∘ Subtype.val, comp_val_mem_pullback_val W h𝔞 hg, ?_⟩
  rw [← W.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq p] at hfreq
  exact Filter.frequently_map.mp hfreq

/-- **Item (1) of `hir:monomial-case` on an open set** (the admissible half, corrected): for a well-formed marked ideal
`(M, N, E, 𝔞, d)` nonzero and monomial along `N` (`n > 0`) and an open `W` on which `γ ≤ v` at the points of the cosupport,
the points of the cosupport over `W` with `γ = v` form an admissible centre of `𝔪|_W`.  (Near each of its points this locus is
`N ∩ ⋂_{i ∈ top(v)} E_i`: `MonomialCaseAlong.eventually_gammaAlong_eq_iff_mem_memberInter`.) -/
theorem isAdmissibleCentre_gammaAlong_level (hn : 0 < n) {𝔪 : MarkedIdeal n M} (h𝔪 : 𝔪.IsWellFormed)
    (hne : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y) (hmono : IsMonomialAlong n 𝔪.N 𝔪.ideal 𝔪.E) (W : Opens M)
    (v : WithBot Val) (hv : ∀ y ∈ 𝔪.cosupp, y ∈ W → gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E 𝔪.d y ≤ v) :
    (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).IsAdmissibleCentre
      ((Subtype.val : W → M) ⁻¹' {y | y ∈ 𝔪.cosupp ∧ gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E 𝔪.d y = v}) := by
  have h𝔞 := h𝔪.isCoherent
  have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hwfV := IsWellFormed.pullback_val h𝔪 W
  have hneV := isNonzeroAlongAt_pullback_val h𝔞 hne W
  have hmonoV := isMonomialAlong_pullback_val_of_isMonomialAlong h𝔞 hmono W
  have hcosV := cosupp_pullback_val 𝔪 hhol W
  have hγ : ∀ q : W,
      gammaAlong n (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N
          (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).E
          (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).d q =
        gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E 𝔪.d q.1 :=
    fun q => MonomialInvariantFunctorialAlong.gammaAlong_pullback_val 𝔪 hhol W q 𝔪.d
  have hbot : ∀ q : W, q ∈ (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N →
      (gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E 𝔪.d q.1 = ⊥ ↔ q.1 ∉ 𝔪.cosupp) := by
    intro q hq
    rw [← hγ q, gammaAlong_eq_bot_iff_of_isMonomialAlong hn hwfV.isClosedSubmanifold_N hwfV.isSNCDivisor
      hwfV.isTransverse hwfV.isCoherent hneV hmonoV _ hq]
    show q ∉ (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).cosupp ↔ _
    rw [hcosV]
    rfl
  cases v with
  | bot =>
    have hemp : (Subtype.val : W → M) ⁻¹' {y | y ∈ 𝔪.cosupp ∧ gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E 𝔪.d y = ⊥} = ∅ := by
      ext q
      simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hq hγq
      have hqN : q ∈ (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N := 𝔪.cosupp_subset_N hq
      exact (hbot q hqN).mp hγq hq
    rw [hemp]
    exact isAdmissibleCentre_empty _
  | coe w =>
    have hmax : ∀ q ∈ (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N,
        gammaAlong n (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N
          (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).E
          (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).d q ≤ (w : WithBot Val) := by
      intro q hqN
      rw [hγ q]
      by_cases hq : q.1 ∈ 𝔪.cosupp
      · exact hv q.1 hq q.2
      · rw [(hbot q hqN).mpr hq]
        exact bot_le
    have hadm := isAdmissibleCentre_gammaAlong_eq hn hwfV.isClosedSubmanifold_N hwfV.isSNCDivisor
      hwfV.isTransverse hwfV.isCoherent hneV (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪) rfl rfl
      rfl rfl hmonoV hmax
    have hset : {q | q ∈ (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N ∧
        gammaAlong n (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).N
          (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).ideal (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).E
          (MarkedIdeal.pullback (Subtype.val : W → M) 𝔪).d q = (w : WithBot Val)} =
        (Subtype.val : W → M) ⁻¹' {y | y ∈ 𝔪.cosupp ∧ gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E 𝔪.d y = w} := by
      ext q
      simp only [mem_preimage, mem_ofPred_eq, hγ q]
      constructor
      · rintro ⟨hqN, hγq⟩
        refine ⟨?_, hγq⟩
        by_contra hq
        rw [(hbot q hqN).mpr hq] at hγq
        exact WithBot.bot_ne_coe hγq
      · rintro ⟨hq, hγq⟩
        exact ⟨𝔪.cosupp_subset_N hq, hγq⟩
    rw [← hset]
    exact hadm

end Level

end

end Hironaka.MonomialCaseLocal
