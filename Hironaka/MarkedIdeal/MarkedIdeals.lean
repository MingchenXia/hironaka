import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Blowup.NormalCrossings
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.Blowup.BlowupStrictSubmanifold

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Marked ideals, admissible blowups, transforms and multiple test blowups

Blueprint `hir:marked-ideal`, `hir:admissible`, `hir:transform`, `hir:test-tower`
(`blueprint/src/hironaka.tex`, Hironaka phase H1/H2 interface).  Sources: Bierstone--Milman 2008,
Definitions 2.1--2.2 (marked ideal `(M, N, E, 𝓘, d)`, cosupport, admissible blowing-up, transform)
and Theorem 1.3; Włodarczyk 2005 §2.1--2.2 (marked ideals `(X, 𝓘, E, μ)`, resolutions, multiple test
blow-ups, controlled transforms).

## Encoding

* `N` is a SUBSET of the ambient manifold (a closed submanifold for well-formed data), never a
  separate manifold type: the ambient spaces of a tower are the only types.
* The ideal of `𝒪_N` is represented by an ambient `GermIdeal` (`ideal`); only the restrictions of its
  germs to `N` matter (`GermIdealOrder.VanishesToOrderOn`).  For `N = M` this is Włodarczyk's
  `(X, 𝓘, E, μ)`.
* `E` is a list of subsets; the transform appends the exceptional divisor `π⁻¹ C` as the LAST
  member (BM08: "introduced as the last member of `E'`"; Włodarczyk: "`D_i` is the maximal element").
* Strict transforms are taken relative to the centre, `closure (π⁻¹ (A \ C))`
  (`BlowupStrictSubmanifold.geoStrictTransform`), for `N` and for the members of `E` (the author's
  decision): along a centre of codimension one the blowup is a biholomorphism, and the
  strict transform `closure (π⁻¹ A \ Exc π)` would keep `A ∩ C`.  The transform is therefore the same as
  `MarkedIdealGeoTransform.geoTransform`.
* The transform of the ideal is the ambient form of `𝓘' = 𝓘_{π⁻¹C}^{-d} π^*𝓘` on `N'`: the colon,
  along the strict transform `N'`, of `π^*𝓘` by `(π^* 𝓘_C)^d`
  (`RestrictedIdealQuotient.colonAlong`, the restricted quotient already used in Copy-4 Step 1).
* All data are raw (no proof fields); well-formedness (`IsWellFormed`) and admissibility are separate
  predicates, so transforms are total functions and the bookkeeping lemmas below are definitional.

## Main declarations

* `MarkedIdeal n M`, `cosupp`, `IsWellFormed`, `IsAdmissibleCentre`, `transform`;
* along a tower `T : BlowupTower X Y` (`Hironaka.BlowupTowers`): `transformAlong`, `IsTestTower` (Włodarczyk's "multiple test
  blow-up", BM08's sequence of admissible blowings-up), `IsResolution` (empty final cosupport);
* bookkeeping: `transformAlong_append`, `isTestTower_append_iff`, `IsResolution.append`,
  `isResolution_refl_iff`, `d_transformAlong`, `length_E_transformAlong`, `N_transformAlong_step`,
  `isTestTower_step_iff`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`, so that those two statements can
later be proved in place from it.

Sorry-free.  No statement about the EXISTENCE of resolutions is made here (by the author's decision, no
new named input).
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.MarkedIdeals

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.NormalCrossings
open Hironaka.BlowupTowers Hironaka.IdealWeightPowers
open Hironaka.RestrictedIdealQuotient
open Hironaka.BlowupStrictSubmanifold

noncomputable section

/-- **A marked ideal** `(M, N, E, 𝓘, d)` on the ambient manifold `M` (BM08 Definitions 2.1): the
submanifold `N ⊆ M`, the ordered divisor `E = [H₁, …, H_s]`, an ambient representative `ideal` of the
ideal `𝓘 ⊆ 𝒪_N`, and the mark `d`. -/
structure MarkedIdeal (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] where
  /-- The submanifold carrying the ideal. -/
  N : Set M
  /-- The ordered normal crossings divisor (newest member last). -/
  E : List (Set M)
  /-- An ambient representative of the ideal of `𝒪_N`. -/
  ideal : GermIdeal n M
  /-- The mark. -/
  d : ℕ

namespace MarkedIdeal

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **The cosupport** `{x ∈ N | ord_x 𝓘 ≥ d}`. -/
def cosupp (𝔪 : MarkedIdeal n M) : Set M :=
  cosupport n 𝔪.N 𝔪.ideal 𝔪.d

theorem cosupp_subset_N (𝔪 : MarkedIdeal n M) : 𝔪.cosupp ⊆ 𝔪.N :=
  cosupport_subset _

variable [IsComplexManifold n M]

/-- **Well-formed marked ideal** (BM08 Definitions 2.1): `N` a closed submanifold, the ideal coherent,
`E` an ordered simple normal crossings divisor transverse to `N`. -/
structure IsWellFormed (𝔪 : MarkedIdeal n M) : Prop where
  isClosedSubmanifold_N : IsClosedSubmanifold n 𝔪.N
  isCoherent : 𝔪.ideal.IsCoherent
  isSNCDivisor : IsSNCDivisor n 𝔪.E
  isTransverse : IsTransverse n 𝔪.N 𝔪.E

/-- **An admissible centre** (BM08 Definitions 2.2; Włodarczyk §2.1 conditions (1)--(2)): a closed
submanifold contained in the cosupport and having only normal crossings with `E`. -/
def IsAdmissibleCentre (𝔪 : MarkedIdeal n M) (C : Set M) : Prop :=
  IsClosedSubmanifold n C ∧ C ⊆ 𝔪.cosupp ∧ HasNormalCrossings n C 𝔪.E

theorem IsAdmissibleCentre.subset_N {𝔪 : MarkedIdeal n M} {C : Set M}
    (h : 𝔪.IsAdmissibleCentre C) : C ⊆ 𝔪.N :=
  h.2.1.trans 𝔪.cosupp_subset_N

/-- The empty centre is admissible. -/
theorem isAdmissibleCentre_empty (𝔪 : MarkedIdeal n M) : 𝔪.IsAdmissibleCentre ∅ :=
  ⟨⟨isClosed_empty, fun _ h => absurd h (notMem_empty _)⟩, empty_subset _,
    fun _ h => absurd h (notMem_empty _)⟩

/-- **The transform** of `(M, N, E, 𝓘, d)` by the blowup `π : M' → M` along `C` (BM08 Definitions
2.2; Włodarczyk §2.1 (3)--(5)): `N' = closure (π⁻¹ (N \ C))`, the strict transform of `N` relative
to the centre; `E'` = the strict transforms `closure (π⁻¹ (H \ C))` of the members `H` of `E`,
followed by the exceptional divisor `π⁻¹ C`; `𝓘' = 𝓘_{π⁻¹C}^{-d} π^*𝓘` on `N'`, realised as the
colon along `N'` of `π^*𝓘` by `(π^*𝓘_C)^d`; `d' = d`. -/
def transform (𝔪 : MarkedIdeal n M) {M' : Type u} [TopologicalSpace M']
    [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M'] (C : Set M) (π : M' → M) :
    MarkedIdeal n M' where
  N := geoStrictTransform π C 𝔪.N
  E := 𝔪.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  ideal := colonAlong n (geoStrictTransform π C 𝔪.N) (GermIdeal.pullback π 𝔪.ideal)
    (idealPow (GermIdeal.pullback π (vanishingIdeal (n := n) C)) 𝔪.d)
  d := 𝔪.d

section Transform

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] (𝔪 : MarkedIdeal n M) (C : Set M) (π : M' → M)

@[simp] theorem transform_N : (𝔪.transform C π).N = geoStrictTransform π C 𝔪.N := rfl

@[simp] theorem transform_E :
    (𝔪.transform C π).E = 𝔪.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] := rfl

@[simp] theorem transform_d : (𝔪.transform C π).d = 𝔪.d := rfl

theorem length_E_transform : (𝔪.transform C π).E.length = 𝔪.E.length + 1 := by
  simp

/-- The exceptional divisor is the last member of the transformed `E`. -/
theorem getLast_E_transform :
    (𝔪.transform C π).E.getLast (by simp) = π ⁻¹' C := by
  simp

end Transform

end OneSpace

/-! ### Along a tower -/

section Tower

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- **The transform along a tower**: the marked ideal on the last space. -/
def transformAlong (𝔪 : MarkedIdeal n X) : {Y : CMfd.{u} n} → BlowupTower X Y → MarkedIdeal n Y
  | _, .refl => 𝔪
  | _, .step T C π _ => (transformAlong 𝔪 T).transform C π

/-- **A multiple test blow-up** of `𝔪` (Włodarczyk §2.1; BM08 Theorem 1.3: each blowing-up
admissible for the transform of the previous stage). -/
def IsTestTower (𝔪 : MarkedIdeal n X) : {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => IsTestTower 𝔪 T ∧ (transformAlong 𝔪 T).IsAdmissibleCentre C

/-- **A resolution** of `𝔪`: a multiple test blow-up after which the cosupport is empty. -/
def IsResolution (𝔪 : MarkedIdeal n X) (T : BlowupTower X Y) : Prop :=
  IsTestTower 𝔪 T ∧ (transformAlong 𝔪 T).cosupp = ∅

variable (𝔪 : MarkedIdeal n X)

@[simp] theorem transformAlong_refl : transformAlong 𝔪 (BlowupTower.refl : BlowupTower X X) = 𝔪 :=
  rfl

@[simp] theorem transformAlong_step (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    transformAlong 𝔪 (.step T C π hπ) = (transformAlong 𝔪 T).transform C π :=
  rfl

theorem N_transformAlong_step (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    (transformAlong 𝔪 (.step T C π hπ)).N = geoStrictTransform π C (transformAlong 𝔪 T).N :=
  rfl

@[simp] theorem isTestTower_step_iff (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    IsTestTower 𝔪 (.step T C π hπ) ↔
      IsTestTower 𝔪 T ∧ (transformAlong 𝔪 T).IsAdmissibleCentre C :=
  Iff.rfl

/-- The mark never changes. -/
@[simp] theorem d_transformAlong (T : BlowupTower X Y) : (transformAlong 𝔪 T).d = 𝔪.d := by
  induction T with
  | refl => rfl
  | step T C π hπ ih => exact ih

/-- `E` grows by exactly one member per blowup (the exceptional divisors, in order). -/
theorem length_E_transformAlong (T : BlowupTower X Y) :
    (transformAlong 𝔪 T).E.length = 𝔪.E.length + T.length := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    rw [transformAlong_step, length_E_transform, ih, BlowupTower.length_step]
    omega

/-- Transforms compose along concatenated towers. -/
theorem transformAlong_append (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    transformAlong 𝔪 (T.append S) = transformAlong (transformAlong 𝔪 T) S := by
  induction S with
  | refl => rfl
  | step S C π hπ ih => simp [BlowupTower.append, transformAlong, ih]

/-- A concatenation is a multiple test blow-up iff both pieces are (the second for the transform). -/
theorem isTestTower_append_iff (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    IsTestTower 𝔪 (T.append S) ↔ IsTestTower 𝔪 T ∧ IsTestTower (transformAlong 𝔪 T) S := by
  induction S with
  | refl => simp [BlowupTower.append, IsTestTower]
  | step S C π hπ ih =>
    simp only [BlowupTower.append, IsTestTower, ih, transformAlong_append]
    tauto

/-- **Resolutions concatenate**: a multiple test blow-up followed by a resolution of the transform is
a resolution. -/
theorem IsResolution.append {T : BlowupTower X Y} {S : BlowupTower Y Z} (hT : IsTestTower 𝔪 T)
    (hS : IsResolution (transformAlong 𝔪 T) S) : IsResolution 𝔪 (T.append S) :=
  ⟨(isTestTower_append_iff 𝔪 T S).mpr ⟨hT, hS.1⟩, by rw [transformAlong_append]; exact hS.2⟩

/-- The empty tower resolves exactly the marked ideals with empty cosupport. -/
theorem isResolution_refl_iff :
    IsResolution 𝔪 (BlowupTower.refl : BlowupTower X X) ↔ 𝔪.cosupp = ∅ := by
  simp [IsResolution, IsTestTower]

end Tower

end MarkedIdeal

end

end Hironaka.MarkedIdeals
