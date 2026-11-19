import Hironaka.Resolution.HironakaG8ClassStepLower
import Hironaka.Resolution.HironakaG8LocalExcSum
import Hironaka.Resolution.HironakaG11InvBMLowerDomainSucc
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.MarkedIdeal.GeoTransformWellFormed

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The class of `𝒥 = 𝒞 + ℰ` depends only on the class of `ℐ|_U` (G8C lane, run 0080, round 2; (B') plan module 10, levels `≥ 1`)

Blueprint: `hironaka-g8-class-step-cut.tex`.  Source: Bierstone--Milman 2008, §5 Step I.B: "`cosupp 𝒥 = cosupp ℐ|_U ∩ {x ∈ P :
s(x) = s}` (and likewise after any sequence of test transformations of `𝒥`).  Thus any sequence of test transformations of `𝒥`
is a sequence of test transformations of `ℐ|_U` (and the centre `C` of each admissible blowing-up lies inside the intersection of
the components of `E` that pass through a point of `C`).  Therefore, the equivalence class of `𝒥` depends only on that of
`ℐ|_U`."

* `hasNormalCrossings_of_append`: normal crossings with `F ++ G` give normal crossings with `G`;
* **`locEquiv_addE`**: adding members in front of the boundary keeps a local equivalence (`AddRel`, `isLocStable_addRel`);
* `ExcRel.cosupp_eq'`, `ExcRel.projectionTest'`, `ExcRel.pullback_val'`: lane G8's `ExcRel` calculus with only well-formedness
  of the summand (the coefficient ideal need not be nonzero along the hypersurface of maximal contact);
* `isWellFormed_projectionTest`, `isSNCDivisor_projectionTest`;
* **`CutRel`, `isLocStable_cutRel`, `locEquiv_of_cutRel`** (BM08 Step I.B): if `A ≈ B` with boundary `F ++ G` (simple normal
  crossings), every member of `F` either belongs to the list `S` of closed submanifolds or is empty, and `P ≅ A_G ⊕ ℰ_S`,
  `Q ≅ B_G ⊕ ℰ_S` (`A_G` = `A` with boundary `G`, well formed), then `P ≈ Q`;
* **`locWPEquiv_lowerIdealBM_succ`**: the lower ideals of levels `s + 1` of class-equivalent marked ideals are locally
  equivalent on every common open of the masks; **`lowerPairs_locWPEquiv`**: the `LocWPEquiv` part of
  `HironakaG8ClassStep.LowerClassBM` at all levels.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8ClassStepCut

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.BlowupStrictSubmanifold
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalStable
  Hironaka.MarkedIdealBiholomorphism Hironaka.NormalCrossings
  Hironaka.HironakaG8LocalExcSum
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal
  projection_test_isInvDomain)
open Hironaka.IdealWeightPowers (idealPow unitIdeal isCoherent_unitIdeal)
open Hironaka.GermIdealOrder (cosupport)
open Hironaka.RestrictedIdealWeight (RestrictLe)
open Hironaka.HironakaG8LogMixedHistory (restrictLe_pullback_of_restrictLe)
open scoped ProductComplexManifold

noncomputable section

/-! ### Normal crossings with a final segment; adding members -/

section AddE

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Normal crossings with `F ++ G` give normal crossings with `G`** (re-index the adapted coordinates). -/
theorem hasNormalCrossings_of_append {C : Set M} {F G : List (Set M)} (h : HasNormalCrossings n C (F ++ G)) :
    HasNormalCrossings n C G := by
  intro x hx
  obtain ⟨S₀, S, hfam, hcard⟩ := h x hx
  let e : Fin G.length → Fin (F ++ G).length := fun i => ⟨F.length + i, by rw [List.length_append]; omega⟩
  have hget : ∀ i : Fin G.length, (F ++ G).get (e i) = G.get i := fun i => by
    simp [e, List.getElem_append_right]
  have hA : ∀ o : Option (Fin G.length), (o.elim C fun i => G.get i) =
      (Option.map e o).elim C fun i => (F ++ G).get i := by
    intro o
    cases o with
    | none => rfl
    | some i => exact (hget i).symm
  have hS : ∀ o : Option (Fin G.length), (o.elim S₀ fun i => S (e i)) = (Option.map e o).elim S₀ S := by
    intro o
    cases o <;> rfl
  refine ⟨S₀, fun i => S (e i),
    NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hfam (Option.map e) hA hS, fun i hi => hcard (e i) ?_⟩
  rw [hget]
  exact hi

end AddE

section AddRel

/-- **The relation of the coinduction for added members**: a locally equivalent pair with the same members `F` added in front
of the boundary. -/
def AddRel (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m} (P' Q' : MarkedIdeal m Y) : Prop :=
  ∃ (P Q : MarkedIdeal m Y) (F : List (Set Y)), LocEquiv κ P Q ∧ P' = { P with E := F ++ P.E } ∧
    Q' = { Q with E := F ++ P.E }

/-- **Adding members is stable under the local test actions.** -/
theorem isLocStable_addRel (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => AddRel κ (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P' Q' ⟨P, Q, F, -, rfl, rfl⟩
    rfl
  cosupp_eq := by
    rintro m Y P' Q' ⟨P, Q, F, h, rfl, rfl⟩
    exact h.cosupp_eq_base
  controlled := by
    rintro m Y P' Q' ⟨P, Q, F, h, rfl, rfl⟩ C Z π hπ hC
    have hCP : P.IsAdmissibleCentre C := ⟨hC.1, hC.2.1, hasNormalCrossings_of_append hC.2.2⟩
    refine ⟨P.geoTransform C π, Q.geoTransform C π, F.map (geoStrictTransform π C),
      (isLocStable_locEquiv κ).controlled h C π hπ hCP, ?_, ?_⟩
    · show ({ P with E := F ++ P.E } : MarkedIdeal m Y).geoTransform C π =
        { P.geoTransform C π with E := F.map (geoStrictTransform π C) ++
          (P.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) }
      show ({ P.geoTransform C π with E := (F ++ P.E).map (geoStrictTransform π C) ++ [π ⁻¹' C] } :
        MarkedIdeal m Z) = _
      rw [List.map_append, List.append_assoc]
    · show ({ Q with E := F ++ P.E } : MarkedIdeal m Y).geoTransform C π =
        { Q.geoTransform C π with E := F.map (geoStrictTransform π C) ++
          (P.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) }
      show ({ Q.geoTransform C π with E := (F ++ P.E).map (geoStrictTransform π C) ++ [π ⁻¹' C] } :
        MarkedIdeal m Z) = _
      rw [List.map_append, List.append_assoc]
  projection := by
    rintro hp m Y P' Q' ⟨P, Q, F, h, rfl, rfl⟩
    refine ⟨projectionTest P, projectionTest Q, F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·),
      (isLocStable_locEquiv κ).projection hp h, ?_, ?_⟩
    · show ({ projectionTest P with E := (F ++ P.E).map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++
          [horizontal Y] } : MarkedIdeal (m + 1) (projectionAmbient Y)) = { projectionTest P with
          E := F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++
            (P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y]) }
      rw [List.map_append, List.append_assoc]
    · show ({ projectionTest Q with E := (F ++ P.E).map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++
          [horizontal Y] } : MarkedIdeal (m + 1) (projectionAmbient Y)) = { projectionTest Q with
          E := F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++
            (P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y]) }
      rw [List.map_append, List.append_assoc]
  restrict := by
    rintro m Y P' Q' ⟨P, Q, F, h, rfl, rfl⟩ U
    refine ⟨MarkedIdeal.pullback (Subtype.val : U → Y) P, MarkedIdeal.pullback (Subtype.val : U → Y) Q,
      F.map ((Subtype.val : U → Y) ⁻¹' ·), (isLocStable_locEquiv κ).restrict h U, ?_, ?_⟩
    · show ({ MarkedIdeal.pullback (Subtype.val : U → Y) P with E := (F ++ P.E).map ((Subtype.val : U → Y) ⁻¹' ·) } :
        MarkedIdeal m (CMfd.of (n := m) U)) = _
      rw [List.map_append]
      rfl
    · show ({ MarkedIdeal.pullback (Subtype.val : U → Y) Q with E := (F ++ P.E).map ((Subtype.val : U → Y) ⁻¹' ·) } :
        MarkedIdeal m (CMfd.of (n := m) U)) = _
      rw [List.map_append]
      rfl

/-- **Adding members keeps a local equivalence** (kinds without exceptional blowups). -/
theorem locEquiv_addE {κ : Kinds} (hexc : κ.exc = false) {n : ℕ} {X : CMfd.{u} n} {P Q : MarkedIdeal n X}
    (h : LocEquiv κ P Q) (F : List (Set X)) :
    LocEquiv κ { P with E := F ++ P.E } { Q with E := F ++ P.E } :=
  LocEquiv.of_isLocStable (isLocStable_addRel κ) hexc ⟨P, Q, F, h, rfl, rfl⟩

end AddRel

/-! ### Lane G8's `ExcRel` calculus with a well-formed (not necessarily native-domain) summand -/

section ExcWeak

variable {n : ℕ} {Y : CMfd.{u} n} {P A : MarkedIdeal n Y} {S : List (Set Y)}

/-- `HironakaG8LocalExcSum.ExcRel.cosupp_eq` for a well-formed summand with `d ≥ 1`. -/
theorem ExcRel.cosupp_eq' (h : ExcRel P A S) (hA : A.IsWellFormed) (hd : 1 ≤ A.d) (hS : ∀ H ∈ S, IsClosed H) :
    P.cosupp = A.cosupp ∩ throughSet S := by
  have hIhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA.isCoherent
  show cosupport n P.N P.ideal P.d = cosupport n A.N A.ideal A.d ∩ throughSet S
  rw [h.N_eq, h.d_eq, ← cosupport_excIdeal hA.isClosedSubmanifold_N.2 hIhol hS hd]
  exact Subset.antisymm (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.ge _)
    (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.le _)

/-- `HironakaG8LocalExcSum.ExcRel.projectionTest` for a summand with holomorphic generators. -/
theorem ExcRel.projectionTest' (h : ExcRel P A S) (hIhol : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x)
    (hS : ∀ H ∈ S, IsClosedSubmanifold n H) :
    ExcRel (projectionTest P) (projectionTest A) (S.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·)) := by
  have hφ := ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := Y) (Y := ComplexModel 1)
  have hsubm := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := 1) (X := Y) (Y := ComplexModel 1)
  have hvan : ∀ i < S.length, GermIdeal.pullback (m := n + 1) (Prod.fst : projectionAmbient Y → Y)
      (vanishingIdeal (n := n) (S.getD i ∅)) =
        vanishingIdeal (n := n + 1) ((Prod.fst : projectionAmbient Y → Y) ⁻¹' S.getD i ∅) := fun i hi =>
    HironakaSmoothSubmersionRelativeRestriction.pullback_vanishingIdeal_submersion hsubm (hS _ (getD_mem hi))
  refine ⟨?_, ?_, h.d_eq, fun _ _ hg => hg.1, ?_, ?_⟩
  · show (Prod.fst : projectionAmbient Y → Y) ⁻¹' P.N = (Prod.fst : projectionAmbient Y → Y) ⁻¹' A.N
    rw [h.N_eq]
  · show P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y] =
      A.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y]
    rw [h.E_eq]
  · exact DerivativeIdealAlongTransform.restrictLe_trans
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) (excIdeal_hol _ _ _) h.le)
      (pullback_excIdeal_le hφ hIhol hvan A.d _)
  · exact DerivativeIdealAlongTransform.restrictLe_trans (excIdeal_pullback_le hφ hIhol hvan A.d _)
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) h.hol h.ge)

/-- `HironakaG8LocalExcSum.ExcRel.pullback_val` for a summand with holomorphic generators. -/
theorem ExcRel.pullback_val' (h : ExcRel P A S) (hIhol : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x)
    (U : Opens Y) :
    ExcRel (Y := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P)
      (MarkedIdeal.pullback (Subtype.val : U → Y) A) (S.map ((Subtype.val : U → Y) ⁻¹' ·)) := by
  have hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : U → Y) := contMDiff_subtype_val
  have hvan : ∀ i < S.length, GermIdeal.pullback (m := n) (Subtype.val : U → Y)
      (vanishingIdeal (n := n) (S.getD i ∅)) = vanishingIdeal (n := n) ((Subtype.val : U → Y) ⁻¹' S.getD i ∅) :=
    fun i _ => SmoothCentreHomogeneity.pullback_val_vanishingIdeal U _
  refine ⟨?_, ?_, h.d_eq, fun _ _ hg => hg.1, ?_, ?_⟩
  · show (Subtype.val : U → Y) ⁻¹' P.N = (Subtype.val : U → Y) ⁻¹' A.N
    rw [h.N_eq]
  · show P.E.map ((Subtype.val : U → Y) ⁻¹' ·) = A.E.map ((Subtype.val : U → Y) ⁻¹' ·)
    rw [h.E_eq]
  · exact DerivativeIdealAlongTransform.restrictLe_trans
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) (excIdeal_hol _ _ _) h.le)
      (pullback_excIdeal_le hφ hIhol hvan A.d _)
  · exact DerivativeIdealAlongTransform.restrictLe_trans (excIdeal_pullback_le hφ hIhol hvan A.d _)
      (restrictLe_pullback_of_restrictLe hφ (fun _ hp => hp) h.hol h.ge)

/-- The unit ideal on a well-formed carrier and boundary is in the native domain. -/
theorem isInvDomain_unit {N : Set Y} {E : List (Set Y)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hT : IsTransverse n N E) :
    IsInvDomain n ({ N := N, E := E, ideal := unitIdeal n Y, d := 1 } : MarkedIdeal n Y) := by
  refine ⟨⟨hN, isCoherent_unitIdeal, hE, hT⟩, ?_, le_rfl, ?_⟩
  · intro x hx
    obtain ⟨k, hk⟩ := hN.2 x hx
    exact ⟨k, hk.1, hk⟩
  · intro x hx
    refine ⟨1, holomorphicAt_const 1, frequently_iff.mpr ?_⟩
    intro U hU
    exact ⟨x, mem_of_mem_nhds hU, hx, one_ne_zero⟩

/-- **The product with a line of a well-formed marked ideal is well formed.** -/
theorem isWellFormed_projectionTest (hA : A.IsWellFormed) : (projectionTest A).IsWellFormed := by
  have h := (projection_test_isInvDomain _ (isInvDomain_unit hA.isClosedSubmanifold_N hA.isSNCDivisor
    hA.isTransverse)).isWellFormed
  exact ⟨h.isClosedSubmanifold_N, GermIdealPullbackCalculus.isCoherent_pullback
    (ProductComplexManifold.contMDiff_fst (n := n) (m := 1) (X := Y) (Y := ComplexModel 1)) hA.isCoherent,
    h.isSNCDivisor, h.isTransverse⟩

/-- **The boundary of a product with a line is simple normal crossings.** -/
theorem isSNCDivisor_projectionTest (hA : IsSNCDivisor n A.E) : IsSNCDivisor (n + 1) (projectionTest A).E :=
  (projection_test_isInvDomain _ (isInvDomain_unit (N := univ) HomogenizedGlueingTower.isClosedSubmanifold_univ hA
    (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hA))).isWellFormed.isSNCDivisor

end ExcWeak

/-! ### Bierstone--Milman's Step I.B: the class of `𝒥` depends only on the class of `ℐ|_U` -/

section Cut

/-- **The relation of Step I.B**: `P ≅ A_G ⊕ ℰ_S` and `Q ≅ B_G ⊕ ℰ_S` for a locally equivalent pair `A ≈ B` with boundary
`F ++ G` (simple normal crossings; `G` the boundary of `P`), every member of `F` in `S` or empty, `S` closed submanifolds, the
summands `A_G`, `B_G` (boundary `G`) well formed with marks `≥ 1`. -/
def CutRel (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m} (P Q : MarkedIdeal m Y) : Prop :=
  ∃ (A B : MarkedIdeal m Y) (F S : List (Set Y)), LocEquiv κ A B ∧ A.E = F ++ P.E ∧ IsSNCDivisor m A.E ∧
    (∀ H ∈ F, H ∈ S ∨ H = ∅) ∧ (∀ H ∈ S, IsClosedSubmanifold m H) ∧
    ({ A with E := P.E } : MarkedIdeal m Y).IsWellFormed ∧ ({ B with E := P.E } : MarkedIdeal m Y).IsWellFormed ∧
    1 ≤ A.d ∧ 1 ≤ B.d ∧ ExcRel P { A with E := P.E } S ∧ ExcRel Q { B with E := P.E } S

/-- **The relation of Step I.B is stable under the local test actions.** -/
theorem isLocStable_cutRel (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => CutRel κ (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P Q ⟨A, B, F, S, -, -, -, -, -, -, -, -, -, -, hQ⟩
    exact hQ.E_eq
  cosupp_eq := by
    rintro m Y P Q ⟨A, B, F, S, h, -, -, -, hS, hwA, hwB, hdA, hdB, hP, hQ⟩
    rw [ExcRel.cosupp_eq' hP hwA hdA (fun H hH => (hS H hH).1), ExcRel.cosupp_eq' hQ hwB hdB (fun H hH => (hS H hH).1)]
    exact congrArg (· ∩ throughSet S) h.cosupp_eq_base
  controlled := by
    rintro m Y P Q ⟨A, B, F, S, h, hAE, hsnc, hFS, hS, hwA, hwB, hdA, hdB, hP, hQ⟩ C Z π hπ hC
    have hcos := ExcRel.cosupp_eq' hP hwA hdA (fun H hH => (hS H hH).1)
    have hCsub : C ⊆ A.cosupp ∩ throughSet S := hcos ▸ hC.2.1
    have hCS : ∀ H ∈ S, C ⊆ H := fun H hH x hx => (hCsub hx).2 H hH
    have hCA' : ({ A with E := P.E } : MarkedIdeal m Y).IsAdmissibleCentre C :=
      ⟨hC.1, fun x hx => (hCsub hx).1, hC.2.2⟩
    have hCB' : ({ B with E := P.E } : MarkedIdeal m Y).IsAdmissibleCentre C :=
      ⟨hC.1, fun x hx => h.cosupp_eq_base ▸ (hCsub hx).1, hC.2.2⟩
    have hncA : HasNormalCrossings m C A.E := by
      rw [hAE]
      refine HironakaG11InvBMAdmissible.hasNormalCrossings_append_of_dichotomy (hAE ▸ hsnc) hC.2.2 fun H hH => ?_
      rcases hFS H hH with hHS | rfl
      · exact Or.inl (hCS H hHS)
      · exact Or.inr (Set.disjoint_empty _)
    have hCA : A.IsAdmissibleCentre C := ⟨hC.1, fun x hx => (hCsub hx).1, hncA⟩
    refine ⟨A.geoTransform C π, B.geoTransform C π, F.map (geoStrictTransform π C), S.map (geoStrictTransform π C),
      (isLocStable_locEquiv κ).controlled h C π hπ hCA, ?_,
      SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hsnc hncA, ?_, ?_,
      GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwA hCA' hπ,
      GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwB hCB' hπ, hdA, hdB,
      hP.geoTransform hwA hCA' hπ hS hCS, hQ.geoTransform hwB hCB' hπ hS hCS⟩
    · show A.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] =
        F.map (geoStrictTransform π C) ++ (P.E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
      rw [hAE, List.map_append, List.append_assoc]
    · intro H' hH'
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      rcases hFS H hH with hHS | rfl
      · exact Or.inl (List.mem_map.mpr ⟨H, hHS, rfl⟩)
      · right
        show closure (π ⁻¹' (∅ \ C)) = ∅
        simp
    · intro H' hH'
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      exact BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ (hS H hH) (hCS H hH)
  projection := by
    rintro hp m Y P Q ⟨A, B, F, S, h, hAE, hsnc, hFS, hS, hwA, hwB, hdA, hdB, hP, hQ⟩
    refine ⟨projectionTest A, projectionTest B, F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·),
      S.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·), (isLocStable_locEquiv κ).projection hp h, ?_,
      isSNCDivisor_projectionTest hsnc, ?_, ?_, isWellFormed_projectionTest hwA, isWellFormed_projectionTest hwB, hdA, hdB,
      ExcRel.projectionTest' hP (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hwA.isCoherent) hS,
      ExcRel.projectionTest' hQ (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hwB.isCoherent) hS⟩
    · show A.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y] =
        F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++
          (P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y])
      rw [hAE, List.map_append, List.append_assoc]
    · intro H' hH'
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      rcases hFS H hH with hHS | rfl
      · exact Or.inl (List.mem_map.mpr ⟨H, hHS, rfl⟩)
      · exact Or.inr (Set.preimage_empty)
    · intro H' hH'
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      exact HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion
        (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)) (hS H hH)
  restrict := by
    rintro m Y P Q ⟨A, B, F, S, h, hAE, hsnc, hFS, hS, hwA, hwB, hdA, hdB, hP, hQ⟩ U
    refine ⟨MarkedIdeal.pullback (Subtype.val : U → Y) A, MarkedIdeal.pullback (Subtype.val : U → Y) B,
      F.map ((Subtype.val : U → Y) ⁻¹' ·), S.map ((Subtype.val : U → Y) ⁻¹' ·), (isLocStable_locEquiv κ).restrict h U,
      ?_, (HironakaBaseChange.isOpenHoloEmbedding_val (n := m) U).isSNCDivisor_map_preimage hsnc, ?_, ?_,
      MarkedIdealRestrictOpen.IsWellFormed.pullback_val hwA U, MarkedIdealRestrictOpen.IsWellFormed.pullback_val hwB U,
      hdA, hdB, ExcRel.pullback_val' hP (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hwA.isCoherent) U,
      ExcRel.pullback_val' hQ (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hwB.isCoherent) U⟩
    · show A.E.map ((Subtype.val : U → Y) ⁻¹' ·) = F.map ((Subtype.val : U → Y) ⁻¹' ·) ++ P.E.map ((Subtype.val : U → Y) ⁻¹' ·)
      rw [hAE, List.map_append]
    · intro H' hH'
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      rcases hFS H hH with hHS | rfl
      · exact Or.inl (List.mem_map.mpr ⟨H, hHS, rfl⟩)
      · exact Or.inr (Set.preimage_empty)
    · intro H' hH'
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val (hS H hH) U

/-- **Bierstone--Milman's Step I.B (local `s(i,ii)` form)**: under `CutRel`, `P ≈ Q`. -/
theorem locEquiv_of_cutRel {κ : Kinds} (hexc : κ.exc = false) {n : ℕ} {X : CMfd.{u} n} {P Q : MarkedIdeal n X}
    (h : CutRel κ P Q) : LocEquiv κ P Q :=
  LocEquiv.of_isLocStable (isLocStable_cutRel κ) hexc h

end Cut

/-! ### The lower ideals at the levels `s + 1` -/

section LevelSucc

variable {n : ℕ} {X : CMfd.{0} n}

/-- The mark `d (d - 1) ⋯ 1` of the coefficient ideal is positive. -/
theorem one_le_coeffEmptyBM_d (A : MarkedIdeal n X) : 1 ≤ (coeffEmptyBM A).d := by
  rw [coeffEmptyBM_d]
  exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j hj => by
    rw [Finset.mem_range] at hj
    omega)

/-- **The lower ideals of the levels `s + 1` of class-equivalent marked ideals are locally equivalent** on every common open of
the masks (BM08 §5 Step I.B: "the equivalence class of `𝒥` depends only on that of `ℐ|_U`"): for `A ≈ B` (`LocWPEquiv`, the same
divisor) of the domain of maximal order, along a multiple test blow-up `T₀` of `J̄_A`, at a point `y₀` of the cosupport, on an
open `O` inside `maskBM A (s+1) T₀ y₀ ⊓ maskBM B (s+1) T₀ y₀`, the restrictions of `lowerIdealBM A (s+1) T₀ y₀` and
`lowerIdealBM B (s+1) T₀ y₀` are `LocWPEquiv`. -/
theorem locWPEquiv_lowerIdealBM_succ (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A)
    (hB : IsInvDomain k' B) (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hE : A.E = B.E) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked A) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked A) T₀).cosupp)
    (s : ℕ) (O : Opens Y₀) (hOA : O ≤ maskBM A (s + 1) T₀ y₀) (hOB : O ≤ maskBM B (s + 1) T₀ y₀) :
    LocWPEquiv (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A (s + 1) T₀ y₀))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B (s + 1) T₀ y₀)) := by
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
  let UA : Opens X := ⟨(tangentChoice A (T₀.proj y₀)).1, hwA.isOpen⟩
  let UB : Opens X := ⟨(tangentChoice B (T₀.proj y₀)).1, hwB.isOpen⟩
  have hOUA : O ≤ openPreimage T₀ UA := fun z hz => interior_subset (hOA hz).2
  have hOUB : O ≤ openPreimage T₀ UB := fun z hz => interior_subset (hOB hz).2
  have hcohA := (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := emptyBoundary A) hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent T₀
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A T₀ hTA)).2
  have hcohB := (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := emptyBoundary B) hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent T₀
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary B T₀ hTB)).2
  have hcLA : (contactCoeffBM A (tangentChoice A (T₀.proj y₀)).2 T₀).ideal.IsCoherent :=
    HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ 0
  have hcLB : (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀).ideal.IsCoherent :=
    HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T₀ hTJB y₀ 0
  -- P4 at the stage, moved to `O`
  have h4A := HironakaG8LocalTransport.locWPEquiv_restrict_of_le hcohA hcLA hOUA
    (HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM hA.isWellFormed hA.one_le_d UA hwA T₀ hTA)
  have h4B := HironakaG8LocalTransport.locWPEquiv_restrict_of_le hcohB hcLB hOUB
    (HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM hB.isWellFormed hB.one_le_d UB hwB T₀ hTB)
  -- the boundary of the transforms restricted to `O`: original members `Fo`, then the born members `Gb`
  have hEAB : (geoTransformAlong A T₀).E = (geoTransformAlong B T₀).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE T₀
  set Fo := ((geoTransformAlong A T₀).E.take A.E.length).map ((Subtype.val : O → Y₀) ⁻¹' ·) with hFo
  set Gb := ((geoTransformAlong A T₀).E.drop A.E.length).map ((Subtype.val : O → Y₀) ⁻¹' ·) with hGb
  have hsplitA : (MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong A T₀)).E = Fo ++ Gb := by
    show (geoTransformAlong A T₀).E.map ((Subtype.val : O → Y₀) ⁻¹' ·) = _
    rw [hFo, hGb, ← List.map_append, List.take_append_drop]
  have hsplitB : (MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong B T₀)).E = Fo ++ Gb := by
    show (geoTransformAlong B T₀).E.map ((Subtype.val : O → Y₀) ⁻¹' ·) = _
    rw [← hEAB]
    exact hsplitA
  have hAe : MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong (emptyBoundary A) T₀) =
      { MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong A T₀) with E := Gb } := by
    rw [HironakaG11InvBMStage.geoTransformAlong_emptyBoundary A T₀]
    rfl
  have hBe : MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong (emptyBoundary B) T₀) =
      { MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong B T₀) with E := Gb } := by
    rw [HironakaG11InvBMStage.geoTransformAlong_emptyBoundary B T₀, hGb, hEAB, ← hE]
    rfl
  have hCEborn : ∀ (C : MarkedIdeal n X) (w : X → ℂ), C.E = A.E →
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM C w T₀)).E = Gb := by
    intro C w hCE
    show (geoTransformAlong (coeffEmptyBM C) T₀).E.map ((Subtype.val : O → Y₀) ⁻¹' ·) = _
    rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := coeffEmptyBM C) (𝔫 := emptyBoundary C) rfl T₀,
      HironakaG11InvBMStage.geoTransformAlong_emptyBoundary C T₀, hGb]
    show ((geoTransformAlong C T₀).E.drop C.E.length).map _ = _
    rw [hCE, MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := C) (𝔫 := A) hCE T₀]
  have hCAE := hCEborn A (tangentChoice A (T₀.proj y₀)).2 rfl
  have hCBE := hCEborn B (tangentChoice B (T₀.proj y₀)).2 hE.symm
  -- add the original members back: the underlying pair of Step I.B
  have hUA := locEquiv_addE rfl h4A.symm Fo
  have hUB := locEquiv_addE rfl h4B.symm Fo
  have hmid := (h.geoTransformAlong T₀ hTA).restrict O
  have eA : ({ MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong (emptyBoundary A) T₀) with
      E := Fo ++ (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (contactCoeffBM A (tangentChoice A (T₀.proj y₀)).2 T₀)).E } : MarkedIdeal n (CMfd.of (n := n) O)) =
      MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong A T₀) := by
    rw [hCAE, hAe]
    show ({ MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong A T₀) with E := Fo ++ Gb } :
      MarkedIdeal n (CMfd.of (n := n) O)) = _
    rw [← hsplitA]
  have eB : ({ MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong (emptyBoundary B) T₀) with
      E := Fo ++ (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀)).E } : MarkedIdeal n (CMfd.of (n := n) O)) =
      MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong B T₀) := by
    rw [hCBE, hBe]
    show ({ MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong B T₀) with E := Fo ++ Gb } :
      MarkedIdeal n (CMfd.of (n := n) O)) = _
    rw [← hsplitB]
  rw [eA] at hUA
  rw [eB] at hUB
  have hU := hUA.trans (hmid.trans hUB.symm)
  rw [hCBE, ← hCAE] at hU
  -- the members: through the anchor (in `S`) or empty on the mask
  set S := throughMembers A T₀ y₀ with hS
  have hSB : throughMembers B T₀ y₀ = S := by
    unfold throughMembers
    rw [HironakaG8MemberLoci.origMembers_eq_of_E_eq hE.symm T₀]
    rfl
  have hJ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked A hA.isWellFormed) T₀ hT₀
  have hSm : ∀ H ∈ S.map ((Subtype.val : O → Y₀) ⁻¹' ·), IsClosedSubmanifold n H := by
    intro H' hH'
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_take (mem_throughMembers.mp hH).1)
    exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val (MonomialPart.isClosedSubmanifold_get hn hJ.isSNCDivisor i) O
  have hFS : ∀ H ∈ Fo, H ∈ S.map ((Subtype.val : O → Y₀) ⁻¹' ·) ∨ H = ∅ := by
    intro H' hH'
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    have hH₀ : H ∈ origMembers A T₀ := by
      show H ∈ (geoTransformAlong (barMarked A) T₀).E.take A.E.length
      rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := barMarked A) (𝔫 := A) rfl T₀]
      exact hH
    by_cases hy : y₀ ∈ H
    · exact Or.inl (List.mem_map.mpr ⟨H, mem_throughMembers.mpr ⟨hH₀, hy⟩, rfl⟩)
    · right
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => hy ?_
      exact (interior_subset (hOA z.2).1).1 H hH₀ hz
  -- the sums
  have hwfCA := (HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le hA.isWellFormed hA.one_le_d UA
    hwA T₀ hA.dimLE hT₀ O hOUA).1
  have hwfCB := (HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le hB.isWellFormed hB.one_le_d UB
    hwB T₀ hB.dimLE hTJB O hOUB).1
  have hPA := ExcRel.pullback_val' (excRel_sumIdeal (contactCoeffBM A (tangentChoice A (T₀.proj y₀)).2 T₀) hcLA S)
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcLA) O
  have hPB := ExcRel.pullback_val' (excRel_sumIdeal (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀) hcLB S)
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcLB) O
  have hsnc : IsSNCDivisor n (Fo ++ Gb) := by
    rw [← hsplitA]
    exact (MarkedIdealRestrictOpen.IsWellFormed.pullback_val
      (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA.isWellFormed T₀ hTA) O).isSNCDivisor
  have hdA := one_le_coeffEmptyBM_d A
  have hdB := one_le_coeffEmptyBM_d B
  have hQS : (lowerIdealBM B (s + 1) T₀ y₀) = ⟨(contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀).N,
      (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀).E,
      RestrictedIdealExtension.sumIdeal (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀).ideal
        (HironakaG11InvBMLower.exceptionalTermBM S (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀).d),
      (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀).d⟩ := by
    rw [← hSB]
    rfl
  rw [hQS]
  refine locEquiv_of_cutRel rfl ⟨_, _, Fo, S.map ((Subtype.val : O → Y₀) ⁻¹' ·), hU, rfl, ?_, hFS, hSm, ?_, ?_, ?_,
    ?_, hPA, ?_⟩
  · show IsSNCDivisor n (Fo ++ _)
    rw [hCAE]
    exact hsnc
  · exact hwfCA
  · show ({ MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀) with
      E := (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM A (tangentChoice A (T₀.proj y₀)).2 T₀)).E } :
        MarkedIdeal n (CMfd.of (n := n) O)).IsWellFormed
    rw [hCAE, ← hCBE]
    exact hwfCB
  · show 1 ≤ (contactCoeffBM A (tangentChoice A (T₀.proj y₀)).2 T₀).d
    rw [contactCoeffBM_d]
    exact hdA
  · show 1 ≤ (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀).d
    rw [contactCoeffBM_d]
    exact hdB
  · show ExcRel _ ({ MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM B (tangentChoice B (T₀.proj y₀)).2 T₀) with
      E := (MarkedIdeal.pullback (Subtype.val : O → Y₀) (contactCoeffBM A (tangentChoice A (T₀.proj y₀)).2 T₀)).E } :
        MarkedIdeal n (CMfd.of (n := n) O)) _
    rw [hCAE, ← hCBE]
    exact hPB

end LevelSucc

/-! ### All levels -/

section All

variable {n : ℕ} {X : CMfd.{0} n}

/-- **The `LocWPEquiv` part of the class data of the lower ideals** (`HironakaG8ClassStep.LowerPairs` for `LocWPEquiv`, all
levels): for class-equivalent marked ideals of the domain of maximal order with the same divisor. -/
theorem lowerPairs_locWPEquiv (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A)
    (hB : IsInvDomain k' B) (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hE : A.E = B.E) :
    HironakaG8ClassStep.LowerPairs A B fun {_} P Q => LocWPEquiv P Q := by
  intro Y₀ T₀ hT₀ s y₀ hy₀ _ O hOA hOB _ _ _ _
  cases s with
  | zero => exact HironakaG8ClassStepLower.locWPEquiv_lowerIdealBM_zero hn hA hB hmA hmB h hE T₀ hT₀ hy₀ O hOA hOB
  | succ s => exact locWPEquiv_lowerIdealBM_succ hn hA hB hmA hmB h hE T₀ hT₀ hy₀ s O hOA hOB

end All



end

end Hironaka.HironakaG8ClassStepCut
