/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaNormalCrossingsLocalBranches
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Blowup.SimultaneousNormalCrossings

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Actual normal crossings branch compatibility

Intrinsic ideal membership ignores labels; genuine finite admissible
sequences are transported under actual branch permutations, and actual
divisor total transforms commute with open restriction. These do not
assert canonical-centre descent for general normal crossings.
Blueprint: `hironaka-normal-crossings-compatibility-extension.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaNormalCrossingsCompatibility

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  NormalCrossings MonomialPart HironakaAdmissibleSequence
  HironakaNormalCrossingsLocalBranches HironakaLocallyFiniteDivisorSum
  HironakaConnectedBoundaryComponents HironakaDivisorResidual
  RelativePrincipalizationSpan GermIdealTotalTransform HironakaEffectiveDivisorSum

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- Identical actual members give identical complete monomial ideals. -/
theorem monomialPart_eq_of_mem_iff (I : GermIdeal n X) {E F : List (Set X)}
    (hmem : ∀ H, H ∈ E ↔ H ∈ F) :
    monomialPart n I E = monomialPart n I F := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · rintro ⟨hhol, h⟩
    refine ⟨hhol, fun i hi => ?_⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((hmem _).mpr (List.get_mem _ i))
    rw [← hj] at hi ⊢
    exact h j hi
  · rintro ⟨hhol, h⟩
    refine ⟨hhol, fun i hi => ?_⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((hmem _).mp (List.get_mem _ i))
    rw [← hj] at hi ⊢
    exact h j hi

omit [IsComplexManifold n X] in
/-- The actual colon nonmonomial ideal is independent of member labels. -/
theorem nonmonomialPart_eq_of_mem_iff (I : GermIdeal n X) {E F : List (Set X)}
    (hmem : ∀ H, H ∈ E ↔ H ∈ F) :
    nonmonomialPart n I E = nonmonomialPart n I F := by
  unfold nonmonomialPart
  rw [monomialPart_eq_of_mem_iff I hmem]

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- Relabel every actual accumulated boundary, retaining the same genuine
blowup projection and actual centres at every finite step. -/
theorem exists_permuted_admissible_sequence {E₀ : List (Set X)} {Z : Set X}
    {f : Y → X} {E : List (Set Y)}
    (hf : IsAdmissibleBlowupSequence n X E₀ Z Y f E)
    (F₀ : List (Set X)) (hp : E₀.Perm F₀) :
    ∃ F : List (Set Y), E.Perm F ∧ IsAdmissibleBlowupSequence n X F₀ Z Y f F := by
  induction hf generalizing F₀ with
  | refl => exact ⟨F₀, hp, .refl⟩
  | step f E C π _ hπ hnc hCZ ih =>
    obtain ⟨F, hEF, hF⟩ := ih F₀ hp
    have hncF : HasNormalCrossings n C F :=
      NormalCrossingsComparison.hasNormalCrossings_of_forall_mem hnc
        (fun H hH => hEF.mem_iff.mpr hH)
    refine ⟨F.map (fun H => closure (π ⁻¹' (H \ C))) ++ [π ⁻¹' C],
      (hEF.map _).append (.refl _), ?_⟩
    exact IsAdmissibleBlowupSequence.step f F C π hF hπ hncF hCZ

/-- Genuine finite admissible blowup sequences retain a genuine SNC boundary. -/
theorem isSNCDivisor_of_admissible_sequence {E₀ : List (Set X)} {Z : Set X}
    {f : Y → X} {E : List (Set Y)}
    (hf : IsAdmissibleBlowupSequence n X E₀ Z Y f E) (hE₀ : IsSNCDivisor n E₀) :
    IsSNCDivisor n E := by
  induction hf with
  | refl => exact hE₀
  | step f E C π _ hπ hnc _ ih =>
    exact SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ ih hnc

/-- Actual blowup total transforms commute with actual open divisor restriction. -/
theorem totalTransform_restrictDivisor {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (D : EffectiveDivisor n X) (U : Opens X) :
    let hV := U.isOpen.preimage hπ.contMDiff.continuous
    let V : Opens Y := ⟨π ⁻¹' (U : Set X), hV⟩
    let hπU := BlowupRestrictOpen.isBlowupAlong_restrict hπ U hV
    BlowupExceptionalDivisor.totalTransform hπU (restrictDivisor D U) =
      restrictDivisor (BlowupExceptionalDivisor.totalTransform hπ D) V := by
  dsimp only
  apply effectiveDivisor_eq_of_ideal_eq
  change GermIdeal.pullback (m := n)
      (fun p : (⟨π ⁻¹' (U : Set X), U.isOpen.preimage hπ.contMDiff.continuous⟩ : Opens Y) =>
        (⟨π p.1, p.2⟩ : U))
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) D.ideal) =
    GermIdeal.pullback (m := n) Subtype.val (GermIdeal.pullback (m := n) π D.ideal)
  have hr := (BlowupRestrictOpen.isBlowupAlong_restrict hπ U
    (U.isOpen.preimage hπ.contMDiff.continuous)).contMDiff
  have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  rw [← pullback_comp contMDiff_subtype_val hr hcoh,
    ← pullback_comp hπ.contMDiff contMDiff_subtype_val hcoh]
  rfl

/-- The actual total transformed divisor has a true locally-finite component
product dictionary on the actual accumulated SNC boundary. -/
theorem exists_transformed_component_dictionary {E₀ : List (Set X)} {Z : Set X}
    {f : Y → X} {E : List (Set Y)}
    (hf : IsAdmissibleBlowupSequence n X E₀ Z Y f E) (hE₀ : IsSNCDivisor n E₀)
    (D : EffectiveDivisor n X) (hD : D.support ⊆ ⋃ H ∈ E₀, H) :
    ∃ D' : EffectiveDivisor n Y, D'.ideal = GermIdeal.pullback (m := n) f D.ideal ∧
      ∃ a : boundaryComponents E → ℕ,
        LocallyFinite (fun C : boundaryComponents E => (C : Set Y)) ∧
        (∀ C : boundaryComponents E, ∀ y ∈ (C : Set Y),
          DivisorExponent.divExp n D'.ideal (C : Set Y) y = a C) ∧
        ∀ y : Y, ∃ V : Set Y, ∃ A : List (Set Y × ℕ), IsOpen V ∧ y ∈ V ∧
          (A.map Prod.fst).Nodup ∧
          (∀ q ∈ A, ∃ hC : q.1 ∈ boundaryComponents E, q.2 = a ⟨q.1, hC⟩ ∧ 0 < q.2) ∧
          ∀ z ∈ V, ∀ g : Y → ℂ, D'.ideal.mem z g ↔
            (componentPowerProduct (n := n) A).mem z g := by
  have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  have hpull : ∃ D' : EffectiveDivisor n Y,
      D'.ideal = GermIdeal.pullback (m := n) f D.ideal ∧ D'.support ⊆ ⋃ H ∈ E, H := by
    induction hf with
    | refl =>
      refine ⟨D, ?_, hD⟩
      exact (BlowupControlledTransform.pullback_id hcoh).symm
    | step f E C π hprev hπ _ _ ih =>
      obtain ⟨D₁, hD₁I, hD₁s⟩ := ih
      let D₂ := BlowupExceptionalDivisor.totalTransform hπ D₁
      refine ⟨D₂, ?_, fun z hz => ?_⟩
      · change GermIdeal.pullback (m := n) π D₁.ideal =
          GermIdeal.pullback (m := n) (f ∘ π) D.ideal
        rw [hD₁I]
        exact (pullback_comp hprev.isBlowupSequence.contMDiff hπ.contMDiff hcoh).symm
      · obtain ⟨H, hH, hzH⟩ := mem_iUnion₂.mp
          (hD₁s ((Set.ext_iff.mp (BlowupExceptionalDivisor.support_totalTransform hπ D₁) z).mp hz))
        by_cases hzC : π z ∈ C
        · exact mem_iUnion₂.mpr ⟨π ⁻¹' C,
            List.mem_append_right _ (List.mem_singleton.mpr rfl), hzC⟩
        · exact mem_iUnion₂.mpr ⟨closure (π ⁻¹' (H \ C)),
            List.mem_append_left _ (List.mem_map.mpr ⟨H, hH, rfl⟩),
            subset_closure ⟨hzH, hzC⟩⟩
  obtain ⟨D', hDI, hDs⟩ := hpull
  obtain ⟨a, hlf, ha, hlocal⟩ := exists_locallyFinite_original_component_products D' E
    (isSNCDivisor_of_admissible_sequence hf hE₀) hDs
  exact ⟨D', hDI, a, hlf, ha, hlocal⟩

end
end Hironaka.HironakaNormalCrossingsCompatibility
