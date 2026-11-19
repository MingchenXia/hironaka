import Hironaka.Resolution.HironakaG3TrailingEmptyComparison

/-! Actual ambient comparison through an all-empty intrinsic suffix. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EmptySuffixComparison
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaDisjointFiniteControlledHistory HironakaG3ControlledHistorySubsetTransport
  HironakaG3AmbientHistoryComparison BlowupTowerIsomorphism
open ResolutionInvariantExt (IsEmptyTower)

/-- A coupled lift of a lower history followed by any all-empty lower
suffix has the same ambient endpoint, over the base and the lower endpoint,
as an arbitrary coupled lift of the lower prefix. -/
theorem exists_comparison_after_empty_suffix
    {d t : ℕ} {X : CMfd.{0} (d+t)} {P Q R : CMfd.{0} d}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} (T : BlowupTower P Q) (S : BlowupTower Q R) :
    IsEmptyTower S →
    ∀ {Y₁ Y₂ : CMfd.{0} (d+t)} {U₁ : BlowupTower X Y₁} {U₂ : BlowupTower X Y₂}
      {η₁ : R → Y₁} {η₂ : Q → Y₂},
      CoupledHistory N B J ι M (T.append S) U₁ η₁ →
      CoupledHistory N B J ι M T U₂ η₂ →
      ∃ e : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Y₂,
        (∀ y, U₂.proj (e y) = U₁.proj y) ∧
        (∀ r, e (η₁ r) = η₂ (S.proj r)) := by
  induction S with
  | refl =>
    intro _he Y₁ Y₂ U₁ U₂ η₁ η₂ hOne hOther
    obtain ⟨e,hIso,hη⟩ := exists_ambient_comparison_of_same_lower_history hOne hOther
    refine ⟨e,?_,?_⟩
    · intro y
      have h := hIso.proj_comm y
      exact h.symm
    · exact hη
  | @step Q₀ R₀ S C ρ hρ ih =>
    intro he Y₁ Y₂ U₁ U₂ η₁ η₂ hOne hOther
    obtain ⟨heS,hC⟩ := he
    subst C
    cases hOne with
    | @step _ _ Yprev _ _ Uprev ηprev _ _ Camb _ πamb _ hπamb hPrev hCentre hSq hEnd =>
      obtain ⟨ePrev,hProj,hEmb⟩ := ih heS hPrev hOther
      have hCamb : Camb = ∅ := by simpa only [image_empty] using hCentre
      have hπempty : IsBlowupAlong (d+t) (∅ : Set Yprev) πamb := by rw [← hCamb]; exact hπamb
      obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπempty
      let e := φ.trans ePrev
      refine ⟨e,?_,?_⟩
      · intro y
        change U₂.proj (ePrev (φ y)) = Uprev.proj (πamb y)
        simpa only [hφ y] using hProj (φ y)
      · intro r
        have hs := congrFun hSq r
        change πamb (η₁ r) = ηprev (ρ r) at hs
        change ePrev (φ (η₁ r)) = η₂ (S.proj (ρ r))
        rw [hφ,hs]
        exact hEmb (ρ r)

end
end Hironaka.HironakaG3EmptySuffixComparison
