import Hironaka.Resolution.HironakaActualSingularBornCriticalBoundary
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Resolution.HironakaNormalCrossingsFiniteMarkedCompletion
import Hironaka.Analytic.VanishingIdealZeroLocus

/-! An actual born boundary germ cannot be contained in the current
strict carrier at one of its intrinsic singular points. -/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8BornBoundaryNoncontainment

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaEmbeddedReducible
  DivisorExponent DivisorExponentAlong GermIdealOrder

/-- Zero reduced exponent at an incident divisor excludes local containment
of that divisor when the original vanishing germ is nonzero. -/
theorem boundary_germ_noncontainment_of_zero_reduced_exponent
    {n : ℕ} {X : CMfd.{0} n} {W B : Set X} {x : X} (hxB : x ∈ B)
    (hNZ : IsNonzeroAlongAt univ (vanishingIdeal (n := n) W) x)
    (hZero : divExpAlong n univ (vanishingIdeal (n := n) W) B x = 0) :
    ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ W := by
  intro hContains
  have hHol : ∀ (y : X) f, (vanishingIdeal (n := n) W).mem y f → HolomorphicAt n f y :=
    fun _ _ hf => hf.1
  have hDiv : IsDivNear n (vanishingIdeal (n := n) W) B 1 x := by
    filter_upwards [hContains] with y hy hyB
    rw [cosupport_one hHol, univ_inter]
    exact VanishingIdealZeroLocus.subset_zeroLocus_vanishingIdeal W (hy hyB)
  have hNot := not_isDivNear_divExp_succ hHol hxB (isNonzeroAlongAt_univ_iff.mp hNZ)
  rw [divExpAlong_univ] at hZero
  rw [hZero] at hNot
  exact hNot hDiv

/-- At an intrinsic singular point, the ambient reduced vanishing ideal
has a nonzero germ. -/
theorem isNonzeroAlongAt_vanishingIdeal_of_singular
    {n : ℕ} {X : CMfd.{0} n} {W : Set X} {x : X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hx : x ∈ singularSet (n := n) W) :
    IsNonzeroAlongAt univ (vanishingIdeal (n := n) W) x := by
  apply isNonzeroAlongAt_vanishingIdeal_of_notMem_interior hW x
  intro hi
  exact (mem_singularSet_iff.mp hx).2 n
      (EmbeddedFromResolution.regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hi))

/-- For a literal original singular-centred test with empty initial
boundary, the entire current boundary meets the noncontainment condition
at every singular point of the actual strict transform. -/
theorem born_boundary_noncontainment_at_current_singular
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    (hStage : StageCentres (fun R C => C ⊆ singularSet (n := n) (strictTransform n R.proj W)) T) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
    let A := strictTransform n T.proj W
    ∀ B ∈ (geoTransformAlong M T).E, ∀ x ∈ singularSet (n := n) A, x ∈ B →
      ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ A := by
  let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
  let A := strictTransform n T.proj W
  let E := (geoTransformAlong M T).E
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, isSNCDivisor_nil,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
  have hE : IsSNCDivisor n E :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hTest).isSNCDivisor
  have hA : IsComplexAnalyticSubset (n := n) A :=
    HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  change ∀ B ∈ E, ∀ x ∈ singularSet (n := n) A, x ∈ B →
    ¬ ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ A
  intro B hB x hx hxB
  have hNZ := isNonzeroAlongAt_vanishingIdeal_of_singular hA hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hB
  have hBsm := hi ▸ MonomialPart.isClosedSubmanifold_get hn hE i
  have hBInv := hi ▸ HironakaNormalCrossingsFiniteMarkedCompletion.isInvertible_vanishingIdeal_snc_member hE i
  have hBorn : B ∈ (geoTransformAlong M T).E.drop M.E.length := by
    simpa only [show M.E = [] from rfl, List.length_nil, List.drop_zero] using hB
  have hZero := HironakaActualSingularBornCriticalBoundary.born_boundary_vanishing_exponent_zero
    M W hW T hStage B hBorn hBsm hBInv x hNZ
  exact boundary_germ_noncontainment_of_zero_reduced_exponent hxB hNZ hZero

end Hironaka.HironakaG8BornBoundaryNoncontainment
