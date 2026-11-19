import Hironaka.Resolution.HironakaActualCompactHSMaximalProfile
import Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel

/-! Maximal actual entire HS profiles and one common upper window on any
compact footprint, without compactness of the ambient analytic carrier. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8CompactFootprintMaxProfile
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaActualCompactHSMaximalProfile HironakaActualWholeAmbientHSSuperlevel
  HironakaHolomorphicJetChartInvariance
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- One actual maximum on a compact footprint yields the compact same-profile
footprint and one open neighborhood with a pointwise all-order upper bound. -/
theorem exists_compact_footprint_maximal_hs_window
    (A : GermIdeal n X) (hA : A.IsCoherent) (K : Set X)
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ a ∈ K,
      (∀ x ∈ K, toLex (hilbertSamuelAt A x) ≤ toLex (hilbertSamuelAt A a)) ∧
      let D := K ∩ actualWholeAmbientHSSuperlevel A (hilbertSamuelAt A a)
      D.Nonempty ∧ IsCompact D ∧
      D = {x | x ∈ K ∧ ∀ ell, hilbertSamuelAt A x ell = hilbertSamuelAt A a ell} ∧
      ∃ U : Opens X, D ⊆ U ∧
        (∀ x ∈ U, ∀ ell, hilbertSamuelAt A x ell ≤ hilbertSamuelAt A a ell) ∧
        actualWholeAmbientHSSuperlevel A (hilbertSamuelAt A a) ∩ (U : Set X) =
          {x | x ∈ U ∧ ∀ ell, hilbertSamuelAt A x ell = hilbertSamuelAt A a ell} := by
  obtain ⟨a,ha,hMax⟩ := exists_actual_compact_hs_lex_maximum A hA K hK hne
  let D := K ∩ actualWholeAmbientHSSuperlevel A (hilbertSamuelAt A a)
  have hDne : D.Nonempty := ⟨a,ha,fun _ => le_rfl⟩
  have hSuper := isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel A hA (hilbertSamuelAt A a)
  have hDK : IsCompact D := hK.of_isClosed_subset (hK.isClosed.inter hSuper.isClosed) inter_subset_left
  have hConst (x : X) (hx : x ∈ D) : ∀ ell, hilbertSamuelAt A x ell = hilbertSamuelAt A a ell := by
    have heq : toLex (hilbertSamuelAt A x) = toLex (hilbertSamuelAt A a) :=
      le_antisymm (hMax x hx.1) (Pi.toLex_monotone hx.2)
    exact fun ell => congrFun (congrArg ofLex heq) ell
  have hDEq : D = {x | x ∈ K ∧ ∀ ell, hilbertSamuelAt A x ell = hilbertSamuelAt A a ell} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,hConst x hx⟩
    · rintro ⟨hx,heq⟩
      exact ⟨hx,fun ell => (heq ell).ge⟩
  choose O hMem hUpper _hLex using fun x : D => exists_actual_entire_hs_pointwise_upper_window A hA x.val
  obtain ⟨s,hCover⟩ := hDK.elim_finite_subcover (fun x : D => (O x : Set X))
    (fun x => (O x).isOpen) (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hMem ⟨x,hx⟩⟩)
  let U : Opens X := ⟨⋃ x ∈ s,(O x : Set X),isOpen_iUnion fun x => isOpen_iUnion fun _ => (O x).isOpen⟩
  have hDU : D ⊆ U := hCover
  have hUpperU : ∀ x ∈ U, ∀ ell, hilbertSamuelAt A x ell ≤ hilbertSamuelAt A a ell := by
    intro x hx ell
    obtain ⟨p,_hp,hxp⟩ := mem_iUnion₂.mp hx
    exact (hUpper p x hxp ell).trans_eq (hConst p.val p.property ell)
  refine ⟨a,ha,hMax,hDne,hDK,hDEq,U,hDU,hUpperU,?_⟩
  ext x
  constructor
  · rintro ⟨hx,hU⟩
    exact ⟨hU,fun ell => le_antisymm (hUpperU x hU ell) (hx ell)⟩
  · rintro ⟨hU,heq⟩
    exact ⟨fun ell => (heq ell).ge,hU⟩
end
end Hironaka.HironakaG8CompactFootprintMaxProfile
