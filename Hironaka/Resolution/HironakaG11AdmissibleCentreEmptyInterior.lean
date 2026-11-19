import Hironaka.Resolution.HironakaG8SuccExponents

set_option autoImplicit false

/-!
# Empty interior of an admissible centre

A positive-mark cosupport cannot contain an ambient neighborhood when the
coherent ideal is nonzero along its carrier at every carrier point. Therefore
any subset of that cosupport, including an admissible centre in an invariant
domain, has empty ambient interior.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11AdmissibleCentreEmptyInterior

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers GermIdealOrder DivisorExponentAlong HironakaG8SuccExponents HadamardBridge
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec InvDomainTowerAlong

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

/-- A subset of a positive cosupport has empty interior when the coherent
ideal is nonzero along its carrier at every carrier point. -/
theorem interior_eq_empty_of_cosupport_nonzero {N C : Set X} {I : GermIdeal n X} {d : ℕ}
    (hI : I.IsCoherent) (hd : 1 ≤ d) (hC : C ⊆ cosupport n N I d)
    (hnz : ∀ x ∈ N, IsNonzeroAlongAt N I x) : interior C = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxC : x ∈ C := interior_subset hx
  have hxN : x ∈ N := (hC hxC).1
  obtain ⟨g, hg, hfreq⟩ := hnz x hxN
  have hnearC : ∀ᶠ y in 𝓝 x, y ∈ C := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact interior_subset hy
  have hnearG : ∀ᶠ y in 𝓝 x, I.mem y g := eventually_mem_of_isCoherent hI hg
  obtain ⟨y, ⟨hyN, hyne⟩, hyC, hyg⟩ := (hfreq.and_eventually (hnearC.and hnearG)).exists
  have hycos : y ∈ cosupport n N I 1 := cosupport_anti hd (hC hyC)
  exact hyne (forall_eq_zero_of_mem_cosupport_one hycos g hyg)

/-- Every admissible centre of an invariant-domain marked ideal has empty
ambient interior. -/
theorem interior_eq_empty_of_invDomain_admissible {M : MarkedIdeal n X} {C : Set X} {k : ℕ}
    (hM : IsInvDomain k M) (hC : M.IsAdmissibleCentre C) : interior C = ∅ :=
  interior_eq_empty_of_cosupport_nonzero hM.isWellFormed.isCoherent hM.one_le_d hC.2.1
    hM.isNonzeroAlongAt

/-- A centre admissible after any test-tower prefix of an invariant-domain
marked ideal has empty ambient interior. -/
theorem interior_eq_empty_of_invDomain_test_tower_centre {M : MarkedIdeal n X} {k : ℕ}
    (hM : IsInvDomain k M) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {C : Set Y} (hC : (geoTransformAlong M T).IsAdmissibleCentre C) : interior C = ∅ :=
  interior_eq_empty_of_invDomain_admissible (isInvDomain_geoTransformAlong hM T hT) hC

end

end Hironaka.HironakaG11AdmissibleCentreEmptyInterior
