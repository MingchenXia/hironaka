import Hironaka.Resolution.HironakaG1InitialPositiveFiniteCentres

/-!
# Maxima on an arbitrary stratum of finite initial-cut anchors

Pairwise comparisons on the actual companions transport the entire
maximum locus of a selected stratum. The anchor map may identify labels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialPositiveStratumCentres

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue StepOneRegime
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualOpenZeroSectionDifferentials
  HironakaG1InitialPositiveFiniteCentres

section Stratum

variable {n k s : ℕ} {U : Opens (ComplexModel n)} {Q : MarkedIdeal n U}
  {Y : CMfd.{0} (n + 1)} {T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y}
  {A : Type*} (i : A → Y)

local notation "P" => properNormalMarked Q
local notation "f" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T

/-- The original maximum locus on the range of the actual anchor map is
the image of the normalized maximum locus. Pullback is exact even for
coincident labels, and every tie at the maximum is retained. -/
theorem initial_finite_stratum_max_loci
    (F : ∀ a : A, InitialFiniteRead Q T (i a) k s)
    (G : ∀ a : A, InitialNormalizedCompanion Q T (i a) k s)
    (mark : ℕ) (hMark : ∀ a, (G a).record.d = mark) :
    let g := fun a => (G a).value (F a)
    i '' maxLocus g univ = maxLocus f (range i) ∧
      i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
  intro g
  have hOrder (a b : A) : f (i a) ≤ f (i b) ↔ g a ≤ g b :=
    (InitialFiniteRead.upper_order_iff_normalized (F a) (F b) (G a) (G b)
      ((hMark a).trans (hMark b).symm)).2.1
  have hPre : i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
    ext a
    constructor
    · intro ha
      have hm : i a ∈ maxLocus f (range i) := ha
      exact ⟨mem_univ a, fun b _ => (hOrder b a).mp (hm.2 (i b) (mem_range_self b))⟩
    · intro ha
      refine ⟨mem_range_self a, ?_⟩
      rintro _ ⟨b, rfl⟩
      exact (hOrder b a).mpr (ha.2 b (mem_univ b))
  refine ⟨?_, hPre⟩
  rw [← hPre, image_preimage_eq_inter_range]
  exact inter_eq_left.mpr (fun _ h => h.1)

/-- The original full positive run and canonical prefix certify the
actual finite read at each anchor. The only comparison records supplied
here are the normalized companions, at one common mark. -/
theorem exists_initial_finite_stratum_max_loci (hQ : IsInvDomain (k + 1) Q)
    (hCan : IsCanonical P
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P) T)
    (hAnchor : ∀ a : A, i a ∈ (geoTransformAlong P T).cosupp ∧ level P T (i a) = s + 1 ∧
      ¬ IsSpecial P T (i a))
    (hRun : ∀ a : A, regimeRun (stepRegime P (s + 1)) T (i a) = T.length)
    (G : ∀ a : A, InitialNormalizedCompanion Q T (i a) k s)
    (mark : ℕ) (hMark : ∀ a, (G a).record.d = mark) :
    ∃ F : ∀ a : A, InitialFiniteRead Q T (i a) k s,
      let g := fun a => (G a).value (F a)
      i '' maxLocus g univ = maxLocus f (range i) ∧
        i ⁻¹' maxLocus f (range i) = maxLocus g univ := by
  let F (a : A) : InitialFiniteRead Q T (i a) k s :=
    Classical.choice (exists_initialFiniteRead Q T (i a) hQ hCan (hAnchor a).1
      (hAnchor a).2.1 (hAnchor a).2.2 (hRun a))
  exact ⟨F, initial_finite_stratum_max_loci i F G mark hMark⟩

end Stratum

end

end Hironaka.HironakaG1InitialPositiveStratumCentres
