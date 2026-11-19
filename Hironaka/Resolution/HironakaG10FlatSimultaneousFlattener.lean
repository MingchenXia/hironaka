import Hironaka.Resolution.HironakaChowAnalyticUniversalFlattener
import Hironaka.Resolution.HironakaChowPresentationIndependentFlattener

/-! # Simultaneous local flattener for an arbitrary family of fibre points

The CANONICAL presentation-independent local flattener ideal satisfies the
universal flattening criterion for EVERY analytic base map and target ideal.
For an ARBITRARY family of relative presentations over the SAME base germ
(e.g. all points of a compact subset of one fibre) the SUM of the canonical
point ideals is finitely generated, is attained by an internally chosen FINITE
subfamily before all target maps, and characterizes simultaneous flatness.
Flatness at the finitely many selected points already forces flatness at every
point, after every analytic base change. Sum, not intersection.
No persistence at nearby base points, no openness of relative flatness and no
global flattening is claimed.
BP FIRST: hironaka-g10-flat-simultaneous-flattener.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology
namespace Hironaka.HironakaG10FlatSimultaneousFlattener
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBaseChangeCoefficients
  HironakaChowOriginalFlattenerCoefficients
  HironakaChowAnalyticPullbackCoefficientIdeal
  HironakaChowSameDivisionQuotientFlatness
  HironakaChowPresentationIndependentFlattener

section Algebra
variable {A B : Type*} [CommRing A] [CommRing B]

/-- ANY family of ideals of a Noetherian ring: an internally chosen FINITE
subfamily has the SAME supremum. -/
theorem exists_finset_iSup_eq [IsNoetherianRing A] {ι : Type*} (p : ι → Ideal A) :
    ∃ s : Finset ι, (⨆ i ∈ s, p i) = ⨆ i, p i := by
  have hc := (Submodule.fg_iff_compact (⨆ i, p i)).mp (IsNoetherian.noetherian _)
  obtain ⟨s,hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc p le_rfl
  exact ⟨s,le_antisymm (iSup₂_le fun i _ => le_iSup p i) hs⟩

/-- The pushed-forward SUM lies in a target ideal exactly when EVERY summand does. -/
theorem map_iSup_le_iff (f : A →+* B) {ι : Type*} (p : ι → Ideal A) (a : Ideal B) :
    Ideal.map f (⨆ i, p i) ≤ a ↔ ∀ i, Ideal.map f (p i) ≤ a := by
  simp only [Ideal.map_le_iff_le_comap, iSup_le_iff]

/-- The same for a bounded (e.g. finite-selection) sum, over ANY predicate. -/
theorem map_biSup_le_iff (f : A →+* B) {ι : Type*} (P : ι → Prop) (p : ι → Ideal A)
    (a : Ideal B) :
    Ideal.map f (⨆ (i) (_ : P i), p i) ≤ a ↔ ∀ i, P i → Ideal.map f (p i) ≤ a := by
  simp only [Ideal.map_le_iff_le_comap, iSup_le_iff]

end Algebra

variable (d : ℕ)
local instance (n : ℕ) :
    Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+n))) := tangentAlgebra d n

/-- The CANONICAL I-only ideal satisfies the universal criterion for EVERY
analytic base map and target ideal; no division or presentation is supplied. -/
theorem flat_iff_map_canonicalFlattenerIdeal_le (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (e : ℕ) (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (a : Ideal (HolGerm (ComplexModel e))) :
    Module.Flat (HolGerm (ComplexModel e) ⧸ a)
      (HolGerm (ComplexModel (e+t)) ⧸
        (Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I ⊔
          Ideal.map (tangentPullback e t).toRingHom a)) ↔
      Ideal.map (compAlgHom φ hφ hφ0).toRingHom (canonicalFlattenerIdeal d t I) ≤ a := by
  obtain ⟨P,eA,hEA,_hFG,_hOriginal⟩ := exists_original_quotient_flattening_ideal d t I
  obtain ⟨PB,eB,_hFib,_hWeight,_hBound,_hLift,hEB,_hRnat,_hWhole,hCoeff⟩ :=
    exists_base_changed_coefficient_ideal d e t I P eA hEA φ hφ hφ0
  rw [canonicalFlattenerIdeal_eq_coefficientIdeal d t I P eA hEA, ← hCoeff]
  exact flat_original_quotient_iff e t _ PB eB hEB a

/-- Over the ORIGINAL base (no base change) the canonical ideal is the criterion. -/
theorem flat_iff_canonicalFlattenerIdeal_le (t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (a : Ideal (HolGerm (ComplexModel d))) :
    Module.Flat (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)) ↔
      canonicalFlattenerIdeal d t I ≤ a := by
  obtain ⟨P,eA,hEA,_hFG,hOriginal⟩ := exists_original_quotient_flattening_ideal d t I
  rw [canonicalFlattenerIdeal_eq_coefficientIdeal d t I P eA hEA]
  exact hOriginal a

/-- The canonical ideal defines the LARGEST flat closed subgerm of the base:
the family is flat over its own quotient, and over A/a only if it lies in a. -/
theorem canonicalFlattenerIdeal_isLeast (t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    IsLeast {a : Ideal (HolGerm (ComplexModel d)) |
      Module.Flat (HolGerm (ComplexModel d) ⧸ a)
        (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a))}
      (canonicalFlattenerIdeal d t I) :=
  ⟨(flat_iff_canonicalFlattenerIdeal_le d t I _).mpr le_rfl,
    fun _ ha => (flat_iff_canonicalFlattenerIdeal_le d t I _).mp ha⟩

/-- Analytic base change preserves flatness of the ACTUAL analytic quotient: if
`S_A/(I+aS_A)` is flat over `A/a`, then for EVERY analytic `φ` and EVERY target
ideal `b` containing `φ*(a)`, the base-changed `S_B/(Φ*I+bS_B)` is flat over
`B/b`. No tensor identification is used; `I` and `a` are arbitrary. -/
theorem flat_baseChange_of_flat (t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : Ideal (HolGerm (ComplexModel d)))
    (hflat : Module.Flat (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+t)) ⧸ (I ⊔ Ideal.map (tangentPullback d t).toRingHom a)))
    (e : ℕ) (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (b : Ideal (HolGerm (ComplexModel e)))
    (hab : Ideal.map (compAlgHom φ hφ hφ0).toRingHom a ≤ b) :
    Module.Flat (HolGerm (ComplexModel e) ⧸ b)
      (HolGerm (ComplexModel (e+t)) ⧸
        (Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I ⊔
          Ideal.map (tangentPullback e t).toRingHom b)) :=
  (flat_iff_map_canonicalFlattenerIdeal_le d t I e φ hφ hφ0 b).mpr
    ((Ideal.map_mono ((flat_iff_canonicalFlattenerIdeal_le d t I a).mp hflat)).trans hab)

section Family
variable {L : Type*} (t : L → ℕ) (I : ∀ x : L, Ideal (HolGerm (ComplexModel (d + t x))))

/-- The SUM (not the intersection) of the canonical point ideals of an
arbitrary family of relative presentations over the SAME base germ. -/
def familyFlattenerIdeal : Ideal (HolGerm (ComplexModel d)) :=
  ⨆ x, canonicalFlattenerIdeal d (t x) (I x)

/-- Genuine analytic Noetherianity: the family ideal is finitely generated. -/
theorem familyFlattenerIdeal_fg : (familyFlattenerIdeal d t I).FG := by
  let : IsNoetherianRing (HolGerm (ComplexModel d)) := isNoetherianRing_holGerm_euclidean d
  exact Ideal.fg_of_isNoetherianRing _

/-- An internally chosen FINITE subcollection of points generates the SAME sum. -/
theorem exists_finset_familyFlattenerIdeal_eq :
    ∃ s : Finset L, (⨆ x ∈ s, canonicalFlattenerIdeal d (t x) (I x)) =
      familyFlattenerIdeal d t I := by
  let : IsNoetherianRing (HolGerm (ComplexModel d)) := isNoetherianRing_holGerm_euclidean d
  exact exists_finset_iSup_eq _

/-- Simultaneous universal criterion: after ANY analytic base change and for ANY
target ideal, EVERY member of the family is flat exactly when the pulled-back
SUM lies in the target ideal. -/
theorem forall_flat_iff_map_familyFlattenerIdeal_le
    (e : ℕ) (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (a : Ideal (HolGerm (ComplexModel e))) :
    (∀ x : L, Module.Flat (HolGerm (ComplexModel e) ⧸ a)
      (HolGerm (ComplexModel (e + t x)) ⧸
        (Ideal.map (jointBasePullback d e (t x) φ hφ hφ0).toRingHom (I x) ⊔
          Ideal.map (tangentPullback e (t x)).toRingHom a))) ↔
      Ideal.map (compAlgHom φ hφ hφ0).toRingHom (familyFlattenerIdeal d t I) ≤ a := by
  rw [familyFlattenerIdeal, map_iSup_le_iff]
  exact forall_congr' fun x =>
    flat_iff_map_canonicalFlattenerIdeal_le d (t x) (I x) e φ hφ hφ0 a

/-- ONE finite selection of points, chosen from the family alone BEFORE all
target maps and ideals: flatness at the selected points after ANY analytic base
change forces flatness at EVERY point of the family, and both are equivalent to
the containment of the pulled-back family ideal. -/
theorem exists_finite_selection_universal :
    ∃ s : Finset L, (⨆ x ∈ s, canonicalFlattenerIdeal d (t x) (I x)) =
        familyFlattenerIdeal d t I ∧
      ∀ (e : ℕ) (φ : ComplexModel e → ComplexModel d)
        (hφ : ∀ᶠ v in nhds (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
        (a : Ideal (HolGerm (ComplexModel e))),
        ((∀ x ∈ s, Module.Flat (HolGerm (ComplexModel e) ⧸ a)
          (HolGerm (ComplexModel (e + t x)) ⧸
            (Ideal.map (jointBasePullback d e (t x) φ hφ hφ0).toRingHom (I x) ⊔
              Ideal.map (tangentPullback e (t x)).toRingHom a))) ↔
        ∀ x : L, Module.Flat (HolGerm (ComplexModel e) ⧸ a)
          (HolGerm (ComplexModel (e + t x)) ⧸
            (Ideal.map (jointBasePullback d e (t x) φ hφ hφ0).toRingHom (I x) ⊔
              Ideal.map (tangentPullback e (t x)).toRingHom a))) ∧
        ((∀ x : L, Module.Flat (HolGerm (ComplexModel e) ⧸ a)
          (HolGerm (ComplexModel (e + t x)) ⧸
            (Ideal.map (jointBasePullback d e (t x) φ hφ hφ0).toRingHom (I x) ⊔
              Ideal.map (tangentPullback e (t x)).toRingHom a))) ↔
          Ideal.map (compAlgHom φ hφ hφ0).toRingHom (familyFlattenerIdeal d t I) ≤ a) := by
  obtain ⟨s,hs⟩ := exists_finset_familyFlattenerIdeal_eq d t I
  refine ⟨s,hs,fun e φ hφ hφ0 a => ⟨?_,forall_flat_iff_map_familyFlattenerIdeal_le d t I e φ hφ hφ0 a⟩⟩
  rw [forall_flat_iff_map_familyFlattenerIdeal_le d t I e φ hφ hφ0 a, ← hs]
  refine Iff.trans ?_ (map_biSup_le_iff _ (fun x => x ∈ s) _ a).symm
  exact forall₂_congr fun x _ =>
    flat_iff_map_canonicalFlattenerIdeal_le d (t x) (I x) e φ hφ hφ0 a

/-- Over the ORIGINAL base the family ideal is the LEAST target ideal over which
EVERY member of the family is flat: the largest simultaneous flat subgerm. -/
theorem familyFlattenerIdeal_isLeast :
    IsLeast {a : Ideal (HolGerm (ComplexModel d)) | ∀ x : L,
      Module.Flat (HolGerm (ComplexModel d) ⧸ a)
        (HolGerm (ComplexModel (d + t x)) ⧸
          (I x ⊔ Ideal.map (tangentPullback d (t x)).toRingHom a))}
      (familyFlattenerIdeal d t I) := by
  have key (a : Ideal (HolGerm (ComplexModel d))) :
      (∀ x : L, Module.Flat (HolGerm (ComplexModel d) ⧸ a)
        (HolGerm (ComplexModel (d + t x)) ⧸
          (I x ⊔ Ideal.map (tangentPullback d (t x)).toRingHom a))) ↔
        familyFlattenerIdeal d t I ≤ a := by
    rw [familyFlattenerIdeal, iSup_le_iff]
    exact forall_congr' fun x => flat_iff_canonicalFlattenerIdeal_le d (t x) (I x) a
  exact ⟨(key _).mpr le_rfl, fun _ ha => (key _).mp ha⟩

/-- Presentation independence of the family ideal: replacing EACH member by
ANY base-linearly equivalent whole original presentation (possibly of another
relative dimension) does not change the family ideal. -/
theorem familyFlattenerIdeal_eq_of_presentation_equiv (s : L → ℕ)
    (J : ∀ x : L, Ideal (HolGerm (ComplexModel (d + s x))))
    (E : ∀ x : L, (HolGerm (ComplexModel (d + t x)) ⧸ I x) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d + s x)) ⧸ J x)) :
    familyFlattenerIdeal d t I = familyFlattenerIdeal d s J := by
  unfold familyFlattenerIdeal
  exact iSup_congr fun x =>
    canonicalFlattenerIdeal_eq_of_presentation_equiv d (t x) (s x) (I x) (J x) (E x)

end Family

end
end Hironaka.HironakaG10FlatSimultaneousFlattener
