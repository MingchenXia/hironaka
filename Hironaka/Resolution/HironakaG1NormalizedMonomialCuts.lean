import Hironaka.Resolution.HironakaActualOriginalLowerChronologicalExponents
import Hironaka.Invariant.MonomialInvariant

/-! Actual marked powers scale the raw monomial keys and their marks. The
feasible subsets and their ordering are invariant under this cross-scaling. -/
set_option autoImplicit false
open Set Finset
namespace Hironaka.HironakaG1NormalizedMonomialCuts
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MonomialInvariant MonomialCase MonomialCaseAlong BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowerTransforms ResolutionInvariantSpec HironakaActualProjectionTestRecord MarkedIdealEquivalence.MarkedIdeal
  HironakaActualOriginalLowerChronologicalExponents.Generic

private theorem cross_sum (S K : Finset ℕ) (a b : ℕ → ℕ) (d e : ℕ)
    (hK : K ⊆ S) (h : ∀ i ∈ S, e * a i = d * b i) :
    e * ∑ i ∈ K, a i = d * ∑ i ∈ K, b i := by
  rw [Finset.mul_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => h i (hK hi)

/-- A positive cross-scaling preserves exactly the feasible original-member
subsets, including the empty set and all tie cases. -/
theorem normalized_feasible_eq (S : Finset ℕ) (a b : ℕ → ℕ) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (h : ∀ i ∈ S, e * a i = d * b i) :
    feasible S a d = feasible S b e := by
  ext K
  simp only [mem_feasible]
  constructor
  · rintro ⟨hK,hcut⟩
    refine ⟨hK,?_⟩
    have hs := cross_sum S K a b d e hK h
    nlinarith
  · rintro ⟨hK,hcut⟩
    refine ⟨hK,?_⟩
    have hs := cross_sum S K a b d e hK h
    nlinarith

/-- A positive cross-scaling preserves strict comparisons of the complete
monomial keys of any two subsets of the actual ordered boundary. -/
theorem normalized_key_lt_iff (n : ℕ) (S K L : Finset ℕ) (a b : ℕ → ℕ) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (hK : K ⊆ S) (hL : L ⊆ S)
    (h : ∀ i ∈ S, e * a i = d * b i) :
    key n a K < key n a L ↔ key n b K < key n b L := by
  have hsumK := cross_sum S K a b d e hK h
  have hsumL := cross_sum S L a b d e hL h
  have hlt : (∑ i ∈ K, a i) < ∑ i ∈ L, a i ↔ (∑ i ∈ K, b i) < ∑ i ∈ L, b i := by
    constructor <;> intro hcmp <;> nlinarith
  have heq : (∑ i ∈ K, a i) = ∑ i ∈ L, a i ↔ (∑ i ∈ K, b i) = ∑ i ∈ L, b i := by
    constructor <;> intro hcmp <;> nlinarith
  simp only [key_lt_key_iff, hlt, heq]

/-- The very same feasible member subset maximizes the original monomial
key on both sides of a positive cross-scaling. -/
theorem normalized_maximizing_key_iff (n : ℕ) (S K : Finset ℕ) (a b : ℕ → ℕ) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (h : ∀ i ∈ S, e * a i = d * b i) :
    (K ∈ feasible S a d ∧ ∀ L ∈ feasible S a d, key n a L ≤ key n a K) ↔
    (K ∈ feasible S b e ∧ ∀ L ∈ feasible S b e, key n b L ≤ key n b K) := by
  have hf := normalized_feasible_eq S a b d e hd he h
  rw [←hf]
  constructor
  · rintro ⟨hK,hmax⟩
    refine ⟨hK,?_⟩
    intro L hL
    have hKS := (mem_feasible.mp hK).1
    have hLS := (mem_feasible.mp hL).1
    have hlt := normalized_key_lt_iff n S K L a b d e hd he hKS hLS h
    exact le_of_not_gt fun hgt => (not_lt_of_ge (hmax L hL)) (hlt.mpr hgt)
  · rintro ⟨hK,hmax⟩
    refine ⟨hK,?_⟩
    intro L hL
    have hKS := (mem_feasible.mp hK).1
    have hLS := (mem_feasible.mp hL).1
    have hlt := normalized_key_lt_iff n S K L a b d e hd he hKS hLS h
    exact le_of_not_gt fun hgt => (not_lt_of_ge (hmax L hL)) (hlt.mp hgt)

/-- On every genuine common controlled history, the chronological
cross-exponent theorem gives the same maximizing original boundary subset
for both records, with their own native marks and whole boundary lists. -/
theorem chronological_maximizing_key_iff
    {n kA kB : ℕ} {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hE : A.E = B.E)
    (hProjected : WEquiv (projectionTest A) (projectionTest B))
    (hInitial : ∀ (i : Fin A.E.length) (x : X),
      B.d * DivisorExponentAlong.divExpAlong n A.N A.ideal (A.E.get i) x =
        A.d * DivisorExponentAlong.divExpAlong n B.N B.ideal (A.E.get i) x)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    (z : Y) (K : Finset ℕ) :
    let AR := geoTransformAlong A T
    let BR := geoTransformAlong B T
    let SA := memberIdx AR.E z
    let SB := memberIdx BR.E z
    let a := expDataAlong n AR.N AR.ideal AR.E z
    let b := expDataAlong n BR.N BR.ideal BR.E z
    (K ∈ feasible SA a AR.d ∧ ∀ L ∈ feasible SA a AR.d, key n a L ≤ key n a K) ↔
    (K ∈ feasible SB b BR.d ∧ ∀ L ∈ feasible SB b BR.d, key n b L ≤ key n b K) := by
  obtain ⟨hAR,hBR,_hNR,hER,_hDA,_hDB,_hLA,_hLB,_hOldA,_hOldB,_hBorn,hExp,_hTrace⟩ :=
    all_chronological_boundary_exponents A B hA hB hN hE hProjected hInitial T hTA hTB
  have hscale : ∀ i ∈ memberIdx (geoTransformAlong A T).E z,
      (geoTransformAlong B T).d * expDataAlong n (geoTransformAlong A T).N
        (geoTransformAlong A T).ideal (geoTransformAlong A T).E z i =
      (geoTransformAlong A T).d * expDataAlong n (geoTransformAlong B T).N
        (geoTransformAlong B T).ideal (geoTransformAlong B T).E z i := by
    intro i _
    exact hExp z i
  have hIdx : memberIdx (geoTransformAlong A T).E z = memberIdx (geoTransformAlong B T).E z := by rw [hER]
  dsimp only
  rw [←hIdx]
  exact normalized_maximizing_key_iff n _ K _ _ _ _ hAR.one_le_d hBR.one_le_d hscale
end Hironaka.HironakaG1NormalizedMonomialCuts
