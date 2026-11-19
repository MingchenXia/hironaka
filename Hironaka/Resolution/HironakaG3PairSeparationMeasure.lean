import Hironaka.Resolution.HironakaOriginalCanonicalSumSeparation
import Hironaka.Resolution.HironakaOriginalLocalCanonicalSumSeparation
import Hironaka.Resolution.HironakaG3Nonerasure
import Hironaka.Resolution.HironakaG3MixedComponentOpen
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3PairSeparationMeasure
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaAdmissibleCalculus RestrictEmptyTower CanonicalCentres HironakaAdmissibleSequence
  HironakaOriginalCanonicalSumSeparation HironakaOriginalLocalCanonicalSumSeparation HironakaG3Nonerasure
  HironakaG3MixedComponentOpen
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- The finite count of distinct indexed pairs whose members still meet. -/
def intersectingPairs {k : ℕ} {X : Type*} (F : Fin k → Set X) : Finset (Fin k × Fin k) :=
  by
    classical
    exact Finset.univ.filter (fun p => p.1 < p.2 ∧ ¬ Disjoint (F p.1) (F p.2))

/-- Strict transform never creates a new intersecting pair of closed sets. -/
theorem intersectingPairs_strictTransform_subset {n k : ℕ}
    {X Y : CMfd.{0} n} (f : Y → X)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (F : Fin k → Set X) (hclosed : ∀ i, IsClosed (F i)) :
    intersectingPairs (fun i => strictTransform n f (F i)) ⊆ intersectingPairs F := by
  classical
  intro p hp
  simp only [intersectingPairs,Finset.mem_filter,Finset.mem_univ,true_and] at hp ⊢
  refine ⟨hp.1,?_⟩
  intro hd
  apply hp.2
  exact Disjoint.mono (strictTransform_subset_preimage hf.continuous (hclosed p.1))
    (strictTransform_subset_preimage hf.continuous (hclosed p.2)) (hd.preimage f)

/-- Separating one previously intersecting indexed pair strictly decreases
the actual intersection count, while no other pair can be newly created. -/
theorem intersectingPairs_strictTransform_card_lt {n k : ℕ}
    {X Y : CMfd.{0} n} (f : Y → X)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (F : Fin k → Set X) (hclosed : ∀ i, IsClosed (F i))
    {i j : Fin k} (hij : i < j) (hMeet : ¬ Disjoint (F i) (F j))
    (hSep : Disjoint (strictTransform n f (F i)) (strictTransform n f (F j))) :
    (intersectingPairs (fun i => strictTransform n f (F i))).card < (intersectingPairs F).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨intersectingPairs_strictTransform_subset f hf F hclosed,?_⟩
  intro heq
  have hmem : (i,j) ∈ intersectingPairs F := by
    simp only [intersectingPairs,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨hij,hMeet⟩
  rw [← heq] at hmem
  simp only [intersectingPairs,Finset.mem_filter,Finset.mem_univ,true_and] at hmem
  exact hmem.2 hSep

/-- A canonical separator for one compact pair gives an actual full-boundary
test tower and strictly decreases the finite mixed-component complexity. -/
theorem exists_canonical_pair_decrease {n k : ℕ} {X : CMfd.{0} n}
    (F : Fin k → Set X) (hF : ∀ i, IsComplexAnalyticSubset (n := n) (F i))
    {i j : Fin k} (hij : i < j) (hMeet : ¬ Disjoint (F i) (F j))
    (hint : interior (F i) = ∅) (hK : IsCompact (F i ∩ F j))
    (hijDense : F i ⊆ closure (F i \ F j)) (hjiDense : F j ⊆ closure (F j \ F i))
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    let M := sumMarkedIdeal (F i) (F j) E
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver (F i ∩ F j) T ∧ IsSNCDivisor n (geoTransformAlong M T).E ∧
      Disjoint (strictTransform n T.proj (F i)) (strictTransform n T.proj (F j)) ∧
      (intersectingPairs (fun a => strictTransform n T.proj (F a))).card < (intersectingPairs F).card := by
  obtain ⟨Y,T,hdom,hcan,hres,hcent,_hadm,hsnc,_hpull,_hsupp,hsep,_hhol,_hproper,_hsurj,_hiso,_hsources⟩ :=
    exists_canonical_sum_separation (hF i) (hF j) hint hK hijDense hjiDense E hE
  exact ⟨Y,T,hdom,hcan,hres,hcent,hsnc,hsep,
    intersectingPairs_strictTransform_card_lt T.proj T.contMDiff_proj F (fun a => (hF a).isClosed) hij hMeet hsep⟩

/-- On a precompact window the actual local canonical separator decreases
the intersection count of the literal restricted analytic family. -/
theorem exists_local_canonical_pair_decrease {n k : ℕ} {X : CMfd.{0} n}
    (F : Fin k → Set X) (hF : ∀ i, IsComplexAnalyticSubset (n := n) (F i))
    {i j : Fin k} (hij : i < j) (hint : interior (F i) = ∅)
    (hijDense : F i ⊆ closure (F i \ F j)) (hjiDense : F j ⊆ closure (F j \ F i))
    (E : List (Set X)) (hE : IsSNCDivisor n E) (U : Opens X)
    {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K)
    (hMeet : ¬ Disjoint ((Subtype.val : U → X) ⁻¹' F i) ((Subtype.val : U → X) ⁻¹' F j)) :
    let FU : Fin k → Set (CMfd.of (n := n) U) := fun a => (Subtype.val : U → X) ⁻¹' F a
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let M := sumMarkedIdeal (FU i) (FU j) EU
    ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver (FU i ∩ FU j) T ∧ IsSNCDivisor n (geoTransformAlong M T).E ∧
      Disjoint (strictTransform n T.proj (FU i)) (strictTransform n T.proj (FU j)) ∧
      (intersectingPairs (fun a => strictTransform n T.proj (FU a))).card < (intersectingPairs FU).card := by
  let FU : Fin k → Set (CMfd.of (n := n) U) := fun a => (Subtype.val : U → X) ⁻¹' F a
  obtain ⟨Y,T,hdom,hcan,hres,hcent,_hadm,hsnc,_hpull,_hsupp,hsep,_hhol,_hproper,_hsurj,_hiso,_hsources⟩ :=
    exists_local_canonical_sum_separation (hF i) (hF j) hint hijDense hjiDense E hE U hK hUK
  exact ⟨Y,T,hdom,hcan,hres,hcent,hsnc,hsep,
    intersectingPairs_strictTransform_card_lt T.proj T.contMDiff_proj FU
      (fun a => (hF a).isClosed.preimage continuous_subtype_val) hij hMeet hsep⟩


/-- If every labelled component is dense away from the selected intersection,
the same decreasing canonical tower preserves every whole component under
projection; it cannot erase a third component while separating the pair. -/
theorem exists_canonical_pair_decrease_preserving {n k : ℕ} {X : CMfd.{0} n}
    (F : Fin k → Set X) (hF : ∀ i, IsComplexAnalyticSubset (n := n) (F i))
    {i j : Fin k} (hij : i < j) (hMeet : ¬ Disjoint (F i) (F j))
    (hint : interior (F i) = ∅) (hK : IsCompact (F i ∩ F j))
    (hijDense : F i ⊆ closure (F i \ F j)) (hjiDense : F j ⊆ closure (F j \ F i))
    (hAllDense : ∀ a, F a ⊆ closure (F a \ (F i ∩ F j)))
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    let M := sumMarkedIdeal (F i) (F j) E
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver (F i ∩ F j) T ∧ IsSNCDivisor n (geoTransformAlong M T).E ∧
      Disjoint (strictTransform n T.proj (F i)) (strictTransform n T.proj (F j)) ∧
      (intersectingPairs (fun a => strictTransform n T.proj (F a))).card < (intersectingPairs F).card ∧
      ∀ a, T.proj '' strictTransform n T.proj (F a) = F a := by
  obtain ⟨Y,T,hdom,hcan,hres,hcent,hsnc,hsep,hdec⟩ :=
    exists_canonical_pair_decrease F hF hij hMeet hint hK hijDense hjiDense E hE
  refine ⟨Y,T,hdom,hcan,hres,hcent,hsnc,hsep,hdec,?_⟩
  let O : Opens X := ⟨(F i ∩ F j)ᶜ, ((hF i).isClosed.inter (hF j).isClosed).isOpen_compl⟩
  have hAvoid : CentresAvoid O T := centresAvoid_of_centresOver O disjoint_compl_left T hcent
  intro a
  have hDense : F a ⊆ closure (F a ∩ (O : Set X)) := by
    change F a ⊆ closure (F a ∩ (F i ∩ F j)ᶜ)
    simpa only [sdiff_eq] using hAllDense a
  have hEq := HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid
    (F a) (hF a).isClosed O hDense T hAvoid
  have hProj := projection_strictAlong_eq_of_centresAvoid (F a) (hF a).isClosed O hDense T hAvoid
  rw [hEq] at hProj
  exact hProj


private theorem irreducible_dense_off_one {n : ℕ} {X : CMfd.{0} n} {C H : Set X}
    (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (hH : IsComplexAnalyticSubset (n := n) H) (hNot : ¬ C ⊆ H) :
    C ⊆ closure (C \ H) := by
  have h := irreducible_dense_off_list hC [H] (by simpa using hH) (by simpa using hNot)
  simpa using h

/-- Distinct incomparable irreducible components need no supplied density
or non-erasure certificates: the actual canonical separator decreases the
intersection count and preserves every labelled component. -/
theorem exists_irreducible_canonical_pair_decrease {n k : ℕ} {X : CMfd.{0} n}
    (F : Fin k → Set X) (hI : ∀ a, IsComplexAnalyticallyIrreducible (n := n) (F a))
    (hDistinct : ∀ a b, a ≠ b → ¬ F a ⊆ F b)
    {i j : Fin k} (hij : i < j) (hMeet : ¬ Disjoint (F i) (F j))
    (hint : interior (F i) = ∅) (hK : IsCompact (F i ∩ F j))
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    let M := sumMarkedIdeal (F i) (F j) E
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver (F i ∩ F j) T ∧ IsSNCDivisor n (geoTransformAlong M T).E ∧
      Disjoint (strictTransform n T.proj (F i)) (strictTransform n T.proj (F j)) ∧
      (intersectingPairs (fun a => strictTransform n T.proj (F a))).card < (intersectingPairs F).card ∧
      (∀ a, T.proj '' strictTransform n T.proj (F a) = F a) ∧
      (∀ a b, a ≠ b → ¬ strictTransform n T.proj (F a) ⊆ strictTransform n T.proj (F b)) := by
  have hF : ∀ a, IsComplexAnalyticSubset (n := n) (F a) := fun a => (hI a).analytic
  have hne : i ≠ j := ne_of_lt hij
  have hDij := irreducible_dense_off_one (hI i) (hF j) (hDistinct i j hne)
  have hDji := irreducible_dense_off_one (hI j) (hF i) (hDistinct j i hne.symm)
  have hAll : ∀ a, F a ⊆ closure (F a \ (F i ∩ F j)) := by
    intro a
    by_cases hai : a = i
    · subst a
      exact hDij.trans (closure_mono (sdiff_subset_sdiff_right inter_subset_right))
    · have hD := irreducible_dense_off_one (hI a) (hF i) (hDistinct a i hai)
      exact hD.trans (closure_mono (sdiff_subset_sdiff_right inter_subset_left))
  obtain ⟨Y,T,hdom,hcan,hres,hcent,hsnc,hsep,hdec,hProj⟩ :=
    exists_canonical_pair_decrease_preserving F hF hij hMeet hint hK hDij hDji hAll E hE
  refine ⟨Y,T,hdom,hcan,hres,hcent,hsnc,hsep,hdec,hProj,?_⟩
  intro a b hab hsub
  apply hDistinct a b hab
  calc
    F a = T.proj '' strictTransform n T.proj (F a) := (hProj a).symm
    _ ⊆ T.proj '' strictTransform n T.proj (F b) := image_mono hsub
    _ = F b := hProj b


/-- A decreasing canonical separator retains the complete compact
irreducible-subvariety state for every labelled component, including its
original dimension and pairwise incomparability. -/
theorem exists_compact_subvariety_pair_decrease {n k : ℕ} {X : CMfd.{0} n}
    (V : Fin k → ClosedIrreducibleAnalyticSubvariety n X)
    (hCompact : ∀ a, IsCompact (V a).carrier)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    {i j : Fin k} (hij : i < j) (hMeet : ¬ Disjoint (V i).carrier (V j).carrier)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    let M := sumMarkedIdeal (V i).carrier (V j).carrier E
    ∃ (Y : CMfd.{0} n) (T : BlowupTower X Y)
      (V' : Fin k → ClosedIrreducibleAnalyticSubvariety n Y),
      IsInvDomain n M ∧ IsCanonical M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T ∧
      CentresOver ((V i).carrier ∩ (V j).carrier) T ∧
      IsSNCDivisor n (geoTransformAlong M T).E ∧
      (∀ a, (V' a).carrier = strictTransform n T.proj (V a).carrier) ∧
      (∀ a, (V' a).dim = (V a).dim) ∧
      (∀ a, IsCompact (V' a).carrier) ∧
      (∀ a b, a ≠ b → ¬ (V' a).carrier ⊆ (V' b).carrier) ∧
      (∀ a, T.proj '' (V' a).carrier = (V a).carrier) ∧
      (intersectingPairs (fun a => (V' a).carrier)).card <
        (intersectingPairs (fun a => (V a).carrier)).card := by
  let F : Fin k → Set X := fun a => (V a).carrier
  have hI : ∀ a, IsComplexAnalyticallyIrreducible (n := n) (F a) := fun a => (V a).irreducible_carrier
  have hK : IsCompact (F i ∩ F j) := (hCompact i).inter_right (V j).isClosed_carrier
  have hint : interior (F i) = ∅ := EmbeddedFromResolution.interior_eq_empty_of_dim_lt (V i) (hDim i)
  obtain ⟨Y,T,hdom,hcan,hres,hcent,hsnc,_hsep,hdec,hProj,hDistinctT⟩ :=
    exists_irreducible_canonical_pair_decrease F hI hDistinct hij hMeet hint hK E hE
  let O : Opens X := ⟨(F i ∩ F j)ᶜ, ((V i).isClosed_carrier.inter (V j).isClosed_carrier).isOpen_compl⟩
  have hAvoid : CentresAvoid O T := centresAvoid_of_centresOver O disjoint_compl_left T hcent
  have hExc : T.proj '' exceptionalLocus n T.proj ⊆ F i ∩ F j := by
    have h := EmbeddedFromResolution.image_exceptionalLocus_subset_compl O T hAvoid
    change T.proj '' exceptionalLocus n T.proj ⊆ ((F i ∩ F j)ᶜ)ᶜ at h
    simpa only [compl_compl] using h
  have hNot : ∀ a, ¬ F a ⊆ F i ∩ F j := by
    intro a h
    by_cases hai : a = i
    · subst a
      exact hDistinct i j (ne_of_lt hij) (h.trans inter_subset_right)
    · exact hDistinct a i hai (h.trans inter_subset_left)
  have hExist : ∀ a, ∃ W : ClosedIrreducibleAnalyticSubvariety n Y,
      W.carrier = strictTransform n T.proj (V a).carrier ∧ W.dim = (V a).dim := by
    intro a
    exact HironakaEmbeddedResolutionLocal.exists_strictTransform_subvariety_of_isBlowupSequence
      T.isBlowupSequence (V a) (fun hs => hNot a (hs.trans hExc))
  choose V' hCarrier hDim' using hExist
  refine ⟨Y,T,V',hdom,hcan,hres,hcent,hsnc,hCarrier,hDim',?_,?_,?_,?_⟩
  · intro a
    rw [hCarrier a]
    exact HironakaAdmissibleCalculus.isCompact_strictTransform T.isBlowupSequence (hCompact a)
  · intro a b hab
    rw [hCarrier a,hCarrier b]
    exact hDistinctT a b hab
  · intro a
    rw [hCarrier a]
    exact hProj a
  · simpa only [hCarrier] using hdec

end
end Hironaka.HironakaG3PairSeparationMeasure
