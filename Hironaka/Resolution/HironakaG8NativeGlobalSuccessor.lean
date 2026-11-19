import Hironaka.Resolution.HironakaG8CompatibleNativeFirstCentre
import Hironaka.Resolution.HironakaActualHSConstantCentreBennett
import Hironaka.Invariant.ResolutionInvariantSeq

/-!
# A globally maximal native centre on a fixed ambient manifold

Common numerical invariant values on the actual overlaps give one
nonempty literal centre from the attained common maximum. The centre is
contained in the chosen closed footprint, is intrinsically singular, and
carries the prescribed Hilbert–Samuel profile on the original analytic set.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeGlobalSuccessor

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  HironakaEmbeddedBoundary HironakaResolutionSpaceLocal HironakaG8CompatibleLocalCentres
  ResolutionInvariantSpec ResolutionInvariantSeq
  ResolutionDriver ResolutionInvariantOrder

variable {n k : ℕ} {X : CMfd.{0} n} {I : Type} {Λ : Type} [LinearOrder Λ]

/-- An attained common maximum of the actual native window invariants gives
one proper singular-centred original-test blowup on the full boundary. -/
theorem exists_actual_native_global_maximum_blowup_along
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (U : I → Opens X) (F : Set X) (hF : IsClosed F)
    (hCover : ∀ x ∈ F, ∃ i, x ∈ U i)
    {B : I → CMfd.{0} n}
    (P : ∀ i, MarkedIdeal n (B i)) (T : ∀ i, BlowupTower (B i) (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain k (P i))
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (T i))
    (hE : ∀ i, (geoTransformAlong (P i) (T i)).E = E.map ((Subtype.val : U i → X) ⁻¹' ·))
    (H : ℕ → ℕ)
    (hCut : ∀ i (x : U i), x ∈ (geoTransformAlong (P i) (T i)).cosupp → x.val ∈ singularSet (n := n) W ∧
      ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x.val ℓ = H ℓ)
    (hFoot : ∀ i (x : U i), x ∈ (geoTransformAlong (P i) (T i)).cosupp → x.val ∈ F)
    (hOverlap : ∀ (i j) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (⟨x, hi⟩ : U i) ∈ (geoTransformAlong (P i) (T i)).cosupp →
        (⟨x, hj⟩ : U j) ∈ (geoTransformAlong (P j) (T j)).cosupp ∧
        R.inv (P i) (T i) ⟨x, hi⟩ = R.inv (P j) (T j) ⟨x, hj⟩)
    (m : Λ) (hUpper : ∀ i (x : U i), x ∈ (geoTransformAlong (P i) (T i)).cosupp → R.inv (P i) (T i) x ≤ m)
    (hAttain : ∃ (i : I) (x : U i), x ∈ (geoTransformAlong (P i) (T i)).cosupp ∧ R.inv (P i) (T i) x = m) :
    ∃ (C : Set X) (Y : CMfd.{0} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ F ∧ C ⊆ singularSet (n := n) W ∧
      IsProperMap π ∧
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
        (.step .refl C π hπ) ∧
      (∀ i, (Subtype.val : U i → X) ⁻¹' C =
        {x | x ∈ (geoTransformAlong (P i) (T i)).cosupp ∧ R.inv (P i) (T i) x = m}) ∧
      (∀ x ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ) ∧
      ∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ := by
  let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
  let L (i : I) : Set (U i) := {x | x ∈ (geoTransformAlong (P i) (T i)).cosupp ∧ R.inv (P i) (T i) x = m}
  let U' : Option I → Opens X
    | none => ⟨Fᶜ, hF.isOpen_compl⟩
    | some i => U i
  let L' : ∀ i, Set (U' i)
    | none => ∅
    | some i => L i
  have hCover' : ∀ x : X, ∃ i, x ∈ U' i := by
    intro x
    by_cases hx : x ∈ F
    · obtain ⟨i, hi⟩ := hCover x hx
      exact ⟨some i, hi⟩
    · exact ⟨none, hx⟩
  have hCompat : ∀ (i j : Option I) (x : X) (hi : x ∈ U' i) (hj : x ∈ U' j),
      (⟨x, hi⟩ : U' i) ∈ L' i ↔ (⟨x, hj⟩ : U' j) ∈ L' j := by
    intro i j x hi hj
    cases i with
    | none =>
      cases j with
      | none => exact Iff.rfl
      | some j =>
        exact ⟨fun h => False.elim h, fun h => False.elim (hi (hFoot j ⟨x, hj⟩ h.1))⟩
    | some i =>
      cases j with
      | none => exact ⟨fun h => False.elim (hj (hFoot i ⟨x, hi⟩ h.1)), fun h => False.elim h⟩
      | some j =>
        constructor
        · intro h
          obtain ⟨hs, hVal⟩ := hOverlap i j x hi hj h.1
          exact ⟨hs, hVal.symm.trans h.2⟩
        · intro h
          obtain ⟨hs, hVal⟩ := hOverlap j i x hj hi h.1
          exact ⟨hs, hVal.symm.trans h.2⟩
  have hNative (i : I) : (geoTransformAlong (P i) (T i)).IsAdmissibleCentre (L i) := by
    by_cases hne : (L i).Nonempty
    · obtain ⟨x, hx, hVal⟩ := hne
      have hMax : L i = maxLocus (R.inv (P i) (T i)) (geoTransformAlong (P i) (T i)).cosupp := by
        ext y
        constructor
        · rintro ⟨hy, hyVal⟩
          exact ⟨hy, fun z hz => (hUpper i z hz).trans_eq hyVal.symm⟩
        · rintro ⟨hy, hyMax⟩
          exact ⟨hy, le_antisymm (hUpper i y hy) (hVal.symm.trans_le (hyMax x hx))⟩
      rw [hMax]
      exact R.isInvValue.isAdmissibleCentre_maxLocus (hP i) (T i) (hCan i)
        (R.isInvValue.isGeoTestTower_of_isCanonical (hP i) (T i) (hCan i))
    · rw [not_nonempty_iff_eq_empty.mp hne]
      exact (geoTransformAlong (P i) (T i)).isAdmissibleCentre_empty
  have hLocal (i : Option I) :
      (MarkedIdeal.pullback (Subtype.val : U' i → X) M).IsAdmissibleCentre (L' i) := by
    cases i with
    | none => exact (MarkedIdeal.pullback (Subtype.val : U' none → X) M).isAdmissibleCentre_empty
    | some i =>
      change (MarkedIdeal.pullback (Subtype.val : U i → X) M).IsAdmissibleCentre (L i)
      rw [show M = (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) from rfl,
        pullback_val_mk_vanishingIdeal]
      refine ⟨(hNative i).1, ?_, ?_⟩
      · rw [cosupp_mk_vanishingIdeal (hW.isClosed.preimage continuous_subtype_val)]
        intro x hx
        exact singularSet_subset W (hCut i x ((hNative i).2.1 hx)).1
      · simpa only [hE i] using (hNative i).2.2
  let C := compatibleCentre U' L'
  have hAdm := compatibleCentre_admissible M (CartanIrreducible.cartanCoherence W hW)
    U' L' hCover' hCompat hLocal
  have hCN : C.Nonempty := by
    obtain ⟨i, x, hx, hVal⟩ := hAttain
    exact ⟨x.val, mem_iUnion.mpr ⟨some i, x, ⟨hx, hVal⟩, rfl⟩⟩
  have hCS : C ⊆ singularSet (n := n) W := by
    rintro _ hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    cases i with
    | none => exact False.elim hy
    | some i => exact (hCut i y hy.1).1
  have hCF : C ⊆ F := by
    rintro _ hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    cases i with
    | none => exact False.elim hy
    | some i => exact hFoot i y hy.1
  have hHS : ∀ x ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ := by
    rintro _ hx ℓ
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    cases i with
    | none => exact False.elim hy
    | some i => exact (hCut i y hy.1).2 ℓ
  have hInt : interior C = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact disjoint_left.mp (HironakaResolutionSpace.disjoint_interior_singularSet W)
      (interior_mono (hCS.trans (singularSet_subset _)) hx) (hCS (interior_subset hx))
  obtain ⟨Y, π, hπ⟩ := ResolutionDriver.exists_blowup C hAdm.1 hInt
  refine ⟨C, Y, π, hπ, hCN, hCF, hCS,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ, ⟨trivial, hAdm⟩,
    fun i => preimage_compatibleCentre U' L' hCompat (some i), hHS, ?_⟩
  exact HironakaActualHSConstantCentreBennett.hilbertSamuelAt_actual_hs_constant_smooth_centre_blowup_le
    hπ hAdm.1 hW (fun x hx y hy ℓ => (hHS x hx ℓ).trans (hHS y hy ℓ).symm)


/-- A compact nonempty union of the actual compatible window cosupports
supplies a common attained numerical maximum. -/
theorem exists_actual_native_compact_maximum_along
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (U : I → Opens X) (F : Set X) (hF : IsCompact F) (hNe : F.Nonempty)
    {B : I → CMfd.{0} n}
    (P : ∀ i, MarkedIdeal n (B i)) (T : ∀ i, BlowupTower (B i) (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain k (P i))
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (T i))
    (hCover : ∀ x ∈ F, ∃ (i : I) (hx : x ∈ U i), (⟨x, hx⟩ : U i) ∈ (geoTransformAlong (P i) (T i)).cosupp)
    (hFoot : ∀ i (x : U i), x ∈ (geoTransformAlong (P i) (T i)).cosupp → x.val ∈ F)
    (hOverlap : ∀ (i j) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (⟨x, hi⟩ : U i) ∈ (geoTransformAlong (P i) (T i)).cosupp →
        (⟨x, hj⟩ : U j) ∈ (geoTransformAlong (P j) (T j)).cosupp ∧
        R.inv (P i) (T i) ⟨x, hi⟩ = R.inv (P j) (T j) ⟨x, hj⟩) :
    ∃ m : Λ, (∀ i (x : U i), x ∈ (geoTransformAlong (P i) (T i)).cosupp → R.inv (P i) (T i) x ≤ m) ∧
      ∃ (i : I) (x : U i), x ∈ (geoTransformAlong (P i) (T i)).cosupp ∧ R.inv (P i) (T i) x = m := by
  classical
  choose index hOpen hLocal using hCover
  have hWitness := hNe
  obtain ⟨x₀, hx₀⟩ := hWitness
  let f (x : X) : Λ :=
    if hx : x ∈ F then R.inv (P (index x hx)) (T (index x hx)) ⟨x, hOpen x hx⟩
    else R.inv (P (index x₀ hx₀)) (T (index x₀ hx₀)) ⟨x₀, hOpen x₀ hx₀⟩
  have hVal (i : I) (z : U i) (hz : z ∈ (geoTransformAlong (P i) (T i)).cosupp) :
      f z.val = R.inv (P i) (T i) z := by
    have hzF := hFoot i z hz
    simp only [f, dif_pos hzF]
    exact (hOverlap i (index z.val hzF) z.val z.property (hOpen z.val hzF) hz).2.symm
  have hUSC : IsInvUSCOn f F := by
    intro x hx
    let i := index x hx
    let z : U i := ⟨x, hOpen x hx⟩
    have hz : z ∈ (geoTransformAlong (P i) (T i)).cosupp := hLocal x hx
    rw [← (U i).isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z, Filter.eventually_map]
    filter_upwards [(R.isInvValue.usc (P i) (hP i) (T i) (hCan i)) z hz] with y hy hyF
    have hyi := (hOverlap (index y.val hyF) i y.val (hOpen y.val hyF) y.property
      (hLocal y.val hyF)).1
    rw [hVal i y hyi, hVal i z hz]
    exact hy hyi
  obtain ⟨a, ha, hMax⟩ := hUSC.exists_isMaxOn hF hNe
  refine ⟨f a, ?_, index a ha, ⟨a, hOpen a ha⟩, hLocal a ha, ?_⟩
  · intro i x hx
    rw [← hVal i x hx]
    exact hMax x.val (hFoot i x hx)
  · exact (hVal (index a ha) ⟨a, hOpen a ha⟩ (hLocal a ha)).symm

/-- An attained common maximum of the actual native window invariants gives
one proper singular-centred original-test blowup on the full boundary. -/
theorem exists_actual_native_global_maximum_blowup
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (U : I → Opens X) (F : Set X) (hF : IsClosed F)
    (hCover : ∀ x ∈ F, ∃ i, x ∈ U i)
    (Q : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hQ : ∀ i, IsInvDomain k (Q i))
    (hE : ∀ i, (Q i).E = E.map ((Subtype.val : U i → X) ⁻¹' ·))
    (H : ℕ → ℕ)
    (hCut : ∀ i (x : U i), x ∈ (Q i).cosupp → x.val ∈ singularSet (n := n) W ∧
      ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x.val ℓ = H ℓ)
    (hFoot : ∀ i (x : U i), x ∈ (Q i).cosupp → x.val ∈ F)
    (hOverlap : ∀ (i j) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (⟨x, hi⟩ : U i) ∈ (Q i).cosupp →
        (⟨x, hj⟩ : U j) ∈ (Q j).cosupp ∧
        R.inv (Q i) .refl ⟨x, hi⟩ = R.inv (Q j) .refl ⟨x, hj⟩)
    (m : Λ) (hUpper : ∀ i (x : U i), x ∈ (Q i).cosupp → R.inv (Q i) .refl x ≤ m)
    (hAttain : ∃ (i : I) (x : U i), x ∈ (Q i).cosupp ∧ R.inv (Q i) .refl x = m) :
    ∃ (C : Set X) (Y : CMfd.{0} n) (π : Y → X) (hπ : IsBlowupAlong n C π),
      C.Nonempty ∧ C ⊆ F ∧ C ⊆ singularSet (n := n) W ∧
      IsProperMap π ∧
      IsGeoTestTower (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X)
        (.step .refl C π hπ) ∧
      (∀ i, (Subtype.val : U i → X) ⁻¹' C =
        {x | x ∈ (Q i).cosupp ∧ R.inv (Q i) .refl x = m}) ∧
      (∀ x ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ = H ℓ) ∧
      ∀ z ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ := by
  exact exists_actual_native_global_maximum_blowup_along R hW E U F hF hCover
    Q (fun _ => .refl) hQ (fun _ => trivial) hE H hCut hFoot hOverlap m hUpper hAttain

/-- A compact nonempty union of the actual compatible window cosupports
supplies a common attained numerical maximum. -/
theorem exists_actual_native_compact_maximum
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (U : I → Opens X) (F : Set X) (hF : IsCompact F) (hNe : F.Nonempty)
    (Q : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i))) (hQ : ∀ i, IsInvDomain k (Q i))
    (hCover : ∀ x ∈ F, ∃ (i : I) (hx : x ∈ U i), (⟨x, hx⟩ : U i) ∈ (Q i).cosupp)
    (hFoot : ∀ i (x : U i), x ∈ (Q i).cosupp → x.val ∈ F)
    (hOverlap : ∀ (i j) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (⟨x, hi⟩ : U i) ∈ (Q i).cosupp →
        (⟨x, hj⟩ : U j) ∈ (Q j).cosupp ∧
        R.inv (Q i) .refl ⟨x, hi⟩ = R.inv (Q j) .refl ⟨x, hj⟩) :
    ∃ m : Λ, (∀ i (x : U i), x ∈ (Q i).cosupp → R.inv (Q i) .refl x ≤ m) ∧
      ∃ (i : I) (x : U i), x ∈ (Q i).cosupp ∧ R.inv (Q i) .refl x = m := by
  exact exists_actual_native_compact_maximum_along R U F hF hNe
    Q (fun _ => .refl) hQ (fun _ => trivial) hCover hFoot hOverlap

end
end Hironaka.HironakaG8NativeGlobalSuccessor
