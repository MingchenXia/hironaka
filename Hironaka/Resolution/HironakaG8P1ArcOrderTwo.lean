import Hironaka.Resolution.HironakaG8P1ArcNativeTangent

set_option autoImplicit false

/-!
# The order-two consequence of the actual native tangent comparison

The existing point-ideal derivative rule and Giraud flattening criterion
identify scalar order at least two with zero value and annihilation of
the intrinsic tangent space. The constructed native tangent equality
therefore compares the order-two cosupport of any original germ ideal.
No Taylor or Hadamard theorem is reproved here.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8P1ArcOrderTwo

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder IdealWeightPowers DerivativeIdeal GiraudAlong OrderTaylor
  HolomorphicTaylorTail BlowupSpaceTangent HadamardBridgeAlong
  HironakaActualProjectionTestRecord HironakaG8P1ArcPair HironakaG8P1ArcNativeTangent

open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)
open scoped Hironaka.ProductComplexManifold

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- Existing scalar order two annihilates the intrinsic native tangent
space: its point-ideal square has zero derivative, and its remaining
vanishing-ideal germ is killed by the common-kernel definition. -/
theorem germDiff_eq_zero_of_order_two {N : Set X} {x : X} {u : X → ℂ}
    (hu : HolomorphicAt n u x) (horder : VanishesToOrderOn n N x 2 u)
    {ξ : ComplexModel n} (hξ : ξ ∈ tangentSpace n N x) : germDiff n u x ξ = 0 := by
  obtain ⟨f, hf, huf⟩ := horder
  have hfh : HolomorphicAt n f x := holomorphicAt_of_mem_idealPow hf
  have hdiff : (vanishingIdeal (n := n) N).mem x (fun y => u y - f y) :=
    ⟨GiraudAlong.holomorphicAt_sub hu hfh, huf.mono fun y hy hyN => by
      change u y - f y = 0
      rw [hy hyN, sub_self]⟩
  have hdiff0 := germDiff_eq_zero_of_mem_tangentSpace hξ hdiff
  have hpoint : (idealPow (pointIdeal n x) 1).mem x
      (DerivativeIdeal.chartDeriv (complexChartAt (n := n) x) ξ f) :=
    chartDeriv_mem_idealPow (mem_complexChartAt_source x) 1 f hf
  have hf0 : germDiff n f x ξ = 0 := by
    have hz := apply_eq_zero_of_mem_idealPow_pointIdeal (x := x)
      (g := DerivativeIdeal.chartDeriv (complexChartAt (n := n) x) ξ f)
      (q := 1) (by decide) hpoint
    exact hz
  have hsub : germDiff n (fun y => u y - f y) x = germDiff n u x - germDiff n f x := by
    unfold germDiff
    exact fderiv_sub (differentiableAt_germ hu) (differentiableAt_germ hfh)
  rw [hsub, sub_apply, hf0, sub_zero] at hdiff0
  exact hdiff0

/-- At a regular carrier, zero value and annihilation of its intrinsic
tangent space give scalar order two, using the existing Giraud flattening
criterion with q=2 and the existing flat-vector tangent criterion. -/
theorem order_two_of_germDiff_eq_zero {N : Set X} {x : X} {u : X → ℂ} {r : ℕ}
    (hN : RegularAtDim (n := n) N x r) (hu : HolomorphicAt n u x) (hu0 : u x = 0)
    (hkill : ∀ ξ ∈ tangentSpace n N x, germDiff n u x ξ = 0) :
    VanishesToOrderOn n N x 2 u := by
  obtain ⟨_hr, hxN, Φ, hsrc, hzero, hflat⟩ := hN
  dsimp only [complexChartAt] at Φ hsrc hzero hflat
  apply vanishesToOrderOn_of_iterDeriv_flatten_eq_zero hsrc hzero hflat hu 2
  intro L hL
  rcases List.eq_nil_or_concat L with rfl | ⟨L', v, rfl⟩
  · change flatten Φ r u 0 = 0
    simp only [flatten, map_zero, flatInv_zero hzero, hu0]
  · have hlen : L'.length = 0 := by simp only [List.length_concat] at hL; omega
    have hnil : L' = [] := List.length_eq_zero_iff.mp hlen
    subst L'
    change dirDeriv v (flatten Φ r u) 0 = 0
    have hvec : flatVec Φ x (planeRetract r v) ∈ tangentSpace n N x := by
      apply (mem_tangentSpace_iff hsrc hflat (mem_flatDomain_self Φ) hxN).mpr
      intro i hi
      rw [germDiff_flatCoord_flatVec hsrc (mem_flatDomain_self Φ)]
      exact planeRetract_mem r v i hi
    have hzeroDeriv := hkill _ hvec
    rw [germDiff_flatVec hsrc (mem_flatDomain_self Φ) hu] at hzeroDeriv
    rw [hzero] at hzeroDeriv
    have hg : DifferentiableAt ℂ (u ∘ GiraudAlong.flatInv Φ) 0 :=
      differentiableAt_comp_flatInv (zero_mem_target hzero) hsrc
        (by rw [flatInv_zero hzero]; exact hu)
    change fderiv ℂ ((u ∘ GiraudAlong.flatInv Φ) ∘ planeRetract r) 0 v = 0
    rw [fderiv_comp _ (by simpa only [map_zero] using hg) (planeRetract r).differentiableAt,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, map_zero]
    exact hzeroDeriv

/-- Order at least two on a regular carrier is exactly zero value and
annihilation of its intrinsic native tangent space. -/
theorem order_two_iff_value_and_germDiff_zero {N : Set X} {x : X} {u : X → ℂ} {r : ℕ}
    (hN : RegularAtDim (n := n) N x r) (hu : HolomorphicAt n u x) :
    VanishesToOrderOn n N x 2 u ↔
      u x = 0 ∧ ∀ ξ ∈ tangentSpace n N x, germDiff n u x ξ = 0 := by
  constructor
  · intro h
    exact ⟨(vanishesToOrderOn_one_iff hN.2.1 hu).mp (h.mono (by decide)),
      fun _ hξ => germDiff_eq_zero_of_order_two hu h hξ⟩
  · rintro ⟨hu0, hkill⟩
    exact order_two_of_germDiff_eq_zero hN hu hu0 hkill

/-- Equal intrinsic native tangent spaces compare scalar order two on
regular carriers, without any assumption on the scalar germ's zero set. -/
theorem order_two_iff_of_tangentSpace_eq {N P : Set X} {x : X} {u : X → ℂ} {r s : ℕ}
    (hN : RegularAtDim (n := n) N x r) (hP : RegularAtDim (n := n) P x s)
    (hT : tangentSpace n N x = tangentSpace n P x) (hu : HolomorphicAt n u x) :
    VanishesToOrderOn n N x 2 u ↔ VanishesToOrderOn n P x 2 u := by
  rw [order_two_iff_value_and_germDiff_zero hN hu,
    order_two_iff_value_and_germDiff_zero hP hu, hT]

/-- The tangent comparison applies to every holomorphic germ of an
original ideal, hence to its literal order-two cosupport. -/
theorem cosupport_two_iff_of_tangentSpace_eq {N P : Set X} {x : X} {r s : ℕ}
    (hN : RegularAtDim (n := n) N x r) (hP : RegularAtDim (n := n) P x s)
    (hT : tangentSpace n N x = tangentSpace n P x)
    (I : GermIdeal n X) (hI : ∀ f, I.mem x f → HolomorphicAt n f x) :
    x ∈ cosupport n N I 2 ↔ x ∈ cosupport n P I 2 := by
  constructor
  · rintro ⟨_hx, h⟩
    exact ⟨hP.2.1, fun f hf => (order_two_iff_of_tangentSpace_eq hN hP hT (hI f hf)).mp (h f hf)⟩
  · rintro ⟨_hx, h⟩
    exact ⟨hN.2.1, fun f hf => (order_two_iff_of_tangentSpace_eq hN hP hT (hI f hf)).mpr (h f hf)⟩

/-- A member which is not tangent to a regular carrier gives an actual
member-ideal germ and an actual carrier tangent vector on which its
differential is nonzero. This supplies a proper linear kernel for generic
point selection, rather than assuming such a kernel as an input. -/
theorem exists_vanishing_germ_tangent_derivative_of_not_cosupport
    {N H : Set X} {x : X} {r : ℕ} (hN : RegularAtDim (n := n) N x r)
    (hxH : x ∈ H) (hnot : x ∉ cosupport n N (vanishingIdeal (n := n) H) 2) :
    ∃ f : X → ℂ, (vanishingIdeal (n := n) H).mem x f ∧
      ∃ ξ ∈ tangentSpace n N x, germDiff n f x ξ ≠ 0 := by
  classical
  have hex : ∃ f : X → ℂ, (vanishingIdeal (n := n) H).mem x f ∧
      ¬ VanishesToOrderOn n N x 2 f := by
    by_contra! hall
    exact hnot ⟨hN.2.1, hall⟩
  obtain ⟨f, hf, hbad⟩ := hex
  refine ⟨f, hf, ?_⟩
  by_contra! hkill
  exact hbad (order_two_of_germDiff_eq_zero hN hf.1 (hf.2.self_of_nhds hxH) hkill)

/-- The actual ordinary native pair construction proves the ideal-theoretic
order-two comparison used by the directrix clause (T'). The ideal can be
any original ideal whose germs are holomorphic at the point. -/
theorem cosupport_two_iff_of_native_pair_order_gt
    {kA kB : ℕ} (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hEB : B.E = A.E) (hdim : SameCarrierDim A B) {x : X} (hx : x ∈ A.cosupp)
    (A' B' : MarkedIdeal (n+1) (projectionAmbient X))
    (hsA : SameNID (projectionTest A) A') (hsB : SameNID (projectionTest B) B')
    (hW : WEquiv A' B') (hE' : IsSNCDivisor (n+1) A'.E)
    (hgreater : A.d < ordinaryTraceOrder A.N A.ideal x)
    (I : GermIdeal n X) (hI : ∀ f, I.mem x f → HolomorphicAt n f x) :
    x ∈ cosupport n A.N I 2 ↔ x ∈ cosupport n B.N I 2 := by
  have hT := tangentSpace_eq_of_native_pair_order_gt
    A B hA hB hEB hdim hx A' B' hsA hsB hW hE' hgreater
  obtain ⟨j, hjA⟩ := hA.isWellFormed.isClosedSubmanifold_N.2 x (A.cosupp_subset_N hx)
  have hjB := (hdim x hx j).mp hjA
  exact cosupport_two_iff_of_tangentSpace_eq hjA hjB hT I hI

end

end Hironaka.HironakaG8P1ArcOrderTwo
