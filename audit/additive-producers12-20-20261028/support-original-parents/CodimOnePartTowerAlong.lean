import TranscendentalNakamaye.Pending.CodimOneAdmissibleAlong
import TranscendentalNakamaye.Pending.CodimOnePartCanonical
import TranscendentalNakamaye.Pending.ContactEquivalenceAlong
import TranscendentalNakamaye.Pending.DerivativeIdealAlongTransform
import TranscendentalNakamaye.Pending.MarkedIdealOpenBiholomorphism
import TranscendentalNakamaye.Pending.DivisorExponentAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The codimension-one part along `N` along multiple test blow-ups

Hironaka phase H2 (TN3), for TN-CLASSICAL's Step 1b inside `N` (`hir:maximal-order-step`; claim
I-0977 C-0100).  Blueprint `bcalc:codim-one-part-tower`, `bcalc:codim-one-part-empty`,
`bcalc:contact-restriction-nonzero` (chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005
(`wlodarczyk05-hironaka`), Step 1b of Proposition `pr:resol`; Włodarczyk 2009
(`wlodarczyk09-analytic-resolution`) Step 1ba (printed p. 57).

In Step 1 of the algorithm for a marked ideal `(M, N, E, 𝔞, d)` of maximal order along `N`, Step 1ba
blows up the codimension-one part `Z₁ = codimOnePartAlong N 𝔞 d` of the cosupport along `N`, and
Step 1bb evaluates the invariant of the restriction `𝒮_w` of the coefficient ideal to a
hypersurface of maximal contact `N_T ∩ V(w)`.  The inductive invariant (`hir:centre-function`) is
only defined for marked ideals whose ideal vanishes identically on no nonempty open subset of their
submanifold.  This module proves that `𝒮_w` has that property at every stage after Step 1ba.

## Main results

* `codimOnePartAlong_geoTransformAlong_subset`: along every multiple test blow-up `T` of a
  well-formed marked ideal of maximal order along `N` with `d ≥ 1`, the codimension-one part along
  `N_T` lies over the original one: `Z₁(𝔪_T) ⊆ T⁻¹ Z₁(𝔪)`.  (Near each of its points `Z₁(𝔪_T)` is the
  strict transform of a hypersurface of maximal contact (TN-CLASSICAL's
  `MaximalContactAlongTower.exists_contact_along`), whose points off the last centre are dense in it;
  off the centre `Z₁` corresponds (`CodimOnePartCanonical`); induction on `T`.)
* `codimOnePartAlong_geoTransformAlong_eq_empty`: if `Z₁(𝔪) = ∅`, then `Z₁(𝔪_T) = ∅` along every
  multiple test blow-up.
* `codimOnePartAlong_geoTransform_codimOnePartAlong_eq_empty`: after Step 1ba (the blowup along
  `Z₁(𝔪)`) the codimension-one part of the transform is empty;
  `codimOnePartAlong_geoTransformAlong_append_eq_empty`: and it stays empty along every multiple
  test blow-up that starts with Step 1ba.
* `IsTangentDirectionAlong.exists_regularAtDim_succ`: at a point of a hypersurface of maximal contact
  `N ∩ V(u) ∩ U`, `N` is regular of some dimension `k + 1` and the hypersurface of dimension `k`.
* `eventually_forall_eq_zero_of_not_isNonzeroAlongAt`: if no germ of a coherent ideal at `y` is
  nonzero on `A` near `y`, the ideal vanishes on `A` near every point near `y`.
* `isNonzeroAlongAt_of_notMem_codimOnePartAlong`: let `A` be regular of dimension `k` at `y` where `N`
  is regular of dimension `k + 1`, with `cosupp(𝔞|_N, μ) ⊆ A` and `cosupp(𝔟|_A, ν) ⊆ cosupp(𝔞|_N, μ)`
  near `y`, `𝔟` coherent.  If `y ∉ Z₁(N, 𝔞, μ)`, then `𝔟|_A` does not vanish near `y`
  (`DivisorExponentAlong.IsNonzeroAlongAt`).
* `isNonzeroAlongAt_contact_open`: for TN23's contact equivalence
  (`ContactEquivalenceAlong.contact_wEquiv_open_along`) `𝔪|_U ≃ 𝒮_u = (U, N ∩ V(u), E, 𝓒_N(𝔞), μ_𝓒)`, at
  every point of `N ∩ V(u) ∩ U` off `Z₁(𝔪)` the ideal of `𝒮_u` is nonzero along its submanifold;
  `isNonzeroAlongAt_contact_open_geoTransformAlong`: hence at every stage of a multiple test blow-up
  of a marked ideal with `Z₁ = ∅`, for every tangent direction of the transform on an open set.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Pending.RelativePrincipalization` or `Pending.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace TranscendentalNakamaye.Pending.CodimOnePartTowerAlong

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open TranscendentalNakamaye.Pending.MarkedIdeals TranscendentalNakamaye.Pending.MarkedIdeals.MarkedIdeal
  TranscendentalNakamaye.Pending.BlowupTowers TranscendentalNakamaye.Pending.BlowupTowerTransforms
  TranscendentalNakamaye.Pending.HomogenizedGlueingTower TranscendentalNakamaye.Pending.MarkedIdealRestrictOpen
  TranscendentalNakamaye.Pending.CodimOneSupportAlong TranscendentalNakamaye.Pending.MarkedIdealBiholomorphism
  TranscendentalNakamaye.Pending.CodimOnePartCanonical TranscendentalNakamaye.Pending.GermIdealOrder
  TranscendentalNakamaye.Pending.HomogenizedIdealAlong TranscendentalNakamaye.Pending.TangentDirectionAlong
  TranscendentalNakamaye.Pending.MaximalContactAlongTower TranscendentalNakamaye.Pending.TransformOffCentre
  TranscendentalNakamaye.Pending.DivisorExponentAlong TranscendentalNakamaye.Pending.CoefficientIdealRestriction
  TranscendentalNakamaye.Pending.MarkedIdealEquivalence TranscendentalNakamaye.Pending.ContactEquivalenceAlong
  TranscendentalNakamaye.Pending.GiraudAlong TranscendentalNakamaye.Pending.BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ}

/-! ### The codimension-one part along towers -/

section Tower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

/-- **The codimension-one part along `N_T` lies over the original one.**  Let `𝔪 = (X, N, E, 𝔞, d)` be
well formed, of maximal order along `N`, `d ≥ 1`, and `T` a multiple test blow-up.  Then
`Z₁(𝔪_T) ⊆ T⁻¹ Z₁(𝔪)`.  Near a point `x ∈ Z₁(𝔪_T)` the codimension-one part is `N_T ∩ V(w)`
(`CodimOneSupportAlong`), the strict transform of a hypersurface of maximal contact `A = N ∩ V(u) ∩ U`
(`MaximalContactAlongTower.exists_contact_along`); after the last blowup `π` along `C`, the strict
transform of `A` is the closure of `π⁻¹(A_T \ C)`, so `x` is a limit of points `y ∈ Z₁(𝔪_T)` with
`π y ∉ C`, at which `Z₁` corresponds (`CodimOnePartCanonical.mem_codimOnePartAlong_geoTransformAlong_step_iff`)
and the induction hypothesis applies; `Z₁(𝔪)` is closed. -/
theorem codimOnePartAlong_geoTransformAlong_subset (h𝔪 : 𝔪.IsWellFormed) (hμ : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔪 T →
      codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
        (geoTransformAlong 𝔪 T).d ⊆ T.proj ⁻¹' codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d
  | _, .refl, _ => fun _ hx => hx
  | _, .step T C π hπ, hT => by
      intro x hx
      have hN := h𝔪.isClosedSubmanifold_N
      have h𝔞 := h𝔪.isCoherent
      obtain ⟨hT0, -⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      set T' : BlowupTower X _ := .step T C π hπ with hT'
      obtain ⟨hNT, h𝔞T⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T' hT
      have hx' : x ∈ codimOnePartAlong (geoTransformAlong 𝔪 T').N (geoTransformAlong 𝔪 T').ideal 𝔪.d := by
        rw [← d_geoTransformAlong 𝔪 T']; exact hx
      have hxS : x ∈ cosupport n (geoTransformAlong 𝔪 T').N (geoTransformAlong 𝔪 T').ideal 𝔪.d :=
        codimOnePartAlong_subset hx'
      have hx0 : T'.proj x ∈ 𝔪.cosupp := cosupp_geoTransformAlong_subset 𝔪 hN h𝔞 T' hT (by
        show x ∈ cosupport n (geoTransformAlong 𝔪 T').N (geoTransformAlong 𝔪 T').ideal
          (geoTransformAlong 𝔪 T').d
        rw [d_geoTransformAlong]; exact hxS)
      obtain ⟨U, u, hxU, hu⟩ := exists_isTangentDirectionAlong h𝔞 hN hμ hx0
        fun h => hmax (T'.proj x) ⟨hx0.1, h⟩
      obtain ⟨O, w, hxO, hO, -, hw, hwD, hw1, hwA⟩ :=
        exists_contact_along 𝔪 hN h𝔞 hμ hu T' hT x hxS.1 hxU
      have hR := eventually_mem_codimOnePartAlong_iff_eq_zero_of_isInSpanOnAt h𝔞T hNT hμ hO hw hwD hw1
        hxO hx'
      set A : Set X := 𝔪.N ∩ {y | u y = 0} ∩ U with hA
      have hAN : A ⊆ 𝔪.N := fun _ hy => hy.1.1
      have hxw : x ∈ (geoTransformAlong 𝔪 T').N ∧ w x = 0 := hR.self_of_nhds.mp hx'
      have hxA : x ∈ closure (π ⁻¹' (strictAlong T A \ C)) := (hwA x hxO hxw.1).mp hxw.2
      have hZc : IsClosed (T'.proj ⁻¹' codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) :=
        (isClosed_codimOnePartAlong h𝔞 hN hμ hmax).preimage T'.contMDiff_proj.continuous
      rw [← hZc.closure_eq, mem_closure_iff_nhds]
      intro t ht
      obtain ⟨y, ⟨⟨hyt, hyR⟩, hyO⟩, hyA, hyC⟩ :=
        mem_closure_iff_nhds.mp hxA _ (inter_mem (inter_mem ht hR) (hO.mem_nhds hxO))
      have hyA' : y ∈ strictAlong T' A := subset_closure ⟨hyA, hyC⟩
      have hyN : y ∈ (geoTransformAlong 𝔪 T').N := strictAlong_subset_N 𝔪 hAN T' hyA'
      have hyZ : y ∈ codimOnePartAlong (geoTransformAlong 𝔪 T').N (geoTransformAlong 𝔪 T').ideal
          (geoTransformAlong 𝔪 T').d := by
        rw [d_geoTransformAlong]
        exact hyR.mpr ⟨hyN, (hwA y hyO hyN).mpr hyA'⟩
      have hπy := (mem_codimOnePartAlong_geoTransformAlong_step_iff hN h𝔞 T hT0 C π hπ hyC).mp hyZ
      exact ⟨y, hyt, codimOnePartAlong_geoTransformAlong_subset h𝔪 hμ hmax T hT0 hπy⟩

/-- **If the codimension-one part along `N` is empty, it stays empty along every multiple test
blow-up** (`𝔪` well formed, of maximal order along `N`, `d ≥ 1`). -/
theorem codimOnePartAlong_geoTransformAlong_eq_empty (h𝔪 : 𝔪.IsWellFormed) (hμ : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) (hZ : codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d = ∅)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) :
    codimOnePartAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
      (geoTransformAlong 𝔪 T).d = ∅ := by
  have h := codimOnePartAlong_geoTransformAlong_subset 𝔪 h𝔪 hμ hmax T hT
  rw [hZ, preimage_empty] at h
  exact subset_empty_iff.mp h

end Tower

/-! ### Step 1ba -/

section Step

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {π : Y → X}

/-- **After Step 1ba the codimension-one part is empty**: for `𝔪` with `N` a closed submanifold, `𝔞`
coherent, `d ≥ 1`, of maximal order along `N`, and `π` the blowup along `Z₁(𝔪)`, the codimension-one
part along `N'` of the cosupport of the transform is empty.  (Over `Z₁(𝔪)` the cosupport of the transform
is empty (`CodimOneSupportAlong.cosupp_geoTransform_inter_preimage_codimOnePartAlong_eq_empty`); off
it `Z₁` corresponds (`CodimOnePartCanonical.mem_codimOnePartAlong_geoTransform_iff`).) -/
theorem codimOnePartAlong_geoTransform_codimOnePartAlong_eq_empty (𝔪 : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d)
    (hπ : IsBlowupAlong n (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π) :
    codimOnePartAlong (𝔪.geoTransform (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π).N
      (𝔪.geoTransform (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π).ideal
      (𝔪.geoTransform (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π).d = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  have hzS := codimOnePartAlong_subset hz
  by_cases hzC : π z ∈ codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d
  · have h := cosupp_geoTransform_inter_preimage_codimOnePartAlong_eq_empty hN h𝔞 hd hmax hπ
    exact (eq_empty_iff_forall_notMem.mp h) z ⟨hzS, hzC⟩
  · exact hzC ((mem_codimOnePartAlong_geoTransform_iff 𝔪 hN.1
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg) hπ hzC).mp hz)

end Step

section StepTower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X)

/-- **After Step 1ba the codimension-one part stays empty**: for `𝔪` well formed, of maximal order along
`N`, `d ≥ 1`, `π` the blowup along `Z₁(𝔪)` and `S` a tower over its source such that `π` followed by `S`
is a multiple test blow-up of `𝔪`, the codimension-one part along `N` of the transform of `𝔪` along
this tower is empty. -/
theorem codimOnePartAlong_geoTransformAlong_append_eq_empty (h𝔪 : 𝔪.IsWellFormed) (hμ : 1 ≤ 𝔪.d)
    (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) {Y₁ : CMfd.{u} n} (π : Y₁ → X)
    (hπ : IsBlowupAlong n (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π) {Y : CMfd.{u} n}
    (S : BlowupTower Y₁ Y)
    (hS : IsGeoTestTower 𝔪 ((BlowupTower.step .refl (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π hπ).append S)) :
    codimOnePartAlong
      (geoTransformAlong 𝔪 ((BlowupTower.step .refl (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π hπ).append S)).N
      (geoTransformAlong 𝔪
        ((BlowupTower.step .refl (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π hπ).append S)).ideal
      (geoTransformAlong 𝔪
        ((BlowupTower.step .refl (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π hπ).append S)).d = ∅ := by
  set T₁ : BlowupTower X Y₁ := .step .refl (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) π hπ with hT₁
  obtain ⟨hT₁t, hSt⟩ := (isGeoTestTower_append_iff 𝔪 T₁ S).mp hS
  have hN := h𝔪.isClosedSubmanifold_N
  have h𝔞 := h𝔪.isCoherent
  have hC : 𝔪.IsAdmissibleCentre (codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) := hT₁t.2
  have hW₁ : (geoTransformAlong 𝔪 T₁).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h𝔪 T₁ hT₁t
  have hd₁ : 1 ≤ (geoTransformAlong 𝔪 T₁).d := by rw [d_geoTransformAlong]; exact hμ
  have hmax₁ : IsMaximalOrderAlong (geoTransformAlong 𝔪 T₁).N (geoTransformAlong 𝔪 T₁).ideal
      (geoTransformAlong 𝔪 T₁).d := by
    rw [d_geoTransformAlong]
    exact DerivativeIdealAlongTransform.isMaximalOrderAlong_geoTransform 𝔪 hN h𝔞 hC hπ hmax
  have hZ₁ : codimOnePartAlong (geoTransformAlong 𝔪 T₁).N (geoTransformAlong 𝔪 T₁).ideal
      (geoTransformAlong 𝔪 T₁).d = ∅ :=
    codimOnePartAlong_geoTransform_codimOnePartAlong_eq_empty 𝔪 hN h𝔞 hμ hmax hπ
  rw [geoTransformAlong_append]
  exact codimOnePartAlong_geoTransformAlong_eq_empty (geoTransformAlong 𝔪 T₁) hW₁ hd₁ hmax₁ hZ₁ S hSt

end StepTower

/-! ### The restriction to a hypersurface of maximal contact is nonzero off the codimension-one part -/

section Nonzero

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A hypersurface of maximal contact has dimension one less than `N`, which is at least one**: at a
point of `N ∩ V(u) ∩ U` for a tangent direction `u` of `(𝔞|_N, μ)` along the closed submanifold `N` on
`U`, `N` is regular of some dimension `k + 1` and `N ∩ V(u) ∩ U` of dimension `k`. -/
theorem IsTangentDirectionAlong.exists_regularAtDim_succ {N : Set M} {𝔞 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (hN : IsClosedSubmanifold n N) {μ : ℕ} {U : Set M}
    {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {y : M} (hy : y ∈ N ∩ {y | u y = 0} ∩ U) :
    ∃ k, RegularAtDim (n := n) N y (k + 1) ∧ RegularAtDim (n := n) (N ∩ {y | u y = 0} ∩ U) y k := by
  obtain ⟨k, hk, hk'⟩ := hu.regularAtDim_contact h𝔞 hN hy
  obtain ⟨⟨hyN, hyu⟩, hyU⟩ := hy
  have hk2 := hk
  obtain ⟨-, -, Φ, hΦsrc, -, hflat⟩ := hk2
  obtain ⟨e, ξ, hξ, hne⟩ := hu.multiplicity_one y hyU hyu
  have huhol : HolomorphicAt n u y :=
    holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (μ - 1) y u (hu.mem y hyU)
  obtain ⟨j, hj, -⟩ := TangentDirectionAlong.exists_flatPartial_ne_zero hΦsrc hflat
    (BlowupFlatCoordinates.mem_flatDomain_self Φ) hyN huhol hξ hne
  refine ⟨k - 1, ?_, hk'⟩
  rw [Nat.sub_add_cancel (by omega)]
  exact hk

/-- **A coherent ideal none of whose germs at `y` is nonzero on `A` near `y` vanishes on `A` near every
point near `y`.** -/
theorem eventually_forall_eq_zero_of_not_isNonzeroAlongAt {A : Set M} {𝔟 : GermIdeal n M}
    (h𝔟 : 𝔟.IsCoherent) {y : M} (h : ¬ IsNonzeroAlongAt A 𝔟 y) :
    ∀ᶠ z in 𝓝 y, ∀ g, 𝔟.mem z g → ∀ᶠ z' in 𝓝 z, z' ∈ A → g z' = 0 := by
  obtain ⟨U, hUo, hyU, K, s, hs, hgen⟩ := h𝔟 y
  have hsy : ∀ i, ∀ᶠ z in 𝓝 y, z ∈ A → s i z = 0 := fun i => by
    have hmem : 𝔟.mem y (s i) := (hgen y hyU _).mpr (isInSpanAt_of_eq_mul ⟨i, rfl⟩
      (DivisorExponent.holomorphicAt_of_mdifferentiableOn_open hUo (hs i) hyU) (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => (one_mul _).symm))
    have h' : ¬ ∃ᶠ z in 𝓝 y, z ∈ A ∧ s i z ≠ 0 := fun hf => h ⟨s i, hmem, hf⟩
    rw [not_frequently] at h'
    filter_upwards [h'] with z hz hzA
    by_contra hne
    exact hz ⟨hzA, hne⟩
  filter_upwards [hUo.mem_nhds hyU, (eventually_all.mpr hsy).eventually_nhds] with z hzU hz g hg
  obtain ⟨-, K', t, a, ht, -, hga⟩ := (hgen z hzU g).mp hg
  filter_upwards [hga, hz] with z' hz'g hz' hz'A
  rw [hz'g]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨i, hi⟩ := ht j
  rw [← hi, hz' i hz'A, mul_zero]

/-- **Off the codimension-one part the restriction to a hypersurface containing the cosupport is
nonzero.**  Let `A` be regular of dimension `k` at `y`, where `N` is regular of dimension `k + 1`, assume
that near `y` the cosupport of `(𝔞|_N, μ)` lies in `A` and the cosupport of `(𝔟|_A, ν)` in that of
`(𝔞|_N, μ)`, and that `𝔟` is coherent.  If `y` is not in the codimension-one part `Z₁(N, 𝔞, μ)`, then
`𝔟|_A` does not vanish near `y`: otherwise `𝔟` vanishes on `A` near `y`, every point of `A` near `y` lies in
the cosupport of `(𝔟|_A, ν)`, hence in that of `(𝔞|_N, μ)`, which therefore agrees with `A` near `y` and
is regular of dimension `k` there. -/
theorem isNonzeroAlongAt_of_notMem_codimOnePartAlong {N A : Set M} {𝔞 𝔟 : GermIdeal n M} {μ ν k : ℕ}
    (h𝔟 : 𝔟.IsCoherent) {y : M} (hN : RegularAtDim (n := n) N y (k + 1))
    (hA : RegularAtDim (n := n) A y k) (hsub : ∀ᶠ z in 𝓝 y, z ∈ cosupport n N 𝔞 μ → z ∈ A)
    (hcos : ∀ᶠ z in 𝓝 y, z ∈ cosupport n A 𝔟 ν → z ∈ cosupport n N 𝔞 μ)
    (hy : y ∉ codimOnePartAlong N 𝔞 μ) : IsNonzeroAlongAt A 𝔟 y := by
  by_contra h
  refine hy ((mem_codimOnePartAlong_iff_of_eventually (A := N) (S := A)
    (Eventually.of_forall fun _ => Iff.rfl) ?_).mpr ⟨k, hN, hA⟩)
  filter_upwards [hsub, hcos, eventually_forall_eq_zero_of_not_isNonzeroAlongAt h𝔟 h] with z h1 h2 h3
  exact ⟨h1, fun hzA => h2 ⟨hzA, fun g hg => ⟨fun _ => 0, zero_mem_idealPow _ z ν, h3 g hg⟩⟩⟩

end Nonzero

section Contact

variable {X : CMfd.{u} n}

/-- **Step 1bb's restricted marked ideal is nonzero along its submanifold off the codimension-one
part.**  Let `𝔪 = (X, N, E, 𝔞, d)` have `N` a closed submanifold, `𝔞` coherent, `d ≥ 1`, and let `u` be a
tangent direction of `(𝔞|_N, d)` along `N` on an open `U`.  For TN23's restricted marked ideal
`𝒮_u = (U, N ∩ V(u), E|_U, 𝓒_N(𝔞)|_U, μ_𝓒)` with `𝔪|_U ≃ 𝒮_u`
(`ContactEquivalenceAlong.contact_wEquiv_open_along`), at every point `y` of `N ∩ V(u) ∩ U` not in
`Z₁(𝔪)`, the ideal of `𝒮_u` is nonzero along `N ∩ V(u)` near `y`.  This is the hypothesis of the inductive
invariant (`hir:centre-function`: the ideal vanishes identically on no nonempty open subset of the
submanifold). -/
theorem isNonzeroAlongAt_contact_open (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u) (y : U)
    (hy : y ∈ (withN (MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong 𝔪))
      ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ {x | u x = 0}))).N)
    (hyZ : (y : X) ∉ codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d) :
    IsNonzeroAlongAt (withN (MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong 𝔪))
        ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ {x | u x = 0}))).N
      (withN (MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong 𝔪))
        ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ {x | u x = 0}))).ideal y := by
  set S := withN (MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong 𝔪))
    ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ {x | u x = 0})) with hSdef
  have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hW := contact_wEquiv_open_along 𝔪 hN h𝔞 hd U hu
  have hcos : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).cosupp = S.cosupp :=
    (hW.2 (BlowupTower.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U))).2 trivial
  have hcoh : S.ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val
      (isCoherent_coeffMarkedAlong h𝔞 hN)
  have hyU : (y : X) ∈ 𝔪.N ∩ {x | u x = 0} ∩ (U : Set X) := ⟨hy, y.2⟩
  obtain ⟨k, hNk, hAk⟩ := IsTangentDirectionAlong.exists_regularAtDim_succ hhol hN hu hyU
  have hAeq : ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ {x | u x = 0} ∩ (U : Set X)) : Set U) = S.N := by
    ext p
    simp only [hSdef, withN_N, mem_preimage, mem_inter_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, p.2⟩⟩
  have hZU : y ∉ codimOnePartAlong ((Subtype.val : U → X) ⁻¹' 𝔪.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) 𝔪.ideal) 𝔪.d := by
    rw [codimOnePartAlong_pullback_val U hhol 𝔪.d]
    exact hyZ
  refine isNonzeroAlongAt_of_notMem_codimOnePartAlong (μ := 𝔪.d) (ν := S.d) hcoh
    (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hNk)
    (hAeq ▸ AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hAk)
    (Eventually.of_forall fun z hz => ?_) (Eventually.of_forall fun z hz => ?_) hZU
  · have hz' : z ∈ S.cosupp := hcos ▸ hz
    exact S.cosupp_subset_N hz'
  · have hz' : z ∈ (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).cosupp := hcos ▸ hz
    exact hz'

/-- **At every stage after Step 1ba the restricted marked ideals of Step 1bb are nonzero along their
submanifolds.**  Let `𝔪` be well formed, of maximal order along `N`, `d ≥ 1`, with `Z₁(𝔪) = ∅` (for
instance the transform after Step 1ba, `codimOnePartAlong_geoTransform_codimOnePartAlong_eq_empty`), `T` a
multiple test blow-up and `w` a tangent direction of the transform along `N_T` on an open `U` of the last
stage.  Then the ideal of `𝒮_w = (U, N_T ∩ V(w), E_T|_U, 𝓒_{N_T}(𝔞_T)|_U, μ_𝓒)` is nonzero along
`N_T ∩ V(w)` near each of its points. -/
theorem isNonzeroAlongAt_contact_open_geoTransformAlong (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hμ : 1 ≤ 𝔪.d) (hmax : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d)
    (hZ : codimOnePartAlong 𝔪.N 𝔪.ideal 𝔪.d = ∅) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) (U : Opens Y) {w : Y → ℂ}
    (hw : IsTangentDirectionAlong (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
      (geoTransformAlong 𝔪 T).d U w) (y : U)
    (hy : y ∈ (withN (MarkedIdeal.pullback (Subtype.val : U → Y) (coeffMarkedAlong (geoTransformAlong 𝔪 T)))
      ((Subtype.val : U → Y) ⁻¹' ((geoTransformAlong 𝔪 T).N ∩ {x | w x = 0}))).N) :
    IsNonzeroAlongAt (withN (MarkedIdeal.pullback (Subtype.val : U → Y)
        (coeffMarkedAlong (geoTransformAlong 𝔪 T)))
        ((Subtype.val : U → Y) ⁻¹' ((geoTransformAlong 𝔪 T).N ∩ {x | w x = 0}))).N
      (withN (MarkedIdeal.pullback (Subtype.val : U → Y) (coeffMarkedAlong (geoTransformAlong 𝔪 T)))
        ((Subtype.val : U → Y) ⁻¹' ((geoTransformAlong 𝔪 T).N ∩ {x | w x = 0}))).ideal y := by
  obtain ⟨hNT, h𝔞T⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong h𝔪.isClosedSubmanifold_N
    h𝔪.isCoherent T hT
  have hZT := codimOnePartAlong_geoTransformAlong_eq_empty 𝔪 h𝔪 hμ hmax hZ T hT
  refine isNonzeroAlongAt_contact_open (geoTransformAlong 𝔪 T) hNT h𝔞T
    (by rw [d_geoTransformAlong]; exact hμ) U hw y hy ?_
  rw [hZT]
  exact notMem_empty _

end Contact

end

end TranscendentalNakamaye.Pending.CodimOnePartTowerAlong
