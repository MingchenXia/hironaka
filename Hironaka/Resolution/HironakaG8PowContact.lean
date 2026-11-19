import Hironaka.Resolution.HironakaG8ContactMax
import Hironaka.Resolution.HironakaG11InvBMStage

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The zero set of the transformed coefficient ideal lies in every hypersurface of maximal contact (G8 lane, run 0080, r7)

Blueprint: `hironaka-g8-resume-pow-contact.tex`.  Plan: `work/hironaka-resume-20261111/G8/REPORT-r7.md` (level `s + 1` of
module 6, lane G11B's `BPRIME-PLAN.md` §6c item (iv)).

For a tangent direction `u` of `(𝔞|_N, d)` on `U`, the coefficient ideal `𝒞 = 𝓒_N(𝔍_∅) = ∑_{j<d} (𝓓_N^j 𝔞)^{δ/(d-j)}` (mark
`δ = d!`) contains `u^δ` (its summand `j = d - 1`).  Along an admissible blowup `π` with centre `C ⊆ cosupp ⊆ V(u)`, `u ∘ π = h·u'`
with `h` a local equation of the exceptional divisor and `u'` a local equation of the strict transform of `N ∩ V(u)` inside the
new carrier (Włodarczyk `le:Gi`, TN3's along-`N` Giraud lemma), so `u'^δ = h^{-δ}·π^*(u^δ)` lies in the controlled transform.
Hence, along every multiple test blow-up, **the zero set of the transformed coefficient ideal lies in the strict transform of
every hypersurface of maximal contact** — at order `1`, not only at order `δ` (the cosupport, `le:Giraud`).

* **`PowContact P S V`**: near every point of `P.N ∩ V` a function `w` with `w^d ∈ P.ideal`, multiplicity one along `P.N` at its
  zeros, and zero set `S` in `P.N`; `PowContact.eventually_mem_of_forall_eq_zero` (the zero set of `P.ideal` lies in `S`);
* `mem_geoTransform_ideal_of_mem_controlledTransform`; **`powContact_geoTransform`** (one admissible blowup) and
  **`powContact_geoTransformAlong`** (multiple test blow-ups); `strictAlong_mono`;
* `powContact_coeffEmptyBM` (the base: `u^δ ∈ 𝓒_N(𝔍_∅)`); **`eventually_mem_contact_of_forall_eq_zero`**: at a stage of a
  test tower of `𝔍`, near a point over `U`, the common zeros of the ideal of `contactCoeffBM 𝔍 u' T₀` (any `u'`) on the stage
  carrier lie in the carrier of `contactCoeffBM 𝔍 u T₀`.

Sorry-free.  Universe-polymorphic.  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8PowContact

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
  Hironaka.DerivativeIdealAlong Hironaka.TangentDirectionAlong
  Hironaka.HomogenizedIdealAlong Hironaka.RestrictedIdealWeight
  Hironaka.BlowupFunctionTransform Hironaka.BlowupStrictSubmanifold
  Hironaka.BlowupExceptionalDivisor Hironaka.BlowupTowers
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.RestrictedIdealExtension
  Hironaka.RestrictedIdealQuotient Hironaka.InvertibleIdealQuotient
  Hironaka.GiraudAlong Hironaka.MaximalContactAlongTower
  Hironaka.BlowupControlledTransform Hironaka.RelativePrincipalizationSpan
  Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen
  Hironaka.CoefficientIdeal
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.HironakaG11InvBMLower (coeffEmptyBM contactCoeffBM emptyBoundary)

noncomputable section

variable {n : ℕ}

/-! ### Elementary facts -/

section Basic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A germ of the ideal vanishes at a point of the cosupport** (order `μ ≥ 1`). -/
theorem apply_eq_zero_of_mem_cosupport_of_mem {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ} (hμ : 1 ≤ μ) {x : M}
    (hx : x ∈ cosupport n N 𝔞 μ) {g : M → ℂ} (hg : 𝔞.mem x g) : g x = 0 := by
  obtain ⟨k, hk, hkeq⟩ := hx.2 g hg
  rw [hkeq.self_of_nhds hx.1]
  exact apply_eq_zero_of_mem_idealPow_pointIdeal hμ hk

end Basic

/-! ### The predicate and one blowup -/

section Stage

variable {Y Z : CMfd.{u} n}

/-- **`w^d` in the ideal, near the points of `P.N ∩ V`**: every point of `P.N ∩ V` has an open neighbourhood `O` and a function
`w`, holomorphic on `O`, with `w^d ∈ P.ideal` at the points of `P.N ∩ O`, of multiplicity one along `P.N` at its zeros there,
and whose zero set in `P.N ∩ O` is `S ∩ O`. -/
def PowContact (P : MarkedIdeal n Y) (S V : Set Y) : Prop :=
  ∀ z ∈ P.N, z ∈ V → ∃ (O : Set Y) (w : Y → ℂ), z ∈ O ∧ IsOpen O ∧ (∀ x ∈ O, HolomorphicAt n w x) ∧
    (∀ x ∈ O, x ∈ P.N → P.ideal.mem x (fun y => w y ^ P.d)) ∧
    (∀ x ∈ O, x ∈ P.N → w x = 0 → ∃ (e : ComplexChart n Y) (ξ : Fin n → Y → ℂ),
      IsTangentField P.N e ξ x ∧ fieldDeriv e ξ w x ≠ 0) ∧
    ∀ y ∈ O, y ∈ P.N → (w y = 0 ↔ y ∈ S)

/-- **The common zeros of the ideal lie in `S`** (near the points of `P.N ∩ V`). -/
theorem PowContact.eventually_mem_of_forall_eq_zero {P : MarkedIdeal n Y} {S V : Set Y} (h : PowContact P S V)
    (hμ : 1 ≤ P.d) {z : Y} (hzN : z ∈ P.N) (hzV : z ∈ V) :
    ∀ᶠ x in 𝓝 z, x ∈ P.N → (∀ g, P.ideal.mem x g → g x = 0) → x ∈ S := by
  obtain ⟨O, w, hzO, hOo, -, hwI, -, hwA⟩ := h z hzN hzV
  filter_upwards [hOo.mem_nhds hzO] with x hxO hxN hx0
  have h0 : w x ^ P.d = 0 := hx0 _ (hwI x hxO hxN)
  exact (hwA x hxO hxN).mp (pow_eq_zero_iff (by omega) |>.mp h0)

/-- **The controlled transform lies in the transform along the strict transform of the carrier.** -/
theorem mem_geoTransform_ideal_of_mem_controlledTransform {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π)
    (P : MarkedIdeal n Y) {x : Z} {g : Z → ℂ} (h : (controlledTransform hπ P.ideal P.d).mem x g) :
    (P.geoTransform C π).ideal.mem x g := by
  obtain ⟨hg, hall⟩ := mem_colon_iff.mp h
  refine mem_colon_iff.mpr ⟨hg, fun l hl => ?_⟩
  have hl' : (idealPow (exceptionalDivisor hπ).ideal P.d).mem x l := by
    rw [← pullback_idealPow_vanishingIdeal hπ, pullback_idealPow hπ.contMDiff (isCoherent_vanishingIdeal_centre hπ)]
    exact hl
  have hm := hall l hl'
  exact ⟨(GermIdeal.mem_pullback_iff.mp hm).1,
    IsInSpanAt.restrict (isInSpanAt_self hm (GermIdeal.mem_pullback_iff.mp hm).1)⟩

/-- **One admissible blowup keeps `PowContact`** (with the strict transform of `S` and the preimage of `V`). -/
theorem powContact_geoTransform {P : MarkedIdeal n Y} {S V : Set Y} (hNT : IsClosedSubmanifold n P.N)
    (hμ : 1 ≤ P.d) (hSN : S ⊆ P.N) (h : PowContact P S V) {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hC : P.IsAdmissibleCentre C) :
    PowContact (P.geoTransform C π) (geoStrictTransform π C S) (π ⁻¹' V) := by
  intro z' hz'N hz'V
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hz'NT : π z' ∈ P.N := geoStrictTransform_subset_preimage hπc hNT.1 hz'N
  obtain ⟨O, w, hzO, hOo, hwhol, hwI, hw1, hwA⟩ := h (π z') hz'NT hz'V
  have hCN : C ⊆ P.N := hC.subset_N
  -- `w` vanishes on the centre
  have hCw : ∀ x ∈ C, x ∈ O → w x = 0 := by
    intro x hxC hxO
    have hxc : x ∈ cosupport n P.N P.ideal P.d := hC.2.1 hxC
    exact (pow_eq_zero_iff (by omega)).mp
      (apply_eq_zero_of_mem_cosupport_of_mem hμ hxc (hwI x hxO (hCN hxC)))
  -- the controlled transform `w'` of `w`
  obtain ⟨Uh, h, hz'h, hh⟩ := exists_isLocalEquation hπ z'
  have hwI1 : (idealPow (vanishingIdeal (n := n) C) 1).mem (π z') w := by
    refine BlowupDerivativeIdeal.mem_idealPow_one_of_mem (fun _ _ hg => hg.1) ⟨hwhol _ hzO, ?_⟩
    filter_upwards [hOo.mem_nhds hzO] with y hy hyC
    exact hCw y hyC hy
  obtain ⟨w', hw'z, heq⟩ := exists_eq_pow_mul hh hz'h hwI1
  have heq' : (w ∘ π) =ᶠ[𝓝 z'] fun y => h y * w' y := heq.mono fun y hy => by rw [hy]; simp
  have hev : ∀ᶠ y in 𝓝 z', (y ∈ Uh ∧ π y ∈ O) ∧ HolomorphicAt n w' y ∧
      ((w ∘ π) =ᶠ[𝓝 y] fun y => h y * w' y) ∧
      (y ∈ geoStrictTransform π C P.N →
        (y ∈ geoStrictTransform π C (P.N ∩ {x | w x = 0} ∩ O) ↔ w' y = 0)) :=
    ((hh.isOpen.eventually_mem hz'h).and ((hOo.preimage hπc).eventually_mem hzO)).and
      ((DerivativeIdeal.HolomorphicAt.eventually_holomorphicAt hw'z).and (heq'.eventually_nhds.and
        (LocalGiraudTransformAlong.eventually_mem_geoStrictTransform_inter_zeroSet_iff hπ hNT hCN hh hOo
          hwhol hw1 hCw hz'h hzO hw'z heq')))
  obtain ⟨O', hO'sub, hO'o, hz'O'⟩ := mem_nhds_iff.mp hev
  refine ⟨O', w', hz'O', hO'o, fun y hy => (hO'sub hy).2.1, ?_, ?_, ?_⟩
  · -- `w'^δ = h^{-δ} π^*(w^δ)` lies in the transform
    intro x hx hxN
    obtain ⟨⟨hxh, hxO⟩, hw'x, heqx, -⟩ := hO'sub hx
    have hπxN : π x ∈ P.N := geoStrictTransform_subset_preimage hπc hNT.1 hxN
    refine mem_geoTransform_ideal_of_mem_controlledTransform hπ P ?_
    refine mem_controlledTransform_of_eq_pow_mul hh hxh (hwI (π x) hxO hπxN) (holomorphicAt_pow hw'x _) ?_
    filter_upwards [heqx] with y hy
    show w (π y) ^ P.d = h y ^ P.d * w' y ^ P.d
    rw [show w (π y) = (w ∘ π) y from rfl, hy, mul_pow]
  · -- multiplicity one along `N'` at the zeros (TN3's along-`N'` local Giraud, (ii))
    intro x hx hxN h0
    obtain ⟨⟨hxh, hxO⟩, hw'x, heqx, hiff⟩ := hO'sub hx
    exact LocalGiraudTransformAlong.exists_fieldDeriv_ne_zero_controlledTransform_along hπ hNT hCN hh hOo
      hwhol hw1 hCw hxh hxO hw'x heqx ((hiff hxN).mpr h0)
  · -- the zero set on `N'` (TN3's (i), and locality of strict transforms over `O`)
    intro y hy hyN
    obtain ⟨⟨-, hyO⟩, -, -, hiff⟩ := hO'sub hy
    rw [← hiff hyN]
    have hAB : (P.N ∩ {x | w x = 0} ∩ O) ∩ O = S ∩ O := by
      ext x
      constructor
      · rintro ⟨⟨⟨hxN, hx0⟩, hxO⟩, -⟩
        exact ⟨(hwA x hxO hxN).mp hx0, hxO⟩
      · rintro ⟨hxA, hxO⟩
        have hxN := hSN hxA
        exact ⟨⟨⟨hxN, (hwA x hxO hxN).mpr hxA⟩, hxO⟩, hxO⟩
    have hloc := MaximalContactTower.geoStrictTransform_inter_preimage (C := C) hπc hOo hAB
    constructor
    · intro hy'
      have : y ∈ geoStrictTransform π C (P.N ∩ {x | w x = 0} ∩ O) ∩ π ⁻¹' O := ⟨hy', hyO⟩
      rw [hloc] at this
      exact this.1
    · intro hy'
      have : y ∈ geoStrictTransform π C S ∩ π ⁻¹' O := ⟨hy', hyO⟩
      rw [← hloc] at this
      exact this.1

end Stage

/-! ### Along multiple test blow-ups -/

section Tower

/-- Strict transforms along a tower are monotone. -/
theorem strictAlong_mono {X : CMfd.{u} n} {A B : Set X} (hAB : A ⊆ B) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), strictAlong T A ⊆ strictAlong T B
  | _, .refl => hAB
  | _, .step T C π _ => by
    show closure _ ⊆ closure _
    exact closure_mono (preimage_mono (sdiff_subset_sdiff_left (strictAlong_mono hAB T)))

/-- **`PowContact` along multiple test blow-ups.** -/
theorem powContact_geoTransformAlong {X : CMfd.{u} n} (P : MarkedIdeal n X) (hN : IsClosedSubmanifold n P.N)
    (hcoh : P.ideal.IsCoherent) (hμ : 1 ≤ P.d) {S V : Set X} (hSN : S ⊆ P.N) (h : PowContact P S V) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower P T →
      PowContact (geoTransformAlong P T) (strictAlong T S) (T.proj ⁻¹' V)
  | _, .refl, _ => h
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff P T C π hπ).mp hT
    have ih := powContact_geoTransformAlong P hN hcoh hμ hSN h T hTT
    obtain ⟨hNT, -⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN hcoh T hTT
    have hSNT : strictAlong T S ⊆ (geoTransformAlong P T).N := by
      rw [HomogenizedGlueingTower.N_geoTransformAlong]
      exact strictAlong_mono hSN T
    exact powContact_geoTransform hNT (by rw [d_geoTransformAlong]; exact hμ) hSNT ih hπ hC

end Tower

/-! ### Bierstone--Milman's coefficient ideal on maximal contact -/

section Contact

variable {X : CMfd.{u} n}

/-- **The base: `u^δ ∈ 𝓒_N(𝔍_∅)`** for a tangent direction `u` on `U` (the summand `j = d - 1`, with exponent `δ`). -/
theorem powContact_coeffEmptyBM (𝔍 : MarkedIdeal n X) (h𝔞 : 𝔍.ideal.IsCoherent) (hd : 1 ≤ 𝔍.d) {U : Set X}
    {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) :
    PowContact (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | u x = 0}) U := by
  have hhol : ∀ x g, 𝔍.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hexp : sumExp (fun j => (derivMarkedAlong (emptyBoundary 𝔍) j).d) 𝔍.d (𝔍.d - 1) = (coeffEmptyBM 𝔍).d := by
    have h2 := mul_sumExp (fun j => (derivMarkedAlong (emptyBoundary 𝔍) j).d) (m := 𝔍.d) (i := 𝔍.d - 1) (by omega)
    have h1 : (derivMarkedAlong (emptyBoundary 𝔍) (𝔍.d - 1)).d = 1 := by
      show 𝔍.d - (𝔍.d - 1) = 1
      omega
    simp only [h1, one_mul] at h2
    exact h2
  intro z _ hzU
  refine ⟨U, u, hzU, hu.isOpen, fun x hx => holomorphicAt_of_mem_iterDerivIdealAlong hhol _ x u (hu.mem x hx), ?_,
    fun x hx _ h0 => hu.multiplicity_one x hx h0, fun y _ hyN => ⟨fun h0 => ⟨hyN, h0⟩, fun h => h.2⟩⟩
  intro x hx _
  have hux : HolomorphicAt n u x := holomorphicAt_of_mem_iterDerivIdealAlong hhol _ x u (hu.mem x hx)
  have hmem : (idealPow (iterDerivIdealAlong 𝔍.N 𝔍.ideal (𝔍.d - 1)) (coeffEmptyBM 𝔍).d).mem x
      (fun y => u y ^ (coeffEmptyBM 𝔍).d) :=
    MonomialPart.pow_mem_idealPow (hu.mem x hx) hux _
  have hmem' : (idealPow (iterDerivIdealAlong 𝔍.N 𝔍.ideal (𝔍.d - 1))
      (sumExp (fun j => (derivMarkedAlong (emptyBoundary 𝔍) j).d) 𝔍.d (𝔍.d - 1))).mem x
      (fun y => u y ^ (coeffEmptyBM 𝔍).d) := by
    rw [hexp]
    exact hmem
  exact isInSpanAt_self (S := fun s => ∃ i, i < 𝔍.d ∧ (idealPow (iterDerivIdealAlong 𝔍.N 𝔍.ideal i)
      (sumExp (fun j => (derivMarkedAlong (emptyBoundary 𝔍) j).d) 𝔍.d i)).mem x s)
    ⟨𝔍.d - 1, by omega, hmem'⟩ (BlowupFunctionTransform.holomorphicAt_pow hux _)

/-- **At a stage of a test tower of `𝔍`, near a point over `U`, the common zeros on the stage carrier of the transformed
coefficient ideal lie in the strict transform of the hypersurface of maximal contact `N ∩ V(u)`** (the carrier of
`contactCoeffBM 𝔍 u T₀`). -/
theorem eventually_mem_contact_of_forall_eq_zero {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔍 T₀) {y : Y₀}
    (hyN : y ∈ (geoTransformAlong (coeffEmptyBM 𝔍) T₀).N) (hyU : T₀.proj y ∈ U) :
    ∀ᶠ z in 𝓝 y, z ∈ (geoTransformAlong (coeffEmptyBM 𝔍) T₀).N →
      (∀ g, (geoTransformAlong (coeffEmptyBM 𝔍) T₀).ideal.mem z g → g z = 0) → z ∈ (contactCoeffBM 𝔍 u T₀).N := by
  have hwf := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM h𝔍
  have hT₀c := HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM h𝔍 hd T₀
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary 𝔍 T₀ hT₀)
  have hμ : 1 ≤ (coeffEmptyBM 𝔍).d := ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary 𝔍)
  have hP := powContact_geoTransformAlong (coeffEmptyBM 𝔍) hwf.isClosedSubmanifold_N hwf.isCoherent hμ
    inter_subset_left (powContact_coeffEmptyBM 𝔍 h𝔍.isCoherent hd hu) T₀ hT₀c
  exact hP.eventually_mem_of_forall_eq_zero (by rw [d_geoTransformAlong]; exact hμ) hyN hyU

end Contact

end

end Hironaka.HironakaG8PowContact
