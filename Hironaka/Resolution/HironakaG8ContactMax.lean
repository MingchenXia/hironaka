import Hironaka.MarkedIdeal.MaximalContactAlongTower
import Hironaka.Resolution.HironakaSmoothSubmersionTangentContact
import Hironaka.Resolution.HironakaG8ContactGood

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Maximal contact inside `N` at a stage (G8 lane, run 0080, round 5; (B') port P4, part 2)

Blueprint: `hironaka-g8-resume-contact-stage-invariant.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2
(P4, Bierstone--Milman 2008 Corollary 4.2), G8 `REPORT-r4.md` (route).

The library carries the hypersurface of maximal contact `N ∩ V(u)` along multiple test blow-ups from a FIXED base
(`MaximalContactAlongTower.exists_contact_along`, Włodarczyk `le:Gi` / `le:Giraud` along `N`).  For the local form of
Bierstone--Milman's Corollary 4.2 the invariant is needed at stages of arbitrary local histories, so here it is stated
for a stage marked ideal `P` and a set `S`:

* **`MaxContact P S`**: every point of `P.N` has an open neighbourhood `O` with a function `w`, holomorphic on `O`, equal
  on `P.N` (at the points of `P.N ∩ O`) to combinations of germs of `𝓓_{P.N}^{d-1}(P.ideal)`, of multiplicity one along
  `P.N` at its zeros there, whose zero set in `P.N ∩ O` is `S ∩ O`;
* `MaxContact.cosupp_subset`: the cosupport lies in `S` (`le:Giraud`); `maxContact_base`: a tangent direction `u` on all
  of the base gives `MaxContact 𝔪 (N ∩ V(u))`;
* **`maxContact_geoTransform`**: one admissible blowup (the induction step of `exists_contact_along`, with stage-only
  hypotheses: TN-CLASSICAL's `hir:along-transform` and TN3's along-`N'` local Giraud lemma);
* **`maxContact_pullback_submersion`**: pullback along a holomorphic submersion (the derivative ideals along `N` pull
  back, `HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_iterDerivIdealAlong`; tangent fields with
  `ξ(w) ≠ 0` lift, `HironakaSmoothSubmersionTangentContact.exists_nonzero_tangentField_preimage`).

Sorry-free.  Universe-polymorphic.  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8ContactMax

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

noncomputable section

section Stage

variable {n : ℕ} {Y : CMfd.{u} n}

/-- **Maximal contact inside `N` at a stage**: every point of `P.N` has an open neighbourhood `O` and a function `w`,
holomorphic on `O`, which at the points of `P.N ∩ O` agrees on `P.N` with combinations of germs of
`𝓓_{P.N}^{d-1}(P.ideal)`, has multiplicity one along `P.N` at its zeros there, and whose zero set in `P.N ∩ O` is
`S ∩ O` (the conclusion of `MaximalContactAlongTower.exists_contact_along`, with the stage as a variable). -/
def MaxContact (P : MarkedIdeal n Y) (S : Set Y) : Prop :=
  ∀ z ∈ P.N, ∃ (O : Set Y) (w : Y → ℂ), z ∈ O ∧ IsOpen O ∧ (∀ x ∈ O, HolomorphicAt n w x) ∧
    (∀ x ∈ O, x ∈ P.N → IsInSpanOnAt (n := n) P.N ((iterDerivIdealAlong P.N P.ideal (P.d - 1)).mem x) x w) ∧
    (∀ x ∈ O, x ∈ P.N → w x = 0 → ∃ (e : ComplexChart n Y) (ξ : Fin n → Y → ℂ),
      IsTangentField P.N e ξ x ∧ fieldDeriv e ξ w x ≠ 0) ∧
    ∀ y ∈ O, y ∈ P.N → (w y = 0 ↔ y ∈ S)

/-- **The cosupport lies in the hypersurface of maximal contact** (Włodarczyk `le:Giraud` at a stage). -/
theorem MaxContact.cosupp_subset {P : MarkedIdeal n Y} {S : Set Y} (h : MaxContact P S) (hcoh : P.ideal.IsCoherent)
    (hμ : 1 ≤ P.d) : P.cosupp ⊆ S := by
  intro z hzc
  have hzN : z ∈ P.N := P.cosupp_subset_N hzc
  obtain ⟨O, w, hzO, -, -, hwD, -, hwA⟩ := h z hzN
  have hhol : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg
  refine (hwA z hzO hzN).mp ?_
  exact apply_eq_zero_of_isInSpanOnAt hzN
    (fun s hs => TangentDirectionAlong.apply_eq_zero_of_mem_cosupport hhol hμ hzc hs) (hwD z hzO hzN)

/-- **At the base**: a tangent direction `u` of `(𝔞|_N, d)` along `N` on all of `Y` gives maximal contact with
`N ∩ V(u)`. -/
theorem maxContact_base (𝔪 : MarkedIdeal n Y) (h𝔞 : 𝔪.ideal.IsCoherent) {u : Y → ℂ}
    (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d univ u) : MaxContact 𝔪 (𝔪.N ∩ {x | u x = 0} ∩ univ) := by
  intro z _
  have hhol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  refine ⟨univ, u, mem_univ z, isOpen_univ,
    fun x hx => holomorphicAt_of_mem_iterDerivIdealAlong hhol _ x u (hu.mem x hx), fun x hx _ => ?_,
    fun x hx _ h0 => hu.multiplicity_one x hx h0,
    fun y hy hyN => ⟨fun h0 => ⟨⟨hyN, h0⟩, hy⟩, fun h => h.1.2⟩⟩
  exact ⟨1, fun _ => u, fun _ _ => 1, fun _ => hu.mem x hx, fun _ => holomorphicAt_const 1,
    Eventually.of_forall fun y _ => by simp⟩

variable {Z : CMfd.{u} n}

/-- **Maximal contact survives one admissible blowup** (the induction step of `exists_contact_along` with stage-only
hypotheses): the controlled transform `w'` of `w` lies on `N'` in `𝓓_{N'}^{d-1}(𝔞')`, has multiplicity one along `N'`
at its zeros, and cuts out on `N'` the strict transform of `S`. -/
theorem maxContact_geoTransform {P : MarkedIdeal n Y} {S : Set Y} (hNT : IsClosedSubmanifold n P.N)
    (hcoh : P.ideal.IsCoherent) (hμ : 1 ≤ P.d) (hSN : S ⊆ P.N) (h : MaxContact P S) {C : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong n C π) (hC : P.IsAdmissibleCentre C) :
    MaxContact (P.geoTransform C π) (geoStrictTransform π C S) := by
  intro z' hz'N
  have hd : P.d = P.d := rfl
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hz'NT : π z' ∈ P.N := geoStrictTransform_subset_preimage hπc hNT.1 hz'N
  obtain ⟨O, w, hzO, hOo, hwhol, hwD, hw1, hwA⟩ := h (π z') hz'NT
  have hCN : C ⊆ P.N := hC.subset_N
  have hhol : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg
  -- `w` vanishes on the centre
  have hCw : ∀ x ∈ C, x ∈ O → w x = 0 := by
    intro x hxC hxO
    have hxc : x ∈ cosupport n P.N P.ideal P.d := by
      have := hC.2.1 hxC
      rwa [MarkedIdeal.cosupp, hd] at this
    exact apply_eq_zero_of_isInSpanOnAt (hCN hxC)
      (fun s hs => TangentDirectionAlong.apply_eq_zero_of_mem_cosupport hhol hμ hxc hs) (hwD x hxO (hCN hxC))
  -- the controlled transform `w'` of `w`
  obtain ⟨Uh, h, hz'h, hh⟩ := exists_isLocalEquation hπ z'
  have hwI : (idealPow (vanishingIdeal (n := n) C) 1).mem (π z') w := by
    refine BlowupDerivativeIdeal.mem_idealPow_one_of_mem (fun _ _ hg => hg.1) ⟨hwhol _ hzO, ?_⟩
    filter_upwards [hOo.mem_nhds hzO] with y hy hyC
    exact hCw y hyC hy
  obtain ⟨w', hw'z, heq⟩ := exists_eq_pow_mul hh hz'h hwI
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
  · -- `w'` lies, on `N'`, in the derivative ideal along `N'` of the transform (`hir:along-transform`)
    intro x hx hxN
    obtain ⟨⟨hxh, hxO⟩, hw'x, heqx, -⟩ := hO'sub hx
    have hπxN : π x ∈ P.N := geoStrictTransform_subset_preimage hπc hNT.1 hxN
    obtain ⟨K, s, a, hs, ha, hsum⟩ := hwD (π x) hxO hπxN
    have hmem : ((derivMarkedAlong P (P.d - 1)).geoTransform C π).ideal.mem x w' := by
      show HolomorphicAt n w' x ∧ ∀ p, (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C))
          (P.d - (P.d - 1))).mem x p →
        (restrictOn n (geoStrictTransform π C P.N)
          (GermIdeal.pullback (m := n) π (iterDerivIdealAlong P.N
            P.ideal (P.d - 1)))).mem x (fun y => p y * w' y)
      refine ⟨hw'x, fun p hp => ?_⟩
      rw [show P.d - (P.d - 1) = 1 by rw [hd]; omega] at hp
      have hp1 : (exceptionalDivisor hπ).ideal.mem x p := by
        rw [← BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ]
        exact hp
      obtain ⟨hph, c, hc, hpc⟩ := isInSpanAt_eq_iff.mp ((hh.generates x hxh p).mp hp1)
      have hπat : ∀ᶠ y' in 𝓝 x, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y' :=
        Eventually.of_forall fun y' => hπ.contMDiff y'
      have hsh : ∀ i, HolomorphicAt n (s i) (π x) := fun i =>
        holomorphicAt_of_mem_iterDerivIdealAlong hhol _ (π x) (s i) (hs i)
      refine ⟨hph.mul hw'x, K, fun i => s i ∘ π, fun i y => c y * a i (π y),
        fun i => BlowupDerivativeIdeal.comp_mem_pullback (c := fun _ => 1) (hs i)
          ((hsh i).comp_contMDiff hπat) (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp),
        fun i => hc.mul ((ha i).comp_contMDiff hπat), ?_⟩
      filter_upwards [hpc, heqx, hπc.continuousAt.eventually hsum] with y h1 h2 h3 hyN
      have h3' := h3 (geoStrictTransform_subset_preimage hπc hNT.1 hyN)
      have h2' : h y * w' y = w (π y) := h2.symm
      rw [h1, mul_assoc, h2', h3', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
      ring
    exact DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong P hNT
      hcoh hC hπ (by show P.d - 1 ≤ P.d; omega) x hxN w' hmem
  · -- multiplicity one along `N'` at the zeros (TN3's along-`N'` local Giraud, (ii))
    intro x hx hxN h0
    obtain ⟨⟨hxh, hxO⟩, hw'x, heqx, hiff⟩ := hO'sub hx
    exact LocalGiraudTransformAlong.exists_fieldDeriv_ne_zero_controlledTransform_along hπ hNT hCN hh hOo
      hwhol hw1 hCw hxh hxO hw'x heqx ((hiff hxN).mpr h0)
  · -- the zero set on `N'` (TN3's (i), and locality of strict transforms over `O`)
    intro y hy hyN
    obtain ⟨⟨-, hyO⟩, -, -, hiff⟩ := hO'sub hy
    rw [← hiff hyN]
    have hAB : (P.N ∩ {x | w x = 0} ∩ O) ∩ O =
        S ∩ O := by
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
      have : y ∈ geoStrictTransform π C (P.N ∩ {x | w x = 0} ∩ O) ∩ π ⁻¹' O :=
        ⟨hy', hyO⟩
      rw [hloc] at this
      exact this.1
    · intro hy'
      have : y ∈ geoStrictTransform π C (S) ∩ π ⁻¹' O := ⟨hy', hyO⟩
      rw [← hloc] at this
      exact this.1

end Stage

/-! ### Pullback along a holomorphic submersion -/

section Pullback

variable {n m : ℕ} {Y : CMfd.{u} n} {Y' : CMfd.{u} m} {f : Y' → Y}

/-- **Maximal contact pulls back along a holomorphic submersion** `f` (products with a line, open restrictions): for
`P'` with carrier `f⁻¹(P.N)`, ideal `f^*(P.ideal)` and the same mark (any boundary), `MaxContact P' (f⁻¹S)`. -/
theorem maxContact_pullback_submersion
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {P : MarkedIdeal n Y} {S : Set Y} {P' : MarkedIdeal m Y'} (hPN : P'.N = f ⁻¹' P.N)
    (hPI : P'.ideal = GermIdeal.pullback (m := m) f P.ideal) (hPd : P'.d = P.d)
    (hN : IsClosedSubmanifold n P.N) (hcoh : P.ideal.IsCoherent) (h : MaxContact P S) :
    MaxContact P' (f ⁻¹' S) := by
  have hfc : Continuous f := hf.contMDiff.continuous
  have hfd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w :=
    fun w => (hf.contMDiff w).mdifferentiableAt (by simp)
  have hD : iterDerivIdealAlong P'.N P'.ideal (P'.d - 1) =
      GermIdeal.pullback (m := m) f (iterDerivIdealAlong P.N P.ideal (P.d - 1)) := by
    rw [hPN, hPI, hPd,
      HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_iterDerivIdealAlong hf P.ideal hcoh P.N hN]
  have hDcoh := DerivativeIdealAlongCoherent.isCoherent_iterDerivIdealAlong hcoh hN (P.d - 1)
  intro z hz
  rw [hPN] at hz
  obtain ⟨O, w, hzO, hOo, hwhol, hwD, hw1, hwA⟩ := h (f z) hz
  refine ⟨f ⁻¹' O, w ∘ f, hzO, hOo.preimage hfc,
    fun x hx => HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hfd) (hwhol _ hx), ?_, ?_, ?_⟩
  · intro x hx hxN
    rw [hD, hPN]
    rw [hPN] at hxN
    refine RelativePrincipalizationSpan.IsInSpanOnAt.mono (fun t ⟨s, hs, ht⟩ => ?_)
      (HironakaG8ContactGood.isInSpanOnAt_comp_map hfc hfd (subset_refl _) (hwD (f x) hx hxN))
    rw [ht]
    exact HironakaG8ContactGood.comp_mem_pullback hfd hs
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDcoh hs)
  · intro x hx hxN h0
    rw [hPN] at hxN ⊢
    obtain ⟨e, ξ, hξ, hne⟩ := hw1 (f x) hx hxN h0
    exact HironakaSmoothSubmersionTangentContact.exists_nonzero_tangentField_preimage hf hN x w (hwhol _ hx) e ξ hξ hne
  · intro y hy hyN
    rw [hPN] at hyN
    exact hwA (f y) hy hyN

end Pullback

end

end Hironaka.HironakaG8ContactMax
