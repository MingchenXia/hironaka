import Hironaka.Invariant.MonomialResolution

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Uniqueness of the monomial / nonmonomial factorization

Blueprint `hir:monomial-factorization-unique` (`blueprint/src/hironaka.tex`, Hironaka phase H4; the algebraic core of
`hir:nonmonomial-transform`, `N = M`).  Sources: Bierstone--Milman 2008, §5 (the monomial part `𝓜(𝓘)` and the
nonmonomial part `𝓝(𝓘)` of a marked ideal, and their transforms); Włodarczyk 2005, Step 2 (the companion ideal).

Let `E` be a simple normal crossings divisor and suppose that near `z` an ideal `𝔟` is the product `𝔫 · (m)` of a
coherent ideal `𝔫` and a monomial `m = ∏_{z ∈ E_i} u_{σ i}^{b_i}` in centred coordinates in which the members through
`z` are the hyperplanes `{u_{σ i} = 0}`, and that `𝔫` is contained in the ideal of no member at the points of that
member near `z`.  Then the factorization is the one of `MonomialPart`:

* `divExp_eq_of_mul_principal`: the exponent of `𝔟` along each member through `z` is `b_i` (at the points of `E_i` near
  `z` off the other hyperplanes where a germ of `𝔫` does not vanish, `a m` has order exactly `b_i`);
* `monomialPart_mem_iff_of_mul_principal`: `𝓜(𝔟)_z = (m)`;
* `nonmonomialPart_mem_iff_of_mul_principal`: `𝓝(𝔟)_z = 𝔫_z` (`m` is a non-zero-divisor).

This is what identifies, after a blowup, the nonmonomial part of the transform with the transform of the nonmonomial
part (`hir:nonmonomial-transform`), once the latter is shown to lie in the ideal of no member of `E'`
(`ExceptionalIdealPushforward.exists_not_mem_exceptionalDivisor`,
`ExceptionalIdealPushforward.exists_not_mem_vanishingIdeal_geoStrictTransform`, TN3).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter Finset
open scoped Topology Manifold

namespace Hironaka.NonmonomialTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.BlowupFlatCoordinates Hironaka.GiraudAlong
  Hironaka.DivisorExponent Hironaka.MemberPullback
  Hironaka.MonomialPart Hironaka.MonomialCase
  Hironaka.IdealOrderArithmetic Hironaka.GermOrderProduct
  Hironaka.OrderTaylor Hironaka.DerivativeIdeal
  Hironaka.NormalCrossings

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

section Factorization

variable {𝔟 𝔫 : GermIdeal n M} {E : List (Set M)} {z : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z)}
  (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) z).target)
  {σ : Fin E.length → Fin n} {T : Finset (Fin E.length)}
  (hσ : Set.InjOn σ T)
  (hA : ∀ i ∈ T, ∀ {y : M}, y ∈ (chartAt (ComplexModel n) z).source →
    chartAt (ComplexModel n) z y ∈ Φ.source → (y ∈ E.get i ↔ Φ.toFun (chartAt (ComplexModel n) z y) (σ i) = 0))
  (b : Fin E.length → ℕ)
  (hfac : ∀ᶠ y in 𝓝 z, ∀ g, 𝔟.mem y g ↔
    IsInSpanAt (n := n) (fun s => ∃ a, 𝔫.mem y a ∧ s = fun p => a p * ∏ i ∈ T, flatCoord Φ (σ i) p ^ b i) y g)
  (hnd : ∀ᶠ y in 𝓝 z, ∀ i ∈ T, y ∈ E.get i → ∃ a, 𝔫.mem y a ∧ ¬ (vanishingIdeal (n := n) (E.get i)).mem y a)

include hΦsrc hσ hA hfac hnd in
/-- **The exponents of `𝔫 · (m)`** along the members through `z` are those of the monomial `m`. -/
theorem divExp_eq_of_mul_principal (h𝔫 : 𝔫.IsCoherent) (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y)
    {i : Fin E.length} (hi : i ∈ T) (hzi : z ∈ E.get i) :
    divExp n 𝔟 (E.get i) z = b i := by
  classical
  have h𝔫hol : ∀ y g, 𝔫.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔫 hg
  have hx : z ∈ flatDomain Φ := mem_flatDomain_self Φ
  set m : M → ℂ := fun p => ∏ i ∈ T, flatCoord Φ (σ i) p ^ b i with hmdef
  have hmhol : ∀ {y}, y ∈ flatDomain Φ → HolomorphicAt n m y := fun hy =>
    holomorphicAt_flatMonomial (σ := σ) (T := T) b hy
  -- `𝔟` is nonzero at `z`
  have hne : IsNonzeroAt 𝔟 z := by
    obtain ⟨a, ha, hna⟩ := hnd.self_of_nhds i hi hzi
    have hahol := h𝔫hol z a ha
    have hfa : ∃ᶠ p in 𝓝 z, a p ≠ 0 := by
      intro hall
      exact hna ⟨hahol, hall.mono fun p hp _ => not_not.mp hp⟩
    refine ⟨fun p => a p * m p, (hfac.self_of_nhds _).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨a, ha, rfl⟩ (hahol.mul (hmhol hx))), ?_⟩
    intro hall
    have hmne : ∃ᶠ p in 𝓝 z, m p ≠ 0 := by
      refine (frequently_flatMap_ne_zero hΦsrc hx (T.image σ)).mono fun p hp => ?_
      exact Finset.prod_ne_zero_iff.mpr fun j hj => pow_ne_zero _ (hp.2.1 (σ j) (Finset.mem_image_of_mem σ hj))
    have h0 := eventually_eq_zero_of_mul_eventually_eq_zero hahol (hmhol hx) hmne
      (hall.mono fun p hp => not_not.mp hp)
    exact hfa (h0.mono fun p hp => not_not.mpr hp)
  -- the monomial lies in `𝓘_{E_i}^{b_i}` near `z`
  have hm := flatMonomial_mem_idealPow_vanishingIdeal hA b hi
  have hdiv : IsDivNear n 𝔟 (E.get i) (b i) z := by
    filter_upwards [hfac, eventually_mem_idealPow_vanishingIdeal hm,
      (isOpen_flatDomain Φ).mem_nhds hx] with y hy hym hyD hyH
    refine ⟨mem_univ y, fun f hf => IsInSpanAt.vanishesToOrderOn ((hy f).mp hf) ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact vanishesToOrderOn_of_mem (mul_mem_idealPow (h𝔫hol y a ha)
      (mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal hyH hym))
  have hndiv : ¬ IsDivNear n 𝔟 (E.get i) (b i + 1) z := by
    intro hd
    -- a point `y₀ ∈ E_i` near `z` off the other hyperplanes, where the hypotheses hold nearby
    have hev := eventually_eventually_nhds.mpr (hd.and (hfac.and hnd))
    have hfreq := frequently_flatMap_ne_zero hΦsrc hx ((T.erase i).image σ)
    obtain ⟨y₀, ⟨hy₀D, hy₀ne, hy₀eq⟩, hy₀ev⟩ := (hfreq.and_eventually hev).exists
    have hσi : σ i ∉ (T.erase i).image σ := by
      intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      exact (Finset.mem_erase.mp hj).1 (hσ (Finset.mem_erase.mp hj).2 hi hji)
    have hy₀i : y₀ ∈ E.get i := by
      refine (hA i hi hy₀D.1 hy₀D.2).mpr ?_
      rw [show Φ.toFun (chartAt (ComplexModel n) z y₀) (σ i) = flatMap Φ y₀ (σ i) from rfl, hy₀eq _ hσi]
      exact (hA i hi hx.1 hx.2).mp hzi
    obtain ⟨a, ha, hna⟩ := (hy₀ev.self_of_nhds).2.2 i hi hy₀i
    have hahol := h𝔫hol y₀ a ha
    -- `a` does not vanish identically on `E_i` near `y₀`
    have hfa : ∃ᶠ p in 𝓝 y₀, p ∈ E.get i ∧ a p ≠ 0 := by
      intro hall
      exact hna ⟨hahol, hall.mono fun p hp hpi => not_not.mp fun h => hp ⟨hpi, h⟩⟩
    -- the other coordinates stay nonzero near `y₀`
    have hcont : ∀ j ∈ T.erase i, ∀ᶠ p in 𝓝 y₀, flatCoord Φ (σ j) p ≠ 0 := fun j hj =>
      (holomorphicAt_flatCoord Φ (σ j) hy₀D).continuousAt.eventually
        (isOpen_ne.mem_nhds (hy₀ne (σ j) (Finset.mem_image_of_mem σ hj)))
    obtain ⟨p, ⟨hpi, hap⟩, ⟨hpd, hpfac, -⟩, hpD, hpa, hpne⟩ := (hfa.and_eventually
      (hy₀ev.and (((isOpen_flatDomain Φ).eventually_mem hy₀D).and
        ((HadamardBridge.eventually_mem_of_isCoherent h𝔫 ha).and
          ((eventually_all_finset (T.erase i)).mpr hcont))))).exists
    -- `a m ∈ 𝔟_p` has order `b_i` at `p`, but `p ∈ cosupp(𝔟, b_i + 1)`
    have hmem : 𝔟.mem p (fun q => a q * m q) :=
      (hpfac _).mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨a, hpa, rfl⟩
        ((h𝔫hol p a hpa).mul (hmhol hpD)))
    have hord := mem_idealPow_of_vanishesToOrderOn_univ ((hpd hpi).2 _ hmem)
    have huh : HolomorphicAt n (flatCoord Φ (σ i)) p := holomorphicAt_flatCoord Φ (σ i) hpD
    have hu0 : flatCoord Φ (σ i) p = 0 := (hA i hi hpD.1 hpD.2).mp hpi
    have hrest : HolomorphicAt n (fun q => a q * ∏ j ∈ T.erase i, flatCoord Φ (σ j) q ^ b j) p :=
      (h𝔫hol p a hpa).mul (holomorphicAt_finset_prod _ fun j _ =>
        CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ j) hpD) (b j))
    have hrest0 : ¬ (idealPow (pointIdeal n p) (0 + 1)).mem p
        (fun q => a q * ∏ j ∈ T.erase i, flatCoord Φ (σ j) q ^ b j) := by
      intro h
      have h' := apply_eq_zero_of_mem_idealPow_pointIdeal (le_refl 1) h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact hap h''
      · exact Finset.prod_ne_zero_iff.mpr (fun j hj => pow_ne_zero _ (hpne j hj)) h''
    have hpow : ¬ (idealPow (pointIdeal n p) (b i + 1)).mem p (fun q => flatCoord Φ (σ i) q ^ b i) := by
      have := CompanionReduction.pow_notMem_idealPow huh (flatCoord_notMem_idealPow_two Φ (σ i) hpD) (b i)
      simpa using this
    have hprod := mul_notMem_idealPow hrest (CompanionReduction.holomorphicAt_pow_of huh (b i)) hrest0 hpow
    refine hprod (mem_idealPow_congr (by simpa using hord) (Eventually.of_forall fun q => ?_))
    change a q * ∏ j ∈ T, flatCoord Φ (σ j) q ^ b j =
      a q * (∏ j ∈ T.erase i, flatCoord Φ (σ j) q ^ b j) * flatCoord Φ (σ i) q ^ b i
    rw [mul_assoc, mul_comm (∏ j ∈ T.erase i, _), Finset.mul_prod_erase T (fun j => flatCoord Φ (σ j) q ^ b j) hi]
  have h1 := (isDivNear_iff_le_divExp h𝔟 hzi hne).mp hdiv
  have h2 : ¬ b i + 1 ≤ divExp n 𝔟 (E.get i) z := fun h => hndiv ((isDivNear_iff_le_divExp h𝔟 hzi hne).mpr h)
  omega


include hΦsrc hσ hA hfac hnd in
/-- **The monomial part of `𝔫 · (m)` is `(m)`** at `z` (`T` the members through `z`). -/
theorem monomialPart_mem_iff_of_mul_principal (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔫 : 𝔫.IsCoherent)
    (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y) (hT : ∀ i, i ∈ T ↔ z ∈ E.get i) (g : M → ℂ) :
    (monomialPart n 𝔟 E).mem z g ↔
      IsInSpanAt (n := n) (· = fun p => ∏ i ∈ T, flatCoord Φ (σ i) p ^ b i) z g := by
  classical
  have hx : z ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hexp : ∀ i ∈ T, divExp n 𝔟 (E.get i) z = b i := fun i hi =>
    divExp_eq_of_mul_principal hΦsrc hσ hA b hfac hnd h𝔫 h𝔟 hi ((hT i).mp hi)
  constructor
  · intro hg
    have hdiv : ∀ i ∈ T, ∃ c, HolomorphicAt n c z ∧ g =ᶠ[𝓝 z] fun p => c p * flatMap Φ p (σ i) ^ b i := by
      intro i hi
      have h1 := hg.2 i ((hT i).mp hi)
      rw [hexp i hi] at h1
      exact exists_eq_mul_pow_of_mem_idealPow
        (fun g hg => (vanishingIdeal_mem_iff_flatCoord Φ (hA i hi) hx g).mp hg) h1
    obtain ⟨c, hc, hgc⟩ := exists_eq_mul_prod_of_forall hΦsrc (A := fun i => E.get i) b hx T
      (fun i hi _ hy1 hy2 => hA i hi hy1 hy2) (fun i _ y hy => (isClosedSubmanifold_get hn hE i).2 y hy) hσ hg.1 hdiv
    exact isInSpanAt_eq_iff.mpr ⟨hg.1, c, hc, hgc⟩
  · intro hg
    obtain ⟨hgh, c, hc, hgc⟩ := isInSpanAt_eq_iff.mp hg
    refine ⟨hgh, fun i hzi => ?_⟩
    have hi := (hT i).mpr hzi
    rw [hexp i hi]
    exact mem_idealPow_congr (mul_mem_idealPow hc (flatMonomial_mem_idealPow_vanishingIdeal hA b hi)) hgc.symm

include hΦsrc hσ hA hfac hnd in
/-- **The nonmonomial part of `𝔫 · (m)` is `𝔫`** at `z` (`m` is a non-zero-divisor). -/
theorem nonmonomialPart_mem_iff_of_mul_principal (hn : 0 < n) (hE : IsSNCDivisor n E) (h𝔫 : 𝔫.IsCoherent)
    (h𝔟 : ∀ y g, 𝔟.mem y g → HolomorphicAt n g y) (hT : ∀ i, i ∈ T ↔ z ∈ E.get i) (h : M → ℂ) :
    (nonmonomialPart n 𝔟 E).mem z h ↔ 𝔫.mem z h := by
  classical
  have hx : z ∈ flatDomain Φ := mem_flatDomain_self Φ
  set m : M → ℂ := fun p => ∏ i ∈ T, flatCoord Φ (σ i) p ^ b i with hmdef
  have hmhol : HolomorphicAt n m z := holomorphicAt_flatMonomial (σ := σ) (T := T) b hx
  have hmM := monomialPart_mem_iff_of_mul_principal hΦsrc hσ hA b hfac hnd hn hE h𝔫 h𝔟 hT
  have h𝔫hol : ∀ y g, 𝔫.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔫 hg
  constructor
  · rintro ⟨hh, hall⟩
    have h1 := (hfac.self_of_nhds _).mp
      (hall m ((hmM m).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hmhol)))
    obtain ⟨-, K, s, c, hs, hc, hsum⟩ := h1
    choose a ha has using hs
    have hahol : ∀ k, HolomorphicAt n (a k) z := fun k => h𝔫hol z _ (ha k)
    have hdiff : HolomorphicAt n (fun p => h p - ∑ k, c k p * a k p) z :=
      GiraudAlong.holomorphicAt_sub hh (HolomorphicAt.sum _ fun k _ => (hc k).mul (hahol k))
    have hmne : ∃ᶠ p in 𝓝 z, m p ≠ 0 := by
      refine (frequently_flatMap_ne_zero hΦsrc hx (T.image σ)).mono fun p hp => ?_
      exact Finset.prod_ne_zero_iff.mpr fun j hj => pow_ne_zero _ (hp.2.1 (σ j) (Finset.mem_image_of_mem σ hj))
    have h0 := eventually_eq_zero_of_mul_eventually_eq_zero hdiff hmhol hmne (by
      filter_upwards [hsum] with p hp
      rw [sub_mul, hp, Finset.sum_mul]
      rw [sub_eq_zero]
      exact Finset.sum_congr rfl fun k _ => by rw [has k]; ring)
    refine GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔫 ⟨hh, K, a, c, ha, hc, ?_⟩
    filter_upwards [h0] with p hp
    exact sub_eq_zero.mp hp
  · intro hh
    have hhh := h𝔫hol z h hh
    refine ⟨hhh, fun m' hm' => ?_⟩
    obtain ⟨-, c, hc, hm'c⟩ := isInSpanAt_eq_iff.mp ((hmM m').mp hm')
    have hm'hol : HolomorphicAt n m' z := hm'.1
    refine (hfac.self_of_nhds _).mpr (isInSpanAt_of_eq_mul ⟨h, hh, rfl⟩ (hhh.mul hm'hol) hc ?_)
    filter_upwards [hm'c] with p hp
    rw [hp]
    ring

end Factorization

end

end Hironaka.NonmonomialTransform
