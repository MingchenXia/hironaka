import Hironaka.Resolution.HironakaG8LogFiniteSumCut

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The transform of the common-mark logarithmic sum (G8 lane, run 0080; leaf G8-3H-C09)

Blueprint: `hironaka-g8-resume-log-finite-sum-transform.tex`.

Let `π : Y → X` be the blowup along `C`, `N` a closed carrier with strict transform `N'`, `J = π^*𝓘_C`.  For ideals
`A_i` (`i < m`) with `A_i|_N ⊆ 𝓘_C^{d_i}|_N` and exponents `k_i` with `d_i k_i = L`
(`restrictLe_colonAlong_finSum_le`, `restrictLe_finSum_le_colonAlong`):

  `(π^*(∑_{i<m} A_i^{k_i}) : J^L)_{N'} = ∑_{i<m} ((π^*A_i : J^{d_i})_{N'})^{k_i}`   restricted to `N'`,

i.e. the transform of a common-mark sum is the common-mark sum of the transforms (Bierstone--Milman 2008, Lemma
3.8(2), for the common-mark sums of §3.4; Włodarczyk 2005, Lemma `le:operations`).  The proof is pointwise with a
generator `y` of `J` near `z ∈ N'`: every germ `a ∈ A_i` is `a ∘ π = y^{d_i} H + t ∘ π` with `H` in the transform and
`t ∈ 𝓘_N`; products and powers multiply these representations; `y^L` is cancelled on `N'` by density.

For the logarithmic family `𝔪_j = rawLogMarked 𝔪 j` of a well-formed marked ideal, an admissible centre and `k < d`
(`geoTransform_bmFiniteSum_rawLogMarked`, `cosupp_geoTransform_bmFiniteSum_rawLogMarked`):

* the transform of `𝓒^k(𝔪) = bmFiniteSum 𝔪_• (k + 1)` is restricted-equivalent to the common-mark sum of the
  transforms `𝔪_j'`, and restricted-contained in `𝓒^k(𝔪')` (with the controlled log inclusion
  `HironakaG8LogControlledMarked.geoTransform_rawLogMarked_le`);
* `cosupp 𝓒^k(𝔪)' = cosupp 𝓒^k(𝔪') = cosupp 𝔪'` (one step of BM08 Theorem 3.10).

Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LogFiniteSumTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.HomogenizedGlueing
  Hironaka.RelativePrincipalizationSpan Hironaka.RestrictedIdealExtension
  Hironaka.RestrictedIdealQuotient Hironaka.RestrictedIdealWeight
  Hironaka.BlowupStrictSubmanifold Hironaka.DerivativeIdealAlongTransform
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.HironakaActualIteratedLogMarkedFamily
  Hironaka.HironakaG8LogControlledInclusion
  Hironaka.HironakaG8LogControlledMarked
  Hironaka.HironakaG8LogFiniteSumCut

noncomputable section

/-! ### Representations `u = y^q K` on a set -/

section PowMul

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable (n) in
/-- `u = y^q K` on `W` near `z`, with `K` holomorphic and in the restricted span of the germs of `T` at `z`. -/
def IsPowMulOn (W : Set M) (T : GermIdeal n M) (y : M → ℂ) (q : ℕ) (z : M) (u : M → ℂ) : Prop :=
  ∃ K : M → ℂ, HolomorphicAt n K z ∧ IsInSpanOnAt (n := n) W (T.mem z) z K ∧
    ∀ᶠ p in 𝓝 z, p ∈ W → u p = y p ^ q * K p

variable {W : Set M} {y : M → ℂ} {z : M}

/-- Representations pass to holomorphic combinations. -/
theorem IsPowMulOn.of_isInSpanAt {T : GermIdeal n M} {q : ℕ} {S : (M → ℂ) → Prop}
    (hS : ∀ s, S s → IsPowMulOn n W T y q z s) {u : M → ℂ} (hu : IsInSpanAt (n := n) S z u) :
    IsPowMulOn n W T y q z u := by
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ := hu
  choose Ks hKs hKsspan hKseq using fun i => hS (s i) (hs i)
  refine ⟨fun p => ∑ i, c i p * Ks i p, HolomorphicAt.sum _ fun i _ => (hc i).mul (hKs i),
    IsInSpanOnAt.sum _ fun i _ => IsInSpanOnAt.mul_left (hc i) (hKsspan i), ?_⟩
  filter_upwards [hsum, eventually_all.2 hKseq] with p hp1 hp2 hpW
  rw [hp1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hp2 i hpW]; ring

/-- Representations are monotone in the target ideal. -/
theorem IsPowMulOn.mono {T T' : GermIdeal n M} {q : ℕ} (hT : ∀ s, T.mem z s → T'.mem z s) {u : M → ℂ}
    (hu : IsPowMulOn n W T y q z u) : IsPowMulOn n W T' y q z u := by
  obtain ⟨K, hK, hKspan, hKeq⟩ := hu
  exact ⟨K, hK, IsInSpanOnAt.mono hT hKspan, hKeq⟩

/-- Representations multiply. -/
theorem IsPowMulOn.mul {T₁ T₂ : GermIdeal n M} {q r : ℕ}
    (h₁ : ∀ g, T₁.mem z g → HolomorphicAt n g z) (h₂ : ∀ g, T₂.mem z g → HolomorphicAt n g z)
    {u v : M → ℂ} (hu : IsPowMulOn n W T₁ y q z u) (hv : IsPowMulOn n W T₂ y r z v) :
    IsPowMulOn n W (T₁.mul T₂) y (q + r) z (fun p => u p * v p) := by
  obtain ⟨K₁, hK₁, hK₁span, hK₁eq⟩ := hu
  obtain ⟨K₂, hK₂, hK₂span, hK₂eq⟩ := hv
  refine ⟨fun p => K₁ p * K₂ p, hK₁.mul hK₂, ?_, ?_⟩
  · refine IsInSpanOnAt.mono ?_ (MarkedIdealOperationsAlong.IsInSpanOnAt.mul hK₁span hK₂span)
    rintro _ ⟨a, b, ha, hb, rfl⟩
    exact IdealOrderArithmetic.mul_mem_mul ha hb ((h₁ a ha).mul (h₂ b hb))
  · filter_upwards [hK₁eq, hK₂eq] with p hp1 hp2 hpW
    rw [hp1 hpW, hp2 hpW, pow_add]
    ring

/-- The unit ideal represents every holomorphic germ with `q = 0`. -/
theorem isPowMulOn_unit {u : M → ℂ} (hu : HolomorphicAt n u z) : IsPowMulOn n W (unitIdeal n M) y 0 z u :=
  ⟨u, hu, IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self (S := (unitIdeal n M).mem z) hu hu),
    Eventually.of_forall fun p _ => by simp⟩

/-- `y^q u` stays in a restricted span under holomorphic combinations of `u`. -/
theorem isInSpanOnAt_pow_mul_of_isInSpanAt {S T : (M → ℂ) → Prop} {q : ℕ}
    (hS : ∀ s, S s → IsInSpanOnAt (n := n) W T z (fun p => y p ^ q * s p)) {u : M → ℂ}
    (hu : IsInSpanAt (n := n) S z u) : IsInSpanOnAt (n := n) W T z (fun p => y p ^ q * u p) := by
  obtain ⟨-, K, s, c, hs, hc, hsum⟩ := hu
  refine IsInSpanOnAt.congr_right (IsInSpanOnAt.sum Finset.univ fun i _ =>
    IsInSpanOnAt.mul_left (hc i) (hS (s i) (hs i))) ?_
  filter_upwards [hsum] with p hp _
  rw [hp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `y^q u` and `y^r v` in restricted spans give `y^{q+r} u v` in the span of the products. -/
theorem isInSpanOnAt_pow_mul_mul {S T R : (M → ℂ) → Prop} {q r : ℕ} {u v : M → ℂ}
    (hR : ∀ s t, S s → T t → R (fun p => s p * t p))
    (hu : IsInSpanOnAt (n := n) W S z (fun p => y p ^ q * u p))
    (hv : IsInSpanOnAt (n := n) W T z (fun p => y p ^ r * v p)) :
    IsInSpanOnAt (n := n) W R z (fun p => y p ^ (q + r) * (u p * v p)) := by
  refine IsInSpanOnAt.congr_right (IsInSpanOnAt.mono ?_ (MarkedIdealOperationsAlong.IsInSpanOnAt.mul hu hv)) ?_
  · rintro _ ⟨s, t, hs, ht, rfl⟩
    exact hR s t hs ht
  · exact Eventually.of_forall fun p _ => by simp only [Pi.mul_apply]; ring

/-- A germ of a finite sum. -/
theorem mem_finSumIdeal_of_mem {J : ℕ → GermIdeal n M} {m i : ℕ} (hi : i < m) {x : M} {g : M → ℂ}
    (hg : (J i).mem x g) (hgh : HolomorphicAt n g x) : (finSumIdeal J m).mem x g :=
  InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ i, i < m ∧ (J i).mem x s) ⟨i, hi, hg⟩ hgh

/-- Finite sums only see their first `m` summands. -/
theorem finSumIdeal_congr {J J' : ℕ → GermIdeal n M} {m : ℕ} (h : ∀ i < m, J i = J' i) :
    finSumIdeal J m = finSumIdeal J' m := by
  apply GermIdeal.ext
  funext x g
  apply propext
  constructor
  · intro hg
    have hg' : IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem x s) x g := hg
    show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J' i).mem x s) x g
    exact hg'.mono fun s ⟨i, hi, hs⟩ => ⟨i, hi, h i hi ▸ hs⟩
  · intro hg
    have hg' : IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J' i).mem x s) x g := hg
    show IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem x s) x g
    exact hg'.mono fun s ⟨i, hi, hs⟩ => ⟨i, hi, (h i hi).symm ▸ hs⟩

/-- Restricted inclusions of the summands give a restricted inclusion of the finite sums. -/
theorem restrictLe_finSumIdeal {J J' : ℕ → GermIdeal n M} {m : ℕ}
    (hJ' : ∀ i < m, ∀ x g, (J' i).mem x g → HolomorphicAt n g x) (h : ∀ i < m, RestrictLe W (J i) (J' i)) :
    RestrictLe W (finSumIdeal J m) (finSumIdeal J' m) := by
  intro x hx g hg
  have hg' : IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (J i).mem x s) x g := hg
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict hg')
  rintro s ⟨i, hi, hs⟩
  exact IsInSpanOnAt.mono (fun t ht => mem_finSumIdeal_of_mem hi ht (hJ' i hi x t ht)) (h i hi x hx s hs)

end PowMul

/-! ### Pointwise calculus on the blowup -/

section Blowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} {z : Y} {U : Set Y} {y : Y → ℂ}

/-- **Colons along a set by a power of `J = π^*𝓘_C`, through the generator**: `g` is in `(B : J^q)_W` at `z` iff
`g` is holomorphic and `y^q g` is in the restricted span of `B` at `z`. -/
theorem mem_colonAlong_iff_of_uniform (hy : IsUniformDerivationGenerator n π C z U y) {W : Set Y}
    {B : GermIdeal n Y} {q : ℕ} {g : Y → ℂ} :
    (colonAlong n W B (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) q)).mem z g ↔
      HolomorphicAt n g z ∧ IsInSpanOnAt (n := n) W (B.mem z) z (fun p => y p ^ q * g p) := by
  have hyz : HolomorphicAt n y z := hy.holomorphicAt z hy.mem
  have hpow := BlowupDerivativeIdeal.idealPow_mem_iff_of_generator hy.holomorphicAt hy.generates q z hy.mem
  constructor
  · rintro ⟨hg, hall⟩
    exact ⟨hg, (hall _ ((hpow _).mpr (isInSpanAt_of_eq_mul rfl (BlowupDerivativeIdeal.holomorphicAt_pow hyz q)
      (holomorphicAt_const 1) (Eventually.of_forall fun p => by simp)))).2⟩
  · rintro ⟨hg, hspan⟩
    refine ⟨hg, fun ℓ hℓ => ?_⟩
    obtain ⟨hℓhol, d, hd, hℓd⟩ := isInSpanAt_eq_iff.mp ((hpow ℓ).mp hℓ)
    refine ⟨hℓhol.mul hg, IsInSpanOnAt.congr_right (IsInSpanOnAt.mul_left hd hspan) ?_⟩
    filter_upwards [hℓd] with p hp _
    simp only [hp]
    ring

/-- **Cancellation of `y^q` on the strict transform**: if `y^q g` is a combination of germs `v` of `B`, each with
`v = y^q K_v` on `N'` and `K_v` in the restricted span of `T`, then `g` is in the restricted span of `T`. -/
theorem isInSpanOnAt_of_isPowMulOn (hπ : IsBlowupAlong n C π) {N : Set X}
    (hy : IsUniformDerivationGenerator n π C z U y) {B T : GermIdeal n Y} {q : ℕ}
    (hB : ∀ v, B.mem z v → IsPowMulOn n (geoStrictTransform π C N) T y q z v) {g : Y → ℂ}
    (hg : HolomorphicAt n g z)
    (hspan : IsInSpanOnAt (n := n) (geoStrictTransform π C N) (B.mem z) z (fun p => y p ^ q * g p)) :
    IsInSpanOnAt (n := n) (geoStrictTransform π C N) (T.mem z) z g := by
  obtain ⟨K, v, c, hv, hc, hsum⟩ := hspan
  choose Kv hKv hKvspan hKveq using fun j => hB (v j) (hv j)
  have hKtot : HolomorphicAt n (fun p => ∑ j, c j p * Kv j p) z :=
    HolomorphicAt.sum _ fun j _ => (hc j).mul (hKv j)
  have hcanc := eventually_eq_on_of_pow_mul hπ hy (N := N) q (g := g)
    (G := fun p => ∑ j, c j p * Kv j p) (hg.eventually.mono fun p hp => hp.continuousAt)
    (hKtot.eventually.mono fun p hp => hp.continuousAt) (by
      filter_upwards [hsum, eventually_all.2 hKveq] with p hp1 hp2 hpN
      rw [hp1 hpN, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hp2 j hpN]; ring)
  exact IsInSpanOnAt.congr_right (IsInSpanOnAt.sum _ fun j _ => IsInSpanOnAt.mul_left (hc j) (hKvspan j)) hcanc

/-- Representations of the generators `a ∘ π` give representations of the pulled-back ideal. -/
theorem isPowMulOn_of_mem_pullback {W : Set Y} {B : GermIdeal n X} {T : GermIdeal n Y} {q : ℕ}
    (hB : ∀ s, B.mem (π z) s → IsPowMulOn n W T y q z (fun p => s (π p))) {v : Y → ℂ}
    (hv : (GermIdeal.pullback (m := n) π B).mem z v) : IsPowMulOn n W T y q z v := by
  have hv' : IsInSpanAt (n := n) (fun s => ∃ a, B.mem (π z) a ∧ s = a ∘ π) z v := hv
  refine IsPowMulOn.of_isInSpanAt ?_ hv'
  rintro s ⟨a, ha, rfl⟩
  exact hB a ha

/-- A holomorphic combination at `π z` composes to a holomorphic combination at `z`. -/
theorem isInSpanAt_comp (hπs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {S : (X → ℂ) → Prop}
    {b : X → ℂ} (hb : IsInSpanAt (n := n) S (π z) b) :
    IsInSpanAt (n := n) (fun t => ∃ s, S s ∧ t = fun p => s (π p)) z (fun p => b (π p)) := by
  obtain ⟨hbhol, K, s, c, hs, hc, hsum⟩ := hb
  refine ⟨hbhol.comp_contMDiff (Eventually.of_forall fun p => hπs p), K, fun i p => s i (π p),
    fun i p => c i (π p), fun i => ⟨s i, hs i, rfl⟩,
    fun i => (hc i).comp_contMDiff (Eventually.of_forall fun p => hπs p), ?_⟩
  filter_upwards [(hπs z).continuousAt.eventually hsum] with p hp
  exact hp

/-- **Powers**: representations `a ∘ π = y^d K` of the germs of `A` give representations
`b ∘ π = y^{dk} K` of the germs of `A^k`, with `K` in the span of `A'^k`. -/
theorem isPowMulOn_comp_idealPow (hπs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {W : Set Y} {A : GermIdeal n X} {A' : GermIdeal n Y} {d : ℕ} (hA' : ∀ g, A'.mem z g → HolomorphicAt n g z)
    (hbase : ∀ s, A.mem (π z) s → IsPowMulOn n W A' y d z (fun p => s (π p))) :
    ∀ k b, (idealPow A k).mem (π z) b → IsPowMulOn n W (idealPow A' k) y (d * k) z (fun p => b (π p))
  | 0, b, hb => isPowMulOn_unit
      ((show HolomorphicAt n b (π z) from hb).comp_contMDiff (Eventually.of_forall fun p => hπs p))
  | k + 1, b, hb => by
    have hb' : IsInSpanAt (n := n) (fun t => ∃ a c, (idealPow A k).mem (π z) a ∧ A.mem (π z) c ∧ t = a * c)
        (π z) b := hb
    refine IsPowMulOn.of_isInSpanAt ?_ (isInSpanAt_comp hπs hb')
    rintro _ ⟨_, ⟨a, c, ha, hc, rfl⟩, rfl⟩
    have h := IsPowMulOn.mul (fun g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg) hA'
      (isPowMulOn_comp_idealPow hπs hA' hbase k a ha) (hbase c hc)
    rw [show d * (k + 1) = d * k + d by ring]
    exact h

/-- **The basic representation** (`A|_N ⊆ 𝓘_C^q|_N`): for `s ∈ A` at `π z`, `z ∈ N'`, `s ∘ π = y^q H` on `N'` with `H`
in the transform `(π^*A : J^q)_{N'}`. -/
theorem isPowMulOn_comp_of_restrictLe (hπ : IsBlowupAlong n C π) {N : Set X} (hN : IsClosed N)
    {𝔞 : GermIdeal n X} (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {q : ℕ}
    (hle : RestrictLe N 𝔞 (idealPow (vanishingIdeal (n := n) C) q)) (hzN : z ∈ geoStrictTransform π C N)
    (hy : IsUniformDerivationGenerator n π C z U y) {s : X → ℂ} (hs : 𝔞.mem (π z) s) :
    IsPowMulOn n (geoStrictTransform π C N)
      (colonAlong n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π 𝔞)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) q)) y q z (fun p => s (π p)) := by
  classical
  set N' := geoStrictTransform π C N with hN'
  set J := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) with hJ
  have hπs := hπ.contMDiff
  have hπc : ContinuousAt π z := (hπs z).continuousAt
  have hcomp : ∀ {f : X → ℂ}, HolomorphicAt n f (π z) → HolomorphicAt n (fun p => f (π p)) z := fun hf =>
    hf.comp_contMDiff (Eventually.of_forall fun p => hπs p)
  have hxN : π z ∈ N := geoStrictTransform_subset_preimage hπs.continuous hN hzN
  have hpow : ∀ q, ∀ p ∈ U, ∀ g, (idealPow J q).mem p g ↔
      IsInSpanAt (n := n) (· = fun p => y p ^ q) p g :=
    BlowupDerivativeIdeal.idealPow_mem_iff_of_generator hy.holomorphicAt hy.generates
  obtain ⟨K, h, a, hh, ha, hsum⟩ := hle (π z) hxN s hs
  have hhhol : ∀ k, HolomorphicAt n (h k) (π z) := fun k => GermIdealOrder.holomorphicAt_of_mem_idealPow (hh k)
  set t : X → ℂ := fun q => s q - ∑ k, a k q * h k q with ht
  have htN : ∀ᶠ p in 𝓝 z, p ∈ N' → t (π p) = 0 := by
    filter_upwards [hπc.eventually hsum] with p hp hpN
    have hpN' : π p ∈ N := geoStrictTransform_subset_preimage hπs.continuous hN hpN
    simp only [ht, hp hpN', sub_self]
  have hHk : ∀ k, ∃ Hk : Y → ℂ, HolomorphicAt n Hk z ∧
      (fun p => h k (π p)) =ᶠ[𝓝 z] fun p => Hk p * y p ^ q := by
    intro k
    have h1 : (GermIdeal.pullback (m := n) π (idealPow (vanishingIdeal (n := n) C) q)).mem z
        (fun p => h k (π p)) :=
      BlowupDerivativeIdeal.comp_mem_pullback (hh k) (hcomp (hhhol k)) (holomorphicAt_const 1)
        (Eventually.of_forall fun p => by simp)
    have h2 := BlowupControlledTransform.pullback_le_idealPow_exceptionalDivisor hπ (fun _ _ h => h) z _ h1
    obtain ⟨-, Hk, hHk, hHkeq⟩ := isInSpanAt_eq_iff.mp ((hpow q z hy.mem _).mp h2)
    exact ⟨Hk, hHk, hHkeq⟩
  choose Hk hHk hHkeq using hHk
  set H : Y → ℂ := fun p => ∑ k, a k (π p) * Hk k p with hHdef
  have hHhol : HolomorphicAt n H z := HolomorphicAt.sum _ fun k _ => (hcomp (ha k)).mul (hHk k)
  have hsH : (fun p => s (π p)) =ᶠ[𝓝 z] fun p => y p ^ q * H p + t (π p) := by
    filter_upwards [eventually_all.2 hHkeq] with p hp
    have e1 : ∑ k, a k (π p) * h k (π p) = y p ^ q * H p := by
      simp only [hHdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hp k]; ring
    simp only [ht, e1]
    ring
  have hsπ : (GermIdeal.pullback (m := n) π 𝔞).mem z (fun p => s (π p)) :=
    BlowupDerivativeIdeal.comp_mem_pullback hs (hcomp (h𝔞 _ _ hs)) (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp)
  have hHmem : (colonAlong n N' (GermIdeal.pullback (m := n) π 𝔞) (idealPow J q)).mem z H := by
    refine ⟨hHhol, fun ℓ hℓ => ⟨(GermIdealOrder.holomorphicAt_of_mem_idealPow hℓ).mul hHhol, ?_⟩⟩
    obtain ⟨-, d, hd, hℓd⟩ := isInSpanAt_eq_iff.mp ((hpow q z hy.mem ℓ).mp hℓ)
    refine IsInSpanOnAt.congr_right (g := fun p => d p * s (π p))
      (IsInSpanAt.restrict (isInSpanAt_of_eq_mul hsπ (hd.mul (hcomp (h𝔞 _ _ hs))) hd
        (Eventually.of_forall fun p => rfl))) ?_
    filter_upwards [hℓd, hsH, htN] with p hp1 hp2 hp3 hpN
    rw [hp1, hp2, hp3 hpN]
    ring
  refine ⟨H, hHhol, IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hHmem hHhol), ?_⟩
  filter_upwards [hsH, htN] with p hp1 hp2 hpN
  rw [hp1, hp2 hpN, add_zero]

/-- **Products of transforms map into the transform of the power**: for `w` in `((π^*A : J^d)_W)^k` at `z`, `y^{dk} w`
is in the restricted span of the germs `a ∘ π`, `a ∈ A^k` at `π z`. -/
theorem isInSpanOnAt_pow_mul_of_mem_idealPow_colonAlong (hy : IsUniformDerivationGenerator n π C z U y)
    {W : Set Y} {A : GermIdeal n X} (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) {d : ℕ} :
    ∀ k w, (idealPow (colonAlong n W (GermIdeal.pullback (m := n) π A)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) d)) k).mem z w →
      IsInSpanOnAt (n := n) W (fun t => ∃ a, (idealPow A k).mem (π z) a ∧ t = fun p => a (π p)) z
        (fun p => y p ^ (d * k) * w p)
  | 0, w, hw => by
    refine ⟨1, fun _ _ => 1, fun _ => w, fun _ => ⟨fun _ => 1, holomorphicAt_const 1, rfl⟩,
      fun _ => hw, ?_⟩
    exact Eventually.of_forall fun p _ => by simp
  | k + 1, w, hw => by
    have hw' : IsInSpanAt (n := n) (fun t => ∃ a b, (idealPow (colonAlong n W (GermIdeal.pullback (m := n) π A)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) d)) k).mem z a ∧
        (colonAlong n W (GermIdeal.pullback (m := n) π A)
          (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) d)).mem z b ∧ t = a * b) z w := hw
    refine isInSpanOnAt_pow_mul_of_isInSpanAt (fun s hs => ?_) hw'
    obtain ⟨a, b, ha, hb, rfl⟩ := hs
    have h1 := isInSpanOnAt_pow_mul_of_mem_idealPow_colonAlong hy hA k a ha
    have h2 : IsInSpanOnAt (n := n) W (fun t => ∃ c, A.mem (π z) c ∧ t = fun p => c (π p)) z
        (fun p => y p ^ d * b p) := by
      refine IsInSpanOnAt.trans (fun v hv => IsInSpanAt.restrict ?_) ((mem_colonAlong_iff_of_uniform hy).mp hb).2
      exact hv
    have h3 := isInSpanOnAt_pow_mul_mul
      (R := fun t => ∃ a, (idealPow A (k + 1)).mem (π z) a ∧ t = fun p => a (π p)) ?_ h1 h2
    · rw [show d * (k + 1) = d * k + d by ring]
      exact h3
    · rintro _ _ ⟨a', ha', rfl⟩ ⟨c', hc', rfl⟩
      exact ⟨fun x => a' x * c' x, IdealOrderArithmetic.mul_mem_mul ha' hc'
        ((GermIdealOrder.holomorphicAt_of_mem_idealPow ha').mul (hA _ _ hc')), rfl⟩

/-- **The transform of a common-mark sum lies in the sum of the transforms** (on `N'`): if `A_i|_N ⊆ 𝓘_C^{d_i}|_N`
and `d_i k_i = L` for `i < m`, then `(π^*(∑ A_i^{k_i}) : J^L)_{N'} ⊆ ∑ ((π^*A_i : J^{d_i})_{N'})^{k_i}` on `N'`. -/
theorem restrictLe_colonAlong_finSum_le (hπ : IsBlowupAlong n C π) {N : Set X} (hN : IsClosed N)
    {A : ℕ → GermIdeal n X} {d k : ℕ → ℕ} {m L : ℕ}
    (hA : ∀ i < m, ∀ x g, (A i).mem x g → HolomorphicAt n g x)
    (hle : ∀ i < m, RestrictLe N (A i) (idealPow (vanishingIdeal (n := n) C) (d i)))
    (hdk : ∀ i < m, d i * k i = L) :
    RestrictLe (geoStrictTransform π C N)
      (colonAlong n (geoStrictTransform π C N)
        (GermIdeal.pullback (m := n) π (finSumIdeal (fun i => idealPow (A i) (k i)) m))
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) L))
      (finSumIdeal (fun i => idealPow (colonAlong n (geoStrictTransform π C N)
        (GermIdeal.pullback (m := n) π (A i))
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (d i))) (k i)) m) := by
  intro z hzN g hg
  obtain ⟨U, y, hy⟩ := exists_isUniformDerivationGenerator hπ z
  obtain ⟨hgh, hspan⟩ := (mem_colonAlong_iff_of_uniform hy).mp hg
  refine isInSpanOnAt_of_isPowMulOn hπ hy (fun v hv => isPowMulOn_of_mem_pullback (fun s hs => ?_) hv) hgh hspan
  have hs' : IsInSpanAt (n := n) (fun t => ∃ i, i < m ∧ (idealPow (A i) (k i)).mem (π z) t) (π z) s := hs
  refine IsPowMulOn.of_isInSpanAt ?_ (isInSpanAt_comp hπ.contMDiff hs')
  rintro _ ⟨t, ⟨i, hi, ht⟩, rfl⟩
  have h := isPowMulOn_comp_idealPow (A' := colonAlong n (geoStrictTransform π C N)
      (GermIdeal.pullback (m := n) π (A i))
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (d i))) hπ.contMDiff
    (fun g hg => hg.1)
    (fun s hs => isPowMulOn_comp_of_restrictLe hπ hN (hA i hi) (hle i hi) hzN hy hs) (k i) t ht
  rw [hdk i hi] at h
  refine h.mono fun w hw => ?_
  exact mem_finSumIdeal_of_mem hi hw (GermIdealOrder.holomorphicAt_of_mem_idealPow hw)

/-- **The sum of the transforms lies in the transform of the common-mark sum** (on `N'`): if `d_i k_i = L` for
`i < m`, then `∑ ((π^*A_i : J^{d_i})_{N'})^{k_i} ⊆ (π^*(∑ A_i^{k_i}) : J^L)_{N'}` on `N'`. -/
theorem restrictLe_finSum_le_colonAlong (hπ : IsBlowupAlong n C π) {N : Set X}
    {A : ℕ → GermIdeal n X} {d k : ℕ → ℕ} {m L : ℕ}
    (hA : ∀ i < m, ∀ x g, (A i).mem x g → HolomorphicAt n g x) (hdk : ∀ i < m, d i * k i = L) :
    RestrictLe (geoStrictTransform π C N)
      (finSumIdeal (fun i => idealPow (colonAlong n (geoStrictTransform π C N)
        (GermIdeal.pullback (m := n) π (A i))
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (d i))) (k i)) m)
      (colonAlong n (geoStrictTransform π C N)
        (GermIdeal.pullback (m := n) π (finSumIdeal (fun i => idealPow (A i) (k i)) m))
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) L)) := by
  intro z _ h hh
  obtain ⟨U, y, hy⟩ := exists_isUniformDerivationGenerator hπ z
  have hh' : IsInSpanAt (n := n) (fun s => ∃ i, i < m ∧ (idealPow (colonAlong n (geoStrictTransform π C N)
      (GermIdeal.pullback (m := n) π (A i))
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (d i))) (k i)).mem z s) z h := hh
  have hmem : (colonAlong n (geoStrictTransform π C N)
      (GermIdeal.pullback (m := n) π (finSumIdeal (fun i => idealPow (A i) (k i)) m))
      (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) L)).mem z h := by
    refine (mem_colonAlong_iff_of_uniform hy).mpr ⟨hh'.1, ?_⟩
    refine isInSpanOnAt_pow_mul_of_isInSpanAt (fun s hs => ?_) hh'
    obtain ⟨i, hi, hsi⟩ := hs
    have h1 := isInSpanOnAt_pow_mul_of_mem_idealPow_colonAlong hy (hA i hi) (k i) s hsi
    rw [hdk i hi] at h1
    refine IsInSpanOnAt.mono (fun t ht => ?_) h1
    obtain ⟨a, ha, rfl⟩ := ht
    have hahol : HolomorphicAt n a (π z) := GermIdealOrder.holomorphicAt_of_mem_idealPow ha
    exact BlowupDerivativeIdeal.comp_mem_pullback (mem_finSumIdeal_of_mem hi ha hahol)
      (hahol.comp_contMDiff (Eventually.of_forall fun p => hπ.contMDiff p)) (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp)
  exact IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hmem hh'.1)

end Blowup

/-! ### Common-mark sums of marked ideals -/

section Marked

variable {n : ℕ} {X Y : CMfd.{0} n} {C : Set X} {π : Y → X}

/-- **The transform of a common-mark sum is the common-mark sum of the transforms** (BM08 Lemma 3.8(2), for the
`lcm` sums of §3.4): for marked ideals `Q i` (`i < m`) on one closed carrier with positive marks, holomorphic germs and
`(Q i).ideal|_N ⊆ 𝓘_C^{d_i}|_N` (e.g. `C` admissible for each `Q i`), the transform of `bmFiniteSum Q m` and
`bmFiniteSum` of the transforms have the same carrier, boundary and mark, and their ideals agree on the strict
transform (two restricted inclusions). -/
theorem geoTransform_bmFiniteSum_restrictEquiv (Q : ℕ → MarkedIdeal n X) (m : ℕ) (hN : IsClosed (Q 0).N)
    (hSameN : ∀ i < m, (Q i).N = (Q 0).N) (hPos : ∀ i < m, 0 < (Q i).d)
    (hhol : ∀ i < m, ∀ x g, (Q i).ideal.mem x g → HolomorphicAt n g x)
    (hle : ∀ i < m, RestrictLe (Q 0).N (Q i).ideal (idealPow (vanishingIdeal (n := n) C) (Q i).d))
    (hπ : IsBlowupAlong n C π) :
    ((bmFiniteSum Q m).geoTransform C π).N = (bmFiniteSum (fun i => (Q i).geoTransform C π) m).N ∧
      ((bmFiniteSum Q m).geoTransform C π).E = (bmFiniteSum (fun i => (Q i).geoTransform C π) m).E ∧
      ((bmFiniteSum Q m).geoTransform C π).d = (bmFiniteSum (fun i => (Q i).geoTransform C π) m).d ∧
      RestrictLe (geoStrictTransform π C (Q 0).N) ((bmFiniteSum Q m).geoTransform C π).ideal
        (bmFiniteSum (fun i => (Q i).geoTransform C π) m).ideal ∧
      RestrictLe (geoStrictTransform π C (Q 0).N) (bmFiniteSum (fun i => (Q i).geoTransform C π) m).ideal
        ((bmFiniteSum Q m).geoTransform C π).ideal := by
  obtain ⟨-, hspec⟩ := bmCommonMark_spec Q m hPos
  have hcongr : (bmFiniteSum (fun i => (Q i).geoTransform C π) m).ideal =
      finSumIdeal (fun i => idealPow (colonAlong n (geoStrictTransform π C (Q 0).N)
        (GermIdeal.pullback (m := n) π (Q i).ideal)
        (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) (Q i).d))
        (bmCommonMark Q m / (Q i).d)) m :=
    finSumIdeal_congr fun i hi => by
      show idealPow (colonAlong n (geoStrictTransform π C (Q i).N) _ _) _ = _
      rw [hSameN i hi]
      rfl
  have hdk : ∀ i < m, (Q i).d * (bmCommonMark Q m / (Q i).d) = bmCommonMark Q m :=
    fun i hi => (hspec i hi).2.2
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rw [hcongr]
    exact restrictLe_colonAlong_finSum_le (A := fun i => (Q i).ideal) (d := fun i => (Q i).d)
      (k := fun i => bmCommonMark Q m / (Q i).d) hπ hN hhol hle hdk
  · rw [hcongr]
    exact restrictLe_finSum_le_colonAlong (A := fun i => (Q i).ideal) (d := fun i => (Q i).d)
      (k := fun i => bmCommonMark Q m / (Q i).d) hπ hhol hdk

/-- For an admissible centre of a well-formed `𝔪` and `i ≤ d`: `(𝓓_{N,E}^i 𝔞)|_N ⊆ 𝓘_C^{d-i}|_N`. -/
theorem restrictLe_rawLogMarked_idealPow (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hC : 𝔪.IsAdmissibleCentre C) {i : ℕ} (hi : i ≤ 𝔪.d) :
    RestrictLe 𝔪.N (rawLogMarked 𝔪 i).ideal (idealPow (vanishingIdeal (n := n) C) (rawLogMarked 𝔪 i).d) := by
  have h𝔞hol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔪.isCoherent hg
  exact HadamardBridgeAlong.restrictLe_idealPow_vanishingIdeal_of_subset_cosupport
    (rawIter_coherent 𝔪.ideal h𝔪.isCoherent h𝔪.isClosedSubmanifold_N h𝔪.isSNCDivisor h𝔪.isTransverse i)
    h𝔪.isClosedSubmanifold_N hC.1 hC.subset_N (hC.2.1.trans (cosupp_subset_cosupp_rawLogMarked 𝔪 h𝔞hol hi))

/-- **One blowup of the logarithmic closure** `𝓒^k(𝔪) = bmFiniteSum (rawLogMarked 𝔪) (k + 1)`, `k < d` (BM08 Lemma
3.8(2) and Corollary 3.4, logarithmic): for a well-formed `𝔪` and an admissible centre, the transform of `𝓒^k(𝔪)` is
restricted-equivalent to the common-mark sum of the transforms `(𝔪_i)'`, has the carrier, boundary and mark of
`𝓒^k(𝔪')`, and its ideal is contained in that of `𝓒^k(𝔪')` on `N'`. -/
theorem geoTransform_bmFiniteSum_rawLogMarked (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {k : ℕ} (hk : k < 𝔪.d) :
    RestrictLe (geoStrictTransform π C 𝔪.N) ((bmFiniteSum (rawLogMarked 𝔪) (k + 1)).geoTransform C π).ideal
        (bmFiniteSum (fun i => (rawLogMarked 𝔪 i).geoTransform C π) (k + 1)).ideal ∧
      RestrictLe (geoStrictTransform π C 𝔪.N)
        (bmFiniteSum (fun i => (rawLogMarked 𝔪 i).geoTransform C π) (k + 1)).ideal
        ((bmFiniteSum (rawLogMarked 𝔪) (k + 1)).geoTransform C π).ideal ∧
      ((bmFiniteSum (rawLogMarked 𝔪) (k + 1)).geoTransform C π).N =
        (bmFiniteSum (rawLogMarked (𝔪.geoTransform C π)) (k + 1)).N ∧
      ((bmFiniteSum (rawLogMarked 𝔪) (k + 1)).geoTransform C π).E =
        (bmFiniteSum (rawLogMarked (𝔪.geoTransform C π)) (k + 1)).E ∧
      ((bmFiniteSum (rawLogMarked 𝔪) (k + 1)).geoTransform C π).d =
        (bmFiniteSum (rawLogMarked (𝔪.geoTransform C π)) (k + 1)).d ∧
      RestrictLe (geoStrictTransform π C 𝔪.N) ((bmFiniteSum (rawLogMarked 𝔪) (k + 1)).geoTransform C π).ideal
        (bmFiniteSum (rawLogMarked (𝔪.geoTransform C π)) (k + 1)).ideal := by
  have h𝔞hol : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔪.isCoherent hg
  obtain ⟨-, -, -, h1, h2⟩ := geoTransform_bmFiniteSum_restrictEquiv (rawLogMarked 𝔪) (k + 1)
    h𝔪.isClosedSubmanifold_N.1 (fun _ _ => rfl) (rawLogMarked_d_pos 𝔪 hk)
    (fun i _ => holomorphicAt_of_mem_logIter h𝔞hol i)
    (fun i hi => restrictLe_rawLogMarked_idealPow 𝔪 h𝔪 hC (by omega)) hπ
  refine ⟨h1, h2, rfl, rfl, rfl, restrictLe_trans h1 ?_⟩
  refine restrictLe_finSumIdeal (fun i _ x g hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg) fun i hi => ?_
  obtain ⟨-, -, -, -, hi'⟩ := geoTransform_rawLogMarked_le 𝔪 h𝔪 hC hπ (j := i) (by omega)
  have hhol' : ∀ x g, (rawLogMarked (𝔪.geoTransform C π) i).ideal.mem x g → HolomorphicAt n g x :=
    holomorphicAt_of_mem_logIter (A := (𝔪.geoTransform C π).ideal) (fun _ _ hg => hg.1) i
  exact MarkedIdealOperationsAlong.restrictLe_idealPow hhol' hi' _

/-- **The cut of the logarithmic closure after one blowup** (one step of BM08 Theorem 3.10, logarithmic): for a
well-formed `𝔪`, an admissible centre and `k < d`, `cosupp 𝓒^k(𝔪)' = cosupp 𝔪'` and `cosupp 𝓒^k(𝔪') = cosupp 𝔪'`. -/
theorem cosupp_geoTransform_bmFiniteSum_rawLogMarked (𝔪 : MarkedIdeal n X) (h𝔪 : 𝔪.IsWellFormed)
    (hC : 𝔪.IsAdmissibleCentre C) (hπ : IsBlowupAlong n C π) {k : ℕ} (hk : k < 𝔪.d) :
    ((bmFiniteSum (rawLogMarked 𝔪) (k + 1)).geoTransform C π).cosupp = (𝔪.geoTransform C π).cosupp ∧
      (bmFiniteSum (rawLogMarked (𝔪.geoTransform C π)) (k + 1)).cosupp = (𝔪.geoTransform C π).cosupp := by
  have hN' : IsClosedSubmanifold n (𝔪.geoTransform C π).N :=
    MarkedIdeals.MarkedIdeal.isClosedSubmanifold_geoTransform_N h𝔪.isClosedSubmanifold_N hC hπ
  have h𝔞'hol : ∀ x g, (𝔪.geoTransform C π).ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => hg.1
  have hk' : k < (𝔪.geoTransform C π).d := hk
  have e2 := cosupp_bmFiniteSum_rawLogMarked (𝔪.geoTransform C π) hN' h𝔞'hol hk'
  obtain ⟨-, h2, -, -, -, h3⟩ := geoTransform_bmFiniteSum_rawLogMarked 𝔪 h𝔪 hC hπ hk
  refine ⟨Subset.antisymm ?_ ?_, e2⟩
  · have hsub := MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h2
      (bmCommonMark (rawLogMarked 𝔪) (k + 1))
    have hQ' := cosupp_bmFiniteSum (fun i => (rawLogMarked 𝔪 i).geoTransform C π) (k + 1) hN'.2
      (fun _ _ => rfl) (rawLogMarked_d_pos 𝔪 hk) (fun i _ x g hg => hg.1)
    intro x hx
    have hx' : x ∈ (bmFiniteSum (fun i => (rawLogMarked 𝔪 i).geoTransform C π) (k + 1)).cosupp := hsub hx
    rw [hQ'] at hx'
    exact hx'.2 0 (Nat.succ_pos k)
  · rw [← e2]
    exact MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h3 _

/-- **The same admissible centres** (BM08 Lemma 3.9 with Lemma 3.2(3)): for `k < d`, a centre is admissible for
`𝓒^k(𝔪)` iff it is admissible for `𝔪`. -/
theorem isAdmissibleCentre_bmFiniteSum_rawLogMarked_iff (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) {k : ℕ} (hk : k < 𝔪.d) {D : Set X} :
    (bmFiniteSum (rawLogMarked 𝔪) (k + 1)).IsAdmissibleCentre D ↔ 𝔪.IsAdmissibleCentre D := by
  unfold MarkedIdeals.MarkedIdeal.IsAdmissibleCentre
  rw [cosupp_bmFiniteSum_rawLogMarked 𝔪 hN h𝔞 hk]
  exact Iff.rfl

end Marked

end

end Hironaka.HironakaG8LogFiniteSumTransform
