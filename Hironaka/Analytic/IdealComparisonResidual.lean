import Hironaka.Analytic.MultiplierIdealProductComparison
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Analytic.IdealPowers
import Hironaka.Analytic.IdealProducts
import Hironaka.Analytic.CoherentIdealWeight

set_option autoImplicit false

/-!
# The residual ideal of `lem:ideal-comparison` and `eq:GB-decomposition`

Source: Copy-4, `lem:ideal-comparison`
(`transcendental-nakamaye-copy4-20260911`, `main-Nulllocus.tex:1666`), the
"Consequently" clause:

> Consequently, on any modification of `V` on which `𝔅̄_m`, `𝔅̄_M` and `𝔅` are
> principal, with divisors `G_m`, `G_M` and `G_B`, the divisors
> `G_M - (M/m) G_m` and `F_B := G_B + p G_m - G_M` are effective, and
> `(1/ℓ) G_B = (1/M) G_M + ((C-1)/M)(G_M - (M/m) G_m) + (C/M) F_B`.

Two independent pieces, both proved here.

1. **`F_B` exists and is effective.**  Effectivity of `F_B` is the inclusion
   `𝔅 𝔅̄_m^{\,p} ⊆ 𝔅̄_M`, and in the germ-ideal encoding an inclusion into an
   invertible ideal is the same thing as a factorization with a *coherent*
   cofactor (`InvertibleIdealQuotient.exists_isCoherent_eq_mul`): `F_B` is the
   divisor of that cofactor once the ambient modification makes it principal.
   The inclusion itself is
   `MultiplierIdealProductComparison.multiplierIdeal_mul_le` composed with the
   trace inclusion `𝓘(Mu) ⊆ 𝔅̄_M` of `sec:setup`, which stays a hypothesis: it
   is fixed before this lemma and is not part of its content.
   The companion statement `G_M ≥ (M/m) G_m` is the same division applied to the
   subadditivity inclusion `𝔅̄_M ⊆ 𝔅̄_m^{\,M/m}`, i.e.
   `InvertibleIdealQuotient.exists_isCoherent_eq_mul` verbatim, so it is not
   restated here.

2. **`eq:GB-decomposition`** is an identity of coefficients, verified from
   `M = C ℓ`, `m p = ℓ(C-1)` and `G_B = G_M - p G_m + F_B` alone.  It is stated
   over an arbitrary linearly ordered field-like carrier — concretely `ℝ` — so
   that it applies to divisors, to their weights, and to Bott--Chern classes
   alike, whichever of the three the project ends up able to express.

The stalkwise *algebra* of `eq:ideal-comparison` already exists in
`Hironaka.IdealRestriction` — `imageRestriction_product_power_inclusion`
transports a product-power inclusion through a restriction homomorphism, and
`ideal_comparison_trans` composes the two inclusions of `eq:ideal-comparison`
for `Ideal R`.  That layer is about ideals of a commutative ring and takes both
inclusions as hypotheses; it is deliberately not what is done here.  This module
works in the sheaf encoding `GermIdeal n M`, where the first inclusion is a
theorem rather than a hypothesis and the cofactor's *coherence* — the reason
`F_B` is a divisor at all — is part of the conclusion.

Coherence of `𝓘(ℓ h_C)` is a hypothesis: it is Nadel's theorem, and in Copy-4 it
is part of the analytic-singularity type `(ℓ^{-1}, 𝔅)` that
`Xia, Theorem 1.6.2` supplies.  Nothing here needs compactness, a Kähler form,
or any input from the modification side, and nothing here is new mathematics: it
is the bookkeeping that makes the two halves of the `Consequently` clause
available to Step 1.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.IdealComparisonResidual

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  MultiplierIdealProductComparison

variable {n : ℕ} {Mfd : Type*} [TopologicalSpace Mfd]
  [ChartedSpace (ComplexModel n) Mfd] [IsComplexManifold n Mfd]

/-- **The residual ideal `F_B` of `lem:ideal-comparison`.**  With
`𝔅 = 𝓘(ℓ h_C)`, `M = ℓ + r`, `r = ℓ(C-1) = m p` and `𝔟 = 𝔅̄_m^{\,p}`, the
inclusion `𝔅 𝔟 ⊆ 𝔅̄_M` holds, hence `𝔅 𝔟 = 𝔅̄_M 𝔠` with `𝔠` coherent.  `𝔠` is
the ideal of `F_B`; its effectivity is the content of the factorization. -/
theorem exists_isCoherent_residual
    {u hC phim : Mfd → EReal} {ell r : ℝ} (hell : 0 < ell) (hr : 0 ≤ r)
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hhC : ManifoldQuasiPlurisubharmonic (n := n) hC)
    (hphim : ManifoldQuasiPlurisubharmonic (n := n) phim)
    {𝔟 𝔅M : GermIdeal n Mfd}
    (hBcoh : (multiplierIdeal (n := n) ell hC).IsCoherent)
    (h𝔟coh : 𝔟.IsCoherent) (hMinv : 𝔅M.IsInvertible)
    (hchain : ∀ x : Mfd, ChartChainAt (n := n) u hC phim ell r x)
    (hbnd : ∀ (x : Mfd) (b : Mfd → ℂ), 𝔟.mem x b → ChartBoundedAt (n := n) phim r x b)
    (htrace : (multiplierIdeal (n := n) (ell + r) u).Le 𝔅M) :
    ∃ 𝔠 : GermIdeal n Mfd, 𝔠.IsCoherent ∧
      (multiplierIdeal (n := n) ell hC).mul 𝔟 = 𝔅M.mul 𝔠 :=
  InvertibleIdealQuotient.exists_isCoherent_eq_mul
    (IdealWeightPowers.isCoherent_mul hBcoh h𝔟coh) hMinv
    (fun x g hg =>
      htrace x g (multiplierIdeal_mul_le hell hr hu hhC hphim 𝔟 hchain hbnd x g hg))

omit [IsComplexManifold n Mfd] in
/-- Rescaling the coefficient of an analytic singularity type: `ψ` of type
`(c, 𝔞)` gives `d ψ` of type `(d c, 𝔞)`.  Needed because
`CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent`
produces a weight at coefficient `1`, while the product comparison requires all
weights at one common coefficient. -/
theorem hasAnalyticSingularitiesOfType_smul {𝔞 : GermIdeal n Mfd} {psi : Mfd → EReal}
    {c d : ℚ} (hd : 0 < d)
    (hpsi : HasAnalyticSingularitiesOfType (n := n) psi c 𝔞) :
    HasAnalyticSingularitiesOfType (n := n) (fun y => ((d : ℝ) : EReal) * psi y)
      (d * c) 𝔞 := by
  obtain ⟨hc, hcoh, hloc⟩ := hpsi
  have hdR : (0 : ℝ) ≤ (d : ℝ) := le_of_lt (by exact_mod_cast hd)
  refine ⟨mul_pos hd hc, hcoh, fun x => ?_⟩
  obtain ⟨U, hU, hxU, N, g, hg, hgen, R, C, hRC, heq⟩ := hloc x
  refine ⟨U, hU, hxU, N, g, hg, hgen, fun y => (d : ℝ) * R y, (d : ℝ) * C, ?_, ?_⟩
  · intro y hy
    rw [abs_mul, abs_of_nonneg hdR]
    exact mul_le_mul_of_nonneg_left (hRC y hy) hdR
  · intro y hy
    show ((d : ℝ) : EReal) * psi y = _
    rw [heq y hy,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hdR)
        (EReal.coe_ne_top _), ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul,
      Rat.cast_mul]

/-- **The `Consequently` clause wired to the weights.**  With `ψ_𝔅`, `ψ_𝔟`, `ψ_{𝔅̄_M}`
weights of the three ideals at one coefficient, the factorization
`𝔅 𝔟 = 𝔅̄_M 𝔠` produced above upgrades to
`ψ_𝔅 + ψ_𝔟 = ψ_{𝔅̄_M} + ψ_𝔠 + O(1)` on a compact manifold — which is Copy-4's
`G_B + p G_m = G_M + F_B`, i.e. exactly the hypothesis `hGB` of
`gb_decomposition` below, read at the weight level.  So the two halves of the
clause are not independent: this is what joins them.

`ψ_𝔠` is constructed, not assumed: `CoherentIdealWeight` gives it at coefficient
`1` and `hasAnalyticSingularitiesOfType_smul` moves it to the common one. -/
theorem exists_isCoherent_residual_weight [CompactSpace Mfd]
    {u hC phim : Mfd → EReal} {ell r : ℝ} (hell : 0 < ell) (hr : 0 ≤ r)
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hhC : ManifoldQuasiPlurisubharmonic (n := n) hC)
    (hphim : ManifoldQuasiPlurisubharmonic (n := n) phim)
    {𝔟 𝔅M : GermIdeal n Mfd} {cq : ℚ} {psiB psib psiM : Mfd → EReal}
    (hpsiB : HasAnalyticSingularitiesOfType (n := n) psiB cq
      (multiplierIdeal (n := n) ell hC))
    (hpsib : HasAnalyticSingularitiesOfType (n := n) psib cq 𝔟)
    (hpsiM : HasAnalyticSingularitiesOfType (n := n) psiM cq 𝔅M)
    (hMinv : 𝔅M.IsInvertible)
    (hchain : ∀ x : Mfd, ChartChainAt (n := n) u hC phim ell r x)
    (hbnd : ∀ (x : Mfd) (b : Mfd → ℂ), 𝔟.mem x b → ChartBoundedAt (n := n) phim r x b)
    (htrace : (multiplierIdeal (n := n) (ell + r) u).Le 𝔅M) :
    ∃ (𝔠 : GermIdeal n Mfd) (psiC : Mfd → EReal),
      𝔠.IsCoherent ∧
      (multiplierIdeal (n := n) ell hC).mul 𝔟 = 𝔅M.mul 𝔠 ∧
      HasAnalyticSingularitiesOfType (n := n) psiC cq 𝔠 ∧
      SameSingularityTypeOn (fun y => psiB y + psib y)
        (fun y => psiM y + psiC y) univ := by
  obtain ⟨𝔠, h𝔠, heq⟩ := exists_isCoherent_residual hell hr hu hhC hphim hpsiB.2.1
    hpsib.2.1 hMinv hchain hbnd htrace
  obtain ⟨psi0, hpsi0⟩ :=
    CoherentIdealWeight.exists_hasAnalyticSingularitiesOfType_of_isCoherent h𝔠
  have hpsiC : HasAnalyticSingularitiesOfType (n := n)
      (fun y => ((cq : ℝ) : EReal) * psi0 y) cq 𝔠 := by
    simpa using hasAnalyticSingularitiesOfType_smul hpsiB.1 hpsi0
  refine ⟨𝔠, fun y => ((cq : ℝ) : EReal) * psi0 y, h𝔠, heq, hpsiC, ?_⟩
  have hprod := IdealWeightPowers.hasAnalyticSingularitiesOfType_mul hpsiB hpsib
  have hprod' := IdealWeightPowers.hasAnalyticSingularitiesOfType_mul hpsiM hpsiC
  rw [← heq] at hprod'
  exact IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hprod hprod'

/-- **`eq:GB-decomposition`** (Copy-4 `lem:ideal-comparison`).  With `M = C ℓ`,
`m p = ℓ(C-1)` and `G_B = G_M - p G_m + F_B`, the coefficient of `G_M` on the
right is `(1 + (C-1) - C)/M = 0`, that of `G_m` is `-(C-1)/m + Cp/M = 0`, and
that of `F_B` is `C/M = 1/ℓ`.  Only these three identities are used, so the
statement is the scalar one and transports to any `ℝ`-linear reading of the
divisors. -/
theorem gb_decomposition {C ell m p Mlvl gB gM gm fB : ℝ}
    (hell : 0 < ell) (hm : 0 < m) (hC : 0 < C)
    (hMlvl : Mlvl = C * ell) (hp : m * p = ell * (C - 1))
    (hGB : gB = gM - p * gm + fB) :
    ell⁻¹ * gB =
      Mlvl⁻¹ * gM + ((C - 1) / Mlvl) * (gM - (Mlvl / m) * gm) + (C / Mlvl) * fB := by
  subst hMlvl hGB
  have hp' : p = ell * (C - 1) / m := by
    field_simp at hp ⊢
    linarith [hp]
  subst hp'
  field_simp
  ring

end

end Hironaka.IdealComparisonResidual
