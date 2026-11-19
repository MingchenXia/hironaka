import Hironaka.Analytic.Unibranch.HironakaG10NfFibreGerm
import Hironaka.Resolution.HironakaG10JointStrictTorsion

/-!
# H3 (3): the fibre identity `B/𝔪_{X'}B ≅ 𝒪_X/𝔪_Y` on a source blowup chart (generic form)

Lane G10FI, run 0081 (H3 item (3) of `G10N5/hfib-H3-route.md`).  Hironaka 1975, proof of Lemma 4.4.5, printed p. 538:
the fibre of `X ×_Y Bl_B Y` over a point `x'` of the blowup is the fibre of `X` over `π x'`.  In charts: a source chart
`S` (coordinates `w`) of the fibre product, with blow-down `π : S → P × ℂ^r` onto the ambient of the graph
`Γ = {(u, G (f u)) : u ∈ S_X}` of `X`, the "raw" base chart `ρ = κ ∘ π : S → U` of `Γ`'s coordinate image `W_Γ ⊇ κ Γ`,
and the map `L : S → T` to the target chart (strict transform `V` of the graph of `Y`).  The joint ideal at `w` is
`raw + tgt = ρ^* I(W_Γ) + L^* I(V)`.  If `w = ι u₁` lies on a **normal slice** `ι : P → S` (`π (ι u) = (u, l₁)`,
`L (ι u) = ι_T (f u)`) with `(u₁, l₁) ∈ Γ` and `L w ∈ V`, then for every germ `h` at `π w`:

  `π^♯ h ∈ raw + tgt + L^♯ 𝔪_{L w}  ⟹  h ∈ I(Γ) + (f × id)^♯ 𝔪`   (`fibre_identity`).

Proof: restrict to the slice (`ι^♯`): the joint ideal and `L^♯ 𝔪` go to `I(S_X) + f^♯ 𝔪` (Hadamard in `λ` for the raw
part, `ι_T^♯ 𝔪 ⊆ 𝔪` for the target part), so `h(·, l₁) ∈ I(S_X) + f^♯ 𝔪`; pull back by `pr₁` and use Hadamard in `λ`
once more: `h − h(·, l₁) ∈ (λ − l₁) ⊆ (f × id)^♯ 𝔪`.

No named input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentity

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaFiniteSectionProductGraph Hironaka.Analytic.Unibranch.HironakaG10NfFibreGerm

variable {N n m mT NU r : ℕ}
  {S : Type} [TopologicalSpace S] [ChartedSpace (ComplexModel N) S] [IsComplexManifold N S]
  {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
  {T : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel mT) T] [IsComplexManifold mT T]
  {U : Type} [TopologicalSpace U] [ChartedSpace (ComplexModel NU) U] [IsComplexManifold NU U]

/-- The maximal ideal of the stalk of a complex manifold. -/
abbrev mx (M : Type) {k : ℕ} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    (y : M) := IsLocalRing.maximalIdeal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel k) M).presheaf.stalk y)

/-- The stalk map of a holomorphic map. -/
abbrev sm {M M' : Type} {k k' : ℕ} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    [TopologicalSpace M'] [ChartedSpace (ComplexModel k') M'] [IsComplexManifold k' M']
    {F : M → M'} (hF : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k') ∞ F) (y : M) :=
  ((ChartedSpace.locallyRingedSpaceMap F hF).stalkMap y).hom

theorem sm_germ {M M' : Type} {k k' : ℕ} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
    [IsComplexManifold k M] [TopologicalSpace M'] [ChartedSpace (ComplexModel k') M'] [IsComplexManifold k' M']
    {F : M → M'} (hF : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k') ∞ F) (p : M) (f : M' → ℂ)
    (hf : HolomorphicAt k' f (F p)) (hf' : HolomorphicAt k (f ∘ F) p) :
    sm hF p (actualOriginalFunctionGerm (F p) f hf) = actualOriginalFunctionGerm p (f ∘ F) hf' :=
  stalkMap_germ hF p f hf

/-- `k ∘ F` vanishing at `y` has its germ in `F^♯ 𝔪`. -/
theorem germ_comp_mem_map {Z : Type} {k' : ℕ} [TopologicalSpace Z] [ChartedSpace (ComplexModel k') Z]
    [IsComplexManifold k' Z] {F : P → Z} (hF : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel k') ∞ F)
    (y : P) (k : Z → ℂ) (hk : HolomorphicAt k' k (F y)) (h0 : k (F y) = 0)
    (hk' : HolomorphicAt n (k ∘ F) y) :
    actualOriginalFunctionGerm y (k ∘ F) hk' ∈ Ideal.map (sm hF y) (mx Z (F y)) := by
  have he := stalkMap_germ hF y k hk
  rw [germ_congr y hk' (hk.comp_contMDiff (Eventually.of_forall fun _ => hF.contMDiffAt))
    (Eventually.of_forall fun _ => rfl), ← he]
  exact Ideal.mem_map_of_mem _ ((germ_mem_maximalIdeal_iff (F y) hk).mpr h0)

/-- Restricting a whole pulled-back vanishing ideal along `ι` lands in `I` as soon as every pulled-back member
function does. -/
theorem map_pullback_vanishing_le {Z : Type} {k' : ℕ} [TopologicalSpace Z] [ChartedSpace (ComplexModel k') Z]
    [IsComplexManifold k' Z] {F : S → Z} (hF : ContMDiff 𝓘(ℂ,ComplexModel N) 𝓘(ℂ,ComplexModel k') ∞ F) (V : Set Z)
    {ι : P → S} (hι : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel N) ∞ ι) (u₁ : P)
    (I : Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) P).presheaf.stalk u₁))
    (hgen : ∀ k, (vanishingIdeal (n := k') V).mem (F (ι u₁)) k → ∀ hk' : HolomorphicAt n (k ∘ F ∘ ι) u₁,
      actualOriginalFunctionGerm u₁ (k ∘ F ∘ ι) hk' ∈ I) :
    Ideal.map (sm hι u₁) (actualWholeSheafStalkIdeal (GermIdeal.pullback (m := N) F (vanishingIdeal (n := k') V))
      (ι u₁)) ≤ I := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨g, hg, ⟨-, K, s, a, hs, ha, hsum⟩, rfl⟩
  choose k hk hsk using hs
  change sm hι u₁ (actualOriginalFunctionGerm (ι u₁) g hg) ∈ I
  rw [stalkMap_germ hι u₁ g hg]
  have hsI : ∀ i, HolomorphicAt n (s i ∘ ι) u₁ := fun i => by
    rw [hsk i]
    exact (hk i).1.comp_contMDiff (f := F ∘ ι) (Eventually.of_forall fun _ => (hF.comp hι).contMDiffAt)
  have haI : ∀ i, HolomorphicAt n (a i ∘ ι) u₁ := fun i =>
    (ha i).comp_contMDiff (Eventually.of_forall fun _ => hι.contMDiffAt)
  have hcont : Tendsto ι (𝓝 u₁) (𝓝 (ι u₁)) := hι.continuous.tendsto u₁
  have hsum' := HolomorphicAt.sum (Finset.univ : Finset (Fin K)) (fun i _ => (haI i).mul (hsI i))
  rw [germ_congr (f := g ∘ ι) u₁ _ hsum' (hcont.eventually hsum), germ_sum u₁ Finset.univ _ (fun i => (haI i).mul (hsI i))]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [germ_mul u₁ (haI i) (hsI i)]
  refine Ideal.mul_mem_left _ _ ?_
  have hkI : HolomorphicAt n (k i ∘ F ∘ ι) u₁ :=
    (hk i).1.comp_contMDiff (f := F ∘ ι) (Eventually.of_forall fun _ => (hF.comp hι).contMDiffAt)
  rw [germ_congr u₁ (hsI i) hkI (Eventually.of_forall fun u => by rw [hsk i]; rfl)]
  exact hgen (k i) (hk i) hkI

theorem germ_sub' {M : Type} {k : ℕ} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    (y : M) {F G : M → ℂ} (hF : HolomorphicAt k F y) (hG : HolomorphicAt k G y)
    (hFG : HolomorphicAt k (fun p => F p - G p) y) :
    actualOriginalFunctionGerm y (fun p => F p - G p) hFG =
      actualOriginalFunctionGerm y F hF - actualOriginalFunctionGerm y G hG := by
  apply (actualStalkChartEquiv (n := k) y).injective
  rw [map_sub, actualOriginalFunctionGerm_chart, actualOriginalFunctionGerm_chart,
    actualOriginalFunctionGerm_chart]
  rfl

/-- Point transport of stalks acts on germs by doing nothing. -/
theorem transport_germ {M : Type} {k : ℕ} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
    [IsComplexManifold k M] {y y' : M} (e : y = y') (F : M → ℂ) (hF : HolomorphicAt k F y) :
    (eqToHom (congrArg (fun z => (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel k) M).presheaf.stalk z) e)).hom
        (actualOriginalFunctionGerm y F hF) = actualOriginalFunctionGerm y' F (e ▸ hF) := by
  subst e
  rfl

variable {f : P → Q} (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)

/-- The fibre ideal `I(S_X) + f^♯ 𝔪_{f u}` at `u`. -/
abbrev fibreJ (SX : Set P) (u : P) :
    Ideal ((ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) P).presheaf.stalk u) :=
  actualWholeSheafStalkIdeal (vanishingIdeal (n := n) SX) u ⊔ Ideal.map (sm hf u) (mx Q (f u))

/-- **The target part on the slice**: `k ∘ L ∘ ι = (k ∘ ι_T) ∘ f` with `k` vanishing at `L (ι u₁)`. -/
theorem tgt_gen_mem {L : S → T} {ι : P → S} {ιT : Q → T}
    (hιT : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel mT) ∞ ιT) (hLι : ∀ u, L (ι u) = ιT (f u)) (u₁ : P)
    (k : T → ℂ) (hk : HolomorphicAt mT k (L (ι u₁))) (h0 : k (L (ι u₁)) = 0)
    (hk' : HolomorphicAt n (k ∘ L ∘ ι) u₁) :
    actualOriginalFunctionGerm u₁ (k ∘ L ∘ ι) hk' ∈ Ideal.map (sm hf u₁) (mx Q (f u₁)) := by
  have hk2 : HolomorphicAt m (k ∘ ιT) (f u₁) :=
    (show HolomorphicAt mT k (ιT (f u₁)) from hLι u₁ ▸ hk).comp_contMDiff
      (Eventually.of_forall fun _ => hιT.contMDiffAt)
  have hk3 : HolomorphicAt n ((k ∘ ιT) ∘ f) u₁ :=
    hk2.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)
  rw [germ_congr u₁ hk' hk3 (Eventually.of_forall fun u => by
    change k (L (ι u)) = k (ιT (f u)); rw [hLι u])]
  exact germ_comp_mem_map hf u₁ (k ∘ ιT) hk2 (by change k (ιT (f u₁)) = 0; rw [← hLι u₁]; exact h0) hk3

/-- **The raw part on the slice** (Hadamard in `λ`): `k ∘ ρ ∘ ι = (k ∘ κ)(·, l₁)` lies in `I(S_X) + f^♯ 𝔪`. -/
theorem raw_gen_mem {G : Q → ComplexModel r} (hG : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel r) ∞ G)
    (SX : Set P) {π : S → P × ComplexModel r} {ρ : S → U} {κ : P × ComplexModel r → U}
    (hκ : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel NU) ∞ κ) (hκρ : ∀ s, κ (π s) = ρ s)
    (Wg : Set U) (hκΓ : MapsTo κ (productGraph SX (G ∘ f)) Wg)
    {ι : P → S} (l₁ : ComplexModel r) (hπι : ∀ u, π (ι u) = (u, l₁))
    (u₁ : P) (hl₁ : l₁ = G (f u₁))
    (k : U → ℂ) (hk : (vanishingIdeal (n := NU) Wg).mem (ρ (ι u₁)) k) (hk' : HolomorphicAt n (k ∘ ρ ∘ ι) u₁) :
    actualOriginalFunctionGerm u₁ (k ∘ ρ ∘ ι) hk' ∈ fibreJ hf SX u₁ := by
  have hρι : ρ (ι u₁) = κ (u₁, l₁) := by rw [← hκρ, hπι]
  have hkp : HolomorphicAt NU k (κ (u₁, l₁)) := hρι ▸ hk.1
  have hK : HolomorphicAt (n+r) (k ∘ κ) (u₁, l₁) :=
    hkp.comp_contMDiff (Eventually.of_forall fun _ => hκ.contMDiffAt)
  obtain ⟨H, hH, hKH⟩ := exists_hadamard_normal (k ∘ κ) (u₁, l₁) hK
  have hgX : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+r)) ∞
      (fun u : P => ((u, G (f u)) : P × ComplexModel r)) :=
    ProductComplexManifold.contMDiff_prodMk contMDiff_id (hG.comp hf)
  have hgXu : ((u₁, G (f u₁)) : P × ComplexModel r) = (u₁, l₁) := by rw [hl₁]
  have hT : Tendsto (fun u : P => ((u, G (f u)) : P × ComplexModel r)) (𝓝 u₁) (𝓝 (u₁, l₁)) := by
    have := hgX.continuous.tendsto u₁
    rwa [hgXu] at this
  -- the three pieces
  have hA : HolomorphicAt n (fun u => (k ∘ κ) ((u, G (f u)) : P × ComplexModel r)) u₁ :=
    (show HolomorphicAt (n+r) (k ∘ κ) ((u₁, G (f u₁)) : P × ComplexModel r) from hgXu ▸ hK).comp_contMDiff
      (f := fun u : P => ((u, G (f u)) : P × ComplexModel r)) (Eventually.of_forall fun _ => hgX.contMDiffAt)
  have hHi : ∀ i, HolomorphicAt n (fun u => H i ((u, G (f u)) : P × ComplexModel r)) u₁ := fun i =>
    (show HolomorphicAt (n+r) (H i) ((u₁, G (f u₁)) : P × ComplexModel r) from hgXu ▸ hH i).comp_contMDiff
      (f := fun u : P => ((u, G (f u)) : P × ComplexModel r)) (Eventually.of_forall fun _ => hgX.contMDiffAt)
  have hEi : ∀ i : Fin r, HolomorphicAt m (fun z => G z i - l₁ i) (f u₁) := fun i =>
    Eventually.of_forall fun _ =>
      ((((EuclideanSpace.proj i : ComplexModel r →L[ℂ] ℂ).contMDiff.comp hG).sub contMDiff_const).contMDiffAt
        ).mdifferentiableAt (by simp)
  have hEi' : ∀ i : Fin r, HolomorphicAt n ((fun z => G z i - l₁ i) ∘ f) u₁ := fun i =>
    (hEi i).comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)
  have hsumH := HolomorphicAt.sum (Finset.univ : Finset (Fin r)) (fun i _ => (hHi i).mul (hEi' i))
  have hdiff : HolomorphicAt n (fun u => (k ∘ κ) ((u, G (f u)) : P × ComplexModel r) -
      ∑ i, H i ((u, G (f u)) : P × ComplexModel r) * ((fun z => G z i - l₁ i) ∘ f) u) u₁ :=
    (hA.and hsumH).mono fun _ h => h.1.sub h.2
  rw [germ_congr u₁ hk' hdiff (by
      filter_upwards [hT.eventually hKH] with u hu
      change k (ρ (ι u)) = _
      rw [← hκρ, hπι]
      simp only [Function.comp_apply] at hu ⊢
      rw [← hu]
      ring),
    germ_sub' u₁ hA hsumH, germ_sum u₁ Finset.univ _ (fun i => (hHi i).mul (hEi' i))]
  refine sub_mem (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right (Ideal.sum_mem _ fun i _ => ?_))
  · apply germ_mem_whole
    refine ⟨hA, ?_⟩
    have hc : Tendsto (fun u => κ ((u, G (f u)) : P × ComplexModel r)) (𝓝 u₁) (𝓝 (ρ (ι u₁))) := by
      rw [hρι]
      exact hκ.continuous.continuousAt.tendsto.comp hT
    filter_upwards [hc.eventually hk.2] with u hu huS
    exact hu (hκΓ ⟨huS, rfl⟩)
  · rw [germ_mul u₁ (hHi i) (hEi' i)]
    exact Ideal.mul_mem_left _ _ (germ_comp_mem_map hf u₁ _ (hEi i) (by rw [hl₁, sub_self]) _)

/-- The pull-back to `P × ℂ^r` of germs at a point equal to `q₀.1`. -/
theorem theta_germ {r' : ℕ} (q₀ : P × ComplexModel r')
    (hpr : ContMDiff 𝓘(ℂ,ComplexModel (n+r')) 𝓘(ℂ,ComplexModel n) ∞ (Prod.fst : P × ComplexModel r' → P))
    {u₁ : P} (e : u₁ = (ChartedSpace.locallyRingedSpaceMap (Prod.fst : P × ComplexModel r' → P) hpr).base q₀)
    (F : P → ℂ) (hF : HolomorphicAt n F u₁) (hF' : HolomorphicAt (n+r') (F ∘ Prod.fst) q₀) :
    sm hpr q₀ ((eqToHom (congrArg (fun z => (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) P).presheaf.stalk z)
      e)).hom (actualOriginalFunctionGerm u₁ F hF)) = actualOriginalFunctionGerm q₀ (F ∘ Prod.fst) hF' := by
  rw [transport_germ e F hF]
  exact sm_germ hpr q₀ F _ hF'

include hf in
/-- **The fibre identity on a source chart** (generic form): along a normal slice through `w = ι u₁`,
`π^♯ h ∈ raw + tgt + L^♯ 𝔪 ⟹ h ∈ I(Γ) + (f × id)^♯ 𝔪`. -/
theorem fibre_identity {G : Q → ComplexModel r} (hG : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel r) ∞ G)
    (SX : Set P) {π : S → P × ComplexModel r} (hπ : ContMDiff 𝓘(ℂ,ComplexModel N) 𝓘(ℂ,ComplexModel (n+r)) ∞ π)
    {ρ : S → U} (hρ : ContMDiff 𝓘(ℂ,ComplexModel N) 𝓘(ℂ,ComplexModel NU) ∞ ρ) {κ : P × ComplexModel r → U}
    (hκ : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel NU) ∞ κ) (hκρ : ∀ s, κ (π s) = ρ s)
    (Wg : Set U) (hκΓ : MapsTo κ (productGraph SX (G ∘ f)) Wg)
    {L : S → T} (hL : ContMDiff 𝓘(ℂ,ComplexModel N) 𝓘(ℂ,ComplexModel mT) ∞ L) (V : Set T)
    {ι : P → S} (hι : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel N) ∞ ι)
    {ιT : Q → T} (hιT : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel mT) ∞ ιT)
    (l₁ : ComplexModel r) (hπι : ∀ u, π (ι u) = (u, l₁)) (hLι : ∀ u, L (ι u) = ιT (f u))
    (hfr : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (m+r)) ∞
      (Prod.map f id : P × ComplexModel r → Q × ComplexModel r))
    (u₁ : P) (hl₁ : l₁ = G (f u₁)) (hLV : L (ι u₁) ∈ V)
    (h : (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel (n+r)) (P × ComplexModel r)).presheaf.stalk (π (ι u₁)))
    (hh : sm hπ (ι u₁) h ∈
      (actualWholeSheafStalkIdeal (GermIdeal.pullback (m := N) ρ (vanishingIdeal (n := NU) Wg)) (ι u₁) ⊔
        actualWholeSheafStalkIdeal (GermIdeal.pullback (m := N) L (vanishingIdeal (n := mT) V)) (ι u₁)) ⊔
        Ideal.map (sm hL (ι u₁)) (mx T (L (ι u₁)))) :
    h ∈ actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) (productGraph SX (G ∘ f))) (π (ι u₁)) ⊔
      Ideal.map (sm hfr (π (ι u₁))) (mx (Q × ComplexModel r) (Prod.map f id (π (ι u₁)))) := by
  -- the slice image lies in `I(S_X) + f^♯ 𝔪`
  have hle : Ideal.map (sm hι u₁)
      ((actualWholeSheafStalkIdeal (GermIdeal.pullback (m := N) ρ (vanishingIdeal (n := NU) Wg)) (ι u₁) ⊔
        actualWholeSheafStalkIdeal (GermIdeal.pullback (m := N) L (vanishingIdeal (n := mT) V)) (ι u₁)) ⊔
        Ideal.map (sm hL (ι u₁)) (mx T (L (ι u₁)))) ≤ fibreJ hf SX u₁ := by
    apply Ideal.map_le_iff_le_comap.mpr
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Ideal.map_le_iff_le_comap.mp (map_pullback_vanishing_le hρ Wg hι u₁ _
        (fun k hk hk' => raw_gen_mem hf hG SX hκ hκρ Wg hκΓ l₁ hπι u₁ hl₁ k hk hk'))
    · exact Ideal.map_le_iff_le_comap.mp (map_pullback_vanishing_le hL V hι u₁ _
        (fun k hk hk' => Ideal.mem_sup_right (tgt_gen_mem hf hιT hLι u₁ k hk.1 (hk.2.self_of_nhds hLV) hk')))
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      obtain ⟨k, hk, rfl⟩ := exists_germ_eq (L (ι u₁)) x
      have h0 := (germ_mem_maximalIdeal_iff (L (ι u₁)) hk).mp hx
      have hkL : HolomorphicAt N (k ∘ L) (ι u₁) :=
        hk.comp_contMDiff (Eventually.of_forall fun _ => hL.contMDiffAt)
      have hkLι : HolomorphicAt n ((k ∘ L) ∘ ι) u₁ :=
        hkL.comp_contMDiff (Eventually.of_forall fun _ => hι.contMDiffAt)
      change sm hι u₁ (sm hL (ι u₁) (actualOriginalFunctionGerm (L (ι u₁)) k hk)) ∈ fibreJ hf SX u₁
      rw [sm_germ hL (ι u₁) k hk hkL, sm_germ hι u₁ (k ∘ L) hkL hkLι]
      exact Ideal.mem_sup_right (tgt_gen_mem hf hιT hLι u₁ k hk h0 _)
  have hJ := hle (Ideal.mem_map_of_mem _ hh)
  obtain ⟨φ, hφ, rfl⟩ := exists_germ_eq (π (ι u₁)) h
  have hφπ : HolomorphicAt N (φ ∘ π) (ι u₁) := hφ.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiffAt)
  have hφπι : HolomorphicAt n ((φ ∘ π) ∘ ι) u₁ :=
    hφπ.comp_contMDiff (Eventually.of_forall fun _ => hι.contMDiffAt)
  replace hJ : actualOriginalFunctionGerm u₁ ((φ ∘ π) ∘ ι) hφπι ∈ fibreJ hf SX u₁ := by
    rw [← sm_germ hι u₁ (φ ∘ π) hφπ hφπι, ← sm_germ hπ (ι u₁) φ hφ hφπ]
    exact hJ
  -- pull back along `pr₁`
  have e : u₁ = (π (ι u₁)).1 := by rw [hπι]
  have hpr : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ (Prod.fst : P × ComplexModel r → P) :=
    ProductComplexManifold.contMDiff_fst
  set q₀ := π (ι u₁) with hq₀
  have hq₂ : q₀.2 = l₁ := by rw [hq₀, hπι]
  have e' : u₁ = (ChartedSpace.locallyRingedSpaceMap (Prod.fst : P × ComplexModel r → P) hpr).base q₀ := e
  let Θ := (sm hpr q₀).comp (eqToHom (congrArg
    (fun z => (ChartedSpace.locallyRingedSpace 𝓘(ℂ,ComplexModel n) P).presheaf.stalk z) e')).hom
  have hΘ : ∀ (F : P → ℂ) (hF : HolomorphicAt n F u₁) (hF' : HolomorphicAt (n+r) (F ∘ Prod.fst) q₀),
      Θ (actualOriginalFunctionGerm u₁ F hF) = actualOriginalFunctionGerm q₀ (F ∘ Prod.fst) hF' :=
    fun F hF hF' => theta_germ q₀ hpr e' F hF hF'
  have hTarget : Ideal.map Θ (fibreJ hf SX u₁) ≤
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n+r) (productGraph SX (G ∘ f))) q₀ ⊔
        Ideal.map (sm hfr q₀) (mx (Q × ComplexModel r) (Prod.map f id q₀)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    refine sup_le ?_ ?_
    · apply Ideal.span_le.mpr
      rintro _ ⟨a, ha, hmem, rfl⟩
      have ha' : HolomorphicAt (n+r) (a ∘ Prod.fst) q₀ :=
        (show HolomorphicAt n a q₀.1 from e ▸ ha).comp_contMDiff (Eventually.of_forall fun _ => hpr.contMDiffAt)
      apply Ideal.mem_comap.mpr
      rw [hΘ a ha ha']
      apply Ideal.mem_sup_left
      apply germ_mem_whole
      refine ⟨ha', ?_⟩
      have hc : Tendsto (Prod.fst : P × ComplexModel r → P) (𝓝 q₀) (𝓝 u₁) := by
        rw [e]; exact continuous_fst.tendsto q₀
      filter_upwards [hc.eventually hmem.2] with q hq hqΓ
      exact hq hqΓ.1
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      obtain ⟨k, hk, rfl⟩ := exists_germ_eq (f u₁) x
      have h0 := (germ_mem_maximalIdeal_iff (f u₁) hk).mp hx
      have hkf : HolomorphicAt n (k ∘ f) u₁ := hk.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)
      have hkq : HolomorphicAt m k (Prod.map f id q₀).1 := by
        change HolomorphicAt m k (f q₀.1); rw [← e]; exact hk
      have hk2 : HolomorphicAt (m+r) (k ∘ Prod.fst) (Prod.map f id q₀) :=
        hkq.comp_contMDiff (Eventually.of_forall fun _ => ProductComplexManifold.contMDiff_fst.contMDiffAt)
      have hk3 : HolomorphicAt (n+r) ((k ∘ f) ∘ Prod.fst) q₀ :=
        (show HolomorphicAt n (k ∘ f) q₀.1 from e ▸ hkf).comp_contMDiff
          (Eventually.of_forall fun _ => hpr.contMDiffAt)
      apply Ideal.mem_comap.mpr
      apply Ideal.mem_comap.mpr
      have e1 : Θ (sm hf u₁ (actualOriginalFunctionGerm (f u₁) k hk)) =
          actualOriginalFunctionGerm q₀ ((k ∘ f) ∘ Prod.fst) hk3 := by
        rw [sm_germ hf u₁ k hk hkf]
        exact hΘ (k ∘ f) hkf hk3
      have hm : actualOriginalFunctionGerm q₀ ((k ∘ f) ∘ Prod.fst) hk3 ∈
          Ideal.map (sm hfr q₀) (mx (Q × ComplexModel r) (Prod.map f id q₀)) :=
        germ_comp_mem_map hfr q₀ (k ∘ Prod.fst) hk2 (by change k (f q₀.1) = 0; rw [← e]; exact h0) hk3
      refine Ideal.mem_sup_right ?_
      exact (congrArg (· ∈ Ideal.map (sm hfr q₀) (mx (Q × ComplexModel r) (Prod.map f id q₀))) e1).mpr hm
  have hφ' : HolomorphicAt (n+r) (((φ ∘ π) ∘ ι) ∘ Prod.fst) q₀ :=
    (show HolomorphicAt n ((φ ∘ π) ∘ ι) q₀.1 from e ▸ (hφ.comp_contMDiff (f := π ∘ ι)
      (Eventually.of_forall fun _ => (hπ.comp hι).contMDiffAt))).comp_contMDiff
      (Eventually.of_forall fun _ => hpr.contMDiffAt)
  have h3 := hTarget (Ideal.mem_map_of_mem _ hJ)
  rw [hΘ _ _ hφ'] at h3
  -- Hadamard in `λ` at `q₀`
  obtain ⟨H, hH, hφH⟩ := exists_hadamard_normal φ q₀ hφ
  have hEi : ∀ i : Fin r, HolomorphicAt (m+r) (fun q : Q × ComplexModel r => q.2 i - l₁ i) (Prod.map f id q₀) :=
    fun i => Eventually.of_forall fun _ =>
      ((((EuclideanSpace.proj i : ComplexModel r →L[ℂ] ℂ).contMDiff.comp
        ProductComplexManifold.contMDiff_snd).sub contMDiff_const).contMDiffAt).mdifferentiableAt (by simp)
  have hEi' : ∀ i : Fin r, HolomorphicAt (n+r) ((fun q : Q × ComplexModel r => q.2 i - l₁ i) ∘ Prod.map f id) q₀ :=
    fun i => (hEi i).comp_contMDiff (Eventually.of_forall fun _ => hfr.contMDiffAt)
  have hsum := HolomorphicAt.sum (Finset.univ : Finset (Fin r)) (fun i _ => (hH i).mul (hEi' i))
  have hadd : HolomorphicAt (n+r) (fun q => (((φ ∘ π) ∘ ι) ∘ Prod.fst) q +
      ∑ i, H i q * ((fun q : Q × ComplexModel r => q.2 i - l₁ i) ∘ Prod.map f id) q) q₀ := hφ'.add hsum
  rw [germ_congr q₀ hφ hadd (by
      filter_upwards [hφH] with q hq
      simp only [Function.comp_apply, Prod.map_snd, id, hπι, ← hq₂]
      rw [← hq]
      ring),
    germ_add q₀ hφ' hsum, germ_sum q₀ Finset.univ _ (fun i => (hH i).mul (hEi' i))]
  refine add_mem h3 (Ideal.mem_sup_right (Ideal.sum_mem _ fun i _ => ?_))
  rw [germ_mul q₀ (hH i) (hEi' i)]
  exact Ideal.mul_mem_left _ _ (germ_comp_mem_map hfr q₀ _ (hEi i) (by
    change q₀.2 i - l₁ i = 0; rw [hq₂, sub_self]) _)

end

end Hironaka.Analytic.Unibranch.HironakaG10NfFibreIdentity
