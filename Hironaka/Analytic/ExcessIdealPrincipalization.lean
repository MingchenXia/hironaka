import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.Analytic.PrincipalizationStepOneAssembly

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 Step 1: the excess ideal `𝔣̃_B` and `eq:PF-restriction`

Source: Copy-4, `prop:principalization`, Step 1
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1810-1830`),
and `lem:ideal-comparison` (`:1666-1711`):

> Next, by `lem:ideal-comparison`, on `W₁` the sheaf
> `𝔣_B := (𝔅 𝒪_{W₁}) · 𝒪_{W₁}(G_M - p G_m) ⊆ 𝒪_{W₁}` is a coherent ideal [...] Let
> `𝔣̃_B ⊆ 𝒪_{Y₁}` be the inverse image of `𝔣_B` [...] it is not contained in `𝓘_{W₁}` because
> `𝔣_B ≠ 0`.  Apply `lem:relative-principalization` to `𝔣̃_B` [...] `P^F|_W = F_B`.

## The encoding

`𝔅 ⊆ 𝒪_V` (the QEA ideal `𝓘(ℓφ_K)`) is represented by an ambient coherent ideal `𝔅̃` on `X`
whose restriction to `V` is `𝔅`, and `eq:ideal-comparison` (`𝔅 𝔅̄_m^p ⊆ 𝔅̄_M` on `V`) by the
restricted inclusion `RestrictLe V (𝔅̃ 𝔅_m^p) 𝔅_M`.  On the model `π : Y₁ → X` of stages 1--2
(`PrincipalizationStepOneAssembly.exists_firstTwoStages`), `𝔅_m 𝒪 = 𝔥 := 𝒪(-(H^fix + H'))` and
`𝔅_M 𝒪 = 𝔥^q · 𝔓` with `𝔓 = 𝒪(-(P^mov + P'))`.  Writing `q = r + p` (Copy-4: `r = ℓ/m`),

* `restrictLe_pullback_divided` — `Res_{W₁}(𝔅̃ 𝒪) ⊆ Res_{W₁}(𝔩)` with `𝔩 := 𝔥^r · 𝔓`: the
  comparison pulled back to `W₁` and divided by the invertible `𝔥^p`
  (`RestrictLeCalculus`).  On `W₁` this is `G_B ≥ G_M - p G_m`, i.e. `F_B ≥ 0`;
* `excessIdeal_spec` — **the excess ideal** `𝔣̃_B := (Res_{W₁}(𝔅̃ 𝒪) : 𝔩)`
  (`RestrictedIdealQuotient.colonAlong`) is coherent, not contained in `𝓘_{W₁}`, and
  `Res_{W₁}(𝔅̃ 𝒪) = Res_{W₁}(𝔩 · 𝔣̃_B)`: Copy-4's `𝔅 𝒪_{W₁} = 𝒪(-(G_M - pG_m)) · 𝔣_B`;
* `restrictLe_pullback_excess` — after the third stage `g : Y → Y₁` with
  `𝔣̃_B 𝒪_Y = 𝒪(-(P^F + P^F'))`: `Res_W(𝔅̃ 𝒪_Y) = Res_W((𝔩 𝒪_Y) · 𝒪(-(P^F + P^F')))`, which is
  `eq:PF-restriction` read through `𝔅`: `G_B = (G_M - p G_m) + P^F|_W` on `W`.

The divisor `𝔩` differs from Copy-4's `𝒪(-(G_M - pG_m))` only by the remainders `H'`, `P'`,
which are disjoint from `W₁`; they are kept ambiently, as in `PrincipalizationStepOneAssembly`.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ExcessIdealPrincipalization

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan RestrictedIdealWeight RestrictedIdealQuotient IdealWeightPowers
  GermIdealTotalTransform GermIdealPullbackCalculus RestrictLeCalculus
  PrincipalizationStepOneAssembly StepFourNoComponentContainsW

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-! ### Density on the strict transform -/

/-- **Every open set meeting the strict transform `W` of `V` contains a point of `W` lying over
the complement of two zero loci not containing `V`** (the run-0100 density lemma, applied
twice). -/
theorem exists_mem_strictTransform_notMem_zeroLocus₂ [CompactSpace X] {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) (V : ClosedIrreducibleAnalyticSubvariety n X)
    {𝔞 𝔟 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent)
    (hV𝔞 : ¬ V.carrier ⊆ 𝔞.zeroLocus) (hV𝔟 : ¬ V.carrier ⊆ 𝔟.zeroLocus)
    {O : Set Y} (hO : IsOpen O) (hOW : (O ∩ strictTransform n π V.carrier).Nonempty) :
    ∃ y ∈ O ∩ strictTransform n π V.carrier, π y ∉ 𝔞.zeroLocus ∧ π y ∉ 𝔟.zeroLocus := by
  obtain ⟨p, hpO, hpV, hpexc, hp𝔞⟩ :=
    exists_mem_notMem_exceptionalLocus_notMem_of_inter_strictTransform hπ V
      (isComplexAnalyticSubset_zeroLocus h𝔞) hV𝔞 hO hOW
  have hpW : p ∈ strictTransform n π V.carrier := subset_closure ⟨hpV, hpexc⟩
  have hO' : IsOpen (O ∩ π ⁻¹' (𝔞.zeroLocus)ᶜ) :=
    hO.inter ((isComplexAnalyticSubset_zeroLocus h𝔞).isClosed.isOpen_compl.preimage
      hπ.contMDiff.continuous)
  obtain ⟨q, ⟨hqO, hq𝔞⟩, hqV, hqexc, hq𝔟⟩ :=
    exists_mem_notMem_exceptionalLocus_notMem_of_inter_strictTransform hπ V
      (isComplexAnalyticSubset_zeroLocus h𝔟) hV𝔟 hO' ⟨p, ⟨hpO, hp𝔞⟩, hpW⟩
  exact ⟨q, ⟨hqO, subset_closure ⟨hqV, hqexc⟩⟩, hq𝔞, hq𝔟⟩

/-- The strict transform of a closed set lies over it. -/
theorem mem_of_mem_strictTransform {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (V : ClosedIrreducibleAnalyticSubvariety n X) :
    ∀ y ∈ strictTransform n π V.carrier, π y ∈ V.carrier :=
  fun _ hy => strictTransform_subset_preimage hπ.continuous V.isClosed_carrier hy

/-- The vanishing ideal of a closed connected submanifold is coherent. -/
theorem isCoherent_vanishingIdeal_of_isClosedConnectedSubmanifold {W : Set Y} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) : (vanishingIdeal (n := n) W).IsCoherent :=
  VanishingIdealCoherent.isCoherent_vanishingIdeal ⟨hW.1, fun x hx => ⟨k, hW.2.2 x hx⟩⟩

/-! ### Dividing `eq:ideal-comparison` on `W₁` -/

/-- **`eq:ideal-comparison` on `W₁`, divided by `𝒪(-p G̃_m)`.**  From
`Res_V(𝔅̃ 𝔅_m^p) ⊆ Res_V 𝔅_M` on `X` and the stage-1--2 identities `𝔅_m 𝒪 = 𝔥`,
`𝔅_M 𝒪 = 𝔥^{r+p} 𝔓` (`𝔥`, `𝔓` invertible): `Res_{W₁}(𝔅̃ 𝒪) ⊆ Res_{W₁}(𝔥^r 𝔓)`. -/
theorem restrictLe_pullback_divided [CompactSpace X] {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) (V : ClosedIrreducibleAnalyticSubvariety n X)
    {𝔟m 𝔟M 𝔅 : GermIdeal n X} (h𝔟m : 𝔟m.IsCoherent) (h𝔟M : 𝔟M.IsCoherent)
    (h𝔅 : 𝔅.IsCoherent) {r p : ℕ}
    (hcomp : RestrictLe V.carrier (𝔅.mul (idealPow 𝔟m p)) 𝔟M)
    (hVm : ¬ V.carrier ⊆ 𝔟m.zeroLocus) (hVM : ¬ V.carrier ⊆ 𝔟M.zeroLocus)
    {𝔥 𝔓 : GermIdeal n Y} (h𝔥 : 𝔥.IsInvertible) (h𝔓 : 𝔓.IsInvertible)
    (hbm : GermIdeal.pullback (m := n) π 𝔟m = 𝔥)
    (hbM : GermIdeal.pullback (m := n) π 𝔟M = (idealPow 𝔥 (r + p)).mul 𝔓) :
    RestrictLe (strictTransform n π V.carrier) (GermIdeal.pullback (m := n) π 𝔅)
      ((idealPow 𝔥 r).mul 𝔓) := by
  have hπc := hπ.contMDiff
  have h𝔥c : 𝔥.IsCoherent := DivisorMetric.isCoherent_of_isInvertible h𝔥
  have h𝔓c : 𝔓.IsCoherent := DivisorMetric.isCoherent_of_isInvertible h𝔓
  have hpb := restrictLe_pullback hπc (mem_of_mem_strictTransform hπc V) h𝔟M hcomp
  rw [pullback_mul hπc h𝔅 (isCoherent_idealPow h𝔟m p), pullback_idealPow hπc h𝔟m p, hbm, hbM,
    idealPow_add h𝔥c r p,
    GermIdealTotalTransform.mul_assoc (isCoherent_idealPow h𝔥c r) (isCoherent_idealPow h𝔥c p)
      h𝔓c,
    mul_comm' (idealPow 𝔥 p) 𝔓,
    ← GermIdealTotalTransform.mul_assoc (isCoherent_idealPow h𝔥c r) h𝔓c
      (isCoherent_idealPow h𝔥c p)] at hpb
  refine restrictLe_of_restrictLe_mul_mul (isCoherent_pullback hπc h𝔅)
    (IdealWeightPowers.isCoherent_mul (isCoherent_idealPow h𝔥c r) h𝔓c)
    (isInvertibleAlong_of_isInvertible (isInvertible_idealPow h𝔥 p) fun O hO hOW => ?_) hpb
  obtain ⟨y, hyOW, hym, -⟩ :=
    exists_mem_strictTransform_notMem_zeroLocus₂ hπ V h𝔟m h𝔟M hVm hVM hO hOW
  refine ⟨y, hyOW, notMem_zeroLocus_idealPow h𝔥c ?_ p⟩
  rw [← hbm, zeroLocus_pullback hπc h𝔟m]
  exact hym

/-! ### The excess ideal -/

/-- **Copy-4's excess ideal `𝔣̃_B`** on the stage-2 model, and `𝔅 𝒪_{W₁} = 𝒪(-(G_M-pG_m)) 𝔣_B`.
With `𝔩 = 𝔥^r 𝔓` (on `W₁`: `𝒪(-(G_M - p G_m))`), `𝔣̃_B := colonAlong W₁ (𝔅̃ 𝒪) 𝔩` is coherent,
not contained in `𝓘_{W₁}`, and `Res_{W₁}(𝔅̃ 𝒪) = Res_{W₁}(𝔩 𝔣̃_B)`. -/
theorem excessIdeal_spec [CompactSpace X] {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) (V : ClosedIrreducibleAnalyticSubvariety n X) {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) k)
    {𝔟m 𝔟M 𝔅 : GermIdeal n X} (h𝔟m : 𝔟m.IsCoherent) (h𝔟M : 𝔟M.IsCoherent)
    (h𝔅 : 𝔅.IsCoherent) {r p : ℕ}
    (hcomp : RestrictLe V.carrier (𝔅.mul (idealPow 𝔟m p)) 𝔟M)
    (hVm : ¬ V.carrier ⊆ 𝔟m.zeroLocus) (hVM : ¬ V.carrier ⊆ 𝔟M.zeroLocus)
    (hVB : ¬ V.carrier ⊆ 𝔅.zeroLocus)
    {𝔥 𝔓 : GermIdeal n Y} (h𝔥 : 𝔥.IsInvertible) (h𝔓 : 𝔓.IsInvertible)
    (hbm : GermIdeal.pullback (m := n) π 𝔟m = 𝔥)
    (hbM : GermIdeal.pullback (m := n) π 𝔟M = (idealPow 𝔥 (r + p)).mul 𝔓) :
    (colonAlong n (strictTransform n π V.carrier) (GermIdeal.pullback (m := n) π 𝔅)
        ((idealPow 𝔥 r).mul 𝔓)).IsCoherent ∧
      ¬ (colonAlong n (strictTransform n π V.carrier) (GermIdeal.pullback (m := n) π 𝔅)
        ((idealPow 𝔥 r).mul 𝔓)).Le (vanishingIdeal (n := n) (strictTransform n π V.carrier)) ∧
      RestrictLe (strictTransform n π V.carrier) (GermIdeal.pullback (m := n) π 𝔅)
        (((idealPow 𝔥 r).mul 𝔓).mul (colonAlong n (strictTransform n π V.carrier)
          (GermIdeal.pullback (m := n) π 𝔅) ((idealPow 𝔥 r).mul 𝔓))) ∧
      RestrictLe (strictTransform n π V.carrier)
        (((idealPow 𝔥 r).mul 𝔓).mul (colonAlong n (strictTransform n π V.carrier)
          (GermIdeal.pullback (m := n) π 𝔅) ((idealPow 𝔥 r).mul 𝔓)))
        (GermIdeal.pullback (m := n) π 𝔅) := by
  set W := strictTransform n π V.carrier with hWdef
  have hπc := hπ.contMDiff
  have h𝔥c : 𝔥.IsCoherent := DivisorMetric.isCoherent_of_isInvertible h𝔥
  have h𝔓c : 𝔓.IsCoherent := DivisorMetric.isCoherent_of_isInvertible h𝔓
  have h𝔅Y : (GermIdeal.pullback (m := n) π 𝔅).IsCoherent := isCoherent_pullback hπc h𝔅
  have hIW := isCoherent_vanishingIdeal_of_isClosedConnectedSubmanifold hW
  have h𝔩c : ((idealPow 𝔥 r).mul 𝔓).IsCoherent :=
    IdealWeightPowers.isCoherent_mul (isCoherent_idealPow h𝔥c r) h𝔓c
  have hle := restrictLe_pullback_divided hπ V h𝔟m h𝔟M h𝔅 hcomp hVm hVM h𝔥 h𝔓 hbm hbM
  -- `𝔩` is invertible along `W₁`
  have h𝔩 : IsInvertibleAlong n W ((idealPow 𝔥 r).mul 𝔓) := by
    refine isInvertibleAlong_of_isInvertible
      (GermIdealTotalTransform.isInvertible_mul (isInvertible_idealPow h𝔥 r) h𝔓)
      fun O hO hOW => ?_
    obtain ⟨y, hyOW, hym, hyM⟩ :=
      exists_mem_strictTransform_notMem_zeroLocus₂ hπ V h𝔟m h𝔟M hVm hVM hO hOW
    refine ⟨y, hyOW, notMem_zeroLocus_mul (isCoherent_idealPow h𝔥c r) h𝔓c
      (notMem_zeroLocus_idealPow h𝔥c ?_ r) fun hy𝔓 => hyM ?_⟩
    · rw [← hbm, zeroLocus_pullback hπc h𝔟m]
      exact hym
    · have hyZ := zeroLocus_right_subset_mul (idealPow 𝔥 (r + p)) 𝔓 hy𝔓
      rw [← hbM, zeroLocus_pullback hπc h𝔟M] at hyZ
      exact hyZ
  have h1 := restrictLe_mul_colon h𝔅Y h𝔩 hle
  refine ⟨isCoherent_colonAlong hW.1 h𝔅Y hIW h𝔩c h𝔩 hle, ?_, h1,
    restrictLe_mul_colon' h𝔅Y hIW⟩
  -- `𝔅̃ 𝒪 ⊄ 𝓘_{W₁}`, hence the cofactor is not either
  refine not_le_vanishingIdeal_of_restrictLe_mul hW.1 h𝔅Y h1
    (not_le_vanishingIdeal_of_not_subset_zeroLocus fun hsub => ?_)
  obtain ⟨y, hyW, hyB, -⟩ :=
    exists_mem_strictTransform_notMem_zeroLocus₂ hπ V h𝔅 h𝔟m hVB hVm isOpen_univ
      (by simpa using hW.2.1.nonempty)
  have hyZ := hsub hyW.2
  rw [zeroLocus_pullback hπc h𝔅] at hyZ
  exact hyB hyZ

/-! ### After the third stage -/

variable {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **`eq:PF-restriction`, through `𝔅`.**  If `Res_{W₁}(𝔅̃ 𝒪_{Y₁}) = Res_{W₁}(𝔩 𝔣̃)` and a
further holomorphic `g : Y → Y₁` maps `W` into `W₁` with `𝔣̃ 𝒪_Y = 𝒪(-(P^F + P^F'))`, then
`Res_W(𝔅̃ 𝒪_Y) = Res_W((𝔩 𝒪_Y) · 𝒪(-(P^F + P^F')))`. -/
theorem restrictLe_pullback_excess {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π) {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {W₁ : Set Y} {W : Set Z} (hWW₁ : ∀ z ∈ W, g z ∈ W₁) {𝔅 : GermIdeal n X}
    (h𝔅 : 𝔅.IsCoherent) {𝔩 𝔣 : GermIdeal n Y} (h𝔩 : 𝔩.IsCoherent) (h𝔣 : 𝔣.IsCoherent)
    {PF PF' : EffectiveDivisor n Z}
    (hid : GermIdeal.pullback (m := n) g 𝔣 = PF.ideal.mul PF'.ideal)
    (h1 : RestrictLe W₁ (GermIdeal.pullback (m := n) π 𝔅) (𝔩.mul 𝔣))
    (h2 : RestrictLe W₁ (𝔩.mul 𝔣) (GermIdeal.pullback (m := n) π 𝔅)) :
    RestrictLe W (GermIdeal.pullback (m := n) (π ∘ g) 𝔅)
        ((GermIdeal.pullback (m := n) g 𝔩).mul (PF.ideal.mul PF'.ideal)) ∧
      RestrictLe W ((GermIdeal.pullback (m := n) g 𝔩).mul (PF.ideal.mul PF'.ideal))
        (GermIdeal.pullback (m := n) (π ∘ g) 𝔅) := by
  have h𝔅Y : (GermIdeal.pullback (m := n) π 𝔅).IsCoherent := isCoherent_pullback hπ h𝔅
  have h𝔩𝔣 : (𝔩.mul 𝔣).IsCoherent := IdealWeightPowers.isCoherent_mul h𝔩 h𝔣
  have e1 := restrictLe_pullback hg hWW₁ h𝔩𝔣 h1
  have e2 := restrictLe_pullback hg hWW₁ h𝔅Y h2
  rw [pullback_mul hg h𝔩 h𝔣, hid, ← pullback_comp hπ hg h𝔅] at e1 e2
  exact ⟨e1, e2⟩

end

end Hironaka.ExcessIdealPrincipalization
