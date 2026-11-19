import Hironaka.Resolution.HironakaG10FlatTorsionInduction
import Hironaka.Resolution.HironakaG10FlatZeroTail
import Hironaka.Resolution.HironakaG10FlatResolutionPkg

/-! # Privileged recipes: the inductive step of Douady's §7 Th. 1 for one sheaf

Douady 1966, §7 n° 4, proof of Th. 1, coordinates `P × ℂ` (`w` = the last coordinate), at `(z₀, 0)`.
A **privileged recipe** for `coker B` (`HasPrivRecipe B z₀`) consists of finitely many matrices `F_μ`
on `P` holomorphic at `z₀` (the "fibre pieces") such that from ANY finite free resolutions `e_μ` of the
`coker F_μ` on an open `U₀ ∋ z₀` one gets a finite free resolution `δ` of `coker B` with first matrix
`B` (zero tail) on an open `V ∋ (z₀, 0)` and a neighbourhood `N₀` of `z₀`, such that for every compact
regular-closed `K' ⊆ U₀ ∩ N₀` privileged for all the `e_μ`, the polydisc `K' × D̄(0,ρ)` is privileged
for `δ` for all small `ρ > 0`. So privileged neighbourhoods of `z₀` for the fibre pieces give privileged
neighbourhoods of `(z₀, 0)` for `coker B`.

* `exists_normal_resolution`: zero-tail normal form of a finite resolution (first matrix kept,
  privilege kept).
* `hasPrivRecipe_of_unit`: a recipe with one fibre piece from a statement about normalized resolutions.
* **`hasPrivRecipe_of_killed`** (torsion, `HironakaG10FlatTorsionStep.torsion_step`): `w` kills
  `coker B`; fibre piece `B(·, 0)`; every `ρ` works.
* **`hasPrivRecipe_of_regular`** (flat, `HironakaG10FlatPrivilegedFlatStep`): `w` regular on
  `coker B` at `(z₀, 0)`; fibre piece `B(·, 0)`; small `ρ`.
* **`hasPrivRecipe_extensionClosed`** (extension, `HironakaG10FlatExtensionStep.extension_step`):
  recipes for `C'` and `[A | T]` give one for `A` (fibre pieces: both families).
* **`hasPrivRecipe`**: with Oka's property and Noetherian germs on `P × ℂ`, EVERY `B` holomorphic at
  `(z₀, 0)` has a privileged recipe (`HironakaG10FlatTorsionInduction.of_noetherian`).
BP: hironaka-g10-flat-privileged-recipe.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatPrivilegedRecipe
noncomputable section
open OkaRelationSheaf HironakaG10FlatResolutionStart HironakaG10FlatPolydiscAlgebra
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatSplitComplex HironakaG10FlatZeroTail
  HironakaG10FlatResolutionPkg HironakaG10FlatReindex HironakaG10FlatSliceResolution
  HironakaG10FlatFlatFamilyPrivilege HironakaG10FlatPrivilegedFlatStep HironakaG10FlatTorsionStep
  HironakaG10FlatExtensionStep HironakaG10FlatTorsionFiltration HironakaG10FlatTorsionInduction

/-! ## Zero-tail normal form -/

section Normalize
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X} {m a b : ℕ} {s : ℕ → ℕ}

/-- **Zero-tail normal form** of a finite free resolution: same first matrix, ranks `0` beyond the
length, privileged wherever the original is. -/
theorem exists_normal_resolution
    {d : (k : ℕ) → Fin (rankSeq a b s k) → Fin (rankSeq a b s (k + 1)) → X → ℂ}
    (hd : FiniteResolutionOn U m d) :
    ∃ (s' : ℕ → ℕ) (d' : (k : ℕ) → Fin (rankSeq a b s' k) → Fin (rankSeq a b s' (k + 1)) → X → ℂ)
      (hd' : FiniteResolutionOn U m d'), d' 0 = d 0 ∧ (∀ k, m < k → rankSeq a b s' k = 0) ∧
      ∀ (K : Set X) [CompactSpace K] (hKU : K ⊆ U), PrivilegedOn K hKU m d hd.hol →
        PrivilegedOn K hKU m d' hd'.hol := by
  have hz := finiteResolutionOn_zeroTail hd
  have h0 : rankZ (rankSeq a b s) m 0 = a := rankZ_of_le (Nat.zero_le m)
  have h1 : rankZ (rankSeq a b s) m 1 = b := rankZ_of_le hd.pos
  refine ⟨fun k => rankZ (rankSeq a b s) m (k + 2), reindexChain (zeroTail hd.top d) (pkgEquiv h0 h1),
    finiteResolutionOn_reindex hz _, ?_, ?_,
    fun K _ hKU hp => privilegedOn_reindex hz _ K hKU (privilegedOn_zeroTail hd K hKU hp)⟩
  · funext i j
    show zeroTail hd.top d 0 (finCongr h0.symm i) (finCongr h1.symm j) = d 0 i j
    rw [zeroTail_apply hd.top (Nat.zero_le m)]
    rfl
  · intro k hk
    match k, hk with
    | 0, hk => omega
    | 1, hk => exact absurd hd.pos (by omega)
    | k + 2, hk => exact rankZ_eq_zero hk

end Normalize

/-! ## The recipe -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- **A privileged recipe for `coker B` at `(z₀, 0)`** (see the module docstring). -/
def HasPrivRecipe {a b : ℕ} (B : Fin a → Fin b → P × ℂ → ℂ) (z₀ : P) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a' b' : ι → ℕ) (F : (μ : ι) → Fin (a' μ) → Fin (b' μ) → P → ℂ),
    (∀ μ i j, HolAt (F μ i j) z₀) ∧
    ∀ (U₀ : Set P), IsOpen U₀ → z₀ ∈ U₀ → ∀ (m : ι → ℕ) (s : ι → ℕ → ℕ)
      (e : (μ : ι) → (k : ℕ) → Fin (rankSeq (a' μ) (b' μ) (s μ) k) →
        Fin (rankSeq (a' μ) (b' μ) (s μ) (k + 1)) → P → ℂ)
      (hres : ∀ μ, FiniteResolutionOn U₀ (m μ) (e μ)), (∀ μ, e μ 0 = F μ) →
      ∃ (V : Set (P × ℂ)) (M : ℕ) (s' : ℕ → ℕ)
        (δ : (k : ℕ) → Fin (rankSeq a b s' k) → Fin (rankSeq a b s' (k + 1)) → P × ℂ → ℂ)
        (hδ : FiniteResolutionOn V M δ), IsOpen V ∧ (z₀, (0 : ℂ)) ∈ V ∧ δ 0 = B ∧
        (∀ k, M < k → rankSeq a b s' k = 0) ∧
        ∃ N₀ ∈ 𝓝 z₀, ∀ (K' : Set P) (hK'U₀ : K' ⊆ U₀), K' ⊆ N₀ → IsCompact K' →
          K' ⊆ closure (interior K') →
          (∀ [CompactSpace K'], ∀ μ, PrivilegedOn K' hK'U₀ (m μ) (e μ) (hres μ).hol) →
          ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ hKV : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ V,
            ∀ [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)],
              PrivilegedOn (K' ×ˢ closedBall (0 : ℂ) ρ) hKV M δ hδ.hol

/-- **A recipe with one fibre piece** `F`, from a statement about normalized resolutions of
`coker F` (the produced resolution of `coker B` need not be normalized). -/
theorem hasPrivRecipe_of_unit {a b a' b' : ℕ} {B : Fin a → Fin b → P × ℂ → ℂ} {z₀ : P}
    (F : Fin a' → Fin b' → P → ℂ) (hF : ∀ i j, HolAt (F i j) z₀)
    (h : ∀ (U₀ : Set P), IsOpen U₀ → z₀ ∈ U₀ → ∀ (m : ℕ) (s : ℕ → ℕ)
      (e : (k : ℕ) → Fin (rankSeq a' b' s k) → Fin (rankSeq a' b' s (k + 1)) → P → ℂ)
      (hres : FiniteResolutionOn U₀ m e), e 0 = F → (∀ k, m < k → rankSeq a' b' s k = 0) →
      ∃ (V : Set (P × ℂ)) (M : ℕ) (s' : ℕ → ℕ)
        (δ : (k : ℕ) → Fin (rankSeq a b s' k) → Fin (rankSeq a b s' (k + 1)) → P × ℂ → ℂ)
        (hδ : FiniteResolutionOn V M δ), IsOpen V ∧ (z₀, (0 : ℂ)) ∈ V ∧ δ 0 = B ∧
        ∃ N₀ ∈ 𝓝 z₀, ∀ (K' : Set P) (hK'U₀ : K' ⊆ U₀), K' ⊆ N₀ → IsCompact K' →
          K' ⊆ closure (interior K') →
          (∀ [CompactSpace K'], PrivilegedOn K' hK'U₀ m e hres.hol) →
          ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ hKV : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ V,
            ∀ [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)],
              PrivilegedOn (K' ×ˢ closedBall (0 : ℂ) ρ) hKV M δ hδ.hol) :
    HasPrivRecipe B z₀ := by
  refine ⟨Unit, inferInstance, fun _ => a', fun _ => b', fun _ => F, fun _ => hF, ?_⟩
  intro U₀ hU₀ hz₀ m s e hres he0
  obtain ⟨s₁, e₁, hres₁, he₁0, htail₁, hpriv₁⟩ := exists_normal_resolution (hres ())
  obtain ⟨V, M, s', δ, hδ, hVo, hV, hδ0, N₀, hN₀, hK⟩ :=
    h U₀ hU₀ hz₀ (m ()) s₁ e₁ hres₁ (he₁0.trans (he0 ())) htail₁
  obtain ⟨s'', δ', hδ', hδ'0, htail', hpriv'⟩ := exists_normal_resolution hδ
  refine ⟨V, M, s'', δ', hδ', hVo, hV, hδ'0.trans hδ0, htail', N₀, hN₀,
    fun K' hK'U₀ hK'N hK'c hK'r hpe => ?_⟩
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  filter_upwards [hK K' hK'U₀ hK'N hK'c hK'r (fun {_} => hpriv₁ K' hK'U₀ (hpe ()))] with ρ hρ
  obtain ⟨hKV, hp⟩ := hρ
  exact ⟨hKV, fun {_} => hpriv' _ hKV hp⟩

/-- The matrix `B` in the coordinates `(w, z)`. -/
def unswapMat {κ ι : Type*} (B : κ → ι → P × ℂ → ℂ) : κ → ι → ℂ × P → ℂ :=
  fun i j x => B i j (x.2, x.1)

theorem holAt_unswapMat {κ ι : Type*} {B : κ → ι → P × ℂ → ℂ} {z₀ : P}
    (hB : ∀ i j, HolAt (B i j) (z₀, (0 : ℂ))) (i : κ) (j : ι) :
    HolAt (unswapMat B i j) ((0 : ℂ), z₀) :=
  (hB i j).comp (φ := fun x : ℂ × P => (x.2, x.1)) (continuous_snd.prodMk continuous_fst)
    fun _ => differentiableAt_snd.prodMk differentiableAt_fst

theorem holAt_slice {κ ι : Type*} {B : κ → ι → P × ℂ → ℂ} {z₀ : P}
    (hB : ∀ i j, HolAt (B i j) (z₀, (0 : ℂ))) (i : κ) (j : ι) :
    HolAt (fun z => B i j (z, 0)) z₀ :=
  (hB i j).comp (φ := fun z : P => (z, (0 : ℂ))) (continuous_id.prodMk continuous_const)
    fun _ => differentiableAt_id.prodMk (differentiableAt_const _)

theorem tendsto_unswap (z₀ : P) :
    Tendsto (fun x : ℂ × P => (x.2, x.1)) (𝓝 ((0 : ℂ), z₀)) (𝓝 (z₀, (0 : ℂ))) :=
  (continuous_snd.prodMk continuous_fst).tendsto ((0 : ℂ), z₀)

/-- A product neighbourhood `ball z₀ ε × ball 0 ε` inside an open set around `(z₀, 0)`. -/
theorem exists_ball_prod {V : Set (P × ℂ)} {z₀ : P} (hV : V ∈ 𝓝 (z₀, (0 : ℂ))) :
    ∃ ε > 0, ball z₀ ε ×ˢ ball (0 : ℂ) ε ⊆ V := by
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  exact ⟨ε, hε, by rwa [ball_prod_same]⟩

variable [FiniteDimensional ℂ P]

/-- **The torsion recipe**: if `w` kills `coker B` near `(z₀, 0)`, the fibre `B(·, 0)` is a recipe
(Douady §7 Prop. 5 Cor.; every `ρ` works). -/
theorem hasPrivRecipe_of_killed (hX : OkaProperty (ℂ × P)) {a b : ℕ} {B : Fin a → Fin b → P × ℂ → ℂ}
    {z₀ : P} (hB : ∀ i j, HolAt (B i j) (z₀, (0 : ℂ))) (hk : IsKilledBy B (fun x => x.2) (z₀, (0 : ℂ))) :
    HasPrivRecipe B z₀ := by
  obtain ⟨W, hW, hBW⟩ := hk
  refine hasPrivRecipe_of_unit (fun i j z => B i j (z, 0)) (holAt_slice hB) ?_
  intro U₀ hU₀ hz₀ m s e hres he0 htail
  obtain ⟨V, M, s', δ, hδ, hVo, hV, hδ0, hpriv⟩ := torsion_step hX hU₀ (exactStartOn_all hres htail)
    htail hz₀ (C := unswapMat B) (holAt_unswapMat hB)
    (Eventually.of_forall fun z i j => by rw [he0]; rfl) (W := unswapMat W) (holAt_unswapMat hW)
    ((tendsto_unswap z₀).eventually hBW)
  obtain ⟨ε, hε, hεV⟩ := exists_ball_prod (hVo.mem_nhds hV)
  refine ⟨V, M, s', δ, hδ, hVo, hV, hδ0.trans rfl, ball z₀ ε, ball_mem_nhds z₀ hε,
    fun K' hK'U₀ hK'N hK'c hK'r hpe => ?_⟩
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  obtain ⟨t, ht⟩ := (privilegedOn_iff_exists_splitBy hres K' hK'U₀).mp hpe
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  have hKV : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ V := fun q hq =>
    hεV ⟨hK'N hq.1, closedBall_subset_ball hρ.2 hq.2⟩
  exact ⟨hKV, fun {_} => hpriv K' hK'U₀ hK'r ⟨t, ht⟩ ρ hρ.1 hKV⟩

/-- **The flat recipe**: if `w` is regular on `coker B` at `(z₀, 0)`, the fibre `B(·, 0)` is a recipe
(Douady §7 Prop. 6 (a); small `ρ`). -/
theorem hasPrivRecipe_of_regular (hX : OkaProperty (ℂ × P)) {a b : ℕ}
    {B : Fin a → Fin b → P × ℂ → ℂ} {z₀ : P} (hB : ∀ i j, HolAt (B i j) (z₀, (0 : ℂ)))
    (hreg : RegularAt B (fun x => x.2) (z₀, (0 : ℂ))) : HasPrivRecipe B z₀ := by
  set L : (ℂ × P) ≃L[ℂ] (P × ℂ) := ContinuousLinearEquiv.prodComm ℂ ℂ P with hL
  have hregC : RegularAt (unswapMat B) (fun x => x.1) ((0 : ℂ), z₀) :=
    regularAt_comp_homeomorph L.toHomeomorph (fun _ => L.differentiableAt)
      (fun _ => L.symm.differentiableAt) (x := ((0 : ℂ), z₀)) hreg
  refine hasPrivRecipe_of_unit (fun i j z => B i j (z, 0)) (holAt_slice hB) ?_
  intro U₀ hU₀ hz₀ m s e hres he0 _
  obtain ⟨V, hVo, hyV, d, hd0, hdres, hdsl⟩ := exists_lift_resolution hX hU₀ hz₀ hres
    (holAt_unswapMat hB) (Eventually.of_forall fun z i j => by rw [he0]; rfl) hregC
  have hsl : ∀ᶠ z in 𝓝 z₀, ∀ k ∈ Finset.range (m + 1), ∀ i j, d k i j ((0 : ℂ), z) = e k i j z :=
    (Finset.eventually_all _).2 fun k hk => hdsl k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hVs : IsOpen (Prod.swap ⁻¹' V : Set (P × ℂ)) := hVo.preimage continuous_swap
  obtain ⟨ε, hε, hεV⟩ := exists_ball_prod (hVs.mem_nhds (show (z₀, (0 : ℂ)) ∈ Prod.swap ⁻¹' V from hyV))
  refine ⟨Prod.swap ⁻¹' V, m, s, fun k => swapMat (d k), finiteResolutionOn_swap hdres, hVs, hyV,
    by show swapMat (d 0) = B; rw [hd0]; rfl, ball z₀ ε ∩ {z | ∀ k ∈ Finset.range (m + 1), ∀ i j,
      d k i j ((0 : ℂ), z) = e k i j z}, inter_mem (ball_mem_nhds z₀ hε) hsl,
    fun K' hK'U₀ hK'N hK'c hK'r hpe => ?_⟩
  have hKW : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ z ∈ K', (w, z) ∈ V := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hε] with w hw z hz
    exact hεV (show (z, w) ∈ ball z₀ ε ×ˢ ball (0 : ℂ) ε from ⟨(hK'N hz).1, hw⟩)
  exact eventually_privilegedOn_prod hK'c hK'r hVo hKW hdres hres.hol hK'U₀
    (fun k hk z hz i j => (hK'N hz).2 k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) i j) hpe

/-- **The extension recipe** (Douady §7 Prop. 3): recipes for `C'` and `[A | T]` give one for `A`. -/
theorem hasPrivRecipe_extensionClosed {z₀ : P} :
    ExtensionClosed (fun a b (B : Fin a → Fin b → P × ℂ → ℂ) => HasPrivRecipe B z₀)
      (y := (z₀, (0 : ℂ))) := by
  intro a b t c A T C' Q _ _ _ hQh hQ hgen h' h''
  obtain ⟨ι₁, _, a₁, b₁, F₁, hF₁, hR₁⟩ := h'
  obtain ⟨ι₂, _, a₂, b₂, F₂, hF₂, hR₂⟩ := h''
  let F : (μ : ι₁ ⊕ ι₂) → Fin (Sum.elim a₁ a₂ μ) → Fin (Sum.elim b₁ b₂ μ) → P → ℂ := fun μ =>
    match μ with
    | .inl μ => F₁ μ
    | .inr μ => F₂ μ
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim a₁ a₂, Sum.elim b₁ b₂, F, ?_, ?_⟩
  · rintro (μ | μ) i j
    exacts [hF₁ μ i j, hF₂ μ i j]
  intro U₀ hU₀ hz₀ m s e hres he0
  obtain ⟨V', M', s₁, δ', hδ', hV'o, hV', hδ'0, htail', N₁, hN₁, hK₁⟩ :=
    hR₁ U₀ hU₀ hz₀ (fun μ => m (.inl μ)) (fun μ => s (.inl μ)) (fun μ => e (.inl μ))
      (fun μ => hres (.inl μ)) (fun μ => he0 (.inl μ))
  obtain ⟨V'', M'', s₂, δ'', hδ'', hV''o, hV'', hδ''0, htail'', N₂, hN₂, hK₂⟩ :=
    hR₂ U₀ hU₀ hz₀ (fun μ => m (.inr μ)) (fun μ => s (.inr μ)) (fun μ => e (.inr μ))
      (fun μ => hres (.inr μ)) (fun μ => he0 (.inr μ))
  obtain ⟨V, s₃, δ, hδhol, hVU', hVU'', hVo, hxV, hδ0, hδex, hδtail, hsplit⟩ :=
    extension_step hV'o hV''o hV' hV'' hQh hQ hgen (exactStartOn_all hδ' htail') hδ'0 htail'
      (exactStartOn_all hδ'' htail'') hδ''0 htail''
  have hres3 : FiniteResolutionOn V (M' + M'' + 5) δ :=
    ⟨by omega, hδtail _ (by omega), hδhol, fun k _ => hδex k⟩
  obtain ⟨ε, hε, hεV⟩ := exists_ball_prod (hVo.mem_nhds hxV)
  refine ⟨V, M' + M'' + 5, s₃, δ, hres3, hVo, hxV, hδ0, fun k hk => hδtail k (by omega),
    N₁ ∩ N₂ ∩ ball z₀ ε, inter_mem (inter_mem hN₁ hN₂) (ball_mem_nhds z₀ hε),
    fun K' hK'U₀ hK'N hK'c hK'r hpe => ?_⟩
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  have e1 := hK₁ K' hK'U₀ (fun z hz => (hK'N hz).1.1) hK'c hK'r (fun {_} μ => hpe (.inl μ))
  have e2 := hK₂ K' hK'U₀ (fun z hz => (hK'N hz).1.2) hK'c hK'r (fun {_} μ => hpe (.inr μ))
  filter_upwards [e1, e2, Ioo_mem_nhdsGT hε] with ρ hρ1 hρ2 hρ
  obtain ⟨hKV', hp'⟩ := hρ1
  obtain ⟨hKV'', hp''⟩ := hρ2
  have hKV : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ V := fun q hq =>
    hεV ⟨(hK'N hq.1).2, closedBall_subset_ball hρ.2 hq.2⟩
  refine ⟨hKV, fun {_} => ?_⟩
  obtain ⟨t1, ht1⟩ := (privilegedOn_iff_exists_splitBy hδ' _ hKV').mp hp'
  obtain ⟨t2, ht2⟩ := (privilegedOn_iff_exists_splitBy hδ'' _ hKV'').mp hp''
  obtain ⟨t3, ht3⟩ := hsplit _ hKV (M' + M'' + 5) ⟨t1, splitBy_all ht1 htail' _⟩
    ⟨t2, splitBy_all ht2 htail'' _⟩
  exact (privilegedOn_iff_exists_splitBy hres3 _ hKV).mpr ⟨t3, ht3⟩

/-- **Every presentation near `(z₀, 0)` has a privileged recipe** (Douady §7 n° 4, the inductive step
of Th. 1 for one sheaf): `P × ℂ` with Oka's property and Noetherian germs. -/
theorem hasPrivRecipe [IsNoetherianRing (HolGerm (P × ℂ))] (hX : OkaProperty (P × ℂ)) {z₀ : P}
    {a b : ℕ} (B : Fin a → Fin b → P × ℂ → ℂ) (hB : ∀ i j, HolAt (B i j) (z₀, (0 : ℂ))) :
    HasPrivRecipe B z₀ := by
  set L : (ℂ × P) ≃L[ℂ] (P × ℂ) := ContinuousLinearEquiv.prodComm ℂ ℂ P with hL
  have hX' : OkaProperty (ℂ × P) := OkaProperty.of_homeomorph L.toHomeomorph
    (fun _ => L.differentiableAt) (fun _ => L.symm.differentiableAt) hX
  exact of_noetherian (fun a b (B : Fin a → Fin b → P × ℂ → ℂ) => HasPrivRecipe B z₀) hX
    (holAt_of_differentiableOn isOpen_univ differentiableOn_snd (mem_univ _))
    (fun _ _ _ hC hk => hasPrivRecipe_of_killed hX' hC hk)
    (fun _ _ _ hA hreg => hasPrivRecipe_of_regular hX' hA hreg) hasPrivRecipe_extensionClosed a b B hB

end
end Hironaka.HironakaG10FlatPrivilegedRecipe
