import Hironaka.Resolution.HironakaG10FlatPrivilegedRecipe

/-! # Assembly of Douady's theorem of privileged neighbourhoods: the induction step `P ⇝ P × ℂ`

Douady 1966, §7 n° 4, Th. 1, the induction step: if every point of `P` has privileged neighbourhoods
in `𝒦'` for every finite family of sheaves, then every point of `P × ℂ` has privileged polydisc
neighbourhoods `K' × D̄(c,ρ)` (`discProd 𝒦'`), provided `P × ℂ` has Oka's property and Noetherian
germs.

* **`hasPrivilegedNbhds_of_recipes`**: ONE application of the induction hypothesis at `z₀` to all the
  fibre pieces of privileged recipes (`HironakaG10FlatPrivilegedRecipe`) of finitely many `B_l` gives
  privileged neighbourhoods of `(z₀, 0)` for all `coker B_l`.
* Transport along biholomorphic homeomorphisms `φ : X ≃ₜ Y`: `pullbackAlg`/`pullbackCLM`
  (`B(L) → B(K)`, `f ↦ f ∘ ψ`), `piCLM`, `matrixOperator_piCLM`;
  `finiteResolutionOn_comp_homeomorph`, **`privilegedOn_comp_homeomorph`** (`φ K` is privileged for
  `d ∘ φ⁻¹` if `K` is for `d`), **`hasPrivilegedNbhds_of_comp_homeomorph`**.
* Translation in `w`: `image_discProd_subset`.
* **`privilegedNbhdsProperty_prod`**: `PrivilegedNbhdsProperty P 𝒦' → PrivilegedNbhdsProperty (P × ℂ)
  (discProd 𝒦')` (Oka and Noetherian germs on `P × ℂ`, `P` finite dimensional).
BP: hironaka-g10-flat-privileged-assembly.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatPrivilegedAssembly
noncomputable section
open OkaRelationSheaf HironakaG10FlatResolutionStart HironakaG10FlatPolydiscAlgebra
  HironakaG10FlatPrivilegedNbhd HironakaG10FlatSplitComplex HironakaG10FlatPrivilegedRecipe

/-! ## Transport along biholomorphic homeomorphisms -/

section Transport
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
  [NormedSpace ℂ Y]

/-- `ψ` restricted to `K → L`. -/
def mapsToCM (ψ : X → Y) (hψc : Continuous ψ) {K : Set X} {L : Set Y} (hKL : MapsTo ψ K L) :
    C(K, L) :=
  ⟨fun z => ⟨ψ z, hKL z.2⟩, (hψc.comp continuous_subtype_val).subtype_mk _⟩

/-- **Pull-back `B(L) → B(K)`**, `f ↦ f ∘ ψ`, along a holomorphic map with `ψ(K) ⊆ L`,
`ψ(K̊) ⊆ L̊`. -/
def pullbackAlg (ψ : X → Y) (hψc : Continuous ψ) (hψd : ∀ x, DifferentiableAt ℂ ψ x) {K : Set X}
    {L : Set Y} (hKL : MapsTo ψ K L) (hint : MapsTo ψ (interior K) (interior L)) :
    holSubalgebra L →ₐ[ℂ] holSubalgebra K where
  toFun f := ⟨(f : C(L, ℂ)).comp (mapsToCM ψ hψc hKL), by
    rw [mem_holSubalgebra]
    intro x hx
    have hψx : ψ x ∈ interior L := hint hx
    have h1 : DifferentiableAt ℂ (extendZero L f) (ψ x) :=
      ((mem_holSubalgebra.mp f.2) (ψ x) hψx).differentiableAt (isOpen_interior.mem_nhds hψx)
    have h3 : extendZero K ((f : C(L, ℂ)).comp (mapsToCM ψ hψc hKL)) =ᶠ[𝓝 x] extendZero L f ∘ ψ :=
      eventually_of_mem (isOpen_interior.mem_nhds hx) fun z hz => by
        simp only [Function.comp_apply, extendZero_of_mem K _ (interior_subset hz),
          extendZero_of_mem L _ (hKL (interior_subset hz))]
        rfl
    exact ((h1.comp x (hψd x)).congr_of_eventuallyEq h3).differentiableWithinAt⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem pullbackAlg_apply (ψ : X → Y) (hψc : Continuous ψ) (hψd : ∀ x, DifferentiableAt ℂ ψ x)
    {K : Set X} {L : Set Y} (hKL : MapsTo ψ K L) (hint : MapsTo ψ (interior K) (interior L))
    (f : holSubalgebra L) (z : K) :
    ((pullbackAlg ψ hψc hψd hKL hint f : holSubalgebra K) : C(K, ℂ)) z =
      (f : C(L, ℂ)) ⟨ψ z, hKL z.2⟩ := rfl

/-- The pull-back as a bounded operator. -/
def pullbackCLM (ψ : X → Y) (hψc : Continuous ψ) (hψd : ∀ x, DifferentiableAt ℂ ψ x) {K : Set X}
    {L : Set Y} [CompactSpace K] [CompactSpace L] (hKL : MapsTo ψ K L)
    (hint : MapsTo ψ (interior K) (interior L)) : holSubalgebra L →L[ℂ] holSubalgebra K :=
  (pullbackAlg ψ hψc hψd hKL hint).toLinearMap.mkContinuous 1 fun f => by
    rw [one_mul, norm_holSubalgebra, norm_holSubalgebra,
      ContinuousMap.norm_le _ (norm_nonneg _)]
    intro z
    exact ContinuousMap.norm_coe_le_norm (f : C(L, ℂ)) _

theorem pullbackCLM_apply (ψ : X → Y) (hψc : Continuous ψ) (hψd : ∀ x, DifferentiableAt ℂ ψ x)
    {K : Set X} {L : Set Y} [CompactSpace K] [CompactSpace L] (hKL : MapsTo ψ K L)
    (hint : MapsTo ψ (interior K) (interior L)) (f : holSubalgebra L) :
    pullbackCLM ψ hψc hψd hKL hint f = pullbackAlg ψ hψc hψd hKL hint f := rfl

/-- A bounded operator applied coordinatewise. -/
def piCLM {R S : Type*} [NormedRing R] [NormedAlgebra ℂ R] [NormedRing S] [NormedAlgebra ℂ S]
    (T : R →L[ℂ] S) (n : ℕ) : (Fin n → R) →L[ℂ] (Fin n → S) :=
  ContinuousLinearMap.pi fun i => T.comp (ContinuousLinearMap.proj i)

theorem piCLM_apply {R S : Type*} [NormedRing R] [NormedAlgebra ℂ R] [NormedRing S]
    [NormedAlgebra ℂ S] (T : R →L[ℂ] S) (n : ℕ) (v : Fin n → R) (i : Fin n) :
    piCLM T n v i = T (v i) := rfl

/-- Matrix operators commute with a coordinatewise algebra map. -/
theorem matrixOperator_piCLM {R S : Type*} [NormedRing R] [NormedAlgebra ℂ R] [NormedRing S]
    [NormedAlgebra ℂ S] (T : R →ₐ[ℂ] S) (Tc : R →L[ℂ] S) (hT : ∀ x, Tc x = T x) {p q : ℕ}
    (M : Fin p → Fin q → R) (M' : Fin p → Fin q → S) (hM : ∀ i j, M' i j = T (M i j))
    (v : Fin q → R) : matrixOperator M' (piCLM Tc q v) = piCLM Tc p (matrixOperator M v) := by
  funext i
  simp only [matrixOperator_apply, piCLM_apply, hT, hM, map_sum, map_mul]

/-- Finite free resolutions transport along biholomorphic homeomorphisms. -/
theorem finiteResolutionOn_comp_homeomorph (φ : X ≃ₜ Y) (hφ : ∀ x, DifferentiableAt ℂ φ x)
    (hφs : ∀ y, DifferentiableAt ℂ φ.symm y) {U : Set X} {m : ℕ} {r : ℕ → ℕ}
    {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ} (hd : FiniteResolutionOn U m d) :
    FiniteResolutionOn (φ.symm ⁻¹' U) m (fun k i j => d k i j ∘ φ.symm) :=
  ⟨hd.pos, hd.top, fun k i j => (hd.hol k i j).comp (fun y _ => (hφs y).differentiableWithinAt)
    fun _ hy => hy, fun k hk => exactStartOn_comp_homeomorph φ.symm hφs hφ (hd.exact k hk)⟩

theorem image_subset_preimage_symm (φ : X ≃ₜ Y) {K U : Set X} (hKU : K ⊆ U) :
    φ '' K ⊆ φ.symm ⁻¹' U := by
  rintro _ ⟨x, hx, rfl⟩
  simpa using hKU hx

theorem mapsTo_symm_image (φ : X ≃ₜ Y) (K : Set X) : MapsTo φ.symm (φ '' K) K := by
  rintro _ ⟨x, hx, rfl⟩
  simpa using hx

theorem mapsTo_symm_interior_image (φ : X ≃ₜ Y) (K : Set X) :
    MapsTo φ.symm (interior (φ '' K)) (interior K) := by
  rw [← φ.image_interior]
  exact mapsTo_symm_image φ (interior K)

theorem mapsTo_interior_image (φ : X ≃ₜ Y) (K : Set X) :
    MapsTo φ (interior K) (interior (φ '' K)) := by
  rw [← φ.image_interior]
  exact fun x hx => mem_image_of_mem φ hx

/-- **Privilege transports along biholomorphic homeomorphisms**: if `K` is privileged for `d`, then
`φ K` is privileged for `d ∘ φ⁻¹` (`B(φ K) ≅ B(K)`, domination with `h = 0`). -/
theorem privilegedOn_comp_homeomorph (φ : X ≃ₜ Y) (hφ : ∀ x, DifferentiableAt ℂ φ x)
    (hφs : ∀ y, DifferentiableAt ℂ φ.symm y) {U : Set X} {m : ℕ} {r : ℕ → ℕ}
    {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ} (hd : FiniteResolutionOn U m d)
    (K : Set X) [CompactSpace K] (hKU : K ⊆ U) [CompactSpace (φ '' K)]
    (hp : PrivilegedOn K hKU m d hd.hol) :
    PrivilegedOn (φ '' K) (image_subset_preimage_symm φ hKU) m (fun k i j => d k i j ∘ φ.symm)
      (finiteResolutionOn_comp_homeomorph φ hφ hφs hd).hol := by
  have hd' := finiteResolutionOn_comp_homeomorph φ hφ hφs hd
  have hKU' := image_subset_preimage_symm φ hKU
  obtain ⟨t, ht⟩ := (privilegedOn_iff_exists_splitBy hd K hKU).mp hp
  rw [privilegedOn_iff_exists_splitBy hd' (φ '' K) hKU']
  set Ta := pullbackAlg φ.symm φ.symm.continuous hφs (mapsTo_symm_image φ K)
    (mapsTo_symm_interior_image φ K) with hTa
  set Tc := pullbackCLM φ.symm φ.symm.continuous hφs (mapsTo_symm_image φ K)
    (mapsTo_symm_interior_image φ K) with hTc
  set Sa := pullbackAlg φ φ.continuous hφ (mapsTo_image φ K) (mapsTo_interior_image φ K) with hSa
  set Sc := pullbackCLM φ φ.continuous hφ (mapsTo_image φ K) (mapsTo_interior_image φ K) with hSc
  have hT : ∀ f, Tc f = Ta f := fun f => rfl
  have hS : ∀ f, Sc f = Sa f := fun f => rfl
  have hM1 : ∀ k i j, restrictMatrix (φ '' K) hKU' (fun i j => d k i j ∘ φ.symm) (hd'.hol k) i j =
      Ta (restrictMatrix K hKU (d k) (hd.hol k) i j) :=
    fun k i j => Subtype.ext (ContinuousMap.ext fun z => rfl)
  have hM2 : ∀ k i j, restrictMatrix K hKU (d k) (hd.hol k) i j =
      Sa (restrictMatrix (φ '' K) hKU' (fun i j => d k i j ∘ φ.symm) (hd'.hol k) i j) := by
    intro k i j
    refine Subtype.ext (ContinuousMap.ext fun z => ?_)
    show d k i j z = d k i j (φ.symm (φ z))
    rw [φ.symm_apply_apply]
  have hTS : ∀ f : holSubalgebra (φ '' K), Ta (Sa f) = f := by
    intro f
    refine Subtype.ext (ContinuousMap.ext fun z => ?_)
    show (f : C(φ '' K, ℂ)) ⟨φ (φ.symm z), _⟩ = (f : C(φ '' K, ℂ)) z
    congr 1
    exact Subtype.ext (φ.apply_symm_apply z)
  refine ⟨_, ht.of_dominated' (fun k => piCLM Tc (r k)) (fun k => piCLM Sc (r k)) (fun _ => 0)
    (fun k x => matrixOperator_piCLM Ta Tc hT _ _ (hM1 k) x)
    (fun k y => matrixOperator_piCLM Sa Sc hS _ _ (hM2 k) y) (fun k _ y => ?_)⟩
  simp only [zero_apply, map_zero, add_zero, sub_eq_zero]
  funext i
  rw [piCLM_apply, piCLM_apply, hT, hS, hTS]

/-- **Privileged neighbourhoods transport along biholomorphic homeomorphisms.** -/
theorem hasPrivilegedNbhds_of_comp_homeomorph (φ : X ≃ₜ Y) (hφ : ∀ x, DifferentiableAt ℂ φ x)
    (hφs : ∀ y, DifferentiableAt ℂ φ.symm y) {𝒦 : Set (Set X)} {ι : Type*} {a b : ι → ℕ}
    {A : (l : ι) → Fin (a l) → Fin (b l) → Y → ℂ} {x : X}
    (h : HasPrivilegedNbhds 𝒦 (fun l i j => A l i j ∘ φ) x) :
    HasPrivilegedNbhds ((fun K => φ '' K) '' 𝒦) A (φ x) := by
  obtain ⟨U, m, s, d, hres, hU, hxU, hd0, hK⟩ := h
  refine ⟨φ.symm ⁻¹' U, m, s, fun l k i j => d l k i j ∘ φ.symm,
    fun l => finiteResolutionOn_comp_homeomorph φ hφ hφs (hres l), hU.preimage φ.symm.continuous,
    by simpa using hxU, fun l => ?_, fun N hN => ?_⟩
  · funext i j y
    show d l 0 i j (φ.symm y) = A l i j y
    rw [hd0 l]
    simp
  · obtain ⟨K, hK𝒦, hKN, hKU, hKc, hKx, hKr, hpriv⟩ :=
      hK (φ ⁻¹' N) (φ.continuous.continuousAt.preimage_mem_nhds hN)
    have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
    refine ⟨φ '' K, mem_image_of_mem _ hK𝒦, image_subset_iff.2 hKN,
      image_subset_preimage_symm φ hKU, hKc.image φ.continuous, ?_, ?_,
      fun {_} l => privilegedOn_comp_homeomorph φ hφ hφs (hres l) K hKU (hpriv l)⟩
    · rw [← φ.map_nhds_eq]
      exact image_mem_map hKx
    · rw [← φ.image_interior, ← φ.image_closure]
      exact image_mono hKr

end Transport

/-! ## One application of the induction hypothesis -/

section Assembly
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- **Privileged neighbourhoods from privileged recipes** (Douady §7 n° 4): the induction hypothesis
at `z₀`, applied ONCE to the finite family of all fibre pieces of recipes for the `B_l`, gives
privileged polydiscs `K' × D̄(0,ρ)` at `(z₀, 0)` for all the `coker B_l`. -/
theorem hasPrivilegedNbhds_of_recipes {𝒦' : Set (Set P)} (hIH : PrivilegedNbhdsProperty P 𝒦')
    {ι : Type} [Fintype ι] {a b : ι → ℕ} {B : (l : ι) → Fin (a l) → Fin (b l) → P × ℂ → ℂ}
    {z₀ : P} (hR : ∀ l, HasPrivRecipe (B l) z₀) :
    HasPrivilegedNbhds (discProd 𝒦') B (z₀, (0 : ℂ)) := by
  choose κ hκ a' b' F hF hRF using hR
  have : ∀ l, Fintype (κ l) := hκ
  obtain ⟨U₀, m, s, e, hres, hU₀o, hz₀, he0, hK⟩ := hIH (Σ l, κ l) (fun p => a' p.1 p.2)
    (fun p => b' p.1 p.2) (fun p => F p.1 p.2) z₀ (fun p i j => hF p.1 p.2 i j)
  have hrec := fun l => hRF l U₀ hU₀o hz₀ (fun μ => m ⟨l, μ⟩) (fun μ => s ⟨l, μ⟩)
    (fun μ => e ⟨l, μ⟩) (fun μ => hres ⟨l, μ⟩) (fun μ => he0 ⟨l, μ⟩)
  choose V M s' δ hδ hVo hV hδ0 _ N hN hKN using hrec
  set W : Set (P × ℂ) := ⋂ l, V l with hW
  have hWo : IsOpen W := isOpen_iInter_of_finite hVo
  have hzW : (z₀, (0 : ℂ)) ∈ W := mem_iInter.2 hV
  refine ⟨W, M, s', δ, fun l => (hδ l).mono (iInter_subset _ l), hWo, hzW, hδ0, fun Nb hNb => ?_⟩
  obtain ⟨ε, hε, hεN⟩ := exists_ball_prod (inter_mem hNb (hWo.mem_nhds hzW))
  obtain ⟨K', hK'𝒦, hK'N, hK'U₀, hK'c, hK'x, hK'r, hpriv⟩ :=
    hK (ball z₀ ε ∩ ⋂ l, N l) (inter_mem (ball_mem_nhds z₀ hε) (iInter_mem.2 hN))
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'c
  have hρ : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ l, ∃ hKV : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ V l,
      ∀ [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)],
        PrivilegedOn (K' ×ˢ closedBall (0 : ℂ) ρ) hKV (M l) (δ l) (hδ l).hol :=
    eventually_all.2 fun l => hKN l K' hK'U₀ (fun z hz => mem_iInter.1 (hK'N hz).2 l) hK'c hK'r
      (fun {_} μ => hpriv ⟨l, μ⟩)
  obtain ⟨ρ, hρl, hρpos, hρε⟩ := (hρ.and (Ioo_mem_nhdsGT hε)).exists
  have hKN' : K' ×ˢ closedBall (0 : ℂ) ρ ⊆ Nb ∩ W := fun q hq =>
    hεN ⟨(hK'N hq.1).1, closedBall_subset_ball hρε hq.2⟩
  refine ⟨K' ×ˢ closedBall (0 : ℂ) ρ, ⟨K', hK'𝒦, 0, ρ, hρpos, rfl⟩, fun q hq => (hKN' hq).1,
    fun q hq => (hKN' hq).2, hK'c.prod (isCompact_closedBall 0 ρ),
    prod_mem_nhds hK'x (closedBall_mem_nhds 0 hρpos), subset_closure_interior_prod hK'r hρpos,
    fun {_} l => ?_⟩
  obtain ⟨_, hpl⟩ := hρl l
  exact hpl

/-- Translations in `w` preserve the polydiscs `K' × D̄(c,ρ)`. -/
theorem image_discProd_subset {𝒦' : Set (Set P)} (w₀ : ℂ) :
    (fun K => (Homeomorph.addRight ((0 : P), w₀)) '' K) '' discProd 𝒦' ⊆ discProd 𝒦' := by
  rintro _ ⟨_, ⟨K', hK', c, ρ, hρ, rfl⟩, rfl⟩
  refine ⟨K', hK', c + w₀, ρ, hρ, ?_⟩
  ext ⟨z, w⟩
  simp only [mem_image, mem_prod, mem_closedBall, Homeomorph.coe_addRight, Prod.exists,
    Prod.mk_add_mk, add_zero, Prod.mk.injEq]
  constructor
  · rintro ⟨z', w', ⟨hz', hw'⟩, rfl, rfl⟩
    refine ⟨hz', ?_⟩
    rwa [dist_add_right]
  · rintro ⟨hz, hw⟩
    refine ⟨z, w - w₀, ⟨hz, ?_⟩, rfl, by ring⟩
    have : dist (w - w₀) c = dist w (c + w₀) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      ring
    rwa [this]

variable [FiniteDimensional ℂ P]

/-- **The induction step of Douady's theorem of privileged neighbourhoods** (§7 n° 4, Th. 1): if
`P × ℂ` has Oka's property and Noetherian germs and every point of `P` has privileged neighbourhoods
in `𝒦'` for every finite family of sheaves, then every point of `P × ℂ` has privileged polydisc
neighbourhoods `K' × D̄(c,ρ)`, `K' ∈ 𝒦'`, for every finite family of sheaves. -/
theorem privilegedNbhdsProperty_prod [IsNoetherianRing (HolGerm (P × ℂ))]
    (hX : OkaProperty (P × ℂ)) {𝒦' : Set (Set P)} (hIH : PrivilegedNbhdsProperty P 𝒦') :
    PrivilegedNbhdsProperty (P × ℂ) (discProd 𝒦') := by
  intro ι _ a b A x hA
  set τ : P × ℂ ≃ₜ P × ℂ := Homeomorph.addRight ((0 : P), x.2) with hτ
  have hτd : ∀ q, DifferentiableAt ℂ τ q := fun q => by
    show DifferentiableAt ℂ (fun y => y + ((0 : P), x.2)) q
    exact differentiableAt_id.add_const _
  have hτsd : ∀ q, DifferentiableAt ℂ τ.symm q := fun q => by
    show DifferentiableAt ℂ (fun y => y + -((0 : P), x.2)) q
    exact differentiableAt_id.add_const _
  have hτx : τ (x.1, 0) = x := by
    show (x.1, (0 : ℂ)) + ((0 : P), x.2) = x
    ext <;> simp
  have hB : ∀ l i j, HolAt (A l i j ∘ τ) (x.1, (0 : ℂ)) := fun l i j => by
    have h1 : HolAt (A l i j) (τ (x.1, 0)) := by rw [hτx]; exact hA l i j
    exact h1.comp τ.continuous hτd
  have h := hasPrivilegedNbhds_of_comp_homeomorph τ hτd hτsd
    (hasPrivilegedNbhds_of_recipes hIH (B := fun l i j => A l i j ∘ τ)
      fun l => hasPrivRecipe hX _ (hB l))
  rw [hτx] at h
  exact h.mono_class (image_discProd_subset x.2)

end Assembly

end
end Hironaka.HironakaG10FlatPrivilegedAssembly
