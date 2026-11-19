import Hironaka.Coherence.OkaCoherence
import Hironaka.Resolution.HironakaG10FlatPolydiscKoszulBase
import Hironaka.Resolution.HironakaG10FlatGeneralizedInverse

/-! # Local starts of free resolutions (Oka) and their direct exactness over `B(K)`

Douady 1966, §7 n° 1 (Déf. 1): a compact polydisc `K` is privileged for a coherent sheaf if the
`B(K)`-complex of a free resolution near `K` is exact and direct. Douady admits the local existence
of finite free resolutions (Oka + syzygies, §7 (a)); here the local existence of free resolutions of
any finite length is derived from the project's Oka coherence theorem
(`OkaCoherence.okaProperty_euclidean`), at every point of a neighbourhood.

Conventions: a matrix `F : ι₀ → ι₁ → X → ℂ` acts on column vectors, `(F a)_i = ∑_j F_{ij} a_j`
(as `HironakaG10FlatPolydiscAlgebra.matrixOperator`).

* `ExactStartOn U G F`: holomorphic matrices `L₂ →G L₁ →F L₀` on `U` with `F G = 0` on `U`, exact at
  the level of germs at EVERY point `y ∈ U` (every germ relation of `F` at `y` is a germ combination of
  the columns of `G`); `ExactStartOn.mono`.
* `exists_exactStartOn` (from Oka's property of `X`), `exists_exactStartOn_euclidean` (on `ℂⁿ`).
* `ResolvesOn U m F`: a chain `F = d₀, d₁, …, d_m` of holomorphic matrices on `U`, exact at every
  point of `U` in the middle degrees; `exists_resolvesOn`, `exists_resolvesOn_euclidean`: a free
  resolution of any prescribed finite length exists on a neighbourhood of every point.
* `restrictMatrix`: the `B(K)`-matrix of a holomorphic matrix on `U ⊇ K`; `restrictMatrix_comp`.
* `DirectExact g f` (over any normed algebra): `f g = 0`, `im g = ker f`, and `ker f`, `im f`,
  `ker g` closed and complemented — exactly the hypotheses of
  `HironakaG10FlatPolydiscKoszulBase.koszul_directExact_of_base` (`DirectExact.koszul`); both maps
  then have bounded generalized inverses (`DirectExact.exists_generalizedInverse_f/_g`), and `g`
  has a bounded right inverse on `ker f` (`DirectExact.exists_rightInverse`, the hypothesis of
  Frisch's Lemme 3 (i) core `HironakaG10FlatFrischExactPersistence.eventually_directExact`).
* `DirectExactStartOn K U G F`: the `B(K)`-complex of an exact start on `U ⊇ K` is direct exact
  (`K` privileged for the start).

NOT proved here: that small polydiscs ARE privileged (Douady §7 Th. 1).
BP: hironaka-g10-flat-resolution-start.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatResolutionStart
noncomputable section
open OkaRelationSheaf HironakaG10FlatPolydiscAlgebra

section Germ
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The columns of a matrix `G : ι₁ → ι₂ → X → ℂ`, as a family of vectors indexed by `ι₂`. -/
def columns {ι₁ ι₂ : Type*} (G : ι₁ → ι₂ → X → ℂ) : ι₂ → ι₁ → X → ℂ := fun k j => G j k

/-- **An exact start of a free resolution on `U`**: holomorphic matrices `L₂ →G L₁ →F L₀` on `U`,
`F G = 0` on `U`, exact at the level of germs at every point of `U`. -/
structure ExactStartOn {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀] (U : Set X)
    (G : ι₁ → ι₂ → X → ℂ) (F : ι₀ → ι₁ → X → ℂ) : Prop where
  holF : ∀ i j, DifferentiableOn ℂ (F i j) U
  holG : ∀ j k, DifferentiableOn ℂ (G j k) U
  comp : ∀ i k, ∀ x ∈ U, ∑ j, F i j x * G j k x = 0
  exact : ∀ y ∈ U, ∀ a : ι₁ → X → ℂ, IsRelationAt F y a → IsCombinationAt (columns G) y a

variable {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

theorem ExactStartOn.mono {U V : Set X} {G : ι₁ → ι₂ → X → ℂ} {F : ι₀ → ι₁ → X → ℂ}
    (h : ExactStartOn U G F) (hVU : V ⊆ U) : ExactStartOn V G F :=
  ⟨fun i j => (h.holF i j).mono hVU, fun j k => (h.holG j k).mono hVU,
    fun i k x hx => h.comp i k x (hVU hx), fun y hy a ha => h.exact y (hVU hy) a ha⟩

/-- Generators of the relation sheaf of `F` on `U` are the columns of an exact start. -/
theorem exactStartOn_of_generates {μ : Type*} [Fintype μ] {U : Set X} {F : ι₀ → ι₁ → X → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) {σ : μ → ι₁ → X → ℂ}
    (hσ : GeneratesRelationsOn F U σ) : ExactStartOn U (fun j k => σ k j) F := by
  refine ⟨hF, fun j k => hσ.1 k j, fun i k x hx => ?_, fun y hy a ha => hσ.2.2 y hy a ha⟩
  rw [← hσ.2.1 k i x hx]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Relabelling the generators along an equivalence. -/
theorem ExactStartOn.reindex {κ : Type*} [Fintype κ] {U : Set X} {G : ι₁ → ι₂ → X → ℂ}
    {F : ι₀ → ι₁ → X → ℂ} (h : ExactStartOn U G F) (e : κ ≃ ι₂) :
    ExactStartOn U (fun j k => G j (e k)) F := by
  refine ⟨h.holF, fun j k => h.holG j (e k), fun i k x hx => h.comp i (e k) x hx,
    fun y hy a ha => ?_⟩
  obtain ⟨c, hc, hca⟩ := h.exact y hy a ha
  refine ⟨fun k => c (e k), fun k => hc (e k), fun j => (hca j).trans ?_⟩
  exact Eventually.of_forall fun x =>
    (Equiv.sum_comp e (fun k => c k x * columns G k j x)).symm

/-- Finitely many functions holomorphic near `x₀` are holomorphic on a common open neighbourhood. -/
theorem exists_open_differentiableOn {κ ι : Type*} [Finite κ] [Finite ι] {F : κ → ι → X → ℂ}
    {x₀ : X} (hF : ∀ i j, HolAt (F i j) x₀) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ ∀ i j, DifferentiableOn ℂ (F i j) V := by
  have h : ∀ᶠ x in 𝓝 x₀, ∀ i j, DifferentiableAt ℂ (F i j) x :=
    eventually_all.2 fun i => eventually_all.2 fun j => hF i j
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.1 h
  exact ⟨V, hVo, hxV, fun i j x hx => (hV x hx i j).differentiableWithinAt⟩

/-- **Oka ⇒ exact starts**: if `X` has Oka's property, every finite holomorphic matrix near `x₀`
is the end of an exact start of a free resolution on an open neighbourhood of `x₀`. -/
theorem exists_exactStartOn (hX : OkaProperty X) {a b : ℕ} (F : Fin a → Fin b → X → ℂ) (x₀ : X)
    (hF : ∀ i j, HolAt (F i j) x₀) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ (c : ℕ) (G : Fin b → Fin c → X → ℂ), ExactStartOn U G F := by
  obtain ⟨U₁, hU₁, hx₁, μ, _, σ, hσ⟩ := hX (Fin a) (Fin b) F x₀ hF
  obtain ⟨V, hV, hxV, hFV⟩ := exists_open_differentiableOn hF
  refine ⟨U₁ ∩ V, hU₁.inter hV, ⟨hx₁, hxV⟩, Fintype.card μ, _,
    ((exactStartOn_of_generates (fun i j => (hFV i j).mono inter_subset_right)
      (hσ.mono inter_subset_left)).reindex (Fintype.equivFin μ).symm)⟩

/-- **A free resolution of length `m` on `U`** ending with `F`: a chain `F = d₀, d₁, …, d_m` of
holomorphic matrices on `U`, each consecutive pair an exact start on `U`. -/
def ResolvesOn (U : Set X) : (m : ℕ) → {a b : ℕ} → (Fin a → Fin b → X → ℂ) → Prop
  | 0, _, _, F => ∀ i j, DifferentiableOn ℂ (F i j) U
  | m + 1, _, b, F =>
      ∃ (c : ℕ) (G : Fin b → Fin c → X → ℂ), ExactStartOn U G F ∧ ResolvesOn U m G

theorem ResolvesOn.mono {U V : Set X} (hVU : V ⊆ U) :
    ∀ (m : ℕ) {a b : ℕ} (F : Fin a → Fin b → X → ℂ), ResolvesOn U m F → ResolvesOn V m F
  | 0, _, _, _, h => fun i j => (h i j).mono hVU
  | m + 1, _, _, _, h => by
      obtain ⟨c, G, hG, hres⟩ := h
      exact ⟨c, G, hG.mono hVU, ResolvesOn.mono hVU m G hres⟩

theorem ResolvesOn.differentiableOn {U : Set X} :
    ∀ (m : ℕ) {a b : ℕ} (F : Fin a → Fin b → X → ℂ), ResolvesOn U m F →
      ∀ i j, DifferentiableOn ℂ (F i j) U
  | 0, _, _, _, h => h
  | _ + 1, _, _, _, h => by
      obtain ⟨c, G, hG, -⟩ := h
      exact hG.holF

/-- **Local free resolutions of any finite length** (Oka iterated): if `X` has Oka's property,
every finite holomorphic matrix near `x₀` has a free resolution of length `m` on an open
neighbourhood of `x₀`, exact at every point of it. -/
theorem exists_resolvesOn (hX : OkaProperty X) :
    ∀ (m : ℕ) {a b : ℕ} (F : Fin a → Fin b → X → ℂ) (x₀ : X), (∀ i j, HolAt (F i j) x₀) →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ResolvesOn U m F
  | 0, _, _, F, x₀, hF => by
      obtain ⟨V, hV, hxV, hFV⟩ := exists_open_differentiableOn hF
      exact ⟨V, hV, hxV, hFV⟩
  | m + 1, _, _, F, x₀, hF => by
      obtain ⟨U₁, hU₁, hx₁, c, G, hG⟩ := exists_exactStartOn hX F x₀ hF
      have hGx : ∀ j k, HolAt (G j k) x₀ := fun j k => holAt_of_differentiableOn hU₁ (hG.holG j k) hx₁
      obtain ⟨U₂, hU₂, hx₂, hres⟩ := exists_resolvesOn hX m G x₀ hGx
      exact ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hx₁, hx₂⟩, c, G, hG.mono inter_subset_left,
        hres.mono inter_subset_right m G⟩

/-- **Local free resolutions on `ℂⁿ`** (from Oka's coherence theorem). -/
theorem exists_resolvesOn_euclidean (n m : ℕ) {a b : ℕ}
    (F : Fin a → Fin b → EuclideanSpace ℂ (Fin n) → ℂ) (x₀ : EuclideanSpace ℂ (Fin n))
    (hF : ∀ i j, HolAt (F i j) x₀) :
    ∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ x₀ ∈ U ∧ ResolvesOn U m F :=
  exists_resolvesOn (OkaCoherence.okaProperty_euclidean n) m F x₀ hF

/-- **Exact starts on `ℂⁿ`** (from Oka's coherence theorem). -/
theorem exists_exactStartOn_euclidean (n : ℕ) {a b : ℕ}
    (F : Fin a → Fin b → EuclideanSpace ℂ (Fin n) → ℂ) (x₀ : EuclideanSpace ℂ (Fin n))
    (hF : ∀ i j, HolAt (F i j) x₀) :
    ∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ x₀ ∈ U ∧
      ∃ (c : ℕ) (G : Fin b → Fin c → EuclideanSpace ℂ (Fin n) → ℂ), ExactStartOn U G F :=
  exists_exactStartOn (OkaCoherence.okaProperty_euclidean n) F x₀ hF

end Germ

/-! ## Direct exactness over a normed algebra -/

section Direct
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **Direct exactness of a start `R^{ι₂} →g R^{ι₁} →f R^{ι₀}`** of matrices over a normed algebra
(Douady 1966, §1 and §7 Déf. 1, for the first two maps of a resolution): `f g = 0`, `im g = ker f`,
and `ker f`, `im f`, `ker g` are closed and complemented. -/
structure DirectExact (g : ι₁ → ι₂ → R) (f : ι₀ → ι₁ → R) : Prop where
  comp : ∀ i k, ∑ j, f i j * g j k = 0
  exact : ∀ x, matrixOperator f x = 0 → ∃ t, matrixOperator g t = x
  kerf : (LinearMap.ker (matrixOperator f : (ι₁ → R) →ₗ[ℂ] (ι₀ → R))).ClosedComplemented
  imf : (LinearMap.range (matrixOperator f : (ι₁ → R) →ₗ[ℂ] (ι₀ → R))).ClosedComplemented
  kerg : (LinearMap.ker (matrixOperator g : (ι₂ → R) →ₗ[ℂ] (ι₁ → R))).ClosedComplemented

omit [Fintype ι₀] in
theorem matrixOperator_comp_apply (g : ι₁ → ι₂ → R) (f : ι₀ → ι₁ → R)
    (hfg : ∀ i k, ∑ j, f i j * g j k = 0) (t : ι₂ → R) : matrixOperator f (matrixOperator g t) = 0 := by
  funext i
  simp only [matrixOperator_apply, Finset.mul_sum, Pi.zero_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hfg i k, zero_mul]

variable {g : ι₁ → ι₂ → R} {f : ι₀ → ι₁ → R}

omit [Fintype ι₀] in
/-- In a direct exact start, `im g = ker f`. -/
theorem DirectExact.range_eq_ker (h : DirectExact g f) :
    LinearMap.range (matrixOperator g : (ι₂ → R) →ₗ[ℂ] (ι₁ → R)) =
      LinearMap.ker (matrixOperator f : (ι₁ → R) →ₗ[ℂ] (ι₀ → R)) := by
  apply le_antisymm
  · rintro x ⟨t, rfl⟩
    exact matrixOperator_comp_apply g f h.comp t
  · intro x hx
    obtain ⟨t, ht⟩ := h.exact x hx
    exact ⟨t, ht⟩

variable [CompleteSpace R]

/-- `f` has a bounded generalized inverse. -/
theorem DirectExact.exists_generalizedInverse_f (h : DirectExact g f) :
    ∃ S : (ι₀ → R) →L[ℂ] (ι₁ → R), ∀ x, matrixOperator f (S (matrixOperator f x)) =
      matrixOperator f x :=
  HironakaG10FlatGeneralizedInverse.exists_generalizedInverse _ h.kerf h.imf

omit [Fintype ι₀] in
/-- `g` has a bounded generalized inverse (its image `ker f` is complemented). -/
theorem DirectExact.exists_generalizedInverse_g (h : DirectExact g f) :
    ∃ S : (ι₁ → R) →L[ℂ] (ι₂ → R), ∀ t, matrixOperator g (S (matrixOperator g t)) =
      matrixOperator g t :=
  HironakaG10FlatGeneralizedInverse.exists_generalizedInverse _ h.kerg (h.range_eq_ker ▸ h.kerf)

omit [Fintype ι₀] in
/-- **A bounded right inverse of `g` on `ker f`**: the hypothesis of Frisch's Lemme 3 (i) core. -/
theorem DirectExact.exists_rightInverse (h : DirectExact g f) :
    ∃ S : (ι₁ → R) →L[ℂ] (ι₂ → R), ∀ x, matrixOperator f x = 0 → matrixOperator g (S x) = x := by
  obtain ⟨S, hS⟩ := h.exists_generalizedInverse_g
  refine ⟨S, fun x hx => ?_⟩
  obtain ⟨t, rfl⟩ := h.exact x hx
  exact hS t

end Direct

/-! ## Restriction to `B(K)` -/

section BK
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- The `B(K)`-matrix of a matrix holomorphic on `U ⊇ K`. -/
def restrictMatrix (K : Set X) {U : Set X} (hKU : K ⊆ U) {κ ι : Type*} (F : κ → ι → X → ℂ)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) : κ → ι → holSubalgebra K :=
  fun i j => restrict K hKU (F i j) (hF i j)

omit [Fintype ι₂] [Fintype ι₀] in
theorem restrictMatrix_comp (K : Set X) {U : Set X} (hKU : K ⊆ U) {G : ι₁ → ι₂ → X → ℂ}
    {F : ι₀ → ι₁ → X → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hG : ∀ j k, DifferentiableOn ℂ (G j k) U) (hFG : ∀ i k, ∀ x ∈ U, ∑ j, F i j x * G j k x = 0)
    (i : ι₀) (k : ι₂) :
    ∑ j, restrictMatrix K hKU F hF i j * restrictMatrix K hKU G hG j k = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  have h := hFG i k z (hKU z.2)
  simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, ContinuousMap.coe_sum,
    Finset.sum_apply, ContinuousMap.mul_apply, ZeroMemClass.coe_zero, ContinuousMap.zero_apply]
  exact h

/-- **`K` is privileged for the exact start `(G, F)` on `U ⊇ K`**: the `B(K)`-complex is direct
exact (Douady 1966, §7 Déf. 1, for the first two maps of a resolution). -/
def DirectExactStartOn (K : Set X) [CompactSpace K] (U : Set X) (G : ι₁ → ι₂ → X → ℂ) (F : ι₀ → ι₁ → X → ℂ) :
    Prop :=
  ∃ (hKU : K ⊆ U) (h : ExactStartOn U G F),
    DirectExact (restrictMatrix K hKU G h.holG) (restrictMatrix K hKU F h.holF)

end BK

/-! ## The Koszul step applies to direct exact starts -/

section Koszul
open HironakaG10FlatPolydiscQuotient HironakaG10FlatPolydiscKoszul HironakaG10FlatKoszulDivision
  HironakaG10FlatPolydiscPushforward HironakaG10FlatPolydiscRemainderMap
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  {K' : Set P} [CompactSpace K'] {ρ : ℝ} {b : ℕ} {A : ℕ → P → ℂ} {U : Set P}
  [CompactSpace (K' ×ˢ Metric.closedBall (0 : ℂ) ρ)]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **Douady §7 Prop. 5 Cor. for a direct exact start**: the Koszul total complex of a Weierstrass
polynomial `W` on the pulled-back start is exact in the middle with complemented kernels and image
(`HironakaG10FlatPolydiscKoszulBase.koszul_directExact_of_base`). -/
theorem DirectExact.koszul (H : WeierstrassHyp K' ρ b A U) {g₀ : ι₁ → ι₂ → holSubalgebra K'}
    {f₀ : ι₀ → ι₁ → holSubalgebra K'} (h : DirectExact g₀ f₀) :
    (∀ z, koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) z = 0 →
      ∃ w, koszulD₂ (divData H ι₁) (matrixOperator (pullMatrix ρ g₀))
        (matrixOperator (pullMatrix ρ f₀)) w = z) ∧
    (LinearMap.ker (koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)) →ₗ[ℂ] (ι₀ → BK K' ρ))).ClosedComplemented ∧
    (LinearMap.range (koszulD₁ (divData H ι₀) (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)) →ₗ[ℂ] (ι₀ → BK K' ρ))).ClosedComplemented ∧
    (LinearMap.ker (koszulD₂ (divData H ι₁) (matrixOperator (pullMatrix ρ g₀))
      (matrixOperator (pullMatrix ρ f₀)) :
      ((ι₂ → BK K' ρ) × (ι₁ → BK K' ρ)) →ₗ[ℂ] ((ι₁ → BK K' ρ) × (ι₀ → BK K' ρ)))).ClosedComplemented :=
  HironakaG10FlatPolydiscKoszulBase.koszul_directExact_of_base H g₀ f₀ h.comp h.exact h.kerf h.imf
    h.kerg

end Koszul

end
end Hironaka.HironakaG10FlatResolutionStart
