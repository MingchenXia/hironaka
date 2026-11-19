import Hironaka.Resolution.HironakaG10FlatRelationLift
import Hironaka.Resolution.HironakaG10FlatZeroTail

/-! # Germ-level exactness as linear algebra over the ring of germs

`ExactStartOn U G F` asks, at every point `y ∈ U`, that every germ relation of `F` be a germ
combination of the columns of `G`. This module turns that condition into **exactness of a pair of
matrices over the commutative ring `HolGerm X`** (`MatExact`), so that algebraic constructions of
resolutions (presentation changes, Koszul cones, horseshoes) can be checked by matrix algebra over an
abstract ring, and transports identities between holomorphic matrices on `U` to the rings
`HolGerm X` (germs at a point of `U`), `B(K)` (`K ⊆ U`) and `ℂ` (values at a point of `U`).

* `MatExact G F` (over any ring): `F v = 0 ⇒ v = G c`; `matExact_submatrix` (relabelling).
* `germMat y F`: the matrix of germs at `y`; `germMat_mulVec_germVec`.
* **`exact_iff_matExact`**: at a point where `F`, `G` are holomorphic, germ exactness of `(G, F)` is
  `MatExact (germMat y G) (germMat y F)`; `matExact_of_exactStartOn`, **`exactStartOn_of_matExact`**.
* `liftMat F hF`: a matrix holomorphic on `U` as a matrix over the ring `holOn U`;
  `map_germAt_liftMat` (germs), `map_restrictHom_liftMat` (`B(K)`).
* `RespectsOn U ψ`: a ring map out of `holOn U` that only sees values on `U`
  (`respectsOn_germAt`, `respectsOn_restrictHom`, `respectsOn_evalHom`); `RespectsOn.map_eq`:
  identities of holomorphic matrices on `U` become identities of matrices over the target.
BP: hironaka-g10-flat-germ-chain.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix
namespace Hironaka.HironakaG10FlatGermChain
noncomputable section
open OkaRelationSheaf OkaGermBridge HironakaG10FlatResolutionStart HironakaG10FlatRelationLift
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatFrischHolomorphicFlattener

/-! ## Exactness of a pair of matrices over a ring -/

section Alg
variable {T : Type*} [Ring T] {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁]

/-- **Exactness at the middle** of `T^{ι₂} →G T^{ι₁} →F T^{ι₀}`: every `v` with `F v = 0` is `G c`. -/
def MatExact (G : Matrix ι₁ ι₂ T) (F : Matrix ι₀ ι₁ T) : Prop :=
  ∀ v : ι₁ → T, F *ᵥ v = 0 → ∃ c : ι₂ → T, G *ᵥ c = v

/-- Exactness is invariant under relabelling the three bases. -/
theorem matExact_submatrix {κ₂ κ₁ κ₀ : Type*} [Fintype κ₂] [Fintype κ₁] {G : Matrix ι₁ ι₂ T}
    {F : Matrix ι₀ ι₁ T} (h : MatExact G F) (e₀ : κ₀ ≃ ι₀) (e₁ : κ₁ ≃ ι₁) (e₂ : κ₂ ≃ ι₂) :
    MatExact (G.submatrix e₁ e₂) (F.submatrix e₀ e₁) := by
  intro v hv
  have hv' : F *ᵥ (v ∘ e₁.symm) = 0 := by
    rw [Matrix.submatrix_mulVec_equiv] at hv
    funext i
    have := congrFun hv (e₀.symm i)
    simpa using this
  obtain ⟨c, hc⟩ := h _ hv'
  refine ⟨c ∘ e₂, ?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  funext j
  simp only [Function.comp_apply]
  have hc' : (c ∘ ⇑e₂) ∘ ⇑e₂.symm = c := funext fun x => by simp
  rw [hc', hc]
  simp

end Alg

/-! ## Germ matrices -/

section Germ
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {ι₂ ι₁ ι₀ : Type*} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- The matrix of germs at `y` of a matrix of functions. -/
def germMat {ι κ : Type*} (y : X) (F : ι → κ → X → ℂ) : Matrix ι κ (HolGerm X) :=
  Matrix.of fun i j => germAt y (F i j)

omit [Fintype ι₀] in
theorem germMat_mulVec_germVec {F : ι₀ → ι₁ → X → ℂ} {y : X} (hF : ∀ i j, HolAt (F i j) y)
    {a : ι₁ → X → ℂ} (ha : ∀ j, HolAt (a j) y) :
    germMat y F *ᵥ germVec y a = germVec y (fun i x => ∑ j, F i j x * a j x) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, germMat, Matrix.of_apply, germVec]
  rw [germAt_sum _ fun j _ => (hF i j).mul (ha j)]
  exact Finset.sum_congr rfl fun j _ => (germAt_mul (hF i j) (ha j)).symm

omit [Fintype ι₀] in
theorem isRelationAt_iff_germ {F : ι₀ → ι₁ → X → ℂ} {y : X} (hF : ∀ i j, HolAt (F i j) y)
    {a : ι₁ → X → ℂ} (ha : ∀ j, HolAt (a j) y) :
    IsRelationAt F y a ↔ germMat y F *ᵥ germVec y a = 0 := by
  rw [germMat_mulVec_germVec hF ha]
  refine ⟨fun h => funext fun i => ?_, fun h => ⟨ha, fun i => ?_⟩⟩
  · show germAt y _ = 0
    rw [germAt_eq_zero_iff (HolAt.fintype_sum fun j => (hF i j).mul (ha j))]
    filter_upwards [h.2 i] with x hx
    rw [← hx]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · have hi : germAt y (fun x => ∑ j, F i j x * a j x) = 0 := congrFun h i
    rw [germAt_eq_zero_iff (HolAt.fintype_sum fun j => (hF i j).mul (ha j))] at hi
    filter_upwards [hi] with x hx
    rw [← hx]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

omit [Fintype ι₁] in
theorem isCombinationAt_columns_iff_germ {G : ι₁ → ι₂ → X → ℂ} {y : X}
    (hG : ∀ j k, HolAt (G j k) y) {a : ι₁ → X → ℂ} (ha : ∀ j, HolAt (a j) y) :
    IsCombinationAt (columns G) y a ↔ ∃ c : ι₂ → HolGerm X, germMat y G *ᵥ c = germVec y a := by
  constructor
  · rintro ⟨c, hc, hca⟩
    refine ⟨germVec y c, ?_⟩
    rw [germMat_mulVec_germVec hG hc]
    funext j
    show germAt y _ = germAt y _
    rw [germAt_eq_germAt_iff (HolAt.fintype_sum fun k => (hG j k).mul (hc k)) (ha j)]
    filter_upwards [hca j] with x hx
    rw [hx]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rintro ⟨c, hc⟩
    choose c' hc' hcc' using fun k => exists_germAt_eq (c k) y
    have hcv : c = germVec y c' := funext fun k => (hcc' k).symm
    rw [hcv, germMat_mulVec_germVec hG hc'] at hc
    refine ⟨c', hc', fun j => ?_⟩
    have hj : germAt y (fun x => ∑ k, G j k x * c' k x) = germAt y (a j) := congrFun hc j
    rw [germAt_eq_germAt_iff (HolAt.fintype_sum fun k => (hG j k).mul (hc' k)) (ha j)] at hj
    filter_upwards [hj] with x hx
    rw [← hx]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

omit [Fintype ι₀] in
/-- **Germ exactness at `y` is exactness over the ring of germs.** -/
theorem exact_iff_matExact {G : ι₁ → ι₂ → X → ℂ} {F : ι₀ → ι₁ → X → ℂ} {y : X}
    (hF : ∀ i j, HolAt (F i j) y) (hG : ∀ j k, HolAt (G j k) y) :
    (∀ a : ι₁ → X → ℂ, IsRelationAt F y a → IsCombinationAt (columns G) y a) ↔
      MatExact (germMat y G) (germMat y F) := by
  constructor
  · intro h v hv
    choose a ha hav using fun j => exists_germAt_eq (v j) y
    have hva : v = germVec y a := funext fun j => (hav j).symm
    rw [hva] at hv ⊢
    exact (isCombinationAt_columns_iff_germ hG ha).1 (h a ((isRelationAt_iff_germ hF ha).2 hv))
  · intro h a ha
    exact (isCombinationAt_columns_iff_germ hG ha.1).2
      (h _ ((isRelationAt_iff_germ hF ha.1).1 ha))

theorem matExact_of_exactStartOn {U : Set X} (hU : IsOpen U) {G : ι₁ → ι₂ → X → ℂ}
    {F : ι₀ → ι₁ → X → ℂ} (h : ExactStartOn U G F) {y : X} (hy : y ∈ U) :
    MatExact (germMat y G) (germMat y F) :=
  (exact_iff_matExact (fun i j => holAt_of_differentiableOn hU (h.holF i j) hy)
    (fun j k => holAt_of_differentiableOn hU (h.holG j k) hy)).1 (h.exact y hy)

/-- **Exact starts from exactness over the rings of germs.** -/
theorem exactStartOn_of_matExact {U : Set X} (hU : IsOpen U) {G : ι₁ → ι₂ → X → ℂ}
    {F : ι₀ → ι₁ → X → ℂ} (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hG : ∀ j k, DifferentiableOn ℂ (G j k) U) (hcomp : ∀ i k, ∀ x ∈ U, ∑ j, F i j x * G j k x = 0)
    (hex : ∀ y ∈ U, MatExact (germMat y G) (germMat y F)) : ExactStartOn U G F :=
  ⟨hF, hG, hcomp, fun y hy => (exact_iff_matExact (fun i j => holAt_of_differentiableOn hU (hF i j) hy)
    (fun j k => holAt_of_differentiableOn hU (hG j k) hy)).2 (hex y hy)⟩

end Germ

/-! ## Matrices over `holOn U` and ring maps that only see `U` -/

section Hol
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X} {ι κ μ : Type*}

/-- A matrix holomorphic on `U`, as a matrix over the ring `holOn U`. -/
def liftMat (F : ι → κ → X → ℂ) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    Matrix ι κ (holOn U) :=
  Matrix.of fun i j => ⟨F i j, hF i j⟩

@[simp] theorem liftMat_apply (F : ι → κ → X → ℂ) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (i : ι) (j : κ) : (liftMat F hF i j : X → ℂ) = F i j := rfl

/-- The germ map of `holOn U` at `y ∈ U` agrees with `OkaGermBridge.germAt`. -/
theorem germAt_holOn (hU : IsOpen U) {y : X} (hy : y ∈ U) (f : holOn U) :
    HironakaG10FlatFrischHolomorphicFlattener.germAt hU y hy f = OkaGermBridge.germAt y f.1 := by
  rw [OkaGermBridge.germAt_of_holAt (holAt_of_differentiableOn hU f.2 hy)]
  show HolGerm.mk (fun z => f.1 (z + y)) (eventually_differentiableAt_translate hU hy f.2) = _
  exact HolGerm.mk_eq_mk_iff.2 (Eventually.of_forall fun z => by simp only [add_comm])

theorem map_germAt_liftMat (hU : IsOpen U) {y : X} (hy : y ∈ U) (F : ι → κ → X → ℂ)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    (liftMat F hF).map (HironakaG10FlatFrischHolomorphicFlattener.germAt hU y hy) = germMat y F := by
  exact Matrix.ext fun i j => germAt_holOn hU hy _

theorem map_restrictHom_liftMat (K : Set X) (hKU : K ⊆ U) (F : ι → κ → X → ℂ)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    (liftMat F hF).map (restrictHom K hKU) = restrictMatrix K hKU F hF := rfl

/-- Evaluation at `x` as a ring map out of `holOn U`. -/
def evalHom (U : Set X) (x : X) : holOn U →+* ℂ :=
  (Pi.evalRingHom (fun _ : X => ℂ) x).comp (holOn U).subtype

@[simp] theorem evalHom_apply (x : X) (f : holOn U) : evalHom U x f = f.1 x := rfl

/-- A ring map out of `holOn U` that only depends on the values on `U`. -/
def RespectsOn {T : Type*} [NonAssocSemiring T] (U : Set X) (ψ : holOn U →+* T) : Prop :=
  ∀ f g : holOn U, (∀ x ∈ U, f.1 x = g.1 x) → ψ f = ψ g

theorem respectsOn_germAt (hU : IsOpen U) {y : X} (hy : y ∈ U) :
    RespectsOn U (HironakaG10FlatFrischHolomorphicFlattener.germAt hU y hy) := by
  intro f g hfg
  rw [germAt_holOn, germAt_holOn, germAt_eq_germAt_iff (holAt_of_differentiableOn hU f.2 hy)
    (holAt_of_differentiableOn hU g.2 hy)]
  filter_upwards [hU.mem_nhds hy] with x hx
  exact hfg x hx

theorem respectsOn_restrictHom (K : Set X) (hKU : K ⊆ U) : RespectsOn U (restrictHom K hKU) := by
  intro f g hfg
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  exact hfg z (hKU z.2)

theorem respectsOn_evalHom {x : X} (hx : x ∈ U) : RespectsOn U (evalHom U x) :=
  fun _ _ hfg => hfg x hx

/-- The value of an entry of a product of matrices over `holOn U`. -/
theorem holOn_mul_apply [Fintype κ] (M : Matrix ι κ (holOn U)) (N : Matrix κ μ (holOn U)) (i : ι)
    (j : μ) (x : X) : ((M * N) i j).1 x = ∑ l, (M i l).1 x * (N l j).1 x := by
  rw [Matrix.mul_apply]
  change (∑ l, M i l * N l j : holOn U).1 x = _
  rw [show ((∑ l, M i l * N l j : holOn U) : X → ℂ) = ∑ l, ((M i l : X → ℂ) * (N l j : X → ℂ)) by
    push_cast; rfl]
  simp

/-- **Identities on `U` become identities over the target of a ring map that only sees `U`.** -/
theorem RespectsOn.map_eq {T : Type*} [NonAssocSemiring T] {ψ : holOn U →+* T} (hψ : RespectsOn U ψ)
    {M N : Matrix ι κ (holOn U)} (h : ∀ x ∈ U, ∀ i j, (M i j).1 x = (N i j).1 x) :
    M.map ψ = N.map ψ := by
  ext i j
  exact hψ _ _ fun x hx => h x hx i j

end Hol

end
end Hironaka.HironakaG10FlatGermChain
