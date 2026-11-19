import Hironaka.Resolution.HironakaG10FlatGermChain
import Hironaka.Resolution.HironakaG10FlatKoszulSplit
import Hironaka.Resolution.HironakaG10FlatResolutionPkg

/-! # Germ exactness of the Koszul chain of a coordinate on a pulled-back resolution

Douady 1966, §7 n° 2 (Prop. 5 Cor., sheaf level): let `e` be a free resolution of a coherent sheaf
`𝓖` on `U₀ ⊆ P` (exact in every degree), `π : ℂ × P → P` the projection and `w` the coordinate of `ℂ`.
The Koszul chain of `w` on `π^* e` (`[π^*e_k  w; 0  −π^*e_{k−1}]`, the matrices of
`HironakaG10FlatKoszulSplit.kosMat`) is exact on `ℂ × U₀` in every degree; it resolves `i_* 𝓖`.

* Algebra over a commutative ring (`kosA`): the Koszul chain composes to zero (`kosA_comp`); it is
  exact in every degree if `w` is a unit (`kosA_exact_unit`, cone of an isomorphism), or if `e` is
  exact in every degree and `w` is a non-zero-divisor on `coker e₀` (`kosA_exact`).
* At the points `(0, z)`: `π^*e` is exact (`exact_pull`, Nakayama:
  `HironakaG10FlatRelationLift.isCombinationAt_of_slice_generates`) and `w` is regular on
  `coker π^*e₀` (`regularAt_pull`); at the points `(w, z)`, `w ≠ 0`, the germ of `w` is a unit.
* **`exactStartOn_kosChain`**: the holomorphic Koszul chain `kosChain` is an exact start on
  `ℂ × U₀` in every degree.
BP: hironaka-g10-flat-koszul-exact.tex. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Matrix
namespace Hironaka.HironakaG10FlatKoszulExact
noncomputable section
open OkaRelationSheaf OkaGermBridge HironakaG10FlatResolutionStart HironakaG10FlatGermChain
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatFrischHolomorphicFlattener HironakaG10FlatKoszulSplit
  HironakaG10FlatSliceResolution HironakaG10FlatRelationLift Matrix

/-! ## The Koszul chain over a commutative ring -/

section Alg
variable {S : Type*} [CommRing S] {r : ℕ → ℕ}

/-- The middle block `w · 1`. -/
def kosMidA (w : S) (k : ℕ) : Matrix (Fin (r k)) (Fin (shiftRank r (k + 1))) S :=
  fun i l => if l.val = i.val then w else 0

/-- The lower block `−e_{k−1}`. -/
def kosLowA (e : (k : ℕ) → Matrix (Fin (r k)) (Fin (r (k + 1))) S) :
    (k : ℕ) → Matrix (Fin (shiftRank r k)) (Fin (shiftRank r (k + 1))) S
  | 0 => fun i => i.elim0
  | j + 1 => -e j

/-- **The Koszul chain** `[e_k  w; 0  −e_{k−1}]` of `w` on `e`. -/
def kosA (e : (k : ℕ) → Matrix (Fin (r k)) (Fin (r (k + 1))) S) (w : S) (k : ℕ) :
    Matrix (Fin (r k) ⊕ Fin (shiftRank r k)) (Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1))) S :=
  fromBlocks (e k) (kosMidA w k) 0 (kosLowA e k)

variable {e : (k : ℕ) → Matrix (Fin (r k)) (Fin (r (k + 1))) S} {w : S}

/-- A vector indexed by `Fin (shiftRank r (k+1))`, read as indexed by `Fin (r k)`. -/
def toR {k : ℕ} (y : Fin (shiftRank r (k + 1)) → S) : Fin (r k) → S := y

/-- A vector indexed by `Fin (r k)`, read as indexed by `Fin (shiftRank r (k+1))`. -/
def ofR {k : ℕ} (y : Fin (r k) → S) : Fin (shiftRank r (k + 1)) → S := y

theorem kosMidA_mulVec (k : ℕ) (y : Fin (shiftRank r (k + 1)) → S) :
    kosMidA (r := r) w k *ᵥ y = w • toR y := by
  funext i
  simp only [mulVec, dotProduct, kosMidA]
  rw [Finset.sum_eq_single (⟨i.val, i.isLt⟩ : Fin (shiftRank r (k + 1)))]
  · rw [if_pos rfl]
    rfl
  · intro l _ hl
    rw [if_neg (fun h => hl (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem kosA_mulVec (k : ℕ) (v : Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1)) → S) :
    kosA e w k *ᵥ v = Sum.elim (e k *ᵥ (v ∘ Sum.inl) + w • toR (v ∘ Sum.inr))
      (kosLowA e k *ᵥ (v ∘ Sum.inr)) := by
  rw [kosA, fromBlocks_mulVec, zero_mulVec, zero_add, kosMidA_mulVec]

/-- The Koszul chain composes to zero. -/
theorem kosA_comp (hc : ∀ k, e k * e (k + 1) = 0) : ∀ k, kosA e w k * kosA e w (k + 1) = 0 := by
  intro k
  rw [kosA, kosA, fromBlocks_multiply, hc k]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hmid : e k * kosMidA (r := r) w (k + 1) + kosMidA w k * kosLowA e (k + 1) = 0 := by
    ext i l
    show ∑ m, e k i m * kosMidA (r := r) w (k + 1) m l +
      ∑ m, kosMidA (r := r) w k i m * kosLowA e (k + 1) m l = 0
    rw [Finset.sum_eq_single (⟨l.val, l.isLt⟩ : Fin (r (k + 1))),
      Finset.sum_eq_single (⟨i.val, i.isLt⟩ : Fin (shiftRank r (k + 1)))]
    · show e k i l * (if l.val = l.val then w else 0) +
        (if i.val = i.val then w else 0) * (-(e k i l)) = 0
      rw [if_pos rfl, if_pos rfl]
      ring
    · intro m _ hm
      show (if m.val = i.val then w else 0) * _ = 0
      rw [if_neg (fun h => hm (Fin.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro m _ hm
      show e k i m * (if l.val = m.val then w else 0) = 0
      rw [if_neg (fun h => hm (Fin.ext h.symm)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hlow : kosLowA e k * kosLowA e (k + 1) = 0 := by
    cases k with
    | zero => ext i; exact i.elim0
    | succ j =>
      show (-e j) * (-e (j + 1)) = 0
      rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hc j]
  rw [hmid, hlow, fromBlocks_zero]

/-- **If `w` is a unit, the Koszul chain is exact in every degree** (cone of an isomorphism). -/
theorem kosA_exact_unit (hw : IsUnit w) : ∀ k, MatExact (kosA e w (k + 1)) (kosA e w k) := by
  intro k v hv
  obtain ⟨u, rfl⟩ := hw
  rw [kosA_mulVec] at hv
  have h1 : e k *ᵥ (v ∘ Sum.inl) + (u : S) • toR (v ∘ Sum.inr) = 0 := by
    simpa using congrArg (· ∘ Sum.inl) hv
  refine ⟨Sum.elim 0 (ofR ((↑u⁻¹ : S) • (v ∘ Sum.inl))), ?_⟩
  rw [kosA_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, zero_add]
  conv_rhs => rw [← Sum.elim_comp_inl_inr v]
  congr 1
  · show (u : S) • ((↑u⁻¹ : S) • (v ∘ Sum.inl)) = v ∘ Sum.inl
    rw [smul_smul, Units.mul_inv, one_smul]
  · show -e k *ᵥ ((↑u⁻¹ : S) • (v ∘ Sum.inl)) = toR (v ∘ Sum.inr)
    rw [neg_mulVec, mulVec_smul, eq_neg_of_add_eq_zero_left h1, smul_neg, neg_neg, smul_smul,
      Units.inv_mul, one_smul]

/-- **If `e` is exact and `w` is a non-zero-divisor on `coker e₀`, the Koszul chain is exact in
every degree.** -/
theorem kosA_exact (hP : ∀ k, MatExact (e (k + 1)) (e k))
    (hreg : ∀ y : Fin (r 0) → S, (∃ x, e 0 *ᵥ x = w • y) → ∃ y', e 0 *ᵥ y' = y) :
    ∀ k, MatExact (kosA e w (k + 1)) (kosA e w k) := by
  intro k v hv
  rw [kosA_mulVec] at hv
  have h1 : e k *ᵥ (v ∘ Sum.inl) + w • toR (v ∘ Sum.inr) = 0 := by
    simpa using congrArg (· ∘ Sum.inl) hv
  have h2 : kosLowA e k *ᵥ (v ∘ Sum.inr) = 0 := by
    simpa using congrArg (· ∘ Sum.inr) hv
  -- `y = e_k y'`
  obtain ⟨y', hy'⟩ : ∃ y' : Fin (r (k + 1)) → S, e k *ᵥ y' = toR (v ∘ Sum.inr) := by
    cases k with
    | zero =>
      refine hreg _ ⟨-(v ∘ Sum.inl), ?_⟩
      rw [mulVec_neg, neg_eq_iff_eq_neg, ← sub_eq_zero, sub_neg_eq_add]
      exact h1
    | succ j =>
      exact hP j _ (by
        have : (-e j) *ᵥ (v ∘ Sum.inr) = 0 := h2
        rwa [neg_mulVec, neg_eq_zero] at this)
  -- `x + w y' = e_{k+1} x'`
  obtain ⟨x', hx'⟩ := hP k (v ∘ Sum.inl + w • y') (by
    rw [mulVec_add, mulVec_smul, hy']
    exact h1)
  refine ⟨Sum.elim x' (ofR (-y')), ?_⟩
  rw [kosA_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, hx']
  conv_rhs => rw [← Sum.elim_comp_inl_inr v]
  congr 1
  · show v ∘ Sum.inl + w • y' + w • (-y') = v ∘ Sum.inl
    rw [smul_neg, add_neg_cancel_right]
  · show -e k *ᵥ (-y') = toR (v ∘ Sum.inr)
    rw [neg_mulVec, mulVec_neg, neg_neg, hy']

/-- The Koszul chain commutes with ring maps. -/
theorem kosA_map {S' : Type*} [CommRing S'] (ψ : S →+* S') (k : ℕ) :
    (kosA e w k).map ψ = kosA (fun k => (e k).map ψ) (ψ w) k := by
  rw [kosA, kosA, fromBlocks_map, Matrix.map_zero ψ (map_zero ψ)]
  congr 1
  · ext i l
    simp only [kosMidA, Matrix.map_apply]
    split_ifs <;> simp
  · cases k with
    | zero => ext i; exact i.elim0
    | succ j =>
      show (-e j).map ψ = -(e j).map ψ
      exact Matrix.map_neg ψ (map_neg ψ) _

end Alg

/-! ## Regularity of `w` and exactness of `π^* e` at the points of `w = 0` -/

section Pull
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The pull-back `(w, z) ↦ F(z)` of a matrix of functions on `P`. -/
def pullMat {κ ι : Type*} (F : κ → ι → P → ℂ) : κ → ι → ℂ × P → ℂ := fun i j x => F i j x.2

theorem holAt_pull {f : P → ℂ} {z : P} (hf : HolAt f z) (w₀ : ℂ) : HolAt (fun x : ℂ × P => f x.2) (w₀, z) :=
  hf.comp (f := f) (φ := Prod.snd) (y := (w₀, z)) continuous_snd fun _ => differentiableAt_snd

theorem differentiableOn_pullMat {κ ι : Type*} {U₀ : Set P} {F : κ → ι → P → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U₀) (i : κ) (j : ι) :
    DifferentiableOn ℂ (pullMat F i j) (univ ×ˢ U₀) :=
  (hF i j).comp differentiableOn_snd fun _ hx => hx.2

variable {ι₂ ι₁ ι₀ : Type} [Fintype ι₂] [Fintype ι₁] [Fintype ι₀]

/-- **`w` is regular on `coker π^* e₀` at the points of `w = 0`** (exactness of `e` at `E₁`). -/
theorem regularAt_pull {U₀ : Set P} (hU₀ : IsOpen U₀) {G : ι₁ → ι₂ → P → ℂ} {F : ι₀ → ι₁ → P → ℂ}
    (h : ExactStartOn U₀ G F) {z : P} (hz : z ∈ U₀) :
    RegularAt (pullMat F) (fun x => x.1) ((0 : ℂ), z) := by
  set y : ℂ × P := ((0 : ℂ), z) with hy
  have hFy : ∀ i j, HolAt (pullMat F i j) y := fun i j =>
    holAt_pull (holAt_of_differentiableOn hU₀ (h.holF i j) hz) 0
  have hGy : ∀ j k, HolAt (pullMat G j k) y := fun j k =>
    holAt_pull (holAt_of_differentiableOn hU₀ (h.holG j k) hz) 0
  have hUy : ∀ᶠ x in 𝓝 y, x.2 ∈ U₀ :=
    (continuous_snd.continuousAt.tendsto (x := y)).eventually (hU₀.mem_nhds hz)
  intro c hc ⟨a, ha, hac⟩
  -- the restriction of `a` to `w = 0` is a relation of `F`
  have hb : IsRelationAt F z (fun j z' => a j ((0 : ℂ), z')) := by
    refine ⟨fun j => HolAt.comp_zero_prod (ha j), fun i => ?_⟩
    filter_upwards [(tendsto_zero_prod z).eventually (hac i)] with z' hz'
    have h0 : (0 : ℂ) * c i ((0 : ℂ), z') = ∑ j, a j ((0 : ℂ), z') * F i j z' := hz'
    rw [zero_mul] at h0
    exact h0.symm
  obtain ⟨β, hβ, hβa⟩ := h.exact z hz _ hb
  -- `a − π^*(G β)` vanishes on `w = 0`
  have hdiv : ∀ j, ∃ s : ℂ × P → ℂ, HolAt s y ∧
      ∀ᶠ x in 𝓝 y, a j x - ∑ k, β k x.2 * G j k x.2 = x.1 * s x := by
    intro j
    refine exists_eq_fst_mul ((ha j).sub (HolAt.fintype_sum fun k =>
      (holAt_pull (hβ k) 0).mul (hGy j k))) rfl ?_
    filter_upwards [hβa j] with z' hz'
    show a j ((0 : ℂ), z') - ∑ k, β k z' * G j k z' = 0
    rw [hz', sub_eq_zero]
    rfl
  choose s hs hsa using hdiv
  refine ⟨s, hs, fun i => ?_⟩
  -- `w (c − F s) = 0`
  have hzero : ∀ᶠ x in 𝓝 y, x.1 * (c i x - ∑ j, s j x * F i j x.2) = 0 := by
    filter_upwards [hac i, eventually_all.2 hsa, hUy] with x hx hsx hxU
    have hx' : x.1 * c i x = ∑ j, a j x * F i j x.2 := hx
    calc x.1 * (c i x - ∑ j, s j x * F i j x.2)
        = ∑ j, a j x * F i j x.2 - ∑ j, (x.1 * s j x) * F i j x.2 := by
          rw [mul_sub, hx', Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, (∑ k, β k x.2 * G j k x.2) * F i j x.2 := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by rw [← hsx j]; ring
      _ = ∑ k, β k x.2 * ∑ j, F i j x.2 * G j k x.2 := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := Finset.sum_eq_zero fun k _ => by rw [h.comp i k x.2 hxU, mul_zero]
  have hcz := nonZeroDivisorAt_fst y _ ((hc i).sub (HolAt.fintype_sum fun j => (hs j).mul (hFy i j)))
    hzero
  filter_upwards [hcz] with x hx
  rw [sub_eq_zero] at hx
  exact hx

/-- **`π^* e` is exact at the points of `w = 0`** (Nakayama). -/
theorem exact_pull (hX : OkaProperty (ℂ × P)) {U₀ : Set P} (hU₀ : IsOpen U₀) {G : ι₁ → ι₂ → P → ℂ}
    {F : ι₀ → ι₁ → P → ℂ} (h : ExactStartOn U₀ G F) {z : P} (hz : z ∈ U₀)
    (a : ι₁ → ℂ × P → ℂ) (ha : IsRelationAt (pullMat F) ((0 : ℂ), z) a) :
    IsCombinationAt (columns (pullMat G)) ((0 : ℂ), z) a := by
  have hUy : ∀ᶠ x in 𝓝 ((0 : ℂ), z), x.2 ∈ U₀ :=
    (continuous_snd.continuousAt.tendsto (x := ((0 : ℂ), z))).eventually (hU₀.mem_nhds hz)
  refine isCombinationAt_of_slice_generates hX
    (fun i j => holAt_pull (holAt_of_differentiableOn hU₀ (h.holF i j) hz) 0)
    (fun k => ⟨fun j => holAt_pull (holAt_of_differentiableOn hU₀ (h.holG j k) hz) 0, fun i => ?_⟩)
    (fun b hb => h.exact z hz b hb) a ha
  filter_upwards [hUy] with x hx
  rw [← h.comp i k x.2 hx]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Regularity, translated to the ring of germs. -/
theorem regular_germ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {F : ι₀ → ι₁ → X → ℂ}
    {φ : X → ℂ} {y : X} (hF : ∀ i j, HolAt (F i j) y) (hφ : HolAt φ y) (h : RegularAt F φ y) :
    ∀ c : ι₀ → HolGerm X, (∃ a, germMat y F *ᵥ a = germAt y φ • c) → ∃ a', germMat y F *ᵥ a' = c := by
  rintro c ⟨a, ha⟩
  choose c' hc' hcc' using fun i => exists_germAt_eq (c i) y
  have hcv : c = germVec y c' := funext fun i => (hcc' i).symm
  have hφc : germAt y φ • germVec y c' = germVec y (fun i x => φ x * c' i x) :=
    funext fun i => (germAt_mul hφ (hc' i)).symm
  rw [hcv, hφc] at ha
  have := h c' hc' ((isCombinationAt_columns_iff_germ hF fun i => hφ.mul (hc' i)).2 ⟨a, ha⟩)
  rw [hcv]
  exact (isCombinationAt_columns_iff_germ hF hc').1 this

end Pull

/-! ## The holomorphic Koszul chain on `ℂ × U₀` -/

section Chain
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {U₀ : Set P} {r : ℕ → ℕ}

/-- The pulled-back chain over `holOn (ℂ × U₀)`. -/
def kosData (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (k : ℕ) :
    Matrix (Fin (r k)) (Fin (r (k + 1))) (holOn ((univ : Set ℂ) ×ˢ U₀)) :=
  liftMat (pullMat (e k)) (differentiableOn_pullMat (he k))

/-- The coordinate `w` as an element of `holOn (ℂ × U₀)`. -/
def wHol (U₀ : Set P) : holOn ((univ : Set ℂ) ×ˢ U₀) :=
  ⟨fun x => x.1, differentiableOn_fst⟩

/-- **The holomorphic Koszul chain** of `w` on `π^* e`. -/
def kosChain (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (k : ℕ) :
    Fin (r k) ⊕ Fin (shiftRank r k) → Fin (r (k + 1)) ⊕ Fin (shiftRank r (k + 1)) → ℂ × P → ℂ :=
  fun i j => (kosA (kosData e he) (wHol U₀) k i j).1

theorem kosChain_hol (e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ)
    (he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀) (k : ℕ) (i) (j) :
    DifferentiableOn ℂ (kosChain e he k i j) ((univ : Set ℂ) ×ˢ U₀) :=
  (kosA (kosData e he) (wHol U₀) k i j).2

/-- **The Koszul chain of `w` on `π^* e` is exact on `ℂ × U₀` in every degree**, if `e` is exact on
`U₀` in every degree (`ℂ × P` with Oka's property). -/
theorem exactStartOn_kosChain (hX : OkaProperty (ℂ × P)) (hU₀ : IsOpen U₀)
    {e : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → P → ℂ} (hex : ∀ k, ExactStartOn U₀ (e (k + 1)) (e k)) :
    ∀ k, ExactStartOn ((univ : Set ℂ) ×ˢ U₀) (kosChain e (fun k => (hex k).holF) (k + 1))
      (kosChain e (fun k => (hex k).holF) k) := by
  intro k
  set he : ∀ k i j, DifferentiableOn ℂ (e k i j) U₀ := fun k => (hex k).holF
  have hU : IsOpen ((univ : Set ℂ) ×ˢ U₀) := isOpen_univ.prod hU₀
  refine exactStartOn_of_matExact hU (kosChain_hol e he k) (kosChain_hol e he (k + 1))
    (fun i l x hx => ?_) (fun y hy => ?_)
  · -- composition, from the values at `x`
    have hc : ∀ k, (kosData e he k).map (evalHom _ x) * (kosData e he (k + 1)).map (evalHom _ x) = 0 :=
      fun k => by
        ext i l
        simp only [Matrix.mul_apply, Matrix.map_apply, evalHom_apply, kosData, liftMat_apply,
          Matrix.zero_apply]
        exact (hex k).comp i l x.2 hx.2
    have := congrFun (congrFun (kosA_comp (w := evalHom _ x (wHol U₀)) hc k) i) l
    rw [← kosA_map, ← kosA_map, ← Matrix.map_mul] at this
    exact (holOn_mul_apply _ _ i l x).symm.trans this
  · -- exactness over the germs at `y`
    have hg : ∀ k, (kosA (kosData e he) (wHol U₀) k).map (germAt hU y hy) =
        germMat y (kosChain e he k) := fun k => (map_germAt_liftMat hU hy _ (kosChain_hol e he k))
    have hm : ∀ k, (kosA (kosData e he) (wHol U₀) k).map (germAt hU y hy) =
        kosA (fun k => (kosData e he k).map (germAt hU y hy)) (germAt hU y hy (wHol U₀)) k :=
      fun k => kosA_map _ k
    rw [← hg, ← hg, hm, hm]
    by_cases hy1 : y.1 = 0
    · -- `y = (0, z)`
      obtain ⟨y1, z⟩ := y
      simp only at hy1
      subst hy1
      have hz : z ∈ U₀ := hy.2
      have hdata : ∀ k, (kosData e he k).map (germAt hU ((0 : ℂ), z) hy) =
          germMat ((0 : ℂ), z) (pullMat (e k)) := fun k => map_germAt_liftMat hU hy _ _
      refine kosA_exact (fun k => ?_) ?_ k
      · rw [hdata, hdata]
        exact (exact_iff_matExact
          (fun i j => holAt_pull (holAt_of_differentiableOn hU₀ (he k i j) hz) 0)
          (fun i j => holAt_pull (holAt_of_differentiableOn hU₀ (he (k + 1) i j) hz) 0)).1
          (exact_pull hX hU₀ (hex k) hz)
      · rw [hdata, germAt_holOn hU hy]
        exact regular_germ (fun i j => holAt_pull (holAt_of_differentiableOn hU₀ (he 0 i j) hz) 0)
          (holAt_of_differentiableOn isOpen_univ differentiableOn_fst (mem_univ _))
          (regularAt_pull hU₀ (hex 0) hz)
    · -- `w(y) ≠ 0`: the germ of `w` is a unit
      refine kosA_exact_unit ?_ k
      rw [HolGerm.isUnit_iff_eval_ne_zero, HironakaG10FlatFrischHolomorphicFlattener.eval_germAt]
      exact hy1

end Chain

end
end Hironaka.HironakaG10FlatKoszulExact
