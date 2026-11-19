import Hironaka.Resolution.HironakaG10FlatPrivilegedNbhd
import Hironaka.Resolution.HironakaG10FlatTriangularExtension

/-! # Split complexes of Banach spaces: privilege as a contracting homotopy

Douady 1966, §1 and §7 n° 1–2: a finite complex of Banach spaces `0 → E_m → ⋯ → E_0`
(`D k : E (k+1) → E k`) is **exact and direct** in degrees `1, …, m` iff it has a **splitting**
`t k : E k → E (k+1)` with `D (k+1) ∘ t (k+1) + t k ∘ D k = 1` on `E (k+1)` for `k < m` (`SplitBy`).
This form composes: it passes to complexes **dominated** by a split complex (chain maps `f`, `g` and a
homotopy `1 − f g = D h + h D`), which gives Douady's Prop. 2 (independence of the resolution), the
Koszul step of Prop. 5 Cor. and Prop. 3 in all degrees, and to **triangular** complexes (horseshoe
resolutions).

* `SplitBy.exact`, `SplitBy.closedComplemented_ker`, `SplitBy.closedComplemented_range`: a split complex
  is exact in degrees `1..m` with complemented kernels and images.
* `exists_splitBy`: conversely (Banach spaces), exactness + complemented kernels and images in degrees
  `< m` and `D m = 0` give a splitting (`splitOfGenInv`, built from generalized inverses).
* **`SplitBy.of_dominated`**: a complex dominated by a split complex is split (`s = f t g + h`).
* **`SplitBy.tri`**: the triangular complex `(x, y) ↦ (a x + φ y, c y)` (`a φ + φ c = 0`) of two split
  complexes is split (`triSplit`), in every degree (Douady's Prop. 3 (a), Banach core, all degrees).
* Matrices over a Banach algebra: `directExact_of_splitBy`, `exists_splitBy_of_directExact`;
  **`privilegedOn_iff_exists_splitBy`**: `K` is privileged for a finite free resolution iff its
  `B(K)`-complex is split.
BP: hironaka-g10-flat-split-complex.tex. -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaG10FlatSplitComplex
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10FlatPrivilegedNbhd
  HironakaG10FlatKoszulDivision HironakaG10FlatGeneralizedInverse HironakaG10FlatTriangularExtension

section Abstract
variable {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℂ (E k)]

/-- `t` **splits** the complex `D` in degrees `1, …, m`: `D (k+1) t (k+1) + t k D k = 1` on
`E (k+1)` for every `k < m`. -/
def SplitBy (D : (k : ℕ) → E (k + 1) →L[ℂ] E k) (t : (k : ℕ) → E k →L[ℂ] E (k + 1)) (m : ℕ) :
    Prop :=
  ∀ k < m, ∀ x, D (k + 1) (t (k + 1) x) + t k (D k x) = x

variable {D : (k : ℕ) → E (k + 1) →L[ℂ] E k} {t : (k : ℕ) → E k →L[ℂ] E (k + 1)} {m : ℕ}

/-- A split complex is exact in degrees `1, …, m`. -/
theorem SplitBy.exact (h : SplitBy D t m) {k : ℕ} (hk : k < m) {x : E (k + 1)} (hx : D k x = 0) :
    ∃ u, D (k + 1) u = x :=
  ⟨t (k + 1) x, by have := h k hk x; rwa [hx, map_zero, add_zero] at this⟩

/-- In a split complex `ker D k` is complemented (projection `D (k+1) t (k+1)`), `k < m`. -/
theorem SplitBy.closedComplemented_ker (h : SplitBy D t m)
    (hc : ∀ k < m, ∀ x, D k (D (k + 1) x) = 0) {k : ℕ} (hk : k < m) :
    (LinearMap.ker (D k : E (k + 1) →ₗ[ℂ] E k)).ClosedComplemented :=
  closedComplemented_of_proj _ ((D (k + 1)).comp (t (k + 1)))
    (fun x => LinearMap.mem_ker.mpr (hc k hk _)) fun x hx => by
      have := h k hk x
      rw [show D k x = 0 from LinearMap.mem_ker.mp hx, map_zero, add_zero] at this
      exact this

/-- In a split complex `im D k` is complemented (projection `D k t k`), `k < m`. -/
theorem SplitBy.closedComplemented_range (h : SplitBy D t m)
    (hc : ∀ k < m, ∀ x, D k (D (k + 1) x) = 0) {k : ℕ} (hk : k < m) :
    (LinearMap.range (D k : E (k + 1) →ₗ[ℂ] E k)).ClosedComplemented :=
  closedComplemented_of_proj _ ((D k).comp (t k)) (fun x => ⟨t k x, rfl⟩) fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    have := h k hk y
    show D k (t k (D k y)) = D k y
    conv_rhs => rw [← this]
    rw [map_add, hc k hk, zero_add]

/-- The splitting built from generalized inverses `S k`: `t 0 = S 0`,
`t (k+1) = S (k+1) (1 − S k D k)`. -/
def splitOfGenInv (D : (k : ℕ) → E (k + 1) →L[ℂ] E k) (S : (k : ℕ) → E k →L[ℂ] E (k + 1)) :
    (k : ℕ) → E k →L[ℂ] E (k + 1)
  | 0 => S 0
  | j + 1 => (S (j + 1)).comp (ContinuousLinearMap.id ℂ (E (j + 1)) - (S j).comp (D j))

theorem splitOfGenInv_comp (S : (k : ℕ) → E k →L[ℂ] E (k + 1))
    (hc : ∀ k < m, ∀ x, D k (D (k + 1) x) = 0) {k : ℕ} (hk : k ≤ m) (x : E (k + 1)) :
    splitOfGenInv D S k (D k x) = S k (D k x) := by
  cases k with
  | zero => rfl
  | succ j =>
      show S (j + 1) (D (j + 1) x - S j (D j (D (j + 1) x))) = _
      rw [hc j (by omega) x, map_zero, sub_zero]

/-- **Exact + direct ⇒ split** (Banach spaces): if `D m = 0` and, for `k < m`, the complex is exact at
`E (k+1)` with `ker D k`, `im D k` complemented, it has a splitting. -/
theorem exists_splitBy [∀ k, CompleteSpace (E k)] (hc : ∀ k < m, ∀ x, D k (D (k + 1) x) = 0)
    (htop : ∀ x, D m x = 0) (hex : ∀ k < m, ∀ x, D k x = 0 → ∃ u, D (k + 1) u = x)
    (hker : ∀ k < m, (LinearMap.ker (D k : E (k + 1) →ₗ[ℂ] E k)).ClosedComplemented)
    (hran : ∀ k < m, (LinearMap.range (D k : E (k + 1) →ₗ[ℂ] E k)).ClosedComplemented) :
    ∃ t : (k : ℕ) → E k →L[ℂ] E (k + 1), SplitBy D t m := by
  have hS : ∀ k, ∃ S : E k →L[ℂ] E (k + 1), k ≤ m → ∀ x, D k (S (D k x)) = D k x := by
    intro k
    by_cases hk : k < m
    · obtain ⟨S, hS⟩ := exists_generalizedInverse (D k) (hker k hk) (hran k hk)
      exact ⟨S, fun _ => hS⟩
    · refine ⟨0, fun hkm x => ?_⟩
      have hkm' : k = m := le_antisymm hkm (not_lt.mp hk)
      subst hkm'
      rw [htop, htop]
  choose S hS using hS
  refine ⟨splitOfGenInv D S, fun k hk x => ?_⟩
  rw [splitOfGenInv_comp S hc hk.le]
  -- `y = x − S k D k x` lies in `ker D k = im D (k+1)`
  have hy : D k (x - S k (D k x)) = 0 := by rw [map_sub, hS k hk.le, sub_self]
  obtain ⟨u, hu⟩ := hex k hk _ hy
  show D (k + 1) (S (k + 1) (x - S k (D k x))) + S k (D k x) = x
  rw [← hu, hS (k + 1) hk, hu, sub_add_cancel]

/-! ## Domination -/

variable {F : ℕ → Type*} [∀ k, NormedAddCommGroup (F k)] [∀ k, NormedSpace ℂ (F k)]

/-- **A complex dominated by a split complex is split.** Let `D` be split by `t` (in the form `hP`
needed on the image of `g`), `f : E → F`, `g : F → E` chain maps and `h` a homotopy
`1 − f g = D' h + h D'` on `F (k+1)`, `k < m`. Then `s k = f (k+1) t k g k + h k` splits `D'`. -/
theorem SplitBy.of_dominated {D' : (k : ℕ) → F (k + 1) →L[ℂ] F k}
    (f : (k : ℕ) → E k →L[ℂ] F k) (g : (k : ℕ) → F k →L[ℂ] E k) (h : (k : ℕ) → F k →L[ℂ] F (k + 1))
    (hf : ∀ k x, D' k (f (k + 1) x) = f k (D k x)) (hg : ∀ k y, D k (g (k + 1) y) = g k (D' k y))
    (hh : ∀ k < m, ∀ y, y - f (k + 1) (g (k + 1) y) = D' (k + 1) (h (k + 1) y) + h k (D' k y))
    (hP : ∀ k < m, ∀ y, f (k + 1) (D (k + 1) (t (k + 1) (g (k + 1) y)) + t k (D k (g (k + 1) y))) =
      f (k + 1) (g (k + 1) y)) :
    SplitBy D' (fun k => (f (k + 1)).comp ((t k).comp (g k)) + h k) m := by
  intro k hk y
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.comp_apply, map_add]
  rw [hf, ← hg]
  have e1 := hP k hk y
  rw [map_add] at e1
  have e2 := hh k hk y
  have e3 : f (k + 1) (D (k + 1) (t (k + 1) (g (k + 1) y))) + D' (k + 1) (h (k + 1) y) +
      (f (k + 1) (t k (D k (g (k + 1) y))) + h k (D' k y)) =
      (f (k + 1) (D (k + 1) (t (k + 1) (g (k + 1) y))) + f (k + 1) (t k (D k (g (k + 1) y)))) +
        (D' (k + 1) (h (k + 1) y) + h k (D' k y)) := by abel
  rw [e3, e1, ← e2]
  abel

/-- Domination by a complex split in the same degrees. -/
theorem SplitBy.of_dominated' (hs : SplitBy D t m) {D' : (k : ℕ) → F (k + 1) →L[ℂ] F k}
    (f : (k : ℕ) → E k →L[ℂ] F k) (g : (k : ℕ) → F k →L[ℂ] E k) (h : (k : ℕ) → F k →L[ℂ] F (k + 1))
    (hf : ∀ k x, D' k (f (k + 1) x) = f k (D k x)) (hg : ∀ k y, D k (g (k + 1) y) = g k (D' k y))
    (hh : ∀ k < m, ∀ y, y - f (k + 1) (g (k + 1) y) = D' (k + 1) (h (k + 1) y) + h k (D' k y)) :
    SplitBy D' (fun k => (f (k + 1)).comp ((t k).comp (g k)) + h k) m :=
  SplitBy.of_dominated f g h hf hg hh fun k hk y => by rw [hs k hk]

/-! ## Triangular complexes -/

variable {A C : ℕ → Type*} [∀ k, NormedAddCommGroup (A k)] [∀ k, NormedSpace ℂ (A k)]
  [∀ k, NormedAddCommGroup (C k)] [∀ k, NormedSpace ℂ (C k)]

/-- The splitting of a triangular complex: `(u, v) ↦ (tA u − tA φ tC v, tC v)`. -/
def triSplit {A₀ A₁ C₀ C₁ : Type*} [NormedAddCommGroup A₀] [NormedSpace ℂ A₀] [NormedAddCommGroup A₁]
    [NormedSpace ℂ A₁] [NormedAddCommGroup C₀] [NormedSpace ℂ C₀] [NormedAddCommGroup C₁]
    [NormedSpace ℂ C₁] (tA : A₀ →L[ℂ] A₁) (φ : C₁ →L[ℂ] A₀) (tC : C₀ →L[ℂ] C₁) :
    A₀ × C₀ →L[ℂ] A₁ × C₁ :=
  ((tA.comp (ContinuousLinearMap.fst ℂ A₀ C₀)) -
      tA.comp (φ.comp (tC.comp (ContinuousLinearMap.snd ℂ A₀ C₀)))).prod
    (tC.comp (ContinuousLinearMap.snd ℂ A₀ C₀))

theorem triSplit_apply {A₀ A₁ C₀ C₁ : Type*} [NormedAddCommGroup A₀] [NormedSpace ℂ A₀]
    [NormedAddCommGroup A₁] [NormedSpace ℂ A₁] [NormedAddCommGroup C₀] [NormedSpace ℂ C₀]
    [NormedAddCommGroup C₁] [NormedSpace ℂ C₁] (tA : A₀ →L[ℂ] A₁) (φ : C₁ →L[ℂ] A₀)
    (tC : C₀ →L[ℂ] C₁) (z : A₀ × C₀) :
    triSplit tA φ tC z = (tA z.1 - tA (φ (tC z.2)), tC z.2) := rfl

/-- **Triangular complexes of split complexes are split** (Douady 1966, §7 Prop. 3 (a), Banach core,
all degrees): if `a` is split by `tA`, `c` by `tC` (degrees `1..m`) and `a k φ (k+1) + φ k c (k+1) = 0`,
the complex `(x, y) ↦ (a k x + φ k y, c k y)` on `A k × C k` is split by `triSplit`. -/
theorem SplitBy.tri {a : (k : ℕ) → A (k + 1) →L[ℂ] A k} {c : (k : ℕ) → C (k + 1) →L[ℂ] C k}
    {φ : (k : ℕ) → C (k + 1) →L[ℂ] A k} {tA : (k : ℕ) → A k →L[ℂ] A (k + 1)}
    {tC : (k : ℕ) → C k →L[ℂ] C (k + 1)} (hA : SplitBy a tA m) (hC : SplitBy c tC m)
    (hφ : ∀ k < m, ∀ y, a k (φ (k + 1) y) + φ k (c (k + 1) y) = 0) :
    SplitBy (fun k => triOp (a k) (φ k) (c k)) (fun k => triSplit (tA k) (φ k) (tC k)) m := by
  intro k hk ⟨x, y⟩
  simp only [triOp_apply, triSplit_apply]
  set z := φ (k + 1) (tC (k + 1) y) with hz
  have e1 : a (k + 1) (tA (k + 1) x) = x - tA k (a k x) := eq_sub_of_add_eq (hA k hk x)
  have e2 : a (k + 1) (tA (k + 1) z) = z - tA k (a k z) := eq_sub_of_add_eq (hA k hk z)
  have e4 : c (k + 1) (tC (k + 1) y) = y - tC k (c k y) := eq_sub_of_add_eq (hC k hk y)
  have e3 : a k z = -φ k (y - tC k (c k y)) := by
    rw [← e4]; exact eq_neg_of_add_eq_zero_left (hφ k hk _)
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, map_sub, map_add, e1, e2, e3, map_neg]
    abel
  · simp only [Prod.snd_add]
    exact hC k hk y

end Abstract

/-! ## Matrices over a Banach algebra -/

section Matrix
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] {r : ℕ → ℕ}
  {M : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → R} {m : ℕ}

/-- The operators of a chain of matrices. -/
abbrev chainOp (M : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → R) (k : ℕ) :
    (Fin (r (k + 1)) → R) →L[ℂ] (Fin (r k) → R) :=
  matrixOperator (M k)

theorem chainOp_comp (hcomp : ∀ k < m, ∀ i l, ∑ j, M k i j * M (k + 1) j l = 0) :
    ∀ k < m, ∀ x, chainOp M k (chainOp M (k + 1) x) = 0 :=
  fun k hk x => matrixOperator_comp_apply (M (k + 1)) (M k) (hcomp k hk) x

theorem chainOp_top (htop : r (m + 1) = 0) (x : Fin (r (m + 1)) → R) : chainOp M m x = 0 := by
  have : x = 0 := funext fun j => (Fin.cast htop j).elim0
  rw [this, map_zero]

/-- **Split ⇒ direct exact in every degree.** -/
theorem directExact_of_splitBy {t : (k : ℕ) → (Fin (r k) → R) →L[ℂ] (Fin (r (k + 1)) → R)}
    (hcomp : ∀ k < m, ∀ i l, ∑ j, M k i j * M (k + 1) j l = 0) (htop : r (m + 1) = 0)
    (h : SplitBy (chainOp M) t m) : ∀ k < m, DirectExact (M (k + 1)) (M k) := by
  have hc := chainOp_comp hcomp
  intro k hk
  refine ⟨hcomp k hk, fun x hx => h.exact hk hx, h.closedComplemented_ker hc hk,
    h.closedComplemented_range hc hk, ?_⟩
  by_cases hk1 : k + 1 < m
  · exact h.closedComplemented_ker hc hk1
  · have hkm : k + 1 = m := by omega
    subst hkm
    have : LinearMap.ker (matrixOperator (M (k + 1)) :
        (Fin (r (k + 1 + 1)) → R) →ₗ[ℂ] (Fin (r (k + 1)) → R)) = ⊤ :=
      LinearMap.ker_eq_top.mpr (LinearMap.ext fun x => chainOp_top htop x)
    rw [this]
    exact Submodule.closedComplemented_top

/-- **Direct exact in every degree ⇒ split** (Banach algebra). -/
theorem exists_splitBy_of_directExact [CompleteSpace R]
    (hcomp : ∀ k < m, ∀ i l, ∑ j, M k i j * M (k + 1) j l = 0) (htop : r (m + 1) = 0)
    (h : ∀ k < m, DirectExact (M (k + 1)) (M k)) :
    ∃ t : (k : ℕ) → (Fin (r k) → R) →L[ℂ] (Fin (r (k + 1)) → R), SplitBy (chainOp M) t m :=
  exists_splitBy (chainOp_comp hcomp) (chainOp_top htop) (fun k hk x hx => (h k hk).exact x hx)
    (fun k hk => (h k hk).kerf) (fun k hk => (h k hk).imf)

end Matrix

/-! ## Privilege as a splitting -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X} {m : ℕ} {r : ℕ → ℕ}
  {d : (k : ℕ) → Fin (r k) → Fin (r (k + 1)) → X → ℂ}

/-- The `B(K)`-matrices of a finite free resolution compose to zero in degrees `< m`. -/
theorem restrictMatrix_chain_comp (hd : FiniteResolutionOn U m d) (K : Set X) [CompactSpace K]
    (hKU : K ⊆ U) :
    ∀ k < m, ∀ i l, ∑ j, restrictMatrix K hKU (d k) (hd.hol k) i j *
      restrictMatrix K hKU (d (k + 1)) (hd.hol (k + 1)) j l = 0 :=
  fun k hk => restrictMatrix_comp K hKU (hd.hol k) (hd.hol (k + 1)) (hd.exact k hk).comp

/-- **`K` is privileged for a finite free resolution iff its `B(K)`-complex is split.** -/
theorem privilegedOn_iff_exists_splitBy (hd : FiniteResolutionOn U m d) (K : Set X) [CompactSpace K]
    (hKU : K ⊆ U) :
    PrivilegedOn K hKU m d hd.hol ↔ ∃ t : (k : ℕ) → (Fin (r k) → holSubalgebra K) →L[ℂ]
      (Fin (r (k + 1)) → holSubalgebra K),
      SplitBy (chainOp fun k => restrictMatrix K hKU (d k) (hd.hol k)) t m :=
  ⟨fun h => exists_splitBy_of_directExact (restrictMatrix_chain_comp hd K hKU) hd.top h,
    fun ⟨_, ht⟩ => directExact_of_splitBy (restrictMatrix_chain_comp hd K hKU) hd.top ht⟩

end
end Hironaka.HironakaG10FlatSplitComplex
