import Hironaka.Analytic.Unibranch.HironakaG10FrMinorTest

/-!
# Route G: constructibility of the acyclicity locus from generic flatness (step G6, fixed fibre point)

Plan item G10FR-2.G6 (`work/hironaka-run0081-20261117/G10FR/frisch-constructibility.md` §4.2), with
G10FR-2.G3 (constructible germs of sets in `ℂᵐ`) and G10FR-2.G4 (well-founded induction on germs of
analytic sets). Setting of Frisch, *Points de platitude…*, Invent. Math. 4 (1967), §III: a parameter set
`P ⊆ ℂᵐ` (analytic near `p₀`, reduced structure), a fibre space `W`, and a complex `(u, v)` of holomorphic
matrices over `P × W` near `(p₀, y₀)`. **`isConstructibleNear_fibreExact`**: the set of parameters
`p ∈ P` at which the fibre complex `(u(p,·), v(p,·))` is exact at `y₀` is constructible near `p₀` —
Frisch's conclusion of Prop. (III,6) + Lemme (IV,5), at a fixed fibre point — from two explicit hypotheses:

* `hstart`: relative exact starts exist over every `P` analytic near `p₀` (Cartan's coherence of the ideal
  of `P × W` and Oka; plan item G10FR-2.G0);
* `hGF`: **generic flatness at a fixed fibre point** (Frisch Th. (II,1) (i)+(ii) and the local criterion):
  for a relative exact start `(G, A)` over `P` there is an analytic `P'' ⊆ P`, nowhere dense in `P` near `p₀`,
  outside which the fibre start is exact at `y₀` (plan item G10FR-2.G5).

Proof (route G): with starts `G_v` of `v` and `G_v'` of `G_v` and `u = G_v X`, off the exceptional set
`P''` of `hGF` the minor test (`HironakaG10FrMinorTest.fibreExactAt_iff_exists_minor_ne_zero`) says the
exact locus is the complement of the common zero set of the maximal minors of `[X | G_v']`; on `P''` the same
matrices form a complex over `P''` and the induction (on the vanishing ideal of the germ of `P` at `p₀`, in
the noetherian ring of germs) applies.

Lane G10FR, run 0081. Blueprint: `hironaka-g10fr-route-g.tex`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Matrix

namespace Hironaka.Analytic.Unibranch.HironakaG10FrRouteG

open Hironaka Hironaka
open OkaRelationSheaf OkaGermBridge HolGerm HironakaG10FlatResolutionStart
  HironakaG10LocSheafExact HironakaG10LocFibreOpen HironakaG10LocRelative
  Hironaka.Analytic.Unibranch.HironakaG10FrMinorTest

noncomputable section

variable {m : ℕ}

/-! ## Holomorphic zero sets and constructible germs in `ℂᵐ` (G3) -/

/-- `A ∩ N` is the common zero set in `N` of finitely many functions holomorphic on `N`. -/
def IsHolZeroSetOn (N A : Set (ComplexModel m)) : Prop :=
  ∃ (r : ℕ) (g : Fin r → ComplexModel m → ℂ), (∀ i, DifferentiableOn ℂ (g i) N) ∧
    A ∩ N = {p | p ∈ N ∧ ∀ i, g i p = 0}

/-- `P` is analytic near `p₀`. -/
def IsAnalyticNear (P : Set (ComplexModel m)) (p₀ : ComplexModel m) : Prop :=
  ∃ N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P

/-- `E` is constructible near `p₀` (Frisch Rem. (IV,2) normal form on a neighbourhood). -/
def IsConstructibleNear (E : Set (ComplexModel m)) (p₀ : ComplexModel m) : Prop :=
  ∃ N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧
    ∃ Q : Finset (Set (ComplexModel m) × Set (ComplexModel m)),
      (∀ q ∈ Q, IsHolZeroSetOn N q.1 ∧ IsHolZeroSetOn N q.2) ∧
        E ∩ N = (⋃ q ∈ Q, q.1 \ q.2) ∩ N

theorem IsHolZeroSetOn.mono {N N' A : Set (ComplexModel m)} (h : IsHolZeroSetOn N A)
    (hN : N' ⊆ N) : IsHolZeroSetOn N' A := by
  obtain ⟨r, g, hg, hA⟩ := h
  refine ⟨r, g, fun i => (hg i).mono hN, ?_⟩
  ext p
  have hp := Set.ext_iff.mp hA p
  simp only [mem_inter_iff, mem_ofPred_eq] at hp ⊢
  constructor
  · rintro ⟨hpA, hpN'⟩
    exact ⟨hpN', (hp.mp ⟨hpA, hN hpN'⟩).2⟩
  · rintro ⟨hpN', hg0⟩
    exact ⟨(hp.mpr ⟨hN hpN', hg0⟩).1, hpN'⟩

theorem isHolZeroSetOn_univ (N : Set (ComplexModel m)) : IsHolZeroSetOn N univ :=
  ⟨0, Fin.elim0, fun i => i.elim0, by ext p; simp⟩

theorem IsHolZeroSetOn.union {N A B : Set (ComplexModel m)} (hA : IsHolZeroSetOn N A)
    (hB : IsHolZeroSetOn N B) : IsHolZeroSetOn N (A ∪ B) := by
  obtain ⟨r, g, hg, hgA⟩ := hA
  obtain ⟨s, h, hh, hhB⟩ := hB
  refine ⟨r * s, fun k p => g (finProdFinEquiv.symm k).1 p * h (finProdFinEquiv.symm k).2 p,
    fun k => (hg _).mul (hh _), ?_⟩
  ext p
  have hA' := Set.ext_iff.mp hgA p
  have hB' := Set.ext_iff.mp hhB p
  simp only [mem_inter_iff, mem_union, mem_ofPred_eq] at hA' hB' ⊢
  constructor
  · rintro ⟨hAB, hpN⟩
    refine ⟨hpN, fun k => ?_⟩
    rcases hAB with hpA | hpB
    · rw [(hA'.mp ⟨hpA, hpN⟩).2 _, zero_mul]
    · rw [(hB'.mp ⟨hpB, hpN⟩).2 _, mul_zero]
  · rintro ⟨hpN, h0⟩
    refine ⟨?_, hpN⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hnA, hnB⟩ := hcon
    have hi : ∃ i, g i p ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hnA (hA'.mpr ⟨hpN, h'⟩).1
    have hj : ∃ j, h j p ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hnB (hB'.mpr ⟨hpN, h'⟩).1
    obtain ⟨i, hi⟩ := hi
    obtain ⟨j, hj⟩ := hj
    have := h0 (finProdFinEquiv (i, j))
    simp only [Equiv.symm_apply_apply] at this
    exact mul_ne_zero hi hj this

/-- Off a holomorphic zero set, an open subset of the domain stays open. -/
theorem IsHolZeroSetOn.isOpen_sdiff {N A U : Set (ComplexModel m)} (hA : IsHolZeroSetOn N A)
    (hU : IsOpen U) (hUN : U ⊆ N) : IsOpen (U \ A) := by
  obtain ⟨r, g, hg, hgA⟩ := hA
  have heq : U \ A = ⋃ i, U ∩ g i ⁻¹' {0}ᶜ := by
    ext p
    have hp := Set.ext_iff.mp hgA p
    simp only [mem_inter_iff, mem_ofPred_eq] at hp
    simp only [Set.mem_sdiff, mem_iUnion, mem_inter_iff, mem_preimage, mem_compl_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨hpU, hpA⟩
      by_contra hcon
      push Not at hcon
      exact hpA (hp.mpr ⟨hUN hpU, fun i => hcon i hpU⟩).1
    · rintro ⟨i, hpU, hi⟩
      exact ⟨hpU, fun hpA => hi ((hp.mp ⟨hpA, hUN hpU⟩).2 i)⟩
  rw [heq]
  exact isOpen_iUnion fun i =>
    ((hg i).mono hUN).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton

namespace IsConstructibleNear

variable {E F : Set (ComplexModel m)} {p₀ : ComplexModel m}

theorem union (hE : IsConstructibleNear E p₀) (hF : IsConstructibleNear F p₀) :
    IsConstructibleNear (E ∪ F) p₀ := by
  classical
  obtain ⟨N, hN, hpN, Q, hQ, hEQ⟩ := hE
  obtain ⟨N', hN', hpN', Q', hQ', hFQ⟩ := hF
  refine ⟨N ∩ N', hN.inter hN', ⟨hpN, hpN'⟩, Q ∪ Q', fun q hq => ?_, ?_⟩
  · rcases Finset.mem_union.mp hq with h | h
    · exact ⟨(hQ q h).1.mono inter_subset_left, (hQ q h).2.mono inter_subset_left⟩
    · exact ⟨(hQ' q h).1.mono inter_subset_right, (hQ' q h).2.mono inter_subset_right⟩
  · ext p
    have h1 := Set.ext_iff.mp hEQ p
    have h2 := Set.ext_iff.mp hFQ p
    simp only [Finset.set_biUnion_union, mem_inter_iff, mem_union] at h1 h2 ⊢
    tauto

/-- A set with an explicit local normal form `(A \ B) ∩ N` is constructible near `p₀`. -/
theorem of_sdiff {N A B : Set (ComplexModel m)} (hN : IsOpen N) (hpN : p₀ ∈ N)
    (hA : IsHolZeroSetOn N A) (hB : IsHolZeroSetOn N B) (hE : E ∩ N = (A \ B) ∩ N) :
    IsConstructibleNear E p₀ := by
  classical
  refine ⟨N, hN, hpN, {(A, B)}, fun q hq => ?_, ?_⟩
  · rw [Finset.mem_singleton] at hq
    subst hq
    exact ⟨hA, hB⟩
  · simpa using hE

/-- A set empty near `p₀` is constructible near `p₀`. -/
theorem of_inter_eq_empty {N : Set (ComplexModel m)} (hN : IsOpen N) (hpN : p₀ ∈ N)
    (hE : E ∩ N = ∅) : IsConstructibleNear E p₀ :=
  ⟨N, hN, hpN, ∅, by simp, by simpa using hE⟩

/-- Constructibility near `p₀` only depends on the set near `p₀`. -/
theorem congr {N : Set (ComplexModel m)} (h : IsConstructibleNear E p₀) (hN : IsOpen N)
    (hpN : p₀ ∈ N) (hEF : E ∩ N = F ∩ N) : IsConstructibleNear F p₀ := by
  obtain ⟨N', hN', hpN', Q, hQ, hEQ⟩ := h
  refine ⟨N ∩ N', hN.inter hN', ⟨hpN, hpN'⟩, Q,
    fun q hq => ⟨(hQ q hq).1.mono inter_subset_right, (hQ q hq).2.mono inter_subset_right⟩, ?_⟩
  ext p
  have h1 := Set.ext_iff.mp hEQ p
  have h2 := Set.ext_iff.mp hEF p
  simp only [mem_inter_iff] at h1 h2 ⊢
  tauto

end IsConstructibleNear

/-! ## The vanishing ideal of a germ of a set (G4) -/

/-- The ideal of germs at `p₀` of holomorphic functions vanishing on `P` near `p₀`. -/
def vanishingGermIdeal (P : Set (ComplexModel m)) (p₀ : ComplexModel m) :
    Ideal (HolGerm (ComplexModel m)) where
  carrier := {g | ∃ f : ComplexModel m → ℂ, HolAt f p₀ ∧ germAt p₀ f = g ∧
    ∀ᶠ z in 𝓝 p₀, z ∈ P → f z = 0}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl, hf0⟩ ⟨f', hf', rfl, hf'0⟩
    refine ⟨fun z => f z + f' z, hf.add hf', germAt_add hf hf', ?_⟩
    filter_upwards [hf0, hf'0] with z h1 h2 hz
    rw [h1 hz, h2 hz, add_zero]
  zero_mem' := ⟨fun _ => 0, holAt_const 0 p₀, germAt_zero p₀, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl, hf0⟩
    obtain ⟨f', hf', rfl⟩ := exists_germAt_eq c p₀
    refine ⟨fun z => f' z * f z, hf'.mul hf, germAt_mul hf' hf, ?_⟩
    filter_upwards [hf0] with z h hz
    rw [h hz, mul_zero]

/-- **Strict decrease of germs.** An analytic `P'' ⊆ P` whose germ at `p₀` does not contain that of `P`
has a strictly larger vanishing ideal. -/
theorem vanishingGermIdeal_lt {P P'' N : Set (ComplexModel m)} {p₀ : ComplexModel m}
    (hN : IsOpen N) (hpN : p₀ ∈ N) (hP'' : IsHolZeroSetOn N P'') (hsub : P'' ∩ N ⊆ P)
    (hstrict : ∀ N₁ ∈ 𝓝 p₀, ¬ P ∩ N₁ ⊆ P'') :
    vanishingGermIdeal P p₀ < vanishingGermIdeal P'' p₀ := by
  refine lt_of_le_of_ne ?_ ?_
  · rintro _ ⟨f, hf, rfl, hf0⟩
    refine ⟨f, hf, rfl, ?_⟩
    filter_upwards [hf0, hN.mem_nhds hpN] with z h hzN hz
    exact h (hsub ⟨hz, hzN⟩)
  · intro heq
    obtain ⟨r, g, hg, hgP⟩ := hP''
    have hvan : ∀ i, ∀ᶠ z in 𝓝 p₀, z ∈ P → g i z = 0 := by
      intro i
      have hgi : HolAt (g i) p₀ := holAt_of_differentiableOn hN (hg i) hpN
      have hmem : germAt p₀ (g i) ∈ vanishingGermIdeal P p₀ := by
        rw [heq]
        refine ⟨g i, hgi, rfl, ?_⟩
        filter_upwards [hN.mem_nhds hpN] with z hzN hz
        have : z ∈ P'' ∩ N := ⟨hz, hzN⟩
        rw [hgP] at this
        exact this.2 i
      obtain ⟨f, hf, hfg, hf0⟩ := hmem
      have heqf : f =ᶠ[𝓝 p₀] g i := (germAt_eq_germAt_iff hf hgi).mp hfg
      filter_upwards [hf0, heqf] with z h1 h2 hz
      rw [← h2]
      exact h1 hz
    have hN' : ∀ᶠ z in 𝓝 p₀, z ∈ N := hN.mem_nhds hpN
    have hall : ∀ᶠ z in 𝓝 p₀, z ∈ N ∧ (z ∈ P → ∀ i, g i z = 0) :=
      hN'.and ((eventually_all.mpr hvan).mono fun z h hz i => h i hz)
    refine hstrict _ hall ?_
    rintro z ⟨hzP, hz⟩
    have : z ∈ P'' ∩ N := by
      rw [hgP]
      exact ⟨hz.1, hz.2 hzP⟩
    exact this.1

/-! ## Slices -/

section Slice

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

omit [NormedSpace ℂ W] in
theorem eventually_slice {Q : ComplexModel m × W → Prop} {p₀ : ComplexModel m} {y₀ : W}
    (h : ∀ᶠ q in 𝓝 (p₀, y₀), Q q) : ∀ᶠ p in 𝓝 p₀, ∀ᶠ y in 𝓝 y₀, Q (p, y) := by
  rw [nhds_prod_eq] at h
  exact h.curry

theorem eventually_holAt_fib {f : ComplexModel m × W → ℂ} {p₀ : ComplexModel m} {y₀ : W}
    (hf : HolAt f (p₀, y₀)) : ∀ᶠ p in 𝓝 p₀, HolAt (fun y => f (p, y)) y₀ := by
  filter_upwards [eventually_slice hf] with p hp
  filter_upwards [hp] with y hy
  exact hy.comp y ((differentiableAt_const p).prodMk differentiableAt_id)

theorem eventually_differentiableAt_param {f : ComplexModel m × W → ℂ} {p₀ : ComplexModel m}
    {y₀ : W} (hf : HolAt f (p₀, y₀)) :
    ∀ᶠ p in 𝓝 p₀, DifferentiableAt ℂ (fun p => f (p, y₀)) p := by
  have ht : Tendsto (fun p : ComplexModel m => (p, y₀)) (𝓝 p₀) (𝓝 (p₀, y₀)) :=
    (continuous_id.prodMk continuous_const).tendsto p₀
  filter_upwards [ht.eventually hf] with p hp
  exact hp.comp p (differentiableAt_id.prodMk (differentiableAt_const y₀))

end Slice

/-- The determinant of a square matrix of holomorphic functions is holomorphic. -/
theorem differentiableOn_det {n : ℕ} (M : Fin n → Fin n → ComplexModel m → ℂ)
    {U : Set (ComplexModel m)} (hM : ∀ i j, DifferentiableOn ℂ (M i j) U) :
    DifferentiableOn ℂ (fun p => (Matrix.of fun i j => M i j p).det) U := by
  have hdet : (fun p => (Matrix.of fun i j => M i j p).det) = fun p =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ a : Fin n, M (σ a) a p := by
    funext p
    simp only [Matrix.det_apply, Matrix.of_apply]
  rw [hdet]
  have hsum : DifferentiableOn ℂ
      (∑ σ : Equiv.Perm (Fin n), fun p => Equiv.Perm.sign σ • ∏ a : Fin n, M (σ a) a p) U := by
    refine DifferentiableOn.sum (𝕜 := ℂ) (E := ComplexModel m) (F := ℂ)
      (u := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (A := fun σ p => Equiv.Perm.sign σ • ∏ a : Fin n, M (σ a) a p) fun σ _ => ?_
    exact (PureDimension.differentiableOn_finset_prod Finset.univ
      (fun a p => M (σ a) a p) U fun a _ => hM _ _).const_smul _
  refine hsum.congr fun p _ => ?_
  exact (Finset.sum_apply p Finset.univ (fun σ : Equiv.Perm (Fin n) => fun p =>
    Equiv.Perm.sign σ • ∏ a : Fin n, M (σ a) a p)).symm


/-! ## Route G: the induction (G6) -/

section Main

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Two closed nowhere dense pieces have a nowhere dense union. -/
theorem nowhereDense_union {P P₁ P₂ N₁ N₂ : Set (ComplexModel m)} (hP₁z : IsHolZeroSetOn N₁ P₁)
    (hP₁nd : ∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N₁ → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P₁)
    (hP₂nd : ∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N₂ → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P₂) :
    ∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N₁ ∩ N₂ → (U ∩ P).Nonempty →
      ¬ U ∩ P ⊆ P₁ ∪ P₂ := by
  intro U hU hUN hne hsub
  have hU' : IsOpen (U \ P₁) := hP₁z.isOpen_sdiff hU (hUN.trans inter_subset_left)
  by_cases h' : ((U \ P₁) ∩ P).Nonempty
  · apply hP₂nd (U \ P₁) hU' (fun z hz => (hUN hz.1).2) h'
    rintro z ⟨⟨hzU, hz1⟩, hzP⟩
    rcases hsub ⟨hzU, hzP⟩ with h | h
    · exact absurd h hz1
    · exact h
  · apply hP₁nd U hU (hUN.trans inter_subset_left) hne
    rintro z ⟨hzU, hzP⟩
    by_contra hz1
    exact h' ⟨z, ⟨hzU, hz1⟩, hzP⟩

/-- **Route G (Frisch (III,6)+(IV,5) at a fixed fibre point, from generic flatness).** For a complex
`(u, v)` of holomorphic matrices over `P × W` near `(p₀, y₀)`, with `P` analytic near `p₀`, the parameters
`p ∈ P` at which the fibre complex is exact at `y₀` form a set constructible near `p₀`. Inputs: existence of
relative exact starts (`hstart`, G0) and generic flatness at a fixed fibre point (`hGF`, Frisch Th. (II,1)). -/
theorem isConstructibleNear_fibreExact (y₀ : W) (p₀ : ComplexModel m)
    (hstart : ∀ P : Set (ComplexModel m), IsAnalyticNear P p₀ → ∀ {a b : ℕ}
      (A : Fin a → Fin b → ComplexModel m × W → ℂ), (∀ i j, HolAt (A i j) (p₀, y₀)) →
      ∃ (c : ℕ) (G : Fin b → Fin c → ComplexModel m × W → ℂ) (Wn : Set (ComplexModel m × W)),
        IsOpen Wn ∧ (p₀, y₀) ∈ Wn ∧ RelExactStartOn P Wn G A)
    (hGF : ∀ P : Set (ComplexModel m), IsAnalyticNear P p₀ → p₀ ∈ P → ∀ {a b c : ℕ}
      (A : Fin a → Fin b → ComplexModel m × W → ℂ) (G : Fin b → Fin c → ComplexModel m × W → ℂ)
      (Wn : Set (ComplexModel m × W)), IsOpen Wn → (p₀, y₀) ∈ Wn → RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p y₀)
    {a b n : ℕ} (u : Fin b → Fin n → ComplexModel m × W → ℂ)
    (v : Fin a → Fin b → ComplexModel m × W → ℂ)
    (hu : ∀ j l, HolAt (u j l) (p₀, y₀)) (hv : ∀ i j, HolAt (v i j) (p₀, y₀))
    (P : Set (ComplexModel m)) (hP : IsAnalyticNear P p₀)
    (hcomp : ∀ᶠ q in 𝓝 (p₀, y₀), q.1 ∈ P → ∀ i l, ∑ j, v i j q * u j l q = 0) :
    IsConstructibleNear {s | s ∈ P ∧ FibreExactAt u v s y₀} p₀ := by
  have := isNoetherianRing_holGerm_euclidean m
  suffices H : ∀ J : Ideal (HolGerm (ComplexModel m)), ∀ P : Set (ComplexModel m),
      vanishingGermIdeal P p₀ = J → IsAnalyticNear P p₀ →
      (∀ᶠ q in 𝓝 (p₀, y₀), q.1 ∈ P → ∀ i l, ∑ j, v i j q * u j l q = 0) →
      IsConstructibleNear {s | s ∈ P ∧ FibreExactAt u v s y₀} p₀ from
    H _ P rfl hP hcomp
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
  intro P hJ hPan hcomp
  obtain ⟨NP, hNP, hpNP, hPz⟩ := hPan
  by_cases hp₀ : p₀ ∉ P
  · refine IsConstructibleNear.of_inter_eq_empty (hPz.isOpen_sdiff hNP subset_rfl) ⟨hpNP, hp₀⟩ ?_
    ext s
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨hsP, -⟩, -, hsP'⟩
    exact hsP' hsP
  push Not at hp₀
  have hPan : IsAnalyticNear P p₀ := ⟨NP, hNP, hpNP, hPz⟩
  -- relative exact starts of `v` and of `G_v`
  obtain ⟨c, Gv, W₁, hW₁, hpW₁, hS₁⟩ := hstart P hPan v hv
  have hGv : ∀ j k, HolAt (Gv j k) (p₀, y₀) := fun j k =>
    holAt_of_differentiableOn hW₁ (hS₁.holG j k) hpW₁
  obtain ⟨c', Gv', W₂, hW₂, hpW₂, hS₂⟩ := hstart P hPan Gv hGv
  have hGv' : ∀ k l, HolAt (Gv' k l) (p₀, y₀) := fun k l =>
    holAt_of_differentiableOn hW₂ (hS₂.holG k l) hpW₂
  -- `u = G_v X` over `P` near `(p₀, y₀)`
  have hcol : ∀ l, ∃ x : Fin c → ComplexModel m × W → ℂ, (∀ k, HolAt (x k) (p₀, y₀)) ∧
      ∀ j, ∀ᶠ q in 𝓝 (p₀, y₀), q.1 ∈ P → u j l q = ∑ k, x k q * Gv j k q := by
    intro l
    refine hS₁.exact (p₀, y₀) hpW₁ hp₀ (fun j => u j l) (fun j => hu j l) fun i => ?_
    filter_upwards [hcomp] with q hq hqP
    rw [← hq hqP i l]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  choose x hx hxu using hcol
  set X : Fin c → Fin n → ComplexModel m × W → ℂ := fun k l => x l k with hXdef
  -- generic flatness for the two starts
  obtain ⟨P₁, N₁, hN₁, hpN₁, hP₁z, hP₁P, hP₁nd, hP₁flat⟩ := hGF P hPan hp₀ v Gv W₁ hW₁ hpW₁ hS₁
  obtain ⟨P₂, N₂, hN₂, hpN₂, hP₂z, hP₂P, hP₂nd, hP₂flat⟩ := hGF P hPan hp₀ Gv Gv' W₂ hW₂ hpW₂ hS₂
  have hN'' : IsOpen (N₁ ∩ N₂) := hN₁.inter hN₂
  have hpN'' : p₀ ∈ N₁ ∩ N₂ := ⟨hpN₁, hpN₂⟩
  have hP''z : IsHolZeroSetOn (N₁ ∩ N₂) (P₁ ∪ P₂) :=
    (hP₁z.mono inter_subset_left).union (hP₂z.mono inter_subset_right)
  have hP''P : (P₁ ∪ P₂) ∩ (N₁ ∩ N₂) ⊆ P := by
    rintro z ⟨hz | hz, hz1, hz2⟩
    · exact hP₁P ⟨hz, hz1⟩
    · exact hP₂P ⟨hz, hz2⟩
  have hP''nd := nowhereDense_union hP₁z hP₁nd hP₂nd
  have hstrict : ∀ N' ∈ 𝓝 p₀, ¬ P ∩ N' ⊆ P₁ ∪ P₂ := by
    intro N' hN' hsub
    obtain ⟨U, hUN', hU, hpU⟩ := mem_nhds_iff.mp hN'
    refine hP''nd (U ∩ (N₁ ∩ N₂)) (hU.inter hN'') inter_subset_right
      ⟨p₀, ⟨hpU, hpN''⟩, hp₀⟩ ?_
    rintro z ⟨⟨hzU, -⟩, hzP⟩
    exact hsub ⟨hzP, hUN' hzU⟩
  have hlt : J < vanishingGermIdeal (P₁ ∪ P₂) p₀ :=
    hJ ▸ vanishingGermIdeal_lt hN'' hpN'' hP''z hP''P hstrict
  -- the induction hypothesis on the exceptional set
  have hE'' := ih _ hlt (P₁ ∪ P₂) rfl ⟨N₁ ∩ N₂, hN'', hpN'', hP''z⟩ (by
    have hN''ev : ∀ᶠ q : ComplexModel m × W in 𝓝 (p₀, y₀), q.1 ∈ N₁ ∩ N₂ :=
      (continuous_fst.tendsto (p₀, y₀)).eventually (hN''.mem_nhds hpN'')
    filter_upwards [hcomp, hN''ev] with q hq hqN hqP
    exact hq (hP''P ⟨hqP, hqN⟩))
  -- the generic part: all fibre hypotheses of the minor test near `p₀`
  have hW₁ev := eventually_slice (hW₁.mem_nhds hpW₁)
  have hW₂ev := eventually_slice (hW₂.mem_nhds hpW₂)
  have hgen : ∀ᶠ p in 𝓝 p₀,
      (∀ i j, HolAt (fib v p i j) y₀) ∧ (∀ j k, HolAt (fib Gv p j k) y₀) ∧
      (∀ k l, HolAt (fib Gv' p k l) y₀) ∧ (∀ k l, HolAt (fib X p k l) y₀) ∧
      (∀ j l, HolAt (fib u p j l) y₀) ∧
      (p ∈ P → ∀ i k, ∀ᶠ z in 𝓝 y₀, ∑ j, v i j (p, z) * Gv j k (p, z) = 0) ∧
      (p ∈ P → ∀ j l, ∀ᶠ z in 𝓝 y₀, ∑ k, Gv j k (p, z) * Gv' k l (p, z) = 0) ∧
      (p ∈ P → ∀ j l, ∀ᶠ z in 𝓝 y₀, u j l (p, z) = ∑ k, Gv j k (p, z) * X k l (p, z)) ∧
      (p ∈ P → p ∉ P₁ → FibreExactAt Gv v p y₀) ∧ (p ∈ P → p ∉ P₂ → FibreExactAt Gv' Gv p y₀) ∧
      (∀ k l, DifferentiableAt ℂ (fun p => X k l (p, y₀)) p) ∧
      (∀ k l, DifferentiableAt ℂ (fun p => Gv' k l (p, y₀)) p) := by
    have e1 := eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_holAt_fib (hv i j)
    have e2 := eventually_all.mpr fun j => eventually_all.mpr fun k => eventually_holAt_fib (hGv j k)
    have e3 := eventually_all.mpr fun k => eventually_all.mpr fun l =>
      eventually_holAt_fib (hGv' k l)
    have e4 := eventually_all.mpr fun k => eventually_all.mpr fun l =>
      eventually_holAt_fib (hx l k)
    have e5 := eventually_all.mpr fun j => eventually_all.mpr fun l => eventually_holAt_fib (hu j l)
    have e8 := eventually_all.mpr fun j => eventually_all.mpr fun l => eventually_slice (hxu l j)
    have e11 := eventually_all.mpr fun k => eventually_all.mpr fun l =>
      eventually_differentiableAt_param (hx l k)
    have e12 := eventually_all.mpr fun k => eventually_all.mpr fun l =>
      eventually_differentiableAt_param (hGv' k l)
    filter_upwards [e1, e2, e3, e4, e5, e8, e11, e12, hW₁ev, hW₂ev, hP₁flat, hP₂flat]
      with p h1 h2 h3 h4 h5 h8 h11 h12 hw1 hw2 hf1 hf2
    refine ⟨h1, h2, h3, fun k l => h4 k l, h5, fun hpP i k => ?_, fun hpP j l => ?_,
      fun hpP j l => ?_, hf1, hf2, fun k l => h11 k l, h12⟩
    · filter_upwards [hw1] with z hz
      exact hS₁.comp i k (p, z) hz hpP
    · filter_upwards [hw2] with z hz
      exact hS₂.comp j l (p, z) hz hpP
    · filter_upwards [h8 j l] with z hz
      rw [hz hpP]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  obtain ⟨N₀, hN₀gen, hN₀, hpN₀⟩ := eventually_nhds_iff.mp hgen
  -- the minor functions and their common zero set
  let RC := (Fin c → Fin c) × (Fin c → Fin n ⊕ Fin c')
  let D : RC → ComplexModel m → ℂ := fun rc p =>
    (Matrix.of fun i j => Sum.elim (fun l => X (rc.1 i) l (p, y₀))
      (fun l => Gv' (rc.1 i) l (p, y₀)) (rc.2 j)).det
  let Z : Set (ComplexModel m) := {p | ∀ rc, D rc p = 0}
  have hDdiff : ∀ rc, DifferentiableOn ℂ (D rc) N₀ := by
    intro rc
    refine differentiableOn_det (fun i j p => Sum.elim (fun l => X (rc.1 i) l (p, y₀))
      (fun l => Gv' (rc.1 i) l (p, y₀)) (rc.2 j)) fun i j => ?_
    intro p hp
    rcases hrc : rc.2 j with l | l
    · simp only [Sum.elim_inl]
      exact ((hN₀gen p hp).2.2.2.2.2.2.2.2.2.2.1 (rc.1 i) l).differentiableWithinAt
    · simp only [Sum.elim_inr]
      exact ((hN₀gen p hp).2.2.2.2.2.2.2.2.2.2.2 (rc.1 i) l).differentiableWithinAt
  have hZz : IsHolZeroSetOn N₀ Z := by
    refine ⟨Fintype.card RC, fun k => D ((Fintype.equivFin RC).symm k),
      fun k => hDdiff _, ?_⟩
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, Z]
    constructor
    · rintro ⟨h, hp⟩
      exact ⟨hp, fun k => h _⟩
    · rintro ⟨hp, h⟩
      refine ⟨fun rc => ?_, hp⟩
      have := h (Fintype.equivFin RC rc)
      simpa using this
  -- the minor test on the generic part
  have hgeneric : ∀ p ∈ N₀, p ∈ P → p ∉ P₁ ∪ P₂ → (FibreExactAt u v p y₀ ↔ p ∉ Z) := by
    intro p hp hpP hpP''
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, -⟩ := hN₀gen p hp
    rw [fibreExactAt_iff_exists_minor_ne_zero v Gv Gv' X u p y₀ h1 h2 h3 h4 h5 (h6 hpP)
      (h7 hpP) (h9 hpP fun h => hpP'' (Or.inl h)) (h10 hpP fun h => hpP'' (Or.inr h)) (h8 hpP)]
    simp only [Z, mem_ofPred_eq, not_forall]
    constructor
    · rintro ⟨rows, cols, h⟩
      exact ⟨(rows, cols), h⟩
    · rintro ⟨rc, h⟩
      exact ⟨rc.1, rc.2, h⟩
  -- assemble
  set N₃ := N₀ ∩ NP ∩ (N₁ ∩ N₂) with hN₃def
  have hN₃ : IsOpen N₃ := (hN₀.inter hNP).inter hN''
  have hpN₃ : p₀ ∈ N₃ := ⟨⟨hpN₀, hpNP⟩, hpN''⟩
  have hF₁ : IsConstructibleNear (P \ ((P₁ ∪ P₂) ∪ Z)) p₀ :=
    IsConstructibleNear.of_sdiff hN₃ hpN₃ (hPz.mono fun z hz => hz.1.2)
      ((hP''z.mono fun z hz => hz.2).union (hZz.mono fun z hz => hz.1.1)) rfl
  refine (hF₁.union hE'').congr hN₃ hpN₃ ?_
  ext p
  simp only [mem_inter_iff, mem_union, Set.mem_sdiff, mem_ofPred_eq]
  constructor
  · rintro ⟨h | ⟨hp'', hex⟩, hpN⟩
    · obtain ⟨hpP, hpn⟩ := h
      push Not at hpn
      exact ⟨⟨hpP, (hgeneric p hpN.1.1 hpP fun h => h.elim hpn.1.1 hpn.1.2).mpr hpn.2⟩, hpN⟩
    · exact ⟨⟨hP''P ⟨hp'', hpN.2⟩, hex⟩, hpN⟩
  · rintro ⟨⟨hpP, hex⟩, hpN⟩
    refine ⟨?_, hpN⟩
    by_cases hp'' : p ∈ P₁ ∪ P₂
    · exact Or.inr ⟨hp'', hex⟩
    · exact Or.inl ⟨hpP, fun h => h.elim hp'' ((hgeneric p hpN.1.1 hpP hp'').mp hex)⟩

end Main

end
end Hironaka.Analytic.Unibranch.HironakaG10FrRouteG
