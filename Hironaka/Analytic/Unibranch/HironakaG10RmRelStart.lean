import Hironaka.Analytic.Unibranch.HironakaG10FrTranslate

/-!
# Relative exact starts over an analytic parameter set (route G, input G0 = `hstart`)

Run 0081 lane G10R2 (assignment G0 of lane G10FR's route G, `work/hironaka-run0081-20261117/G10FR/
frisch-constructibility.md` §7). Setting of Frisch, *Points de platitude d'un morphisme d'espaces
analytiques complexes*, Invent. Math. 4 (1967), §III: a parameter set `P ⊆ ℂᵐ`, analytic near `p₀`, and a
holomorphic matrix `A` over `ℂᵐ × ℂᵗ` near `(p₀, y₀)`.

* **`exists_relExactStartOn`**: there is a relatively exact start `RelExactStartOn P Wn G A` on an open
  neighbourhood `Wn` of `(p₀, y₀)` — exactly the hypothesis `hstart` of
  `HironakaG10FrRouteG.isConstructibleNear_fibreExact` (for `W = ℂᵗ`) and of
  `HironakaG10FrTranslate.isConstructibleNear_fibreExact_varying`.
* `isConstructibleNear_fibreExact_of_hGF`, `isConstructibleNear_fibreExact_varying_of_hGF`: the two route-G
  theorems with `hstart` discharged (only the generic-flatness hypothesis `hGF` remains).

Proof. Cartan's coherence theorem (local form in `ℂⁿ`, `CartanLocalReduction.LocalCartan`, proved as
`CartanIrreducible.irreducibleLocalCartan`), transported to `ℂᵐ × ℂᵗ`, gives finitely many holomorphic `h_l`
generating, at every point near `(p₀, y₀)`, the ideal of germs vanishing on the cylinder `P × ℂᵗ`. Oka's
theorem (`OkaCoherence.okaProperty_euclidean`, transported to `ℂᵐ × ℂᵗ`) gives generators `σ_k` of the
relations of the block matrix `[A | δ ⊗ h]` (the columns `δ_{i i'} h_l` for `(i', l)`) on a neighbourhood. A
relation `a` of `A` modulo the ideal of `P × ℂᵗ` (`∑ a_j A_ij = ∑_l d_il h_l`) is a relation `(a, -d)` of the
block matrix, hence a combination of the `σ_k`; projecting to the `A`-block gives the start `G`.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10RmRelStart

open Hironaka Hironaka
open OkaRelationSheaf OkaIdealOperations HironakaG10FlatResolutionStart HironakaG10LocRelative
  HironakaG10LocFibreOpen Hironaka.Analytic.Unibranch.HironakaG10FrRouteG

noncomputable section

/-! ### Transport of finitely generated vanishing ideals along linear equivalences -/

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] (L : E ≃L[ℂ] F)

theorem eventually_comp_iff {p : F → Prop} (y : F) :
    (∀ᶠ w in 𝓝 (L.symm y), p (L w)) ↔ ∀ᶠ v in 𝓝 y, p v := by
  have h : Filter.map L (𝓝 (L.symm y)) = 𝓝 y := by
    rw [L.map_nhds_eq, L.apply_symm_apply]
  rw [← h, eventually_map]

theorem holAt_comp_iff {g : F → ℂ} (y : F) :
    HolAt (fun w => g (L w)) (L.symm y) ↔ HolAt g y := by
  constructor
  · intro h
    have h' := HolAt.comp (φ := fun v => L.symm v) (y := y) h L.symm.continuous
      (fun _ => L.symm.differentiableAt)
    have e : ((fun w => g (L w)) ∘ fun v => L.symm v) = g := funext fun v => by simp
    rwa [e] at h'
  · intro h
    have h1 : HolAt g ((fun w => L w) (L.symm y)) := by simpa using h
    exact HolAt.comp (φ := fun w => L w) h1 L.continuous fun _ => L.differentiableAt

theorem inSpanAt_comp_iff {μ : Type*} [Fintype μ] (s : μ → E → ℂ) (g : F → ℂ) (y : F) :
    InSpanAt s (L.symm y) (fun w => g (L w)) ↔ InSpanAt (fun k v => s k (L.symm v)) y g := by
  constructor
  · rintro ⟨hg, c, hc, hgc⟩
    refine ⟨(holAt_comp_iff L y).1 hg, fun k v => c k (L.symm v), fun k => ?_, ?_⟩
    · have h1 : HolAt (fun w => (fun v => c k (L.symm v)) (L w)) (L.symm y) := by
        simpa using hc k
      exact (holAt_comp_iff L y).1 h1
    · apply (eventually_comp_iff L (p := fun v =>
        g v = ∑ k, c k (L.symm v) * s k (L.symm v)) y).1
      filter_upwards [hgc] with w hw
      simpa using hw
  · rintro ⟨hg, c, hc, hgc⟩
    refine ⟨(holAt_comp_iff L y).2 hg, fun k w => c k (L w),
      fun k => (holAt_comp_iff L y).2 (hc k), ?_⟩
    have := (eventually_comp_iff L (p := fun v => g v = ∑ k, c k v * s k (L.symm v)) y).2 hgc
    filter_upwards [this] with w hw
    simpa using hw

/-- Finite generation of a vanishing ideal is transported along a linear equivalence. -/
theorem idealFGAt_vanishingIdealF_map {A : Set F} {x₀ : F}
    (h : IdealFGAt (vanishingIdealF (L ⁻¹' A)) (L.symm x₀)) : IdealFGAt (vanishingIdealF A) x₀ := by
  obtain ⟨U, hU, h0U, μ, _, s, hsd, hsI⟩ := h
  refine ⟨L.symm ⁻¹' U, hU.preimage L.symm.continuous, h0U, μ, inferInstance,
    fun k v => s k (L.symm v), fun k => ?_, fun y hy g => ?_⟩
  · intro v hv
    exact (((hsd k).differentiableAt (hU.mem_nhds hv)).comp v
      L.symm.differentiableAt).differentiableWithinAt
  rw [← inSpanAt_comp_iff L s g y, ← hsI (L.symm y) hy]
  constructor
  · rintro ⟨hg, hgA⟩
    exact ⟨(holAt_comp_iff L y).2 hg,
      (eventually_comp_iff L (p := fun v => v ∈ A → g v = 0) y).2 hgA⟩
  · rintro ⟨hg, hgA⟩
    exact ⟨(holAt_comp_iff L y).1 hg,
      (eventually_comp_iff L (p := fun v => v ∈ A → g v = 0) y).1 hgA⟩

end Transport

/-! ### Cartan and Oka on `ℂᵐ × ℂᵗ` -/

variable {m t : ℕ}

/-- The product coordinates `ℂ^{m+t} ≅ ℂᵐ × ℂᵗ`. -/
abbrev splitL (m t : ℕ) : ComplexModel (m + t) ≃L[ℂ] ComplexModel m × ComplexModel t :=
  EuclideanSpace.finAddEquivProd

/-- **Oka's coherence theorem on `ℂᵐ × ℂᵗ`.** -/
theorem okaProperty_prodModel (m t : ℕ) : OkaProperty (ComplexModel m × ComplexModel t) :=
  OkaProperty.of_homeomorph (splitL m t).symm.toHomeomorph (fun _ => (splitL m t).symm.differentiableAt)
    (fun _ => (splitL m t).differentiableAt) (OkaCoherence.okaProperty_euclidean (m + t))

/-- **Cartan's coherence theorem for a cylinder** `{g = 0} × ℂᵗ` (local form): the ideal of germs vanishing
on it is finitely generated near every point over the domain of `g`. -/
theorem idealFGAt_vanishingIdealF_cylinder {N : Set (ComplexModel m)} (hN : IsOpen N) {r : ℕ}
    {g : Fin r → ComplexModel m → ℂ} (hg : ∀ i, DifferentiableOn ℂ (g i) N)
    {q₀ : ComplexModel m × ComplexModel t} (hq₀ : q₀.1 ∈ N) :
    IdealFGAt (vanishingIdealF {q : ComplexModel m × ComplexModel t | ∀ i, g i q.1 = 0}) q₀ := by
  set L := splitL m t
  refine idealFGAt_vanishingIdealF_map L ?_
  have hΩ : IsOpen (L ⁻¹' (N ×ˢ (univ : Set (ComplexModel t)))) :=
    (hN.prod isOpen_univ).preimage L.continuous
  have hf : ∀ i, DifferentiableOn ℂ (fun w => g i (L w).1) (L ⁻¹' (N ×ˢ univ)) := by
    intro i w hw
    have hw1 : (L w).1 ∈ N := hw.1
    exact (((hg i).differentiableAt (hN.mem_nhds hw1)).comp w
      (differentiableAt_fst.comp w L.differentiableAt)).differentiableWithinAt
  have hmem : L.symm q₀ ∈ L ⁻¹' (N ×ˢ (univ : Set (ComplexModel t))) := by
    change L (L.symm q₀) ∈ N ×ˢ univ
    rw [L.apply_symm_apply]
    exact ⟨hq₀, mem_univ _⟩
  exact CartanIrreducibleReduction.localCartan_of_irreducibleLocalCartan
    (CartanIrreducible.irreducibleLocalCartan (m + t)) _ hΩ r (fun i w => g i (L w).1) hf _ hmem

/-! ### The relative exact start -/

/-- The Kronecker coefficient. -/
private def kron {a : ℕ} (i i' : Fin a) : ℂ := if i = i' then 1 else 0

private theorem sum_kron {a : ℕ} {μ : Type*} [Fintype μ] (i : Fin a) (f : Fin a → μ → ℂ) :
    ∑ il : Fin a × μ, f il.1 il.2 * kron i il.1 = ∑ l, f i l := by
  rw [Fintype.sum_prod_type]
  simp only [kron, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- **G0 (`hstart` of route G): relative exact starts exist over an analytic parameter set.** For `P`
analytic near `p₀` and a matrix `A` holomorphic near `(p₀, y₀)`, there is a relatively exact start of `A`
over `P` on an open neighbourhood of `(p₀, y₀)`. -/
theorem exists_relExactStartOn {P : Set (ComplexModel m)} {p₀ : ComplexModel m}
    (y₀ : ComplexModel t) (hP : IsAnalyticNear P p₀) {a b : ℕ}
    (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ) (hA : ∀ i j, HolAt (A i j) (p₀, y₀)) :
    ∃ (c : ℕ) (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn ∧ (p₀, y₀) ∈ Wn ∧
        RelExactStartOn P Wn G A := by
  classical
  obtain ⟨N, hN, hp₀N, r, g, hg, hPN⟩ := hP
  have hPiff : ∀ s ∈ N, (s ∈ P ↔ ∀ i, g i s = 0) := by
    intro s hs
    have h := Set.ext_iff.mp hPN s
    simp only [mem_inter_iff, mem_ofPred_eq] at h
    exact ⟨fun hsP => (h.mp ⟨hsP, hs⟩).2, fun h0 => (h.mpr ⟨hs, h0⟩).1⟩
  set Z : Set (ComplexModel m × ComplexModel t) := {q | ∀ i, g i q.1 = 0} with hZdef
  -- Cartan's generators of the ideal of the cylinder
  obtain ⟨U, hU, hq₀U, μ, _, h, hhd, hhI⟩ :=
    idealFGAt_vanishingIdealF_cylinder (t := t) hN hg (q₀ := (p₀, y₀)) hp₀N
  have hhol : ∀ q ∈ U, ∀ l, HolAt (h l) q := fun q hq l => holAt_of_differentiableOn hU (hhd l) hq
  have hh0 : ∀ q ∈ U, q ∈ Z → ∀ l, h l q = 0 := by
    intro q hq hqZ l
    have hv := (hhI q hq (h l)).mpr (inSpanAt_self (hhol q hq) l)
    exact hv.2.self_of_nhds hqZ
  -- the block matrix `[A | δ ⊗ h]`
  let ι := Fin b ⊕ (Fin a × μ)
  let M : Fin a → ι → ComplexModel m × ComplexModel t → ℂ := fun i =>
    Sum.elim (fun j => A i j) (fun il q => kron i il.1 * h il.2 q)
  have hM : ∀ i j, HolAt (M i j) (p₀, y₀) := by
    intro i j
    rcases j with j | il
    · exact hA i j
    · exact (holAt_const _ _).mul (hhol _ hq₀U il.2)
  obtain ⟨U₂, hU₂, hq₀U₂, μ₂, _, σ, hσd, hσrel, hσgen⟩ :=
    okaProperty_prodModel m t (Fin a) ι M (p₀, y₀) hM
  obtain ⟨V, hV, hq₀V, hAV⟩ := exists_open_differentiableOn hA
  -- the start
  set c := Fintype.card μ₂ with hc
  let eμ : μ₂ ≃ Fin c := Fintype.equivFin μ₂
  let G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ := fun j k => σ (eμ.symm k) (Sum.inl j)
  have hsplit : ∀ (i : Fin a) (w : ι → ComplexModel m × ComplexModel t → ℂ)
      (q : ComplexModel m × ComplexModel t),
      ∑ j', w j' q * M i j' q =
        ∑ j, w (Sum.inl j) q * A i j q + ∑ l, w (Sum.inr (i, l)) q * h l q := by
    intro i w q
    rw [Fintype.sum_sum_type]
    congr 1
    have := sum_kron i (fun i' l => w (Sum.inr (i', l)) q * h l q)
    rw [← this]
    refine Finset.sum_congr rfl fun il _ => ?_
    simp only [M, Sum.elim_inr]
    ring
  refine ⟨c, G, U ∩ U₂ ∩ V ∩ (N ×ˢ univ),
    ((hU.inter hU₂).inter hV).inter (hN.prod isOpen_univ),
    ⟨⟨⟨hq₀U, hq₀U₂⟩, hq₀V⟩, hp₀N, mem_univ _⟩, ?_⟩
  refine ⟨fun i j => (hAV i j).mono fun q hq => hq.1.2, fun j k => (hσd _ _).mono
    fun q hq => hq.1.1.2, ?_, ?_⟩
  · -- `A G = 0` over `P`
    intro i k q hq hqP
    have hqZ : q ∈ Z := (hPiff q.1 hq.2.1).mp hqP
    have h1 := hσrel (eμ.symm k) i q hq.1.1.2
    rw [hsplit] at h1
    have h2 : ∑ l, σ (eμ.symm k) (Sum.inr (i, l)) q * h l q = 0 :=
      Finset.sum_eq_zero fun l _ => by rw [hh0 q hq.1.1.1 hqZ l, mul_zero]
    rw [h2, add_zero] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · -- relative exactness
    intro p hp hpP a' ha hrel
    have hpU : p ∈ U := hp.1.1.1
    have hpN : p.1 ∈ N := hp.2.1
    have hAp : ∀ i j, HolAt (A i j) p := fun i j => holAt_of_differentiableOn hV (hAV i j) hp.1.2
    -- the relation modulo the ideal of the cylinder
    have hspan : ∀ i, InSpanAt h p (fun q => ∑ j, a' j q * A i j q) := by
      intro i
      refine (hhI p hpU _).mp ⟨HolAt.fintype_sum fun j => (ha j).mul (hAp i j), ?_⟩
      filter_upwards [hrel i, (hN.preimage continuous_fst).mem_nhds hpN] with q hq hqN hqZ
      exact hq ((hPiff q.1 hqN).mpr hqZ)
    choose _hφ d hd hdeq using hspan
    -- the relation of the block matrix
    let w : ι → ComplexModel m × ComplexModel t → ℂ :=
      Sum.elim a' (fun il q => -d il.1 il.2 q)
    have hw : IsRelationAt M p w := by
      refine ⟨fun j' => ?_, fun i => ?_⟩
      · rcases j' with j | il
        · exact ha j
        · exact (hd il.1 il.2).neg
      · filter_upwards [hdeq i] with q hq
        rw [hsplit]
        simp only [w, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
        have hq' : ∑ j, a' j q * A i j q = ∑ l, d i l q * h l q := hq
        rw [hq', add_neg_cancel]
    obtain ⟨c', hc', hcomb⟩ := hσgen p hp.1.1.2 w hw
    refine ⟨fun k => c' (eμ.symm k), fun k => hc' _, fun j => ?_⟩
    filter_upwards [hcomb (Sum.inl j)] with q hq _
    simp only [w, Sum.elim_inl] at hq
    rw [hq]
    exact (Equiv.sum_comp eμ.symm (fun k => c' k q * σ k (Sum.inl j) q)).symm

/-! ### The route-G theorems with `hstart` discharged -/

/-- **Route G at a fixed fibre point, with G0 proved**: only the generic-flatness hypothesis `hGF` remains. -/
theorem isConstructibleNear_fibreExact_of_hGF (y₀ : ComplexModel t) (p₀ : ComplexModel m)
    (hGF : ∀ P : Set (ComplexModel m), IsAnalyticNear P p₀ → p₀ ∈ P → ∀ {a b c : ℕ}
      (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn → (p₀, y₀) ∈ Wn →
      RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ p₀ ∈ N ∧ IsHolZeroSetOn N P'' ∧ P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 p₀, p ∈ P → p ∉ P'' → FibreExactAt G A p y₀)
    {a b n : ℕ} (u : Fin b → Fin n → ComplexModel m × ComplexModel t → ℂ)
    (v : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
    (hu : ∀ j l, HolAt (u j l) (p₀, y₀)) (hv : ∀ i j, HolAt (v i j) (p₀, y₀))
    (P : Set (ComplexModel m)) (hP : IsAnalyticNear P p₀)
    (hcomp : ∀ᶠ q in 𝓝 (p₀, y₀), q.1 ∈ P → ∀ i l, ∑ j, v i j q * u j l q = 0) :
    IsConstructibleNear {s | s ∈ P ∧ FibreExactAt u v s y₀} p₀ :=
  isConstructibleNear_fibreExact y₀ p₀ (fun _ hP' {_ _} A hA => exists_relExactStartOn y₀ hP' A hA) hGF
    u v hu hv P hP hcomp

/-- **Item 2 (route G), varying fibre points, with G0 proved**: only `hGF` remains. -/
theorem isConstructibleNear_fibreExact_varying_of_hGF {d : ℕ}
    (e : ComplexModel m ≃L[ℂ] ComplexModel d × ComplexModel t)
    (T : Set (ComplexModel d)) (s₀ : ComplexModel d) (x₀ : ComplexModel t) (hT : IsAnalyticNear T s₀)
    (hGF : ∀ P : Set (ComplexModel m), IsAnalyticNear P (e.symm (s₀, x₀)) → e.symm (s₀, x₀) ∈ P →
      ∀ {a b c : ℕ} (A : Fin a → Fin b → ComplexModel m × ComplexModel t → ℂ)
      (G : Fin b → Fin c → ComplexModel m × ComplexModel t → ℂ)
      (Wn : Set (ComplexModel m × ComplexModel t)), IsOpen Wn →
      (e.symm (s₀, x₀), (0 : ComplexModel t)) ∈ Wn → RelExactStartOn P Wn G A →
      ∃ P'' N : Set (ComplexModel m), IsOpen N ∧ e.symm (s₀, x₀) ∈ N ∧ IsHolZeroSetOn N P'' ∧
        P'' ∩ N ⊆ P ∧
        (∀ U : Set (ComplexModel m), IsOpen U → U ⊆ N → (U ∩ P).Nonempty → ¬ U ∩ P ⊆ P'') ∧
        ∀ᶠ p in 𝓝 (e.symm (s₀, x₀)), p ∈ P → p ∉ P'' → FibreExactAt G A p 0)
    {a b n : ℕ} (u : Fin b → Fin n → ComplexModel d × ComplexModel t → ℂ)
    (v : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (hu : ∀ j l, HolAt (u j l) (s₀, x₀)) (hv : ∀ i j, HolAt (v i j) (s₀, x₀))
    (hcomp : ∀ᶠ q in 𝓝 (s₀, x₀), q.1 ∈ T → ∀ i l, ∑ j, v i j q * u j l q = 0) :
    IsConstructibleNear (e ⁻¹' {q | q.1 ∈ T ∧ FibreExactAt u v q.1 q.2}) (e.symm (s₀, x₀)) :=
  HironakaG10FrTranslate.isConstructibleNear_fibreExact_varying e T s₀ x₀ hT
    (fun _ hP' {_ _} A hA => exists_relExactStartOn 0 hP' A hA) hGF u v hu hv hcomp

end

end Hironaka.Analytic.Unibranch.HironakaG10RmRelStart
