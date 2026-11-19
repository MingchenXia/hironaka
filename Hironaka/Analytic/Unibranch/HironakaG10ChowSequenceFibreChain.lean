import Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain

/-!
# The fibre chain of an arbitrary flattening sequence (termination from frequent decrease)

Module M1 of lane G10H's plan (`work/hironaka-resume-20261111/G10H/HIRONAKA75-GLOBAL-STEP.md` §4):
`HironakaG10ChowFibreChain` generalized from the stateless driver `stage rule s₀` to any
`HironakaG10ChowStrictTransformCalculus.FlatteningSequence` `F` (rounds `σ_n : X_{n+1} → X_n` with
strict transforms `q_n : Y_{n+1} → Y_n`, `f_{n+1}`).  Hironaka's algorithm (Hironaka 1975, §4) chooses
its centres from a state carried along the sequence (tracked local flatteners), and it proves a
strict decrease of the fibre once per round of Theorem `II_n` (Lemma 4.6.1), not at every step; the
consumer of that is `exists_flattening_of_frequentDecrease`.

* `StepFibreSurjective F n` (N6), `StepFibreDecreasesAt F n x'` (strict decrease over `x'`),
  `fibreKernel F z n` (the kernel of `𝒪_{Y_0,y} → 𝒪_{Y_n,y_n}/m_{z_n}` along `F.strict n`);
* `fibreKernel_mono`, `fibreKernel_lt` — the kernels increase, strictly at a decrease;
* `not_frequently_fibreDecreases'` — with the local Noether property of `Y_0` (lane G10P,
  `HironakaG10PNSourceNoether.hasLocalNoetherProperty`) and locally finitely generated kernels the
  fibre cannot strictly decrease infinitely often along a compatible sequence;
* `not_frequently_kernelGrowth'` — the composite form (no N6 needed);
* `exists_flattening_of_frequentDecrease` — the conclusion of `HironakaFlattening` for `F.f 0` from
  closed non-flat images, compatibility of the non-flat images, N6, coherent kernels and FREQUENT
  strict decrease along every branch of non-flat points.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowSequenceFibreChain

open Hironaka HironakaG10ChowFibreAlgebra HironakaG10PNIdealFamily
  HironakaG10ChowCompactBranch HironakaG10ChowStrictTransformCalculus HironakaG10ChowFibreChain
  HironakaG10ChowFlatteningReduction HironakaG10ChowTowerDomination HironakaG10ChowFlatBimeromorphicIso

noncomputable section

variable (F : FlatteningSequence)

/-! ### One round -/

theorem step_comm_apply (n : ℕ) (y : (F.Y (n + 1)).obj.left) :
    (F.σ n).hom.left.base ((F.f (n + 1)).hom.left.base y) =
      (F.f n).hom.left.base ((F.q n).hom.left.base y) :=
  (congrArg (fun H : F.Y (n + 1) ⟶ F.X n => H.hom.left.base y) (F.data n).strict.comm).symm

theorem map_fibreIdealAt_le (n : ℕ) (y : (F.Y (n + 1)).obj.left) :
    Ideal.map ((F.q n).hom.left.stalkMap y).hom (fibreIdealAt (F.f n) ((F.q n).hom.left.base y)) ≤
      fibreIdealAt (F.f (n + 1)) y :=
  map_lrsFibreIdeal_le_of_comm (F.f n).hom.left (F.σ n).hom.left (F.q n).hom.left
    (F.f (n + 1)).hom.left
    (congrArg (fun H : F.Y (n + 1) ⟶ F.X n => H.hom.left) (F.data n).strict.comm) y

/-- **N6 for round `n`**: the fibre algebras of `f_{n+1}` are quotients of those of `f_n`. -/
def StepFibreSurjective (n : ℕ) : Prop :=
  ∀ (y : (F.Y (n + 1)).obj.left) (b : (F.Y (n + 1)).obj.left.presheaf.stalk y),
    ∃ a : (F.Y n).obj.left.presheaf.stalk ((F.q n).hom.left.base y),
      b - ((F.q n).hom.left.stalkMap y).hom a ∈ fibreIdealAt (F.f (n + 1)) y

/-- **Strict fibre decrease over `x' ∈ X_{n+1}` in round `n`** (Hironaka (2.4.3), Lemma 3.1). -/
def StepFibreDecreasesAt (n : ℕ) (x' : (F.X (n + 1)).obj.left) : Prop :=
  ∃ y : (F.Y n).obj.left, (F.f n).hom.left.base y = (F.σ n).hom.left.base x' ∧
    ∀ y' : (F.Y (n + 1)).obj.left, (F.q n).hom.left.base y' = y →
      (F.f (n + 1)).hom.left.base y' = x' →
        ∃ h : (F.Y n).obj.left.presheaf.stalk ((F.q n).hom.left.base y'),
          h ∉ fibreIdealAt (F.f n) ((F.q n).hom.left.base y') ∧
            ((F.q n).hom.left.stalkMap y').hom h ∈ fibreIdealAt (F.f (n + 1)) y'

/-! ### The chain -/

theorem strict_succ_base (n : ℕ) (y : (F.Y (n + 1)).obj.left) :
    (F.strict (n + 1)).hom.left.base y =
      (F.strict n).hom.left.base ((F.q n).hom.left.base y) := rfl

theorem strict_zero_stalkMap (y : (F.Y 0).obj.left) (g : (F.Y 0).obj.left.presheaf.stalk y) :
    ((F.strict 0).hom.left.stalkMap y).hom g = g := by
  change ((𝟙 (F.Y 0).obj.left : _ ⟶ _).stalkMap y).hom g = g
  rw [LocallyRingedSpace.stalkMap_id]
  rfl

theorem strict_succ_stalkMap (n : ℕ) (y : (F.Y (n + 1)).obj.left)
    (g : (F.Y 0).obj.left.presheaf.stalk ((F.strict (n + 1)).hom.left.base y)) :
    ((F.strict (n + 1)).hom.left.stalkMap y).hom g =
      ((F.q n).hom.left.stalkMap y).hom
        (((F.strict n).hom.left.stalkMap ((F.q n).hom.left.base y)).hom g) :=
  congrArg (fun φ => CommRingCat.Hom.hom φ g)
    (LocallyRingedSpace.stalkMap_comp (F.q n).hom.left (F.strict n).hom.left y)

variable {F}

theorem strict_mem_fibre (z : ∀ n, (F.X n).obj.left)
    (hz : ∀ n, (F.σ n).hom.left.base (z (n + 1)) = z n) :
    ∀ n (y : (F.Y n).obj.left), (F.f n).hom.left.base y = z n →
      (F.f 0).hom.left.base ((F.strict n).hom.left.base y) = z 0
  | 0, _, hy => hy
  | n + 1, y, hy =>
    strict_mem_fibre z hz n ((F.q n).hom.left.base y)
      ((step_comm_apply F n y).symm.trans ((congrArg (F.σ n).hom.left.base hy).trans (hz n)))

theorem strict_injective :
    ∀ n (a c : (F.Y n).obj.left), (F.f n).hom.left.base a = (F.f n).hom.left.base c →
      (F.strict n).hom.left.base a = (F.strict n).hom.left.base c → a = c
  | 0, _, _, _, h => h
  | n + 1, a, c, hf, hQ => by
    have hq : (F.q n).hom.left.base a = (F.q n).hom.left.base c := by
      apply strict_injective n
      · exact (step_comm_apply F n a).symm.trans
          ((congrArg (F.σ n).hom.left.base hf).trans (step_comm_apply F n c))
      · exact hQ
    exact (F.data n).strict.pair_injective a c hf hq

theorem exists_sub_mem_chain (hsurj : ∀ n, StepFibreSurjective F n) :
    ∀ n (y : (F.Y n).obj.left) (b : (F.Y n).obj.left.presheaf.stalk y),
      ∃ a₀ : (F.Y 0).obj.left.presheaf.stalk ((F.strict n).hom.left.base y),
        b - ((F.strict n).hom.left.stalkMap y).hom a₀ ∈ fibreIdealAt (F.f n) y
  | 0, y, b => ⟨b, by rw [strict_zero_stalkMap, sub_self]; exact Ideal.zero_mem _⟩
  | n + 1, y, b => by
    obtain ⟨a, ha⟩ := hsurj n y b
    obtain ⟨a₀, ha₀⟩ := exists_sub_mem_chain hsurj n _ a
    refine ⟨a₀, ?_⟩
    rw [strict_succ_stalkMap F n y a₀, ← sub_add_sub_cancel b (((F.q n).hom.left.stalkMap y).hom a),
      ← map_sub]
    exact Ideal.add_mem _ ha (map_fibreIdealAt_le F n y (Ideal.mem_map_of_mem _ ha₀))

/-! ### The kernels on `Y_0` -/

variable (F)

/-- The kernel of `𝒪_{Y_0,y} → 𝒪_{Y_n,y_n}/m_{z_n}𝒪_{Y_n,y_n}` at the points `y_n` over `y` in the
fibre over `z_n` (the unit ideal if there is none). -/
def fibreKernel (z : ∀ n, (F.X n).obj.left) (n : ℕ) (y : (F.Y 0).obj.left) :
    Ideal ((F.Y 0).obj.left.presheaf.stalk y) :=
  ⨅ (yn : (F.Y n).obj.left) (h : (F.strict n).hom.left.base yn = y)
    (_ : (F.f n).hom.left.base yn = z n),
    Ideal.comap (((F.strict n).hom.left.stalkMap yn).hom.comp
      (eqToHom (congrArg (F.Y 0).obj.left.presheaf.stalk h.symm)).hom)
      (fibreIdealAt (F.f n) yn)

variable {F}

theorem mem_fibreKernel_iff (z : ∀ n, (F.X n).obj.left) (n : ℕ) (y : (F.Y 0).obj.left)
    (g : (F.Y 0).obj.left.presheaf.stalk y) :
    g ∈ fibreKernel F z n y ↔
      ∀ (yn : (F.Y n).obj.left) (h : (F.strict n).hom.left.base yn = y),
        (F.f n).hom.left.base yn = z n →
          ((F.strict n).hom.left.stalkMap yn).hom
            ((eqToHom (congrArg (F.Y 0).obj.left.presheaf.stalk h.symm)).hom g) ∈
            fibreIdealAt (F.f n) yn := by
  simp only [fibreKernel, Ideal.mem_iInf, Ideal.mem_comap, RingHom.comp_apply]

theorem mem_fibreKernel_at {z : ∀ n, (F.X n).obj.left} {n : ℕ} {yn : (F.Y n).obj.left}
    (hyn : (F.f n).hom.left.base yn = z n)
    {g : (F.Y 0).obj.left.presheaf.stalk ((F.strict n).hom.left.base yn)}
    (hg : g ∈ fibreKernel F z n ((F.strict n).hom.left.base yn)) :
    ((F.strict n).hom.left.stalkMap yn).hom g ∈ fibreIdealAt (F.f n) yn := by
  have h := (mem_fibreKernel_iff z n _ g).mp hg yn rfl hyn
  simpa using h

/-- **The kernels increase along a compatible sequence.** -/
theorem fibreKernel_mono (z : ∀ n, (F.X n).obj.left)
    (hz : ∀ n, (F.σ n).hom.left.base (z (n + 1)) = z n) (n : ℕ) (y : (F.Y 0).obj.left) :
    fibreKernel F z n y ≤ fibreKernel F z (n + 1) y := by
  intro g hg
  rw [mem_fibreKernel_iff]
  intro y' h hy'
  subst h
  simp only [eqToHom_refl, CommRingCat.hom_id, RingHom.id_apply]
  rw [strict_succ_stalkMap F n y' g]
  apply map_fibreIdealAt_le F n y'
  apply Ideal.mem_map_of_mem
  exact mem_fibreKernel_at ((step_comm_apply F n y').symm.trans
    ((congrArg (F.σ n).hom.left.base hy').trans (hz n))) hg

theorem isAscending_fibreKernel (z : ∀ n, (F.X n).obj.left)
    (hz : ∀ n, (F.σ n).hom.left.base (z (n + 1)) = z n) :
    IsAscending (F.Y 0).obj.left (fibreKernel F z) :=
  fun n y => fibreKernel_mono z hz n y

/-- **A strict fibre decrease makes the kernel grow strictly** at a point of `f_0⁻¹(z_0)`. -/
theorem fibreKernel_lt (hsurj : ∀ n, StepFibreSurjective F n) (z : ∀ n, (F.X n).obj.left)
    (hz : ∀ n, (F.σ n).hom.left.base (z (n + 1)) = z n) (n : ℕ)
    (hdec : StepFibreDecreasesAt F n (z (n + 1))) :
    ∃ y : (F.Y 0).obj.left, (F.f 0).hom.left.base y = z 0 ∧
      fibreKernel F z n y < fibreKernel F z (n + 1) y := by
  classical
  obtain ⟨yn, hyn, hdec⟩ := hdec
  rw [hz n] at hyn
  refine ⟨(F.strict n).hom.left.base yn, strict_mem_fibre z hz n yn hyn,
    lt_of_le_of_ne (fibreKernel_mono z hz n _) fun heq => ?_⟩
  by_cases hex : ∃ y' : (F.Y (n + 1)).obj.left,
      (F.q n).hom.left.base y' = yn ∧ (F.f (n + 1)).hom.left.base y' = z (n + 1)
  · obtain ⟨y', hy'q, hy'f⟩ := hex
    obtain ⟨h, hh, hqh⟩ := hdec y' hy'q hy'f
    subst hy'q
    obtain ⟨a₀, ha₀⟩ := exists_sub_mem_chain hsurj n _ h
    have hin : a₀ ∈ fibreKernel F z (n + 1)
        ((F.strict n).hom.left.base ((F.q n).hom.left.base y')) := by
      rw [mem_fibreKernel_iff]
      intro y'' h'' hy''
      have hqq : (F.q n).hom.left.base y'' = (F.q n).hom.left.base y' := by
        apply strict_injective n
        · exact (step_comm_apply F n y'').symm.trans
            ((congrArg (F.σ n).hom.left.base (hy''.trans hy'f.symm)).trans (step_comm_apply F n y'))
        · exact h''
      have hyy : y'' = y' :=
        (F.data n).strict.pair_injective y'' y' (hy''.trans hy'f.symm) hqq
      subst hyy
      change ((F.strict (n + 1)).hom.left.stalkMap y'').hom a₀ ∈ _
      rw [strict_succ_stalkMap F n y'' a₀]
      have h1 : ((F.strict n).hom.left.stalkMap ((F.q n).hom.left.base y'')).hom a₀ =
          h - (h - ((F.strict n).hom.left.stalkMap ((F.q n).hom.left.base y'')).hom a₀) := by abel
      rw [h1, map_sub]
      exact Ideal.sub_mem _ hqh (map_fibreIdealAt_le F n y'' (Ideal.mem_map_of_mem _ ha₀))
    rw [← heq] at hin
    apply hh
    have h1 : h = (h - ((F.strict n).hom.left.stalkMap ((F.q n).hom.left.base y')).hom a₀) +
        ((F.strict n).hom.left.stalkMap ((F.q n).hom.left.base y')).hom a₀ := by abel
    rw [h1]
    exact Ideal.add_mem _ ha₀ (mem_fibreKernel_at ((step_comm_apply F n y').symm.trans
      ((congrArg (F.σ n).hom.left.base hy'f).trans (hz n))) hin)
  · simp only [not_exists, not_and] at hex
    have htop : (1 : (F.Y 0).obj.left.presheaf.stalk ((F.strict n).hom.left.base yn)) ∈
        fibreKernel F z (n + 1) ((F.strict n).hom.left.base yn) := by
      rw [mem_fibreKernel_iff]
      intro y'' h'' hy''
      exfalso
      have hqq : (F.q n).hom.left.base y'' = yn := by
        apply strict_injective n
        · exact (step_comm_apply F n y'').symm.trans
            ((congrArg (F.σ n).hom.left.base hy'').trans ((hz n).trans hyn.symm))
        · exact h''
      exact hex y'' hqq hy''
    rw [← heq] at htop
    have h1 := mem_fibreKernel_at hyn htop
    rw [map_one] at h1
    exact lrsFibreIdeal_ne_top _ _ ((Ideal.eq_top_iff_one _).mpr h1)

/-! ### Termination -/

/-- **No strict fibre decrease infinitely often**, given the local Noether property of `Y_0`. -/
theorem not_frequently_fibreDecreases (hf : IsProperMap (F.f 0).hom.left.base)
    (hN : HasLocalNoetherProperty (F.Y 0).obj.left) (hsurj : ∀ n, StepFibreSurjective F n)
    (z : ∀ n, (F.X n).obj.left) (hz : ∀ n, (F.σ n).hom.left.base (z (n + 1)) = z n)
    (hfg : ∀ n, IsLocallyFinitelyGenerated (F.Y 0).obj.left (fibreKernel F z n)) :
    ¬ ∀ N, ∃ m, N ≤ m ∧ StepFibreDecreasesAt F m (z (m + 1)) := by
  intro hfreq
  set K : Set (F.Y 0).obj.left := (F.f 0).hom.left.base ⁻¹' {z 0} with hK
  have hKc : IsCompact K := hf.isCompact_preimage isCompact_singleton
  obtain ⟨N, W, hKW, hW⟩ := hN.exists_stationary_nhds (isAscending_fibreKernel z hz) hfg K hKc
  obtain ⟨m, hm, hdec⟩ := hfreq N
  obtain ⟨y, hy, hlt⟩ := fibreKernel_lt hsurj z hz m hdec
  have h1 := hW m hm y (hKW hy)
  have h2 := hW (m + 1) (by omega) y (hKW hy)
  rw [h1, h2] at hlt
  exact lt_irrefl _ hlt

/-- `not_frequently_fibreDecreases` with the Noether property discharged (lane G10P). -/
theorem not_frequently_fibreDecreases' (hf : IsProperMap (F.f 0).hom.left.base)
    (hsurj : ∀ n, StepFibreSurjective F n)
    (z : ∀ n, (F.X n).obj.left) (hz : ∀ n, (F.σ n).hom.left.base (z (n + 1)) = z n)
    (hfg : ∀ n, IsLocallyFinitelyGenerated (F.Y 0).obj.left (fibreKernel F z n)) :
    ¬ ∀ N, ∃ m, N ≤ m ∧ StepFibreDecreasesAt F m (z (m + 1)) :=
  not_frequently_fibreDecreases hf (HironakaG10PNSourceNoether.hasLocalNoetherProperty (F.Y 0))
    hsurj z hz hfg

/-- **Composite form** (Hironaka pp. 545–546 compares the fibres over a whole round): the kernel
family cannot change between two times infinitely often (Noether and `hfg` only; no N6). -/
theorem not_frequently_kernelGrowth' (hf : IsProperMap (F.f 0).hom.left.base)
    (z : ∀ n, (F.X n).obj.left) (hz : ∀ n, (F.σ n).hom.left.base (z (n + 1)) = z n)
    (hfg : ∀ n, IsLocallyFinitelyGenerated (F.Y 0).obj.left (fibreKernel F z n)) :
    ¬ ∀ N, ∃ m m', N ≤ m ∧ m < m' ∧ ∃ y : (F.Y 0).obj.left,
      (F.f 0).hom.left.base y = z 0 ∧ fibreKernel F z m y ≠ fibreKernel F z m' y := by
  intro hfreq
  set K : Set (F.Y 0).obj.left := (F.f 0).hom.left.base ⁻¹' {z 0} with hK
  have hKc : IsCompact K := hf.isCompact_preimage isCompact_singleton
  obtain ⟨N, W, hKW, hW⟩ := (HironakaG10PNSourceNoether.hasLocalNoetherProperty (F.Y 0)).exists_stationary_nhds
    (isAscending_fibreKernel z hz) hfg K hKc
  obtain ⟨m, m', hm, hmm', y, hy, hne⟩ := hfreq N
  exact hne ((hW m hm y (hKW hy)).trans (hW m' (by omega) y (hKW hy)).symm)

/-- **No infinite branch of non-flat points** from frequent strict decrease along every branch. -/
theorem not_isBranch_of_frequentDecrease (hf : IsProperMap (F.f 0).hom.left.base)
    (hsurj : ∀ n, StepFibreSurjective F n)
    (hfg : ∀ (z : ∀ n, (F.X n).obj.left) n,
      IsLocallyFinitelyGenerated (F.Y 0).obj.left (fibreKernel F z n))
    (hfreq : ∀ z : ∀ n, (F.X n).obj.left,
      IsBranch (fun n => (F.σ n).hom.left.base) F.nonflatImage z →
        ∀ N, ∃ m, N ≤ m ∧ StepFibreDecreasesAt F m (z (m + 1)))
    (z : ∀ n, (F.X n).obj.left) :
    ¬ IsBranch (fun n => (F.σ n).hom.left.base) F.nonflatImage z := fun hb =>
  not_frequently_fibreDecreases' hf hsurj z hb.2 (hfg z) (hfreq z hb)

/-- **Flattening from frequent decrease along every branch** (the consumer of Hironaka's
Lemma 4.6.1 + iteration, pp. 544–546). -/
theorem exists_flattening_of_frequentDecrease (hX : CompactSpace (F.X 0).obj.left)
    (hf : IsProperMap (F.f 0).hom.left.base) (hclosed : ∀ n, IsClosed (F.nonflatImage n))
    (hmaps : ∀ n, MapsTo (F.σ n).hom.left.base (F.nonflatImage (n + 1)) (F.nonflatImage n))
    (hsurj : ∀ n, StepFibreSurjective F n)
    (hfg : ∀ (z : ∀ n, (F.X n).obj.left) n,
      IsLocallyFinitelyGenerated (F.Y 0).obj.left (fibreKernel F z n))
    (hfreq : ∀ z : ∀ n, (F.X n).obj.left,
      IsBranch (fun n => (F.σ n).hom.left.base) F.nonflatImage z →
        ∀ N, ∃ m, N ≤ m ∧ StepFibreDecreasesAt F m (z (m + 1))) :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ F.X 0) (E : Set X'.obj.left),
      IsNativeBlowupTower (F.X 0) X' σ ∧ IsClosed E ∧ interior E = ∅ ∧ IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ F.Y 0),
        IsStrictTransform (F.f 0) σ E p q ∧ IsFlatMorphism p :=
  F.exists_flattening hX hf hclosed hmaps
    fun z => not_isBranch_of_frequentDecrease hf hsurj hfg hfreq z

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowSequenceFibreChain
