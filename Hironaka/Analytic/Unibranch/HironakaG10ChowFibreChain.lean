import Hironaka.Analytic.Unibranch.HironakaG10ChowPairInjective
import Hironaka.Resolution.HironakaG10ChowFibreAlgebra
import Hironaka.Resolution.HironakaG10PNIdealFamily
import Hironaka.Analytic.Unibranch.HironakaG10PNSourceNoether

/-!
# No infinite branch from strict fibre decrease and the Noether property (route step (4.3))

Termination step (4.3) of the global flattening algorithm
(`work/hironaka-resume-20261111/G10C/GLOBAL-FLATTENING-ROUTE.md` §3.3a, §4; Rydh, arXiv:2501.08394,
proof of Thm. 1.1 with Lemma 1.18).  Along a compatible sequence `z_n` of base points of the stages
`f_n : Y_n → X_n` of the algorithm (`HironakaG10ChowFlatteningDriver.stage`), the fibres
`f_n⁻¹(z_n)` — with their nilpotents, i.e. the fibre ideals `m_{z_n} 𝒪_{Y_n}` — are compared inside
the first family `Y_0` through the composite strict-transform maps `chainQ n : Y_n → Y_0`:
`fibreKernel z n y` is the kernel of `𝒪_{Y_0,y} → 𝒪_{Y_n,y_n}/m_{z_n}𝒪_{Y_n,y_n}` at the (unique, by
pair-injectivity) point `y_n` over `y` in the fibre, and the unit ideal if there is none.

* `fibreKernel_mono` — the kernels increase (the fibres shrink);
* `exists_sub_mem_chain` — if every step has surjective fibre algebras (route step N6,
  `StepFibreSurjective`), so does every composite `Y_n → Y_0`;
* `fibreKernel_lt` — a step with a strict fibre decrease over `z_{n+1}` (`StepFibreDecreasesAt`, the
  conclusion of Rydh's Lemma 1.18) makes the kernel grow strictly at a point of `f_0⁻¹(z_0)`;
* `not_frequently_fibreDecreases` — with the local Noether property of `Y_0`
  (`HironakaG10PNIdealFamily.HasLocalNoetherProperty`, lane G10P) and locally finitely generated
  kernels, the fibre cannot decrease strictly infinitely often along a compatible sequence;
* `not_isBranch_of_fibreDecreases`, `exists_flattening_of_fibreDecreases` — the hypothesis `hno` of
  `HironakaG10ChowPairInjective.exists_flattening_of_rule'` from strict decrease at every non-flat
  point of the next stage;
* `not_frequently_fibreDecreases'`, `not_isBranch_of_fibreDecreases'`,
  `exists_flattening_of_fibreDecreases'` — the same with the Noether property discharged by lane G10P
  (`HironakaG10PNSourceNoether.hasLocalNoetherProperty`).

The inputs that remain explicit hypotheses: `StepFibreSurjective` (N6, the chart computation),
`StepFibreDecreasesAt` (Lemma 1.18 at points where the centre rule satisfies (RR)), local finite
generation of the kernels (coherence of the ideal of the image of a compact fibre) and the local
Noether property of `Y_0` (the last one is proved by lane G10P and discharged in the primed
versions).
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain

open Hironaka HironakaG10ChowFibreAlgebra HironakaG10PNIdealFamily
  HironakaG10ChowFlatteningDriver HironakaG10ChowOneStepStrictTransform
  HironakaG10ChowStrictFlatLocus HironakaG10ChowCompactBranch

noncomputable section

/-- The fibre ideal `m_{f y} 𝒪_{Y,y}` of a morphism of reduced complex spaces at `y`. -/
abbrev fibreIdealAt {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (y : Y.obj.left) :
    Ideal (Y.obj.left.presheaf.stalk y) :=
  lrsFibreIdeal f.hom.left y

variable (rule : ∀ s : Stage, AdmissibleCentre s.f)

/-! ### One step -/

/-- The square of one step commutes: `f' ≫ σ = q ≫ f`. -/
theorem step_comm (s : Stage) :
    (Stage.next rule s).f ≫ Stage.σ rule s = Stage.q rule s ≫ s.f := by
  let c := rule s
  let _ := c.finiteType
  exact strictP_comp c.B c.b c.dense s.f

theorem step_comm_apply (s : Stage) (y : (Stage.next rule s).Y.obj.left) :
    (Stage.σ rule s).hom.left.base ((Stage.next rule s).f.hom.left.base y) =
      s.f.hom.left.base ((Stage.q rule s).hom.left.base y) :=
  congrArg (fun H : (Stage.next rule s).Y ⟶ s.X => H.hom.left.base y) (step_comm rule s)

/-- Fibre ideals of a step map into fibre ideals of the strict transform. -/
theorem map_fibreIdealAt_le (s : Stage) (y : (Stage.next rule s).Y.obj.left) :
    Ideal.map ((Stage.q rule s).hom.left.stalkMap y).hom
        (fibreIdealAt s.f ((Stage.q rule s).hom.left.base y)) ≤
      fibreIdealAt (Stage.next rule s).f y :=
  map_lrsFibreIdeal_le_of_comm s.f.hom.left (Stage.σ rule s).hom.left (Stage.q rule s).hom.left
    (Stage.next rule s).f.hom.left
    (congrArg (fun H : (Stage.next rule s).Y ⟶ s.X => H.hom.left) (step_comm rule s)).symm y

/-- **Route step N6 for one step**: the fibre algebras of the strict transform are quotients of the
original fibre algebras (`𝒪_{Y,q y'} → 𝒪_{Y',y'}/m_{x'}𝒪_{Y',y'}` is surjective). -/
def StepFibreSurjective (s : Stage) : Prop :=
  ∀ (y : (Stage.next rule s).Y.obj.left) (b : (Stage.next rule s).Y.obj.left.presheaf.stalk y),
    ∃ a : s.Y.obj.left.presheaf.stalk ((Stage.q rule s).hom.left.base y),
      b - ((Stage.q rule s).hom.left.stalkMap y).hom a ∈ fibreIdealAt (Stage.next rule s).f y

/-- **Strict fibre decrease over `x'`** (conclusion of Rydh's Lemma 1.18): some point `y` of the
fibre over `σ x'` either has no point of the strict transform over it in the fibre over `x'`, or the
fibre-algebra map at that point is not injective. -/
def StepFibreDecreasesAt (s : Stage) (x' : (Stage.next rule s).X.obj.left) : Prop :=
  ∃ y : s.Y.obj.left, s.f.hom.left.base y = (Stage.σ rule s).hom.left.base x' ∧
    ∀ y' : (Stage.next rule s).Y.obj.left, (Stage.q rule s).hom.left.base y' = y →
      (Stage.next rule s).f.hom.left.base y' = x' →
        ∃ h : s.Y.obj.left.presheaf.stalk ((Stage.q rule s).hom.left.base y'),
          h ∉ fibreIdealAt s.f ((Stage.q rule s).hom.left.base y') ∧
            ((Stage.q rule s).hom.left.stalkMap y').hom h ∈ fibreIdealAt (Stage.next rule s).f y'

/-! ### The chain of stages -/

variable (s₀ : Stage)

/-- The composite strict-transform map `Y_n → Y_0`. -/
def chainQ : ∀ n, (stage rule s₀ n).Y ⟶ (stage rule s₀ 0).Y
  | 0 => 𝟙 _
  | n + 1 => Stage.q rule (stage rule s₀ n) ≫ chainQ n

theorem chainQ_succ_base (n : ℕ) (y : (stage rule s₀ (n + 1)).Y.obj.left) :
    (chainQ rule s₀ (n + 1)).hom.left.base y =
      (chainQ rule s₀ n).hom.left.base ((Stage.q rule (stage rule s₀ n)).hom.left.base y) := rfl

theorem chainQ_zero_stalkMap (y : (stage rule s₀ 0).Y.obj.left)
    (g : (stage rule s₀ 0).Y.obj.left.presheaf.stalk y) :
    ((chainQ rule s₀ 0).hom.left.stalkMap y).hom g = g := by
  change ((𝟙 (stage rule s₀ 0).Y.obj.left : _ ⟶ _).stalkMap y).hom g = g
  rw [LocallyRingedSpace.stalkMap_id]
  rfl

theorem chainQ_succ_stalkMap (n : ℕ) (y : (stage rule s₀ (n + 1)).Y.obj.left)
    (g : (stage rule s₀ 0).Y.obj.left.presheaf.stalk ((chainQ rule s₀ (n + 1)).hom.left.base y)) :
    ((chainQ rule s₀ (n + 1)).hom.left.stalkMap y).hom g =
      ((Stage.q rule (stage rule s₀ n)).hom.left.stalkMap y).hom
        (((chainQ rule s₀ n).hom.left.stalkMap
          ((Stage.q rule (stage rule s₀ n)).hom.left.base y)).hom g) := by
  exact congrArg (fun φ => CommRingCat.Hom.hom φ g)
    (LocallyRingedSpace.stalkMap_comp (Stage.q rule (stage rule s₀ n)).hom.left
      (chainQ rule s₀ n).hom.left y)

variable {rule s₀}

/-- Points over a compatible sequence lie over `z 0`. -/
theorem chainQ_mem_fibre (z : ∀ n, (stage rule s₀ n).X.obj.left)
    (hz : ∀ n, (Stage.σ rule (stage rule s₀ n)).hom.left.base (z (n + 1)) = z n) :
    ∀ n (y : (stage rule s₀ n).Y.obj.left), (stage rule s₀ n).f.hom.left.base y = z n →
      (stage rule s₀ 0).f.hom.left.base ((chainQ rule s₀ n).hom.left.base y) = z 0
  | 0, _, hy => hy
  | n + 1, y, hy =>
    chainQ_mem_fibre z hz n ((Stage.q rule (stage rule s₀ n)).hom.left.base y)
      ((step_comm_apply rule (stage rule s₀ n) y).symm.trans
        ((congrArg (Stage.σ rule (stage rule s₀ n)).hom.left.base hy).trans (hz n)))

/-- **The composite maps are injective on every fibre** (pair-injectivity of each step). -/
theorem chainQ_injective :
    ∀ n (a c : (stage rule s₀ n).Y.obj.left),
      (stage rule s₀ n).f.hom.left.base a = (stage rule s₀ n).f.hom.left.base c →
        (chainQ rule s₀ n).hom.left.base a = (chainQ rule s₀ n).hom.left.base c → a = c
  | 0, _, _, _, h => h
  | n + 1, a, c, hf, hQ => by
    have hq : (Stage.q rule (stage rule s₀ n)).hom.left.base a =
        (Stage.q rule (stage rule s₀ n)).hom.left.base c := by
      apply chainQ_injective n
      · exact (step_comm_apply rule (stage rule s₀ n) a).symm.trans
          ((congrArg (Stage.σ rule (stage rule s₀ n)).hom.left.base hf).trans
            (step_comm_apply rule (stage rule s₀ n) c))
      · exact hQ
    exact HironakaG10ChowPairInjective.stage_pairInjective rule (stage rule s₀ n) a c hf hq

/-- **Fibre algebras along the chain** (route step N6 iterated): if every step has surjective fibre
algebras, every germ on `Y_n` is congruent modulo `m_{z_n}` to a germ pulled back from `Y_0`. -/
theorem exists_sub_mem_chain (hsurj : ∀ n, StepFibreSurjective rule (stage rule s₀ n)) :
    ∀ n (y : (stage rule s₀ n).Y.obj.left) (b : (stage rule s₀ n).Y.obj.left.presheaf.stalk y),
      ∃ a₀ : (stage rule s₀ 0).Y.obj.left.presheaf.stalk ((chainQ rule s₀ n).hom.left.base y),
        b - ((chainQ rule s₀ n).hom.left.stalkMap y).hom a₀ ∈ fibreIdealAt (stage rule s₀ n).f y
  | 0, y, b => ⟨b, by rw [chainQ_zero_stalkMap, sub_self]; exact Ideal.zero_mem _⟩
  | n + 1, y, b => by
    obtain ⟨a, ha⟩ := hsurj n y b
    obtain ⟨a₀, ha₀⟩ := exists_sub_mem_chain hsurj n _ a
    refine ⟨a₀, ?_⟩
    rw [chainQ_succ_stalkMap rule s₀ n y a₀]
    let b' : (Stage.next rule (stage rule s₀ n)).Y.obj.left.presheaf.stalk y := b
    show b' - ((Stage.q rule (stage rule s₀ n)).hom.left.stalkMap y).hom
        (((chainQ rule s₀ n).hom.left.stalkMap
          ((Stage.q rule (stage rule s₀ n)).hom.left.base y)).hom a₀) ∈
      fibreIdealAt (Stage.next rule (stage rule s₀ n)).f y
    rw [← sub_add_sub_cancel b' (((Stage.q rule (stage rule s₀ n)).hom.left.stalkMap y).hom a),
      ← map_sub]
    exact Ideal.add_mem _ ha (map_fibreIdealAt_le rule _ y (Ideal.mem_map_of_mem _ ha₀))

/-! ### The kernels on `Y_0` -/

variable (rule s₀)

/-- The kernel of `𝒪_{Y_0,y} → 𝒪_{Y_n,y_n}/m_{z_n}𝒪_{Y_n,y_n}` at the points `y_n` over `y` in the
fibre over `z_n` (the unit ideal if there is none): the ideal of the image of the fibre
`f_n⁻¹(z_n)` in `Y_0`, nilpotents kept. -/
def fibreKernel (z : ∀ n, (stage rule s₀ n).X.obj.left) (n : ℕ)
    (y : (stage rule s₀ 0).Y.obj.left) : Ideal ((stage rule s₀ 0).Y.obj.left.presheaf.stalk y) :=
  ⨅ (yn : (stage rule s₀ n).Y.obj.left) (h : (chainQ rule s₀ n).hom.left.base yn = y)
    (_ : (stage rule s₀ n).f.hom.left.base yn = z n),
    Ideal.comap (((chainQ rule s₀ n).hom.left.stalkMap yn).hom.comp
      (eqToHom (congrArg (stage rule s₀ 0).Y.obj.left.presheaf.stalk h.symm)).hom)
      (fibreIdealAt (stage rule s₀ n).f yn)

variable {rule s₀}

theorem mem_fibreKernel_iff (z : ∀ n, (stage rule s₀ n).X.obj.left) (n : ℕ)
    (y : (stage rule s₀ 0).Y.obj.left) (g : (stage rule s₀ 0).Y.obj.left.presheaf.stalk y) :
    g ∈ fibreKernel rule s₀ z n y ↔
      ∀ (yn : (stage rule s₀ n).Y.obj.left) (h : (chainQ rule s₀ n).hom.left.base yn = y),
        (stage rule s₀ n).f.hom.left.base yn = z n →
          ((chainQ rule s₀ n).hom.left.stalkMap yn).hom
            ((eqToHom (congrArg (stage rule s₀ 0).Y.obj.left.presheaf.stalk h.symm)).hom g) ∈
            fibreIdealAt (stage rule s₀ n).f yn := by
  simp only [fibreKernel, Ideal.mem_iInf, Ideal.mem_comap, RingHom.comp_apply]

/-- Membership at the image of a point of the fibre. -/
theorem mem_fibreKernel_at {z : ∀ n, (stage rule s₀ n).X.obj.left} {n : ℕ}
    {yn : (stage rule s₀ n).Y.obj.left} (hyn : (stage rule s₀ n).f.hom.left.base yn = z n)
    {g : (stage rule s₀ 0).Y.obj.left.presheaf.stalk ((chainQ rule s₀ n).hom.left.base yn)}
    (hg : g ∈ fibreKernel rule s₀ z n ((chainQ rule s₀ n).hom.left.base yn)) :
    ((chainQ rule s₀ n).hom.left.stalkMap yn).hom g ∈ fibreIdealAt (stage rule s₀ n).f yn := by
  have h := (mem_fibreKernel_iff z n _ g).mp hg yn rfl hyn
  simpa using h

/-- **The kernels increase along a compatible sequence** (the fibres shrink). -/
theorem fibreKernel_mono (z : ∀ n, (stage rule s₀ n).X.obj.left)
    (hz : ∀ n, (Stage.σ rule (stage rule s₀ n)).hom.left.base (z (n + 1)) = z n) (n : ℕ)
    (y : (stage rule s₀ 0).Y.obj.left) :
    fibreKernel rule s₀ z n y ≤ fibreKernel rule s₀ z (n + 1) y := by
  intro g hg
  rw [mem_fibreKernel_iff]
  intro y' h hy'
  subst h
  simp only [eqToHom_refl, CommRingCat.hom_id, RingHom.id_apply]
  have e := chainQ_succ_stalkMap rule s₀ n y' g
  rw [e]
  apply map_fibreIdealAt_le rule _ y'
  apply Ideal.mem_map_of_mem
  exact mem_fibreKernel_at ((step_comm_apply rule (stage rule s₀ n) y').symm.trans
    ((congrArg (Stage.σ rule (stage rule s₀ n)).hom.left.base hy').trans (hz n))) hg

theorem isAscending_fibreKernel (z : ∀ n, (stage rule s₀ n).X.obj.left)
    (hz : ∀ n, (Stage.σ rule (stage rule s₀ n)).hom.left.base (z (n + 1)) = z n) :
    IsAscending (stage rule s₀ 0).Y.obj.left (fibreKernel rule s₀ z) :=
  fun n y => fibreKernel_mono z hz n y

/-- **A strict fibre decrease makes the kernel grow strictly** at a point of `f_0⁻¹(z_0)`. -/
theorem fibreKernel_lt (hsurj : ∀ n, StepFibreSurjective rule (stage rule s₀ n))
    (z : ∀ n, (stage rule s₀ n).X.obj.left)
    (hz : ∀ n, (Stage.σ rule (stage rule s₀ n)).hom.left.base (z (n + 1)) = z n) (n : ℕ)
    (hdec : StepFibreDecreasesAt rule (stage rule s₀ n) (z (n + 1))) :
    ∃ y : (stage rule s₀ 0).Y.obj.left, (stage rule s₀ 0).f.hom.left.base y = z 0 ∧
      fibreKernel rule s₀ z n y < fibreKernel rule s₀ z (n + 1) y := by
  classical
  obtain ⟨yn, hyn, hdec⟩ := hdec
  rw [hz n] at hyn
  refine ⟨(chainQ rule s₀ n).hom.left.base yn, chainQ_mem_fibre z hz n yn hyn,
    lt_of_le_of_ne (fibreKernel_mono z hz n _) fun heq => ?_⟩
  by_cases hex : ∃ y' : (stage rule s₀ (n + 1)).Y.obj.left,
      (Stage.q rule (stage rule s₀ n)).hom.left.base y' = yn ∧
        (stage rule s₀ (n + 1)).f.hom.left.base y' = z (n + 1)
  · obtain ⟨y', hy'q, hy'f⟩ := hex
    obtain ⟨h, hh, hqh⟩ := hdec y' hy'q hy'f
    subst hy'q
    obtain ⟨a₀, ha₀⟩ := exists_sub_mem_chain hsurj n _ h
    -- `a₀` lies in the next kernel
    have hin : a₀ ∈ fibreKernel rule s₀ z (n + 1)
        ((chainQ rule s₀ n).hom.left.base ((Stage.q rule (stage rule s₀ n)).hom.left.base y')) := by
      rw [mem_fibreKernel_iff]
      intro y'' h'' hy''
      have hqq : (Stage.q rule (stage rule s₀ n)).hom.left.base y'' =
          (Stage.q rule (stage rule s₀ n)).hom.left.base y' := by
        apply chainQ_injective n
        · exact (step_comm_apply rule (stage rule s₀ n) y'').symm.trans
            ((congrArg (Stage.σ rule (stage rule s₀ n)).hom.left.base (hy''.trans hy'f.symm)).trans
              (step_comm_apply rule (stage rule s₀ n) y'))
        · exact h''
      have hyy : y'' = y' :=
        HironakaG10ChowPairInjective.stage_pairInjective rule (stage rule s₀ n) y'' y'
          (hy''.trans hy'f.symm) hqq
      subst hyy
      change ((chainQ rule s₀ (n + 1)).hom.left.stalkMap y'').hom a₀ ∈ _
      have e := chainQ_succ_stalkMap rule s₀ n y'' a₀
      rw [e]
      have h1 : ((chainQ rule s₀ n).hom.left.stalkMap
          ((Stage.q rule (stage rule s₀ n)).hom.left.base y'')).hom a₀ =
          h - (h - ((chainQ rule s₀ n).hom.left.stalkMap
            ((Stage.q rule (stage rule s₀ n)).hom.left.base y'')).hom a₀) := by abel
      rw [h1, map_sub]
      exact Ideal.sub_mem _ hqh (map_fibreIdealAt_le rule _ y'' (Ideal.mem_map_of_mem _ ha₀))
    rw [← heq] at hin
    apply hh
    have h1 : h = (h - ((chainQ rule s₀ n).hom.left.stalkMap
        ((Stage.q rule (stage rule s₀ n)).hom.left.base y')).hom a₀) +
        ((chainQ rule s₀ n).hom.left.stalkMap
          ((Stage.q rule (stage rule s₀ n)).hom.left.base y')).hom a₀ := by abel
    rw [h1]
    exact Ideal.add_mem _ ha₀ (mem_fibreKernel_at ((step_comm_apply rule (stage rule s₀ n) y').symm.trans
      ((congrArg (Stage.σ rule (stage rule s₀ n)).hom.left.base hy'f).trans (hz n))) hin)
  · -- no point over `yn` in the next fibre: the next kernel is the unit ideal
    simp only [not_exists, not_and] at hex
    have htop : (1 : (stage rule s₀ 0).Y.obj.left.presheaf.stalk
        ((chainQ rule s₀ n).hom.left.base yn)) ∈ fibreKernel rule s₀ z (n + 1)
        ((chainQ rule s₀ n).hom.left.base yn) := by
      rw [mem_fibreKernel_iff]
      intro y'' h'' hy''
      exfalso
      have hqq : (Stage.q rule (stage rule s₀ n)).hom.left.base y'' = yn := by
        apply chainQ_injective n
        · exact (step_comm_apply rule (stage rule s₀ n) y'').symm.trans
            ((congrArg (Stage.σ rule (stage rule s₀ n)).hom.left.base hy'').trans ((hz n).trans hyn.symm))
        · exact h''
      exact hex y'' hqq hy''
    rw [← heq] at htop
    have h1 := mem_fibreKernel_at hyn htop
    rw [map_one] at h1
    exact lrsFibreIdeal_ne_top _ _ ((Ideal.eq_top_iff_one _).mpr h1)

/-! ### Termination -/

/-- **No strict fibre decrease infinitely often** (route step (4.3)): along a compatible sequence of
base points, with surjective fibre algebras at every step, the local Noether property of `Y_0` and
locally finitely generated kernels, the fibre cannot strictly decrease infinitely often. -/
theorem not_frequently_fibreDecreases (hf : IsProperMap s₀.f.hom.left.base)
    (hN : HasLocalNoetherProperty (stage rule s₀ 0).Y.obj.left)
    (hsurj : ∀ n, StepFibreSurjective rule (stage rule s₀ n))
    (z : ∀ n, (stage rule s₀ n).X.obj.left)
    (hz : ∀ n, (Stage.σ rule (stage rule s₀ n)).hom.left.base (z (n + 1)) = z n)
    (hfg : ∀ n, IsLocallyFinitelyGenerated (stage rule s₀ 0).Y.obj.left (fibreKernel rule s₀ z n)) :
    ¬ ∀ N, ∃ m, N ≤ m ∧ StepFibreDecreasesAt rule (stage rule s₀ m) (z (m + 1)) := by
  intro hfreq
  set K : Set (stage rule s₀ 0).Y.obj.left :=
    (stage rule s₀ 0).f.hom.left.base ⁻¹' {z 0} with hK
  have hKc : IsCompact K := hf.isCompact_preimage isCompact_singleton
  obtain ⟨N, W, hKW, hW⟩ :=
    hN.exists_stationary_nhds (isAscending_fibreKernel z hz) hfg K hKc
  obtain ⟨m, hm, hdec⟩ := hfreq N
  obtain ⟨y, hy, hlt⟩ := fibreKernel_lt hsurj z hz m hdec
  have h1 := hW m hm y (hKW hy)
  have h2 := hW (m + 1) (by omega) y (hKW hy)
  rw [h1, h2] at hlt
  exact lt_irrefl _ hlt

/-- **No infinite branch of non-flat points** from strict fibre decrease at every non-flat point of
the next stage (the hypothesis `hno` of `exists_flattening_of_rule'`). -/
theorem not_isBranch_of_fibreDecreases (hf : IsProperMap s₀.f.hom.left.base)
    (hN : HasLocalNoetherProperty (stage rule s₀ 0).Y.obj.left)
    (hsurj : ∀ n, StepFibreSurjective rule (stage rule s₀ n))
    (hfg : ∀ (z : ∀ n, (stage rule s₀ n).X.obj.left) n,
      IsLocallyFinitelyGenerated (stage rule s₀ 0).Y.obj.left (fibreKernel rule s₀ z n))
    (hdec : ∀ n, ∀ x' ∈ nonflatImage (stage rule s₀ (n + 1)).f,
      StepFibreDecreasesAt rule (stage rule s₀ n) x')
    (z : ∀ n, (stage rule s₀ n).X.obj.left) :
    ¬ IsBranch (fun n => (Stage.σ rule (stage rule s₀ n)).hom.left.base)
      (fun n => nonflatImage (stage rule s₀ n).f) z := by
  rintro ⟨hmem, hz⟩
  exact not_frequently_fibreDecreases hf hN hsurj z hz (hfg z)
    fun N => ⟨N, le_rfl, hdec N (z (N + 1)) (hmem (N + 1))⟩

/-- **Flattening from strict fibre decrease** (assembly of route steps (4.1), (4.3)): for compact
`X` and proper `f`, the conclusion of `HironakaFlattening` for `f` follows from closed non-flat
images, surjective fibre algebras of the steps (N6), strict fibre decrease at the non-flat points of
the next stage (Lemma 1.18 under (RR)), locally finitely generated fibre kernels and the local
Noether property of `Y`. -/
theorem exists_flattening_of_fibreDecreases (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base)
    (hclosed : ∀ n, IsClosed (nonflatImage (stage rule s₀ n).f))
    (hN : HasLocalNoetherProperty (stage rule s₀ 0).Y.obj.left)
    (hsurj : ∀ n, StepFibreSurjective rule (stage rule s₀ n))
    (hfg : ∀ (z : ∀ n, (stage rule s₀ n).X.obj.left) n,
      IsLocallyFinitelyGenerated (stage rule s₀ 0).Y.obj.left (fibreKernel rule s₀ z n))
    (hdec : ∀ n, ∀ x' ∈ nonflatImage (stage rule s₀ (n + 1)).f,
      StepFibreDecreasesAt rule (stage rule s₀ n) x') :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      HironakaG10ChowTowerDomination.IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧
        interior E = ∅ ∧ HironakaG10ChowFlatteningReduction.IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        HironakaG10ChowFlatteningReduction.IsStrictTransform s₀.f σ E p q ∧
          HironakaG10ChowFlatBimeromorphicIso.IsFlatMorphism p :=
  HironakaG10ChowPairInjective.exists_flattening_of_rule' rule s₀ hX hf hclosed
    fun z => not_isBranch_of_fibreDecreases hf hN hsurj hfg hdec z

/-! ### The Noether property discharged (lane G10P) -/

/-- `not_frequently_fibreDecreases` with the Noether property of `Y_0` discharged
(`HironakaG10PNSourceNoether.hasLocalNoetherProperty`). -/
theorem not_frequently_fibreDecreases' (hf : IsProperMap s₀.f.hom.left.base)
    (hsurj : ∀ n, StepFibreSurjective rule (stage rule s₀ n))
    (z : ∀ n, (stage rule s₀ n).X.obj.left)
    (hz : ∀ n, (Stage.σ rule (stage rule s₀ n)).hom.left.base (z (n + 1)) = z n)
    (hfg : ∀ n, IsLocallyFinitelyGenerated (stage rule s₀ 0).Y.obj.left (fibreKernel rule s₀ z n)) :
    ¬ ∀ N, ∃ m, N ≤ m ∧ StepFibreDecreasesAt rule (stage rule s₀ m) (z (m + 1)) :=
  not_frequently_fibreDecreases hf
    (HironakaG10PNSourceNoether.hasLocalNoetherProperty (stage rule s₀ 0).Y) hsurj z hz hfg

/-- `not_isBranch_of_fibreDecreases` with the Noether property discharged. -/
theorem not_isBranch_of_fibreDecreases' (hf : IsProperMap s₀.f.hom.left.base)
    (hsurj : ∀ n, StepFibreSurjective rule (stage rule s₀ n))
    (hfg : ∀ (z : ∀ n, (stage rule s₀ n).X.obj.left) n,
      IsLocallyFinitelyGenerated (stage rule s₀ 0).Y.obj.left (fibreKernel rule s₀ z n))
    (hdec : ∀ n, ∀ x' ∈ nonflatImage (stage rule s₀ (n + 1)).f,
      StepFibreDecreasesAt rule (stage rule s₀ n) x')
    (z : ∀ n, (stage rule s₀ n).X.obj.left) :
    ¬ IsBranch (fun n => (Stage.σ rule (stage rule s₀ n)).hom.left.base)
      (fun n => nonflatImage (stage rule s₀ n).f) z :=
  not_isBranch_of_fibreDecreases hf
    (HironakaG10PNSourceNoether.hasLocalNoetherProperty (stage rule s₀ 0).Y) hsurj hfg hdec z

/-- **Flattening from strict fibre decrease, Noether discharged**: for compact `X` and proper `f`,
the conclusion of `HironakaFlattening` for `f` follows from closed non-flat images (4.1), surjective
fibre algebras of the steps (N6), strict fibre decrease at the non-flat points of the next stage
(Lemma 1.18 under (RR)) and locally finitely generated fibre kernels. -/
theorem exists_flattening_of_fibreDecreases' (hX : CompactSpace s₀.X.obj.left)
    (hf : IsProperMap s₀.f.hom.left.base)
    (hclosed : ∀ n, IsClosed (nonflatImage (stage rule s₀ n).f))
    (hsurj : ∀ n, StepFibreSurjective rule (stage rule s₀ n))
    (hfg : ∀ (z : ∀ n, (stage rule s₀ n).X.obj.left) n,
      IsLocallyFinitelyGenerated (stage rule s₀ 0).Y.obj.left (fibreKernel rule s₀ z n))
    (hdec : ∀ n, ∀ x' ∈ nonflatImage (stage rule s₀ (n + 1)).f,
      StepFibreDecreasesAt rule (stage rule s₀ n) x') :
    ∃ (X' : SourceReducedComplexSpace) (σ : X' ⟶ s₀.X) (E : Set X'.obj.left),
      HironakaG10ChowTowerDomination.IsNativeBlowupTower s₀.X X' σ ∧ IsClosed E ∧
        interior E = ∅ ∧ HironakaG10ChowFlatteningReduction.IsOpenImmersionOn σ Eᶜ ∧
      ∃ (Y' : SourceReducedComplexSpace) (p : Y' ⟶ X') (q : Y' ⟶ s₀.Y),
        HironakaG10ChowFlatteningReduction.IsStrictTransform s₀.f σ E p q ∧
          HironakaG10ChowFlatBimeromorphicIso.IsFlatMorphism p :=
  exists_flattening_of_fibreDecreases hX hf hclosed
    (HironakaG10PNSourceNoether.hasLocalNoetherProperty (stage rule s₀ 0).Y) hsurj hfg hdec

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
