import Hironaka.Resolution.HironakaG10ChowFlatFibreParameters
import Hironaka.Analytic.RueckertNullstellensatz
import Hironaka.Analytic.ProperMappingTheorem
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.FibreDimensionLowerBound
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Resolution.HironakaHolomorphicJetChartInvariance
import Hironaka.Analytic.HolomorphicGermNoetherian

/-!
# Flat holomorphic map germs are open

Blueprint `hironaka-g10-chowside-flat-open.tex` (node `g10c:flat-germ-open`).

Let `C ⊆ ℂ^m`, `D ⊆ ℂ^n` be analytic germs at `0`, `I_C ⊆ I(C)`, `I_D ⊆ I(D)` ideals of germs
(with `I_C` containing local equations of `C`), and `G : (ℂ^m, 0) → (ℂ^n, 0)` holomorphic with
`I_D ∘ G ⊆ I_C`.  If the induced local homomorphism `𝒪_n ⧸ I_D → 𝒪_m ⧸ I_C`, `[g] ↦ [g ∘ G]`, is
flat, then `G` maps every neighbourhood of `0` in `C` onto a neighbourhood of `0` in `D`
(`eventually_mem_image_of_flat`).

Proof (no dimension theory of analytic sets is used):

1. Fibre parameters (`HironakaG10ChowFlatFibreParameters`): germs `ξ` with `0` isolated in
   `C ∩ {ξ = 0} ∩ G⁻¹(0)` (`eventually_eq_zero_of_isolated`), and such that for every
   prime `P` of `A = 𝒪_n ⧸ I_D`, `√(P B + ξ B) ∩ A = P`.
2. For a prime `P` with lifted generators `π`, the slice `Z_P = C ∩ {π ∘ G = 0, ξ = 0}` maps
   properly to a small ball near `0`, so its image is an analytic germ (Remmert's proper mapping
   theorem, `isAnalyticGerm_image_of_isolated`).  Rückert's Nullstellensatz and step 1 show that
   every local equation of that image vanishes on `D ∩ {π = 0}`: the image contains the germ
   `D ∩ {π = 0}` (`eventually_mem_image_of_prime`).
3. `D` is the union of the germs `D ∩ {π_P = 0}` over the finitely many minimal primes `P` of `A`
   (`eventually_exists_minimalPrime_vanish`).

Sorry-free.
-/

set_option autoImplicit false

open Set Filter Topology Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG10ChowFlatGermOpen

open AnalyticGermDecomposition IsLocalRing HironakaHolomorphicJetChartInvariance

noncomputable section

/-! ### Rückert's Nullstellensatz for finitely indexed families -/

/-- **Rückert's Nullstellensatz**, for a family indexed by any finite type. -/
theorem vanishingIdeal_le_radical_of_finite {n : ℕ} (I : Ideal (HolGerm (ComplexModel n)))
    {ι : Type*} [Finite ι] (f : ι → ComplexModel n → ℂ)
    (hf : ∀ j, ∃ hfj : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f j) z, HolGerm.mk (f j) hfj ∈ I) :
    vanishingIdeal {z | ∀ j, f j z = 0} ≤ I.radical := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  have h := RueckertNullstellensatz.vanishingIdeal_le_radical I (fun i => f (e.symm i))
    (fun i => hf (e.symm i))
  have hset : {z : ComplexModel n | ∀ j, f j z = 0} = {z | ∀ i, f (e.symm i) z = 0} := by
    ext z
    constructor
    · exact fun hz i => hz _
    · intro hz j
      simpa using hz (e j)
  rw [hset]
  exact h

/-! ### Images of isolated slices are analytic germs (Remmert) -/

/-- Holomorphic on an open set of `ℂ^m` gives holomorphic on that set as a manifold. -/
theorem contMDiff_opens_of_differentiableOn {m k : ℕ} {W : Opens (ComplexModel m)}
    {g : ComplexModel m → ComplexModel k} {s : Set (ComplexModel m)} (hs : IsOpen s)
    (hg : DifferentiableOn ℂ g s) (hWs : (W : Set (ComplexModel m)) ⊆ s) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel k) ∞ (fun w : W => g w) := by
  have h1 : ContDiffOn ℂ ∞ g s := contDiffOn_of_differentiableOn_complex hg hs
  exact AnalyticSubsetOpens.contMDiff_restrict ((h1.mono hWs).contMDiffOn)

/-- The image in `ℂ^n` of an analytic subset of an open set `U ∋ 0` is an analytic germ at `0`
(the argument of `HironakaRealOpenGeometricStrictSaturation`). -/
theorem image_analytic_germ {n : ℕ} (U : Opens (ComplexModel n))
    (h0 : (0 : ComplexModel n) ∈ U) (W : Set U)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsAnalyticGerm ((Subtype.val : U → ComplexModel n) '' W) := by
  let x : U := ⟨0, h0⟩
  obtain ⟨p⟩ := hW x
  let e := (complexChartAt (n := n) x).val
  have he (y : U) : e y = y.val := rfl
  have hxval : x.val = 0 := rfl
  have hs (y : U) : y ∈ e.source := by trivial
  have hset : {z : ComplexModel n | z + e x ∈ e.target ∩ e.symm ⁻¹' W} =
      (Subtype.val : U → ComplexModel n) '' W := by
    ext z
    constructor
    · rintro ⟨hzT, hzW⟩
      refine ⟨e.symm (z + e x), hzW, ?_⟩
      have hz := e.right_inv hzT
      change (e.symm (z + e x)).val = z
      simpa only [he, hxval, add_zero] using hz
    · rintro ⟨y, hy, rfl⟩
      have hyT := e.map_source (hs y)
      have hyW : e.symm (e y) ∈ W := (e.left_inv (hs y)).symm ▸ hy
      change y.val + e x ∈ e.target ∩ e.symm ⁻¹' W
      simpa only [he, hxval, add_zero, mem_inter_iff, mem_preimage] using And.intro hyT hyW
  rw [← hset]
  exact ClosureDifferenceAnalytic.isAnalyticGerm_chart_translate p

/-- **Images of isolated slices are analytic germs.**  Let `f_i`, `G` be holomorphic on the ball
`B(0, ρ)` and suppose that on the closed ball `B̄(0, r)`, `r < ρ`, the only common zero of the
`f_i` in the fibre `G⁻¹(0)` is `0`.  Then for some `δ > 0` the image under `G` of the common zero
set of the `f_i` in `B(0, r) ∩ G⁻¹(B(0, δ))` is an analytic germ at `0` (Remmert's proper mapping
theorem). -/
theorem isAnalyticGerm_image_of_isolated {m n : ℕ} {ι : Type} [Fintype ι]
    (f : ι → ComplexModel m → ℂ) (G : ComplexModel m → ComplexModel n) {ρ r : ℝ}
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball 0 ρ)) (hG : DifferentiableOn ℂ G (ball 0 ρ))
    (hr : 0 < r) (hrρ : r < ρ)
    (hiso : ∀ z ∈ closedBall (0 : ComplexModel m) r, (∀ i, f i z = 0) → G z = 0 → z = 0) :
    ∃ δ > 0, IsAnalyticGerm (G '' {z | z ∈ ball (0 : ComplexModel m) r ∧ (∀ i, f i z = 0) ∧
      G z ∈ ball (0 : ComplexModel n) δ}) := by
  classical
  have hcb : closedBall (0 : ComplexModel m) r ⊆ ball 0 ρ := closedBall_subset_ball hrρ
  have hGc : ContinuousOn G (closedBall (0 : ComplexModel m) r) := hG.continuousOn.mono hcb
  have hfc : ∀ i, ContinuousOn (f i) (closedBall (0 : ComplexModel m) r) :=
    fun i => (hf i).continuousOn.mono hcb
  set F : ComplexModel m → (ι → ℂ) := fun z i => f i z with hFdef
  have hFc : ContinuousOn F (closedBall (0 : ComplexModel m) r) := continuousOn_pi.mpr hfc
  have hZ : ∀ z, (∀ i, f i z = 0) ↔ F z = 0 := fun z =>
    ⟨fun h => funext h, fun h i => congrFun h i⟩
  have hZclosed : IsClosed (closedBall (0 : ComplexModel m) r ∩ F ⁻¹' {0}) :=
    hFc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  -- the part of the slice on the boundary sphere
  set K := sphere (0 : ComplexModel m) r ∩ F ⁻¹' {0} with hK
  have hKc : IsCompact K := by
    have : K = sphere 0 r ∩ (closedBall 0 r ∩ F ⁻¹' {0}) := by
      ext z
      simp only [K, mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, sphere_subset_closedBall h1, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [this]
    exact (isCompact_sphere 0 r).inter_right hZclosed
  have hKG : ∀ z ∈ K, G z ≠ 0 := by
    rintro z ⟨hzs, hzF⟩ hGz
    have hz0 := hiso z (sphere_subset_closedBall hzs) ((hZ z).mpr hzF) hGz
    rw [mem_sphere_zero_iff_norm, hz0, norm_zero] at hzs
    exact hr.ne hzs
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ z ∈ K, δ ≤ ‖G z‖ := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · have hcont : ContinuousOn (fun z => ‖G z‖) K :=
        (hGc.mono (fun z hz => sphere_subset_closedBall hz.1)).norm
      obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn hne hcont
      exact ⟨‖G z₀‖, norm_pos_iff.mpr (hKG z₀ hz₀), fun z hz => hmin hz⟩
  refine ⟨δ, hδ, ?_⟩
  -- the source and target manifolds
  have hWopen : IsOpen (ball (0 : ComplexModel m) r ∩ G ⁻¹' ball 0 δ) :=
    (hG.continuousOn.mono (ball_subset_ball hrρ.le)).isOpen_inter_preimage isOpen_ball isOpen_ball
  let W : Opens (ComplexModel m) := ⟨_, hWopen⟩
  let Y : Opens (ComplexModel n) := ⟨ball 0 δ, isOpen_ball⟩
  let Φ : W → Y := fun w => ⟨G w, w.2.2⟩
  have hWρ : (W : Set (ComplexModel m)) ⊆ ball 0 ρ := fun w hw => ball_subset_ball hrρ.le hw.1
  have hΦ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ Φ :=
    (ContMDiff.subtypeVal_comp_iff Y Φ).mp
      (contMDiff_opens_of_differentiableOn isOpen_ball hG hWρ)
  -- the slice as an analytic subset of `W`
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let v : ComplexModel m → ComplexModel k := fun z =>
    (EuclideanSpace.equiv (Fin k) ℂ).symm (fun j => f (e.symm j) z)
  have hv : DifferentiableOn ℂ v (ball 0 ρ) :=
    (EuclideanSpace.equiv (Fin k) ℂ).symm.differentiable.comp_differentiableOn
      (differentiableOn_pi.mpr fun j => hf (e.symm j))
  let Ψ : W → ComplexModel k := fun w => v w
  have hΨ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel k) ∞ Ψ :=
    contMDiff_opens_of_differentiableOn isOpen_ball hv hWρ
  let Aset : Set W := Ψ ⁻¹' {0}
  have hA : IsComplexAnalyticSubset (n := m) Aset :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hΨ
      (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton 0)
  have hvz : ∀ z, v z = 0 ↔ ∀ i, f i z = 0 := by
    intro z
    simp only [v, map_eq_zero_iff _ (EuclideanSpace.equiv (Fin k) ℂ).symm.injective]
    constructor
    · intro h i
      simpa using congrFun h (e i)
    · intro h
      funext j
      exact h _
  have hAmem : ∀ w : W, w ∈ Aset ↔ ∀ i, f i w = 0 := fun w => hvz w
  -- properness
  have hprop : AnalyticDimensionBasics.ProperOn Φ Aset := by
    intro L hL
    let L' : Set (ComplexModel n) := Subtype.val '' L
    have hL' : IsCompact L' := hL.image continuous_subtype_val
    let Q : Set (ComplexModel m) := (closedBall 0 r ∩ F ⁻¹' {0}) ∩ G ⁻¹' L'
    have hQclosed : IsClosed Q :=
      (hGc.mono inter_subset_left).preimage_isClosed_of_isClosed hZclosed hL'.isClosed
    have hQc : IsCompact Q :=
      (isCompact_closedBall (0 : ComplexModel m) r).of_isClosed_subset hQclosed
        (fun z hz => hz.1.1)
    have hL'δ : L' ⊆ ball 0 δ := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hQW : Q ⊆ (W : Set (ComplexModel m)) := by
      rintro z ⟨⟨hzb, hzF⟩, hzL⟩
      refine ⟨?_, hL'δ hzL⟩
      rcases (mem_closedBall.mp hzb).lt_or_eq with hlt | heq
      · exact mem_ball.mpr hlt
      · exfalso
        have hzK : z ∈ K := ⟨by rwa [mem_sphere], hzF⟩
        have h1 := hδK z hzK
        have h2 : ‖G z‖ < δ := mem_ball_zero_iff.mp (hL'δ hzL)
        linarith
    have hset : Subtype.val '' (Aset ∩ Φ ⁻¹' L) = Q := by
      ext z
      constructor
      · rintro ⟨w, ⟨hwA, hwL⟩, rfl⟩
        refine ⟨⟨(ball_subset_closedBall w.2.1), (hZ w).mp ((hAmem w).mp hwA)⟩, ?_⟩
        exact ⟨Φ w, hwL, rfl⟩
      · intro hz
        refine ⟨⟨z, hQW hz⟩, ⟨(hAmem _).mpr ((hZ z).mpr hz.1.2), ?_⟩, rfl⟩
        obtain ⟨y, hyL, hyz⟩ := hz.2
        have : y = Φ ⟨z, hQW hz⟩ := Subtype.ext hyz
        rw [mem_preimage, ← this]
        exact hyL
    rw [Subtype.isCompact_iff, hset]
    exact hQc
  -- Remmert's proper mapping theorem
  have hS : IsComplexAnalyticSubset (n := n) (Φ '' Aset) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hΦ hA hprop
  have hgerm := image_analytic_germ Y (mem_ball_self hδ) (Φ '' Aset) hS
  convert hgerm using 1
  ext u
  constructor
  · rintro ⟨z, ⟨hzb, hzf, hzG⟩, rfl⟩
    exact ⟨Φ ⟨z, hzb, hzG⟩, ⟨⟨z, hzb, hzG⟩, (hAmem _).mpr hzf, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w.val, ⟨w.2.1, (hAmem w).mp hw, w.2.2⟩, rfl⟩

/-! ### Germ calculus -/

section Germ

instance instIsNoetherianRingHolGerm (k : ℕ) : IsNoetherianRing (HolGerm (ComplexModel k)) :=
  isNoetherianRing_holGerm_euclidean k

/-- Vanishing ideals are radical. -/
theorem mem_vanishingIdeal_of_pow_mem {k : ℕ} {S : Set (ComplexModel k)}
    {a : HolGerm (ComplexModel k)} {e : ℕ} (h : a ^ e ∈ vanishingIdeal S) :
    a ∈ vanishingIdeal S := by
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk a
  rw [← HolGerm.mk_pow, mem_vanishingIdeal_mk] at h
  refine mem_vanishingIdeal_mk.mpr ?_
  filter_upwards [h] with z hz hzS
  exact eq_zero_of_pow_eq_zero (hz hzS)

/-- `vanishingIdeal S` contains the radical of every ideal it contains. -/
theorem radical_le_vanishingIdeal {k : ℕ} {S : Set (ComplexModel k)}
    {K : Ideal (HolGerm (ComplexModel k))} (h : K ≤ vanishingIdeal S) :
    K.radical ≤ vanishingIdeal S := by
  rintro a ⟨e, he⟩
  exact mem_vanishingIdeal_of_pow_mem (h he)

/-- Germs of finite products. -/
theorem mk_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} (s : Finset ι)
    (f : ι → E → ℂ) (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (f i) z)
    (h : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) h = ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, ← HolGerm.mk_one]
    exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z => by simp)
  | insert a s ha ih =>
    have hs : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
      filter_upwards [(eventually_all_finset s).mpr fun i _ => hf i] with z hz
      exact (HasFDerivAt.finsetProd fun i hi => (hz i hi).hasFDerivAt).differentiableAt
    rw [Finset.prod_insert ha, ← ih hs, ← HolGerm.mk_mul]
    exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun z => by simp [Finset.prod_insert ha])

/-- Lifting a finite set of elements of a quotient of the germ ring to holomorphic functions. -/
theorem exists_lift_finset {k : ℕ} (I : Ideal (HolGerm (ComplexModel k)))
    (S : Finset (HolGerm (ComplexModel k) ⧸ I)) :
    ∃ (t : ℕ) (π : Fin t → ComplexModel k → ℂ) (hπ : ∀ i, ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ (π i) w),
      (S : Set (HolGerm (ComplexModel k) ⧸ I)) =
        range fun i => Ideal.Quotient.mk I (HolGerm.mk (π i) (hπ i)) := by
  classical
  have hb : ∀ j : Fin S.card, ∃ (ξ : ComplexModel k → ℂ) (h : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ ξ z),
      Ideal.Quotient.mk I (HolGerm.mk ξ h) = (S.equivFin.symm j : _) := by
    intro j
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (S.equivFin.symm j : HolGerm (ComplexModel k) ⧸ I)
    obtain ⟨ξ, h, rfl⟩ := HolGerm.exists_eq_mk g
    exact ⟨ξ, h, hg⟩
  choose ξ hξ hξb using hb
  refine ⟨S.card, ξ, hξ, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨S.equivFin ⟨x, hx⟩, ?_⟩
    dsimp only
    rw [hξb]
    simp
  · rintro ⟨j, rfl⟩
    dsimp only
    rw [hξb]
    exact (S.equivFin.symm j).2

variable {m n : ℕ}

/-- Composition preserves the value at `0`. -/
theorem eval_compAlgHom (G : ComplexModel m → ComplexModel n)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) (hG0 : G 0 = 0) (g : HolGerm (ComplexModel n)) :
    HolGerm.eval (compAlgHom G hG hG0 g) = HolGerm.eval g := by
  obtain ⟨F, hF, rfl⟩ := HolGerm.exists_eq_mk g
  rw [compAlgHom_mk, HolGerm.eval_mk, HolGerm.eval_mk, Function.comp_apply, hG0]

/-- The germ map `[g] ↦ [g ∘ G]` is local. -/
theorem isLocalHom_quotientMap_compAlgHom (IC : Ideal (HolGerm (ComplexModel m)))
    (ID : Ideal (HolGerm (ComplexModel n))) (G : ComplexModel m → ComplexModel n)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) (hG0 : G 0 = 0) (hICt : IC ≠ ⊤)
    (hcomap : ID ≤ IC.comap (compAlgHom G hG hG0).toRingHom) :
    IsLocalHom (Ideal.quotientMap IC (compAlgHom G hG hG0).toRingHom hcomap) := by
  have : IsLocalRing (HolGerm (ComplexModel m) ⧸ IC) :=
    HironakaG10ChowFlatFibreParameters.isLocalRing_quotient hICt
  refine ⟨fun a ha => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.quotientMap_mk] at ha
  have hg : IsUnit g := by
    rw [HolGerm.isUnit_iff_eval_ne_zero]
    intro h0
    have hm : (compAlgHom G hG hG0).toRingHom g ∈ maximalIdeal (HolGerm (ComplexModel m)) := by
      rw [HolGerm.mem_maximalIdeal_iff]
      change HolGerm.eval (compAlgHom G hG hG0 g) = 0
      rw [eval_compAlgHom, h0]
    have : Ideal.Quotient.mk IC ((compAlgHom G hG hG0).toRingHom g) ∈
        maximalIdeal (HolGerm (ComplexModel m) ⧸ IC) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem _ hm
    exact (IsLocalRing.mem_maximalIdeal _).mp this ha
  exact hg.map _

/-- **The fibre is isolated.**  If `m_B ⊆ √(ξ B + m_A B)`, then `0` is isolated in
`C ∩ {ξ = 0} ∩ G⁻¹(0)`. -/
theorem eventually_eq_zero_of_isolated (IC : Ideal (HolGerm (ComplexModel m)))
    (ID : Ideal (HolGerm (ComplexModel n))) (G : ComplexModel m → ComplexModel n)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) (hG0 : G 0 = 0)
    (hcomap : ID ≤ IC.comap (compAlgHom G hG hG0).toRingHom)
    [IsLocalRing (HolGerm (ComplexModel m) ⧸ IC)] [IsLocalRing (HolGerm (ComplexModel n) ⧸ ID)]
    (C : Set (ComplexModel m)) (hIC : IC ≤ vanishingIdeal C)
    {k : ℕ} (ξ : Fin k → ComplexModel m → ℂ) (hξ : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (ξ j) z)
    (hrad : maximalIdeal (HolGerm (ComplexModel m) ⧸ IC) ≤
      (Ideal.span (range fun j => Ideal.Quotient.mk IC (HolGerm.mk (ξ j) (hξ j))) ⊔
        (maximalIdeal (HolGerm (ComplexModel n) ⧸ ID)).map
          (Ideal.quotientMap IC (compAlgHom G hG hG0).toRingHom hcomap)).radical) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel m), z ∈ C → (∀ j, ξ j z = 0) → G z = 0 → z = 0 := by
  classical
  set κ := (compAlgHom G hG hG0).toRingHom with hκ
  set φ := Ideal.quotientMap IC κ hcomap with hφ
  let S0 : Set (ComplexModel m) := {z | z ∈ C ∧ (∀ j, ξ j z = 0) ∧ G z = 0}
  let X : Ideal (HolGerm (ComplexModel m)) := Ideal.span (range fun j => HolGerm.mk (ξ j) (hξ j)) ⊔
    (maximalIdeal (HolGerm (ComplexModel n))).map κ
  have hXS : X ⊔ IC ≤ vanishingIdeal S0 := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun z hz => hz.2.1 j)
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      obtain ⟨F, hF, rfl⟩ := HolGerm.exists_eq_mk g
      rw [HolGerm.mem_maximalIdeal_iff, HolGerm.eval_mk] at hg
      rw [Ideal.mem_comap]
      change compAlgHom G hG hG0 (HolGerm.mk F hF) ∈ _
      rw [compAlgHom_mk]
      refine mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun z hz => ?_)
      change F (G z) = 0
      rw [hz.2.2, hg]
    · exact hIC.trans (vanishingIdeal_anti (Eventually.of_forall fun z hz => hz.1))
  have hmapX : Ideal.span (range fun j => Ideal.Quotient.mk IC (HolGerm.mk (ξ j) (hξ j))) ⊔
      (maximalIdeal (HolGerm (ComplexModel n) ⧸ ID)).map φ ≤ X.map (Ideal.Quotient.mk IC) := by
    rw [Ideal.map_sup]
    refine sup_le_sup (le_of_eq ?_) (le_of_eq ?_)
    · rw [Ideal.map_span, ← Set.range_comp]
      rfl
    · rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk ID)
        Ideal.Quotient.mk_surjective, Ideal.map_map, Ideal.map_map, hφ, Ideal.quotientMap_comp_mk]
  have hm : maximalIdeal (HolGerm (ComplexModel m)) ≤ vanishingIdeal S0 := by
    have : IsLocalHom (Ideal.Quotient.mk IC) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk IC)]
    refine (Ideal.comap_mono (hrad.trans (Ideal.radical_mono hmapX))).trans ?_
    rw [Ideal.comap_radical, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact radical_le_vanishingIdeal hXS
  have hcoord : ∀ l : Fin m, ∀ᶠ z in 𝓝 (0 : ComplexModel m), z ∈ S0 → z l = 0 := by
    intro l
    have hd : ∀ᶠ z in 𝓝 (0 : ComplexModel m),
        DifferentiableAt ℂ (fun z : ComplexModel m => z l) z :=
      Eventually.of_forall fun z =>
        (EuclideanSpace.proj (𝕜 := ℂ) l : ComplexModel m →L[ℂ] ℂ).differentiableAt
    have hmem : HolGerm.mk (fun z : ComplexModel m => z l) hd ∈
        maximalIdeal (HolGerm (ComplexModel m)) := by
      rw [HolGerm.mem_maximalIdeal_iff, HolGerm.eval_mk]
      rfl
    exact mem_vanishingIdeal_mk.mp (hm hmem)
  filter_upwards [eventually_all.mpr hcoord] with z hz hzC hzξ hzG
  ext l
  exact hz l ⟨hzC, hzξ, hzG⟩

/-- **The image contains the subgerm of a prime.**  Let `P` be a prime of `A = 𝒪_n ⧸ I_D`
generated by the classes of `π_i`, and suppose `√(P B + ξ B) ∩ A ⊆ P` (fibre parameters).  Then
for every neighbourhood `U` of `0`, the germ `D ∩ {π = 0}` lies in `G(C ∩ U)`. -/
theorem eventually_mem_image_of_prime (IC : Ideal (HolGerm (ComplexModel m)))
    (ID : Ideal (HolGerm (ComplexModel n))) (G : ComplexModel m → ComplexModel n)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) (hG0 : G 0 = 0)
    (hcomap : ID ≤ IC.comap (compAlgHom G hG hG0).toRingHom)
    (C : Set (ComplexModel m)) (D : Set (ComplexModel n)) (hID : ID ≤ vanishingIdeal D)
    {q : ℕ} (c : Fin q → ComplexModel m → ℂ) (hc : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (c j) z)
    (hcI : ∀ j, HolGerm.mk (c j) (hc j) ∈ IC)
    (hcC : ∀ᶠ z in 𝓝 (0 : ComplexModel m), (∀ j, c j z = 0) → z ∈ C)
    {k : ℕ} (ξ : Fin k → ComplexModel m → ℂ) (hξ : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (ξ j) z)
    (hiso : ∀ᶠ z in 𝓝 (0 : ComplexModel m), z ∈ C → (∀ j, ξ j z = 0) → G z = 0 → z = 0)
    (P : Ideal (HolGerm (ComplexModel n) ⧸ ID))
    (hkey : ∀ h, Ideal.quotientMap IC (compAlgHom G hG hG0).toRingHom hcomap h ∈
      (P.map (Ideal.quotientMap IC (compAlgHom G hG hG0).toRingHom hcomap) ⊔
        Ideal.span (range fun j => Ideal.Quotient.mk IC (HolGerm.mk (ξ j) (hξ j)))).radical → h ∈ P)
    {t : ℕ} (π : Fin t → ComplexModel n → ℂ) (hπ : ∀ i, ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ (π i) w)
    (hP : P = Ideal.span (range fun i => Ideal.Quotient.mk ID (HolGerm.mk (π i) (hπ i))))
    (U : Set (ComplexModel m)) (hU : U ∈ 𝓝 0) :
    ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ D → (∀ i, π i w = 0) → w ∈ G '' (C ∩ U) := by
  classical
  set κ := (compAlgHom G hG hG0).toRingHom with hκ
  set φ := Ideal.quotientMap IC κ hcomap with hφ
  have hπG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ (π i ∘ G) z :=
    fun i => holomorphic_comp G hG hG0 (hπ i)
  -- a ball on which everything is holomorphic and the local statements hold
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ G z ∧
      (∀ j, DifferentiableAt ℂ (c j) z) ∧ (∀ i, DifferentiableAt ℂ (π i ∘ G) z) ∧
      (∀ j, DifferentiableAt ℂ (ξ j) z) ∧ ((∀ j, c j z = 0) → z ∈ C) ∧
      (z ∈ C → (∀ j, ξ j z = 0) → G z = 0 → z = 0) :=
    hG.and ((eventually_all.mpr hc).and ((eventually_all.mpr hπG).and
      ((eventually_all.mpr hξ).and (hcC.and hiso))))
  obtain ⟨ρ, hρ, hρev⟩ := Metric.eventually_nhds_iff_ball.mp hev
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  set r := min ρ ε / 2 with hrdef
  have hmin : 0 < min ρ ε := lt_min hρ hε
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrρ : r < ρ := by
    rw [hrdef]
    linarith [min_le_left ρ ε]
  have hrε : r < ε := by
    rw [hrdef]
    linarith [min_le_right ρ ε]
  -- the slice
  let f : (Fin q ⊕ Fin t ⊕ Fin k) → ComplexModel m → ℂ :=
    Sum.elim c (Sum.elim (fun i => π i ∘ G) ξ)
  have hfd : ∀ i, DifferentiableOn ℂ (f i) (ball 0 ρ) := by
    rintro (j | i | j) z hz
    · exact ((hρev z hz).2.1 j).differentiableWithinAt
    · exact ((hρev z hz).2.2.1 i).differentiableWithinAt
    · exact ((hρev z hz).2.2.2.1 j).differentiableWithinAt
  have hGd : DifferentiableOn ℂ G (ball 0 ρ) := fun z hz => (hρev z hz).1.differentiableWithinAt
  have hiso' : ∀ z ∈ closedBall (0 : ComplexModel m) r, (∀ i, f i z = 0) → G z = 0 → z = 0 := by
    intro z hz hfz hGz
    have hzρ : z ∈ ball 0 ρ := closedBall_subset_ball hrρ hz
    have h := hρev z hzρ
    exact h.2.2.2.2.2 (h.2.2.2.2.1 fun j => hfz (Sum.inl j)) (fun j => hfz (Sum.inr (Sum.inr j))) hGz
  obtain ⟨δ, hδ, hS⟩ := isAnalyticGerm_image_of_isolated f G hfd hGd hr0 hrρ hiso'
  set S := G '' {z | z ∈ ball (0 : ComplexModel m) r ∧ (∀ i, f i z = 0) ∧
    G z ∈ ball (0 : ComplexModel n) δ} with hSdef
  have hSsub : S ⊆ G '' (C ∩ U) := by
    rintro _ ⟨z, ⟨hzb, hzf, -⟩, rfl⟩
    have hzρ : z ∈ ball 0 ρ := ball_subset_ball hrρ.le hzb
    exact ⟨z, ⟨(hρev z hzρ).2.2.2.2.1 (fun j => hzf (Sum.inl j)),
      hεU (ball_subset_ball hrε.le hzb)⟩, rfl⟩
  obtain ⟨p, s, hsd, hSeq⟩ := hS
  -- the local equations of the image vanish on the slice
  have hGt : Tendsto G (𝓝 0) (𝓝 0) := by
    simpa only [hG0] using hG.self_of_nhds.continuousAt.tendsto
  have hJ : ∀ l, HolGerm.mk (s l ∘ G) (holomorphic_comp G hG hG0 (hsd l)) ∈
      vanishingIdeal {z | ∀ i, f i z = 0} := by
    intro l
    refine mem_vanishingIdeal_mk.mpr ?_
    have h1 : ∀ᶠ z in 𝓝 (0 : ComplexModel m), z ∈ ball (0 : ComplexModel m) r := ball_mem_nhds 0 hr0
    have h2 : ∀ᶠ z in 𝓝 (0 : ComplexModel m), G z ∈ ball (0 : ComplexModel n) δ :=
      hGt.eventually (ball_mem_nhds 0 hδ)
    have h3 : ∀ᶠ z in 𝓝 (0 : ComplexModel m), (G z ∈ S ↔ ∀ l, s l (G z) = 0) :=
      hGt.eventually hSeq
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3 hzf
    exact (hz3.mp ⟨z, ⟨hz1, hzf, hz2⟩, rfl⟩) l
  -- Rückert
  let J : Ideal (HolGerm (ComplexModel m)) :=
    IC ⊔ Ideal.span (range fun i => HolGerm.mk (π i ∘ G) (hπG i)) ⊔
      Ideal.span (range fun j => HolGerm.mk (ξ j) (hξ j))
  have hfJ : ∀ i, ∃ hfi : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z, HolGerm.mk (f i) hfi ∈ J := by
    rintro (j | i | j)
    · exact ⟨hc j, Ideal.mem_sup_left (Ideal.mem_sup_left (hcI j))⟩
    · exact ⟨hπG i, Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))⟩
    · exact ⟨hξ j, Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)⟩
  have hRu := vanishingIdeal_le_radical_of_finite J f hfJ
  have hJle : J ≤ (P.map φ ⊔ Ideal.span (range fun j =>
      Ideal.Quotient.mk IC (HolGerm.mk (ξ j) (hξ j)))).comap (Ideal.Quotient.mk IC) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro g hg
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      exact zero_mem _
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      have : Ideal.Quotient.mk IC (HolGerm.mk (π i ∘ G) (hπG i)) =
          φ (Ideal.Quotient.mk ID (HolGerm.mk (π i) (hπ i))) := by
        rw [hφ, Ideal.quotientMap_mk]
        rfl
      rw [this]
      refine Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ?_)
      rw [hP]
      exact Ideal.subset_span ⟨i, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
  -- each local equation of the image lies in `P`
  have hsP : ∀ l, Ideal.Quotient.mk ID (HolGerm.mk (s l) (hsd l)) ∈ P := by
    intro l
    apply hkey
    rw [hφ, Ideal.quotientMap_mk]
    have h1 : κ (HolGerm.mk (s l) (hsd l)) =
        HolGerm.mk (s l ∘ G) (holomorphic_comp G hG hG0 (hsd l)) := rfl
    rw [h1]
    have h3 := Ideal.radical_mono hJle (hRu (hJ l))
    rw [← Ideal.comap_radical] at h3
    exact h3
  -- the germ `D ∩ {π = 0}` lies in the image
  have hPv : ∀ l, ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ D → (∀ i, π i w = 0) → s l w = 0 := by
    intro l
    have hle : P.comap (Ideal.Quotient.mk ID) ≤ vanishingIdeal {w | w ∈ D ∧ ∀ i, π i w = 0} := by
      have hspan : Ideal.span (range fun i => Ideal.Quotient.mk ID (HolGerm.mk (π i) (hπ i))) =
          (Ideal.span (range fun i => HolGerm.mk (π i) (hπ i))).map (Ideal.Quotient.mk ID) := by
        rw [Ideal.map_span, ← Set.range_comp]
        rfl
      rw [hP, hspan, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      refine sup_le ?_ (hID.trans (vanishingIdeal_anti (Eventually.of_forall fun w hw => hw.1)))
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun w hw => hw.2 i)
    have := mem_vanishingIdeal_mk.mp (hle (hsP l))
    filter_upwards [this] with w hw hwD hwπ
    exact hw ⟨hwD, hwπ⟩
  filter_upwards [eventually_all.mpr hPv, hSeq] with w hw hwS hwD hwπ
  exact hSsub (hwS.mpr fun l => hw l hwD hwπ)

/-- **`D` is covered by the subgerms of its minimal primes.**  If for each minimal prime `P` of
`𝒪_n ⧸ I_D` the classes of `π_P` lie in `P`, then near `0` every point of `D` is a common zero of
some family `π_P`. -/
theorem eventually_exists_minimalPrime_vanish (ID : Ideal (HolGerm (ComplexModel n)))
    (D : Set (ComplexModel n)) (hID : ID ≤ vanishingIdeal D)
    (t : Ideal (HolGerm (ComplexModel n) ⧸ ID) → ℕ)
    (π : ∀ P : Ideal (HolGerm (ComplexModel n) ⧸ ID), Fin (t P) → ComplexModel n → ℂ)
    (hπ : ∀ P i, ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ (π P i) w)
    (hP : ∀ P ∈ minimalPrimes (HolGerm (ComplexModel n) ⧸ ID), ∀ i,
      Ideal.Quotient.mk ID (HolGerm.mk (π P i) (hπ P i)) ∈ P) :
    ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ D →
      ∃ P ∈ minimalPrimes (HolGerm (ComplexModel n) ⧸ ID), ∀ i, π P i w = 0 := by
  classical
  have hfin : (minimalPrimes (HolGerm (ComplexModel n) ⧸ ID)).Finite :=
    minimalPrimes.finite_of_isNoetherianRing _
  let M := hfin.toFinset
  have hσ : ∀ σ : (P : M) → Fin (t P), ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      w ∈ D → ∏ P : M, π P (σ P) w = 0 := by
    intro σ
    let a : HolGerm (ComplexModel n) ⧸ ID :=
      ∏ P : M, Ideal.Quotient.mk ID (HolGerm.mk (π P (σ P)) (hπ P (σ P)))
    have ha : a ∈ (⊥ : Ideal (HolGerm (ComplexModel n) ⧸ ID)).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      refine Ideal.mem_sInf.mpr fun P hPmin => ?_
      let P' : M := ⟨P, hfin.mem_toFinset.mpr hPmin⟩
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem (fun P : M => Ideal.Quotient.mk ID
        (HolGerm.mk (π P (σ P)) (hπ P (σ P)))) (Finset.mem_univ P')) (hP P hPmin _)
    obtain ⟨N, hN⟩ := ha
    have hdiff : ∀ᶠ w in 𝓝 (0 : ComplexModel n),
        DifferentiableAt ℂ (fun w => ∏ P : M, π P (σ P) w) w := by
      filter_upwards [(eventually_all_finset (Finset.univ : Finset M)).mpr
        fun P _ => hπ P (σ P)] with w hw
      exact (HasFDerivAt.finsetProd fun i hi => (hw i hi).hasFDerivAt).differentiableAt
    have hprod := mk_prod (Finset.univ : Finset M) (fun P => π P (σ P)) (fun P => hπ P (σ P)) hdiff
    have hmem : (HolGerm.mk (fun w => ∏ P : M, π P (σ P) w) hdiff) ^ N ∈ ID := by
      rw [hprod, ← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_prod]
      exact hN
    rw [← HolGerm.mk_pow] at hmem
    have hv := mem_vanishingIdeal_mk.mp (hID hmem)
    filter_upwards [hv] with w hw hwD
    exact pow_eq_zero_iff'.mp (hw hwD) |>.1
  have hall : ∀ᶠ w in 𝓝 (0 : ComplexModel n), ∀ σ : (P : M) → Fin (t P),
      w ∈ D → ∏ P : M, π P (σ P) w = 0 := eventually_all.mpr hσ
  filter_upwards [hall] with w hw hwD
  by_contra hne
  push Not at hne
  choose σ hσne using fun P : M => hne P (hfin.mem_toFinset.mp P.2)
  exact (Finset.prod_ne_zero_iff.mpr fun P _ => hσne P) (hw σ hwD)

/-- **Flat holomorphic map germs are open.**  Let `I_C ⊆ I(C)` contain local equations of `C`
(`0 ∈ C`), `I_D ⊆ I(D)`, and `G : (ℂ^m, 0) → (ℂ^n, 0)` holomorphic with `I_D ∘ G ⊆ I_C`.  If the
induced homomorphism `𝒪_n ⧸ I_D → 𝒪_m ⧸ I_C` is flat, then for every neighbourhood `U` of `0`,
`G(C ∩ U)` contains a neighbourhood of `0` in `D`. -/
theorem eventually_mem_image_of_flat (IC : Ideal (HolGerm (ComplexModel m)))
    (ID : Ideal (HolGerm (ComplexModel n))) (G : ComplexModel m → ComplexModel n)
    (hG : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ G z) (hG0 : G 0 = 0)
    (hcomap : ID ≤ IC.comap (compAlgHom G hG hG0).toRingHom)
    (C : Set (ComplexModel m)) (D : Set (ComplexModel n)) (hIC : IC ≤ vanishingIdeal C)
    (hID : ID ≤ vanishingIdeal D) (h0C : (0 : ComplexModel m) ∈ C)
    {q : ℕ} (c : Fin q → ComplexModel m → ℂ) (hc : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (c j) z)
    (hcI : ∀ j, HolGerm.mk (c j) (hc j) ∈ IC)
    (hcC : ∀ᶠ z in 𝓝 (0 : ComplexModel m), (∀ j, c j z = 0) → z ∈ C)
    (hflat : (Ideal.quotientMap IC (compAlgHom G hG hG0).toRingHom hcomap).Flat)
    (U : Set (ComplexModel m)) (hU : U ∈ 𝓝 0) :
    ∀ᶠ w in 𝓝 (0 : ComplexModel n), w ∈ D → w ∈ G '' (C ∩ U) := by
  classical
  -- the local rings
  have hICm : IC ≤ maximalIdeal (HolGerm (ComplexModel m)) := by
    intro g hg
    obtain ⟨F, hF, rfl⟩ := HolGerm.exists_eq_mk g
    rw [HolGerm.mem_maximalIdeal_iff, HolGerm.eval_mk]
    exact (mem_vanishingIdeal_mk.mp (hIC hg)).self_of_nhds h0C
  have hICt : IC ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hICm
  have hIDm : ID ≤ maximalIdeal (HolGerm (ComplexModel n)) := by
    intro g hg
    have h1 := hICm (hcomap hg)
    rw [HolGerm.mem_maximalIdeal_iff] at h1 ⊢
    change HolGerm.eval (compAlgHom G hG hG0 g) = 0 at h1
    rwa [eval_compAlgHom] at h1
  have hIDt : ID ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hIDm
  have : IsLocalRing (HolGerm (ComplexModel m) ⧸ IC) :=
    HironakaG10ChowFlatFibreParameters.isLocalRing_quotient hICt
  have : IsLocalRing (HolGerm (ComplexModel n) ⧸ ID) :=
    HironakaG10ChowFlatFibreParameters.isLocalRing_quotient hIDt
  have := isLocalHom_quotientMap_compAlgHom IC ID G hG hG0 hICt hcomap
  -- fibre parameters
  obtain ⟨s, -, hrad, hkey⟩ :=
    HironakaG10ChowFlatFibreParameters.exists_flat_fibre_parameters_of_ringHom _ hflat
  obtain ⟨k, ξ, hξ, hspan⟩ := exists_lift_finset IC s
  rw [hspan] at hrad hkey
  have hiso := eventually_eq_zero_of_isolated IC ID G hG hG0 hcomap C hIC ξ hξ hrad
  -- generators of the primes of `A`
  have hgen : ∀ P : Ideal (HolGerm (ComplexModel n) ⧸ ID), ∃ (t : ℕ)
      (π : Fin t → ComplexModel n → ℂ) (hπ : ∀ i, ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ (π i) w),
      P = Ideal.span (range fun i => Ideal.Quotient.mk ID (HolGerm.mk (π i) (hπ i))) := by
    intro P
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian P : P.FG)
    obtain ⟨t, π, hπ, hTeq⟩ := exists_lift_finset ID T
    refine ⟨t, π, hπ, ?_⟩
    rw [← hTeq]
    exact hT.symm
  choose t π hπ hPgen using hgen
  have hcov := eventually_exists_minimalPrime_vanish ID D hID t π hπ
    (fun P _ i => (hPgen P).ge (Ideal.subset_span ⟨i, rfl⟩))
  have hfin : (minimalPrimes (HolGerm (ComplexModel n) ⧸ ID)).Finite :=
    minimalPrimes.finite_of_isNoetherianRing _
  have hpieces : ∀ᶠ w in 𝓝 (0 : ComplexModel n), ∀ P ∈ minimalPrimes (HolGerm (ComplexModel n) ⧸ ID),
      w ∈ D → (∀ i, π P i w = 0) → w ∈ G '' (C ∩ U) := by
    refine (eventually_all_finite hfin).mpr fun P hP => ?_
    have hPprime : P.IsPrime := hP.1.1
    exact eventually_mem_image_of_prime IC ID G hG hG0 hcomap C D hID c hc hcI hcC ξ hξ hiso P
      (fun h hh => hkey P hPprime h hh) (π P) (hπ P) (hPgen P) U hU
  filter_upwards [hcov, hpieces] with w hw1 hw2 hwD
  obtain ⟨P, hPmin, hPw⟩ := hw1 hwD
  exact hw2 P hPmin hwD hPw

end Germ

end

end Hironaka.HironakaG10ChowFlatGermOpen
