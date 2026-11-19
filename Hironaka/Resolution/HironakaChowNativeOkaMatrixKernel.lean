import Hironaka.Coherence.OkaCoherence
import Hironaka.Resolution.HironakaSmoothCentreRealDomainActualSheafStalk
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! ONE finite relation matrix on ONE original open, exact on EVERY original
native scalar stalk. Oka supplies the all-nearby generators internally.
No reduction of the original whole module or ideal is performed.
Blueprint FIRST: hironaka-g10-native-oka-matrix-kernel.tex. -/
set_option autoImplicit false
noncomputable section

open Set Filter TopologicalSpace CategoryTheory Opposite
open scoped Topology Manifold ContDiff BigOperators

namespace Hironaka.HironakaChowNativeOkaMatrixKernel

open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf OkaGermBridge
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetRankLoci

private theorem section_holAt {n : ℕ} (U : Opens (ComplexModel n))
    (s : actualComplexSection (n := n) U) (y : ComplexModel n) (hy : y ∈ U) :
    HolAt (sectionExtension U s) y := by
  filter_upwards [sectionExtension_holomorphicAt U s y hy] with z hz
  exact mdifferentiableAt_iff_differentiableAt.mp hz

private theorem original_section_germ_chart {n : ℕ} (U : Opens (ComplexModel n))
    (s : actualComplexSection (n := n) U) (y : ComplexModel n) (hy : y ∈ U) :
    actualStalkChartEquiv y
        ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U y hy s) =
      germAt y (sectionExtension U s) := by
  rw [actualStalkChartEquiv_germ, germAt_of_holAt (section_holAt U s y hy)]
  change HolGerm.mk (fun z => sectionExtension U s (z + y))
    (translated_holomorphic y (section_holAt U s y hy)) = _
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => congrArg (sectionExtension U s) (add_comm z y)

private def sectionOfHolOn {n : ℕ} (V : Opens (ComplexModel n))
    (f : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f V) :
    actualComplexSection (n := n) V :=
  ⟨fun z : V => f z, by
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (fun z : V => f z)
    intro z
    apply contMDiffAt_subtype_iff.mpr
    apply contMDiffAt_of_eventually_mdifferentiableAt
    filter_upwards [V.isOpen.mem_nhds z.property] with w hw
    exact mdifferentiableAt_iff_differentiableAt.mpr
      ((hf w hw).differentiableAt (V.isOpen.mem_nhds hw))⟩

private theorem sectionOfHolOn_germ_chart {n : ℕ} (V : Opens (ComplexModel n))
    (f : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f V)
    (y : ComplexModel n) (hy : y ∈ V) :
    actualStalkChartEquiv y
        ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ V y hy
          (sectionOfHolOn V f hf)) = germAt y f := by
  rw [original_section_germ_chart]
  apply (germAt_eq_germAt_iff
    (section_holAt V (sectionOfHolOn V f hf) y hy)
    (holAt_of_differentiableOn V.isOpen hf hy)).mpr
  filter_upwards [V.isOpen.mem_nhds hy] with z hz
  rw [sectionExtension_apply V (sectionOfHolOn V f hf) z hz]
  rfl

private theorem germAt_fintype_sum {n : ℕ} {I : Type} [Fintype I]
    {f : I → ComplexModel n → ℂ} {y : ComplexModel n} (hf : ∀ i, HolAt (f i) y) :
    germAt y (fun z => ∑ i, f i z) = ∑ i, germAt y (f i) := by
  exact germAt_sum Finset.univ (fun i _ => hf i)

/-- Ordinary original holomorphic sections produce ONE relation matrix before
ALL nearby points, exact for the SAME original whole native scalar stalks. -/
theorem exists_relation_matrix_all_original_stalks {n r q : ℕ}
    (U : Opens (ComplexModel n)) (p : ComplexModel n) (hp : p ∈ U)
    (B : Matrix (Fin r) (Fin q) (actualComplexSection (n := n) U)) :
    ∃ (V : Opens (ComplexModel n)) (hVU : V ≤ U) (_hpV : p ∈ V) (s : ℕ)
      (C : Matrix (Fin q) (Fin s) (actualComplexSection (n := n) V)),
      (B.map ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.map
        (homOfLE hVU).op).hom) * C = 0 ∧
      ∀ (y : ComplexModel n) (hy : y ∈ V),
        (Matrix.toLin' (C.map
          ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ V y hy).hom)).range =
        LinearMap.ker (Matrix.toLin' (B.map
          ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ U y
            (hVU hy)).hom)) := by
  classical
  let b (i : Fin r) (j : Fin q) := sectionExtension U (B i j)
  have hb (i : Fin r) (j : Fin q) : HolAt (b i j) p := section_holAt U (B i j) p hp
  obtain ⟨W,hWo,hpW,μ,hμ,σ,hσhol,hσrel,hσgen⟩ :=
    OkaCoherence.okaProperty_euclidean n (Fin r) (Fin q) b p hb
  let : Fintype μ := hμ
  let e := Fintype.equivFin μ
  let V : Opens (ComplexModel n) := ⟨(U : Set (ComplexModel n)) ∩ W,U.isOpen.inter hWo⟩
  have hVU : V ≤ U := fun _ hz => hz.1
  have hpV : p ∈ V := ⟨hp,hpW⟩
  let σ' (k : Fin (Fintype.card μ)) (j : Fin q) := σ (e.symm k) j
  have hσ' (k : Fin (Fintype.card μ)) (j : Fin q) : DifferentiableOn ℂ (σ' k j) V :=
    (hσhol (e.symm k) j).mono (fun _ hz => hz.2)
  let C : Matrix (Fin q) (Fin (Fintype.card μ)) (actualComplexSection (n := n) V) :=
    fun j k => sectionOfHolOn V (σ' k j) (hσ' k j)
  let R := actualComplexStructureSheaf (n := n) (ComplexModel n)
  let BV : Matrix (Fin r) (Fin q) (actualComplexSection (n := n) V) :=
    B.map (R.presheaf.map (homOfLE hVU).op).hom
  have hBC : BV * C = 0 := by
    ext i k
    apply ContMDiffMap.ext
    intro z
    let ev : actualComplexSection (n := n) V →+* ℂ := ContMDiffMap.evalRingHom z
    change ev ((BV * C) i k) = 0
    have hsum : ev (∑ j : Fin q, BV i j * C j k) =
        ∑ j : Fin q, ev (BV i j * C j k) :=
      map_sum ev (fun j : Fin q => BV i j * C j k) Finset.univ
    rw [Matrix.mul_apply,hsum]
    simp only [ev.map_mul]
    change ∑ j, (B i j) ⟨z.val,hVU z.property⟩ * σ' k j z.val = 0
    have h := hσrel (e.symm k) i z.val z.property.2
    calc
      _ = ∑ j, σ' k j z.val * (B i j) ⟨z.val,hVU z.property⟩ :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = 0 := by
        simpa only [b,σ',sectionExtension_apply U (B i _) z.val (hVU z.property)] using h
  refine ⟨V,hVU,hpV,Fintype.card μ,C,hBC,?_⟩
  intro y hy
  let E := actualStalkChartEquiv (n := n) y
  let Bg := B.map (R.presheaf.germ U y (hVU hy)).hom
  let Cg := C.map (R.presheaf.germ V y hy).hom
  have hBg (i : Fin r) (j : Fin q) : E (Bg i j) = germAt y (b i j) :=
    original_section_germ_chart U (B i j) y (hVU hy)
  have hCg (j : Fin q) (k : Fin (Fintype.card μ)) :
      E (Cg j k) = germAt y (σ' k j) :=
    sectionOfHolOn_germ_chart V (σ' k j) (hσ' k j) y hy
  have hprod : Bg * Cg = 0 := by
    have hh := congrArg (fun M : Matrix (Fin r) (Fin (Fintype.card μ))
      (actualComplexSection (n := n) V) => M.map (R.presheaf.germ V y hy).hom) hBC
    rw [Matrix.map_mul] at hh
    have hzero : (0 : Matrix (Fin r) (Fin (Fintype.card μ))
        (actualComplexSection (n := n) V)).map (R.presheaf.germ V y hy).hom = 0 := by
      ext i j
      change (R.presheaf.germ V y hy).hom 0 = 0
      exact (R.presheaf.germ V y hy).hom.map_zero
    have hBV : BV.map (R.presheaf.germ V y hy).hom = Bg := by
      ext i j
      exact TopCat.Presheaf.germ_res_apply R.presheaf (homOfLE hVU) y hy (B i j)
    rw [hBV,hzero] at hh
    exact hh
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.toLin'_mul,hprod]
    exact map_zero _
  · intro a ha
    choose α hα hαg using fun j : Fin q => exists_germAt_eq (E (a j)) y
    have hrelation : IsRelationAt b y α := by
      refine ⟨hα,?_⟩
      intro i
      have hbY (j : Fin q) : HolAt (b i j) y := section_holAt U (B i j) y (hVU hy)
      apply (germAt_eq_zero_iff (HolAt.fintype_sum (fun j => (hα j).mul (hbY j)))).mp
      rw [germAt_fintype_sum (fun j => (hα j).mul (hbY j))]
      have hai := congrFun (show Matrix.toLin' Bg a = 0 from ha) i
      have hei := congrArg E hai
      simp only [Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Pi.zero_apply,map_sum,map_mul,map_zero] at hei
      calc
        ∑ j, germAt y (fun z => α j z * b i j z) =
            ∑ j, E (a j) * E (Bg i j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [germAt_mul (hα j) (hbY j),hαg j,← hBg i j]
        _ = ∑ j, E (Bg i j) * E (a j) :=
          Finset.sum_congr rfl (fun j _ => mul_comm _ _)
        _ = 0 := hei
    obtain ⟨γ,hγ,hαγ⟩ := hσgen y hy.2 α hrelation
    let c (k : Fin (Fintype.card μ)) := E.symm (germAt y (γ (e.symm k)))
    refine ⟨c,?_⟩
    funext j
    apply E.injective
    change E (∑ k, Cg j k * c k) = E (a j)
    rw [map_sum]
    calc
      ∑ k, E (Cg j k * c k) =
          ∑ k, germAt y (σ' k j) * germAt y (γ (e.symm k)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [map_mul,hCg j k]
        exact congrArg (fun z => germAt y (σ' k j) * z) (E.apply_symm_apply _)
      _ = ∑ k : μ, germAt y (fun z => γ k z * σ k j z) := by
        rw [← Equiv.sum_comp e.symm]
        apply Finset.sum_congr rfl
        intro k _
        rw [germAt_mul (hγ (e.symm k))
          (holAt_of_differentiableOn hWo (hσhol (e.symm k) j) hy.2)]
        exact mul_comm _ _
      _ = germAt y (fun z => ∑ k : μ, γ k z * σ k j z) :=
        (germAt_fintype_sum (fun k => (hγ k).mul
          (holAt_of_differentiableOn hWo (hσhol k j) hy.2))).symm
      _ = germAt y (α j) :=
        ((germAt_eq_germAt_iff (hα j)
          (HolAt.fintype_sum (fun k => (hγ k).mul
            (holAt_of_differentiableOn hWo (hσhol k j) hy.2)))).mpr (hαγ j)).symm
      _ = E (a j) := hαg j

end Hironaka.HironakaChowNativeOkaMatrixKernel
