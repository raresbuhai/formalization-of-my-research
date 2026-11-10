module

public import BHSV25.Alg.Partition
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Partitions into three parts

Facts for [BHSV25, Theorem 7.9 and Corollary 1.4] about partitions of the vertices into `3` parts:

* **accounting with exceptions** (`BHSV25.Alg.three_sub_le_sum_max`): if every vertex outside `S`
  lies in the independent set `I_a` of its cluster `a`, the rounding colors at least `n - 2 |S|`
  vertices;
* **large parts** (`BHSV25.Alg.three_card_part_ge`): if every part has at most `B` vertices, each
  has at least `n - 2 B`;
* **separated rows** (the claim in the proof of Theorem 7.9, `BHSV25.Alg.three_rowSep`): the
  computation of Lemmas 7.7 and 7.8, done directly on the model `M`, whose diagonal is small rather
  than `0`. With `E_ab = |V_a| M_ab`, which is symmetric with row sums `|V_a|`, the three parts
  `a, b, c` satisfy `2 E_ab = |V_a| + |V_b| - |V_c| - E_aa - E_bb + E_cc`; if the parts have
  between `g n` and `(1/2 - g + λ) n` vertices and the weight inside them is at most `2 λ n`, then
  `M_ab ≥ g - 2 λ` for `a ≠ b` while `M_bb ≤ 2 λ / g`, so `‖M_a - M_b‖ ≥ g / 2`;
* **the classes of a partial coloring** are independent sets (`BHSV25.Alg.threeClass`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Filter Topology Turing.MultiTapeTM Matrix

/-! ### Counting the colored vertices -/

section Counting

variable (G : Graph)

/-- **Accounting with a set of exceptions**: if every vertex outside `S` lies in the independent
set `I_a` of its part `a`, then `∑_a max(0, |R_a ∩ I_a| - |R_a \ I_a|) ≥ n - 2 |S|`. -/
theorem three_sub_le_sum_max {m : ℕ} (p : List ℕ) (hp : ∀ v : Fin G.1, p.getD v m < m)
    (I : ℕ → Finset (Fin G.1)) (S : Finset (Fin G.1)) (hS : ∀ v, v ∉ S → v ∈ I (p.getD v m)) :
    (G.1 : ℝ) - 2 * S.card ≤ ∑ a ∈ range m, max 0
      (((classSet G m p a ∩ I a).card : ℝ) - (classSet G m p a \ I a).card) := by
  have hdisj : (↑(range m) : Set ℕ).PairwiseDisjoint (classSet G m p) := by
    intro a _ b _ hab
    refine disjoint_left.2 fun v hva hvb ↦ hab ?_
    rw [classSet, mem_filter] at hva hvb
    exact hva.2.symm.trans hvb.2
  have hdisj' : (↑(range m) : Set ℕ).PairwiseDisjoint (fun a ↦ classSet G m p a \ I a) :=
    hdisj.mono fun a ↦ sdiff_subset
  have hR : ∑ a ∈ range m, ((classSet G m p a).card : ℝ) = G.1 := by
    rw [← Nat.cast_sum, ← card_biUnion hdisj]
    have : (range m).biUnion (classSet G m p) = univ := by
      ext v
      simp only [mem_biUnion, mem_range, classSet, mem_filter, mem_univ, true_and, iff_true]
      exact ⟨_, hp v, rfl⟩
    rw [this, card_univ, Fintype.card_fin]
  have hD : ∑ a ∈ range m, ((classSet G m p a \ I a).card : ℝ) ≤ S.card := by
    rw [← Nat.cast_sum, ← card_biUnion hdisj']
    refine Nat.cast_le.2 (card_le_card fun v hv ↦ ?_)
    rw [mem_biUnion] at hv
    obtain ⟨a, -, hv⟩ := hv
    obtain ⟨hv1, hv2⟩ := mem_sdiff.1 hv
    rw [classSet, mem_filter] at hv1
    by_contra hvS
    have := hS v hvS
    rw [hv1.2] at this
    exact hv2 this
  have hsplit : ∀ a, ((classSet G m p a ∩ I a).card : ℝ) - (classSet G m p a \ I a).card =
      (classSet G m p a).card - 2 * (classSet G m p a \ I a).card := by
    intro a
    have h' : ((classSet G m p a ∩ I a).card : ℝ) + (classSet G m p a \ I a).card =
        (classSet G m p a).card := by exact_mod_cast card_inter_add_card_sdiff _ _
    linarith only [h']
  calc (G.1 : ℝ) - 2 * S.card ≤ ∑ a ∈ range m, (((classSet G m p a).card : ℝ) -
        2 * (classSet G m p a \ I a).card) := by
        rw [sum_sub_distrib, ← mul_sum, hR]
        linarith only [hD]
    _ = ∑ a ∈ range m, (((classSet G m p a ∩ I a).card : ℝ) - (classSet G m p a \ I a).card) :=
        sum_congr rfl fun a _ ↦ (hsplit a).symm
    _ ≤ _ := sum_le_sum fun a _ ↦ le_max_right _ _

end Counting

/-! ### Partitions into three parts -/

section Three

variable {G : Graph}

/-- For two of the three parts, the third one. -/
theorem three_exists_third {a b : Fin 3} (hab : a ≠ b) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ ∀ f : Fin 3 → ℝ, ∑ j, f j = f a + f b + f c := by
  have key : ∀ a b : Fin 3, a ≠ b → ∃ c, c ≠ a ∧ c ≠ b := by decide
  have hcov : ∀ a b c x : Fin 3, a ≠ b → c ≠ a → c ≠ b → x = a ∨ x = b ∨ x = c := by decide
  obtain ⟨c, hca, hcb⟩ := key a b hab
  refine ⟨c, hca, hcb, fun f ↦ ?_⟩
  have huniv : (univ : Finset (Fin 3)) = {a, b, c} := by
    ext x
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    exact hcov a b c x hab hca hcb
  rw [huniv, sum_insert (by simp [hab, hca.symm]), sum_insert (by simp [hcb.symm]),
    sum_singleton, add_assoc]

/-- If every part has at most `B` vertices, every part has at least `n - 2 B`. -/
theorem three_card_part_ge (χ : Fin G.1 → Fin 3) {B : ℝ}
    (hup : ∀ a, ((part G χ a).card : ℝ) ≤ B) (a : Fin 3) :
    G.1 - 2 * B ≤ (part G χ a).card := by
  have h1 := sum_card_part (G := G) χ
  rw [← add_sum_erase _ _ (mem_univ a)] at h1
  have h2 : ∑ x ∈ univ.erase a, ((part G χ x).card : ℝ) ≤ ∑ _x ∈ univ.erase a, B :=
    sum_le_sum fun x _ ↦ hup x
  rw [sum_const, card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin, nsmul_eq_mul]
    at h2
  have h3 : ((3 - 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [h3] at h2
  linarith only [h1, h2]

open Classical in
/-- **Separated rows** (the claim in the proof of [BHSV25, Theorem 7.9]): if the three parts have
between `g n` and `(1/2 - g + λ) n` vertices and weight at most `2 λ n` inside them, then the rows
of the model are `g / 2`-separated, provided `2 λ + 2 λ / g ≤ g / 2`. -/
theorem three_rowSep {d : ℕ} (h : G.2.IsRegularOfDegree d) (hd : d ≠ 0) (hn : 0 < G.1)
    (χ : Fin G.1 → Fin 3) {g lam : ℝ} (hg : 0 < g) (hlam0 : 0 ≤ lam) (hgl : 2 * lam ≤ g)
    (hup : ∀ a, ((part G χ a).card : ℝ) ≤ (1 / 2 - g + lam) * G.1)
    (hlow : ∀ a, g * G.1 ≤ (part G χ a).card)
    (hint : intWt G χ ≤ 2 * lam * G.1) (hcond : 2 * lam + 2 * lam / g ≤ g / 2) (a b : Fin 3)
    (hab : a ≠ b) : (g / 2) ^ 2 ≤ ∑ j, (pmodel G χ a j - pmodel G χ b j) ^ 2 := by
  have hnR : (0 : ℝ) < G.1 := by exact_mod_cast hn
  obtain ⟨c, -, -, hsum⟩ := three_exists_third hab
  set E : Fin 3 → Fin 3 → ℝ := fun x y ↦ ∑ v ∈ part G χ x, wt G χ v y with hE
  have hrow : ∀ x, ∑ y, E x y = (part G χ x).card := by
    intro x
    simp only [hE]
    rw [sum_comm]
    simp [sum_wt h hd χ]
  have hsym : ∀ x y, E x y = E y x := fun x y ↦ sum_wt_comm χ x y
  have hdiag : ∑ x, E x x = intWt G χ := by
    rw [intWt, ← sum_part χ]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun v hv ↦ ?_
    rw [mem_part.1 hv]
  have hnn : ∀ x y, 0 ≤ E x y := fun x y ↦ sum_nonneg fun v _ ↦ wt_nonneg χ v y
  have hcard := sum_card_part (G := G) χ
  have hRa := hrow a
  have hRb := hrow b
  have hRc := hrow c
  rw [hsum] at hRa hRb hRc hdiag hcard
  have hsab := hsym a b
  have hsac := hsym a c
  have hsbc := hsym b c
  have hupc := hup c
  have hcc := hnn c c
  have haa := hnn a a
  -- the weight between `a` and `b`
  have hEab : (g - 2 * lam) * G.1 ≤ E a b := by
    linarith only [hRa, hRb, hRc, hdiag, hcard, hsab, hsac, hsbc, hupc, hcc, hint]
  -- the entries of the model
  have hpa : (0 : ℝ) < (part G χ a).card := lt_of_lt_of_le (mul_pos hg hnR) (hlow a)
  have hpb : (0 : ℝ) < (part G χ b).card := lt_of_lt_of_le (mul_pos hg hnR) (hlow b)
  have hpan : ((part G χ a).card : ℝ) ≤ G.1 := by
    have h1 := Nat.cast_nonneg (α := ℝ) (part G χ b).card
    have h2 := Nat.cast_nonneg (α := ℝ) (part G χ c).card
    linarith only [hcard, h1, h2]
  have hMab : g - 2 * lam ≤ pmodel G χ a b := by
    change g - 2 * lam ≤ E a b / (part G χ a).card
    rw [le_div_iff₀ hpa]
    have := mul_le_mul_of_nonneg_left hpan (by linarith only [hgl] : (0 : ℝ) ≤ g - 2 * lam)
    linarith only [this, hEab]
  have hMbb : pmodel G χ b b ≤ 2 * lam / g := by
    change E b b / (part G χ b).card ≤ 2 * lam / g
    rw [div_le_iff₀ hpb]
    have hEbb : E b b ≤ 2 * lam * G.1 := by
      have := hnn b b
      linarith only [hdiag, haa, hcc, hint]
    have hlam : 0 ≤ 2 * lam / g := by positivity
    have h1 := mul_le_mul_of_nonneg_left (hlow b) hlam
    have h2 : 2 * lam / g * (g * G.1) = 2 * lam * G.1 := by field_simp
    linarith only [h1, h2, hEbb]
  have hdiff : g / 2 ≤ pmodel G χ a b - pmodel G χ b b := by linarith only [hMab, hMbb, hcond]
  calc (g / 2) ^ 2 ≤ (pmodel G χ a b - pmodel G χ b b) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdiff 2
    _ ≤ ∑ j, (pmodel G χ a j - pmodel G χ b j) ^ 2 :=
        single_le_sum (f := fun j ↦ (pmodel G χ a j - pmodel G χ b j) ^ 2)
          (fun j _ ↦ sq_nonneg _) (mem_univ b)

end Three

/-! ### The clustering algorithm on balanced `3`-colorable expanders -/

section Main

variable (G : Graph)

/-- The class `a` of a partial `3`-coloring `c` (empty for `a ≥ 3`). -/
def threeClass (c : List ℕ) (a : ℕ) : Finset (Fin G.1) :=
  univ.filter fun v ↦ G.color 3 c v = a ∧ G.color 3 c v < 3

theorem isIndepSet_threeClass {c : List ℕ} (hc : G.IsPartialColoring 3 c) (a : ℕ) :
    G.2.IsIndepSet (threeClass G c a : Set (Fin G.1)) := by
  intro u hu v hv _ huv
  rw [mem_coe, threeClass, mem_filter] at hu hv
  exact hc u v huv hu.2.2 (hu.2.1.trans hv.2.1.symm)

theorem card_threeClass (c : List ℕ) {a : ℕ} (ha : a < 3) :
    (threeClass G c a).card = G.classSize 3 c a := by
  rw [threeClass, Graph.classSize]
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨And.left, fun h ↦ ⟨h, h ▸ ha⟩⟩

end Main

/-! ### The parameters -/

end Alg

end BHSV25
