module

public import BGHKLMM26.Hardness.DecoderSums
public import BGHKLMM26.Hardness.LTF
public import BGHKLMM26.Hardness.Sparsify

/-!
# The law of a decoded edge

A block of `L = 2t + R + Rb` uniform coins is read as two indices `r₁, r₂ < 2^t`, a point `x` and
numbers `zᵢ < 2^b` (`BGHKLMM26.Hard.sum_decE`); the decoded edge then has the law of the KKMO graph
(`BGHKLMM26.Hard.kkmoCut`) up to the bias of reading the indices modulo the number of constraints
(`BGHKLMM26.Hard.abs_avgDec_sub_le`).
-/

@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman

variable (P : Prm) (G : UGInstance)

/-- The edge decoded from a block of coins. -/
def decE (ω : Fin (P.blockLen G) → Bool) : ℕ × ℕ := edgeOfBlock P G (List.ofFn ω)

/-- The decoded edge in terms of the parts of the block. -/
theorem edgeOfBlock_append (l₁ l₂ l₃ l₄ : List Bool) (h₁ : l₁.length = P.tBits G)
    (h₂ : l₂.length = P.tBits G) (h₃ : l₃.length = P.R) :
    edgeOfBlock P G (l₁ ++ (l₂ ++ (l₃ ++ l₄))) =
      edgeOf G.2.2.2 P.R P.q (bitsVal l₁) (bitsVal l₂) (fun i ↦ l₃.getD i false)
        (fun i ↦ bitsVal ((l₄.drop (i * P.b)).take P.b)) := by
  unfold edgeOfBlock
  have e1 : (l₁ ++ (l₂ ++ (l₃ ++ l₄))).take (P.tBits G) = l₁ := by
    rw [← h₁, List.take_left]
  have e2 : ((l₁ ++ (l₂ ++ (l₃ ++ l₄))).drop (P.tBits G)).take (P.tBits G) = l₂ := by
    rw [← h₁, List.drop_left, h₁, ← h₂, List.take_left]
  have e3 (i : Fin P.R) : (l₁ ++ (l₂ ++ (l₃ ++ l₄))).getD (2 * P.tBits G + i) false =
      l₃.getD i false := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_left (by omega)]
    congr 2; omega
  have e4 : (l₁ ++ (l₂ ++ (l₃ ++ l₄))).drop (2 * P.tBits G + P.R) = l₄ := by
    rw [show 2 * P.tBits G + P.R = l₁.length + (l₂.length + l₃.length) by omega,
      ← List.drop_drop, List.drop_left, ← List.drop_drop, List.drop_left, List.drop_left]
  simp only [e1, e2, e3, e4]

theorem blockLen_eq : P.blockLen G = P.tBits G + (P.tBits G + (P.R + P.R * P.b)) := by
  unfold Prm.blockLen; ring

/-- **Reading a block**: a sum over the blocks is a sum over the indices, the point and the
numbers. -/
theorem sum_decE {M : Type*} [AddCommMonoid M] (φ : ℕ × ℕ → M) :
    ∑ ω : Fin (P.blockLen G) → Bool, φ (decE P G ω) =
      ∑ a₁ ∈ range (2 ^ P.tBits G), ∑ a₂ ∈ range (2 ^ P.tBits G), ∑ x : Fin P.R → Bool,
        ∑ z : Fin P.R → Fin (2 ^ P.b), φ (edgeOf G.2.2.2 P.R P.q a₁ a₂ x (fun i ↦ z i)) := by
  unfold decE
  have hc := sum_cast (M := M) (blockLen_eq P G) (fun l ↦ φ (edgeOfBlock P G l))
  rw [hc, sum_append (P.tBits G) _ (fun l ↦ φ (edgeOfBlock P G l))]
  have step2 : ∀ ω₁ : Fin (P.tBits G) → Bool,
      ∑ ω' : Fin (P.tBits G + (P.R + P.R * P.b)) → Bool,
          φ (edgeOfBlock P G (List.ofFn ω₁ ++ List.ofFn ω')) =
        ∑ ω₂ : Fin (P.tBits G) → Bool, ∑ ω₃ : Fin P.R → Bool, ∑ ω₄ : Fin (P.R * P.b) → Bool,
          φ (edgeOfBlock P G
            (List.ofFn ω₁ ++ (List.ofFn ω₂ ++ (List.ofFn ω₃ ++ List.ofFn ω₄)))) := by
    intro ω₁
    rw [sum_append (P.tBits G) _ (fun l ↦ φ (edgeOfBlock P G (List.ofFn ω₁ ++ l)))]
    refine sum_congr rfl fun ω₂ _ ↦ ?_
    exact sum_append P.R _ (fun l ↦ φ (edgeOfBlock P G (List.ofFn ω₁ ++ (List.ofFn ω₂ ++ l))))
  simp only [step2]
  have hR (x : Fin P.R → Bool) : (fun i : Fin P.R ↦ (List.ofFn x).getD i false) = x := by
    funext i; simp [List.getD_eq_getElem?_getD]
  simp only [edgeOfBlock_append P G _ _ _ _ (List.length_ofFn) (List.length_ofFn)
    (List.length_ofFn), hR]
  rw [sum_bitsVal (P.tBits G) (fun a₁ ↦ ∑ ω₂ : Fin (P.tBits G) → Bool, ∑ x : Fin P.R → Bool,
    ∑ ω₄ : Fin (P.R * P.b) → Bool, φ (edgeOf G.2.2.2 P.R P.q a₁ (bitsVal (List.ofFn ω₂)) x
      (fun i ↦ bitsVal (((List.ofFn ω₄).drop (i * P.b)).take P.b))))]
  refine sum_congr rfl fun a₁ _ ↦ ?_
  rw [sum_bitsVal (P.tBits G) (fun a₂ ↦ ∑ x : Fin P.R → Bool,
    ∑ ω₄ : Fin (P.R * P.b) → Bool, φ (edgeOf G.2.2.2 P.R P.q a₁ a₂ x
      (fun i ↦ bitsVal (((List.ofFn ω₄).drop (i * P.b)).take P.b))))]
  refine sum_congr rfl fun a₂ _ ↦ sum_congr rfl fun x _ ↦ ?_
  exact sum_blocks_bitsVal P.R P.b (fun z ↦ φ (edgeOf G.2.2.2 P.R P.q a₁ a₂ x z))

/-! ### The decoded law as correlated averages -/

/-- The correlation of the decoder, `ρ = 1 - 2q/2^b`. -/
noncomputable def Prm.rho : ℝ := 1 - 2 * P.q / 2 ^ P.b

variable {P G}

/-- The average of `φ` over `ρ`-correlated pairs on the edge between the tables of the
constraints `c₁` and `c₂`. -/
noncomputable def pairAvg (φ : ℕ × ℕ → ℝ) (c₁ c₂ : UGConstraint) : ℝ :=
  corrAverage P.rho P.R fun x y ↦ φ (vtx c₁.1.2 (permCube c₁.2 x), vtx c₂.1.2 (permCube c₂.2 y))

variable (P G) in
/-- The first constraint read from the index `a₁`. -/
def con₁ (a₁ : ℕ) : UGConstraint := G.2.2.2.getD (a₁ % G.2.2.2.length) default

variable (P G) in
/-- The second constraint read from the index `a₂`, at the left vertex of the first. -/
def con₂ (a₁ a₂ : ℕ) : UGConstraint :=
  (nbrs G.2.2.2 (con₁ G a₁).1.1).getD (a₂ % (nbrs G.2.2.2 (con₁ G a₁).1.1).length) default

/-- **The decoded law**: the average over blocks is the average over the two indices of the
correlated averages. -/
theorem avg_decE (hq : P.q ≤ 2 ^ P.b) (φ : ℕ × ℕ → ℝ) :
    (∑ ω : Fin (P.blockLen G) → Bool, φ (decE P G ω)) / 2 ^ P.blockLen G =
      (∑ a₁ ∈ range (2 ^ P.tBits G), ∑ a₂ ∈ range (2 ^ P.tBits G),
        pairAvg (P := P) φ (con₁ G a₁) (con₂ G a₁ a₂)) / (2 ^ P.tBits G * 2 ^ P.tBits G) := by
  rw [sum_decE]
  have hin (a₁ a₂ : ℕ) : ∑ x : Fin P.R → Bool, ∑ z : Fin P.R → Fin (2 ^ P.b),
      φ (edgeOf G.2.2.2 P.R P.q a₁ a₂ x (fun i ↦ z i)) =
        2 ^ P.R * (2 ^ P.b) ^ P.R * pairAvg (P := P) φ (con₁ G a₁) (con₂ G a₁ a₂) := by
    rw [pairAvg, Prm.rho, ← sum_flip_eq_corrAverage P.b P.q hq P.R, mul_div_cancel₀ _
      (by positivity)]
    rfl
  simp only [hin, ← Finset.mul_sum]
  have hpow : (2 : ℝ) ^ P.blockLen G =
      2 ^ P.R * (2 ^ P.b) ^ P.R * (2 ^ P.tBits G * 2 ^ P.tBits G) := by
    rw [Prm.blockLen, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1; ring
  rw [hpow, mul_div_mul_left _ _ (by positivity)]

/-- A list sum as a sum over the indices. -/
theorem list_sum_map_eq {α : Type*} [Inhabited α] (l : List α) (g : α → ℝ) :
    (l.map g).sum = ∑ j ∈ range l.length, g (l.getD j default) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']
    simp [add_comm]

theorem abs_pairAvg_le (hq : P.q ≤ 2 ^ P.b) {φ : ℕ × ℕ → ℝ} {B : ℝ} (hB : ∀ e, |φ e| ≤ B)
    (c₁ c₂ : UGConstraint) : |pairAvg (P := P) φ c₁ c₂| ≤ B := by
  have hρ : P.rho ∈ Set.Icc (-1 : ℝ) 1 := by
    have h2 : (0 : ℝ) < 2 ^ P.b := by positivity
    have hq' : (P.q : ℝ) ≤ 2 ^ P.b := by exact_mod_cast hq
    have h0 : 0 ≤ 2 * (P.q : ℝ) / 2 ^ P.b := by positivity
    have h1 : 2 * (P.q : ℝ) / 2 ^ P.b ≤ 2 := by
      rw [div_le_iff₀ h2]; linarith
    constructor <;> simp only [Prm.rho] <;> linarith
  have hc (c : ℝ) : corrAverage P.rho P.R (fun _ _ ↦ c) = c := by
    have := corrAverage_fst P.rho P.R (fun _ ↦ c)
    rw [Fintype.expect_const] at this
    exact this
  rw [abs_le]
  constructor
  · have := corrAverage_mono hρ P.R (F := fun _ _ ↦ -B) (G := fun x y ↦
      φ (vtx c₁.1.2 (permCube c₁.2 x), vtx c₂.1.2 (permCube c₂.2 y)))
      fun x y ↦ (abs_le.1 (hB _)).1
    rw [hc] at this
    exact this
  · have := corrAverage_mono hρ P.R (G := fun _ _ ↦ B) (F := fun x y ↦
      φ (vtx c₁.1.2 (permCube c₁.2 x), vtx c₂.1.2 (permCube c₂.2 y)))
      fun x y ↦ (abs_le.1 (hB _)).2
    rw [hc] at this
    exact this

/-- The exact law of the KKMO graph: a uniform constraint, a uniform constraint at its left
vertex, and correlated points. -/
noncomputable def avgExact (φ : ℕ × ℕ → ℝ) : ℝ :=
  (G.2.2.2.map fun c₁ ↦ ((nbrs G.2.2.2 c₁.1.1).map fun c₂ ↦
      pairAvg (P := P) φ c₁ c₂).sum / (nbrs G.2.2.2 c₁.1.1).length).sum / G.2.2.2.length

theorem mem_nbrs_self {cs : List UGConstraint} {c : UGConstraint} (hc : c ∈ cs) :
    c ∈ nbrs cs c.1.1 := by
  simp [nbrs, hc]

theorem con₁_mem (hcs : G.2.2.2 ≠ []) (a₁ : ℕ) : con₁ G a₁ ∈ G.2.2.2 := by
  unfold con₁
  have hpos : 0 < G.2.2.2.length := List.length_pos_iff.2 hcs
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ hpos), Option.getD_some]
  exact List.getElem_mem _

theorem nbrs_length_pos (hcs : G.2.2.2 ≠ []) (a₁ : ℕ) :
    0 < (nbrs G.2.2.2 (con₁ G a₁).1.1).length :=
  List.length_pos_of_mem (mem_nbrs_self (con₁_mem hcs a₁))

theorem nbrs_length_le (cs : List UGConstraint) (u : ℕ) : (nbrs cs u).length ≤ cs.length :=
  List.length_filter_le _ _

/-- **Total variation**: the decoded law is within `2 |cs| B / 2^t` of the exact law, for `φ`
bounded by `B`. -/
theorem abs_avgDec_sub_le (hq : P.q ≤ 2 ^ P.b) (hcs : G.2.2.2 ≠ []) {φ : ℕ × ℕ → ℝ} {B : ℝ}
    (hB : ∀ e, |φ e| ≤ B) :
    |(∑ ω : Fin (P.blockLen G) → Bool, φ (decE P G ω)) / 2 ^ P.blockLen G -
        avgExact (P := P) (G := G) φ| ≤ 2 * G.2.2.2.length * B / 2 ^ P.tBits G := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (0, 0))
  set E := G.2.2.2.length with hE
  have hEpos : 0 < E := List.length_pos_iff.2 hcs
  set t := P.tBits G
  -- the inner averages, over `a₂` and over the exact second constraint
  let h₂ : ℕ → ℝ := fun j ↦ (∑ a₂ ∈ range (2 ^ t),
    pairAvg (P := P) φ (con₁ G j) (con₂ G j a₂)) / 2 ^ t
  let h₁ : ℕ → ℝ := fun j ↦ (∑ k ∈ range (nbrs G.2.2.2 (con₁ G j).1.1).length,
    pairAvg (P := P) φ (con₁ G j) ((nbrs G.2.2.2 (con₁ G j).1.1).getD k default)) /
      (nbrs G.2.2.2 (con₁ G j).1.1).length
  have hcon₁ (a : ℕ) : con₁ G (a % E) = con₁ G a := by
    simp only [con₁, ← hE, Nat.mod_mod]
  have hcon₂ (a a₂ : ℕ) : con₂ G (a % E) a₂ = con₂ G a a₂ := by
    simp only [con₂, hcon₁]
  have hdec : (∑ a₁ ∈ range (2 ^ t), ∑ a₂ ∈ range (2 ^ t),
      pairAvg (P := P) φ (con₁ G a₁) (con₂ G a₁ a₂)) / (2 ^ t * 2 ^ t) =
        (∑ a₁ ∈ range (2 ^ t), h₂ (a₁ % E)) / 2 ^ t := by
    simp only [h₂, hcon₁, hcon₂]
    rw [← Finset.sum_div, div_div]
  have hexact : avgExact (P := P) (G := G) φ = (∑ j ∈ range E, h₁ j) / E := by
    unfold avgExact
    rw [list_sum_map_eq]
    congr 1
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j < E := mem_range.1 hj
    have hc : G.2.2.2.getD j default = con₁ G j := by
      simp only [con₁, ← hE, Nat.mod_eq_of_lt hj']
    simp only [h₁, hc, list_sum_map_eq]
  have hh₂ : ∀ j, |h₂ j| ≤ B := by
    intro j
    simp only [h₂]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ t), div_le_iff₀ (by positivity)]
    calc |∑ a₂ ∈ range (2 ^ t), pairAvg (P := P) φ (con₁ G j) (con₂ G j a₂)|
        ≤ ∑ a₂ ∈ range (2 ^ t), |pairAvg (P := P) φ (con₁ G j) (con₂ G j a₂)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a₂ ∈ range (2 ^ t), B := Finset.sum_le_sum fun _ _ ↦ abs_pairAvg_le hq hB _ _
      _ = B * 2 ^ t := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]; push_cast; ring
  have hh₂₁ : ∀ j, |h₂ j - h₁ j| ≤ E * B / 2 ^ t := by
    intro j
    have hM := nbrs_length_pos hcs j
    have := abs_sum_mod_sub_le t _ hM
      (fun k ↦ pairAvg (P := P) φ (con₁ G j) ((nbrs G.2.2.2 (con₁ G j).1.1).getD k default))
      (B := B) fun k _ ↦ abs_pairAvg_le hq hB _ _
    refine le_trans (le_of_eq_of_le ?_ this) ?_
    · rfl
    · have hle : ((nbrs G.2.2.2 (con₁ G j).1.1).length : ℝ) ≤ E := by
        exact_mod_cast nbrs_length_le _ _
      gcongr
  rw [hdec.symm.trans (avg_decE hq φ).symm |>.symm, hexact]
  have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
  have h1 := abs_sum_mod_sub_le t E hEpos h₂ (B := B) fun j _ ↦ hh₂ j
  have h2 : |(∑ j ∈ range E, h₂ j) / E - (∑ j ∈ range E, h₁ j) / E| ≤ E * B / 2 ^ t := by
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hEr, div_le_iff₀ hEr]
    calc |∑ j ∈ range E, (h₂ j - h₁ j)| ≤ ∑ j ∈ range E, |h₂ j - h₁ j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range E, E * B / 2 ^ t := Finset.sum_le_sum fun j _ ↦ hh₂₁ j
      _ = E * B / 2 ^ t * E := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]
  calc |(∑ a₁ ∈ range (2 ^ t), h₂ (a₁ % E)) / 2 ^ t - (∑ j ∈ range E, h₁ j) / E|
      ≤ |(∑ a₁ ∈ range (2 ^ t), h₂ (a₁ % E)) / 2 ^ t - (∑ j ∈ range E, h₂ j) / E| +
          |(∑ j ∈ range E, h₂ j) / E - (∑ j ∈ range E, h₁ j) / E| := abs_sub_le _ _ _
    _ ≤ E * B / 2 ^ t + E * B / 2 ^ t := add_le_add h1 h2
    _ = 2 * E * B / 2 ^ t := by ring

/-! ### Grouping constraints -/

/-- Group a list sum by a key below `m`. -/
theorem list_sum_group {α : Type*} (k : α → ℕ) (l : List α) (m : ℕ) (hm : ∀ c ∈ l, k c < m)
    (g : α → ℝ) :
    (l.map g).sum = ∑ u ∈ range m, ((l.filter fun c ↦ k c = u).map g).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun c' hc' ↦ hm c' (List.mem_cons_of_mem _ hc'))]
    have h (u : ℕ) : (((c :: l).filter fun c ↦ k c = u).map g).sum =
        (if k c = u then g c else 0) + ((l.filter fun c ↦ k c = u).map g).sum := by
      by_cases hu : k c = u <;> simp [hu]
    simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, mem_range,
      hm c (List.mem_cons_self ..), ite_true]

/-- **The second constraint is uniform**: averaging over the constraints at the left vertex of a
uniform constraint gives the uniform average over constraints. -/
theorem list_sum_nbrs_avg (cs : List UGConstraint) (m : ℕ) (hm : ∀ c ∈ cs, c.1.1 < m)
    (g : UGConstraint → ℝ) :
    (cs.map fun c₁ ↦ ((nbrs cs c₁.1.1).map g).sum / (nbrs cs c₁.1.1).length).sum =
      (cs.map g).sum := by
  rw [list_sum_group (fun c ↦ c.1.1) cs m hm, list_sum_group (fun c ↦ c.1.1) cs m hm g]
  refine sum_congr rfl fun u _ ↦ ?_
  have hmem : ∀ c₁ ∈ cs.filter (fun c ↦ c.1.1 = u), c₁.1.1 = u := fun c₁ hc₁ ↦ by
    simpa using (List.mem_filter.1 hc₁).2
  rw [List.map_congr_left (g := fun _ ↦ ((nbrs cs u).map g).sum / (nbrs cs u).length)
    (fun c₁ hc₁ ↦ by rw [hmem c₁ hc₁]), List.map_const', List.sum_replicate, nsmul_eq_mul]
  change ((nbrs cs u).length : ℝ) * (((nbrs cs u).map g).sum / (nbrs cs u).length) =
    ((nbrs cs u).map g).sum
  by_cases h0 : (nbrs cs u).length = 0
  · rw [List.length_eq_zero_iff.1 h0]; simp
  · field_simp

/-- In a good instance with constraints, every right vertex lies on `D ≥ 1` constraints, and
there are `|V| D` constraints. -/
theorem exists_right_degree {R : ℕ} {G : UGInstance} (hG : UGValid G ∧ G.2.2.1 = R ∧ UGSimple G ∧
    BiRegular G) (hcs : G.2.2.2 ≠ []) :
    ∃ D : ℕ, 0 < D ∧ G.2.2.2.length = G.2.1 * D ∧
      ∀ v, (G.2.2.2.filter fun c ↦ c.1.2 = v).length ≤ D := by
  obtain ⟨D, hD⟩ := hG.2.2.2.2
  have hval := hG.1
  have hlt : ∀ c ∈ G.2.2.2, c.1.2 < G.2.1 := fun c hc ↦ (hval c hc).2.1
  have hlen : G.2.2.2.length = G.2.1 * D := by
    have := list_sum_group (fun c : UGConstraint ↦ c.1.2) G.2.2.2 G.2.1 hlt (fun _ ↦ (1 : ℝ))
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at this
    rw [Finset.sum_congr rfl fun v hv ↦ by rw [hD v (mem_range.1 hv)], sum_const, card_range,
      nsmul_eq_mul] at this
    exact_mod_cast this
  refine ⟨D, Nat.pos_of_ne_zero fun h0 ↦ hcs ?_, hlen, fun v ↦ ?_⟩
  · rw [h0, mul_zero] at hlen; exact List.length_eq_zero_iff.1 hlen
  · by_cases hv : v < G.2.1
    · rw [hD v hv]
    · rw [List.filter_eq_nil_iff.2 fun c hc ↦ by
        have := hlt c hc; simp only [decide_eq_true_eq]; omega]
      exact Nat.zero_le _

/-! ### Points of the reduction graph -/

theorem cubeIdx_lt {R : ℕ} (x : Cube (Fin R)) : cubeIdx x < 2 ^ R := by
  have := bitsVal_lt (List.ofFn x); simpa [cubeIdx] using this

theorem cubeIdx_injective {R : ℕ} : Function.Injective (cubeIdx (R := R)) := fun x y h ↦
  List.ofFn_injective (bitsVal_injective (by simp) h)

theorem vtx_eq_iff {R : ℕ} {v a : ℕ} {x : Cube (Fin R)} :
    vtx v x = a ↔ v = a / 2 ^ R ∧ cubeIdx x = a % 2 ^ R := by
  have h := cubeIdx_lt x
  have hp : 0 < 2 ^ R := by positivity
  unfold vtx
  constructor
  · rintro rfl
    constructor
    · rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]
  · rintro ⟨h1, h2⟩
    rw [h1, h2, Nat.mul_comm, Nat.div_add_mod]

theorem vtx_lt {R : ℕ} {v n : ℕ} (hv : v < n) (x : Cube (Fin R)) : vtx v x < n * 2 ^ R := by
  have := cubeIdx_lt x
  unfold vtx
  calc v * 2 ^ R + cubeIdx x < v * 2 ^ R + 2 ^ R := by omega
    _ = (v + 1) * 2 ^ R := by ring
    _ ≤ n * 2 ^ R := Nat.mul_le_mul_right _ hv

/-- The points `x` whose permuted vertex is `a` are at most one. -/
theorem exists_point {R : ℕ} {π : List ℕ} (hπ : IsPermTable R π) (v a : ℕ) :
    ∃ x₀ : Cube (Fin R), ∀ x, vtx v (permCube π x) = a → v = a / 2 ^ R ∧ x = x₀ := by
  by_cases h : ∃ x : Cube (Fin R), vtx v (permCube π x) = a
  · obtain ⟨x₀, hx₀⟩ := h
    refine ⟨x₀, fun x hx ↦ ⟨(vtx_eq_iff.1 hx).1, ?_⟩⟩
    have h1 := (vtx_eq_iff.1 hx).2
    have h2 := (vtx_eq_iff.1 hx₀).2
    have : permCube π x = permCube π x₀ := cubeIdx_injective (h1.trans h2.symm)
    rw [← permCubeEquiv_apply hπ, ← permCubeEquiv_apply hπ] at this
    exact (permCubeEquiv hπ).injective this
  · push Not at h
    exact ⟨fun _ ↦ false, fun x hx ↦ absurd hx (h x)⟩

/-! ### Point masses of correlated pairs -/

theorem cons_eq_iff {n : ℕ} (a : Bool) (x : BitCube n) (x₀ : BitCube (n + 1)) :
    (Fin.cons a x : BitCube (n + 1)) = x₀ ↔ a = x₀ 0 ∧ x = Fin.tail x₀ := by
  conv_lhs => rw [← Fin.cons_self_tail x₀]
  exact Fin.cons_inj

/-- The probability of a pair of points under `t`-correlation. -/
theorem corrAverage_point (t : ℝ) (n : ℕ) (x₀ y₀ : BitCube n) :
    corrAverage t n (fun x y ↦ (if x = x₀ then (1 : ℝ) else 0) * (if y = y₀ then 1 else 0)) =
      ∏ i, bitPairWeight t (x₀ i) (y₀ i) := by
  induction n with
  | zero =>
    simp only [corrAverage, Finset.univ_eq_empty, prod_empty]
    rw [ite_eq_left (Subsingleton.elim _ _), ite_eq_left (Subsingleton.elim _ _), mul_one]
  | succ n ih =>
    rw [corrAverage]
    have h : (fun x y : BitCube n ↦ ∑ a : Bool, ∑ c : Bool, bitPairWeight t a c *
        ((if (Fin.cons a x : BitCube (n + 1)) = x₀ then (1 : ℝ) else 0) *
          (if (Fin.cons c y : BitCube (n + 1)) = y₀ then 1 else 0))) =
        fun x y ↦ bitPairWeight t (x₀ 0) (y₀ 0) *
          ((if x = Fin.tail x₀ then (1 : ℝ) else 0) * (if y = Fin.tail y₀ then 1 else 0)) := by
      funext x y
      simp only [cons_eq_iff, ite_and]
      rcases Bool.eq_false_or_eq_true (x₀ 0) with h0 | h0 <;>
        rcases Bool.eq_false_or_eq_true (y₀ 0) with h1 | h1 <;>
        simp [h0, h1]
    rw [h, corrAverage_const_mul, ih, Fin.prod_univ_succ]
    rfl

theorem bitPairWeight_le {t : ℝ} (a c : Bool) : bitPairWeight t a c ≤ (1 + |t|) / 4 := by
  have := le_abs_self t
  have := neg_abs_le t
  cases a <;> cases c <;> simp [bitPairWeight, sign] <;> linarith

theorem bitPairWeight_nonneg' {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) (a c : Bool) :
    0 ≤ bitPairWeight t a c :=
  bitPairWeight_nonneg ht a c

theorem corrAverage_point_le {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) (n : ℕ) (x₀ y₀ : BitCube n) :
    corrAverage t n (fun x y ↦ (if x = x₀ then (1 : ℝ) else 0) * (if y = y₀ then 1 else 0)) ≤
      ((1 + |t|) / 4) ^ n := by
  rw [corrAverage_point]
  calc ∏ i, bitPairWeight t (x₀ i) (y₀ i) ≤ ∏ _i : Fin n, (1 + |t|) / 4 :=
        Finset.prod_le_prod₀ (fun i _ ↦ bitPairWeight_nonneg' ht _ _)
          (fun i _ ↦ bitPairWeight_le _ _)
    _ = ((1 + |t|) / 4) ^ n := by rw [prod_const, card_univ, Fintype.card_fin]

/-! ### The marginals of the exact law -/

/-- The good instances: valid, simple, bi-regular, with `R` labels (as `BGHKLMM26.Hard.Good`). -/
def GoodI (R : ℕ) (G : UGInstance) : Prop := UGValid G ∧ G.2.2.1 = R ∧ UGSimple G ∧ BiRegular G

theorem isPermTable_of_mem {R : ℕ} {G : UGInstance} (hG : GoodI R G) {c : UGConstraint}
    (hc : c ∈ G.2.2.2) : IsPermTable R c.2 := by
  obtain ⟨-, -, h1, h2, h3⟩ := hG.1 c hc
  refine ⟨hG.2.1 ▸ h1, h2, fun a ha ↦ hG.2.1 ▸ h3 a ha⟩

theorem expect_vtx_le {R : ℕ} {π : List ℕ} (hπ : IsPermTable R π) (v a : ℕ) :
    𝔼 x : Cube (Fin R), (if vtx v (permCube π x) = a then (1 : ℝ) else 0) ≤
      (if v = a / 2 ^ R then 1 else 0) / 2 ^ R := by
  obtain ⟨x₀, hx₀⟩ := exists_point hπ v a
  calc 𝔼 x : Cube (Fin R), (if vtx v (permCube π x) = a then (1 : ℝ) else 0)
      ≤ 𝔼 x : Cube (Fin R), (if v = a / 2 ^ R then (1 : ℝ) else 0) *
          (if x = x₀ then (1 : ℝ) else 0) := by
        refine Finset.expect_le_expect fun x _ ↦ ?_
        by_cases h : vtx v (permCube π x) = a
        · obtain ⟨h1, h2⟩ := hx₀ x h
          have hl : (if vtx v (permCube π x) = a then (1 : ℝ) else 0) = 1 := ite_eq_left h
          have hr : (if v = a / 2 ^ R then (1 : ℝ) else 0) * (if x = x₀ then (1 : ℝ) else 0) = 1 :=
            by rw [ite_eq_left h1, ite_eq_left h2, mul_one]
          rw [hl, hr]
        · simp only [h, ↓reduceIte]; positivity
    _ = (if v = a / 2 ^ R then 1 else 0) / 2 ^ R := by
        rw [← Finset.mul_expect, Finset.expect_eq_sum_div_card, Finset.sum_ite_eq']
        simp [div_eq_mul_inv]

theorem list_sum_ite_eq {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map fun c ↦ if p c then (1 : ℝ) else 0).sum = (l.filter fun c ↦ p c).length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    by_cases h : p c <;> simp [h, ih]; ring

theorem list_sum_le_sum {α : Type*} {l : List α} {f g : α → ℝ} (h : ∀ c ∈ l, f c ≤ g c) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h c (List.mem_cons_self ..))
      (ih fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc'))

/-- The average over the constraints of a bound by the right vertex. -/
theorem list_avg_right_le {R : ℕ} {G : UGInstance} (hG : GoodI R G) (hcs : G.2.2.2 ≠ [])
    {A : UGConstraint → ℝ} {v₀ : ℕ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hA : ∀ c ∈ G.2.2.2, A c ≤ (if c.1.2 = v₀ then 1 else 0) * κ) :
    (G.2.2.2.map A).sum / G.2.2.2.length ≤ κ / G.2.1 := by
  obtain ⟨D, hD, hlen, hcount⟩ := exists_right_degree hG hcs
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hE : (0 : ℝ) < G.2.2.2.length := by exact_mod_cast List.length_pos_iff.2 hcs
  have hn : (0 : ℝ) < G.2.1 := by
    have : 0 < G.2.1 * D := hlen ▸ List.length_pos_iff.2 hcs
    exact_mod_cast Nat.pos_of_mul_pos_right this
  have h1 : (G.2.2.2.map A).sum ≤ D * κ := by
    calc (G.2.2.2.map A).sum ≤ (G.2.2.2.map fun c ↦ (if c.1.2 = v₀ then (1 : ℝ) else 0) * κ).sum :=
          list_sum_le_sum hA
      _ = (G.2.2.2.filter fun c ↦ c.1.2 = v₀).length * κ := by
          rw [← list_sum_ite_eq, ← List.sum_map_mul_right]
      _ ≤ D * κ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount v₀) hκ
  rw [div_le_div_iff₀ hE hn, show (G.2.2.2.length : ℝ) = G.2.1 * D by exact_mod_cast hlen]
  nlinarith

theorem rho_mem (hq : P.q ≤ 2 ^ P.b) : P.rho ∈ Set.Icc (-1 : ℝ) 1 := by
  have h2 : (0 : ℝ) < 2 ^ P.b := by positivity
  have hq' : (P.q : ℝ) ≤ 2 ^ P.b := by exact_mod_cast hq
  have h0 : 0 ≤ 2 * (P.q : ℝ) / 2 ^ P.b := by positivity
  have h1 : 2 * (P.q : ℝ) / 2 ^ P.b ≤ 2 := by
    rw [div_le_iff₀ h2]; linarith
  constructor <;> simp only [Prm.rho] <;> linarith

theorem list_avg_le_of_le {α : Type*} {l : List α} (hl : l ≠ []) {f : α → ℝ} {B : ℝ}
    (h : ∀ c ∈ l, f c ≤ B) : (l.map f).sum / l.length ≤ B := by
  have hpos : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff.2 hl
  rw [div_le_iff₀ hpos]
  calc (l.map f).sum ≤ (l.map fun _ ↦ B).sum := list_sum_le_sum h
    _ = B * l.length := by rw [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_comm]

/-- **The first end** of an edge of the exact law is `a` with probability at most `1/n`. -/
theorem avgExact_fst_le (hG : GoodI P.R G) (hcs : G.2.2.2 ≠ []) (a : ℕ) :
    avgExact (P := P) (G := G) (fun e ↦ if e.1 = a then 1 else 0) ≤ (1 / 2 ^ P.R) / G.2.1 := by
  unfold avgExact
  refine list_avg_right_le hG hcs (v₀ := a / 2 ^ P.R) (by positivity) fun c₁ hc₁ ↦ ?_
  have hpair : ∀ c₂, pairAvg (P := P) (fun e : ℕ × ℕ ↦ if e.1 = a then (1 : ℝ) else 0) c₁ c₂ =
      𝔼 x : Cube (Fin P.R), (if vtx c₁.1.2 (permCube c₁.2 x) = a then (1 : ℝ) else 0) :=
    fun c₂ ↦ corrAverage_fst _ _ (fun x ↦ if vtx c₁.1.2 (permCube c₁.2 x) = a then (1 : ℝ) else 0)
  simp only [hpair]
  refine list_avg_le_of_le (List.ne_nil_of_mem (mem_nbrs_self hc₁)) fun _ _ ↦ ?_
  refine (expect_vtx_le (isPermTable_of_mem hG hc₁) _ _).trans (le_of_eq ?_)
  ring

/-- **The second end** of an edge of the exact law is `a` with probability at most `1/n`. -/
theorem avgExact_snd_le (hG : GoodI P.R G) (hcs : G.2.2.2 ≠ []) (a : ℕ) :
    avgExact (P := P) (G := G) (fun e ↦ if e.2 = a then 1 else 0) ≤ (1 / 2 ^ P.R) / G.2.1 := by
  unfold avgExact
  have hpair : ∀ c₁ c₂, pairAvg (P := P) (fun e : ℕ × ℕ ↦ if e.2 = a then (1 : ℝ) else 0) c₁ c₂ =
      𝔼 y : Cube (Fin P.R), (if vtx c₂.1.2 (permCube c₂.2 y) = a then (1 : ℝ) else 0) :=
    fun c₁ c₂ ↦ corrAverage_snd _ _
      (fun y ↦ if vtx c₂.1.2 (permCube c₂.2 y) = a then (1 : ℝ) else 0)
  simp only [hpair]
  rw [list_sum_nbrs_avg G.2.2.2 G.1 (fun c hc ↦ (hG.1 c hc).1)]
  refine list_avg_right_le hG hcs (v₀ := a / 2 ^ P.R) (by positivity) fun c hc ↦ ?_
  refine (expect_vtx_le (isPermTable_of_mem hG hc) _ _).trans (le_of_eq ?_)
  ring

/-- **An ordered pair** has probability at most `((1 + |ρ|)/4)^R / |V|` under the exact law. -/
theorem avgExact_pair_le (hq : P.q ≤ 2 ^ P.b) (hG : GoodI P.R G) (hcs : G.2.2.2 ≠ [])
    (a b : ℕ) :
    avgExact (P := P) (G := G) (fun e ↦ if e = (a, b) then 1 else 0) ≤
      ((1 + |P.rho|) / 4) ^ P.R / G.2.1 := by
  unfold avgExact
  refine list_avg_right_le hG hcs (v₀ := a / 2 ^ P.R) (by positivity) fun c₁ hc₁ ↦ ?_
  refine list_avg_le_of_le (List.ne_nil_of_mem (mem_nbrs_self hc₁)) fun c₂ hc₂ ↦ ?_
  have hc₂' : c₂ ∈ G.2.2.2 := (List.mem_filter.1 hc₂).1
  obtain ⟨x₁, hx₁⟩ := exists_point (isPermTable_of_mem hG hc₁) c₁.1.2 a
  obtain ⟨y₂, hy₂⟩ := exists_point (isPermTable_of_mem hG hc₂') c₂.1.2 b
  unfold pairAvg
  calc corrAverage P.rho P.R (fun x y ↦ (fun e : ℕ × ℕ ↦ if e = (a, b) then (1 : ℝ) else 0)
          (vtx c₁.1.2 (permCube c₁.2 x), vtx c₂.1.2 (permCube c₂.2 y)))
      ≤ corrAverage P.rho P.R (fun x y ↦ (if c₁.1.2 = a / 2 ^ P.R then (1 : ℝ) else 0) *
          ((if x = x₁ then (1 : ℝ) else 0) * (if y = y₂ then 1 else 0))) := by
        refine corrAverage_mono (rho_mem hq) P.R fun x y ↦ ?_
        beta_reduce
        by_cases h : (vtx c₁.1.2 (permCube c₁.2 x), vtx c₂.1.2 (permCube c₂.2 y)) = (a, b)
        · obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
          obtain ⟨h3, h4⟩ := hx₁ x h1
          have h5 := (hy₂ y h2).2
          have hl : (if (vtx c₁.1.2 (permCube c₁.2 x), vtx c₂.1.2 (permCube c₂.2 y)) = (a, b)
              then (1 : ℝ) else 0) = 1 := ite_eq_left h
          rw [hl, ite_eq_left h3, ite_eq_left h4, ite_eq_left h5]
          norm_num
        · have hl : (if (vtx c₁.1.2 (permCube c₁.2 x), vtx c₂.1.2 (permCube c₂.2 y)) = (a, b)
              then (1 : ℝ) else 0) = 0 := ite_eq_right h
          rw [hl]; positivity
    _ = (if c₁.1.2 = a / 2 ^ P.R then (1 : ℝ) else 0) *
          corrAverage P.rho P.R (fun x y ↦ (if x = x₁ then (1 : ℝ) else 0) *
            (if y = y₂ then 1 else 0)) := corrAverage_const_mul _ _ _ _
    _ ≤ (if c₁.1.2 = a / 2 ^ P.R then (1 : ℝ) else 0) * ((1 + |P.rho|) / 4) ^ P.R :=
        mul_le_mul_of_nonneg_left (corrAverage_point_le (rho_mem hq) _ _ _) (by positivity)

/-! ### The decoder on good instances -/

theorem ok_iff : P.ok G = true ↔ G.2.2.1 = P.R ∧ 0 < G.2.2.2.length ∧ G.1 ≤ G.2.2.2.length ∧
    G.2.1 ≤ G.2.2.2.length := by
  simp [Prm.ok, and_assoc]

theorem nVert_eq (hok : P.ok G = true) : P.nVert G = G.2.1 * 2 ^ P.R := by
  rw [Prm.nVert, min_eq_left (ok_iff.1 hok).2.2.2]

theorem getD_mod_mem {α : Type*} [Inhabited α] {l : List α} (hl : l ≠ []) (r : ℕ) :
    l.getD (r % l.length) default ∈ l := by
  have hpos : 0 < l.length := List.length_pos_iff.2 hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ hpos), Option.getD_some]
  exact List.getElem_mem _

theorem edgeOf_lt {cs : List UGConstraint} {R q nV : ℕ} (hcs : cs ≠ [])
    (hv : ∀ c ∈ cs, c.1.2 < nV) (r₁ r₂ : ℕ) (x : Cube (Fin R)) (z : Fin R → ℕ) :
    (edgeOf cs R q r₁ r₂ x z).1 < nV * 2 ^ R ∧ (edgeOf cs R q r₁ r₂ x z).2 < nV * 2 ^ R := by
  have h₁ := getD_mod_mem hcs r₁
  have hN : nbrs cs (cs.getD (r₁ % cs.length) default).1.1 ≠ [] :=
    List.ne_nil_of_mem (mem_nbrs_self h₁)
  have h₂ := (List.mem_filter.1 (getD_mod_mem hN r₂)).1
  exact ⟨vtx_lt (hv _ h₁) _, vtx_lt (hv _ h₂) _⟩

theorem decE_lt (hG : GoodI P.R G) (hok : P.ok G = true) (ω : Fin (P.blockLen G) → Bool) :
    (decE P G ω).1 < P.nVert G ∧ (decE P G ω).2 < P.nVert G := by
  rw [nVert_eq hok]
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 (ok_iff.1 hok).2.1
  exact edgeOf_lt hcs (fun c hc ↦ (hG.1 c hc).2.1) _ _ _ _

/-- The decoder with values in the vertices of the graph. -/
def dec (hG : GoodI P.R G) (hok : P.ok G = true) (ω : Fin (P.blockLen G) → Bool) :
    Fin (P.nVert G) × Fin (P.nVert G) :=
  (⟨_, (decE_lt hG hok ω).1⟩, ⟨_, (decE_lt hG hok ω).2⟩)

theorem frac_eq_avg {Ω : Type} [Fintype Ω] (p : Ω → Prop) [DecidablePred p] :
    frac p = (∑ ω, if p ω then (1 : ℝ) else 0) / Fintype.card Ω := by
  unfold frac
  rw [Finset.sum_boole (s := univ) (p := p)]
  congr 3
  exact Finset.filter_congr_decidable _ _ _

theorem card_block : Fintype.card (Fin (P.blockLen G) → Bool) = (2 : ℝ) ^ P.blockLen G := by
  simp

theorem four_mul_sq_le (E : ℕ) : 4 * E ^ 2 ≤ 4 ^ E := by
  induction E with
  | zero => simp
  | succ E ih =>
    rcases Nat.eq_zero_or_pos E with h | h
    · subst h; norm_num
    · calc 4 * (E + 1) ^ 2 ≤ 4 * (4 * E ^ 2) := by nlinarith
        _ ≤ 4 * 4 ^ E := Nat.mul_le_mul_left _ ih
        _ = 4 ^ (E + 1) := by ring

/-- The bias of the indices is small next to `1/n`. -/
theorem tv_le (hG : GoodI P.R G) (hok : P.ok G = true) :
    2 * (G.2.2.2.length : ℝ) * 1 / 2 ^ P.tBits G ≤ 1 / (2 * P.nVert G * 2 ^ P.Δ) := by
  obtain ⟨-, hE, -, hV⟩ := ok_iff.1 hok
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 hE
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hcs
  have hV1 : 0 < G.2.1 := Nat.zero_lt_of_lt (hG.1 c hc).2.1
  rw [nVert_eq hok]
  set E := G.2.2.2.length
  have hnat : 2 * E * (2 * (G.2.1 * 2 ^ P.R) * 2 ^ P.Δ) ≤ 2 ^ P.tBits G := by
    have h4 := four_mul_sq_le E
    have h1 : 2 * E * (2 * (G.2.1 * 2 ^ P.R) * 2 ^ P.Δ) ≤ 4 * E ^ 2 * (2 ^ P.R * 2 ^ P.Δ) := by
      have : G.2.1 ≤ E := hV
      calc 2 * E * (2 * (G.2.1 * 2 ^ P.R) * 2 ^ P.Δ) = 4 * E * G.2.1 * (2 ^ P.R * 2 ^ P.Δ) := by
            ring
        _ ≤ 4 * E * E * (2 ^ P.R * 2 ^ P.Δ) := by gcongr
        _ = 4 * E ^ 2 * (2 ^ P.R * 2 ^ P.Δ) := by ring
    calc 2 * E * (2 * (G.2.1 * 2 ^ P.R) * 2 ^ P.Δ) ≤ 4 * E ^ 2 * (2 ^ P.R * 2 ^ P.Δ) := h1
      _ ≤ 4 ^ E * (2 ^ P.R * 2 ^ P.Δ) := Nat.mul_le_mul_right _ h4
      _ = 2 ^ P.tBits G := by
          rw [Prm.tBits, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add,
            Nat.add_assoc]
  have hpos : (0 : ℝ) < 2 * ((G.2.1 * 2 ^ P.R : ℕ) : ℝ) * 2 ^ P.Δ := by positivity
  rw [div_le_div_iff₀ (by positivity) hpos]
  have : ((2 * E * (2 * (G.2.1 * 2 ^ P.R) * 2 ^ P.Δ) : ℕ) : ℝ) ≤ ((2 ^ P.tBits G : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at this ⊢
  linarith

theorem frac_dec_le (hG : GoodI P.R G) (hok : P.ok G = true)
    (p : Fin (P.nVert G) × Fin (P.nVert G) → Prop) (φ : ℕ × ℕ → ℝ)
    (h : ∀ ω, p (dec hG hok ω) → 1 ≤ φ (decE P G ω)) (h0 : ∀ e, 0 ≤ φ e) :
    frac (fun ω ↦ p (dec hG hok ω)) ≤
      (∑ ω : Fin (P.blockLen G) → Bool, φ (decE P G ω)) / 2 ^ P.blockLen G := by
  classical
  rw [frac_eq_avg, card_block]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ ↦ ?_) (by positivity)
  split_ifs with hp
  · exact h ω hp
  · exact h0 _

theorem avgDec_le (hq : P.q ≤ 2 ^ P.b) (hG : GoodI P.R G) (hok : P.ok G = true)
    {φ : ℕ × ℕ → ℝ} (hφ : ∀ e, |φ e| ≤ 1) :
    (∑ ω : Fin (P.blockLen G) → Bool, φ (decE P G ω)) / 2 ^ P.blockLen G ≤
      avgExact (P := P) (G := G) φ + 1 / (2 * P.nVert G * 2 ^ P.Δ) := by
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 (ok_iff.1 hok).2.1
  have h1 := abs_avgDec_sub_le hq hcs hφ
  have h2 := tv_le hG hok
  have := (abs_le.1 h1).2
  linarith

theorem abs_ite_le (p : Prop) [Decidable p] : |(if p then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

/-- **Each vertex is an end** of a decoded edge with probability at most `3/n`. -/
theorem dec_touch (hq : P.q ≤ 2 ^ P.b) (hG : GoodI P.R G) (hok : P.ok G = true)
    (a : Fin (P.nVert G)) :
    frac (fun ω ↦ (dec hG hok ω).1 = a ∨ (dec hG hok ω).2 = a) ≤ 3 / P.nVert G := by
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 (ok_iff.1 hok).2.1
  have hle := frac_dec_le hG hok (fun e ↦ e.1 = a ∨ e.2 = a)
    (fun e ↦ (if e.1 = a.1 then (1 : ℝ) else 0) + (if e.2 = a.1 then 1 else 0))
    (fun ω hω ↦ by
      rcases hω with h | h
      · have : (decE P G ω).1 = a.1 := congrArg Fin.val h
        rw [ite_eq_left this]; split_ifs <;> norm_num
      · have : (decE P G ω).2 = a.1 := congrArg Fin.val h
        rw [ite_eq_left this]; split_ifs <;> norm_num)
    (fun e ↦ by positivity)
  rw [Finset.sum_add_distrib, add_div] at hle
  have h1 := avgDec_le hq hG hok (φ := fun e ↦ if e.1 = a.1 then (1 : ℝ) else 0)
    fun e ↦ abs_ite_le _
  have h2 := avgDec_le hq hG hok (φ := fun e ↦ if e.2 = a.1 then (1 : ℝ) else 0)
    fun e ↦ abs_ite_le _
  have h3 := avgExact_fst_le hG hcs a.1
  have h4 := avgExact_snd_le hG hcs a.1
  have hn : (P.nVert G : ℝ) = G.2.1 * 2 ^ P.R := by rw [nVert_eq hok]; push_cast; ring
  have hnpos : (0 : ℝ) < P.nVert G := by
    have := a.2; exact_mod_cast Nat.zero_lt_of_lt this
  have e1 : (1 / 2 ^ P.R) / (G.2.1 : ℝ) = 1 / P.nVert G := by
    rw [hn]; field_simp
  have e2 : 1 / (2 * (P.nVert G : ℝ) * 2 ^ P.Δ) ≤ 1 / (2 * P.nVert G) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (1 : ℝ) ≤ 2 ^ P.Δ := one_le_pow₀ (by norm_num)
    nlinarith
  have e3 : 1 / (2 * (P.nVert G : ℝ)) = 1 / P.nVert G / 2 := by field_simp
  have e4 : 3 / (P.nVert G : ℝ) = 3 * (1 / P.nVert G) := by ring
  rw [e1] at h3 h4
  rw [e3] at e2
  rw [e4]
  linarith

/-- **Each ordered pair** is decoded with probability at most `1/(n D²)`, when
`((1 + |ρ|)/2)^R ≤ 1/(2D²)` and `D² ≤ 2^Δ`. -/
theorem dec_maxw (hq : P.q ≤ 2 ^ P.b) (hG : GoodI P.R G) (hok : P.ok G = true) {D : ℕ}
    (hκ : ((1 + |P.rho|) / 2) ^ P.R ≤ 1 / (2 * D ^ 2)) (hΔ : D ^ 2 ≤ 2 ^ P.Δ) (hD : 1 ≤ D)
    (e : Fin (P.nVert G) × Fin (P.nVert G)) :
    frac (fun ω ↦ dec hG hok ω = e) ≤ 1 / (P.nVert G * D ^ 2) := by
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 (ok_iff.1 hok).2.1
  have hle := frac_dec_le hG hok (fun e' ↦ e' = e)
    (fun e' ↦ if e' = (e.1.1, e.2.1) then (1 : ℝ) else 0)
    (fun ω hω ↦ by
      have : decE P G ω = (e.1.1, e.2.1) := by
        rw [← hω]; rfl
      rw [ite_eq_left this])
    (fun e ↦ by positivity)
  have h1 := avgDec_le hq hG hok (φ := fun e' ↦ if e' = (e.1.1, e.2.1) then (1 : ℝ) else 0)
    fun e ↦ abs_ite_le _
  have h3 := avgExact_pair_le hq hG hcs e.1.1 e.2.1
  have hn : (P.nVert G : ℝ) = G.2.1 * 2 ^ P.R := by rw [nVert_eq hok]; push_cast; ring
  have hnpos : (0 : ℝ) < P.nVert G := by
    have := e.1.2; exact_mod_cast Nat.zero_lt_of_lt this
  have hV : (0 : ℝ) < G.2.1 := by
    have h2R : (0 : ℝ) < 2 ^ P.R := by positivity
    rw [hn] at hnpos
    exact pos_of_mul_pos_left hnpos h2R.le
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have e1 : ((1 + |P.rho|) / 4) ^ P.R / (G.2.1 : ℝ) =
      ((1 + |P.rho|) / 2) ^ P.R / P.nVert G := by
    rw [hn, show (1 + |P.rho|) / 4 = (1 + |P.rho|) / 2 / 2 by ring, div_pow]
    field_simp
  have e2 : ((1 + |P.rho|) / 2) ^ P.R / (P.nVert G : ℝ) ≤ 1 / (2 * D ^ 2) / P.nVert G :=
    div_le_div_of_nonneg_right hκ hnpos.le
  have e3 : 1 / (2 * (P.nVert G : ℝ) * 2 ^ P.Δ) ≤ 1 / (2 * D ^ 2) / P.nVert G := by
    rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
    have : ((D ^ 2 : ℕ) : ℝ) ≤ ((2 ^ P.Δ : ℕ) : ℝ) := by exact_mod_cast hΔ
    push_cast at this
    nlinarith
  have e4 : 1 / (2 * (D : ℝ) ^ 2) / P.nVert G + 1 / (2 * D ^ 2) / P.nVert G =
      1 / (P.nVert G * D ^ 2) := by
    field_simp; ring
  rw [e1] at h3
  linarith

/-- A cut of `0, …, n - 1` read on all of `ℕ`. -/
def liftCut {n : ℕ} (f : Fin n → Bool) (a : ℕ) : Bool := if h : a < n then f ⟨a, h⟩ else false

theorem kkmoCut_eq_avgExact (F : ℕ → Bool) :
    kkmoCut P.rho P.R G.2.2.2 (fun v y ↦ F (vtx v y)) =
      avgExact (P := P) (G := G) (fun e ↦ bitVal (F e.1 != F e.2)) := rfl

/-- **The cut values of the decoded law and of the KKMO graph** differ by at most the bias of the
indices. -/
theorem abs_lawCut_dec_sub_le (hq : P.q ≤ 2 ^ P.b) (hG : GoodI P.R G) (hok : P.ok G = true)
    (f : Fin (P.nVert G) → Bool) :
    |lawCut (dec hG hok) f - kkmoCut P.rho P.R G.2.2.2 (fun v y ↦ liftCut f (vtx v y))| ≤
      1 / (2 * P.nVert G * 2 ^ P.Δ) := by
  have hcs : G.2.2.2 ≠ [] := List.length_pos_iff.1 (ok_iff.1 hok).2.1
  have hlaw : lawCut (dec hG hok) f = (∑ ω : Fin (P.blockLen G) → Bool,
      bitVal (liftCut f (decE P G ω).1 != liftCut f (decE P G ω).2)) / 2 ^ P.blockLen G := by
    classical
    unfold lawCut
    rw [frac_eq_avg, card_block]
    congr 1
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    have h1 : liftCut f (decE P G ω).1 = f (dec hG hok ω).1 := by
      simp [liftCut, (decE_lt hG hok ω).1, dec]
    have h2 : liftCut f (decE P G ω).2 = f (dec hG hok ω).2 := by
      simp [liftCut, (decE_lt hG hok ω).2, dec]
    rw [h1, h2]
    by_cases h : f (dec hG hok ω).1 = f (dec hG hok ω).2 <;> simp [h, bitVal]
  rw [hlaw, kkmoCut_eq_avgExact]
  have hB : ∀ e : ℕ × ℕ, |bitVal (liftCut f e.1 != liftCut f e.2)| ≤ 1 := fun e ↦ by
    unfold bitVal; split_ifs <;> simp
  exact (abs_avgDec_sub_le hq hcs hB).trans (tv_le hG hok)

end BGHKLMM26.Hard
