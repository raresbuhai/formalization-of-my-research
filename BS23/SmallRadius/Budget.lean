module

public import BS23.SmallRadius.Peel
public import BS23.SmallRadius.RunTime

/-!
# The size of the programs, and the budget of the small-radius algorithm

The algorithm of [BS23, Theorem 1.3] (`BS23.SmallRadius.srAlg C₁`) hands the solver, in every
round, the program `roundProb` of `BS23/SmallRadius/Program.lean`, with the unary budget
`Lb = radiusTime C₁ x`. The analysis (`BS23.SmallRadius.peel_good_of_sep`) needs that the budget
cuts nothing (`BS23.SmallRadius.Fits`) and suffices for the solver in every round
(`BS23.SmallRadius.BudgetFits`: `(|P| + 2)^(64 t + 1) ≤ Lb` for the encoded program `P`). This file
proves both for `C₁ = budgetC = 2^14`, on the guard (`BS23.SmallRadius.budget_facts`).

**The size of a program** (`BS23.SmallRadius.length_encProblem_le`). Every term `c x^e` of every
constraint and of the objective has an exponent vector `e` with at most `N + d` entries (`N` the
number of variables), of sum at most `4t + 2`, and a coefficient `c` that is a multiple of `1/D` of
absolute value at most `M` with `M D, D < 2^κ` (`BS23.SmallRadius.QB`): the coefficients are `±1`,
the ball bound `Bd`, products of `2s + 1` data values or `±1`, and `K b_γ`. So a term has encoded
length at most `2 (2 (4t + 2) + N + d) + 3κ + 4` (`BS23.SmallRadius.length_encTerm_le_of`), and the
program is bounded by the number of constraints times their lengths.

**The guard** (`BS23.SmallRadius.NumGuard`: `n ≥ 2^20`, `(d+1)^(4t) ≤ n`, `2^(4t) ≤ n`) makes all
counts at most `n` (`(d+1)^(2s)`, `(d+1)^(3t)`, `(2d+2)^(2t)`, ...), the data `zⱼₐ` multiples of
`2^{-p}` of absolute value at most `n² + 1`, and `κ = 16 n²` enough
(`BS23.SmallRadius.length_roundProb_le`): `|P| + 2 ≤ n^6`. With `n ≤ |x|` and
`6 (64 t + 1) ≤ 2^14 (⌈R²⌉ + logInv w + 1)`, the budget `radiusTime 2^14 x` suffices.
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial SoS SoS.Solver SoS.Poly RawAlg
open Encoding (encRat)

/-! ### Rationals with a bounded denominator -/

/-- `q` has absolute value at most `M` and is a multiple of `1/D`. -/
def QB (D : ℕ) (M q : ℚ) : Prop := |q| ≤ M ∧ ∃ z : ℤ, q * D = z

namespace QB

variable {D D' : ℕ} {M M' q q' : ℚ}

theorem M_nonneg (h : QB D M q) : 0 ≤ M := (abs_nonneg q).trans h.1

theorem den_le (hD : 0 < D) (h : QB D M q) : q.den ≤ D := by
  obtain ⟨-, z, hz⟩ := h
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hq' : q = z / D := by rw [← hz]; field_simp
  have hden : q.den ∣ D := by
    have := Rat.den_dvd z D
    rw [Rat.divInt_eq_div] at this
    push_cast at this
    rw [← hq'] at this
    exact_mod_cast this
  exact Nat.le_of_dvd hD hden

theorem natAbs_num_le (hD : 0 < D) (h : QB D M q) : (q.num.natAbs : ℚ) ≤ M * D := by
  have h1 : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
      abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
  rw [h1]
  exact mul_le_mul h.1 (by exact_mod_cast h.den_le hD) (by positivity) h.M_nonneg

theorem neg (h : QB D M q) : QB D M (-q) := by
  obtain ⟨h1, z, hz⟩ := h
  exact ⟨by rwa [abs_neg], -z, by push_cast; rw [← hz]; ring⟩

theorem mul (h : QB D M q) (h' : QB D' M' q') : QB (D * D') (M * M') (q * q') := by
  obtain ⟨h1, z, hz⟩ := h
  obtain ⟨h1', z', hz'⟩ := h'
  refine ⟨?_, z * z', ?_⟩
  · rw [abs_mul]
    exact mul_le_mul h1 h1' (abs_nonneg _) ((abs_nonneg q).trans h1)
  · push_cast
    rw [← hz, ← hz']
    ring

theorem mono (h : QB D M q) (hM : M ≤ M') : QB D M' q := ⟨h.1.trans hM, h.2⟩

theorem one (hM : 1 ≤ M) : QB D M 1 := ⟨by rwa [abs_one], D, by push_cast; ring⟩

theorem natCast (a : ℕ) : QB 1 a a := ⟨by rw [Nat.abs_cast], a, by push_cast; ring⟩

/-- Products of a list. -/
theorem prod {l : List ℚ} (h : ∀ q ∈ l, QB D M q) :
    QB (D ^ l.length) (M ^ l.length) l.prod := by
  induction l with
  | nil => exact ⟨by simp, 1, by simp⟩
  | cons a l ih =>
    have := (h a List.mem_cons_self).mul (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
    rw [List.prod_cons, List.length_cons, pow_succ', pow_succ']
    exact this

/-- Sums of a list. -/
theorem sum {l : List ℚ} (h : ∀ q ∈ l, QB D M q) : QB D (l.length * M) l.sum := by
  induction l with
  | nil => exact ⟨by simp, 0, by simp⟩
  | cons a l ih =>
    obtain ⟨h1, z, hz⟩ := h a List.mem_cons_self
    obtain ⟨h2, z', hz'⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine ⟨?_, z + z', ?_⟩
    · rw [List.sum_cons, List.length_cons]
      push_cast
      calc |a + l.sum| ≤ |a| + |l.sum| := abs_add_le _ _
        _ ≤ M + l.length * M := add_le_add h1 h2
        _ = (l.length + 1) * M := by ring
    · rw [List.sum_cons]
      push_cast
      rw [← hz, ← hz']
      ring

end QB

/-- The length of the code of a rational `q`, a multiple of `1/D` with `|q| ≤ M`, when
`M D < 2^κ` and `D < 2^κ`. -/
theorem length_encRat_le_of_QB {D κ : ℕ} {M q : ℚ} (hD : 0 < D) (h : QB D M q)
    (hMD : M * D < 2 ^ κ) (hDκ : D < 2 ^ κ) : (encRat q).length ≤ 3 * κ + 3 := by
  have e : (encRat q).length =
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encIntBin Turing.MultiTapeTM.encNat
        (q.num, q.den)).length := rfl
  rw [e, Turing.MultiTapeTM.length_encPair, Turing.MultiTapeTM.length_encIntBin]
  have h1 : q.num.natAbs < 2 ^ κ := by
    have := (h.natAbs_num_le hD).trans_lt hMD
    exact_mod_cast this
  have h2 : q.den < 2 ^ κ := (h.den_le hD).trans_lt hDκ
  have h3 : (Turing.MultiTapeTM.encNat q.den).length ≤ κ :=
    Turing.MultiTapeTM.length_encNat_le_of_lt_two_pow h2
  have h4 : q.num.natAbs.size ≤ κ := Nat.size_le.2 h1
  simp only at h3 h4 ⊢
  omega

/-- A coefficient whose code is short: a multiple of `1/D` of absolute value at most `M`, with
`M D < 2^κ` and `0 < D < 2^κ`. -/
def CoefOK (κ : ℕ) (q : ℚ) : Prop :=
  ∃ D : ℕ, ∃ M : ℚ, 0 < D ∧ QB D M q ∧ M * D < 2 ^ κ ∧ D < 2 ^ κ

theorem CoefOK.neg {κ : ℕ} {q : ℚ} (h : CoefOK κ q) : CoefOK κ (-q) := by
  obtain ⟨D, M, hD, hq, h1, h2⟩ := h
  exact ⟨D, M, hD, hq.neg, h1, h2⟩

theorem CoefOK.length_le {κ : ℕ} {q : ℚ} (h : CoefOK κ q) : (encRat q).length ≤ 3 * κ + 3 := by
  obtain ⟨D, M, hD, hq, h1, h2⟩ := h
  exact length_encRat_le_of_QB hD hq h1 h2

theorem coefOK_of_QB {κ D : ℕ} {M q : ℚ} (hD : 0 < D) (h : QB D M q) (hMD : M * D < 2 ^ κ)
    (hDκ : D < 2 ^ κ) : CoefOK κ q := ⟨D, M, hD, h, hMD, hDκ⟩

theorem coefOK_one {κ : ℕ} (hκ : 1 ≤ κ) : CoefOK κ 1 := by
  have h2 : (1 : ℕ) < 2 ^ κ := Nat.one_lt_two_pow (by omega)
  refine coefOK_of_QB (D := 1) (M := 1) one_pos (QB.one le_rfl) ?_ h2
  have : ((1 : ℕ) : ℚ) < 2 ^ κ := by exact_mod_cast h2
  push_cast at this ⊢
  linarith

theorem coefOK_neg_one {κ : ℕ} (hκ : 1 ≤ κ) : CoefOK κ (-1) := (coefOK_one hκ).neg

/-! ### Codes of exponent vectors, terms and raw polynomials -/

theorem length_encNat_le_self (a : ℕ) : (Turing.MultiTapeTM.encNat a).length ≤ a := by
  rw [Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- An exponent vector `e` has a code of length at most `2 ∑ e + |e|`. -/
theorem length_encList_encNat_le (e : List ℕ) :
    (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat e).length ≤ 2 * e.sum + e.length := by
  rw [Turing.MultiTapeTM.length_encList]
  induction e with
  | nil => simp
  | cons a e ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := length_encNat_le_self a
    omega

/-- A term with an exponent vector of at most `E` entries and sum at most `S`, and a coefficient
whose code is short (`BS23.SmallRadius.CoefOK κ`). -/
def TermOK (E S κ : ℕ) (τ : List ℕ × ℚ) : Prop :=
  τ.1.length ≤ E ∧ τ.1.sum ≤ S ∧ CoefOK κ τ.2

theorem TermOK.neg {E S κ : ℕ} {τ : List ℕ × ℚ} (h : TermOK E S κ τ) :
    TermOK E S κ (τ.1, -τ.2) := ⟨h.1, h.2.1, h.2.2.neg⟩

/-- **The code of a term.** -/
theorem length_encTerm_le_of {E S κ : ℕ} {τ : List ℕ × ℚ} (h : TermOK E S κ τ) :
    (encTerm τ).length ≤ 2 * (2 * S + E) + 1 + (3 * κ + 3) := by
  have e : (encTerm τ).length =
      2 * (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat τ.1).length + 1 +
        (encRat τ.2).length :=
    Turing.MultiTapeTM.length_encPair τ
  rw [e]
  have h1 := length_encList_encNat_le τ.1
  have h2 := h.2.2.length_le
  have h3 := h.1
  have h4 := h.2.1
  omega

/-- **The code of a raw polynomial** with `TermOK` terms. -/
theorem length_encRaw_le_of {E S κ : ℕ} {f : RawPoly} (h : ∀ τ ∈ f, TermOK E S κ τ) :
    (encRaw f).length ≤ f.length * (2 * (2 * (2 * S + E) + 1 + (3 * κ + 3)) + 1) :=
  Turing.MultiTapeTM.length_encList_le encTerm f fun τ hτ => length_encTerm_le_of (h τ hτ)

/-! ### Products -/

theorem length_sectStep_le {α : Type} (L : ℕ) (acc : List (List α)) (l : List α) :
    (sectStep L acc l).length ≤ acc.length * l.length := by
  rw [sectStep]
  refine (List.length_take_le' _ _).trans (le_of_eq ?_)
  rw [List.length_flatMap]
  simp only [List.length_map, List.map_const', List.sum_replicate, smul_eq_mul]

theorem length_foldl_sectStep_le {α : Type} (L : ℕ) :
    ∀ (ls : List (List α)) (acc : List (List α)),
      (ls.foldl (sectStep L) acc).length ≤ acc.length * (ls.map List.length).prod
  | [], acc => by simp
  | l :: ls, acc => by
    rw [List.foldl_cons, List.map_cons, List.prod_cons]
    calc (ls.foldl (sectStep L) (sectStep L acc l)).length
        ≤ (sectStep L acc l).length * (ls.map List.length).prod :=
          length_foldl_sectStep_le L ls _
      _ ≤ acc.length * l.length * (ls.map List.length).prod :=
          Nat.mul_le_mul_right _ (length_sectStep_le L acc l)
      _ = acc.length * (l.length * (ls.map List.length).prod) := by ring

/-- A product has at most the product of the lengths of its factors as terms. -/
theorem length_prodRaw_le (n L : ℕ) (fs : List RawPoly) :
    (prodRaw n L fs).length ≤ (fs.map List.length).prod := by
  rw [prodRaw, List.length_map, sectB]
  simpa using length_foldl_sectStep_le L fs [[]]

theorem length_prodRaw_replicate_le (n L k : ℕ) (f : RawPoly) :
    (prodRaw n L (List.replicate k f)).length ≤ f.length ^ k := by
  have := length_prodRaw_le n L (List.replicate k f)
  rwa [List.map_replicate, List.prod_replicate] at this

/-- The degree of an exponent vector in its first `M` entries is at most its sum. -/
theorem udeg_le_sum : ∀ (M : ℕ) (e : List ℕ), udeg M e ≤ e.sum
  | M, [] => by simp [udeg]
  | 0, a :: e => by simp [udeg]
  | M + 1, a :: e => by
    have ih := udeg_le_sum M e
    have h : udeg (M + 1) (a :: e) = a + udeg M e := by
      simp only [udeg, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      simp [Function.comp_def]
    rw [h, List.sum_cons]
    omega

/-- The sum of the exponent vector of a product of terms. -/
theorem sum_sumE_le (M : ℕ) (tup : List (List ℕ × ℚ)) :
    (sumE M tup).sum ≤ (tup.map fun τ => τ.1.sum).sum := by
  have e : (sumE M tup).sum = (tup.map fun τ => udeg M τ.1).sum := by
    rw [sumE]
    exact list_sum_comm (List.range M) tup fun i τ => τ.1.getD i 0
  rw [e]
  exact List.sum_le_sum fun τ _ => udeg_le_sum M τ.1

theorem length_sumE (M : ℕ) (tup : List (List ℕ × ℚ)) : (sumE M tup).length = M := by
  simp [sumE]

/-- Sums over a tuple with one entry from each list. -/
theorem sum_le_of_forall₂ {g : List ℕ × ℚ → ℕ} {S₀ : ℕ} :
    ∀ {tup : List (List ℕ × ℚ)} {fs : List RawPoly}, List.Forall₂ (· ∈ ·) tup fs →
      (∀ f ∈ fs, ∀ τ ∈ f, g τ ≤ S₀) → (tup.map g).sum ≤ fs.length * S₀
  | [], [], _, _ => by simp
  | τ :: tup, f :: fs, List.Forall₂.cons h1 h2, h => by
    have ih := sum_le_of_forall₂ h2 fun f' hf' => h f' (List.mem_cons_of_mem _ hf')
    have := h f List.mem_cons_self τ h1
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- Coefficients of a tuple with one entry from each list. -/
theorem qb_prod_of_forall₂ {D : ℕ} {M : ℚ} {tup : List (List ℕ × ℚ)}
    {fs : List RawPoly} (htup : List.Forall₂ (· ∈ ·) tup fs) (h : ∀ f ∈ fs, ∀ τ ∈ f, QB D M τ.2) :
    QB (D ^ fs.length) (M ^ fs.length) (tup.map Prod.snd).prod := by
  have hlen : (tup.map Prod.snd).length = fs.length := by
    rw [List.length_map]; exact htup.length_eq
  rw [← hlen]
  refine QB.prod (fun q hq => ?_)
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hq
  obtain ⟨f, hf, hτf⟩ : ∃ f ∈ fs, τ ∈ f := by
    clear h hlen hq
    induction htup with
    | nil => simp at hτ
    | cons h1 _ ih =>
      rcases List.mem_cons.1 hτ with rfl | hτ
      · exact ⟨_, List.mem_cons_self, h1⟩
      · obtain ⟨f, hf, hτf⟩ := ih hτ
        exact ⟨f, List.mem_cons_of_mem _ hf, hτf⟩
  exact h f hf τ hτf

theorem mem_neg_iff' {p : RawPoly} {τ : List ℕ × ℚ} (hτ : τ ∈ neg p) :
    ∃ τ' ∈ p, τ = (τ'.1, -τ'.2) := by
  obtain ⟨τ', h, rfl⟩ := List.mem_map.1 hτ
  exact ⟨τ', h, rfl⟩

theorem length_neg' (p : RawPoly) : (neg p).length = p.length := List.length_map _

/-! ### The terms of the program -/

namespace Lay

variable (L : Lay) {s t m Lb κ : ℕ}

theorem sum_tm (u α : List ℕ) (c : ℚ) : (tm u α c).1.sum = u.sum + α.sum := by
  simp [tm]

theorem length_tm (u α : List ℕ) (c : ℚ) : (tm u α c).1.length = u.length + α.length := by
  simp [tm]

/-- The terms of `⟨zᵢ - μ, v⟩`: exponent sum at most `2`, coefficient `zᵢₐ` or `-1`. -/
theorem linRaw_terms (z : Fin L.n → Fin L.d → ℚ) (i : Fin L.n) {τ : List ℕ × ℚ}
    (hτ : τ ∈ L.linRaw z i) :
    τ.1.length = L.N + L.d ∧ τ.1.sum ≤ 2 ∧ ((∃ a, τ.2 = z i a) ∨ τ.2 = -1) := by
  obtain ⟨a, -, ha⟩ := List.mem_flatMap.1 hτ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · refine ⟨by simp [tm], ?_, Or.inl ⟨a, rfl⟩⟩
    rw [sum_tm, sum_unitExp a 1]
    simp
  · refine ⟨by simp [tm], ?_, Or.inr rfl⟩
    rw [sum_tm, sum_unitExp a 1, sum_unitExp (L.mv a) 1]

/-- The terms of `∑_α C_α v^α`. -/
theorem cLin_terms {s : ℕ} (hA : ∀ e ∈ L.As, e.length = L.d ∧ e.sum ≤ 2 * s)
    {τ : List ℕ × ℚ} (hτ : τ ∈ L.cLin) :
    τ.1.length = L.N + L.d ∧ τ.1.sum ≤ 1 + 2 * s ∧ τ.2 = 1 := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hτ
  have h := hA _ (List.get_mem L.As j)
  refine ⟨?_, ?_, rfl⟩
  · rw [length_tm, length_unitExp, h.1]
  · rw [sum_tm, sum_unitExp (L.cv j) 1]
    exact Nat.add_le_add_left h.2 1

/-- The terms of `∑_β P_{βc} v^β`. -/
theorem pLin_terms {t : ℕ} (hB : ∀ e ∈ L.Bs, e.length = L.d ∧ e.sum ≤ t) (c : Fin L.B)
    {τ : List ℕ × ℚ} (hτ : τ ∈ L.pLin c) :
    τ.1.length = L.N + L.d ∧ τ.1.sum ≤ 1 + t ∧ τ.2 = 1 := by
  obtain ⟨β, -, rfl⟩ := List.mem_map.1 hτ
  have h := hB _ (List.get_mem L.Bs β)
  refine ⟨?_, ?_, rfl⟩
  · rw [length_tm, length_unitExp, h.1]
  · rw [sum_tm, sum_unitExp (L.pv β c) 1]
    exact Nat.add_le_add_left h.2 1

theorem qb_one_of_eq {D : ℕ} {M q : ℚ} (hM : 1 ≤ M) (h : q = 1) : QB D M q := h ▸ QB.one hM

/-- **The terms of `F_coef`**, for data that are multiples of `1/Dz` of absolute value at most
`Mz ≥ 1`. -/
theorem termOK_coefF (z : Fin L.n → Fin L.d → ℚ) (hst : s ≤ t)
    (hA : ∀ e ∈ L.As, e.length = L.d ∧ e.sum ≤ 2 * s) {Dz : ℕ} {Mz : ℚ} (hDz : 0 < Dz)
    (hMz : 1 ≤ Mz) (hz : ∀ i a, QB Dz Mz (z i a)) (hκ : 1 ≤ κ)
    (hzκ : Mz ^ (2 * s + 1) * ((Dz ^ (2 * s + 1) : ℕ) : ℚ) < 2 ^ κ)
    (hzκ' : Dz ^ (2 * s + 1) < 2 ^ κ) :
    ∀ τ ∈ L.coefF z s Lb, TermOK (L.N + L.d) (4 * t + 2) κ τ := by
  intro τ hτ
  rcases List.mem_append.1 hτ with hτ | hτ
  · obtain ⟨h1, h2, h3⟩ := L.cLin_terms hA hτ
    exact ⟨h1.le, by omega, by rw [h3]; exact coefOK_one hκ⟩
  · obtain ⟨τ', hτ', rfl⟩ := mem_neg_iff' hτ
    refine TermOK.neg ?_
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hτ'
    obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hi
    have hfs : ∀ f ∈ L.wTerm i :: List.replicate (2 * s) (L.linRaw z i), ∀ τ ∈ f,
        τ.1.sum ≤ 2 ∧ QB Dz Mz τ.2 := by
      intro f hf τ hτ
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [wTerm, List.mem_singleton] at hτ
        subst hτ
        refine ⟨?_, QB.one hMz⟩
        rw [sum_tm, sum_unitExp (L.wv i) 1]
        simp
      · rw [(List.mem_replicate.1 hf).2] at hτ
        obtain ⟨-, h2, h3⟩ := L.linRaw_terms z i hτ
        refine ⟨h2, ?_⟩
        rcases h3 with ⟨a, ha⟩ | ha
        · rw [ha]; exact hz i a
        · rw [ha]; exact (QB.one hMz).neg
    have hlen : (L.wTerm i :: List.replicate (2 * s) (L.linRaw z i)).length = 2 * s + 1 := by
      simp
    refine ⟨by simp [prodTerm, length_sumE], ?_, ?_⟩
    · have h1 := sum_sumE_le (L.N + L.d) tup
      have h2 := sum_le_of_forall₂ (g := fun τ => τ.1.sum) htup fun f hf τ hτ => (hfs f hf τ hτ).1
      rw [hlen] at h2
      change (sumE (L.N + L.d) tup).sum ≤ 4 * t + 2
      omega
    · have h := qb_prod_of_forall₂ htup fun f hf τ hτ => (hfs f hf τ hτ).2
      rw [hlen] at h
      exact coefOK_of_QB (pow_pos hDz _) h hzκ hzκ'

/-- **The terms of `F_mom`**, for coefficients `K b_γ` that are multiples of `1/Db` of absolute
value at most `Mb`. -/
theorem termOK_momF {Gs : List (List ℕ)} (b : List ℕ → ℚ) (K : ℚ) (hs : 1 ≤ s)
    (hms : m * s ≤ t) (hA : ∀ e ∈ L.As, e.length = L.d ∧ e.sum ≤ 2 * s)
    (hB : ∀ e ∈ L.Bs, e.length = L.d ∧ e.sum ≤ t) (hG : ∀ e ∈ Gs, e.length = L.d ∧ e.sum ≤ 2 * t)
    {Db : ℕ} {Mb : ℚ} (hDb : 0 < Db) (hb : ∀ γ ∈ Gs, QB Db Mb (K * b γ)) (hκ : 1 ≤ κ)
    (hbκ : Mb * Db < 2 ^ κ) (hbκ' : Db < 2 ^ κ) :
    ∀ τ ∈ L.momF Gs b m K Lb, TermOK (L.N + L.d) (4 * t + 2) κ τ := by
  have hmt : m ≤ t := le_trans (Nat.le_mul_of_pos_right m hs) hms
  have hm2 : m * (1 + 2 * s) ≤ 3 * t := by
    have : m * (1 + 2 * s) = m + 2 * (m * s) := by ring
    omega
  have hone : CoefOK κ (-(1 : ℚ)) := coefOK_neg_one hκ
  intro τ hτ
  rcases List.mem_append.1 hτ with hτ | hτ
  · rcases List.mem_append.1 hτ with hτ | hτ
    · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hτ
      have h := hG γ hγ
      refine ⟨?_, ?_, coefOK_of_QB hDb (hb γ hγ) hbκ hbκ'⟩
      · rw [length_tm, length_unitExp, h.1]
      · rw [sum_tm, sum_unitExp L.sv m]
        omega
    · obtain ⟨τ', hτ', rfl⟩ := mem_neg_iff' hτ
      obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hτ'
      have hfs : ∀ f ∈ List.replicate m L.cLin, ∀ τ ∈ f, τ.1.sum ≤ 1 + 2 * s ∧ QB 1 1 τ.2 := by
        intro f hf τ hτ
        rw [(List.mem_replicate.1 hf).2] at hτ
        obtain ⟨-, h2, h3⟩ := L.cLin_terms hA hτ
        exact ⟨h2, qb_one_of_eq le_rfl h3⟩
      refine ⟨by simp [prodTerm, length_sumE], ?_, ?_⟩
      · have h1 := sum_sumE_le (L.N + L.d) tup
        have h2 := sum_le_of_forall₂ (g := fun τ => τ.1.sum) htup
          fun f hf τ hτ => (hfs f hf τ hτ).1
        rw [List.length_replicate] at h2
        change (sumE (L.N + L.d) tup).sum ≤ 4 * t + 2
        omega
      · have h := qb_prod_of_forall₂ htup fun f hf τ hτ => (hfs f hf τ hτ).2
        rw [one_pow, one_pow] at h
        have h' := h.neg
        refine coefOK_of_QB one_pos h' ?_ (Nat.one_lt_two_pow (by omega))
        have : ((1 : ℕ) : ℚ) < 2 ^ κ := by exact_mod_cast Nat.one_lt_two_pow (n := κ) (by omega)
        push_cast at this ⊢
        linarith
  · obtain ⟨τ', hτ', rfl⟩ := mem_neg_iff' hτ
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.1 hτ'
    obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hc
    have hfs : ∀ f ∈ List.replicate 2 (L.pLin c), ∀ τ ∈ f, τ.1.sum ≤ 1 + t ∧ QB 1 1 τ.2 := by
      intro f hf τ hτ
      rw [(List.mem_replicate.1 hf).2] at hτ
      obtain ⟨-, h2, h3⟩ := L.pLin_terms hB c hτ
      exact ⟨h2, qb_one_of_eq le_rfl h3⟩
    refine ⟨by simp [prodTerm, length_sumE], ?_, ?_⟩
    · have h1 := sum_sumE_le (L.N + L.d) tup
      have h2 := sum_le_of_forall₂ (g := fun τ => τ.1.sum) htup fun f hf τ hτ => (hfs f hf τ hτ).1
      rw [List.length_replicate] at h2
      change (sumE (L.N + L.d) tup).sum ≤ 4 * t + 2
      omega
    · have h := qb_prod_of_forall₂ htup fun f hf τ hτ => (hfs f hf τ hτ).2
      rw [one_pow, one_pow] at h
      have h' := h.neg
      refine coefOK_of_QB one_pos h' ?_ (Nat.one_lt_two_pow (by omega))
      have : ((1 : ℕ) : ℚ) < 2 ^ κ := by exact_mod_cast Nat.one_lt_two_pow (n := κ) (by omega)
      push_cast at this ⊢
      linarith

/-- The terms of `∑ᵢ wᵢ`-type rows: `(unitExp N k e, ±1)`. -/
theorem termOK_unit {κ : ℕ} (hκ : 1 ≤ κ) (k : Fin L.N) {e : ℕ} (he : e ≤ 4 * t + 2) {c : ℚ}
    (hc : c = 1 ∨ c = -1) : TermOK (L.N + L.d) (4 * t + 2) κ (unitExp L.N k e, c) := by
  refine ⟨by simp, by rw [sum_unitExp k e]; exact he, ?_⟩
  rcases hc with rfl | rfl
  · exact coefOK_one hκ
  · exact coefOK_neg_one hκ

/-- **The terms of the constraints.** -/
theorem termOK_of_mem_constraints (z : Fin L.n → Fin L.d → ℚ) {Gs : List (List ℕ)}
    (b : List ℕ → ℚ) (K Bd : ℚ) (hs : 1 ≤ s) (hst : s ≤ t) (hms : m * s ≤ t)
    (hA : ∀ e ∈ L.As, e.length = L.d ∧ e.sum ≤ 2 * s)
    (hB : ∀ e ∈ L.Bs, e.length = L.d ∧ e.sum ≤ t) (hG : ∀ e ∈ Gs, e.length = L.d ∧ e.sum ≤ 2 * t)
    {Dz : ℕ} {Mz : ℚ} (hDz : 0 < Dz) (hMz : 1 ≤ Mz) (hz : ∀ i a, QB Dz Mz (z i a)) (hκ : 1 ≤ κ)
    (hzκ : Mz ^ (2 * s + 1) * ((Dz ^ (2 * s + 1) : ℕ) : ℚ) < 2 ^ κ)
    (hzκ' : Dz ^ (2 * s + 1) < 2 ^ κ)
    {Db : ℕ} {Mb : ℚ} (hDb : 0 < Db) (hb : ∀ γ ∈ Gs, QB Db Mb (K * b γ))
    (hbκ : Mb * Db < 2 ^ κ) (hbκ' : Db < 2 ^ κ) (hBd : CoefOK κ Bd)
    {f : RawPoly} (hf : f ∈ L.constraints z Gs b s m K Bd Lb) :
    ∀ τ ∈ f, TermOK (L.N + L.d) (4 * t + 2) κ τ := by
  have hcoef := L.termOK_coefF (Lb := Lb) z hst hA hDz hMz hz hκ hzκ hzκ'
  have hmom := L.termOK_momF (Lb := Lb) b K hs hms hA hB hG hDb hb hκ hbκ hbκ'
  have hneg : ∀ p : RawPoly, (∀ τ ∈ p, TermOK (L.N + L.d) (4 * t + 2) κ τ) →
      ∀ τ ∈ neg p, TermOK (L.N + L.d) (4 * t + 2) κ τ := fun p hp τ hτ => by
    obtain ⟨τ', hτ', rfl⟩ := mem_neg_iff' hτ
    exact (hp τ' hτ').neg
  have hbool : ∀ i, ∀ τ ∈ L.boolRaw i, TermOK (L.N + L.d) (4 * t + 2) κ τ := fun i τ hτ => by
    simp only [boolRaw, List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl
    · exact L.termOK_unit hκ _ (by omega) (Or.inl rfl)
    · exact L.termOK_unit hκ _ (by omega) (Or.inr rfl)
  have hsum : ∀ τ ∈ L.sumRaw, TermOK (L.N + L.d) (4 * t + 2) κ τ := fun τ hτ => by
    rcases List.mem_cons.1 hτ with rfl | hτ
    · exact L.termOK_unit hκ _ (by omega) (Or.inl rfl)
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hτ
      exact L.termOK_unit hκ _ (by omega) (Or.inr rfl)
  rcases cases_of_mem_constraints hf with rfl | ⟨i, rfl | rfl⟩ | (rfl | rfl) |
    ⟨α, -, rfl | rfl⟩ | ⟨γ, -, rfl | rfl⟩
  · intro τ hτ
    rcases List.mem_cons.1 hτ with rfl | hτ
    · exact ⟨by simp, by simp, hBd⟩
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hτ
      exact L.termOK_unit hκ _ (by omega) (Or.inr rfl)
  · exact hbool i
  · exact hneg _ (hbool i)
  · exact hsum
  · exact hneg _ hsum
  · exact fun τ hτ => hcoef τ (coeffV_sublist _ _ _ _ hτ)
  · exact hneg _ fun τ hτ => hcoef τ (coeffV_sublist _ _ _ _ hτ)
  · exact fun τ hτ => hmom τ (coeffV_sublist _ _ _ _ hτ)
  · exact hneg _ fun τ hτ => hmom τ (coeffV_sublist _ _ _ _ hτ)

/-- The terms of the objective. -/
theorem termOK_objRaw (hκ : 1 ≤ κ) : ∀ τ ∈ L.objRaw, TermOK (L.N + L.d) (4 * t + 2) κ τ := by
  intro τ hτ
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hτ
  exact L.termOK_unit hκ _ (by omega) (Or.inr rfl)

/-! ### The lengths of the constraints -/

theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) {D : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ D) : (l.flatMap f).length ≤ l.length * D := by
  rw [List.length_flatMap]
  exact sum_map_le l _ h

theorem length_coefF_le (z : Fin L.n → Fin L.d → ℚ) (s Lb : ℕ) :
    (L.coefF z s Lb).length ≤ L.A + L.n * (2 * L.d) ^ (2 * s) := by
  rw [coefF, List.length_append, length_cLin, length_neg']
  refine Nat.add_le_add_left ?_ _
  refine (length_flatMap_le _ _ fun i _ => ?_).trans (by rw [List.length_finRange])
  refine (length_prodRaw_le _ _ _).trans (le_of_eq ?_)
  simp [wTerm]

theorem length_momF_le {Gs : List (List ℕ)} (b : List ℕ → ℚ) (m : ℕ) (K : ℚ) (Lb : ℕ) :
    (L.momF Gs b m K Lb).length ≤ Gs.length + L.A ^ m + L.B * L.B ^ 2 := by
  rw [momF, List.length_append, List.length_append, length_neg', length_neg']
  have h1 : (L.bPart Gs b m K).length = Gs.length := by simp [bPart]
  have h2 := length_prodRaw_replicate_le (L.N + L.d) Lb m L.cLin
  rw [length_cLin] at h2
  have h3 : ((List.finRange L.B).flatMap fun c =>
      prodRaw (L.N + L.d) Lb (List.replicate 2 (L.pLin c))).length ≤ L.B * L.B ^ 2 := by
    refine (length_flatMap_le _ _ fun c _ => ?_).trans (by rw [List.length_finRange])
    have := length_prodRaw_replicate_le (L.N + L.d) Lb 2 (L.pLin c)
    rwa [length_pLin] at this
  omega

/-- **Every constraint has at most `F` terms**, for `F` above the lengths of all the rows. -/
theorem length_le_of_mem_constraints (z : Fin L.n → Fin L.d → ℚ) {Gs : List (List ℕ)}
    (b : List ℕ → ℚ) (K Bd : ℚ) {F : ℕ} (hF1 : L.N + 1 ≤ F) (hF2 : L.n + 2 ≤ F)
    (hF3 : L.A + L.n * (2 * L.d) ^ (2 * s) ≤ F) (hF4 : Gs.length + L.A ^ m + L.B * L.B ^ 2 ≤ F)
    {f : RawPoly} (hf : f ∈ L.constraints z Gs b s m K Bd Lb) : f.length ≤ F := by
  have hc : ∀ α, (L.coefRaw z s Lb α).length ≤ F := fun α =>
    (List.filter_sublist.length_le).trans ((L.length_coefF_le z s Lb).trans hF3)
  have hm : ∀ γ, (L.momRaw Gs b m K Lb γ).length ≤ F := fun γ =>
    (List.filter_sublist.length_le).trans ((L.length_momF_le b m K Lb).trans hF4)
  rcases cases_of_mem_constraints hf with rfl | ⟨i, rfl | rfl⟩ | (rfl | rfl) |
    ⟨α, -, rfl | rfl⟩ | ⟨γ, -, rfl | rfl⟩
  · simp only [ballRaw, List.length_cons, List.length_map, List.length_finRange]; omega
  · simp only [boolRaw, List.length_cons, List.length_nil]; omega
  · simp only [neg, boolRaw, List.length_map, List.length_cons, List.length_nil]; omega
  · simp only [sumRaw, List.length_cons, List.length_map, List.length_finRange]; omega
  · simp only [neg, sumRaw, List.length_map, List.length_cons, List.length_finRange]; omega
  · exact hc α
  · rw [length_neg']; exact hc α
  · exact hm γ
  · rw [length_neg']; exact hm γ

/-- The number of constraints. -/
theorem length_constraints (z : Fin L.n → Fin L.d → ℚ) (Gs : List (List ℕ)) (b : List ℕ → ℚ)
    (s m : ℕ) (K Bd : ℚ) (Lb : ℕ) :
    (L.constraints z Gs b s m K Bd Lb).length = 3 + 2 * L.n + 2 * L.A + 2 * Gs.length := by
  simp only [constraints, List.length_cons, List.length_append, List.length_flatMap,
    List.length_nil, List.length_finRange, List.map_const', List.sum_replicate, smul_eq_mul]
  ring

end Lay

/-! ### The size of a program -/

/-- **The size of a program** whose constraints have at most `F` terms each, at most `nc` of
them, an objective `q₀` with at most `no` terms and no squared terms, all terms `TermOK E S κ`. -/
theorem length_encProblem_le (P : Problem) {E S κ F nc no : ℕ}
    (hcons : ∀ f ∈ P.2.2.1, (∀ τ ∈ f, TermOK E S κ τ) ∧ f.length ≤ F)
    (hnc : P.2.2.1.length ≤ nc) (hobj : ∀ τ ∈ P.2.2.2.1, TermOK E S κ τ)
    (hno : P.2.2.2.1.length ≤ no) (hrest : P.2.2.2.2 = []) :
    (encProblem P).length ≤ 2 * P.1 + 1 + (2 * P.2.1 + 1 +
      (2 * (nc * (2 * (F * (2 * (2 * (2 * S + E) + 1 + (3 * κ + 3)) + 1)) + 1)) + 1 +
        (2 * (no * (2 * (2 * (2 * S + E) + 1 + (3 * κ + 3)) + 1)) + 1))) := by
  set Tb := 2 * (2 * S + E) + 1 + (3 * κ + 3) with hTb
  rw [SoS.Correct.length_encProblem, hrest]
  have h1 := length_encNat_le_self P.1
  have h2 := length_encNat_le_self P.2.1
  have h3 : (Turing.MultiTapeTM.encList encRaw P.2.2.1).length ≤
      nc * (2 * (F * (2 * Tb + 1)) + 1) := by
    refine (Turing.MultiTapeTM.length_encList_le encRaw P.2.2.1 (b := F * (2 * Tb + 1))
      fun f hf => ?_).trans (Nat.mul_le_mul_right _ hnc)
    exact (length_encRaw_le_of (hcons f hf).1).trans
      (Nat.mul_le_mul_right _ (hcons f hf).2)
  have h4 : (encRaw P.2.2.2.1).length ≤ no * (2 * Tb + 1) :=
    (length_encRaw_le_of hobj).trans (Nat.mul_le_mul_right _ hno)
  have h5 : (Turing.MultiTapeTM.encList encRaw ([] : List RawPoly)).length = 0 := rfl
  rw [h5]
  omega

/-! ### The data and the coefficients of `B̃` -/

theorem abs_clampAbs_le {B : ℚ} (hB : 0 ≤ B) (x : ℚ) : |clampAbs B x| ≤ B := by
  rw [clampAbs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- **The re-rounded data** are multiples of `2^{-p}` of absolute value at most `n² + 1`. -/
theorem qb_whitenData {n d : ℕ} (p : ℕ) (Y : Fin n → Fin d → ℚ) (j : Fin n) (a : Fin d) :
    QB (2 ^ p) ((n : ℚ) ^ 2 + 1) (whitenData p Y j a) := by
  set x := ((whitenMat (secondMoment Y)).mulVec (Y j)) a
  have e : whitenData p Y j a = (⌊(2 : ℚ) ^ p * clampAbs ((n : ℚ) ^ 2) x⌋ : ℚ) / 2 ^ p := rfl
  have h2 : (0 : ℚ) < 2 ^ p := by positivity
  refine ⟨?_, ⌊(2 : ℚ) ^ p * clampAbs ((n : ℚ) ^ 2) x⌋, ?_⟩
  · rw [e, abs_div, abs_of_pos h2, div_le_iff₀ h2]
    set y := (2 : ℚ) ^ p * clampAbs ((n : ℚ) ^ 2) x
    have hy : |y| ≤ 2 ^ p * (n : ℚ) ^ 2 := by
      rw [abs_mul, abs_of_pos h2]
      exact mul_le_mul_of_nonneg_left (abs_clampAbs_le (by positivity) x) h2.le
    have hf : |(⌊y⌋ : ℚ)| ≤ |y| + 1 := by
      have h1 := Int.floor_le y
      have h3 := Int.sub_one_lt_floor y
      rw [abs_le] at ⊢
      have := abs_nonneg y
      constructor
      · linarith [neg_abs_le y]
      · linarith [le_abs_self y]
    have h1 : (1 : ℚ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    nlinarith
  · rw [e]
    push_cast
    field_simp

/-- The scaling `(n t^t)⁻¹` of `B̃`. -/
theorem qb_inv_mul {nY t : ℕ} (hnY : 0 < nY) (ht : 0 < t) :
    QB (nY * t ^ t) 1 (((nY : ℚ) * t ^ t)⁻¹) := by
  have h1 : (1 : ℚ) ≤ (nY : ℚ) * t ^ t := by
    have : (1 : ℕ) ≤ nY * t ^ t := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  refine ⟨?_, 1, ?_⟩
  · rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ h1
  · push_cast
    field_simp

/-- **The coefficients of `B̃`**, for `nY` points that are multiples of `1/Dz` of absolute value
at most `Mz`: multiples of `1/(nY t^t Dz^(2t))` of absolute value at most
`nY d^(2t) Mz^(2t)`. -/
theorem qb_bOf {nY d : ℕ} (Y : Fin nY → Fin d → ℚ) {Dz : ℕ} {Mz : ℚ} (hMz : 0 ≤ Mz)
    (hz : ∀ j a, QB Dz Mz (Y j a)) (hnY : 0 < nY) {t : ℕ} (ht : 0 < t) (Lb : ℕ) (γ : List ℕ) :
    QB (nY * t ^ t * Dz ^ (2 * t)) (((nY * d ^ (2 * t) : ℕ) : ℚ) * Mz ^ (2 * t))
      (bOf Y t Lb γ) := by
  have hterm : ∀ τ ∈ bRaw Y t Lb, QB (nY * t ^ t * Dz ^ (2 * t)) (Mz ^ (2 * t)) τ.2 := by
    intro τ hτ
    obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hτ
    obtain ⟨τ', hτ', rfl⟩ := List.mem_map.1 hj
    obtain ⟨tup, htup, rfl⟩ := mem_prodRaw hτ'
    have h := qb_prod_of_forall₂ (D := Dz) (M := Mz) htup fun f hf τ hτ => by
      rw [(List.mem_replicate.1 hf).2] at hτ
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hτ
      exact hz j a
    rw [List.length_replicate] at h
    have := (qb_inv_mul hnY ht).mul h
    rwa [one_mul] at this
  have hlen : (bRaw Y t Lb).length ≤ nY * d ^ (2 * t) := by
    refine (Lay.length_flatMap_le _ _ fun j _ => ?_).trans (by rw [List.length_finRange])
    rw [smul, List.length_map]
    have := length_prodRaw_replicate_le d Lb (2 * t) (yLin Y j)
    rwa [yLin, List.length_map, List.length_finRange] at this
  have hs := QB.sum (l := ((bRaw Y t Lb).filter fun τ => expo d τ.1 = γ).map Prod.snd)
    fun q hq => by
      obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hq
      exact hterm τ (List.mem_of_mem_filter hτ)
  refine hs.mono (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hMz _))
  rw [List.length_map]
  exact_mod_cast (List.length_filter_le _ _).trans hlen

/-! ### Arithmetic -/

/-- **The size arithmetic**: with every count at most `Z` (up to constant factors) and
`κ ≤ 16 Z²`, the program has size at most `Z^6 - 2`. -/
theorem size_arith {Z N t κ F nc no E S : ℕ} (hZ : 2 ^ 20 ≤ Z) (hN : N ≤ 4 * Z + 1)
    (hE : E ≤ 5 * Z + 1) (hS : S ≤ Z) (ht : 64 * t ≤ Z) (hκ : κ ≤ 16 * Z ^ 2)
    (hF : F ≤ 2 * Z ^ 2) (hnc : nc ≤ 7 * Z) (hno : no ≤ Z) :
    2 * N + 1 + (2 * (64 * t) + 1 +
      (2 * (nc * (2 * (F * (2 * (2 * (2 * S + E) + 1 + (3 * κ + 3)) + 1)) + 1)) + 1 +
        (2 * (no * (2 * (2 * (2 * S + E) + 1 + (3 * κ + 3)) + 1)) + 1))) + 2 ≤ Z ^ 6 := by
  have hZ1 : 15 ≤ Z := le_trans (by norm_num) hZ
  have hTb : 2 * (2 * (2 * S + E) + 1 + (3 * κ + 3)) + 1 ≤ 99 * Z ^ 2 := by nlinarith
  calc 2 * N + 1 + (2 * (64 * t) + 1 +
      (2 * (nc * (2 * (F * (2 * (2 * (2 * S + E) + 1 + (3 * κ + 3)) + 1)) + 1)) + 1 +
        (2 * (no * (2 * (2 * (2 * S + E) + 1 + (3 * κ + 3)) + 1)) + 1))) + 2
      ≤ 2 * (4 * Z + 1) + 1 + (2 * Z + 1 +
        (2 * (7 * Z * (2 * (2 * Z ^ 2 * (99 * Z ^ 2)) + 1)) + 1 +
          (2 * (Z * (99 * Z ^ 2)) + 1))) + 2 := by gcongr
    _ = 5544 * Z ^ 5 + 198 * Z ^ 3 + 24 * Z + 8 := by ring
    _ ≤ Z ^ 6 := by
      have h1 : 1 ≤ Z := le_trans (by norm_num) hZ
      have h3 : Z ^ 3 ≤ Z ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
      have h0 : Z ≤ Z ^ 5 := by
        calc Z = Z ^ 1 := (pow_one Z).symm
          _ ≤ Z ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
      have h00 : 1 ≤ Z ^ 5 := Nat.one_le_pow _ _ h1
      have h6 : 2 ^ 20 * Z ^ 5 ≤ Z ^ 6 := by
        rw [pow_succ Z 5, mul_comm]
        exact Nat.mul_le_mul_left _ hZ
      have : (2 : ℕ) ^ 20 = 1048576 := by norm_num
      omega

/-- `n ≤ 2^n`. -/
theorem le_two_pow_self' (n : ℕ) : n ≤ 2 ^ n := Nat.lt_two_pow_self.le

/-- `n² + 1 ≤ 2^(2n)`. -/
theorem sq_add_one_le_two_pow (n : ℕ) : n ^ 2 + 1 ≤ 2 ^ (2 * n) := by
  have h : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  calc n ^ 2 + 1 ≤ (n + 1) ^ 2 := by nlinarith
    _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]

/-- `64 t ≤ 2^(4t)` for `t ≥ 2`. -/
theorem sixtyfour_mul_le {t : ℕ} (ht : 2 ≤ t) : 64 * t ≤ 2 ^ (4 * t) := by
  have h1 : t ≤ 2 ^ t := le_two_pow_self' t
  have h2 : 64 ≤ 2 ^ (3 * t) :=
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (3 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 64 * t ≤ 2 ^ (3 * t) * 2 ^ t := Nat.mul_le_mul h2 h1
    _ = 2 ^ (4 * t) := by rw [← pow_add]; ring_nf

/-- `(2d + 2)^(2t) ≤ n` when `(d + 1)^(4t) ≤ n` and `2^(4t) ≤ n`. -/
theorem two_d_two_pow_le {d t n : ℕ} (hd : (d + 1) ^ (4 * t) ≤ n)
    (h2 : 2 ^ (4 * t) ≤ n) : (2 * d + 2) ^ (2 * t) ≤ n := by
  have hsq : ((2 * d + 2) ^ (2 * t)) ^ 2 ≤ n ^ 2 := by
    calc ((2 * d + 2) ^ (2 * t)) ^ 2 = 2 ^ (4 * t) * (d + 1) ^ (4 * t) := by
          rw [← pow_mul, show 2 * d + 2 = 2 * (d + 1) by ring, mul_pow]; ring_nf
      _ ≤ n * n := Nat.mul_le_mul h2 hd
      _ = n ^ 2 := (sq n).symm
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 hsq

/-- **The grid precision** is at most `4 n + 3`. -/
theorem gridPrec_le {R : ℚ} {n d : ℕ} (hR : ⌈R ^ 2⌉₊ + 2 ≤ n) (hd : d + 1 ≤ n) :
    gridPrec R n d ≤ 4 * n + 3 := by
  have h : 4 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2 ≤ 2 ^ (4 * n + 2) := by
    have h1 := le_two_pow_self' n
    calc 4 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2 ≤ 4 * 2 ^ n * 2 ^ n * (2 ^ n) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (hR.trans h1)) (hd.trans h1))
            (Nat.pow_le_pow_left h1 2)
      _ = 2 ^ (4 * n + 2) := by ring
  have := Nat.clog_le_of_le_pow h
  unfold gridPrec
  omega

/-- The bound on the codes of the products of `2s + 1` data values. -/
theorem data_prod_lt {n s p : ℕ} (hn : 9 ≤ n) (hs : s ≤ n) (hp : p ≤ 4 * n + 3) :
    (n ^ 2 + 1) ^ (2 * s + 1) * (2 ^ p) ^ (2 * s + 1) < 2 ^ (16 * n ^ 2) := by
  have h1 := sq_add_one_le_two_pow n
  calc (n ^ 2 + 1) ^ (2 * s + 1) * (2 ^ p) ^ (2 * s + 1)
      ≤ (2 ^ (2 * n)) ^ (2 * s + 1) * (2 ^ (4 * n + 3)) ^ (2 * s + 1) := by
        exact Nat.mul_le_mul (Nat.pow_le_pow_left h1 _)
          (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hp) _)
    _ = 2 ^ ((6 * n + 3) * (2 * s + 1)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
    _ < 2 ^ (16 * n ^ 2) := by
        refine Nat.pow_lt_pow_right (by norm_num) ?_
        have : (6 * n + 3) * (2 * s + 1) ≤ (6 * n + 3) * (2 * n + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        nlinarith

/-- The bound on the codes of the coefficients `K b_γ`. -/
theorem bcoef_lt {n d s t p : ℕ} (hn : 9 ≤ n) (hs : s ≤ n) (ht : t ≤ n) (hp : p ≤ 4 * n + 3)
    (hd : d ^ (2 * t) ≤ n) :
    (256 * s) ^ t * (n * d ^ (2 * t) * (n ^ 2 + 1) ^ (2 * t)) *
      (1 * (n * t ^ t * (2 ^ p) ^ (2 * t))) < 2 ^ (16 * n ^ 2) := by
  have h1 := le_two_pow_self' n
  have h2 := sq_add_one_le_two_pow n
  have hK : 256 * s ≤ 2 ^ (n + 8) := by
    rw [pow_add]
    have := hs.trans h1
    omega
  calc (256 * s) ^ t * (n * d ^ (2 * t) * (n ^ 2 + 1) ^ (2 * t)) *
      (1 * (n * t ^ t * (2 ^ p) ^ (2 * t)))
      ≤ (2 ^ (n + 8)) ^ t * (2 ^ n * 2 ^ n * (2 ^ (2 * n)) ^ (2 * t)) *
        (1 * (2 ^ n * (2 ^ n) ^ t * (2 ^ (4 * n + 3)) ^ (2 * t))) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hK t)
          (Nat.mul_le_mul (Nat.mul_le_mul h1 (hd.trans h1)) (Nat.pow_le_pow_left h2 _)))
          (Nat.mul_le_mul le_rfl (Nat.mul_le_mul (Nat.mul_le_mul h1
            (Nat.pow_le_pow_left (ht.trans h1) t))
            (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hp) _)))
    _ = 2 ^ ((n + 8) * t + (n + n + 2 * n * (2 * t)) + (n + n * t + (4 * n + 3) * (2 * t))) := by
        simp only [← pow_mul, ← pow_add, one_mul]
    _ < 2 ^ (16 * n ^ 2) := by
        refine Nat.pow_lt_pow_right (by norm_num) ?_
        have : n * t ≤ n * n := Nat.mul_le_mul_left _ ht
        nlinarith

/-! ### The programs of the rounds -/

/-- The counts of the program under the guard: every list of exponent vectors, every product,
and the dimension are at most `n`. -/
theorem counts_le {d s t m Lb n : ℕ} (hfit : Fits d s t m Lb) (hms : m * s = t) (ht : 1 ≤ t)
    (hdpow : (d + 1) ^ (4 * t) ≤ n) (htpow : 2 ^ (4 * t) ≤ n) :
    d + 1 ≤ n ∧ (Mono.allB Lb d (2 * s)).length ≤ n ∧
      (Mono.allB Lb d t).length * (Mono.allB Lb d t).length ≤ n ∧
      (gams d t Lb).length ≤ n ∧ (Mono.allB Lb d (2 * s)).length ^ m ≤ n ∧
      (Mono.allB Lb d t).length * (Mono.allB Lb d t).length ^ 2 ≤ n ∧
      (2 * d) ^ (2 * s) ≤ n ∧ d ^ (2 * t) ≤ n := by
  have hst := hfit.2.1
  have hA : Mono.allB Lb d (2 * s) = Mono.all d (2 * s) := allB_eq_of_fits hfit (by omega)
  have hB : Mono.allB Lb d t = Mono.all d t := allB_eq_of_fits hfit (by omega)
  have hG : gams d t Lb = Mono.all d (2 * t) := allB_eq_of_fits hfit le_rfl
  have hd1 : 1 ≤ d + 1 := by omega
  have hpow : ∀ e ≤ 4 * t, (d + 1) ^ e ≤ n := fun e he =>
    (Nat.pow_le_pow_right hd1 he).trans hdpow
  have hAl : (Mono.all d (2 * s)).length ≤ (d + 1) ^ (2 * s) := Mono.length_all_le _ _
  have hBl : (Mono.all d t).length ≤ (d + 1) ^ t := Mono.length_all_le _ _
  rw [hA, hB, hG]
  refine ⟨?_, hAl.trans (hpow _ (by omega)), ?_, (Mono.length_all_le _ _).trans (hpow _ (by omega)),
    ?_, ?_, ?_, ?_⟩
  · have : d + 1 ≤ (d + 1) ^ (4 * t) := Nat.le_self_pow (by omega) _
    omega
  · calc (Mono.all d t).length * (Mono.all d t).length ≤ (d + 1) ^ t * (d + 1) ^ t :=
          Nat.mul_le_mul hBl hBl
      _ = (d + 1) ^ (2 * t) := by ring
      _ ≤ n := hpow _ (by omega)
  · calc (Mono.all d (2 * s)).length ^ m ≤ ((d + 1) ^ (2 * s)) ^ m := Nat.pow_le_pow_left hAl _
      _ = (d + 1) ^ (2 * t) := by rw [← pow_mul, ← hms]; ring_nf
      _ ≤ n := hpow _ (by omega)
  · calc (Mono.all d t).length * (Mono.all d t).length ^ 2 ≤ (d + 1) ^ t * ((d + 1) ^ t) ^ 2 :=
          Nat.mul_le_mul hBl (Nat.pow_le_pow_left hBl 2)
      _ = (d + 1) ^ (3 * t) := by ring
      _ ≤ n := hpow _ (by omega)
  · calc (2 * d) ^ (2 * s) ≤ (2 * d + 2) ^ (2 * t) :=
          (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ n := two_d_two_pow_le hdpow htpow
  · exact (Nat.pow_le_pow_left (by omega) _).trans (hpow _ (by omega))

/-- The coefficient bounds under the guard, with `κ = 16 n²`. -/
theorem coef_bounds {n d s t p K : ℕ} (hn : 9 ≤ n) (hd : 1 ≤ d) (hs : 1 ≤ s) (hst : s ≤ t)
    (htn : t ≤ n) (hp : p ≤ 4 * n + 3) (hdt : d ^ (2 * t) ≤ n) (hK : K = (256 * s) ^ t) :
    ((n : ℚ) ^ 2 + 1) ^ (2 * s + 1) * (((2 ^ p) ^ (2 * s + 1) : ℕ) : ℚ) < 2 ^ (16 * n ^ 2) ∧
      (2 ^ p) ^ (2 * s + 1) < 2 ^ (16 * n ^ 2) ∧
      (K : ℚ) * (((n * d ^ (2 * t) : ℕ) : ℚ) * ((n : ℚ) ^ 2 + 1) ^ (2 * t)) *
        ((1 * (n * t ^ t * (2 ^ p) ^ (2 * t)) : ℕ) : ℚ) < 2 ^ (16 * n ^ 2) ∧
      1 * (n * t ^ t * (2 ^ p) ^ (2 * t)) < 2 ^ (16 * n ^ 2) := by
  have h1 := data_prod_lt hn (hst.trans htn) hp
  have h2 := bcoef_lt hn (hst.trans htn) htn hp hdt
  rw [← hK] at h2
  refine ⟨by exact_mod_cast h1, lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) h1,
    by exact_mod_cast h2, lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ?_) h2⟩
  have hK0 : 0 < K := by rw [hK]; exact pow_pos (by omega) _
  have : 0 < n * d ^ (2 * t) * (n ^ 2 + 1) ^ (2 * t) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos hd _)) (by positivity)
  exact Nat.mul_pos hK0 this

/-- **The program of a round has size at most `n^6 - 2`** on the guard, for the whitened data
`z = whitenData (gridPrec R n d) Y`, the coefficients `b = bOf z t Lb`, any list `Rem` of points
without repetitions, and a budget that cuts nothing. -/
theorem length_roundProb_le {k : ℕ} {w R : ℚ} {n d : ℕ} (hG : NumGuard k w R n d)
    (Y : Fin n → Fin d → ℚ) {Lb : ℕ} (hfit : Fits d (sDeg w) (tDeg w R) (mDeg w R) Lb)
    {Rem : List (Fin n)} (hRem : Rem.Nodup) :
    (encProblem (roundProb (srPar w R n Lb) (whitenData (gridPrec R n d) Y)
      (bOf (whitenData (gridPrec R n d) Y) (tDeg w R) Lb) Rem)).length + 2 ≤ n ^ 6 := by
  have hs8 : 8 ≤ sDeg w := eight_le_sDeg w
  have hst : sDeg w ≤ tDeg w R := sDeg_le_tDeg w R
  have hms : mDeg w R * sDeg w = tDeg w R := mDeg_mul_sDeg w R
  have h4R : 4 * ⌈R ^ 2⌉₊ + 4 ≤ tDeg w R := four_ceil_le_tDeg w R
  have hn20 := hG.n_ge
  have hdpow := hG.dpow_le
  have htpow := hG.tpow_le
  have hd1 := hG.one_le_d
  have hn9 : 9 ≤ n := le_trans (by norm_num) hn20
  have ht64 : 64 * tDeg w R ≤ n := (sixtyfour_mul_le (by omega)).trans htpow
  obtain ⟨hdn, hAn, hBn, hGn, hAm, hBB, h2d, hdt⟩ :=
    counts_le hfit hms (by omega) hdpow htpow
  have hRemn : Rem.length ≤ n := by
    have := hRem.length_le_card
    rwa [Fintype.card_fin] at this
  have hp4 : gridPrec R n d ≤ 4 * n + 3 := gridPrec_le (by omega) hdn
  obtain ⟨hzκ, hzκ', hbκ, hbκ'⟩ :=
    coef_bounds hn9 hd1 (by omega) hst (by omega) hp4 hdt (rfl : Kc w R = (256 * sDeg w) ^ tDeg w R)
  have hκ1 : 1 ≤ 16 * n ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hF : n * n + 4 * n + 2 ≤ 2 * n ^ 2 := by
    have : 5 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    rw [sq]
    omega
  set s := sDeg w with hs
  set t := tDeg w R with ht
  set m := mDeg w R with hm
  set p := gridPrec R n d with hp
  set z := whitenData p Y with hz
  set L := lay Rem.length d s t Lb with hL
  set κ := 16 * n ^ 2 with hκ
  have hgood := good_lay (n := Rem.length) hfit
  -- the coefficients
  have hzq : ∀ i a, QB (2 ^ p) ((n : ℚ) ^ 2 + 1) (remPts z Rem i a) := fun i a =>
    qb_whitenData p Y (Rem.get i) a
  have hMz : (1 : ℚ) ≤ (n : ℚ) ^ 2 + 1 := by have := sq_nonneg (n : ℚ); linarith
  have hbq : ∀ γ ∈ gams d t Lb, QB (1 * (n * t ^ t * (2 ^ p) ^ (2 * t)))
      ((Kc w R : ℚ) * (((n * d ^ (2 * t) : ℕ) : ℚ) * ((n : ℚ) ^ 2 + 1) ^ (2 * t)))
      ((Kc w R : ℚ) * bOf z t Lb γ) := fun γ _ =>
    (QB.natCast (Kc w R)).mul
      (qb_bOf z (by positivity) (fun j a => qb_whitenData p Y j a) (by omega) (by omega) Lb γ)
  have hBdκ : CoefOK κ ((ballBd n : ℕ) : ℚ) := by
    refine coefOK_of_QB one_pos (QB.natCast _) ?_ (Nat.one_lt_two_pow (by omega))
    have h4 : 4 * n ^ 2 < κ := by rw [hκ]; have := pow_pos (by omega : 0 < n) 2; omega
    have : ballBd n * 1 < 2 ^ κ := by
      rw [mul_one, ballBd]
      exact Nat.pow_lt_pow_right (by norm_num) h4
    exact_mod_cast this
  have hDb : 0 < 1 * (n * t ^ t * (2 ^ p) ^ (2 * t)) :=
    Nat.mul_pos one_pos (Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos (by omega) _))
      (pow_pos (pow_pos two_pos _) _))
  -- the program
  have hP : roundProb (srPar w R n Lb) z (bOf z t Lb) Rem =
      problem (remPts z Rem) (bOf z t Lb) s t m (Kc w R) (ballBd n) Lb := rfl
  rw [hP]
  have hN : L.N ≤ 4 * n + 1 := by
    change Rem.length + d + 1 + (Mono.allB Lb d (2 * s)).length +
      (Mono.allB Lb d t).length * (Mono.allB Lb d t).length ≤ 4 * n + 1
    omega
  have hF3 : L.A + L.n * (2 * L.d) ^ (2 * s) ≤ n * n + 4 * n + 2 := by
    change (Mono.allB Lb d (2 * s)).length + Rem.length * (2 * d) ^ (2 * s) ≤ _
    have := Nat.mul_le_mul hRemn h2d
    omega
  have hF4 : (gams d t Lb).length + L.A ^ m + L.B * L.B ^ 2 ≤ n * n + 4 * n + 2 := by
    change (gams d t Lb).length + (Mono.allB Lb d (2 * s)).length ^ m +
      (Mono.allB Lb d t).length * (Mono.allB Lb d t).length ^ 2 ≤ _
    omega
  have hcons : ∀ f ∈ L.constraints (remPts z Rem) (gams d t Lb) (bOf z t Lb) s m (Kc w R)
      (ballBd n) Lb, (∀ τ ∈ f, TermOK (L.N + L.d) (4 * t + 2) κ τ) ∧
        f.length ≤ n * n + 4 * n + 2 := fun f hf =>
    ⟨L.termOK_of_mem_constraints (remPts z Rem) (bOf z t Lb) (Kc w R) (ballBd n) (by omega)
        hst hms.le (fun e he => (hgood.memA e).1 he) (fun e he => (hgood.memB e).1 he)
        (fun e he => (hgood.memG e).1 he) (by positivity) hMz hzq hκ1 hzκ hzκ' hDb
        hbq hbκ hbκ' hBdκ hf,
      L.length_le_of_mem_constraints (remPts z Rem) (bOf z t Lb) (Kc w R) (ballBd n)
        (by omega) (by change Rem.length + 2 ≤ _; omega) hF3 hF4 hf⟩
  have hnc : (L.constraints (remPts z Rem) (gams d t Lb) (bOf z t Lb) s m (Kc w R) (ballBd n)
      Lb).length ≤ 6 * n + 3 := by
    calc _ = 3 + 2 * L.n + 2 * L.A + 2 * (gams d t Lb).length :=
          L.length_constraints (remPts z Rem) (gams d t Lb) (bOf z t Lb) s m (Kc w R) (ballBd n) Lb
      _ ≤ 6 * n + 3 := by
          change 3 + 2 * Rem.length + 2 * (Mono.allB Lb d (2 * s)).length +
            2 * (gams d t Lb).length ≤ _
          omega
  have hobj := L.termOK_objRaw (t := t) hκ1
  have hno : L.objRaw.length ≤ n := by
    simp only [Lay.objRaw, List.length_map, List.length_finRange]
    exact hRemn
  have hmain := length_encProblem_le
    (problem (remPts z Rem) (bOf z t Lb) s t m (Kc w R) (ballBd n) Lb)
    (E := L.N + L.d) (S := 4 * t + 2) (κ := κ) (F := n * n + 4 * n + 2) (nc := 6 * n + 3)
    (no := n) hcons hnc hobj hno rfl
  refine le_trans (Nat.add_le_add_right hmain 2) ?_
  have hE : L.N + L.d ≤ 5 * n + 1 := by change L.N + d ≤ _; omega
  exact size_arith hn20 hN hE (by omega) ht64 le_rfl hF (by omega) le_rfl

/-! ### The budget -/

/-- **On the guard, a budget `Lb ≥ n^(6 (64 t + 1))` cuts nothing and suffices for every
round.** -/
theorem budget_facts {k : ℕ} {w R : ℚ} {n d : ℕ} (hG : NumGuard k w R n d)
    (Y : Fin n → Fin d → ℚ) {Lb : ℕ} (hLb : n ^ (6 * (64 * tDeg w R + 1)) ≤ Lb) :
    Fits d (sDeg w) (tDeg w R) (tDeg w R / sDeg w) Lb ∧
      BudgetFits (srPar w R n Lb) (whitenData (gridPrec R n d) Y)
        (bOf (whitenData (gridPrec R n d) Y) (tDeg w R) Lb) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hG.n_ge
  have hst : sDeg w ≤ tDeg w R := sDeg_le_tDeg w R
  have h2d : (2 * d + 2) ^ (2 * tDeg w R) ≤ n := two_d_two_pow_le hG.dpow_le hG.tpow_le
  have hnLb : n ≤ Lb :=
    (Nat.le_self_pow (by omega) n).trans hLb
  have hfit : Fits d (sDeg w) (tDeg w R) (tDeg w R / sDeg w) Lb :=
    ⟨Nat.div_mul_le_self _ _, hst, h2d.trans hnLb⟩
  refine ⟨hfit, fun Rem hRem => ?_⟩
  have h := length_roundProb_le hG Y hfit hRem
  calc ((encProblem (roundProb (srPar w R n Lb) (whitenData (gridPrec R n d) Y)
        (bOf (whitenData (gridPrec R n d) Y) (tDeg w R) Lb) Rem)).length + 2) ^
          (64 * (srPar w R n Lb).t + 1)
      ≤ (n ^ 6) ^ (64 * tDeg w R + 1) := Nat.pow_le_pow_left h _
    _ = n ^ (6 * (64 * tDeg w R + 1)) := (pow_mul _ _ _).symm
    _ ≤ Lb := hLb

/-- **The budget constant** `C₁ = 2^14` of the algorithm. -/
def budgetC : ℕ := 2 ^ 14

/-- `6 (64 t + 1) ≤ 2^14 (⌈R²⌉ + logInv w + 1)`. -/
theorem exponent_le_budgetC (w R : ℚ) :
    6 * (64 * tDeg w R + 1) ≤ budgetC * (⌈R ^ 2⌉₊ + logInv w + 1) := by
  have h1 := tDeg_le w R
  have h2 := sDeg_le w
  unfold budgetC
  omega

/-- **The budget `radiusTime budgetC x` is at least `n^(6 (64 t + 1))`** for an input with `n`
points. -/
theorem pow_le_budgetOf (x : RadiusInput) :
    x.points.length ^ (6 * (64 * tDeg x.wmin x.R + 1)) ≤ budgetOf budgetC x := by
  have hn := RT.length_points_le x
  calc x.points.length ^ (6 * (64 * tDeg x.wmin x.R + 1))
      ≤ ((encRadiusInput x).length + 2) ^ (6 * (64 * tDeg x.wmin x.R + 1)) :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ ((encRadiusInput x).length + 2) ^ (budgetC * (⌈x.R ^ 2⌉₊ + logInv x.wmin + 1)) :=
        Nat.pow_le_pow_right (by omega) (exponent_le_budgetC x.wmin x.R)
    _ = budgetOf budgetC x := rfl

end BS23.SmallRadius
