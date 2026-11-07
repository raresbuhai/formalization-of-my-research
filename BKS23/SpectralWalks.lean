module

public import Background.RandomGraph

/-!
# Counting walks for the moment method

The combinatorial core of [BKS23, Fact 3.14] (`BKS23/SpectralNorm.lean`): a bound on the sum, over
the walks of length `L` on `n` vertices from a given vertex, without loops, in which every edge is
traversed `0` or at least `2` times, of `K^(L - 2s)` with `s` the number of distinct edges, which
is the product over the steps of `K^[c ≥ 2]` (`c` the earlier traversals of the step's edge). With
`B = L + 1` and `K² B⁴ ≤ n`, the sum is at most `(3 √n)^L` (`BKS23.Spectral.Walk.bound_le`).

A walk is built step by step; its state is the current vertex `a` and the list `p` of the earlier
vertices, the latest first. A step `a → b` is of one of four kinds, by the number `c` of earlier
traversals of the edge `ab` (`Walk.cnt`): to a new vertex (`c = 0`), to an old vertex along a new
edge (`c = 0`), closing an edge (`c = 1`), or along an edge traversed at least twice (`c ≥ 2`).
The open degree `D(x)` of a vertex (`Walk.deg`) is the number of edges at `x` traversed exactly
once. A closing step is forced if `D(a) = 1`. The steps get weights (`Walk.wt`): `1/n` to a new
vertex, `1` for a forced closing step and `1/B` otherwise, and from each state the weights of the
next steps add up to at most `3` (`Walk.sum_wt_le`).

The potential `Φ = ∑_x (D(x) - 2)⁺ + [D(a) ≥ 2]` (`Walk.pot`) does not change on a step to a new
vertex, grows by at most `2` along a new edge to an old vertex and by at most `1` along an edge
traversed at least twice, and drops by at least `1` on a closing step that is not forced. With
the number `O` of edges traversed exactly once (`Walk.opens`), one step multiplies the weight
`K^[c ≥ 2] B^Φ / √n^O` by at most `√n` times the weight of the step (`Walk.step_le`). By
induction on the length, the walks of length `t` from a state that end with every edge traversed
`0` or at least `2` times have total `∏ K^[c ≥ 2]` at most `(3 √n)^t B^Φ / √n^O`
(`Walk.bound_le`).
-/

@[expose] public section

open Finset

namespace BKS23.Spectral.Walk

variable {n : ℕ}

/-! ### Walks and their edge counts -/

/-- The number of times the walk `a :: p`, written backwards (`a` is the current vertex), traverses
the edge `e`. -/
def cnt : Fin n → List (Fin n) → Sym2 (Fin n) → ℕ
  | _, [], _ => 0
  | a, a' :: p, e => cnt a' p e + if s(a', a) = e then 1 else 0

@[simp] theorem cnt_nil (a : Fin n) (e : Sym2 (Fin n)) : cnt a [] e = 0 := rfl

theorem cnt_cons (a b : Fin n) (p : List (Fin n)) (e : Sym2 (Fin n)) :
    cnt b (a :: p) e = cnt a p e + if s(a, b) = e then 1 else 0 := rfl

/-- A walk only traverses edges between its vertices. -/
theorem cnt_eq_zero_of_notMem {a b : Fin n} {p : List (Fin n)} (hb : b ∉ a :: p) (y : Fin n) :
    cnt a p s(b, y) = 0 := by
  induction p generalizing a with
  | nil => rfl
  | cons a' p ih =>
    rw [cnt_cons]
    simp only [List.mem_cons, not_or] at hb
    rw [ih (by simp [hb.2.1, hb.2.2]), zero_add, ite_eq_right]
    intro h
    have : b ∈ s(a', a) := h ▸ Sym2.mem_mk_left b y
    rcases Sym2.mem_iff.1 this with h' | h'
    · exact hb.2.1 h'
    · exact hb.1 h'

/-! ### Open degrees, open edges and the potential -/

/-- The open degree of `x`: the number of `y` with the edge `xy` traversed exactly once. -/
def deg (a : Fin n) (p : List (Fin n)) (x : Fin n) : ℕ :=
  #{y | cnt a p s(x, y) = 1}

/-- The number of edges traversed exactly once. -/
def opens (a : Fin n) (p : List (Fin n)) : ℕ :=
  #{e : RandomGraph.Pair (Fin n) | cnt a p e.1 = 1}

/-- The potential `Φ = ∑_x (D(x) - 2)⁺ + [D(a) ≥ 2]`. -/
def pot (a : Fin n) (p : List (Fin n)) : ℕ :=
  (∑ x, (deg a p x - 2)) + if 2 ≤ deg a p a then 1 else 0

@[simp] theorem deg_nil (a x : Fin n) : deg a [] x = 0 := by simp [deg]

@[simp] theorem opens_nil (a : Fin n) : opens a [] = 0 := by simp [opens]

@[simp] theorem pot_nil (a : Fin n) : pot a [] = 0 := by simp [pot]

/-- Adding one to a function at one point changes the number of points where it is `1` by
`[f e₀ = 0] - [f e₀ = 1]`. -/
theorem card_filter_add_ite {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (e₀ : α) :
    #{e | f e + (if e₀ = e then 1 else 0) = 1} + (if f e₀ = 1 then 1 else 0) =
      #{e | f e = 1} + if f e₀ = 0 then 1 else 0 := by
  simp only [card_filter]
  rw [← add_sum_erase _ _ (mem_univ e₀), ← add_sum_erase _ _ (mem_univ e₀)]
  have hrest : ∑ x ∈ univ.erase e₀, (if f x + (if e₀ = x then 1 else 0) = 1 then 1 else 0) =
      ∑ x ∈ univ.erase e₀, (if f x = 1 then 1 else 0) :=
    sum_congr rfl fun x hx ↦ by rw [ite_eq_right (ne_of_mem_erase hx).symm, add_zero]
  rw [hrest, ite_eq_left rfl]
  split_ifs <;> omega

variable {a b : Fin n} {p : List (Fin n)}

theorem deg_cons_of_ne {x : Fin n} (hxa : x ≠ a) (hxb : x ≠ b) :
    deg b (a :: p) x = deg a p x := by
  unfold deg
  congr 1
  refine filter_congr fun y _ ↦ ?_
  rw [cnt_cons, ite_eq_right, add_zero]
  intro h
  have : x ∈ s(a, b) := h ▸ Sym2.mem_mk_left x y
  rcases Sym2.mem_iff.1 this with h' | h'
  · exact hxa h'
  · exact hxb h'

theorem deg_cons_left :
    deg b (a :: p) a + (if cnt a p s(a, b) = 1 then 1 else 0) =
      deg a p a + if cnt a p s(a, b) = 0 then 1 else 0 := by
  have h := card_filter_add_ite (fun y ↦ cnt a p s(a, y)) b
  have hf : ∀ y, cnt b (a :: p) s(a, y) = cnt a p s(a, y) + if b = y then 1 else 0 := by
    intro y
    rw [cnt_cons]
    congr 1
    exact if_congr Sym2.congr_right rfl rfl
  unfold deg
  simp_rw [hf]
  exact h

theorem deg_cons_right :
    deg b (a :: p) b + (if cnt a p s(a, b) = 1 then 1 else 0) =
      deg a p b + if cnt a p s(a, b) = 0 then 1 else 0 := by
  have h := card_filter_add_ite (fun y ↦ cnt a p s(b, y)) a
  have hf : ∀ y, cnt b (a :: p) s(b, y) = cnt a p s(b, y) + if a = y then 1 else 0 := by
    intro y
    rw [cnt_cons, Sym2.eq_swap (a := a)]
    congr 1
    exact if_congr Sym2.congr_right rfl rfl
  rw [Sym2.eq_swap (a := a)]
  unfold deg
  simp_rw [hf]
  exact h

theorem opens_cons (hab : a ≠ b) :
    opens b (a :: p) + (if cnt a p s(a, b) = 1 then 1 else 0) =
      opens a p + if cnt a p s(a, b) = 0 then 1 else 0 := by
  set e₀ : RandomGraph.Pair (Fin n) := ⟨s(a, b), by simpa using hab⟩
  have h := card_filter_add_ite (fun e : RandomGraph.Pair (Fin n) ↦ cnt a p e.1) e₀
  have hf : ∀ e : RandomGraph.Pair (Fin n),
      cnt b (a :: p) e.1 = cnt a p e.1 + if e₀ = e then 1 else 0 := by
    intro e
    rw [cnt_cons]
    congr 1
    exact if_congr ⟨fun h ↦ Subtype.ext h, fun h ↦ h ▸ rfl⟩ rfl rfl
  unfold opens
  simp_rw [hf]
  exact h

/-- The potential before and after a step, with the vertices other than `a` and `b` split off. -/
theorem pot_split (hab : a ≠ b) : ∃ S : ℕ,
    pot a p = S + (deg a p a - 2) + (deg a p b - 2) + (if 2 ≤ deg a p a then 1 else 0) ∧
    pot b (a :: p) = S + (deg b (a :: p) a - 2) + (deg b (a :: p) b - 2) +
      (if 2 ≤ deg b (a :: p) b then 1 else 0) := by
  have hb : b ∈ univ.erase a := mem_erase.2 ⟨hab.symm, mem_univ b⟩
  have hsplit : ∀ g : Fin n → ℕ, ∑ x, g x = (∑ x ∈ (univ.erase a).erase b, g x) + g a + g b := by
    intro g
    rw [← add_sum_erase _ _ (mem_univ a), ← add_sum_erase _ _ hb]
    ring
  refine ⟨∑ x ∈ (univ.erase a).erase b, (deg a p x - 2), ?_, ?_⟩
  · rw [pot, hsplit]
  · rw [pot, hsplit]
    congr 3
    refine sum_congr rfl fun x hx ↦ ?_
    have hxb := ne_of_mem_erase hx
    have hxa := ne_of_mem_erase (mem_of_mem_erase hx)
    rw [deg_cons_of_ne hxa hxb]

/-! ### Weights of steps -/

/-- The weight of the step from the state `a :: p` to `b`: `1/n` to a new vertex, `1` for a
forced closing step, `1/B` otherwise. -/
noncomputable def wt (B : ℝ) (a : Fin n) (p : List (Fin n)) (b : Fin n) : ℝ :=
  if b ∉ a :: p then 1 / n else if cnt a p s(a, b) = 1 ∧ deg a p a = 1 then 1 else 1 / B

/-- The factor `K^[c ≥ 2]` of the step from `a :: p` to `b`. -/
noncomputable def fac (K : ℝ) (a : Fin n) (p : List (Fin n)) (b : Fin n) : ℝ :=
  if 2 ≤ cnt a p s(a, b) then K else 1

theorem fac_nonneg {K : ℝ} (hK : 0 ≤ K) (a : Fin n) (p : List (Fin n)) (b : Fin n) :
    0 ≤ fac K a p b := by
  unfold fac
  split_ifs <;> linarith

theorem wt_nonneg {B : ℝ} (hB : 0 < B) (a : Fin n) (p : List (Fin n)) (b : Fin n) :
    0 ≤ wt B a p b := by
  unfold wt
  split_ifs <;> positivity

/-- **The weights of the next steps add up to at most `3`**: at most `n` new vertices of weight
`1/n`, at most `B` old ones of weight at most `1/B`, and at most one forced closing step. -/
theorem sum_wt_le {B : ℝ} (hn : 0 < n) (hB : 0 < B) (a : Fin n) (p : List (Fin n))
    (hcard : ((a :: p).toFinset.card : ℝ) ≤ B) : ∑ b, wt B a p b ≤ 3 := by
  set T := (a :: p).toFinset
  have hpt : ∀ b, wt B a p b ≤ 1 / n + (if b ∈ T then 1 / B else 0) +
      (if cnt a p s(a, b) = 1 ∧ deg a p a = 1 then 1 else 0) := by
    intro b
    have h1 : (0 : ℝ) ≤ 1 / n := by positivity
    have h2 : (0 : ℝ) ≤ 1 / B := by positivity
    unfold wt
    by_cases hb : b ∈ a :: p
    · have hbT : b ∈ T := List.mem_toFinset.2 hb
      rw [ite_eq_right (not_not.2 hb), ite_eq_left hbT]
      split_ifs <;> linarith
    · rw [ite_eq_left hb]
      split_ifs <;> linarith
  refine (sum_le_sum fun b _ ↦ hpt b).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  have h1 : (n : ℝ) * (1 / n) = 1 := by field_simp
  have h2 : (T.card : ℝ) * (1 / B) ≤ 1 := by
    rw [mul_one_div, div_le_one hB]
    exact hcard
  have h3 : ∑ b, (if cnt a p s(a, b) = 1 ∧ deg a p a = 1 then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hd : deg a p a = 1
    · simp only [hd, and_true]
      rw [sum_boole]
      have : (#{b | cnt a p s(a, b) = 1} : ℝ) = deg a p a := rfl
      rw [this, hd, Nat.cast_one]
    · simp [hd]
  linarith

/-! ### One step -/

/-- Cross-multiplying the inequality of one step. -/
theorem mul_div_le_mul_div {x y B s : ℝ} {P P' O O' : ℕ} (hs : 0 < s)
    (h : x * B ^ P' * s ^ O ≤ y * B ^ P * s ^ O') :
    x * (B ^ P' / s ^ O') ≤ y * (B ^ P / s ^ O) := by
  rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  exact h

/-- **One step**: the factor `K^[c ≥ 2]` of a step times the change of `B^Φ / √n^O` is at most
`√n` times the weight of the step. -/
theorem step_le {K B s : ℝ} (hn : (n : ℝ) = s ^ 2) (hs : 0 < s) (hB : 1 ≤ B)
    (hB3 : B ^ 3 ≤ s ^ 2) (hK : 0 ≤ K) (hKB : K * B ^ 2 ≤ s) (hab : a ≠ b) :
    fac K a p b * (B ^ pot b (a :: p) / s ^ opens b (a :: p)) ≤
      s * wt B a p b * (B ^ pot a p / s ^ opens a p) := by
  have hB0 : 0 < B := by linarith
  obtain ⟨S, hP, hP'⟩ := pot_split (p := p) hab
  have hDa := deg_cons_left (a := a) (b := b) (p := p)
  have hDb := deg_cons_right (a := a) (b := b) (p := p)
  have hO := opens_cons (p := p) hab
  have hca : cnt a p s(a, b) = 1 → 1 ≤ deg a p a := fun h ↦
    card_pos.2 ⟨b, mem_filter.2 ⟨mem_univ b, h⟩⟩
  have hcb : cnt a p s(a, b) = 1 → 1 ≤ deg a p b := fun h ↦
    card_pos.2 ⟨a, mem_filter.2 ⟨mem_univ a, by rw [Sym2.eq_swap]; exact h⟩⟩
  have hnew : b ∉ a :: p → cnt a p s(a, b) = 0 ∧ deg a p b = 0 := by
    intro hb
    refine ⟨by rw [Sym2.eq_swap]; exact cnt_eq_zero_of_notMem hb a, ?_⟩
    unfold deg
    rw [card_eq_zero, filter_eq_empty_iff]
    intro y _
    rw [cnt_eq_zero_of_notMem hb y]
    omega
  refine mul_div_le_mul_div hs ?_
  unfold fac wt
  set c := cnt a p s(a, b)
  set P := pot a p
  set P' := pot b (a :: p)
  set O := opens a p
  set O' := opens b (a :: p)
  by_cases hb : b ∈ a :: p
  · rw [ite_eq_right (not_not.2 hb)]
    rcases Nat.lt_trichotomy c 1 with hc | hc | hc
    · -- A new edge to an old vertex: `Φ` grows by at most `2`.
      have hc0 : c = 0 := by omega
      rw [hc0] at hDa hDb hO
      simp only [zero_ne_one, ite_false, ite_true, add_zero] at hDa hDb hO
      rw [ite_eq_right (show ¬ 2 ≤ c by omega),
        ite_eq_right (show ¬ (c = 1 ∧ deg a p a = 1) by omega)]
      have hPP : P' ≤ P + 2 := by
        rw [hP, hP']
        split_ifs <;> omega
      have hX : B ^ P' ≤ B ^ P * B ^ 2 := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hB hPP
      rw [hO, pow_succ]
      have hY : 0 ≤ B ^ P * s ^ O / B := by positivity
      calc 1 * B ^ P' * s ^ O ≤ B ^ P * B ^ 2 * s ^ O := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right hX (by positivity)
        _ = B ^ P * s ^ O / B * B ^ 3 := by field_simp
        _ ≤ B ^ P * s ^ O / B * s ^ 2 := mul_le_mul_of_nonneg_left hB3 hY
        _ = s * (1 / B) * B ^ P * (s ^ O * s) := by field_simp
    · -- A closing step: `Φ` drops, by at least `1` if the step is not forced.
      have hda := hca hc
      have hdb := hcb hc
      rw [hc] at hDa hDb hO
      simp only [one_ne_zero, ite_false, ite_true, add_zero] at hDa hDb hO
      rw [ite_eq_right (show ¬ 2 ≤ c by omega)]
      rw [← hO, pow_succ]
      by_cases hd : deg a p a = 1
      · rw [ite_eq_left ⟨hc, hd⟩]
        have hPP : P' ≤ P := by
          rw [hP, hP']
          split_ifs <;> omega
        have hX : B ^ P' ≤ B ^ P := pow_le_pow_right₀ hB hPP
        calc 1 * B ^ P' * (s ^ O' * s) ≤ B ^ P * (s ^ O' * s) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right hX (by positivity)
          _ = s * 1 * B ^ P * s ^ O' := by ring
      · rw [ite_eq_right fun h ↦ hd h.2]
        have hPP : P' + 1 ≤ P := by
          rw [hP, hP']
          split_ifs <;> omega
        have hX : B ^ P' * B ≤ B ^ P := by
          rw [← pow_succ]
          exact pow_le_pow_right₀ hB hPP
        calc 1 * B ^ P' * (s ^ O' * s) = B ^ P' * B * (s ^ O' * s) / B := by field_simp
          _ ≤ B ^ P * (s ^ O' * s) / B := by gcongr
          _ = s * (1 / B) * B ^ P * s ^ O' := by field_simp
    · -- An edge traversed at least twice: `Φ` grows by at most `1`, and the factor is `K`.
      have hc2 : ¬ c = 0 := by omega
      have hc1 : ¬ c = 1 := by omega
      simp only [hc2, hc1, ite_false, add_zero] at hDa hDb hO
      rw [ite_eq_left (show 2 ≤ c by omega), ite_eq_right fun h ↦ hc1 h.1]
      have hPP : P' ≤ P + 1 := by
        rw [hP, hP', hDa, hDb]
        split_ifs <;> omega
      have hX : B ^ P' ≤ B ^ P * B := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ hB hPP
      rw [hO]
      have hY : 0 ≤ B ^ P * s ^ O / B := by positivity
      calc K * B ^ P' * s ^ O ≤ K * (B ^ P * B) * s ^ O := by gcongr
        _ = B ^ P * s ^ O / B * (K * B ^ 2) := by field_simp
        _ ≤ B ^ P * s ^ O / B * s := mul_le_mul_of_nonneg_left hKB hY
        _ = s * (1 / B) * B ^ P * s ^ O := by ring
  · -- A new vertex: `Φ` does not change.
    rw [ite_eq_left hb]
    obtain ⟨hc0, hdb⟩ := hnew hb
    rw [hc0] at hDa hDb hO
    simp only [zero_ne_one, ite_false, ite_true, add_zero] at hDa hDb hO
    rw [ite_eq_right (by omega)]
    have hPP : P' = P := by
      rw [hP, hP', hDa, hDb, hdb]
      split_ifs <;> omega
    rw [hPP, hO, pow_succ, hn]
    field_simp
    exact le_refl _

/-! ### Walks -/

/-- The sum of the products of the factors `K^[c ≥ 2]` of the steps, over the walks of `t` more
steps from the state `a :: p`, without loops, that end with no edge traversed exactly once. -/
noncomputable def bound (K : ℝ) : ℕ → Fin n → List (Fin n) → ℝ
  | 0, a, p => if opens a p = 0 then 1 else 0
  | t + 1, a, p => ∑ b, if a ≠ b then fac K a p b * bound K t b (a :: p) else 0

theorem bound_nonneg {K : ℝ} (hK : 0 ≤ K) :
    ∀ (t : ℕ) (a : Fin n) (p : List (Fin n)), 0 ≤ bound K t a p
  | 0, a, p => by
    unfold bound
    split_ifs <;> norm_num
  | t + 1, a, p => by
    unfold bound
    refine sum_nonneg fun b _ ↦ ?_
    split_ifs
    · exact mul_nonneg (fac_nonneg hK a p b) (bound_nonneg hK t b (a :: p))
    · exact le_rfl

/-- **The walk bound**, by induction on the number `t` of steps left. -/
theorem bound_le_aux {K B s : ℝ} (hn : (n : ℝ) = s ^ 2) (hs : 0 < s) (hB : 1 ≤ B)
    (hB3 : B ^ 3 ≤ s ^ 2) (hK : 0 ≤ K) (hKB : K * B ^ 2 ≤ s) :
    ∀ (t : ℕ) (a : Fin n) (p : List (Fin n)), ((p.length + 1 + t : ℕ) : ℝ) ≤ B →
      bound K t a p ≤ (3 * s) ^ t * (B ^ pot a p / s ^ opens a p)
  | 0, a, p, _ => by
    unfold bound
    split_ifs with h
    · rw [h, pow_zero, pow_zero, div_one, one_mul]
      exact one_le_pow₀ hB
    · positivity
  | t + 1, a, p, hlen => by
    have hB0 : 0 < B := by linarith
    have hn0 : 0 < n := by
      have : (0 : ℝ) < n := by rw [hn]; positivity
      exact_mod_cast this
    have hcard : ((a :: p).toFinset.card : ℝ) ≤ B := by
      refine le_trans ?_ hlen
      have := List.toFinset_card_le (a :: p)
      simp only [List.length_cons] at this
      exact_mod_cast (by omega)
    unfold bound
    have hterm : ∀ b, (if a ≠ b then fac K a p b * bound K t b (a :: p) else 0) ≤
        (3 * s) ^ t * (s * wt B a p b * (B ^ pot a p / s ^ opens a p)) := by
      intro b
      split_ifs with hab
      · have ih := bound_le_aux hn hs hB hB3 hK hKB t b (a :: p) (by
          refine le_trans (le_of_eq ?_) hlen
          simp only [List.length_cons]
          push_cast
          ring)
        calc fac K a p b * bound K t b (a :: p)
            ≤ fac K a p b * ((3 * s) ^ t * (B ^ pot b (a :: p) / s ^ opens b (a :: p))) :=
              mul_le_mul_of_nonneg_left ih (fac_nonneg hK a p b)
          _ = (3 * s) ^ t * (fac K a p b * (B ^ pot b (a :: p) / s ^ opens b (a :: p))) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (step_le hn hs hB hB3 hK hKB hab) (by positivity)
      · have := wt_nonneg hB0 a p b
        positivity
    refine (sum_le_sum fun b _ ↦ hterm b).trans ?_
    rw [← mul_sum, ← sum_mul, ← mul_sum]
    have hsum := sum_wt_le hn0 hB0 a p hcard
    have hX : 0 ≤ B ^ pot a p / s ^ opens a p := by positivity
    calc (3 * s) ^ t * (s * (∑ b, wt B a p b) * (B ^ pot a p / s ^ opens a p))
        ≤ (3 * s) ^ t * (s * 3 * (B ^ pot a p / s ^ opens a p)) := by gcongr
      _ = (3 * s) ^ (t + 1) * (B ^ pot a p / s ^ opens a p) := by ring

/-- **The walk bound** from a single vertex: for `B ≥ L + 1` and `K B² ≤ √n`, `B³ ≤ n`, the walks
of length `L` without loops from `a`, ending with no edge traversed exactly once, have total
`∏ K^[c ≥ 2]` at most `(3 √n)^L`. -/
theorem bound_le {K B s : ℝ} (hn : (n : ℝ) = s ^ 2) (hs : 0 < s) (hB : 1 ≤ B)
    (hB3 : B ^ 3 ≤ s ^ 2) (hK : 0 ≤ K) (hKB : K * B ^ 2 ≤ s) {L : ℕ} (hL : (L + 1 : ℝ) ≤ B)
    (a : Fin n) : bound K L a [] ≤ (3 * s) ^ L := by
  have h := bound_le_aux hn hs hB hB3 hK hKB L a [] (by
    simp only [List.length_nil, zero_add]; push_cast; linarith)
  simpa using h

end BKS23.Spectral.Walk
