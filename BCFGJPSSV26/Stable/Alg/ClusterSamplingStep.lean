module

public import BCFGJPSSV26.Stable.Alg.ClusterSamplingBridge

/-!
# The analysis of the cluster sampling: one step

Every good chunk keeps the invariant (`BCFGJPSSV26.Stable.KSData.inv_step`), mode by mode, along
the case analysis of the proof of the cluster-sampling theorem [BCFGJPSSV26b, Section 4.7].
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

theorem nodup_append_singleton {α : Type*} {l : List α} {a : α} :
    (l ++ [a]).Nodup ↔ a ∉ l ∧ l.Nodup := by
  rw [← List.concat_eq_append, List.nodup_concat]

/-! ### The radii of the dummies -/

/-- Two grid points `x < x'` differ by at least `r₀/N⁴`. -/
theorem grid_sub_ge {N : ℕ} (hN : 1 ≤ N) {r₀ : ℚ} (hr : 0 ≤ r₀) {x x' : ℕ} (h : x < x') :
    r₀ / (N : ℚ) ^ 4 ≤ grid N r₀ x' - grid N r₀ x := by
  have hN' : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hq : (1 : ℚ) ≤ ((N : ℚ) + 1) / N := by rw [le_div_iff₀ (by linarith)]; linarith
  have h1 : (((N : ℚ) + 1) / N) ^ (x + 1) ≤ (((N : ℚ) + 1) / N) ^ x' := pow_le_pow_right₀ hq h
  have h2 : (1 : ℚ) ≤ (((N : ℚ) + 1) / N) ^ x := one_le_pow₀ hq
  have h3 : (((N : ℚ) + 1) / N) ^ (x + 1) - (((N : ℚ) + 1) / N) ^ x =
      (((N : ℚ) + 1) / N) ^ x * (1 / N) := by
    rw [pow_succ]
    field_simp
    ring
  have h4 : 1 / (N : ℚ) ≤ (((N : ℚ) + 1) / N) ^ x' - (((N : ℚ) + 1) / N) ^ x := by
    have : 1 / (N : ℚ) ≤ (((N : ℚ) + 1) / N) ^ x * (1 / N) :=
      le_mul_of_one_le_left (by positivity) h2
    linarith
  unfold grid
  have h5 : r₀ / (N : ℚ) ^ 4 = r₀ / (N : ℚ) ^ 3 * (1 / N) := by
    field_simp
  rw [h5, ← mul_sub]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **The dummies of one leader are distinct**: `ksRad` is injective in the index `t ≤ 2 s`. -/
theorem ksRad_inj {N s : ℕ} (hN : 1 ≤ N) {r₀ : ℚ} (hr : 0 < r₀) {x x' t t' : ℕ}
    (ht : t ≤ 2 * s) (ht' : t' ≤ 2 * s) (h : ksRad N s r₀ x t = ksRad N s r₀ x' t') :
    t = t' := by
  have hN' : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hc : (0 : ℚ) < (N : ℚ) ^ 4 * (2 * s + 2) := by positivity
  unfold ksRad at h
  -- the shifts differ by less than `r₀/N⁴`
  have hsh : ∀ {a b : ℕ}, a ≤ 2 * s → b ≤ 2 * s →
      r₀ * a / ((N : ℚ) ^ 4 * (2 * s + 2)) - r₀ * b / ((N : ℚ) ^ 4 * (2 * s + 2)) <
        r₀ / (N : ℚ) ^ 4 := by
    intro a b ha hb
    have ha' : (a : ℚ) ≤ 2 * s := by exact_mod_cast ha
    have hb' : (0 : ℚ) ≤ b := Nat.cast_nonneg b
    rw [← sub_div, ← mul_sub, div_lt_div_iff₀ hc (by positivity)]
    have : r₀ * (a - b) * N ^ 4 ≤ r₀ * (2 * s) * N ^ 4 := by
      have : r₀ * (a - b) ≤ r₀ * (2 * s) := mul_le_mul_of_nonneg_left (by linarith) hr.le
      exact mul_le_mul_of_nonneg_right this (by positivity)
    nlinarith [pow_pos (by linarith : (0 : ℚ) < N) 4]
  rcases lt_trichotomy x x' with hx | rfl | hx
  · have := grid_sub_ge hN hr.le hx
    have := hsh ht ht'
    linarith
  · have h' : r₀ * t / ((N : ℚ) ^ 4 * (2 * s + 2)) = r₀ * t' / ((N : ℚ) ^ 4 * (2 * s + 2)) := by
      linarith
    rw [div_left_inj' hc.ne', mul_right_inj' hr.ne'] at h'
    exact_mod_cast h'
  · have := grid_sub_ge hN hr.le hx
    have := hsh ht' ht
    linarith

/-- **The radius of a new dummy**: between the distance `d` and `(1 + κ + 6ε) per`. -/
theorem ksRad_bounds {N s : ℕ} (hN : 201 ≤ N) {r₀ : ℚ} (hr : 0 ≤ r₀) {x t : ℕ}
    (ht : t ≤ 2 * s) {d p κ : ℝ} (hp : 0 ≤ p) (hg1 : d ≤ (grid N r₀ x : ℝ))
    (hg2 : (grid N r₀ x : ℝ) ≤ (1 + 1 / (N : ℝ)) * d) (hd : d ≤ (1 + κ + 3 * (1 / N)) * p)
    (hκ : κ ≤ 23 / 65) (hr15 : (r₀ : ℝ) ≤ 15 * p) :
    d ≤ (ksRad N s r₀ x t : ℝ) ∧ (ksRad N s r₀ x t : ℝ) ≤ (1 + κ + 6 * (1 / N)) * p := by
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hr' : (0 : ℝ) ≤ r₀ := by exact_mod_cast hr
  have ht' : (t : ℝ) ≤ 2 * s := by exact_mod_cast ht
  have hc : (0 : ℝ) < (N : ℝ) ^ 4 * (2 * s + 2) := by positivity
  have hsh0 : 0 ≤ (r₀ : ℝ) * t / ((N : ℝ) ^ 4 * (2 * s + 2)) := by positivity
  have hsh1 : (r₀ : ℝ) * t / ((N : ℝ) ^ 4 * (2 * s + 2)) ≤ r₀ / (N : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ hc (by positivity)]
    have : (r₀ : ℝ) * t ≤ r₀ * (2 * s + 2) := mul_le_mul_of_nonneg_left (by linarith) hr'
    nlinarith [pow_pos hNpos 4]
  have hcast : (ksRad N s r₀ x t : ℝ) =
      (grid N r₀ x : ℝ) + (r₀ : ℝ) * t / ((N : ℝ) ^ 4 * (2 * s + 2)) := by
    unfold ksRad
    push_cast
    ring
  rw [hcast]
  refine ⟨by linarith, ?_⟩
  set e : ℝ := 1 / N with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 201 := by rw [he]; exact one_div_le_one_div_of_le (by norm_num) hN'
  have hr4 : (r₀ : ℝ) / (N : ℝ) ^ 4 = r₀ * e ^ 4 := by rw [he]; field_simp
  have h1 : (grid N r₀ x : ℝ) ≤ (1 + e) * ((1 + κ + 3 * e) * p) :=
    hg2.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  have h2 : (r₀ : ℝ) * e ^ 4 ≤ 15 * p * e ^ 4 := mul_le_mul_of_nonneg_right hr15 (by positivity)
  have h3 : (1 + e) * ((1 + κ + 3 * e) * p) + 15 * p * e ^ 4 ≤ (1 + κ + 6 * e) * p := by
    have : e * (1 + κ + 3 * e) + 15 * e ^ 4 ≤ 3 * e := by
      have : e ^ 4 ≤ e * (1 / 201) ^ 3 := by
        rw [show e ^ 4 = e * e ^ 3 by ring]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he0.le he1 3) he0.le
      nlinarith
    nlinarith
  linarith

variable (K : KSData)

/-! ### Monotonicity -/

theorem cc_zero_mono {del del' : List ℕ} {D D' : List DumQ} (h : K.cc 0 del D)
    (hD : K.OB D' ⊆ K.OB D) : K.cc 0 del' D' := by
  classical
  have hv := K.H.valid
  unfold cc GoodL wt at *
  simp only [↓reduceIte] at *
  refine lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg
    (biUnion_subset_biUnion_of_subset_left _ hD) fun c _ _ ↦ Instance.costOn_nonneg hv _ _) h

theorem GamSub.mono {K : KSData} {del : List ℕ} {D D' : List DumQ} (h : K.GamSub del D)
    (hD : K.OB D' ⊆ K.OB D) : K.GamSub del D' := by
  classical
  exact fun c hc ↦ h c (biUnion_subset_biUnion_of_subset_left _ hD hc)

theorem Base.del_append {K : KSData} {del : List ℕ} {D : List DumQ} (hb : K.Base del D) {i : ℕ}
    (hi : i < K.X.I.m) (hS : K.fac i ∈ K.X.S \ K.X.LSX K.w₁.OL) (hnd : i ∉ del) :
    K.Base (del ++ [i]) D where
  dums_nodup := hb.dums_nodup
  card := hb.card
  rad := hb.rad
  del_nodup := nodup_append_singleton.2 ⟨hnd, hb.del_nodup⟩
  del_sub := fun i' hi' ↦ by
    rcases List.mem_append.1 hi' with hi' | hi'
    · exact hb.del_sub i' hi'
    · rw [List.mem_singleton.1 hi']
      exact ⟨hi, hS⟩

theorem Base.dums_append {K : KSData} {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    {d : DumQ} {c : Fin K.X.I.m} (hp : K.pick (K.matched D) d.1 = some c) (hnd : d ∉ D)
    (hrad : K.X.I.dd (.inr c) (K.toDum d).leader ≤ (K.toDum d).radius ∧
      (K.toDum d).radius ≤ (1 + K.X.kap c + 6 * K.X.ε) * K.X.per c) :
    K.Base del (D ++ [d]) := by
  obtain ⟨-, hcM, -⟩ := K.pick_some hp
  obtain ⟨e1, e2⟩ := K.ghost_append_some hp
  refine ⟨nodup_append_singleton.2 ⟨hnd, hb.dums_nodup⟩, ?_, ?_, hb.del_nodup, hb.del_sub⟩
  · rw [e1, card_insert_of_notMem hcM, hb.card, List.length_append, List.length_singleton]
  · intro c' hc'
    rw [e1] at hc'
    rw [e2]
    rcases mem_insert.1 hc' with rfl | hc'
    · rw [Function.update_self]
      exact hrad
    · have hne : c' ≠ c := fun h ↦ hcM (h ▸ hc')
      rw [Function.update_of_ne hne]
      exact hb.rad c' hc'

/-! ### The steps, mode by mode -/

theorem step_tag0 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 0, l, r₀) u =
      if j = K.X.s then (if ph = 0 then (1, 0, del, D, 0, l, r₀) else (2, 0, del, D, 0, l, r₀))
      else if cbit K.X.b u then (ph, j + 1, del, D, 0, l, r₀)
      else (ph, j, del, D, 1, l, r₀) := by
  dsimp only [step, ksStep]
  rw [ite_eq_right hph]
  rfl

theorem step_tag1 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 1, l, r₀) u =
      if K.cand del = [] then (ph, j + 1, del, D, 0, l, r₀)
      else (ph, j, del, D, 2, K.sampled (ph, j, del, D, 1, l, r₀) u, r₀) := by
  dsimp only [step, ksStep]
  rw [ite_eq_right hph]
  rfl

theorem step_tag2 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 2, l, r₀) u =
      if del.length ≤ K.X.s ∧ cbit K.X.b u = true then (ph, j + 1, del ++ [l], D, 0, l, r₀)
      else (ph, j, del, D, 3, l, r₀) := by
  dsimp only [step, ksStep]
  rw [ite_eq_right hph]
  rfl

theorem step_tag3 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 3, l, r₀) u =
      if 2 * K.X.s < D.length + del.length then (ph, j + 1, del, D, 0, l, r₀)
      else if K.LS.filter (fun c ↦ decide (c ∉ del ∧ c ≠ l)) = [] then
        (ph, j + 1, del, D, 0, l, r₀)
      else if cbit K.X.b u then
        (ph, j, del, D, 4, l, (toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l))
      else (ph, j, del ++ [K.nearOther del l], D, 3, l, r₀) := by
  dsimp only [step, ksStep]
  rw [ite_eq_right hph]
  rfl

theorem step_tag4 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 4, l, r₀) u =
      if 2 * K.X.s < D.length + del.length then (ph, j + 1, del ++ [l], D, 0, l, r₀)
      else (ph, j, del, D ++ [(K.X.I.n + l,
        ksRad K.X.P.N K.X.s r₀ (cunif (Par.Gr K.X.P.N) u) D.length)], 5, l, r₀) := by
  dsimp only [step, ksStep]
  rw [ite_eq_right hph]
  rfl

theorem step_tag5 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 5, l, r₀) u =
      if cbit K.X.b u then (ph, j + 1, del ++ [l], D, 0, l, r₀)
      else (ph, j, del, D, 4, l, r₀) := by
  dsimp only [step, ksStep]
  rw [ite_eq_right hph]
  rfl

/-! ### Building the invariant -/

theorem Inv.mk_start {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j ≤ K.X.s)
    (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i) (hg : K.GamSub del D)
    (h1 : 1 ≤ ph → K.cc 0 del D) (hs : K.cc ph del D ∨ j ≤ del.length) :
    K.Inv (ph, j, del, D, 0, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj
  j_lt := fun h ↦ absurd rfl h
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun _ ↦ hg
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ _ ↦ hs
  prog := fun _ h ↦ absurd rfl h
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ h ↦ absurd h (by simp)
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ h ↦ absurd h (by simp)

theorem Inv.mk_phase2 {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i) (hg : K.GamSub del D)
    (h0 : K.cc 0 del D) (h1 : K.cc 1 del D) : K.Inv (2, 0, del, D, 0, l, r₀) where
  base := hb
  phase_le := le_rfl
  j_le := Nat.zero_le _
  j_lt := fun h ↦ absurd rfl h
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun _ ↦ hg
  ph1 := fun _ ↦ h0
  ph2 := fun _ ↦ ⟨h1, rfl⟩
  start := fun h ↦ absurd h (by simp)
  prog := fun h ↦ absurd h (by simp)
  sample := fun h ↦ absurd h (by simp)
  radd := fun h ↦ absurd h (by simp)
  mid := fun h ↦ absurd h (by simp)
  dg := fun h ↦ absurd h (by simp)
  rg := fun h ↦ absurd h (by simp)
  rad0 := fun h ↦ absurd h (by simp)

theorem Inv.mk_sample {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i) (hg : K.GamSub del D)
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hns : ¬ K.cc ph del D) :
    K.Inv (ph, j, del, D, 1, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun _ ↦ hg
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ _ ↦ hns
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ h ↦ absurd h (by simp)
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ h ↦ absurd h (by simp)

theorem Inv.mk_radd {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i) (hg : K.GamSub del D)
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hl : l ∈ K.LS) (hld : l ∉ del)
    (hgood : K.fac l ∈ K.GoodL ph del D) :
    K.Inv (ph, j, del, D, 2, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun _ ↦ hg
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ _ ↦ ⟨hl, hld, hgood⟩
  mid := fun _ h ↦ absurd h (by simp)
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ h ↦ absurd h (by simp)

theorem Inv.mk_dg {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i)
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hm : K.Mid del D l)
    (hdg : K.DGc del D l) :
    K.Inv (ph, j, del, D, 3, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun h ↦ absurd h (by simp)
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ _ ↦ hm
  dg := fun _ _ ↦ hdg
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ h ↦ absurd h (by simp)

theorem Inv.mk_rg {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, (∃ i ∈ del, d.1 = K.X.I.n + i) ∨ (d.1 = K.X.I.n + l ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < D.length, d.2 = ksRad K.X.P.N K.X.s r₀ x t))
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hm : K.Mid del D l)
    (hrg : K.RGc D l) (hr : K.Rad0 D l r₀) :
    K.Inv (ph, j, del, D, 4, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ (hlead d hd).imp id fun h ↦ ⟨by simp, h⟩
  gam := fun h ↦ absurd h (by simp)
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ _ ↦ hm
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ _ ↦ hrg
  rad0 := fun _ _ ↦ hr

theorem Inv.mk_rgb {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, (∃ i ∈ del, d.1 = K.X.I.n + i) ∨ (d.1 = K.X.I.n + l ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < D.length, d.2 = ksRad K.X.P.N K.X.s r₀ x t))
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hm : K.Mid del D l)
    (hr : K.Rad0 D l r₀) :
    K.Inv (ph, j, del, D, 5, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ (hlead d hd).imp id fun h ↦ ⟨by simp, h⟩
  gam := fun h ↦ absurd h (by simp)
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ _ ↦ hm
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ _ ↦ hr

/-! ### Geometry of satellites -/

theorem mem_Gam {c c' : Fin K.X.I.m} : c' ∈ K.X.Gam c ↔ c' ∈ K.X.S ∧
    K.X.dF c' c ≤ (1 + K.X.kap c + 2 * K.X.ε) * K.X.per c ∧
      ∃ j ∈ K.X.C c, K.X.dist j c' ≤ K.X.ε * K.X.per c := by
  unfold Ctx.Gam
  rw [mem_filter]

theorem mem_GamE {c c' : Fin K.X.I.m} : c' ∈ K.X.GamE c ↔ c' ∈ K.X.S ∧
    K.X.dF c' c ≤ (1 + K.X.kap c + 3 * K.X.ε) * K.X.per c ∧
      ∃ j ∈ K.X.C c, K.X.dist j c' ≤ 2 * K.X.ε * K.X.per c := by
  unfold Ctx.GamE
  rw [mem_filter]

theorem dF_comm (a b : Fin K.X.I.m) : K.X.dF a b = K.X.dF b a :=
  Instance.dd_comm K.H.valid _ _

theorem dF_tri (a b c : Fin K.X.I.m) : K.X.dF a c ≤ K.X.dF a b + K.X.dF b c :=
  Instance.dd_triangle K.H.valid _ _ _

theorem dist_tri (j : Fin K.X.I.n) (b c : Fin K.X.I.m) :
    K.X.dist j c ≤ K.X.dist j b + K.X.dF b c :=
  Instance.dd_triangle K.H.valid _ _ _

theorem eps_le_one : K.X.ε ≤ 1 := by have := K.H.eps_lt; linarith

theorem per_nonneg' (c : Fin K.X.I.m) : 0 ≤ K.X.per c := per_nonneg K.H.valid _ _ _

/-- A center within `ε² per₀` of a satellite of `c₀` is a loose satellite of `c₀`. -/
theorem GamE_of_near {c₀ ℓ c' : Fin K.X.I.m} (hℓ : ℓ ∈ K.X.Gam c₀) (hc' : c' ∈ K.X.S)
    (hd : K.X.dF ℓ c' ≤ K.X.ε ^ 2 * K.X.per c₀) : c' ∈ K.X.GamE c₀ := by
  obtain ⟨-, h1, j, hj, h2⟩ := K.mem_Gam.1 hℓ
  have hp := K.per_nonneg' c₀
  have he := K.H.eps_pos
  have he1 := K.eps_le_one
  have hee : K.X.ε ^ 2 * K.X.per c₀ ≤ K.X.ε * K.X.per c₀ :=
    mul_le_mul_of_nonneg_right (by nlinarith) hp
  refine K.mem_GamE.2 ⟨hc', ?_, j, hj, ?_⟩
  · have := K.dF_tri c' ℓ c₀
    rw [K.dF_comm c' ℓ] at this
    nlinarith
  · have := K.dist_tri j ℓ c'
    nlinarith

/-- A center within `3 ε² per` of a satellite of `c` is a loose satellite of `c`. -/
theorem GamE_of_near' {c ℓ c' : Fin K.X.I.m} (hc' : c' ∈ K.X.Gam c) (hℓ : ℓ ∈ K.X.S)
    (hd : K.X.dF ℓ c' ≤ 3 * K.X.ε ^ 2 * K.X.per c) : ℓ ∈ K.X.GamE c := by
  obtain ⟨-, h1, j, hj, h2⟩ := K.mem_Gam.1 hc'
  have hp := K.per_nonneg' c
  have he := K.H.eps_pos
  have he1 := K.H.eps_lt
  have hee : 3 * K.X.ε ^ 2 * K.X.per c ≤ K.X.ε * K.X.per c :=
    mul_le_mul_of_nonneg_right (by nlinarith) hp
  refine K.mem_GamE.2 ⟨hℓ, ?_, j, hj, ?_⟩
  · have := K.dF_tri ℓ c' c
    nlinarith
  · have := K.dist_tri j c' ℓ
    rw [K.dF_comm c' ℓ] at this
    nlinarith

theorem isFar_of_OB {D : List DumQ} {c : Fin K.X.I.m} (hc : c ∈ K.OB D) : K.X.IsFar c :=
  K.w₁.isFar K.H (mem_sdiff.1 (K.mem_OB.1 hc).1).1

theorem kap_le (c : Fin K.X.I.m) : K.X.kap c ≤ 23 / 65 := (kappa_mem _).2

theorem kap_ge (c : Fin K.X.I.m) : 12 / 65 ≤ K.X.kap c := (kappa_mem _).1

/-- **A kept satellite at the right distance** (from `BCFGJPSSV26.Stable.Hyp.no_dense_cores`). -/
theorem exists_far_sat {c₀ ℓ : Fin K.X.I.m} (hc₀ : K.X.IsFar c₀) (hℓ : ℓ ∈ K.X.Gam c₀) :
    ∃ w ∈ K.X.Gam c₀, K.X.ε * K.X.per c₀ / 2 ≤ K.X.dF ℓ w ∧ K.X.dF ℓ w < 5 * K.X.per c₀ := by
  obtain ⟨c₁, h₁, c₂, h₂, h12⟩ := K.H.no_dense_cores hc₀
  have hp := hc₀.per_pos
  have he := K.H.eps_pos
  have he1 := K.H.eps_lt
  have hk := K.kap_le c₀
  have hup : ∀ w ∈ K.X.Gam c₀, K.X.dF ℓ w < 5 * K.X.per c₀ := by
    intro w hw
    have a1 := (K.mem_Gam.1 hℓ).2.1
    have a2 := (K.mem_Gam.1 hw).2.1
    have := K.dF_tri ℓ c₀ w
    rw [K.dF_comm c₀ w] at this
    nlinarith
  have htri := K.dF_tri c₁ ℓ c₂
  rw [K.dF_comm c₁ ℓ] at htri
  by_cases h : K.X.ε * K.X.per c₀ / 2 ≤ K.X.dF ℓ c₁
  · exact ⟨c₁, h₁, h, hup c₁ h₁⟩
  · exact ⟨c₂, h₂, by linarith, hup c₂ h₂⟩

/-! ### The good chunks, mode by mode -/

theorem good_tag0 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 0, l, r₀) u ↔
      (j = K.X.s ∨ (cbit K.X.b u = true ↔ K.cc ph del D)) := by
  rw [Good, KSState.phase_mk, ite_eq_right hph]
  rfl

theorem good_tag1 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 1, l, r₀) u ↔
      K.fac (K.sampled (ph, j, del, D, 1, l, r₀) u) ∈ K.GoodL ph del D := by
  rw [Good, KSState.phase_mk, ite_eq_right hph]
  rfl

theorem good_tag2 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 2, l, r₀) u ↔
      (cbit K.X.b u = true ↔ K.fac l ∉ K.X.GamOf (K.OB D)) := by
  rw [Good, KSState.phase_mk, ite_eq_right hph]
  rfl

theorem good_tag3 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 3, l, r₀) u ↔
      (cbit K.X.b u = true ↔ ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c ∧
        K.X.ε ^ 2 * K.X.per c ≤ ((toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l) : ℝ)) := by
  rw [Good, KSState.phase_mk, ite_eq_right hph]
  rfl

theorem good_tag4 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 4, l, r₀) u ↔
      ∀ c, K.pick (K.matched D) (K.X.I.n + l) = some c →
        K.X.dF c (K.fac l) ≤ (grid K.X.P.N r₀ (cunif (Par.Gr K.X.P.N) u) : ℝ) ∧
          (grid K.X.P.N r₀ (cunif (Par.Gr K.X.P.N) u) : ℝ) ≤ (1 + K.X.ε) * K.X.dF c (K.fac l) := by
  rw [Good, KSState.phase_mk, ite_eq_right hph]
  rfl

theorem good_tag5 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 5, l, r₀) u ↔
      (cbit K.X.b u = true ↔ ¬ ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c) := by
  rw [Good, KSState.phase_mk, ite_eq_right hph]
  rfl

/-! ### The steps -/

/-- `START`: skip exactly when the cost condition holds; at the end of a phase, the condition
holds (if all of `S \ LS_X` is deleted, there is nothing left to pay). -/
theorem inv_tag0 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 0, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 0, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 0, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hg : K.GamSub del D := hI.gam (by simp)
  have hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
  have hs : K.cc ph del D ∨ j ≤ del.length := hI.start hph2 rfl
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j ≤ K.X.s := hI.j_le
  rw [K.good_tag0 hph] at hG
  rw [K.step_tag0 hph]
  by_cases hjs : j = K.X.s
  · rw [ite_eq_left hjs]
    have hcc : K.cc ph del D :=
      hs.elim id fun h ↦ K.cc_of_empty (hb.GoodL_eq_empty hg (by omega))
    by_cases h0 : ph = 0
    · rw [ite_eq_left h0]
      subst h0
      exact Inv.mk_start K hb (by norm_num) (Nat.zero_le _) hlead hg (fun _ ↦ hcc)
        (.inr (Nat.zero_le _))
    · rw [ite_eq_right h0]
      obtain rfl : ph = 1 := by omega
      exact Inv.mk_phase2 K hb hlead hg (h1 le_rfl) hcc
  · rw [ite_eq_right hjs]
    have hG' := hG.resolve_left hjs
    by_cases hc : cbit K.X.b u = true
    · rw [ite_eq_left hc]
      exact Inv.mk_start K hb hph2 (by omega) hlead hg h1 (.inl (hG'.1 hc))
    · rw [ite_eq_right hc]
      have hns : ¬ K.cc ph del D := fun h ↦ hc (hG'.2 h)
      exact Inv.mk_sample K hb hph2 (by omega) hlead hg h1 (hs.resolve_left hns) hns

/-- `SAMPLE`: a good center is sampled. -/
theorem inv_tag1 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 1, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 1, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 1, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hg : K.GamSub del D := hI.gam (by simp)
  have hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  have hns : ¬ K.cc ph del D := hI.sample hph2 rfl
  rw [K.good_tag1 hph] at hG
  rw [K.step_tag1 hph]
  by_cases hc : K.cand del = []
  · exfalso
    have he : K.LSp del = ∅ := by
      ext c
      rw [LSp, hc]
      simp [Instance.centers]
    exact hns (K.cc_of_empty (subset_empty.1 (he ▸ K.GoodL_subset hg)))
  · rw [ite_eq_right hc]
    have hmem := getD_wsample_mem (toRaw K.X.I) K.LS K.Λ₁ ph del D hc K.X.b u
    have hmem' := List.mem_filter.1 hmem
    exact Inv.mk_radd K hb hph2 hj hlead hg h1 hp hmem'.1 (of_decide_eq_true hmem'.2) hG

/-- `RADD`: delete the sampled center exactly when it is not a satellite of `O_B`; else it is a
satellite of some `c₀ ∈ O_B`, which has another kept satellite at distance in
`[ε per₀/2, 5 per₀)` (`BCFGJPSSV26.Stable.Hyp.no_dense_cores`). -/
theorem inv_tag2 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 2, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 2, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 2, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hg : K.GamSub del D := hI.gam (by simp)
  have hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  obtain ⟨hlLS, hld, hgood⟩ := hI.radd hph2 rfl
  have hl : l < K.X.I.m := K.hm l hlLS
  rw [K.good_tag2 hph] at hG
  rw [K.step_tag2 hph]
  have hdel : del.length ≤ K.X.s := hb.card_del_le
  by_cases hc : cbit K.X.b u = true
  · rw [ite_eq_left ⟨hdel, hc⟩]
    have hnot : K.fac l ∉ K.X.GamOf (K.OB D) := hG.1 hc
    have hS : K.fac l ∈ K.X.S \ K.X.LSX K.w₁.OL := by
      unfold GoodL at hgood
      split_ifs at hgood with h0
      · exact absurd hgood hnot
      · rcases mem_union.1 hgood with h | h
        · exact absurd h hnot
        · exact mem_sdiff.2 ⟨K.LSp_subset del (mem_sdiff.1 h).1, (mem_sdiff.1 h).2⟩
    refine Inv.mk_start K (hb.del_append hl hS hld) hph2 (by omega) ?_ ?_
      (fun h ↦ K.cc_zero_mono (h1 h) subset_rfl) (.inr (by simp; omega))
    · intro d hd
      obtain ⟨i, hi, he⟩ := hlead d hd
      exact ⟨i, List.mem_append_left _ hi, he⟩
    · intro c hc' hcd
      rcases List.mem_append.1 hcd with h | h
      · exact hg c hc' h
      · apply hnot
        rw [← List.mem_singleton.1 h, K.fac_fin]
        exact hc'
  · have hc' : ¬(del.length ≤ K.X.s ∧ cbit K.X.b u = true) := fun h ↦ hc h.2
    rw [ite_eq_right hc']
    have hin : K.fac l ∈ K.X.GamOf (K.OB D) := by
      by_contra h
      exact hc (hG.2 h)
    obtain ⟨c₀, hc₀, hlc₀⟩ := mem_biUnion.1 hin
    obtain ⟨w, hw, hw1, hw2⟩ := K.exists_far_sat (K.isFar_of_OB hc₀) hlc₀
    refine Inv.mk_dg K hb hph2 hj hlead h1 hp ⟨hl, ?_, hld, ?_⟩
      ⟨c₀, hc₀, hlc₀, w, hw, hg w (mem_biUnion.2 ⟨c₀, hc₀, hw⟩), hw1, hw2⟩
    · exact mem_sdiff.2 ⟨K.X.Gam_subset_S c₀ hlc₀,
        K.not_mem_LSX_of_GamE (K.GamOf_OB_subset_GamE D hin)⟩
    · rintro c hc ⟨i, hi, hid⟩
      exact absurd hid (hg i (mem_biUnion.2 ⟨c, hc, hi⟩))

/-- `DG`: with `c'` the nearest other kept center, go to `RG` exactly when `ℓ` is a loose
satellite of some `c ∈ O_B` with `d(ℓ, c') ≥ ε² per`; then `r₀ = d(ℓ, c')` is comparable with the
percentiles (`BCFGJPSSV26.Stable.Hyp.comparable_per`). Else `d(ℓ, c') < ε² per₀`, so `c'` is a
loose satellite of `c₀`, outside `LS_X`, and every cluster losing the satellite `c'` can be led by
`ℓ` (`BCFGJPSSV26.Stable.Hyp.comparable_per` at `c'`). -/
theorem inv_tag3 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 3, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 3, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 3, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  have hm : K.Mid del D l := hI.mid hph2 (by simp)
  have hdg : K.DGc del D l := hI.dg hph2 rfl
  obtain ⟨c₀, hc₀, hlc₀, w, hw, hwd, hw1, hw2⟩ := hdg
  have hfar₀ := K.isFar_of_OB hc₀
  have hp₀ := hfar₀.per_pos
  have he := K.H.eps_pos
  have he1 := K.H.eps_lt
  have hwl : w.1 ≠ l := by
    intro h
    have hw' : w = K.fac l := by rw [← h, K.fac_fin]
    rw [hw', Ctx.dF, Instance.dd_self K.H.valid] at hw1
    nlinarith
  obtain ⟨hc'lt, hc'S, hc'd, hc'l, hfd, hle⟩ :=
    K.nearOther_spec hm.lt (K.X.Gam_subset_S c₀ hw) hwd hwl
  rw [K.good_tag3 hph] at hG
  rw [K.step_tag3 hph]
  have hA := hb.card_add_le
  rw [ite_eq_right (by omega)]
  have hne : K.LS.filter (fun c ↦ decide (c ∉ del ∧ c ≠ l)) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.2 ⟨K.mem_S.1 (K.X.Gam_subset_S c₀ hw),
      decide_eq_true ⟨hwd, hwl⟩⟩)
  rw [ite_eq_right hne]
  by_cases hc : cbit K.X.b u = true
  · rw [ite_eq_left hc]
    obtain ⟨c₁, hc₁, hlc₁, hr₁⟩ := hG.1 hc
    have hfar₁ := K.isFar_of_OB hc₁
    refine Inv.mk_rg K hb hph2 hj (fun d hd ↦ .inl (hlead d hd)) h1 hp hm ⟨c₁, hc₁, hlc₁⟩
      ⟨?_, ?_⟩
    · have : 0 < K.X.ε ^ 2 * K.X.per c₁ := by have := hfar₁.per_pos; positivity
      linarith
    · intro c hc hlc
      have hfar := K.isFar_of_OB hc
      have hA1 := (K.H.comparable_per hfar hfar₁ ⟨K.fac l, mem_inter.2 ⟨hlc, hlc₁⟩⟩).1
      have hB2 := (K.H.comparable_per hfar hfar₀
        ⟨K.fac l, mem_inter.2 ⟨hlc, K.X.Gam_subset_GamE K.H.valid c₀ hlc₀⟩⟩).2
      have hpc := hfar.per_pos
      constructor
      · have : K.X.ε ^ 2 * K.X.per c / 3 ≤ K.X.ε ^ 2 * K.X.per c₁ := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hA1 (by positivity)
        linarith
      · rw [hfd]
        linarith
  · rw [ite_eq_right hc]
    have hno : ¬∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c ∧
        K.X.ε ^ 2 * K.X.per c ≤ ((toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l) : ℝ) :=
      fun h ↦ hc (hG.2 h)
    have hlt : K.X.dF (K.fac l) (K.fac (K.nearOther del l)) < K.X.ε ^ 2 * K.X.per c₀ := by
      by_contra h
      push Not at h
      exact hno ⟨c₀, hc₀, K.X.Gam_subset_GamE K.H.valid c₀ hlc₀, by rw [hfd]; exact h⟩
    have hc'E : K.fac (K.nearOther del l) ∈ K.X.GamE c₀ := K.GamE_of_near hlc₀ hc'S hlt.le
    have hc'X : K.fac (K.nearOther del l) ∉ K.X.LSX K.w₁.OL :=
      K.not_mem_LSX_of_GamE (mem_biUnion.2 ⟨c₀, (K.mem_OB.1 hc₀).1, hc'E⟩)
    have hb' := hb.del_append hc'lt (mem_sdiff.2 ⟨hc'S, hc'X⟩) hc'd
    have hee : K.X.ε ^ 2 * K.X.per c₀ < K.X.ε * K.X.per c₀ / 2 := by
      have : K.X.ε ^ 2 < K.X.ε / 2 := by nlinarith
      nlinarith
    refine Inv.mk_dg K hb' hph2 hj ?_ (fun h ↦ K.cc_zero_mono (h1 h) subset_rfl)
      (by simp; omega) ⟨hm.lt, hm.mem, ?_, ?_⟩ ⟨c₀, hc₀, hlc₀, w, hw, ?_, hw1, hw2⟩
    · intro d hd
      obtain ⟨i, hi, he⟩ := hlead d hd
      exact ⟨i, List.mem_append_left _ hi, he⟩
    · rw [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hm.nmem, fun h ↦ hc'l h.symm⟩
    · rintro c hc ⟨i, hi, hid⟩
      rcases List.mem_append.1 hid with h | h
      · exact hm.lose c hc ⟨i, hi, h⟩
      · have hi' : i = K.fac (K.nearOther del l) := by
          rw [← List.mem_singleton.1 h, K.fac_fin]
        rw [hi'] at hi
        have hfar := K.isFar_of_OB hc
        have hB2 := (K.H.comparable_per hfar hfar₀
          ⟨_, mem_inter.2 ⟨K.X.Gam_subset_GamE K.H.valid c hi, hc'E⟩⟩).2
        refine K.GamE_of_near' hi (mem_sdiff.1 hm.mem).1 ?_
        have : K.X.ε ^ 2 * K.X.per c₀ ≤ K.X.ε ^ 2 * (3 * K.X.per c) :=
          mul_le_mul_of_nonneg_left hB2 (by positivity)
        linarith
    · rw [List.mem_append, List.mem_singleton, not_or]
      refine ⟨hwd, fun h ↦ ?_⟩
      have hw' : w = K.fac (K.nearOther del l) := by rw [← h, K.fac_fin]
      rw [hw'] at hw1
      linarith

/-- `RG`: the radius is a grid point in `[d, (1 + ε) d]`, `d = d(c*, ℓ)` for the least
unmatched `c*` led by `ℓ`, shifted by less than `ε⁴ r₀ ≤ 15 ε⁴ per`; the new dummy is matched to
`c*`, and differs from the previous ones of the same leader. -/
theorem inv_tag4 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 4, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 4, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 4, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  have hm : K.Mid del D l := hI.mid hph2 (by simp)
  have hr : K.Rad0 D l r₀ := hI.rad0 hph2 (by simp)
  have hleadI : ∀ d ∈ D, (∃ i ∈ del, d.1 = K.X.I.n + i) ∨ (4 ≤ 4 ∧ d.1 = K.X.I.n + l ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < D.length, d.2 = ksRad K.X.P.N K.X.s r₀ x t) := hI.leaders
  have hrg : K.RGc D l := hI.rg hph2 rfl
  obtain ⟨c₂, hc₂, hlc₂⟩ := hrg
  rw [K.good_tag4 hph] at hG
  rw [K.step_tag4 hph]
  have hA := hb.card_add_le
  rw [ite_eq_right (by omega)]
  have hcand₂ : K.Cand c₂ (K.X.I.n + l) := by
    have := K.cand_iff.2 hlc₂
    rwa [K.fac_val hm.lt] at this
  obtain ⟨c, hpick⟩ := K.pick_isSome (K.mem_OB.1 hc₂).1 (K.mem_OB.1 hc₂).2 hcand₂
  obtain ⟨hcO, hcM, hcand⟩ := K.pick_some hpick
  have hcOB : c ∈ K.OB D := K.mem_OB.2 ⟨hcO, hcM⟩
  have hlc : K.fac l ∈ K.X.GamE c := by
    rw [← K.fac_val hm.lt] at hcand
    exact K.cand_iff.1 hcand
  obtain ⟨hg1, hg2⟩ := hG c hpick
  have hr0 : 0 < r₀ := by exact_mod_cast hr.1
  have hDle : D.length ≤ 2 * K.X.s := by have := hb.card_dums_le; omega
  have hN1 : 1 ≤ K.X.P.N := by have := K.X.P.hN; omega
  set x := cunif (Par.Gr K.X.P.N) u with hx
  have hdD : (K.X.I.n + l, ksRad K.X.P.N K.X.s r₀ x D.length) ∉ D := by
    intro hd
    rcases hleadI _ hd with ⟨i, hi, he⟩ | ⟨-, -, x', -, t', ht', he⟩
    · have : l = i := by simp only at he; omega
      exact hm.nmem (this ▸ hi)
    · have := ksRad_inj hN1 hr0 hDle (by omega) he
      omega
  have heps : K.X.ε = 1 / (K.X.P.N : ℝ) := rfl
  have hd' : K.X.dF c (K.fac l) ≤ (1 + K.X.kap c + 3 * (1 / (K.X.P.N : ℝ))) * K.X.per c := by
    rw [K.dF_comm, ← heps]
    exact (K.mem_GamE.1 hlc).2.1
  have hbd := ksRad_bounds (s := K.X.s) (t := D.length) K.X.P.hN hr0.le hDle (K.per_nonneg' c)
    hg1 (by rw [← heps]; exact hg2) hd' (K.kap_le c) (hr.2 c hcOB hlc).2
  have hb' : K.Base del (D ++ [(K.X.I.n + l, ksRad K.X.P.N K.X.s r₀ x D.length)]) := by
    refine hb.dums_append hpick hdD ?_
    rw [K.toDum_leader (d := (K.X.I.n + l, _)) hm.lt rfl, K.toDum_radius, ← K.fac_eq hm.lt]
    exact ⟨hbd.1, by rw [heps]; exact hbd.2⟩
  refine Inv.mk_rgb K hb' hph2 hj ?_
    (fun h ↦ K.cc_zero_mono (h1 h) (K.OB_append_subset D _)) hp
    ⟨hm.lt, hm.mem, hm.nmem, fun c' hc' ↦ hm.lose c' (K.OB_append_subset D _ hc')⟩
    ⟨hr.1, fun c' hc' ↦ hr.2 c' (K.OB_append_subset D _ hc')⟩
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · rcases hleadI d hd with h | ⟨-, h1', x', hx', t', ht', he⟩
    · exact .inl h
    · exact .inr ⟨h1', x', hx', t', by simp; omega, he⟩
  · rw [List.mem_singleton.1 hd]
    refine .inr ⟨rfl, x, Nat.mod_lt _ (by unfold Par.Gr; omega), D.length, by simp, rfl⟩

/-- `RGB`: stop (and delete `ℓ`) exactly when `ℓ` leads no unmatched cluster any more; then every
cluster of `O_B` that lost a satellite in this iteration was matched. -/
theorem inv_tag5 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 5, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 5, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 5, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  have hm : K.Mid del D l := hI.mid hph2 (by simp)
  have hr : K.Rad0 D l r₀ := hI.rad0 hph2 (by simp)
  have hleadI : ∀ d ∈ D, (∃ i ∈ del, d.1 = K.X.I.n + i) ∨ (4 ≤ 5 ∧ d.1 = K.X.I.n + l ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < D.length, d.2 = ksRad K.X.P.N K.X.s r₀ x t) := hI.leaders
  rw [K.good_tag5 hph] at hG
  rw [K.step_tag5 hph]
  by_cases hc : cbit K.X.b u = true
  · rw [ite_eq_left hc]
    have hno := hG.1 hc
    have hb' := hb.del_append hm.lt hm.mem hm.nmem
    refine Inv.mk_start K hb' hph2 (by omega) ?_ ?_
      (fun h ↦ K.cc_zero_mono (h1 h) subset_rfl) (.inr (by simp; omega))
    · intro d hd
      rcases hleadI d hd with ⟨i, hi, he⟩ | ⟨-, he, -⟩
      · exact ⟨i, List.mem_append_left _ hi, he⟩
      · exact ⟨l, List.mem_append_right _ (List.mem_singleton_self l), he⟩
    · intro c hc' hcd
      obtain ⟨c₁, hc₁, hcc₁⟩ := mem_biUnion.1 hc'
      rcases List.mem_append.1 hcd with h | h
      · exact hno ⟨c₁, hc₁, hm.lose c₁ hc₁ ⟨c, hcc₁, h⟩⟩
      · have : c = K.fac l := by rw [← List.mem_singleton.1 h, K.fac_fin]
        rw [this] at hcc₁
        exact hno ⟨c₁, hc₁, K.X.Gam_subset_GamE K.H.valid c₁ hcc₁⟩
  · rw [ite_eq_right hc]
    have hex : ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c := by
      by_contra h
      exact hc (hG.2 h)
    exact Inv.mk_rg K hb hph2 hj (fun d hd ↦ (hleadI d hd).imp id fun h ↦ h.2) h1 hp hm hex hr

/-- **One step**: every good chunk keeps the invariant. -/
theorem inv_step {st : KSState} {u : ℕ} (hI : K.Inv st) (hG : K.Good st u) :
    K.Inv (K.step st u) := by
  obtain ⟨ph, j, del, D, tag, l, r₀⟩ := st
  by_cases hph : ph = 2
  · rw [show K.step (ph, j, del, D, tag, l, r₀) u = (ph, j, del, D, tag, l, r₀) from
      KSSteps.step_phase_two _ _ _ _ _ _ _ u hph]
    exact hI
  · have ht : tag ≤ 5 := hI.tag_le
    interval_cases tag
    · exact K.inv_tag0 hI hph hG
    · exact K.inv_tag1 hI hph hG
    · exact K.inv_tag2 hI hph hG
    · exact K.inv_tag3 hI hph hG
    · exact K.inv_tag4 hI hph hG
    · exact K.inv_tag5 hI hph hG

end KSData

end BCFGJPSSV26.Stable
