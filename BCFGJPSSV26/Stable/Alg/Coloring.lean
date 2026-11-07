module

public import BCFGJPSSV26.Stable.Alg.Coins
public import BCFGJPSSV26.Stable.Structure.Partition

/-!
# Color coding

The last `k` chunks of a trial color the kept centers `LS'` (a list), one fair bit per position:
red for `true` (`BCFGJPSSV26.Stable.colors`, `BCFGJPSSV26.Stable.redOf`,
`BCFGJPSSV26.Stable.blueOf`).

[BCFGJPSSV26b, Section 3.3] (`BCFGJPSSV26.Stable.Partition.card_colorEvent`): the
color event of a partition (the centers of `Z*` red, their nearest centers in `LS' \ Z*` blue)
constrains at most `2 z ≤ 2 s` positions, each satisfied by exactly half the chunks, so it holds
for at least `4^(-s) K^k` chunk vectors.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- One color bit for each position of `LS'`. -/
def colors (b : ℕ) (LS' : List ℕ) (ch : ℕ → ℕ) : List Bool :=
  (List.range LS'.length).map fun i ↦ cbit b (ch i)

/-- The red centers. -/
def redOf (LS' : List ℕ) (col : List Bool) : List ℕ :=
  (LS'.zip col).filterMap fun p ↦ if p.2 then some p.1 else none

/-- The blue centers. -/
def blueOf (LS' : List ℕ) (col : List Bool) : List ℕ :=
  (LS'.zip col).filterMap fun p ↦ if p.2 then none else some p.1

/-- Membership in a zip of two lists of the same length, by positions. -/
theorem mem_zip_iff_getElem {LS' : List ℕ} {col : List Bool} (hcol : col.length = LS'.length)
    {i : ℕ} {x : Bool} :
    (i, x) ∈ LS'.zip col ↔ ∃ p, ∃ h : p < LS'.length, LS'[p] = i ∧ col[p] = x := by
  rw [List.mem_iff_getElem]
  simp only [List.length_zip, List.getElem_zip, Prod.mk.injEq]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, by omega, h1, h2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, by omega, h1, h2⟩

theorem mem_redOf {LS' : List ℕ} {col : List Bool} {i : ℕ} :
    i ∈ redOf LS' col ↔ (i, true) ∈ LS'.zip col := by
  simp only [redOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, c⟩, ha, h⟩
    cases c
    · simp at h
    · simp only [ite_true, Option.some.injEq] at h
      exact h ▸ ha
  · intro h
    exact ⟨(i, true), h, by simp⟩

theorem mem_blueOf {LS' : List ℕ} {col : List Bool} {i : ℕ} :
    i ∈ blueOf LS' col ↔ (i, false) ∈ LS'.zip col := by
  simp only [blueOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, c⟩, ha, h⟩
    cases c
    · simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at h
      exact h ▸ ha
    · simp at h
  · intro h
    exact ⟨(i, false), h, by simp⟩

/-- Red and blue split a list of distinct centers. -/
theorem centers_red_blue {I : Instance} {LS' : List ℕ} (hnd : LS'.Nodup) {col : List Bool}
    (hcol : col.length = LS'.length) :
    I.centers (redOf LS' col) ⊆ I.centers LS' ∧
      I.centers (blueOf LS' col) = I.centers LS' \ I.centers (redOf LS' col) := by
  have huniq : ∀ i x y, (i, x) ∈ LS'.zip col → (i, y) ∈ LS'.zip col → x = y := by
    intro i x y hx hy
    obtain ⟨p, hp, h1, h2⟩ := (mem_zip_iff_getElem hcol).1 hx
    obtain ⟨p', hp', h1', h2'⟩ := (mem_zip_iff_getElem hcol).1 hy
    have : p = p' := hnd.getElem_inj_iff.1 (h1.trans h1'.symm)
    subst this
    rw [← h2, ← h2']
  have hex : ∀ i ∈ LS', ∃ x, (i, x) ∈ LS'.zip col := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hi
    exact ⟨col[p], (mem_zip_iff_getElem hcol).2 ⟨p, hp, rfl, rfl⟩⟩
  refine ⟨Instance.centers_mono fun i hi ↦ (List.of_mem_zip (mem_redOf.1 hi)).1, ?_⟩
  ext c
  rw [mem_sdiff, Instance.mem_centers, Instance.mem_centers, Instance.mem_centers, mem_blueOf,
    mem_redOf]
  constructor
  · intro h
    exact ⟨(List.of_mem_zip h).1, fun h' ↦ absurd (huniq _ _ _ h h') (by decide)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx⟩ := hex _ h1
    cases x
    · exact hx
    · exact absurd hx h2

theorem length_colors (b : ℕ) (LS' : List ℕ) (ch : ℕ → ℕ) :
    (colors b LS' ch).length = LS'.length := by
  simp [colors]

/-- A position colored red gives a red center. -/
theorem mem_redOf_colors {b : ℕ} {LS' : List ℕ} {ch : ℕ → ℕ} {p : ℕ} (hp : p < LS'.length)
    (h : cbit b (ch p) = true) : LS'[p] ∈ redOf LS' (colors b LS' ch) := by
  rw [mem_redOf, mem_zip_iff_getElem (length_colors b LS' ch)]
  exact ⟨p, hp, rfl, by simp [colors, h]⟩

/-- A position colored blue gives a blue center. -/
theorem mem_blueOf_colors {b : ℕ} {LS' : List ℕ} {ch : ℕ → ℕ} {p : ℕ} (hp : p < LS'.length)
    (h : cbit b (ch p) = false) : LS'[p] ∈ blueOf LS' (colors b LS' ch) := by
  rw [mem_blueOf, mem_zip_iff_getElem (length_colors b LS' ch)]
  exact ⟨p, hp, rfl, by simp [colors, h]⟩

theorem toCh_of_lt {M K : ℕ} (u : Fin M → Fin K) {p : ℕ} (hp : p < M) : toCh u p = u ⟨p, hp⟩ := by
  simp [toCh, hp]

open Classical in
/-- **The color event is likely.** -/
theorem Partition.card_colorEvent {X : Ctx} (H : Hyp X) {Λ₁ : List (Dummy X.I)}
    {w₁ : ClientWitness X Λ₁} {LS' : List ℕ} {Λ₂ : List (Dummy X.I)}
    {w₂ : ClusterWitness w₁ (X.I.centers LS') Λ₂} (Q : Partition w₂) (hnd : LS'.Nodup)
    (hm : ∀ i ∈ LS', i < X.I.m) (hk : LS'.length ≤ X.I.k) :
    (1 / 4 : ℝ) ^ X.s * ((2 : ℝ) ^ X.b) ^ X.I.k ≤
      (univ.filter fun u : Fin X.I.k → Fin (2 ^ X.b) ↦
        Q.ColorEvent (X.I.centers (redOf LS' (colors X.b LS' (toCh u))))
          (X.I.centers (blueOf LS' (colors X.b LS' (toCh u))))).card := by
  have hb : 1 ≤ X.b := by
    have := X.P.N_pos
    simp only [Ctx.b, Par.bits]
    omega
  have hZL : Q.Zstar ⊆ X.I.centers LS' := Q.Zstar_sub.trans sdiff_subset
  have hpos : ∀ c ∈ X.I.centers LS', ∃ p, ∃ hp : p < LS'.length, LS'[p] = c.1 :=
    fun c hc ↦ List.getElem_of_mem (Instance.mem_centers.1 hc)
  -- the centers to be blue
  let B : Finset (Fin X.I.m) := if h : (X.I.centers LS' \ Q.Zstar).Nonempty then
    Q.Zstar.image fun c ↦ X.I.near (X.I.centers LS' \ Q.Zstar) h (.inr c) else ∅
  have hBL : B ⊆ X.I.centers LS' \ Q.Zstar := by
    intro d hd
    simp only [B] at hd
    split_ifs at hd with h
    · obtain ⟨c, -, rfl⟩ := mem_image.1 hd
      exact Instance.near_mem h _
    · simp at hd
  have hBcard : B.card ≤ Q.Zstar.card := by
    simp only [B]
    split_ifs
    · exact card_image_le
    · simp
  -- the allowed chunks at each position
  let T : Finset (Fin (2 ^ X.b)) := univ.filter fun v ↦ cbit X.b v = true
  let F : Finset (Fin (2 ^ X.b)) := univ.filter fun v ↦ cbit X.b v = false
  let A : Fin X.I.k → Finset (Fin (2 ^ X.b)) := fun e ↦
    if ∃ c ∈ Q.Zstar, LS'[e.1]? = some c.1 then T
    else if ∃ c ∈ B, LS'[e.1]? = some c.1 then F else univ
  have hsub : Fintype.piFinset A ⊆ univ.filter fun u : Fin X.I.k → Fin (2 ^ X.b) ↦
      Q.ColorEvent (X.I.centers (redOf LS' (colors X.b LS' (toCh u))))
        (X.I.centers (blueOf LS' (colors X.b LS' (toCh u)))) := by
    intro u hu
    rw [Fintype.mem_piFinset] at hu
    rw [mem_filter]
    refine ⟨mem_univ _, fun c hc ↦ ?_, fun c hc h ↦ ?_⟩
    · obtain ⟨p, hp, hpc⟩ := hpos c (hZL hc)
      have hpk : p < X.I.k := by omega
      have hA : A ⟨p, hpk⟩ = T := by
        refine ite_eq_left_iff.2 fun hn ↦ absurd ⟨c, hc, ?_⟩ hn
        exact (List.getElem?_eq_getElem hp).trans (congrArg some hpc)
      have hbit := hu ⟨p, hpk⟩
      rw [hA] at hbit
      rw [Instance.mem_centers, ← hpc]
      refine mem_redOf_colors hp ?_
      rw [toCh_of_lt u hpk]
      exact (mem_filter.1 hbit).2
    · have hdB : X.I.near (X.I.centers LS' \ Q.Zstar) h (.inr c) ∈ B := by
        simp only [B, h, ↓reduceDIte]
        exact mem_image_of_mem _ hc
      have hdL := mem_sdiff.1 (hBL hdB)
      obtain ⟨p, hp, hpd⟩ := hpos _ hdL.1
      have hpk : p < X.I.k := by omega
      have hnZ : ¬ ∃ c ∈ Q.Zstar, LS'[p]? = some c.1 := by
        rintro ⟨c', hc', h'⟩
        rw [List.getElem?_eq_getElem hp, Option.some.injEq, hpd] at h'
        exact hdL.2 (Fin.ext h' ▸ hc')
      have hA : A ⟨p, hpk⟩ = F := by
        simp only [A]
        rw [ite_eq_right hnZ]
        refine ite_eq_left_iff.2 fun hn ↦ absurd ⟨_, hdB, ?_⟩ hn
        exact (List.getElem?_eq_getElem hp).trans (congrArg some hpd)
      have hbit := hu ⟨p, hpk⟩
      rw [hA] at hbit
      rw [Instance.mem_centers, ← hpd]
      refine mem_blueOf_colors hp ?_
      rw [toCh_of_lt u hpk]
      exact (mem_filter.1 hbit).2
  -- the number of constrained positions
  let cnt : Fin X.I.k → ℕ := fun e ↦
    if ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1 then 1 else 0
  have hK : (2 : ℝ) ^ X.b = 2 * 2 ^ (X.b - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcT : (T.card : ℝ) = 2 ^ (X.b - 1) := by exact_mod_cast card_cbit hb true
  have hcF : (F.card : ℝ) = 2 ^ (X.b - 1) := by exact_mod_cast card_cbit hb false
  have hA : ∀ e, (2 : ℝ) ^ X.b * (1 / 2) ^ cnt e ≤ (A e).card := by
    intro e
    simp only [A, cnt]
    by_cases h1 : ∃ c ∈ Q.Zstar, LS'[e.1]? = some c.1
    · have h1' : ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1 :=
        let ⟨c, hc, h⟩ := h1
        ⟨c, mem_union_left _ hc, h⟩
      rw [ite_eq_left h1, ite_eq_left h1', hcT, hK, pow_one]
      linarith
    · by_cases h2 : ∃ c ∈ B, LS'[e.1]? = some c.1
      · have h2' : ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1 :=
          let ⟨c, hc, h⟩ := h2
          ⟨c, mem_union_right _ hc, h⟩
        rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left h2', hcF, hK, pow_one]
        linarith
      · have h3 : ¬ ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1 := by
          rintro ⟨c, hc, h⟩
          rcases mem_union.1 hc with hc | hc
          · exact h1 ⟨c, hc, h⟩
          · exact h2 ⟨c, hc, h⟩
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, pow_zero, mul_one, card_univ,
          Fintype.card_fin]
        push_cast
        rfl
  have hC : ∑ e, cnt e =
      (univ.filter fun e : Fin X.I.k ↦ ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1).card := by
    simp only [cnt]
    rw [sum_boole, Nat.cast_id]
  have hZs : Q.Zstar.card ≤ X.s := by
    have h1 := Q.Zstar_card
    have h2 := Q.card_OLam_add_OP_le H
    have h3 := Instance.card_centers hnd hm
    rw [List.length_append] at h2
    omega
  have hCle : (univ.filter fun e : Fin X.I.k ↦
      ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1).card ≤ 2 * X.s := by
    have h1 : (univ.filter fun e : Fin X.I.k ↦ ∃ c ∈ Q.Zstar ∪ B, LS'[e.1]? = some c.1).card ≤
        ((Q.Zstar ∪ B).map Fin.valEmbedding).card := by
      refine card_le_card_of_injOn (fun e ↦ (LS'[e.1]?).getD 0) (fun e he ↦ ?_)
        (fun e he e' he' h ↦ ?_)
      · obtain ⟨c, hc, h⟩ := (mem_filter.1 he).2
        simp only [h, Option.getD_some]
        exact mem_map_of_mem _ hc
      · obtain ⟨c, -, hc⟩ := (mem_filter.1 he).2
        obtain ⟨c', -, hc'⟩ := (mem_filter.1 he').2
        simp only [hc, hc', Option.getD_some] at h
        rw [h] at hc
        obtain ⟨h1, h1'⟩ := List.getElem?_eq_some_iff.1 hc
        obtain ⟨h2, h2'⟩ := List.getElem?_eq_some_iff.1 hc'
        exact Fin.ext (hnd.getElem_inj_iff.1 (h1'.trans h2'.symm))
    rw [card_map] at h1
    have h2 := card_union_le Q.Zstar B
    omega
  have hfinal : (1 / 4 : ℝ) ^ X.s * ((2 : ℝ) ^ X.b) ^ X.I.k ≤ ∏ e, ((A e).card : ℝ) := by
    calc (1 / 4 : ℝ) ^ X.s * ((2 : ℝ) ^ X.b) ^ X.I.k ≤
          ((2 : ℝ) ^ X.b) ^ X.I.k * (1 / 2) ^ (∑ e, cnt e) := by
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hC]
          calc (1 / 4 : ℝ) ^ X.s = (1 / 2) ^ (2 * X.s) := by
                rw [pow_mul]
                norm_num
            _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hCle
      _ = ∏ e, (2 : ℝ) ^ X.b * (1 / 2) ^ (cnt e) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow_eq_pow_sum]
      _ ≤ _ := prod_le_prod₀ (fun e _ ↦ by positivity) (fun e _ ↦ hA e)
  calc _ ≤ ∏ e, ((A e).card : ℝ) := hfinal
    _ = (Fintype.piFinset A).card := by
        rw [Fintype.card_piFinset]
        push_cast
        rfl
    _ ≤ _ := by exact_mod_cast card_le_card hsub

end BCFGJPSSV26.Stable
