module

public import BGHKLMM26.Model
public import Complexity.Computability.Complexity.Classes.Promise.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Enlarging the alphabet of a Unique Games instance

The reduction needs many labels, but `UniqueGames.UGC` gives NP-hardness for one number `R` of
labels. Replacing each constraint `π` on `[R]` by `π × id` on `[R] × [k]` (label `(a, j)` numbered
`a + R j`) keeps the value: a labeling of the new instance read modulo `R` satisfies at least as
many constraints, and a labeling of the old one is one of the new. So the hardness carries over to
`kR` labels (`BGHKLMM26.Hard.enlarge_reduces`). For `R = 0` there are no yes-instances, and every
instance maps to a fixed no-instance (`BGHKLMM26.Hard.exists_npHard_ge`).

The new table is built from the length of the old one rather than from `R`, so that the map runs in
polynomial time on every input (`R` is written in binary).
-/

@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Cslib.Complexity Turing.MultiTapeTM

/-- The table of `π × id` on `[r] × [k]`, for a table `π` of length `r`: label `l = a + r j`
goes to `π(a) + r j`. -/
def enlargeTable (k : ℕ) (π : List ℕ) : List ℕ :=
  (List.range (π.length * k)).map fun l ↦ π.getD (l % π.length) 0 + π.length * (l / π.length)

/-- The instance with every constraint `π` replaced by `π × id` on `[R] × [k]`, and `R k` labels. -/
def enlarge (k : ℕ) (G : UGInstance) : UGInstance :=
  (G.1, G.2.1, G.2.2.1 * k, G.2.2.2.map fun c ↦ (c.1, enlargeTable k c.2))

namespace Enlarge

open ComputableInPolyTime

/-! ### Polynomial time -/

/-- The enlarged table is computed in polynomial time, from the length of `π` in unary. -/
theorem enlargeTable_polytime (k : ℕ) :
    ComputableInPolyTime (enlargeTable k) (encList encNat) (encList encNat) := by
  unfold enlargeTable
  have hl : ComputableInPolyTime (fun π : List ℕ ↦ List.range (π.length * k))
      (encList encNat) (encList encUnary) := by fun_prop
  have hlen : ComputableInPolyTime (fun p : List ℕ × ℕ ↦ p.1.length)
      (encPair (encList encNat) encUnary) encUnary := by fun_prop
  have hmod : ComputableInPolyTime (fun p : List ℕ × ℕ ↦ p.2 % p.1.length)
      (encPair (encList encNat) encUnary) encUnary :=
    unary_mod.comp ((snd _ _).prod hlen)
  have hdiv : ComputableInPolyTime (fun p : List ℕ × ℕ ↦ p.1.length * (p.2 / p.1.length))
      (encPair (encList encNat) encUnary) encUnary :=
    unary_mul' hlen (unary_div.comp ((snd _ _).prod hlen))
  have hget : ComputableInPolyTime (fun p : List ℕ × ℕ ↦ p.1.getD (p.2 % p.1.length) 0)
      (encPair (encList encNat) encUnary) encNat :=
    listGetDWithInput (fst _ _) hmod 0
  have hb : ComputableInPolyTime (fun p : List ℕ × ℕ ↦
      p.1.getD (p.2 % p.1.length) 0 + p.1.length * (p.2 / p.1.length))
      (encPair (encList encNat) encUnary) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_add' hget.tidy
      (ComputableTidilyInPolyTime.unary_to_binary.comp hdiv.tidy))
  exact mapWithInput (f := fun (π : List ℕ) (l : ℕ) ↦
    π.getD (l % π.length) 0 + π.length * (l / π.length)) hl hb

end Enlarge

open Enlarge ComputableInPolyTime in
/-- The enlargement runs in polynomial time, for a fixed `k`. -/
theorem enlarge_polytime (k : ℕ) : ComputableInPolyTime (enlarge k) encUG encUG := by
  unfold enlarge encUG
  have ht := enlargeTable_polytime k
  have hc : ComputableInPolyTime (fun c : UGConstraint ↦ (c.1, enlargeTable k c.2))
      (encPair (encPair encNat encNat) (encList encNat))
      (encPair (encPair encNat encNat) (encList encNat)) :=
    (fst _ _).prod (ht.comp (snd _ _))
  have hR : ComputableInPolyTime (fun G : UGInstance ↦ G.2.2.1 * k)
      (encPair encNat (encPair encNat (encPair encNat
        (encList (encPair (encPair encNat encNat) (encList encNat)))))) encNat :=
    binary_mul' (by fun_prop) (const k)
  have hL : ComputableInPolyTime (fun G : UGInstance ↦
      G.2.2.2.map fun c ↦ (c.1, enlargeTable k c.2))
      (encPair encNat (encPair encNat (encPair encNat
        (encList (encPair (encPair encNat encNat) (encList encNat))))))
      (encList (encPair (encPair encNat encNat) (encList encNat))) :=
    mapWithInput (f := fun _ (c : UGConstraint) ↦ (c.1, enlargeTable k c.2)) (by fun_prop)
      (hc.comp (snd _ _))
  exact (fst _ _).prod ((fst _ _).comp (snd _ _) |>.prod (hR.prod hL))

namespace Enlarge

/-! ### The value -/

/-- The labeling of `ℕ` read off a labeling of `Fin m` (`0` past `m`), as in `ugValue`. -/
def lab {m R : ℕ} (σ : Fin m → Fin R) (u : ℕ) : ℕ := if h : u < m then σ ⟨u, h⟩ else 0

theorem lab_lt {m R : ℕ} (σ : Fin m → Fin R) (hR : 0 < R) (u : ℕ) : lab σ u < R := by
  unfold lab; split_ifs
  · exact (σ _).isLt
  · exact hR

/-- The fraction of the constraints satisfied by `(σ, τ)`. -/
noncomputable def frac (G : UGInstance) (σ : Fin G.1 → Fin G.2.2.1)
    (τ : Fin G.2.1 → Fin G.2.2.1) : ℝ :=
  (ugSatisfied G (lab σ) (lab τ) : ℝ) / G.2.2.2.length

theorem ugValue_eq (G : UGInstance) : ugValue G = ⨆ (σ) (τ), frac G σ τ := rfl

theorem frac_nonneg (G : UGInstance) (σ τ) : 0 ≤ frac G σ τ :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ugValue_nonneg (G : UGInstance) : 0 ≤ ugValue G :=
  Real.iSup_nonneg fun σ ↦ Real.iSup_nonneg fun τ ↦ frac_nonneg G σ τ

theorem frac_le_ugValue (G : UGInstance) (σ τ) : frac G σ τ ≤ ugValue G := by
  rw [ugValue_eq]
  refine le_trans ?_ (le_ciSup (f := fun σ ↦ ⨆ τ, frac G σ τ) (Set.finite_range _).bddAbove σ)
  exact le_ciSup (f := frac G σ) (Set.finite_range _).bddAbove τ

theorem ugValue_le {G : UGInstance} {c : ℝ} (hc : 0 ≤ c) (h : ∀ σ τ, frac G σ τ ≤ c) :
    ugValue G ≤ c :=
  Real.iSup_le (fun σ ↦ Real.iSup_le (h σ) hc) hc

/-! ### The enlarged table -/

theorem length_enlargeTable (k : ℕ) (π : List ℕ) :
    (enlargeTable k π).length = π.length * k := by
  simp [enlargeTable]

theorem getD_enlargeTable (k : ℕ) (π : List ℕ) {l : ℕ} (hl : l < π.length * k) :
    (enlargeTable k π).getD l 0 = π.getD (l % π.length) 0 + π.length * (l / π.length) := by
  simp [enlargeTable, List.getD_eq_getElem?_getD, hl]

theorem getD_enlargeTable_of_lt {k : ℕ} (hk : 1 ≤ k) (π : List ℕ) {l : ℕ} (hl : l < π.length) :
    (enlargeTable k π).getD l 0 = π.getD l 0 := by
  rw [getD_enlargeTable k π (lt_of_lt_of_le hl (Nat.le_mul_of_pos_right _ hk)),
    Nat.mod_eq_of_lt hl, Nat.div_eq_of_lt hl, Nat.mul_zero, Nat.add_zero]

theorem getD_eq_getElem' (π : List ℕ) {i : ℕ} (hi : i < π.length) : π.getD i 0 = π[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem getD_lt {π : List ℕ} (hlt : ∀ a ∈ π, a < π.length) {i : ℕ} (hi : i < π.length) :
    π.getD i 0 < π.length := by
  rw [getD_eq_getElem' _ hi]; exact hlt _ (List.getElem_mem hi)

theorem mem_enlargeTable_lt {k : ℕ} {π : List ℕ} (hlt : ∀ a ∈ π, a < π.length) :
    ∀ a ∈ enlargeTable k π, a < π.length * k := by
  intro a ha
  simp only [enlargeTable, List.mem_map, List.mem_range] at ha
  obtain ⟨l, hl, rfl⟩ := ha
  have hr : 0 < π.length := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hl
  have h1 := getD_lt hlt (Nat.mod_lt l hr)
  have h2 : l / π.length < k := Nat.div_lt_of_lt_mul hl
  calc π.getD (l % π.length) 0 + π.length * (l / π.length)
      < π.length + π.length * (l / π.length) := by omega
    _ = π.length * (l / π.length + 1) := by ring
    _ ≤ π.length * k := Nat.mul_le_mul_left _ h2

theorem nodup_enlargeTable {k : ℕ} {π : List ℕ} (hπ : π.Nodup) (hlt : ∀ a ∈ π, a < π.length) :
    (enlargeTable k π).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro l hl l' hl' h
  simp only [List.mem_range] at hl hl'
  have hr : 0 < π.length := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hl
  have h1 := getD_lt hlt (Nat.mod_lt l hr)
  have h1' := getD_lt hlt (Nat.mod_lt l' hr)
  have hmod := congrArg (· % π.length) h
  have hdiv := congrArg (· / π.length) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h1'] at hmod
  simp only [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h1',
    Nat.zero_add] at hdiv
  rw [getD_eq_getElem' _ (Nat.mod_lt l hr), getD_eq_getElem' _ (Nat.mod_lt l' hr),
    hπ.getElem_inj_iff] at hmod
  rw [← Nat.mod_add_div l π.length, ← Nat.mod_add_div l' π.length, hmod, hdiv]


/-! ### The enlarged instance -/

/-- The promise of `ugGap R`: valid, simple, bi-regular, with `R` labels. -/
def Promised (R : ℕ) (G : UGInstance) : Prop :=
  UGValid G ∧ G.2.2.1 = R ∧ UGSimple G ∧ BiRegular G

/-- The enlarged instance is valid, simple and bi-regular, with `R k` labels. -/
theorem enlarge_good {R k : ℕ} {G : UGInstance} (hG : Promised R G) :
    Promised (R * k) (enlarge k G) := by
  obtain ⟨hV, hR, hS, hB⟩ := hG
  refine ⟨?_, by simp [enlarge, hR], ?_, ?_⟩
  · intro c hc
    simp only [enlarge, List.mem_map] at hc
    obtain ⟨c, hc, rfl⟩ := hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hV c hc
    have hlt : ∀ a ∈ c.2, a < c.2.length := fun a ha ↦ h3 ▸ h5 a ha
    refine ⟨h1, h2, ?_, nodup_enlargeTable h4 hlt, ?_⟩
    · simp [enlarge, length_enlargeTable, h3]
    · intro a ha
      have := mem_enlargeTable_lt hlt a ha
      simpa [enlarge, h3] using this
  · simpa [UGSimple, enlarge, Function.comp_def] using hS
  · obtain ⟨⟨D, hD⟩, ⟨D', hD'⟩⟩ := hB
    refine ⟨⟨D, fun u hu ↦ ?_⟩, ⟨D', fun v hv ↦ ?_⟩⟩
    · simpa [enlarge, List.filter_map, Function.comp_def] using hD u hu
    · simpa [enlarge, List.filter_map, Function.comp_def] using hD' v hv

theorem ugSatisfied_enlarge (k : ℕ) (G : UGInstance) (σ τ : ℕ → ℕ) :
    ugSatisfied (enlarge k G) σ τ =
      G.2.2.2.countP fun c ↦ σ c.1.1 = (enlargeTable k c.2).getD (τ c.1.2) 0 := by
  simp [ugSatisfied, enlarge, List.filter_map, Function.comp_def, List.countP_eq_length_filter]

theorem ugSatisfied_eq_countP (G : UGInstance) (σ τ : ℕ → ℕ) :
    ugSatisfied G σ τ = G.2.2.2.countP fun c ↦ σ c.1.1 = c.2.getD (τ c.1.2) 0 := by
  simp [ugSatisfied, List.countP_eq_length_filter]

/-- **Lower bound on the value** by a labeling `(σ, τ)` of `ℕ`, with labels below `R` on the
vertices and `0` past them. -/
theorem le_ugValue (G : UGInstance) {σ τ : ℕ → ℕ} (hσ : ∀ u < G.1, σ u < G.2.2.1)
    (hτ : ∀ v < G.2.1, τ v < G.2.2.1) (hσ0 : ∀ u, G.1 ≤ u → σ u = 0)
    (hτ0 : ∀ v, G.2.1 ≤ v → τ v = 0) :
    (ugSatisfied G σ τ : ℝ) / G.2.2.2.length ≤ ugValue G := by
  have hs : lab (fun u : Fin G.1 ↦ (⟨σ u, hσ u u.isLt⟩ : Fin G.2.2.1)) = σ := by
    funext u; unfold lab; split_ifs with h
    · rfl
    · exact (hσ0 u (not_lt.1 h)).symm
  have ht : lab (fun v : Fin G.2.1 ↦ (⟨τ v, hτ v v.isLt⟩ : Fin G.2.2.1)) = τ := by
    funext v; unfold lab; split_ifs with h
    · rfl
    · exact (hτ0 v (not_lt.1 h)).symm
  have := frac_le_ugValue G (fun u ↦ ⟨σ u, hσ u u.isLt⟩) (fun v ↦ ⟨τ v, hτ v v.isLt⟩)
  rwa [frac, hs, ht] at this

/-- **Upper bound on the value** by a bound on every labeling `(σ, τ)` of `ℕ`, with labels below
`R` on the vertices and `0` past them. -/
theorem ugValue_le' {G : UGInstance} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ σ τ : ℕ → ℕ, (∀ u < G.1, σ u < G.2.2.1) → (∀ v < G.2.1, τ v < G.2.2.1) →
      (∀ u, G.1 ≤ u → σ u = 0) → (∀ v, G.2.1 ≤ v → τ v = 0) →
      (ugSatisfied G σ τ : ℝ) / G.2.2.2.length ≤ c) :
    ugValue G ≤ c := by
  refine ugValue_le hc fun σ τ ↦ h _ _ ?_ ?_ ?_ ?_
  · intro u hu; simp [lab, hu]
  · intro v hv; simp [lab, hv]
  · intro u hu; simp [lab, not_lt.2 hu]
  · intro v hv; simp [lab, not_lt.2 hv]

/-- A labeling of `G` is one of `enlarge k G`, satisfying the same constraints. -/
theorem ugValue_le_enlarge {R k : ℕ} (hk : 1 ≤ k) {G : UGInstance} (hG : Promised R G) :
    ugValue G ≤ ugValue (enlarge k G) := by
  obtain ⟨hV, hGR, -, -⟩ := hG
  have hle : G.2.2.1 ≤ G.2.2.1 * k := Nat.le_mul_of_pos_right _ hk
  refine ugValue_le' (ugValue_nonneg _) fun σ τ hσ hτ hσ0 hτ0 ↦ ?_
  refine le_of_eq_of_le ?_ (le_ugValue (enlarge k G) (σ := σ) (τ := τ)
    (fun u hu ↦ lt_of_lt_of_le (hσ u hu) hle) (fun v hv ↦ lt_of_lt_of_le (hτ v hv) hle) hσ0 hτ0)
  have hcount : (G.2.2.2.countP fun c ↦ σ c.1.1 = c.2.getD (τ c.1.2) 0) =
      G.2.2.2.countP fun c ↦ σ c.1.1 = (enlargeTable k c.2).getD (τ c.1.2) 0 := by
    refine List.countP_congr fun c hc ↦ ?_
    obtain ⟨-, h2, h3, -, -⟩ := hV c hc
    rw [getD_enlargeTable_of_lt hk]
    rw [h3]; exact hτ _ h2
  have hlen : (enlarge k G).2.2.2.length = G.2.2.2.length := by simp [enlarge]
  rw [ugSatisfied_enlarge, ugSatisfied_eq_countP, hcount, hlen]

/-- A labeling of `enlarge k G`, read modulo `R`, satisfies at least as many constraints of `G`. -/
theorem enlarge_ugValue_le {R k : ℕ} (hR : 1 ≤ R) {G : UGInstance} (hG : Promised R G) :
    ugValue (enlarge k G) ≤ ugValue G := by
  obtain ⟨hV, hGR, -, -⟩ := hG
  have hR' : 0 < G.2.2.1 := hGR ▸ hR
  refine ugValue_le' (ugValue_nonneg _) fun σ τ hσ hτ hσ0 hτ0 ↦ ?_
  refine le_trans ?_ (le_ugValue G (σ := fun u ↦ σ u % G.2.2.1) (τ := fun v ↦ τ v % G.2.2.1)
    (fun u _ ↦ Nat.mod_lt _ hR') (fun v _ ↦ Nat.mod_lt _ hR')
    (fun u hu ↦ by simp [hσ0 u hu]) (fun v hv ↦ by simp [hτ0 v hv]))
  rw [ugSatisfied_enlarge, ugSatisfied_eq_countP]
  have hlen : (enlarge k G).2.2.2.length = G.2.2.2.length := by simp [enlarge]
  rw [hlen]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine Nat.cast_le.2 (List.countP_mono_left fun c hc h ↦ ?_)
  obtain ⟨-, h2, h3, -, h5⟩ := hV c hc
  have hlt : ∀ a ∈ c.2, a < c.2.length := fun a ha ↦ h3 ▸ h5 a ha
  simp only [decide_eq_true_eq] at h ⊢
  have hτ' : τ c.1.2 < c.2.length * k := h3 ▸ hτ _ h2
  rw [getD_enlargeTable k c.2 hτ'] at h
  have hx := getD_lt hlt (Nat.mod_lt (τ c.1.2) (h3 ▸ hR'))
  rw [h3] at h hx
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- An instance with no constraints has value `0`. -/
theorem ugValue_eq_zero_of_nil {G : UGInstance} (h : G.2.2.2 = []) : ugValue G = 0 :=
  le_antisymm (ugValue_le le_rfl fun σ τ ↦ by simp [frac, h]) (ugValue_nonneg G)

/-- A valid instance with no labels has value `0`: it has no labeling, or no constraint. -/
theorem ugValue_eq_zero_of_zero {G : UGInstance} (hV : UGValid G) (h0 : G.2.2.1 = 0) :
    ugValue G = 0 := by
  refine le_antisymm (ugValue_le' le_rfl fun σ τ hσ _ _ _ ↦ ?_) (ugValue_nonneg G)
  rcases hcs : G.2.2.2 with _ | ⟨c, cs⟩
  · simp
  · have := hσ _ (hV c (hcs ▸ List.mem_cons_self ..)).1
    omega

end Enlarge

open Enlarge

/-- **Alphabet enlargement**: the gap problem with `R ≥ 1` labels reduces to the one with `R k`
labels, `k ≥ 1`. -/
theorem enlarge_reduces {R k : ℕ} (hR : 1 ≤ R) (hk : 1 ≤ k) (ε δ : ℝ) :
    PromiseProblem.PolyTimeReducible encUG encUG (ugGap R ε δ) (ugGap (R * k) ε δ) := by
  refine ⟨enlarge k, enlarge_polytime k, ?_, ?_⟩
  · rintro G ⟨hyes, hG⟩
    exact ⟨le_trans hyes (ugValue_le_enlarge hk hG), enlarge_good hG⟩
  · rintro G ⟨⟨hno, hlt⟩, hG⟩
    exact ⟨⟨le_trans (enlarge_ugValue_le hR hG) hno, hlt⟩, enlarge_good hG⟩

/-- NP-hardness with `R` labels gives NP-hardness with arbitrarily many labels (for `ε < 1` and
`0 ≤ δ`; with `R = 0` there are no yes-instances). -/
theorem exists_npHard_ge {R : ℕ} {ε δ : ℝ} (hε : ε < 1) (hδ : 0 ≤ δ)
    (h : PromiseProblem.NPHard encUG (ugGap R ε δ)) (R₀ : ℕ) :
    ∃ R' : ℕ, R₀ ≤ R' ∧ PromiseProblem.NPHard encUG (ugGap R' ε δ) := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · refine ⟨R₀, le_rfl, h.trans ⟨fun _ ↦ (0, 0, R₀, []), ComputableInPolyTime.const _, ?_, ?_⟩⟩
    · rintro G ⟨hyes, hV, hR0, -, -⟩
      rw [PromiseProblem.mem_yes_gapMax, ugValue_eq_zero_of_zero hV hR0] at hyes
      linarith
    · rintro G ⟨⟨-, hlt⟩, -⟩
      refine ⟨⟨by rw [ugValue_eq_zero_of_nil rfl]; exact hδ, hlt⟩, ?_, rfl, List.nodup_nil, ?_⟩
      · intro c hc; simp at hc
      · exact ⟨⟨0, fun u hu ↦ absurd hu (Nat.not_lt_zero _)⟩,
          ⟨0, fun v hv ↦ absurd hv (Nat.not_lt_zero _)⟩⟩
  · exact ⟨R * max R₀ 1, le_trans (le_max_left R₀ 1) (Nat.le_mul_of_pos_left _ hR),
      h.trans (enlarge_reduces hR (le_max_right _ _) ε δ)⟩

end BGHKLMM26.Hard
