module

public import BGHKLMM26.Hardness.Coins
public import BGHKLMM26.Hardness.Concentration

/-!
# Glue for the proof of Theorem 1.2

* Good instances with constraints pass the machine's check (`BGHKLMM26.Hard.ok_of_good`), and the
  fixed output on the others, the triangle, is a no-instance of Max-Cut
  (`BGHKLMM26.Hard.maxCutValue_triangle_le`).
* The vertices of the graph are the pairs `(v, x)` (`BGHKLMM26.Hard.vtxEquiv`), so a cut is a
  family of tables `f_v`.
* The cuts whose tables are all LTFs (`BGHKLMM26.Hard.ltfCuts`): at most `(2^R + 1)^((R+1)|V|)`
  of them, and a cut whose tables are on average within `δ` of LTFs is within `δ n` vertices of one
  of them (`BGHKLMM26.Hard.exists_ltfCut_near`).
-/

@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad

variable {P : Prm} {G : UGInstance} {R : ℕ}

/-! ### The check -/

theorem le_length_of_good {R : ℕ} {G : UGInstance} (hG : GoodI R G) (hcs : G.2.2.2 ≠ []) :
    G.1 ≤ G.2.2.2.length ∧ G.2.1 ≤ G.2.2.2.length := by
  obtain ⟨D, hD, hlen, -⟩ := exists_right_degree hG hcs
  refine ⟨?_, ?_⟩
  · obtain ⟨DL, hDL⟩ := hG.2.2.2.1
    have hlt : ∀ c ∈ G.2.2.2, c.1.1 < G.1 := fun c hc ↦ (hG.1 c hc).1
    have := list_sum_group (fun c : UGConstraint ↦ c.1.1) G.2.2.2 G.1 hlt (fun _ ↦ (1 : ℝ))
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at this
    rw [Finset.sum_congr rfl fun u hu ↦ by rw [hDL u (mem_range.1 hu)], sum_const, card_range,
      nsmul_eq_mul] at this
    have hlenL : G.2.2.2.length = G.1 * DL := by exact_mod_cast this
    have hDL1 : 0 < DL := Nat.pos_of_ne_zero fun h0 ↦ hcs (by
      rw [h0, mul_zero] at hlenL; exact List.length_eq_zero_iff.1 hlenL)
    rw [hlenL]; exact Nat.le_mul_of_pos_right _ hDL1
  · rw [hlen]; exact Nat.le_mul_of_pos_right _ hD

theorem ok_of_good (hG : GoodI P.R G) (hcs : G.2.2.2 ≠ []) : P.ok G = true := by
  obtain ⟨h1, h2⟩ := le_length_of_good hG hcs
  exact ok_iff.2 ⟨hG.2.1, List.length_pos_iff.2 hcs, h1, h2⟩

theorem nil_of_not_ok (hG : GoodI P.R G) (hok : P.ok G = false) : G.2.2.2 = [] := by
  by_contra hcs
  rw [ok_of_good hG hcs] at hok
  exact Bool.noConfusion hok

/-! ### The single vertex -/

theorem maxCutValue_pointGraph : maxCutValue pointGraph = 0 := by
  classical
  unfold maxCutValue
  rw [div_eq_zero_iff]
  right
  norm_cast
  refine Finset.card_eq_zero.2 (Finset.eq_empty_iff_forall_notMem.2 fun e he ↦ ?_)
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ a b => exact (show ¬ pointGraph.2.Adj a b from fun h ↦ h) he

theorem maxDegree_pointGraph (d : ℕ) : MaxDegreeAtMost pointGraph d := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine le_of_eq_of_le (Finset.card_eq_zero.2
    (Finset.eq_empty_iff_forall_notMem.2 fun w hw ↦ ?_)) (Nat.zero_le d)
  rw [SimpleGraph.mem_neighborFinset] at hw
  exact (show ¬ pointGraph.2.Adj v w from fun h ↦ h) hw

/-! ### Vertices as pairs -/

theorem vtx_injective {R nV : ℕ} :
    Function.Injective fun p : Fin nV × Cube (Fin R) ↦ vtx p.1.1 p.2 := by
  intro p p' h
  have h1 := (vtx_eq_iff (x := p.2) (v := p.1.1)).1 rfl
  have h2 := (vtx_eq_iff (x := p'.2) (v := p'.1.1)).1 rfl
  simp only at h
  rw [h] at h1
  exact Prod.ext (Fin.ext (h1.1.trans h2.1.symm))
    (cubeIdx_injective (h1.2.trans h2.2.symm))

/-- The vertex `(v, x)` of the graph on `n = |V| 2^R` vertices. -/
noncomputable def vtxEquiv (R nV : ℕ) {n : ℕ} (hn : n = nV * 2 ^ R) :
    Fin nV × Cube (Fin R) ≃ Fin n :=
  Equiv.ofBijective (fun p ↦ ⟨vtx p.1.1 p.2, hn ▸ vtx_lt p.1.2 p.2⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun p p' h ↦ vtx_injective (Fin.ext_iff.1 h), ?_⟩
    simp [hn])

theorem vtxEquiv_apply {R nV n : ℕ} (hn : n = nV * 2 ^ R) (v : Fin nV) (x : Cube (Fin R)) :
    (vtxEquiv R nV hn (v, x)).1 = vtx v.1 x := rfl

/-- Every family of tables comes from a cut of the graph. -/
theorem exists_cut_of_tables (R nV : ℕ) {n : ℕ} (hn : n = nV * 2 ^ R)
    (F : ℕ → Cube (Fin R) → Bool) :
    ∃ f : Fin n → Bool, ∀ v < nV, ∀ x, liftCut f (vtx v x) = F v x := by
  refine ⟨fun a ↦ F ((vtxEquiv R nV hn).symm a).1.1 ((vtxEquiv R nV hn).symm a).2,
    fun v hv x ↦ ?_⟩
  have hlt : vtx v x < n := hn ▸ vtx_lt hv x (R := R)
  simp only [liftCut, hlt, dite_true]
  have : (⟨vtx v x, hlt⟩ : Fin n) = vtxEquiv R nV hn (⟨v, hv⟩, x) := rfl
  rw [this, Equiv.symm_apply_apply]

/-! ### Cuts whose tables are LTFs -/

open Classical in
/-- The cuts of the graph whose tables are all LTFs. -/
noncomputable def ltfCuts (R nV : ℕ) {n : ℕ} (hn : n = nV * 2 ^ R) : Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin nV → {L : Cube (Fin R) → Bool // IsLTF L})).image
    fun Ls a ↦ (Ls ((vtxEquiv R nV hn).symm a).1).1 ((vtxEquiv R nV hn).symm a).2

theorem card_ltfCuts_le (R nV : ℕ) {n : ℕ} (hn : n = nV * 2 ^ R) :
    (ltfCuts R nV hn).card ≤ ((2 ^ R + 1) ^ (R + 1)) ^ nV := by
  classical
  unfold ltfCuts
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  refine Nat.pow_le_pow_left ?_ _
  rw [← Nat.card_eq_fintype_card]
  exact card_ltf_le R

theorem expect_abs_bitVal (F L : Cube (Fin R) → Bool) :
    𝔼 x, |bitVal (F x) - bitVal (L x)| =
      ((univ.filter fun x ↦ F x ≠ L x).card : ℝ) / 2 ^ R := by
  rw [Finset.expect_eq_sum_div_card, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  congr 1
  · rw [Finset.card_filter]
    push_cast
    refine sum_congr rfl fun x _ ↦ ?_
    cases F x <;> cases L x <;> simp [bitVal]
  · push_cast; ring

theorem card_filter_prod {nV : ℕ} (Q : Fin nV → Cube (Fin R) → Prop)
    [∀ v, DecidablePred (Q v)] :
    (univ.filter fun p : Fin nV × Cube (Fin R) ↦ Q p.1 p.2).card =
      ∑ v : Fin nV, (univ.filter (Q v)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- **A cut near LTFs is near a cut of `ltfCuts`**: a cut differs from one of `ltfCuts` in
`2^R ∑_v dist(f_v, ℒ)` vertices. -/
theorem exists_ltfCut_near (R nV : ℕ) {n : ℕ} (hn : n = nV * 2 ^ R) (f : Fin n → Bool) :
    ∃ L ∈ ltfCuts R nV hn, ((univ.filter fun a ↦ f a ≠ L a).card : ℝ) =
      2 ^ R * ∑ v ∈ range nV, ltfDist (fun x ↦ bitVal (liftCut f (vtx (R := R) v x))) := by
  classical
  have hL : ∀ v : Fin nV, ∃ L : {L : Cube (Fin R) → Bool // IsLTF L},
      𝔼 x, |bitVal (liftCut f (vtx v.1 x)) - bitVal (L.1 x)| =
        ltfDist (fun x ↦ bitVal (liftCut f (vtx (R := R) v.1 x))) := fun v ↦ by
    obtain ⟨L, hL, h⟩ := exists_ltfDist_eq (fun x ↦ bitVal (liftCut f (vtx (R := R) v.1 x)))
    exact ⟨⟨L, hL⟩, h⟩
  choose Ls hLs using hL
  refine ⟨fun a ↦ (Ls ((vtxEquiv R nV hn).symm a).1).1 ((vtxEquiv R nV hn).symm a).2,
    mem_image.2 ⟨Ls, mem_univ _, rfl⟩, ?_⟩
  have hf : ∀ (v : Fin nV) (x : Cube (Fin R)), f (vtxEquiv R nV hn (v, x)) =
      liftCut f (vtx v.1 x) := fun v x ↦ by
    have hlt : vtx v.1 x < n := hn ▸ vtx_lt v.2 x
    simp only [liftCut, hlt, dite_true]
    rfl
  have hcount : (univ.filter fun a ↦ f a ≠
      (Ls ((vtxEquiv R nV hn).symm a).1).1 ((vtxEquiv R nV hn).symm a).2).card =
      ∑ v : Fin nV, (univ.filter fun x ↦ liftCut f (vtx v.1 x) ≠ (Ls v).1 x).card := by
    rw [← Finset.card_map (vtxEquiv R nV hn).symm.toEmbedding]
    have : ((univ.filter fun a ↦ f a ≠
        (Ls ((vtxEquiv R nV hn).symm a).1).1 ((vtxEquiv R nV hn).symm a).2).map
          (vtxEquiv R nV hn).symm.toEmbedding) =
        univ.filter fun p : Fin nV × Cube (Fin R) ↦
          liftCut f (vtx p.1.1 p.2) ≠ (Ls p.1).1 p.2 := by
      ext p
      simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have := hf ((vtxEquiv R nV hn).symm a).1 ((vtxEquiv R nV hn).symm a).2
        rw [Prod.mk.eta, Equiv.apply_symm_apply] at this
        rw [← this]
        exact ha
      · intro hp
        refine ⟨vtxEquiv R nV hn p, ?_, Equiv.symm_apply_apply _ _⟩
        rw [Equiv.symm_apply_apply, ← Prod.mk.eta (p := p), hf]
        exact hp
    rw [this, card_filter_prod (fun v x ↦ liftCut f (vtx v.1 x) ≠ (Ls v).1 x)]
  rw [hcount]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun v ↦ ltfDist (fun x ↦ bitVal (liftCut f (vtx (R := R) v x)))),
    Finset.mul_sum]
  refine sum_congr rfl fun v _ ↦ ?_
  rw [← hLs v, expect_abs_bitVal]
  field_simp

end BGHKLMM26.Hard
