import MPC.Geometry.KingImmobility
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
/-!
# MPC.Glare.NonGlaringCount

The paper's Lemmas 2.8 and 2.9 on independent traces, by counting instead of
tracking pieces. While the kings stay put, whether a square glares at its enemy
king depends only on the piece standing there, because the immovable squares
keep their contents. Count the occupied squares whose piece does not glare. A
glaring piece only moves to glaring squares (Lemma 2.6) and every drop glares
(Lemma 2.7), so a move never raises the count. Moving a non-glaring piece to a
glaring square, or removing a non-glaring piece from a move's destination,
lowers it. In a periodic trace the count returns to its initial value, so
neither happens: a non-glaring piece never moves to a glaring square
(Lemma 2.8) and is never captured (Lemma 2.9). Overwriting by a drop is
covered too. No GameSeq is used, and pieces are not followed through hands.
-/

namespace MPC
namespace MoveTrace

open Classical in
/-- Occupied squares of state `k` whose piece does not glare at its enemy king. -/
noncomputable def nonGlaringSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) : Finset Pos :=
  Finset.univ.filter fun q => (tr.states k).board.grid q ≠ none ∧ ¬ tr.GlaresAtEnemyKing kp k q

theorem mem_nonGlaringSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (q : Pos) :
    q ∈ tr.nonGlaringSquares kp k ↔
      (tr.states k).board.grid q ≠ none ∧ ¬ tr.GlaresAtEnemyKing kp k q := by
  simp [nonGlaringSquares]

/-- Glare is determined by the square's contents and the king positions: the
    stripped boards of two states agree when the square holds the same piece. -/
theorem glaresAtEnemyKing_congr (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) {k k' : Fin (tr.len + 1)} {q : Pos}
    (hq : (tr.states k).board.grid q = (tr.states k').board.grid q) (hkp : kp k = kp k') :
    tr.GlaresAtEnemyKing kp k q ↔ tr.GlaresAtEnemyKing kp k' q := by
  have hgrid : ∀ k₁ k₂ : Fin (tr.len + 1),
      (tr.states k₁).board.grid q = (tr.states k₂).board.grid q →
        ∀ r, (tr.strippedBoard k₁ q).grid r = (tr.strippedBoard k₂ q).grid r := by
    intro k₁ k₂ h r
    simp only [strippedBoard]
    split_ifs with hr
    · rcases hr with rfl | himm
      · exact h
      · rw [tr.immovableAt_grid_eq ht himm k₁, tr.immovableAt_grid_eq ht himm k₂]
    · rfl
  have dir : ∀ k₁ k₂ : Fin (tr.len + 1),
      (tr.states k₁).board.grid q = (tr.states k₂).board.grid q → kp k₁ = kp k₂ →
        tr.GlaresAtEnemyKing kp k₁ q → tr.GlaresAtEnemyKing kp k₂ q := by
    rintro k₁ k₂ h hk ⟨piece, hp, ha⟩
    refine ⟨piece, h.symm.trans hp, ?_⟩
    rw [← hk]
    exact attacksOriented_mono_of_empty_preserved _ _
      (fun r hr => (hgrid k₁ k₂ h r).symm.trans hr) _ _ _ _ ha
  exact ⟨dir k k' hq hkp, dir k' k hq.symm hkp.symm⟩

/-- For a board move, sending the destination back to the source maps the next
    state's non-glaring squares into the current ones, and the source is never
    among them. -/
private theorem boardMove_mapsTo (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote) (hsd : src ≠ dst)
    (hkp : kp i.succ = kp i.castSucc) (q : Pos) (hq : q ∈ tr.nonGlaringSquares kp i.succ) :
    (if q = dst then src else q) ∈ tr.nonGlaringSquares kp i.castSucc ∧ q ≠ src := by
  obtain ⟨hocc, hng⟩ := (tr.mem_nonGlaringSquares kp i.succ q).mp hq
  by_cases hqd : q = dst
  · subst hqd
    rw [ite_eq_left rfl]
    refine ⟨(tr.mem_nonGlaringSquares kp i.castSucc src).mpr ⟨?_, ?_⟩, Ne.symm hsd⟩
    · obtain ⟨piece, hp, _⟩ := hs i src q promote hm
      change (tr.before i).board.grid src ≠ none
      rw [hp]
      exact Option.some_ne_none _
    · exact fun hg => hng (tr.destination_glares_of_source_glares kp ht hs hk hsafe h0 hc i src q
        promote hm hg)
  · rw [ite_eq_right hqd]
    have hqs : q ≠ src := by
      rintro rfl
      exact hocc (tr.boardMove_grid_src ht i q dst promote hm hsd)
    have hg : (tr.states i.succ).board.grid q = (tr.states i.castSucc).board.grid q :=
      tr.boardMove_grid_other ht i src dst promote q hm hqs hqd
    refine ⟨(tr.mem_nonGlaringSquares kp i.castSucc q).mpr ⟨hg ▸ hocc, ?_⟩, hqs⟩
    exact fun h => hng ((tr.glaresAtEnemyKing_congr kp ht hg hkp).mpr h)

private theorem boardMove_injOn (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote) (hsd : src ≠ dst) :
    Set.InjOn (fun q => if q = dst then src else q) (tr.nonGlaringSquares kp i.succ : Set Pos) := by
  intro q₁ h₁ q₂ h₂ he
  have hsrc : ∀ q, q ∈ tr.nonGlaringSquares kp i.succ → q ≠ src := by
    intro q hq hqs
    subst hqs
    exact ((tr.mem_nonGlaringSquares kp i.succ q).mp hq).1
      (tr.boardMove_grid_src ht i q dst promote hm hsd)
  simp only at he
  by_cases e₁ : q₁ = dst <;> by_cases e₂ : q₂ = dst
  · rw [e₁, e₂]
  · rw [ite_eq_left e₁, ite_eq_right e₂] at he
    exact absurd he.symm (hsrc q₂ h₂)
  · rw [ite_eq_right e₁, ite_eq_left e₂] at he
    exact absurd he (hsrc q₁ h₁)
  · rwa [ite_eq_right e₁, ite_eq_right e₂] at he

/-- A drop's destination glares afterwards, and every other square keeps its
    piece and its glare. -/
private theorem dropMove_subset (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) (pt : PieceType) (dst : Pos)
    (hm : tr.moves i = .dropMove pt dst) (hkp : kp i.succ = kp i.castSucc) :
    tr.nonGlaringSquares kp i.succ ⊆ (tr.nonGlaringSquares kp i.castSucc).erase dst := by
  intro q hq
  obtain ⟨hocc, hng⟩ := (tr.mem_nonGlaringSquares kp i.succ q).mp hq
  have hqd : q ≠ dst := by
    rintro rfl
    exact hng (tr.dropMove_glares_of_everyMoveChecksOpponent kp ht hs hk hsafe h0 hc i pt q hm)
  have hg : (tr.states i.succ).board.grid q = (tr.states i.castSucc).board.grid q :=
    tr.dropMove_grid_other ht i pt dst q hm hqd
  refine Finset.mem_erase.mpr ⟨hqd, (tr.mem_nonGlaringSquares kp i.castSucc q).mpr ⟨hg ▸ hocc, ?_⟩⟩
  exact fun h => hng ((tr.glaresAtEnemyKing_congr kp ht hg hkp).mpr h)

/-- While the kings stay put, a move never raises the number of non-glaring
    squares. -/
theorem nonGlaringSquares_card_succ_le (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hd : tr.BoardMoveEndpointsDistinct) (i : Fin tr.len)
    (hkp : kp i.succ = kp i.castSucc) :
    (tr.nonGlaringSquares kp i.succ).card ≤ (tr.nonGlaringSquares kp i.castSucc).card := by
  rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
  · have hsd := hd i src dst promote hm
    exact Finset.card_le_card_of_injOn _
      (fun q hq => (boardMove_mapsTo tr kp ht hs hk hsafe h0 hc i src dst promote hm hsd hkp q hq).1)
      (boardMove_injOn tr kp ht i src dst promote hm hsd)
  · exact (Finset.card_le_card (dropMove_subset tr kp ht hs hk hsafe h0 hc i pt dst hm hkp)).trans
      (Finset.card_erase_le)

/-- Moving a non-glaring piece to a glaring square lowers the count. -/
theorem nonGlaringSquares_card_succ_lt_of_glares_destination (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hd : tr.BoardMoveEndpointsDistinct) (i : Fin tr.len)
    (hkp : kp i.succ = kp i.castSucc) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hsrc : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (hdst : tr.GlaresAtEnemyKing kp i.succ dst) :
    (tr.nonGlaringSquares kp i.succ).card < (tr.nonGlaringSquares kp i.castSucc).card := by
  have hsd := hd i src dst promote hm
  have hmem : src ∈ tr.nonGlaringSquares kp i.castSucc := by
    refine (tr.mem_nonGlaringSquares kp i.castSucc src).mpr ⟨?_, hsrc⟩
    obtain ⟨piece, hp, _⟩ := hs i src dst promote hm
    change (tr.before i).board.grid src ≠ none
    rw [hp]
    exact Option.some_ne_none _
  refine lt_of_le_of_lt (Finset.card_le_card_of_injOn (fun q => if q = dst then src else q) ?_
    (boardMove_injOn tr kp ht i src dst promote hm hsd)) (Finset.card_erase_lt_of_mem hmem)
  intro q hq
  obtain ⟨hmap, hqs⟩ := boardMove_mapsTo tr kp ht hs hk hsafe h0 hc i src dst promote hm hsd hkp q hq
  have hqd : q ≠ dst := by
    rintro rfl
    exact ((tr.mem_nonGlaringSquares kp i.succ q).mp hq).2 hdst
  simp only [ite_eq_right hqd] at hmap ⊢
  exact Finset.mem_erase.mpr ⟨hqs, hmap⟩

/-- Removing a non-glaring piece from a move's destination lowers the count. This
    covers captures and drops onto an occupied square. -/
theorem nonGlaringSquares_card_succ_lt_of_occupied_destination (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hd : tr.BoardMoveEndpointsDistinct) (i : Fin tr.len)
    (hkp : kp i.succ = kp i.castSucc)
    (h : (tr.moves i).destination ∈ tr.nonGlaringSquares kp i.castSucc) :
    (tr.nonGlaringSquares kp i.succ).card < (tr.nonGlaringSquares kp i.castSucc).card := by
  refine lt_of_le_of_lt ?_ (Finset.card_erase_lt_of_mem h)
  rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
  · have hsd := hd i src dst promote hm
    refine Finset.card_le_card_of_injOn (fun q => if q = dst then src else q) ?_
      (boardMove_injOn tr kp ht i src dst promote hm hsd)
    intro q hq
    obtain ⟨hmap, hqs⟩ :=
      boardMove_mapsTo tr kp ht hs hk hsafe h0 hc i src dst promote hm hsd hkp q hq
    refine Finset.mem_erase.mpr ⟨?_, hmap⟩
    show (if q = dst then src else q) ≠ dst
    split_ifs with hqd
    · exact hsd
    · exact hqd
  · exact Finset.card_le_card (dropMove_subset tr kp ht hs hk hsafe h0 hc i pt dst hm hkp)

/-- In a periodic trace satisfying 's premises, the number of non-glaring
    squares is the same in every state. -/
theorem nonGlaringSquares_card_eq_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (k : Fin (tr.len + 1)) :
    (tr.nonGlaringSquares kp k).card = (tr.nonGlaringSquares kp 0).card := by
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hconst := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hstep : ∀ i : Fin tr.len,
      (tr.nonGlaringSquares kp i.succ).card ≤ (tr.nonGlaringSquares kp i.castSucc).card :=
    fun i => tr.nonGlaringSquares_card_succ_le kp ht hs hk hsafe h0 hc hd i
      ((hconst _).trans (hconst _).symm)
  have hmono : ∀ {j l : Fin (tr.len + 1)}, j ≤ l →
      (tr.nonGlaringSquares kp l).card ≤ (tr.nonGlaringSquares kp j).card := by
    intro j l hjl
    revert hjl
    induction l using Fin.induction with
    | zero =>
      intro hjl
      rw [Fin.le_zero_iff.mp hjl]
    | succ i ih =>
      intro hjl
      by_cases he : j = i.succ
      · rw [he]
      · have hlt : j < i.succ := Nat.lt_of_le_of_ne hjl fun hv => he (Fin.ext hv)
        exact (hstep i).trans (ih (Fin.le_castSucc_iff.mpr hlt))
  have hlast : tr.nonGlaringSquares kp (Fin.last tr.len) = tr.nonGlaringSquares kp 0 := by
    have hgrid : ∀ q, (tr.states (Fin.last tr.len)).board.grid q = (tr.states 0).board.grid q :=
      fun q => by rw [show tr.states (Fin.last tr.len) = tr.states 0 from hp]
    ext q
    rw [tr.mem_nonGlaringSquares, tr.mem_nonGlaringSquares, hgrid q,
      tr.glaresAtEnemyKing_congr kp ht (hgrid q) (hp.kingPos_last hk)]
  have h1 := hmono (Fin.zero_le k)
  have h2 := hmono (Fin.le_last k)
  rw [hlast] at h2
  omega

/-- Lemma 2.8: in a periodic mutual-check trace satisfying 's premises, a
    board move to a glaring square moves a glaring piece. -/
theorem glares_source_of_glares_destination_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote) (hg : tr.GlaresAtEnemyKing kp i.succ dst) :
    tr.GlaresAtEnemyKing kp i.castSucc src := by
  by_contra hns
  have hconst := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hlt := tr.nonGlaringSquares_card_succ_lt_of_glares_destination kp ht hs hk hsafe h0 hc
    (tr.boardMoveEndpointsDistinct_of_oriented hs hr) i ((hconst _).trans (hconst _).symm)
    src dst promote hm hns hg
  have e1 := tr.nonGlaringSquares_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp i.succ
  have e2 := tr.nonGlaringSquares_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp i.castSucc
  omega

/-- Lemma 2.9: under the same premises, a piece standing on a move's destination
    glares at its enemy king, so a non-glaring piece is never captured (nor
    overwritten by a drop). -/
theorem glares_destination_of_occupied_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len)
    (h : (tr.before i).board.grid (tr.moves i).destination ≠ none) :
    tr.GlaresAtEnemyKing kp i.castSucc (tr.moves i).destination := by
  by_contra hng
  have hconst := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hlt := tr.nonGlaringSquares_card_succ_lt_of_occupied_destination kp ht hs hk hsafe h0 hc
    (tr.boardMoveEndpointsDistinct_of_oriented hs hr) i ((hconst _).trans (hconst _).symm)
    ((tr.mem_nonGlaringSquares kp i.castSucc _).mpr ⟨h, hng⟩)
  have e1 := tr.nonGlaringSquares_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp i.succ
  have e2 := tr.nonGlaringSquares_card_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp i.castSucc
  omega

/-- Lemmas 2.6 and 2.8 together: under the same premises, a board move's source
    glares before it exactly when its destination glares after it. -/
theorem glares_destination_iff_source_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote) :
    tr.GlaresAtEnemyKing kp i.succ dst ↔ tr.GlaresAtEnemyKing kp i.castSucc src :=
  ⟨tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0 hc hr hp i src dst
      promote hm,
    tr.destination_glares_of_source_glares kp ht hs hk hsafe h0 hc i src dst promote hm⟩

end MoveTrace
end MPC
