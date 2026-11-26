import MPC.Basic.Lemmas
import MPC.Geometry.HalfPlaneChecker
/-!
# MPC.Invariants.DiscHTrace

The paper's Proposition 3.8 on periodic traces: on each half-plane, the number
of openable pieces of both sides plus the number of checking pieces is the same
in every state.

An openable piece (Section 2, class I that moves) is a present, non-glaring
piece on a square some move touches (`IsOpenableAt`). On a side `s` of the line
through both kings, `discHCount k s` counts the openable squares and the
checking squares there. There is exactly one checking square per state.

- A direct check (the destination glares) changes no openable square. The moved
  piece glares before and after (Lemmas 2.6, 2.8), and a captured piece glares
  (Lemma 2.9). The checker moves from the old checker's side to the
  destination, which is on the same side.
- A discovered check moves an openable piece from its source to its destination
  (Lemmas 2.4, 2.8). The old checker was on the destination's side, and the new
  checker is on the source's side. The two changes cancel.

The count uses the sign of `lineSide`, so points on the line count on neither
side and Propositions 3.5/3.6 are not needed here. -/

namespace MPC

namespace MoveTrace

/-- An openable piece stands on `q`: present, not glaring at its enemy king, and on
    a square that some move touches. -/
def IsOpenableAt (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (q : Pos) : Prop :=
  (tr.states k).board.grid q ≠ none ∧ ¬ tr.GlaresAtEnemyKing kp k q ∧ ¬ tr.ImmovableAt q

open Classical in
/-- The openable squares on side `s` of the line through both kings. -/
noncomputable def openableSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (s : ℤ) : Finset Pos :=
  Finset.univ.filter fun q =>
    0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q ∧ tr.IsOpenableAt kp k q

open Classical in
/-- The checking squares on side `s` of the line through both kings. -/
noncomputable def checkerSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (s : ℤ) : Finset Pos :=
  Finset.univ.filter fun q =>
    0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q ∧ tr.IsCheckerAt kp k q

/-- `|disc H|` for the half-plane on side `s`: openable pieces plus checking pieces. -/
noncomputable def discHCount (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (s : ℤ) : ℕ :=
  (tr.openableSquares kp k s).card + (tr.checkerSquares kp k s).card

theorem mem_openableSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (s : ℤ) (q : Pos) :
    q ∈ tr.openableSquares kp k s ↔
      0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q ∧ tr.IsOpenableAt kp k q := by
  simp [openableSquares]

theorem mem_checkerSquares (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (s : ℤ) (q : Pos) :
    q ∈ tr.checkerSquares kp k s ↔
      0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q ∧ tr.IsCheckerAt kp k q := by
  simp [checkerSquares]

/-- With a unique checking square `C`, a side holds one checker or none. -/
theorem checkerSquares_card_eq (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) (s : ℤ) (C : Pos) (hC : tr.IsCheckerAt kp k C)
    (huniq : ∀ C', tr.IsCheckerAt kp k C' → C' = C) :
    (tr.checkerSquares kp k s).card =
      if 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) C then 1 else 0 := by
  split_ifs with h
  · have : tr.checkerSquares kp k s = {C} := by
      ext q
      rw [mem_checkerSquares, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hq⟩
        exact huniq q hq
      · rintro rfl
        exact ⟨h, hC⟩
    rw [this, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hs, hq⟩ := (tr.mem_checkerSquares kp k s q).mp hq
    rw [huniq q hq] at hs
    exact h hs

/-- Moving one member from `a` to `b`: the count changes by the two indicators. -/
theorem card_move_eq (O O' : Finset Pos) (a b : Pos) (pa pb : Prop) [Decidable pa]
    [Decidable pb] (hO' : ∀ q, q ∈ O' ↔ (q ∈ O ∧ q ≠ a) ∨ (q = b ∧ pb))
    (ha : a ∈ O ↔ pa) (hb : b ∉ O) :
    O'.card + (if pa then 1 else 0) = O.card + (if pb then 1 else 0) := by
  by_cases hpa : pa <;> by_cases hpb : pb <;> simp only [hpa, hpb, ite_true, ite_false]
  · have haO : a ∈ O := ha.mpr hpa
    have e : O' = insert b (O.erase a) := by
      ext q
      rw [hO', Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
        · exact Or.inr ⟨h2, h1⟩
        · exact Or.inl h1
      · rintro (h1 | ⟨h1, h2⟩)
        · exact Or.inr ⟨h1, hpb⟩
        · exact Or.inl ⟨h2, h1⟩
    have hbn : b ∉ O.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    rw [e, Finset.card_insert_of_notMem hbn, Finset.card_erase_of_mem haO]
    have := Finset.card_pos.mpr ⟨a, haO⟩
    omega
  · have haO : a ∈ O := ha.mpr hpa
    have e : O' = O.erase a := by
      ext q
      rw [hO', Finset.mem_erase]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨_, h2⟩)
        · exact ⟨h2, h1⟩
        · exact absurd h2 hpb
      · rintro ⟨h1, h2⟩
        exact Or.inl ⟨h2, h1⟩
    rw [e, Finset.card_erase_of_mem haO]
    have := Finset.card_pos.mpr ⟨a, haO⟩
    omega
  · have haO : a ∉ O := fun h => hpa (ha.mp h)
    have e : O' = insert b O := by
      ext q
      rw [hO', Finset.mem_insert]
      constructor
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
        · exact Or.inr h1
        · exact Or.inl h1
      · rintro (h1 | h1)
        · exact Or.inr ⟨h1, hpb⟩
        · exact Or.inl ⟨h1, fun h => haO (h ▸ h1)⟩
    rw [e, Finset.card_insert_of_notMem hb]
  · have haO : a ∉ O := fun h => hpa (ha.mp h)
    have e : O' = O := by
      ext q
      rw [hO']
      constructor
      · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · exact h1
        · exact absurd h2 hpb
      · intro h1
        exact Or.inl ⟨h1, fun h => haO (h ▸ h1)⟩
    rw [e]

/-- A square whose contents a move does not change keeps its openable status,
    while the kings stay put. -/
private theorem isOpenableAt_congr (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) {k k' : Fin (tr.len + 1)} {q : Pos}
    (hq : (tr.states k).board.grid q = (tr.states k').board.grid q) (hkp : kp k = kp k') :
    tr.IsOpenableAt kp k q ↔ tr.IsOpenableAt kp k' q := by
  unfold IsOpenableAt
  rw [hq, tr.glaresAtEnemyKing_congr kp ht hq hkp]

/-- One move of Proposition 3.8: `|disc H|` is unchanged on each side. -/
theorem discHCount_succ_eq (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (s : ℤ) :
    tr.discHCount kp i.succ s = tr.discHCount kp i.castSucc s := by
  have hlen : 0 < tr.len := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hkpi : kp i.succ = kp i.castSucc := (hkp _).trans (hkp _).symm
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hgd := tr.glaringDestinationsCheck_of_periodic kp ht hs hk hsafe h0 hc hr hp
  -- The unique checker before the move, and the reply's side.
  obtain ⟨C, X, hX, hXo, hatkX⟩ := tr.inCheck_before_of_periodic kp ht hk hc hp i
  have hC : tr.IsCheckerAt kp i.castSucc C := ⟨X, hX, by
    rw [show kp i.castSucc X.owner.opponent = kp i.castSucc (tr.before i).turn by
      rw [hXo, Player.opponent_opponent]]
    exact hatkX⟩
  have huC : ∀ C', tr.IsCheckerAt kp i.castSucc C' → C' = C := fun C' h' =>
    tr.checker_unique_of_periodic kp ht hs hk hsafe h0 hc hr hp hlen i.castSucc C' C h' hC
  have huS : ∀ C₁ C₂, tr.IsCheckerAt kp i.succ C₁ → tr.IsCheckerAt kp i.succ C₂ → C₁ = C₂ :=
    fun C₁ C₂ h₁ h₂ =>
      tr.checker_unique_of_periodic kp ht hs hk hsafe h0 hc hr hp hlen i.succ C₁ C₂ h₁ h₂
  have hside := tr.destination_side_of_checker kp ht hs hk hsafe h0 hc hr hp i C hC s
  have eC := tr.checkerSquares_card_eq kp i.castSucc s C hC huC
  obtain ⟨D, hD⟩ : ∃ D, (tr.moves i).destination = D := ⟨_, rfl⟩
  rw [hD] at hside
  -- The destination was not openable before the move.
  have hDtouch : ¬ tr.ImmovableAt D := fun himm =>
    himm.2 i (by
      have h := Move.touches_destination (tr.moves i)
      rw [hD] at h
      exact h)
  have hDnot : ¬ tr.IsOpenableAt kp i.castSucc D := by
    rintro ⟨hocc, hng, _⟩
    have h := tr.glares_destination_of_occupied_of_periodic kp ht hs hk hsafe h0 hc hr hp i
      (by rw [hD]; exact hocc)
    rw [hD] at h
    exact hng h
  -- Squares away from the move keep their status.
  have hkeep : ∀ q : Pos, q ≠ D → (∀ (src : Pos) (promote : Bool),
      tr.moves i = .boardMove src D promote → q ≠ src) →
      (tr.IsOpenableAt kp i.succ q ↔ tr.IsOpenableAt kp i.castSucc q) := by
    intro q hqD hqs
    have key : ∀ mv : Move, tr.moves i = mv →
        (tr.states i.succ).board.grid q = (tr.states i.castSucc).board.grid q := by
      intro mv hm
      have hdst : mv.destination = D := by rw [← hm]; exact hD
      cases mv with
      | boardMove src dst promote =>
        change dst = D at hdst
        subst hdst
        exact tr.boardMove_grid_other ht i src dst promote q hm (hqs src promote hm) hqD
      | dropMove pt dst =>
        change dst = D at hdst
        subst hdst
        exact tr.dropMove_grid_other ht i pt dst q hm hqD
    exact tr.isOpenableAt_congr kp ht (key _ rfl) hkpi
  by_cases hgl : tr.GlaresAtEnemyKing kp i.succ D
  · -- A direct check: the openable squares do not change; the checker moves to `D`.
    obtain ⟨R, hR, hRo, hatkR⟩ := hgd i (by rw [hD]; exact hgl)
    rw [hD] at hR hatkR
    have hCD : tr.IsCheckerAt kp i.succ D := ⟨R, hR, by
      rw [show kp i.succ R.owner.opponent = kp i.succ (tr.before i).turn.opponent by
        rw [hRo, Player.opponent_opponent]]
      exact hatkR⟩
    have eD := tr.checkerSquares_card_eq kp i.succ s D hCD (fun C' h' => huS C' D h' hCD)
    have eO : tr.openableSquares kp i.succ s = tr.openableSquares kp i.castSucc s := by
      ext q
      rw [mem_openableSquares, mem_openableSquares]
      refine and_congr_right fun _ => ?_
      by_cases hqD : q = D
      · subst hqD
        exact ⟨fun h => absurd hgl h.2.1, fun h => absurd h hDnot⟩
      by_cases hsrc : ∃ (src : Pos) (promote : Bool),
          tr.moves i = .boardMove src D promote ∧ q = src
      · obtain ⟨src, promote, hm, rfl⟩ := hsrc
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exact (h.1 (tr.boardMove_grid_src ht i q D promote hm (hd i q D promote hm))).elim
        · exact (h.2.1 (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0
            hc hr hp i q D promote hm hgl)).elim
      · exact hkeep q hqD fun src promote hm h => hsrc ⟨src, promote, hm, h⟩
    unfold discHCount
    rw [eO, eD, eC, if_congr hside rfl rfl]
  · -- A discovered check: an openable piece moves from `src` to `D`, and the checker
    -- moves from `D`'s side to `src`'s side.
    obtain ⟨src, promote, hm⟩ : ∃ (src : Pos) (promote : Bool),
        tr.moves i = .boardMove src D promote := by
      have key : ∀ mv : Move, tr.moves i = mv →
          ∃ (src : Pos) (promote : Bool), tr.moves i = .boardMove src D promote := by
        intro mv hm
        have hdst : mv.destination = D := by rw [← hm]; exact hD
        cases mv with
        | boardMove src dst promote =>
          change dst = D at hdst
          exact ⟨src, promote, by rw [hm, hdst]⟩
        | dropMove pt dst =>
          change dst = D at hdst
          exfalso
          apply hgl
          rw [← hdst]
          exact tr.dropMove_glares_of_everyMoveChecksOpponent kp ht hs hk hsafe h0 hc i pt dst hm
      exact key _ rfl
    have hu := (tr.everyMoveChecksOpponent_glares_or_unblocked kp ht hs hk hsafe h0 hc i).resolve_left
      (by rw [hD]; exact hgl)
    obtain ⟨B, hB, hBside⟩ := tr.unblockedChecker_side_of_periodic kp ht hs hk hsafe h0 hc hr hp i
      src D promote hm hu
    have eB := tr.checkerSquares_card_eq kp i.succ s B hB (fun C' h' => huS C' B h' hB)
    have hsd : src ≠ D := hd i src D promote hm
    have hsrcng : ¬ tr.GlaresAtEnemyKing kp i.castSucc src := fun h =>
      hgl (tr.destination_glares_of_source_glares kp ht hs hk hsafe h0 hc i src D promote hm h)
    have hsrcopen : tr.IsOpenableAt kp i.castSucc src := by
      refine ⟨?_, hsrcng, fun himm => himm.2 i (by rw [hm]; exact Or.inl rfl)⟩
      obtain ⟨piece, hp', _⟩ := hs i src D promote hm
      change (tr.before i).board.grid src ≠ none
      rw [hp']
      exact Option.some_ne_none _
    have hDopen : tr.IsOpenableAt kp i.succ D := by
      refine ⟨?_, hgl, hDtouch⟩
      obtain ⟨P, hP, _⟩ := tr.destination_piece_owner ht hs i
      rw [hD] at hP
      rw [hP]
      exact Option.some_ne_none _
    have hmove := card_move_eq (tr.openableSquares kp i.castSucc s) (tr.openableSquares kp i.succ s)
      src D (0 < s * lineSide (kp 0 .sente) (kp 0 .gote) src)
      (0 < s * lineSide (kp 0 .sente) (kp 0 .gote) D)
      (by
        intro q
        rw [mem_openableSquares, mem_openableSquares]
        by_cases hqD : q = D
        · subst hqD
          constructor
          · rintro ⟨h1, _⟩
            exact Or.inr ⟨rfl, h1⟩
          · rintro (⟨⟨_, h⟩, _⟩ | ⟨_, h1⟩)
            · exact absurd h hDnot
            · exact ⟨h1, hDopen⟩
        by_cases hqs : q = src
        · subst hqs
          constructor
          · rintro ⟨_, h⟩
            exact absurd (tr.boardMove_grid_src ht i q D promote hm hsd) h.1
          · rintro (⟨_, h⟩ | ⟨h, _⟩)
            · exact absurd rfl h
            · exact absurd h hsd
        have hiff := hkeep q hqD fun src' promote' hm' h => by
          rw [hm] at hm'
          cases hm'
          exact hqs h
        rw [hiff]
        constructor
        · intro h
          exact Or.inl ⟨h, hqs⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact h
          · exact absurd h hqD)
      (by
        rw [mem_openableSquares]
        exact ⟨fun h => h.1, fun h => ⟨h, hsrcopen⟩⟩)
      (by
        rw [mem_openableSquares]
        exact fun h => hDnot h.2)
    unfold discHCount
    rw [eB, eC, if_congr (hBside s) rfl rfl, ← if_congr hside rfl rfl]
    omega

/-- Proposition 3.8: in a periodic trace satisfying 's premises, `|disc H|` on
    each side of the line through both kings is the same in every state. -/
theorem discHCount_eq_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (k : Fin (tr.len + 1)) (s : ℤ) :
    tr.discHCount kp k s = tr.discHCount kp 0 s := by
  induction k using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [tr.discHCount_succ_eq kp ht hs hk hsafe h0 hc hr hp i s, ih]

/-- Both half-planes together. -/
noncomputable def discHTotal (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (k : Fin (tr.len + 1)) : ℕ :=
  tr.discHCount kp k 1 + tr.discHCount kp k (-1)

theorem discHTotal_eq_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (k k' : Fin (tr.len + 1)) :
    tr.discHTotal kp k = tr.discHTotal kp k' := by
  unfold discHTotal
  rw [tr.discHCount_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp k 1,
    tr.discHCount_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp k (-1),
    tr.discHCount_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp k' 1,
    tr.discHCount_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp k' (-1)]

end MoveTrace
end MPC
