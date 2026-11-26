import MPC.Basic.Lemmas
import MPC.Geometry.OpenableLine
/-!
# MPC.Geometry.OpenableLineCyclic

The paper's Proposition 3.3 and Corollary 3.4 in full, on periodic traces.
proved them for an interval that ends at a later departure inside one period.
Here the openable piece's stay on `A` may wrap around the end of the period, and
the departure is derived rather than assumed:

- A square nobody touches keeps its contents (`grid_eq_of_untouched`).
- From any state where `A` holds a non-glaring piece, the first later move that
  touches `A` moves that piece away. A move onto `A` would remove a non-glaring
  piece, which Lemma 2.9 forbids (`departure_of_not_glares_of_periodic`).
- When a move puts a non-glaring piece on `A`, either `A` is touched again later
  in the period, or `A` keeps the piece up to the last
  state, which equals the first. Then the departure comes early in the period,
   gives the glaring piece `Q` up to it, and the periodicity-free interval
  theorem carries `Q` back from the last state to the arrival.

The cyclic interval is the predicate `cyclicBetween`. -/

namespace MPC

/-- `k` lies on the cyclic interval from `a` to `b`. When `b < a` the interval
    wraps around the end of the period. -/
def cyclicBetween {n : ℕ} (a b k : Fin (n + 1)) : Prop :=
  (a ≤ b ∧ a ≤ k ∧ k ≤ b) ∨ (b < a ∧ (a ≤ k ∨ k ≤ b))

instance {n : ℕ} (a b k : Fin (n + 1)) : Decidable (cyclicBetween a b k) := by
  unfold cyclicBetween
  infer_instance

/-- The start of a cyclic interval belongs to it. -/
theorem cyclicBetween_self_left {n : ℕ} (a b : Fin (n + 1)) : cyclicBetween a b a := by
  rcases le_or_gt a b with h | h
  · exact Or.inl ⟨h, le_refl a, h⟩
  · exact Or.inr ⟨h, Or.inl (le_refl a)⟩

/-- Without wrapping, a cyclic interval is an ordinary one. -/
theorem cyclicBetween_iff_of_le {n : ℕ} {a b : Fin (n + 1)} (k : Fin (n + 1)) (h : a ≤ b) :
    cyclicBetween a b k ↔ a ≤ k ∧ k ≤ b := by
  constructor
  · rintro (⟨_, h1, h2⟩ | ⟨h', _⟩)
    · exact ⟨h1, h2⟩
    · exact absurd h (not_le.mpr h')
  · intro hk
    exact Or.inl ⟨h, hk⟩

/-- Every move touches its destination. -/
theorem Move.touches_destination (m : Move) : m.Touches m.destination := by
  cases m with
  | boardMove src dst promote => exact Or.inr rfl
  | dropMove pt dst => rfl

namespace MoveTrace

/-- A square that no move of `[a, k)` touches keeps its contents from `a` to `k`. -/
theorem grid_eq_of_untouched (tr : MoveTrace) (ht : tr.FollowsTransitions) (A : Pos)
    {a k : Fin (tr.len + 1)} (hak : a ≤ k)
    (hun : ∀ m : Fin tr.len, a ≤ m.castSucc → m.castSucc < k → ¬ (tr.moves m).Touches A) :
    (tr.states k).board.grid A = (tr.states a).board.grid A := by
  revert hak hun
  induction k using Fin.induction with
  | zero =>
    intro hak _
    rw [Fin.le_zero_iff.mp hak]
  | succ i ih =>
    intro hak hun
    by_cases he : a = i.succ
    · rw [he]
    · have hai : a ≤ i.castSucc := Fin.le_castSucc_iff.mpr (lt_of_le_of_ne hak he)
      have hmi : ¬ (tr.moves i).Touches A := hun i hai (Fin.castSucc_lt_succ (i := i))
      rw [← ih hai fun m h1 h2 => hun m h1 (lt_trans h2 (Fin.castSucc_lt_succ (i := i)))]
      have key : ∀ mv : Move, tr.moves i = mv →
          (tr.states i.succ).board.grid A = (tr.states i.castSucc).board.grid A := by
        intro mv hm
        rw [hm] at hmi
        cases mv with
        | boardMove src dst promote =>
          simp only [Move.Touches, not_or] at hmi
          exact tr.boardMove_grid_other ht i src dst promote A hm hmi.1 hmi.2
        | dropMove pt dst =>
          exact tr.dropMove_grid_other ht i pt dst A hm hmi
      exact key _ rfl

/-- The destination of a move afterwards holds a piece of the mover. -/
theorem destination_piece_owner (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (hs : tr.BoardMoveSourcesOwned) (i : Fin tr.len) :
    ∃ P : Piece, (tr.states i.succ).board.grid (tr.moves i).destination = some P ∧
      P.owner = (tr.before i).turn := by
  have key : ∀ mv : Move, tr.moves i = mv → ∃ P : Piece,
      (tr.states i.succ).board.grid mv.destination = some P ∧ P.owner = (tr.before i).turn := by
    intro mv hm
    cases mv with
    | boardMove src dst promote =>
      obtain ⟨piece, hp, ho⟩ := hs i src dst promote hm
      have h := tr.boardMove_grid_dst ht i src dst promote hm
      rw [hp] at h
      exact ⟨_, h, ho⟩
    | dropMove pt dst =>
      exact ⟨_, tr.dropMove_grid_dst ht i pt dst hm, rfl⟩
  exact key _ rfl

/-- Before a move, no piece of the mover attacks the opponent's king by a step,
    since step attacks ignore the board and the opponent is not in check. -/
theorem not_stepAttack_of_before (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hsafe : tr.EveryMoveLeavesOwnKingSafe kp)
    (h0 : tr.InitialOpponentKingSafe kp) (j : Fin tr.len) (B : Pos) (Q : Piece)
    (hQ : (tr.before j).board.grid B = some Q) (hown : Q.owner = (tr.before j).turn) :
    Pos.dirTo B (kp j.castSucc (tr.before j).turn.opponent) ∉
      Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner) := by
  intro hst
  exact tr.before_opponent_not_inCheck kp ht hsafe h0 j
    ⟨B, Q, hQ, by rw [hown, Player.opponent_opponent], Or.inl hst⟩

/-- In a periodic trace satisfying 's premises, suppose `A` holds a
    non-glaring piece at state `a` and some later move touches `A`. Then the
    first such move moves that piece off `A`; until then `A` keeps it. -/
theorem departure_of_not_glares_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (A : Pos) (a : Fin (tr.len + 1))
    (hocc : (tr.states a).board.grid A ≠ none) (hng : ¬ tr.GlaresAtEnemyKing kp a A)
    (hex : ∃ m : Fin tr.len, a ≤ m.castSucc ∧ (tr.moves m).Touches A) :
    ∃ (j : Fin tr.len) (dst : Pos) (promote : Bool), a ≤ j.castSucc ∧
      tr.moves j = .boardMove A dst promote ∧
      ∀ k : Fin (tr.len + 1), a ≤ k → k ≤ j.castSucc →
        (tr.states k).board.grid A = (tr.states a).board.grid A := by
  classical
  have hP : ∃ n, ∃ h : n < tr.len, a.val ≤ n ∧ (tr.moves ⟨n, h⟩).Touches A := by
    obtain ⟨m, hm1, hm2⟩ := hex
    exact ⟨m.val, m.isLt, hm1, hm2⟩
  obtain ⟨hn, han, htouch⟩ := Nat.find_spec hP
  obtain ⟨j, hj⟩ : ∃ j : Fin tr.len, j.val = Nat.find hP := ⟨⟨_, hn⟩, rfl⟩
  have hjeq : j = ⟨Nat.find hP, hn⟩ := Fin.ext hj
  have htj : (tr.moves j).Touches A := by
    rw [hjeq]
    exact htouch
  have haj : a ≤ j.castSucc := by
    rw [Fin.le_def]
    show a.val ≤ j.val
    omega
  have hconst : ∀ k : Fin (tr.len + 1), a ≤ k → k ≤ j.castSucc →
      (tr.states k).board.grid A = (tr.states a).board.grid A := by
    intro k hak hkj
    apply tr.grid_eq_of_untouched ht A hak
    intro m hm1 hm2 htm
    have hmj : m.val < Nat.find hP := by
      rw [Fin.lt_def] at hm2
      rw [Fin.le_def] at hkj
      have : (m.castSucc : Fin (tr.len + 1)).val = m.val := rfl
      have : (j.castSucc : Fin (tr.len + 1)).val = j.val := rfl
      omega
    exact Nat.find_min hP hmj ⟨m.isLt, hm1, htm⟩
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  -- The first move touching `A` cannot land on it.
  have hnot_dest : (tr.moves j).destination ≠ A := by
    intro hd
    have hgrid := hconst j.castSucc haj (le_refl _)
    have hocc_j : (tr.before j).board.grid (tr.moves j).destination ≠ none := by
      rw [hd]
      change (tr.states j.castSucc).board.grid A ≠ none
      rw [hgrid]
      exact hocc
    have hg := tr.glares_destination_of_occupied_of_periodic kp ht hs hk hsafe h0 hc hr hp j hocc_j
    rw [hd] at hg
    exact hng ((tr.glaresAtEnemyKing_congr kp ht hgrid ((hkp _).trans (hkp _).symm)).mp hg)
  have key : ∀ mv : Move, tr.moves j = mv → ∃ (dst : Pos) (promote : Bool),
      tr.moves j = .boardMove A dst promote := by
    intro mv hm
    rw [hm] at htj
    cases mv with
    | boardMove src dst promote =>
      rcases htj with hA | hA
      · exact ⟨dst, promote, by rw [hm, hA]⟩
      · exact absurd (show (tr.moves j).destination = A by rw [hm]; exact hA.symm) hnot_dest
    | dropMove pt dst =>
      exact absurd (show (tr.moves j).destination = A by rw [hm]; exact htj.symm) hnot_dest
  obtain ⟨dst, promote, hmj⟩ := key _ rfl
  exact ⟨j, dst, promote, haj, hmj, hconst⟩

/-- Proposition 3.3 in full: in a periodic trace satisfying 's premises,
    let move `i` put a non-glaring piece on `A`. Then the piece later leaves `A`
    by a board move `j` (possibly in the next period). Some piece `Q` of the
    arriving side stands on a square `B` whose line to the enemy king runs
    through `A`. On the whole cyclic interval from the arrival to the departure,
    `A` keeps its piece and `Q` stays on `B` and glares: it is neither moved nor
    captured. -/
theorem openable_glaring_line_cyclic_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination) :
    ∃ (j : Fin tr.len) (dst : Pos) (promote : Bool) (B : Pos) (Q : Piece),
      tr.moves j = .boardMove (tr.moves i).destination dst promote ∧
      Q.owner = (tr.before i).turn ∧
      (tr.moves i).destination.toInt ∈ slidePath B (kp 0 Q.owner.opponent) ∧
      ∀ k : Fin (tr.len + 1), cyclicBetween i.succ j.castSucc k →
        (tr.states k).board.grid (tr.moves i).destination =
          (tr.states i.succ).board.grid (tr.moves i).destination ∧
        (tr.states k).board.grid B = some Q ∧ tr.GlaresAtEnemyKing kp k B := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hgd := tr.glaringDestinationsCheck_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have htouch_i := Move.touches_destination (tr.moves i)
  obtain ⟨P, hP, hPo⟩ := tr.destination_piece_owner ht hs i
  generalize (tr.moves i).destination = A at hng htouch_i hP ⊢
  have hocc : (tr.states i.succ).board.grid A ≠ none := by
    rw [hP]
    exact Option.some_ne_none _
  -- The departing side is the arriving side: the same piece leaves `A`.
  have howner : ∀ (j : Fin tr.len) (dst : Pos) (promote : Bool),
      tr.moves j = .boardMove A dst promote →
      (tr.states j.castSucc).board.grid A = (tr.states i.succ).board.grid A →
      (tr.before j).turn = (tr.before i).turn := by
    intro j dst promote hmj hgrid
    obtain ⟨piece, hpiece, ho⟩ := hs j A dst promote hmj
    change (tr.states j.castSucc).board.grid A = some piece at hpiece
    rw [hgrid, hP] at hpiece
    cases hpiece
    exact ho.symm.trans hPo
  by_cases hcase : ∃ m : Fin tr.len, i.succ ≤ m.castSucc ∧ (tr.moves m).Touches A
  · -- The departure comes later in the same period.
    obtain ⟨j, dst, promote, hij, hmj, hconst⟩ :=
      tr.departure_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp A i.succ hocc hng hcase
    have hgridj := hconst j.castSucc hij (le_refl _)
    have hnsj : ¬ tr.GlaresAtEnemyKing kp j.castSucc A := fun h =>
      hng ((tr.glaresAtEnemyKing_congr kp ht hgridj ((hkp _).trans (hkp _).symm)).mp h)
    obtain ⟨B, Q, hown, hmem, hall⟩ := tr.openable_glaring_line_of_periodic kp ht hs hk hsafe h0
      hc hr hp j A dst promote hmj hnsj (a := i.succ) fun k h1 h2 => by
        rw [hconst k (le_of_lt h1) h2]
        exact hocc
    have hturn := howner j dst promote hmj hgridj
    refine ⟨j, dst, promote, B, Q, hmj, hown.trans hturn, by rw [hown]; exact hmem,
      fun k hk => ?_⟩
    rw [cyclicBetween_iff_of_le k hij] at hk
    exact ⟨hconst k hk.1 hk.2, (hall k hk.1 hk.2).1, (hall k hk.1 hk.2).2⟩
  · -- `A` keeps its piece to the end of the period, so the departure wraps.
    push Not at hcase
    have hperiod : tr.states (Fin.last tr.len) = tr.states 0 := hp
    have hlast : (tr.states (Fin.last tr.len)).board.grid A =
        (tr.states i.succ).board.grid A :=
      tr.grid_eq_of_untouched ht A (Fin.le_last _) fun m h1 _ => hcase m h1
    have hzero : (tr.states 0).board.grid A = (tr.states i.succ).board.grid A := by
      rw [← hperiod]
      exact hlast
    have hocc0 : (tr.states 0).board.grid A ≠ none := by
      rw [hzero]
      exact hocc
    have hng0 : ¬ tr.GlaresAtEnemyKing kp 0 A := fun h =>
      hng ((tr.glaresAtEnemyKing_congr kp ht hzero ((hkp _).trans (hkp _).symm)).mp h)
    obtain ⟨j, dst, promote, _, hmj, hconst⟩ :=
      tr.departure_of_not_glares_of_periodic kp ht hs hk hsafe h0 hc hr hp A 0 hocc0 hng0
        ⟨i, Fin.zero_le _, htouch_i⟩
    have hji : j.castSucc < i.succ := by
      by_contra h
      push Not at h
      exact hcase j h (by rw [hmj]; exact Or.inl rfl)
    have hgridj := hconst j.castSucc (Fin.zero_le _) (le_refl _)
    have hnsj : ¬ tr.GlaresAtEnemyKing kp j.castSucc A := fun h =>
      hng0 ((tr.glaresAtEnemyKing_congr kp ht hgridj ((hkp _).trans (hkp _).symm)).mp h)
    obtain ⟨B, Q, hown, hmem, hall⟩ := tr.openable_glaring_line_of_periodic kp ht hs hk hsafe h0
      hc hr hp j A dst promote hmj hnsj (a := 0) fun k h1 h2 => by
        rw [hconst k (le_of_lt h1) h2]
        exact hocc0
    have hturn := howner j dst promote hmj (hgridj.trans hzero)
    have hmem' : A.toInt ∈ slidePath B (kp 0 Q.owner.opponent) := by
      rw [hown]
      exact hmem
    -- Carry `Q` from the first state to the last and back to the arrival.
    obtain ⟨hQ0, hgl0⟩ := hall 0 (le_refl _) (Fin.zero_le _)
    have hQlast : (tr.states (Fin.last tr.len)).board.grid B = some Q := by
      rw [hperiod]
      exact hQ0
    have hgllast : tr.GlaresAtEnemyKing kp (Fin.last tr.len) B :=
      (tr.glaresAtEnemyKing_congr kp ht (hQlast.trans hQ0.symm)
        ((hkp _).trans (hkp _).symm)).mpr hgl0
    have hstep : Pos.dirTo B (kp 0 Q.owner.opponent) ∉
        Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner) := by
      have h := tr.not_stepAttack_of_before kp ht hsafe h0 j B Q
        (hall j.castSucc (Fin.zero_le _) (le_refl _)).1 hown
      rw [hkp j.castSucc, ← hown] at h
      exact h
    have hcore := tr.grid_eq_of_glares_through_occupied kp ht hd hkp hgd (a := i.succ)
      (b := Fin.last tr.len) B A Q hQlast hgllast hmem' hstep fun k h1 _ => by
        rw [tr.grid_eq_of_untouched ht A (le_of_lt h1) fun m hm1 _ => hcase m hm1]
        exact hocc
    refine ⟨j, dst, promote, B, Q, hmj, hown.trans hturn, hmem', fun k hk => ?_⟩
    rcases hk with ⟨hle, _, _⟩ | ⟨_, hk | hk⟩
    · exact absurd hle (not_le.mpr hji)
    · have hQk := hcore k hk (Fin.le_last k)
      refine ⟨tr.grid_eq_of_untouched ht A hk fun m hm1 _ => hcase m hm1, hQk, ?_⟩
      exact (tr.glaresAtEnemyKing_congr kp ht (hQk.trans hQlast.symm)
        ((hkp _).trans (hkp _).symm)).mpr hgllast
    · obtain ⟨hQk, hglk⟩ := hall k (Fin.zero_le _) hk
      exact ⟨(hconst k (Fin.zero_le _) hk).trans hzero, hQk, hglk⟩

/-- Corollary 3.4 in full: under the same premises, when a move puts a
    non-glaring piece on its destination, right afterwards the destination lies
    on the glaring line of another piece of the arriving side. If an enemy piece
    checked the mover's king before the move, the destination is that checker's
    square or lies on its sliding line to the king. -/
theorem openable_destination_lines_cyclic_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len)
    (hng : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination)
    (C : Pos) (X : Piece) (hX : (tr.before i).board.grid C = some X)
    (hXo : X.owner = (tr.before i).turn.opponent)
    (hatk : attacksOriented (tr.before i).board X.owner X.pieceType C
      (kp i.castSucc (tr.before i).turn)) :
    (∃ (B : Pos) (Q : Piece), Q.owner = (tr.before i).turn ∧
      (tr.moves i).destination.toInt ∈ slidePath B (kp 0 Q.owner.opponent) ∧
      (tr.states i.succ).board.grid B = some Q ∧ tr.GlaresAtEnemyKing kp i.succ B) ∧
    ((tr.moves i).destination = C ∨
      ((tr.moves i).destination.toInt ∈ slidePath C (kp i.castSucc (tr.before i).turn) ∧
        Pos.dirTo C (kp i.castSucc (tr.before i).turn) ∉
          X.pieceType.stepDirs.map (Dir.forPlayer · X.owner))) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨_, _, _, B, Q, _, hown, hmem, hall⟩ :=
    tr.openable_glaring_line_cyclic_of_periodic kp ht hs hk hsafe h0 hc hr hp i hng
  obtain ⟨_, hQ, hgl⟩ := hall i.succ (cyclicBetween_self_left _ _)
  exact ⟨⟨B, Q, hown, hmem, hQ, hgl⟩, tr.destination_on_checker_line kp ht hs hsafe i
    (by rw [hkp i.succ, hkp i.castSucc]) C X hX hXo hatk⟩

end MoveTrace
end MPC
