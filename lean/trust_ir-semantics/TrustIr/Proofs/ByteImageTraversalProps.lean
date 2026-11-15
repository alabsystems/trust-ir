-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.State.ByteImageTraversal

namespace TrustIr.ByteImage

private theorem get_cast {size target : Nat} (h : size = target) (tree : Tree size) (index : Nat) :
    (cast (congrArg Tree h) tree).get index = tree.get index := by
  cases h
  rfl

theorem Tree.storageHeight_window {size : Nat} (tree : Tree size) (offset count : Nat)
    (inside : offset + count ≤ size) :
    (tree.window offset count inside).storageHeight ≤ tree.storageHeight + 1 := by
  induction tree generalizing offset count with
  | view original start size bound ih =>
    simp only [Tree.window, Tree.storageHeight]
    have := ih (start + offset) count (by omega)
    omega
  | fill size byte => exact Nat.le_refl _
  | literal data => exact Nat.le_refl _
  | append left right _ _ => exact Nat.le_refl _
  | periodic unit positive phase size _ => exact Nat.le_refl _
  | source size read => exact Nat.le_refl _

/-- Once the source is a view, further cropping cannot increase stored depth.
    This holds even for externally constructed, already nested views. -/
theorem Tree.storageHeight_window_view {sourceSize : Nat} (source : Tree sourceSize)
    (start size : Nat) (bound : start + size ≤ sourceSize) (offset count : Nat)
    (inside : offset + count ≤ size) :
    ((Tree.view source start size bound).window offset count inside).storageHeight ≤
      (Tree.view source start size bound).storageHeight := by
  exact source.storageHeight_window (start + offset) count (by omega)

theorem get_slice_exact (image : ByteImage) (offset count index : Nat) :
    (image.slice offset count).get index =
      if index < min count (image.size - offset) then image.get (offset + index) else none := by
  by_cases inside : index < min count (image.size - offset)
  · rw [if_pos inside]
    exact image.get_slice offset count index (by omega) (by omega)
  · rw [if_neg inside]
    apply get_outside
    rw [size_slice]
    omega

theorem Tree.get_map_inside {size : Nat} (tree : Tree size)
    (f : Option UInt8 → Option UInt8) (index : Nat) (inside : index < size) :
    (tree.map f).get index = f (tree.get index) := by
  induction tree generalizing index with
  | fill count byte => simp [Tree.map, Tree.get, inside]
  | source count read => simp [Tree.map, Tree.get, inside]
  | literal data =>
    have sizes : (data.map f).size = data.size := by simp
    change (cast (congrArg Tree sizes) (Tree.literal (data.map f))).get index = f ((Tree.literal data).get index)
    rw [get_cast sizes (Tree.literal (data.map f)) index]
    have inMapped : index < (data.map f).size := by simpa using inside
    simp only [Tree.get, if_pos inside, if_pos inMapped]
    first
    | rw [Array.getElem?_lt _ inMapped, Array.getElem?_lt _ inside]
      simp only [Option.getD_some, Array.getElem_eq_data_get]
      apply Option.some.inj
      rw [← List.get?_eq_get inMapped, Array.map_data, List.get?_map, List.get?_eq_get inside]
      rfl
    | rw [Array.getElem?_eq_getElem inMapped,Array.getElem?_eq_getElem inside]
      simp only [Option.getD_some,Array.getElem_map]

  | periodic original positive phase count ih =>
    simp only [Tree.map, Tree.get, if_pos inside]
    exact ih _ (Nat.mod_lt _ positive)
  | view original offset count bound ih =>
    simp only [Tree.map, Tree.get, if_pos inside]
    exact ih _ (by omega)
  | @append leftSize rightSize left right ihl ihr =>
    simp only [Tree.map, Tree.get, if_pos inside]
    by_cases before : index < leftSize
    · simp only [if_pos before]
      exact ihl _ before
    · simp only [if_neg before]
      exact ihr _ (by omega)

theorem get_map_inside (image : ByteImage) (f : Option UInt8 → Option UInt8)
    (index : Nat) (inside : index < image.size) :
    (image.map f).get index = f (image.get index) :=
  image.tree.get_map_inside f index inside

/-- The smart repetition preserves every byte, including arbitrary phases,
    clipped tails, nested finite windows, and out-of-range absence. -/
theorem Tree.get_repeatWindow {size : Nat} (tree : Tree size) (positive : 0 < size)
    (phase count index : Nat) :
    (tree.repeatWindow positive phase count).get index =
      if index < count then tree.get ((phase + index) % size) else none := by
  induction tree generalizing phase count with
  | periodic unit innerPositive innerPhase size ih =>
    simp only [Tree.repeatWindow]
    split
    · rename_i aligned
      rw [ih]
      by_cases inside : index < count
      · simp only [if_pos inside, Tree.get,
          if_pos (Nat.mod_lt _ positive)]
        congr 1
        have divides := Nat.dvd_of_mod_eq_zero aligned
        rw [Nat.mod_add_mod, Nat.add_assoc]
        rw [Nat.add_mod innerPhase ((phase + index) % size),
          Nat.mod_mod_of_dvd _ divides, ← Nat.add_mod]
      · simp [inside]
    · rfl
  | fill size byte => rfl
  | literal data => rfl
  | append left right _ _ => rfl
  | view original offset size within _ => rfl
  | source size read => rfl

/-- An exact depth law: normalization removes precisely the certified prefix.
    It never treats a logical extent as a bound on retained template depth. -/
theorem Tree.storageHeight_repeatWindow {size : Nat} (tree : Tree size)
    (positive : 0 < size) (phase count : Nat) :
    (tree.repeatWindow positive phase count).storageHeight =
      tree.storageHeight + 1 - tree.alignedPrefix := by
  induction tree generalizing phase count with
  | periodic unit innerPositive innerPhase size ih =>
    simp only [Tree.repeatWindow, Tree.storageHeight, Tree.alignedPrefix]
    split
    · rw [ih]
      omega
    · simp only [Tree.storageHeight, Nat.sub_zero]
  | fill size byte => rfl
  | literal data => rfl
  | append left right _ _ => rfl
  | view original offset size within _ => rfl
  | source size read => rfl

theorem Tree.repeatWindow_unaligned {period size : Nat} (unit : Tree period)
    (innerPositive : 0 < period) (positive : 0 < size) (innerPhase phase count : Nat)
    (unaligned : size % period ≠ 0) :
    (Tree.periodic unit innerPositive innerPhase size).repeatWindow positive phase count =
      Tree.periodic (.periodic unit innerPositive innerPhase size) positive phase count := by
  simp only [Tree.repeatWindow, if_neg unaligned]

/-- The retained period always divides the original finite template extent.
    Divisibility is a structural certificate, not a guess from sampled bytes. -/
theorem Tree.repeatWindow_template {size : Nat} (tree : Tree size)
    (positive : 0 < size) (phase count : Nat) :
    ∃ (period : Nat) (unit : Tree period) (nonempty : 0 < period) (start : Nat),
      tree.repeatWindow positive phase count = .periodic unit nonempty start count ∧
        period ∣ size := by
  induction tree generalizing phase count with
  | periodic unit innerPositive innerPhase size ih =>
    simp only [Tree.repeatWindow]
    split
    · rename_i aligned
      obtain ⟨period, source, nonempty, start, result, divides⟩ :=
        ih innerPositive ((innerPhase + phase) % _) count
      exact ⟨period, source, nonempty, start, result,
        Nat.dvd_trans divides (Nat.dvd_of_mod_eq_zero aligned)⟩
    · exact ⟨_, _, positive, phase, rfl, Nat.dvd_refl _⟩
  | fill size byte => exact ⟨_, _, positive, phase, rfl, Nat.dvd_refl _⟩
  | literal data => exact ⟨_, _, positive, phase, rfl, Nat.dvd_refl _⟩
  | append left right _ _ => exact ⟨_, _, positive, phase, rfl, Nat.dvd_refl _⟩
  | view original offset size within _ => exact ⟨_, _, positive, phase, rfl, Nat.dvd_refl _⟩
  | source size read => exact ⟨_, _, positive, phase, rfl, Nat.dvd_refl _⟩

theorem storageHeight_tile (unit : ByteImage) (count : Nat) :
    (unit.tile count).tree.storageHeight ≤ unit.tree.storageHeight + 1 := by
  unfold tile
  by_cases hEmpty : unit.size = 0
  · rw [dif_pos hEmpty]
    change 1 ≤ _
    omega
  · rw [dif_neg hEmpty]
    by_cases hZero : count = 0
    · rw [if_pos hZero]
      change 1 ≤ _
      omega
    · rw [if_neg hZero]
      by_cases hOne : count = 1
      · rw [if_pos hOne]
        omega
      · rw [if_neg hOne]
        change (unit.tree.repeatWindow _ _ _).storageHeight ≤ _
        rw [Tree.storageHeight_repeatWindow]
        exact Nat.sub_le _ _

/-- Retiling an aligned periodic head never increases its actual stored depth,
    even if its retained template contains views or further unaligned windows. -/
theorem storageHeight_tile_aligned {period size : Nat} (unit : Tree period)
    (positive : 0 < period) (phase count : Nat) (aligned : size % period = 0) :
    ((⟨size, .periodic unit positive phase size⟩ : ByteImage).tile count).tree.storageHeight ≤
      unit.storageHeight + 1 := by
  unfold tile
  by_cases hEmpty : size = 0
  · rw [dif_pos hEmpty]
    change 1 ≤ _
    omega
  · rw [dif_neg hEmpty]
    by_cases hZero : count = 0
    · rw [if_pos hZero]
      change 1 ≤ _
      omega
    · rw [if_neg hZero]
      by_cases hOne : count = 1
      · rw [if_pos hOne]
        exact Nat.le_refl _
      · rw [if_neg hOne]
        change ((Tree.periodic unit positive phase size).repeatWindow _ _ _).storageHeight ≤ _
        rw [Tree.repeatWindow, if_pos aligned]
        rw [Tree.storageHeight_repeatWindow]
        exact Nat.sub_le _ _

private def phaseUnit : ByteImage := ByteImage.ofList [some 1, some 2, some 3]
private def clippedPhaseUnit : ByteImage :=
  ⟨5, .periodic phaseUnit.tree (by decide) 1 5⟩

/-- A concrete kernel counterexample to unconditional phase flattening:
    repeating the finite five-byte word must restart at byte five. -/
theorem unaligned_flattening_changes_byte :
    ((clippedPhaseUnit.tile 2).get 5,
      (⟨10, .periodic phaseUnit.tree (by decide) 1 10⟩ : ByteImage).get 5) =
        (some 2, some 1) := rfl

/-- Repetition preserves the actual template at every logical byte, for
    arbitrary extents. The empty-template case has no in-range observation. -/
theorem get_tile_inside (unit : ByteImage) (count index : Nat)
    (inside : index < unit.size * count) :
    (unit.tile count).get index = unit.get (index % unit.size) := by
  by_cases empty : unit.size = 0
  · simp [empty] at inside <;> omega
  by_cases zero : count = 0
  · simp [zero] at inside <;> omega
  by_cases one : count = 1
  · have inUnit : index < unit.size := by simpa [one] using inside
    simp [tile, empty, zero, one, Nat.mod_eq_of_lt inUnit]
  · unfold tile
    rw [dif_neg empty, if_neg zero, if_neg one]
    change (unit.tree.repeatWindow (by omega) 0 (unit.size * count)).get index = _
    simpa only [if_pos inside, Nat.zero_add, ByteImage.get] using
      (Tree.get_repeatWindow unit.tree (by omega) 0 (unit.size * count) index)

/-- Every periodic window returned by the structural recognizer has a real
    nonempty template and agrees with every byte of the original window. -/
theorem Tree.periodicWindow_sound {size : Nat} (tree : Tree size)
    (offset count : Nat) (unit : ByteImage) (phase : Nat)
    (found : tree.periodicWindow offset count = some (unit, phase)) :
    0 < unit.size ∧ offset + count ≤ size ∧
      ∀ index, index < count →
        tree.get (offset + index) = unit.get ((phase + index) % unit.size) := by
  induction tree generalizing offset count unit phase with
  | fill size byte =>
    rw [Tree.periodicWindow] at found
    split at found
    · contradiction
    · cases found
      refine ⟨by change 0 < 1; omega, by omega, ?_⟩
      intro index inside
      simp only [Tree.get, ByteImage.fill, ByteImage.get, Nat.zero_add, Nat.mod_one]
      rw [if_pos (by omega)]
      rfl
  | literal data =>
    rw [Tree.periodicWindow] at found
    split at found <;> contradiction
  | source size read =>
    rw [Tree.periodicWindow] at found
    split at found <;> contradiction
  | periodic original positive oldPhase size _ih =>
    rw [Tree.periodicWindow] at found
    split at found
    · contradiction
    · cases found
      refine ⟨positive, by omega, ?_⟩
      intro index inside
      have inSize : offset + index < size := by omega
      rw [Tree.get, if_pos inSize]
      change original.get ((oldPhase + (offset + index)) % _) =
        original.get ((((oldPhase + offset) % _) + index) % _)
      congr 1
      rw [← Nat.add_assoc, Nat.add_mod (oldPhase + offset) index]
      simp only [Nat.add_mod, Nat.mod_mod]
  | view original start size within ih =>
    rw [Tree.periodicWindow] at found
    split at found
    · contradiction
    · obtain ⟨positive, _bound, exactBytes⟩ := ih (start + offset) count unit phase found
      refine ⟨positive, by omega, ?_⟩
      intro index inside
      have inSize : offset + index < size := by omega
      rw [Tree.get, if_pos inSize]
      simpa only [Nat.add_assoc] using exactBytes index inside
  | @append leftSize rightSize left right ihl ihr =>
    rw [Tree.periodicWindow] at found
    split at found
    · contradiction
    · split at found
      · obtain ⟨positive, _bound, exactBytes⟩ := ihl offset count unit phase found
        refine ⟨positive, by omega, ?_⟩
        intro index inside
        have inLeft : offset + index < leftSize := by omega
        rw [Tree.get, if_pos (by omega), if_pos inLeft]
        exact exactBytes index inside
      · split at found
        · obtain ⟨positive, bound, exactBytes⟩ := ihr (offset - leftSize) count unit phase found
          refine ⟨positive, by omega, ?_⟩
          intro index inside
          rw [Tree.get, if_pos (by omega), if_neg (by omega)]
          have arithmetic : offset + index - leftSize = offset - leftSize + index := by omega
          rw [arithmetic]
          exact exactBytes index inside
        · contradiction

theorem periodicWindow_sound (image : ByteImage) (unit : ByteImage) (phase : Nat)
    (found : image.periodicWindow = some (unit, phase)) :
    0 < unit.size ∧ ∀ index, index < image.size →
      image.get index = unit.get ((phase + index) % unit.size) := by
  obtain ⟨positive, _, exactBytes⟩ := image.tree.periodicWindow_sound 0 image.size unit phase found
  exact ⟨positive, fun index inside => by simpa only [Nat.zero_add] using exactBytes index inside⟩

#trustIrAxioms Tree.periodicWindow_sound <= [Classical.choice, propext, Quot.sound]
#trustIrAxioms periodicWindow_sound <= [Classical.choice, propext, Quot.sound]

#trustIrAxioms Tree.get_map_inside <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms get_map_inside <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms get_tile_inside <= [propext, Classical.choice, Quot.sound]

#trustIrAxioms Tree.get_repeatWindow <= [Classical.choice, propext, Quot.sound]
#trustIrAxioms Tree.storageHeight_repeatWindow <= [Classical.choice, propext, Quot.sound]
#trustIrAxioms Tree.repeatWindow_unaligned <= [propext]
#trustIrAxioms Tree.repeatWindow_template <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms storageHeight_tile <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms storageHeight_tile_aligned <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms unaligned_flattening_changes_byte <= [propext, Classical.choice, Quot.sound]

#trustIrAxioms Tree.get_window <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms Tree.storageHeight_window <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms Tree.storageHeight_window_view <= [propext, Classical.choice, Quot.sound]

#trustIrAxioms Tree.firstWhere_sound <= [Classical.choice, propext, Quot.sound]
#trustIrAxioms firstWhere_sound <= [Classical.choice, propext, Quot.sound]

#trustIrAxioms Tree.firstWhere_none <= [propext, Quot.sound, Classical.choice]
#trustIrAxioms Tree.firstWhere_eq_none_iff <= [propext, Quot.sound, Classical.choice]
#trustIrAxioms firstWhere_eq_none_iff <= [Quot.sound, propext, Classical.choice]

#trustIrAxioms Tree.firstWhere_before <= [Classical.choice, propext, Quot.sound]
#trustIrAxioms Tree.firstWhere_eq_some_iff <= [Classical.choice, propext, Quot.sound]
#trustIrAxioms firstWhere_eq_some_iff <= [Quot.sound, Classical.choice, propext]

/-- Advancing a complete decoded-value cycle restores the exact byte phase.
    This justifies retaining one value template, even for callbacks that
    observe the canonical byte constructor's phase metadata. -/
theorem block_phase_cycle (period width phase index : Nat) :
    (phase + (index % (period / Nat.gcd period width)) * width) % period =
      (phase + index * width) % period := by
  let cycle := period / Nat.gcd period width
  have cycleProduct : cycle * width = Nat.lcm period width := by
    dsimp only [cycle]
    unfold Nat.lcm
    rw [Nat.mul_comm period width, Nat.mul_div_assoc width (Nat.gcd_dvd_left period width)]
    exact Nat.mul_comm _ _
  have divides : period ∣ cycle * width := by
    rw [cycleProduct]
    exact Nat.dvd_lcm_left period width
  have decomposition : index * width = (index % cycle) * width + (cycle * width) * (index / cycle) := by
    calc
      index * width = (index % cycle + cycle * (index / cycle)) * width :=
        congrArg (· * width) (Nat.mod_add_div index cycle).symm
      _ = _ := by rw [Nat.add_mul]; congr 1; ac_rfl
  have tailZero : ((cycle * width) * (index / cycle)) % period = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans divides (Nat.dvd_mul_right _ _))
  change (phase + (index % cycle) * width) % period = (phase + index * width) % period
  apply Eq.symm
  rw [decomposition, ← Nat.add_assoc, Nat.add_mod, tailZero, Nat.add_zero, Nat.mod_mod]

/-- Successful logical block mapping retains an actual callback image for
    every slot, with the exact original source bytes. All periodic/window
    premises of the lower proof are discharged by their proved laws. -/
theorem mapBlocksSpec_decoded {α ε : Type} (decode : ByteImage → Except ε α)
    (image : ByteImage) (width count : Nat) (extent : image.size = width * count) :
    BlockResult (DecodedSlots decode image width) (fun _ : ε => True)
      (mapBlocksSpec decode image width count) :=
  mapBlocksSpec_decoded_of_periods block_phase_cycle periodicWindow_sound decode image width count extent

/-- An actual successful mapBlocks run supplies slot-indexed callback custody.
    This is a logical semantics theorem, not a native cache refinement claim. -/
theorem mapBlocks_decoded {α ε : Type} (decode : ByteImage → Except ε α)
    (image : ByteImage) (width count : Nat) (extent : image.size = width * count)
    (tree : CompactArray.Tree α count) (run : mapBlocks decode image width count = .ok tree) :
    DecodedSlots decode image width tree := by
  have held := mapBlocksSpec_decoded decode image width count extent
  change mapBlocksSpec decode image width count = .ok tree at run
  rw [run] at held
  exact held

/-- The production mapper's errors come from actual visible callback windows. -/
theorem mapBlocksSpec_failure {α ε : Type} (decode : ByteImage → Except ε α) (image : ByteImage)
    (width count : Nat) (extent : image.size = width * count) :
    BlockResult (fun _ => True) (FailedSlots decode image width count) (mapBlocksSpec decode image width count) :=
  mapBlocksSpec_failure_of_periods periodicWindow_sound decode image width count extent

theorem mapBlocks_failure {α ε : Type} (decode : ByteImage → Except ε α) (image : ByteImage)
    (width count : Nat) (extent : image.size = width * count) (failure : ε)
    (run : mapBlocks decode image width count = .error failure) : FailedSlots decode image width count failure := by
  have held := mapBlocksSpec_failure decode image width count extent
  change mapBlocksSpec decode image width count = .error failure at run
  rw [run] at held
  exact held

/-- Actual slot-read guarantees exclude every production mapper error. This
    concludes success and retains the compact output tree, without expansion. -/
theorem mapBlocks_exists_of_windows {α ε : Type} (decode : ByteImage → Except ε α) (image : ByteImage)
    (width count : Nat) (extent : image.size = width * count)
    (windows : BlockWindowsSucceed decode image width count) :
    ∃ tree, mapBlocks decode image width count = .ok tree := by
  cases run : mapBlocks decode image width count with
  | ok tree => exact ⟨tree,rfl⟩
  | error failure =>
    obtain ⟨slot,inside,part,partSize,bytes,failed⟩ := mapBlocks_failure decode image width count extent failure run
    obtain ⟨value,decoded⟩ := windows slot inside part partSize bytes
    rw [decoded] at failed
    cases failed

namespace DecoderSlotControls

private def observeSlot (image : ByteImage) (width count slot : Nat) : Except Unit (Option (List (Option UInt8))) := do
  let tree ← mapBlocks (fun window => (pure window.toList : Except Unit _)) image width count
  pure (tree.get? slot)
private def unit : ByteImage := ByteImage.ofList [some 1,none,some 3]
private def cyclic : ByteImage := ⟨20,.periodic unit.tree (by decide) 7 20⟩
private def gcdUnit : ByteImage := ByteImage.ofList [some 1,some 2,some 3,some 4]
private def gcdCyclic : ByteImage := ⟨10,.periodic gcdUnit.tree (by decide) 5 10⟩
private def aligned : ByteImage := ⟨12,.periodic unit.tree (by decide) 1 12⟩
private def original : ByteImage := ⟨14,.source 14 (fun index => some (UInt8.ofNat (index + 1)))⟩
private def nested : ByteImage := ⟨12,.view (.view original.tree 1 13 (by decide)) 0 12 (by decide)⟩
private def joined : ByteImage := ⟨8,.append (.fill 4 (some 7)) (.fill 4 none)⟩

theorem periodic_prefix : observeSlot cyclic 2 10 0 = .ok (some [none,some 3]) := by trustIrReduce

theorem periodic_middle : observeSlot cyclic 2 10 5 = .ok (some [some 3,some 1]) := by trustIrReduce

theorem periodic_tail_and_outside :
    observeSlot cyclic 2 10 9 = .ok (some [none,some 3]) ∧ observeSlot cyclic 2 10 10 = .ok none := ⟨by trustIrReduce,by trustIrReduce⟩

theorem nontrivial_gcd_cycle : observeSlot gcdCyclic 2 5 3 = .ok (some [some 4,some 1]) := by trustIrReduce

theorem whole_period_width : observeSlot aligned 3 4 3 = .ok (some [none,some 3,some 1]) := by trustIrReduce

theorem ordinary_nested_views : observeSlot nested 2 6 4 = .ok (some [some 10,some 11]) := by trustIrReduce

theorem append_descent_and_padding :
    observeSlot joined 2 4 1 = .ok (some [some 7,some 7]) ∧ observeSlot joined 2 4 2 = .ok (some [none,none]) := ⟨by trustIrReduce,by trustIrReduce⟩

theorem zero_width_has_logical_slots :
    observeSlot empty 0 3 2 = .ok (some []) ∧ observeSlot empty 0 3 3 = .ok none := ⟨by trustIrReduce,by trustIrReduce⟩

theorem zero_count_ignores_callback_error :
    mapBlocks (fun _ => (.error 7 : Except Nat UInt8)) empty 0 0 =
      .ok (.dense (by decide) .nil) := by trustIrReduce

theorem nonempty_zero_width_forces_callback_error :
    mapBlocks (fun _ => (.error 7 : Except Nat UInt8)) empty 0 3 = .error 7 := by trustIrReduce

private def errorUnit : ByteImage := ByteImage.ofList [some 1,some 2,some 3]
private def errors : ByteImage := ⟨20,.periodic errorUnit.tree (by decide) 0 20⟩
private def refuse (image : ByteImage) : Except Nat Unit :=
  match image.get 0 with
  | none => .error 0
  | some byte => if byte == 2 then .error 2 else if byte == 3 then .error 3 else .ok ()

theorem periodic_errors_keep_left_to_right : mapBlocks refuse errors 2 10 = .error 3 := by trustIrReduce

/-- Exact extent is necessary for full-width custody: the underlying mapper
    itself permits clipped callbacks when its input is undersized. -/
theorem incorrect_extent_can_clip :
    observeSlot (ByteImage.fill 1 (some 7)) 2 1 0 = .ok (some [some 7]) := by trustIrReduce

theorem periodic_slot_has_actual_callback {α ε : Type} (decode : ByteImage → Except ε α)
    (tree : CompactArray.Tree α 10) (run : mapBlocks decode cyclic 2 10 = .ok tree)
    (value : α) (found : tree.get? 5 = some value) :
    BlockDecoded decode 2 (fun index => cyclic.get (10 + index)) value :=
  mapBlocks_decoded decode cyclic 2 10 rfl tree run 5 value (by decide) found

theorem ordinary_slot_has_actual_callback {α ε : Type} (decode : ByteImage → Except ε α)
    (tree : CompactArray.Tree α 6) (run : mapBlocks decode nested 2 6 = .ok tree)
    (value : α) (found : tree.get? 4 = some value) :
    BlockDecoded decode 2 (fun index => nested.get (8 + index)) value :=
  mapBlocks_decoded decode nested 2 6 rfl tree run 4 value (by decide) found

end DecoderSlotControls

namespace CanonicalWindowControls

private def original : ByteImage := ⟨8,.source 8 (fun index =>
  if index == 3 then none else some (UInt8.ofNat (index + 10)))⟩
private def nested : ByteImage :=
  ⟨3,.view (.view original.tree 1 6 (by decide)) 1 3 (by decide)⟩
private def joined : ByteImage := ⟨8,.append (.fill 4 (some 7)) (.fill 4 none)⟩
private def leftWindow : ByteImage := ⟨2,.view joined.tree 1 2 (by decide)⟩
private def rightWindow : ByteImage := ⟨2,.view joined.tree 5 2 (by decide)⟩
private def crossWindow : ByteImage := ⟨2,.view joined.tree 3 2 (by decide)⟩
private def observe (image : ByteImage) (width : Nat) :
    Except Unit (CompactArray.Tree (List (Option UInt8)) 1) :=
  mapBlocksSpec (fun window => pure window.toList) image width 1

theorem nested_views_preserve_source_and_padding :
    observe nested 3 = .ok (.uniform 1 [some 12,none,some 14]) := by trustIrReduce

theorem left_branch_window_preserves_bytes :
    observe leftWindow 2 = .ok (.uniform 1 [some 7,some 7]) := by trustIrReduce

theorem right_branch_window_preserves_absence :
    observe rightWindow 2 = .ok (.uniform 1 [none,none]) := by trustIrReduce

theorem crossing_window_retains_both_branches :
    observe crossWindow 2 = .ok (.uniform 1 [some 7,none]) := by trustIrReduce

theorem oversized_request_stays_clipped :
    observe (original.slice 7 5) 3 = .ok (.uniform 1 [some 17]) := by trustIrReduce

theorem empty_window_has_no_invented_bytes :
    observe ⟨0,.view original.tree 8 0 (by decide)⟩ 0 = .ok (.uniform 1 []) := by trustIrReduce

private def sourceTree {size : Nat} : Tree size → Bool
  | .source _ _ => true
  | _ => false
private def sourceView {size : Nat} : Tree size → Bool
  | .view source _ _ _ => sourceTree source
  | _ => false
private def isSourceView (image : ByteImage) : Bool := sourceView image.tree
private def sameBytesSource : ByteImage := ⟨2,.source 2 (fun _ => some 7)⟩

/-- Equal observed bytes do not justify equating arbitrary callback results.
    Certified repetition and an arbitrary source retain different constructors. -/
theorem byte_equality_does_not_equate_constructor_callbacks :
    (ByteImage.fill 2 (some 7)).toList = sameBytesSource.toList ∧
    mapBlocksSpec (fun window => (pure (isSourceView window) : Except Unit Bool))
      (ByteImage.fill 2 (some 7)) 2 1 = .ok (.uniform 1 false) ∧
    mapBlocksSpec (fun window => (pure (isSourceView window) : Except Unit Bool))
      sameBytesSource 2 1 = .ok (.uniform 1 true) := ⟨by trustIrReduce,by trustIrReduce,by trustIrReduce⟩

end CanonicalWindowControls

end TrustIr.ByteImage

namespace TrustIr.ByteImage.MapperFailureControls

private def read (part : ByteImage) : Except Nat UInt8 :=
  match part.get 0 with
  | none => .error 8
  | some value => if value == 255 then .error 7 else .ok value
private def source : ByteImage := ByteImage.ofList [some 1,some 255,some 1]

theorem visible_callback_failure : mapBlocks read source 1 3 = .error 7 := by trustIrReduce

theorem visible_failure_has_actual_slot : FailedSlots read source 1 3 7 :=
  mapBlocks_failure read source 1 3 rfl 7 visible_callback_failure

private def observed (image : ByteImage) (width count slot : Nat) : Except Nat (Option UInt8) := do
  let tree ← mapBlocks read image width count
  pure (tree.get? slot)

theorem hidden_template_error_is_not_forced :
    observed ((ByteImage.ofList [some 1,some 255]).tile 3 |>.slice 0 1) 1 1 0 = .ok (some 1) := by trustIrReduce

theorem zero_count_does_not_call_failing_callback :
    (mapBlocks (fun _ => (.error 7 : Except Nat UInt8)) ByteImage.empty 1 0).map (fun tree => tree.get? 0) = .ok none := by trustIrReduce

theorem zero_width_callback_failure_has_visible_slot :
    FailedSlots (fun _ => (.error 7 : Except Nat UInt8)) ByteImage.empty 0 3 7 :=
  mapBlocks_failure _ ByteImage.empty 0 3 rfl 7 (by trustIrReduce)

private def widthCheck (part : ByteImage) : Except Nat UInt8 := if part.size == 1 then .ok 0 else .error 9

theorem wrong_extent_has_no_complete_failure_window :
    mapBlocks widthCheck ByteImage.empty 1 1 = .error 9 ∧ ¬ FailedSlots widthCheck ByteImage.empty 1 1 9 := by
  refine ⟨by trustIrReduce,?_⟩
  rintro ⟨slot,inside,part,partSize,bytes,failed⟩
  simp [widthCheck,partSize] at failed

end TrustIr.ByteImage.MapperFailureControls
