import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address

import Generated.erc20shim.ERC20Shim.Common.if_9141570808380448040_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_if_9141570808380448040 (s₀ s₉ : State) : Prop :=

  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
  (
    ( -- Case 1.1 : Reversion
      preservesEvm s₀ s₉ ∧
      s₉.evm.reverted = true  ∧
      s₀["_3"]!! ≠ 0 ∧
      s₉.evm.hash_collision = false
    )
    ∨
    ( -- Case 1.2 : No Reversion
      preservesEvm s₀ s₉ ∧
      s₀["_3"]!! = 0 ∧
      s₉.evm.hash_collision = false
    )
    ∨
      -- Case 1.3 : Collision in function
      s₉.evm.hash_collision = true
  )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

set_option maxHeartbeats 400000

lemma if_9141570808380448040_abs_of_concrete {s₀ s₉ : State} :
  Spec if_9141570808380448040_concrete_of_code s₀ s₉ →
  Spec A_if_9141570808380448040 s₀ s₉ := by
  unfold if_9141570808380448040_concrete_of_code A_if_9141570808380448040

  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  rintro hasFuel ⟨s, call_encode_tuple, code⟩

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold A_abi_encode_tuple_address at call_encode_tuple

  rw [←s0_all] at call_encode_tuple
  rw [insert_of_ok] at call_encode_tuple
  rw [insert_of_ok] at call_encode_tuple
  rw [insert_of_ok] at call_encode_tuple
  simp at call_encode_tuple
  unfold setEvm at call_encode_tuple
  unfold multifill at call_encode_tuple
  simp at call_encode_tuple
  rw [insert_of_ok] at call_encode_tuple
  rw [insert_of_ok] at call_encode_tuple
  rw [insert_of_ok] at call_encode_tuple
  unfold lookup! at call_encode_tuple
  simp at call_encode_tuple

  generalize s0__all : (Ok
            (mstore evm₀
              (Finmap.lookup "_5"
                  (Finmap.insert "_6" (Fin.shiftLeft 1264811663 225)
                    (Finmap.insert "_5" (EVMState.mload evm₀ 64)
                      (Finmap.insert "_4" 64 (Finmap.insert "expr_1" 0 varstore₀))))).get!
              (Fin.shiftLeft 1264811663 225))
            (Finmap.insert "_8"
              ((Finmap.lookup "_5"
                    (Finmap.insert "_7" 4
                      (Finmap.insert "_6" (Fin.shiftLeft 1264811663 225)
                        (Finmap.insert "_5" (EVMState.mload evm₀ 64)
                          (Finmap.insert "_4" 64 (Finmap.insert "expr_1" 0 varstore₀)))))).get! +
                4)
              (Finmap.insert "_7" 4
                (Finmap.insert "_6" (Fin.shiftLeft 1264811663 225)
                  (Finmap.insert "_5" (EVMState.mload evm₀ 64) (Finmap.insert "_4" 64 (Finmap.insert "expr_1" 0 varstore₀))))))) = s0_ at *

  have : preservesEvm s₀ s0_ := by
            have : Preserved evm₀ (mstore evm₀
          (Finmap.lookup "_5"
              (Finmap.insert "_6" (Fin.shiftLeft 1264811663 225)
                (Finmap.insert "_5" (EVMState.mload evm₀ 64)
                  (Finmap.insert "_4" 64 (Finmap.insert "expr_1" 0 varstore₀))))).get!
          (Fin.shiftLeft 1264811663 225)) := by
              apply mstore_preserved
            aesop

  have s0__ok : s0_.isOk := by aesop

  by_cases _3_var : s₀["_3"]!! ≠ 0
  · simp [_3_var] at code
    clr_spec at call_encode_tuple
    obtain ⟨s_ok, ⟨s_preserves_evm, encode, s_no_collision⟩ | s_collision ⟩ := call_encode_tuple
    · obtain ⟨s_evm, ⟨s_varstore, s_all⟩⟩ := State_of_isOk s_ok

      have s0_s_preservesEvm : preservesEvm s₀ s := by
                apply preservesEvm_trans s0__ok
                aesop
                aesop

      have s_s9_preservesEvm : preservesEvm s s₉ := by
        have : Preserved s.evm s₉.evm := by
          have : (s.evm.account_map    = s₉.evm.account_map ∧
                          s.evm.hash_collision = s₉.evm.hash_collision ∧
                          s.evm.execution_env  = s₉.evm.execution_env ∧
                          s.evm.keccak_map     ≤ s₉.evm.keccak_map) := by
                          rw[←code]
                          unfold setEvm
                          simp [s_all]
                          rw [insert_of_ok]
                          unfold evm_revert
                          unfold evm_return
                          simp

          simp [Preserved_def]
          aesop
        aesop

      unfold setEvm at code
      simp [s_all] at code
      split_ands
      · aesop
      · intro s0_no_collision
        left
        split_ands
        · apply preservesEvm_trans s_ok
          · aesop
          · aesop
        · aesop
        · aesop
        · rw[←code]
          simp only [evm_insert, get_evm_of_ok]
          unfold evm_revert
          simp only
          unfold evm_return
          simp only
          rw [s_all] at s_no_collision
          simp only [get_evm_of_ok] at s_no_collision
          exact s_no_collision

      · -- collision at s0
        intro s0_colliision

        have s0_s_preservesEvm : preservesEvm s₀ s := by
                apply preservesEvm_trans s0__ok
                aesop
                aesop

        have s_s9_preservesEvm : preservesEvm s s₉ := by
          have : Preserved s.evm s₉.evm := by
            have : (s.evm.account_map    = s₉.evm.account_map ∧
                            s.evm.hash_collision = s₉.evm.hash_collision ∧
                            s.evm.execution_env  = s₉.evm.execution_env ∧
                            s.evm.keccak_map     ≤ s₉.evm.keccak_map) := by
                            rw[←code]
                            simp [s_all]
                            rw [insert_of_ok]
                            unfold evm_revert
                            unfold evm_return
                            simp

            simp [Preserved_def]
            aesop
          aesop

        have this : preservesEvm s₀ s₉ := by
          apply preservesEvm_trans s_ok
          all_goals aesop

        clr_varstore,
        simp [←s0_all, ←code] at this
        unfold evm_revert at this
        unfold preservesEvm at this
        unfold lookup! at this
        unfold State.insert at this
        simp at this

        generalize updated_evm : ({
                      account_map := s_evm.account_map,
                      machine_state := s_evm.machine_state,
                      execution_env := s_evm.execution_env,
                      keccak_map := s_evm.keccak_map,
                      keccak_range := s_evm.keccak_range,
                      used_range := s_evm.used_range,
                      blocks := s_evm.blocks,
                      hash_collision := s_evm.hash_collision,
                      reverted := true
                    }: EVMState) = upd_evm

        have : upd_evm.hash_collision = evm₀.hash_collision := by
          simp [Preserved_def] at this
          unfold evm_return at this
          aesop

        aesop
    aesop
  · aesop

end

end ERC20Shim.Common
