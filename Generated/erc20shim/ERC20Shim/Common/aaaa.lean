import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.Common.if_3989404597755436942
import Generated.erc20shim.ERC20Shim.abi_encode_address_uint256_uint256
import Generated.erc20shim.ERC20Shim.update_storage_value_offsett_uint256_to_uint256
import Generated.erc20shim.ERC20Shim.checked_add_uint256

import Generated.erc20shim.ERC20Shim.Common.switch_2364266820542243941_gen


namespace ERC20Shim.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

-- set_option maxHeartbeats 2500000
-- set_option maxRecDepth 1000

theorem ERC20Shim.Common.extracted_1 {s₉ : State} (evm₀ : EVM) (varstore₀ : VarStore) (s1 s2 s3 s4 : State)
  (hasFuel : ¬❓ s4) (s₀ : State) (s0_all : Ok evm₀ varstore₀ = s₀) (s0_ok : s₀.isOk) (_3 : s₀["_3"]!! = 0)
  (code : s4 = s₉) (s3_hasFuel : ¬❓ s3)
  (s2insert_hasFuel : ¬❓ (s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧)) (s2_hasFuel : ¬❓ s2)
  (s1insert_hasFuel :
    ¬❓
        (s1⟦"_6"↦sload s1.evm
                (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                  (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
              (s1⟦"_6"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                s1⟦"_6"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                          (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧))
  (s1_hasFuel : ¬❓ s1)
  (mapping1 :
    s1.isOk ∧
      (preservesEvm (s₀⟦"_4"↦0⟧) s1 ∧
            (isEVMState (s₀⟦"_4"↦0⟧.evm) → isEVMState s1.evm) ∧
              (∃ keccak,
                  Finmap.lookup [↑↑(Address.ofUInt256 (s₀["var_from"]!!)), 0] s1.evm.keccak_map = some keccak ∧
                    s1.store = s₀⟦"_4"↦0⟧⟦"_5"↦keccak⟧.store) ∧
                s1.evm.hash_collision = false ∨
          s1.evm.hash_collision = true) ∧
        (s₀⟦"_4"↦0⟧.evm.hash_collision = true → s1.evm.hash_collision = true))
  (if308 :
    s2.isOk ∧
      (s1⟦"_6"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"var_fromBalance"↦sload s1.evm
                      (s1["_5"]!!)⟧⟦"_7"↦(decide
                      (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256⟧.evm.hash_collision =
            false →
          preservesEvm
                (s1⟦"_6"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"var_fromBalance"↦sload s1.evm
                      (s1["_5"]!!)⟧⟦"_7"↦(decide (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256⟧)
                s2 ∧
              s2.evm.reverted = true ∧ (decide (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256 ≠ 0 ∨
            preservesEvm
                  (s1⟦"_6"↦sload s1.evm
                          (s1["_5"]!!)⟧⟦"var_fromBalance"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"_7"↦(decide (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256⟧)
                  s2 ∧
                (decide (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256 = 0 ∨
              s2.evm.hash_collision = true) ∧
        (s1⟦"_6"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"var_fromBalance"↦sload s1.evm
                      (s1["_5"]!!)⟧⟦"_7"↦(decide
                      (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256⟧.evm.hash_collision =
            true →
          s2.evm.hash_collision = true))
  (mapping2 :
    s3.isOk ∧
      (preservesEvm (s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧) s3 ∧
            (isEVMState (s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧).evm → isEVMState s3.evm) ∧
              (∃ keccak,
                  Finmap.lookup [↑↑(Address.ofUInt256 (s2["var_from"]!!)), s2["_4"]!!] s3.evm.keccak_map = some keccak ∧
                    s3.store = s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧⟦"_16"↦keccak⟧.store) ∧
                s3.evm.hash_collision = false ∨
          s3.evm.hash_collision = true) ∧
        (s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧.evm.hash_collision = true →
          s3.evm.hash_collision = true))
  (update1 :
    s4.isOk ∧
      (s3.evm.hash_collision = false →
          (let s := Ok (sstore s3.evm (s3["_16"]!!) (s3["expr_4"]!!)) s3.store;
            preservesEvm s s4) ∨
            s4.evm.hash_collision = true) ∧
        (s3.evm.hash_collision = true → s4.evm.hash_collision = true)) :
  s₉.isOk ∧
    (s₀.evm.hash_collision = false →
        (preservesEvm s₀ s₉ ∧ s₉.evm.reverted = true ∧ s₉.evm.hash_collision = false ∨
            preservesEvm s₀ s₉ ∧ s₉.evm.hash_collision = false) ∨
          preservesEvm s₀ s₉ ∧ s₉.evm.hash_collision = false ∨ s₉.evm.hash_collision = true) ∧
      (s₀.evm.hash_collision = true → s₉.evm.hash_collision = true) := by

      obtain ⟨s1_ok, ⟨s0s1_preserves, s0s1_state, s1_keccak, s1_no_collision⟩ | s1_collision, s0s1_colliion⟩ := mapping1

      · -- NO collision in mapping1
        obtain ⟨s1_evm, ⟨s1_varstore, s1_all⟩⟩ := State_of_isOk s1_ok
        by_cases _7 : (decide (sload s1.evm (s1["_5"]!!) < s1["var_value"]!!)).toUInt256 = 1

        · -- _7 = 1 (Reversion)

          simp[s1_no_collision, _7] at if308
          obtain ⟨s2_ok, ⟨s1s2_preserves, s2_reverted⟩| s2_collision⟩ := if308

          · -- no Collision in if308
            obtain ⟨s2_evm, ⟨s2_varstore, s2_all⟩⟩ := State_of_isOk s2_ok
            obtain ⟨s3_ok, ⟨s2s3_preserves, s2s3_state, s3_keccak, s3_no_collision⟩ | s3_collision, s2s3_colliion⟩ := mapping2

            · -- No collision in mapping2
              obtain ⟨s3_evm, ⟨s3_varstore, s3_all⟩⟩ := State_of_isOk s3_ok
              have s3__ok : (Ok (sstore s3.evm (s3["_16"]!!) (s3["expr_4"]!!)) s3.store).isOk := by aesop
              simp[s3_no_collision, _7] at update1
              obtain ⟨s4_ok, s3s4_preserves | s4_collision⟩ := update1

              · -- No collision in update1
                obtain ⟨s4_evm, ⟨s4_varstore, s4_all⟩⟩ := State_of_isOk s4_ok
                rw[←code]
                split_ands
                · aesop
                · intro s0_no_collison
                  left
                  left
                  split_ands
                  · apply preservesEvm_trans s2_ok
                    · apply preservesEvm_trans s1_ok
                      · aesop
                      · aesop
                    · apply preservesEvm_trans s3_ok
                      · aesop
                      · cases' s1_keccak with keccak1 keccak_value
                        have : s1["_5"]!! = keccak1 := by
                          unfold lookup!
                          simp[s1_all]
                          have : s1_varstore = s₀⟦"_4"↦0⟧⟦"_5"↦keccak1⟧.store := by aesop
                          rw[this]
                          unfold State.insert
                          aesop



                · aesop

              · -- Collision in update 1
                sorry --aesop

            · -- Collision in mapping 2
              sorry -- aesop

          · -- collision in if308
            sorry --aesop

        · -- _7 = 0 (No reversion)
          sorry

      · -- Collision in mapping1
        sorry --aesop














end

end ERC20Shim.Common
