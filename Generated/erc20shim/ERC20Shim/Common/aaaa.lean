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
            (isEVMState s₀⟦"_4"↦0⟧.evm → isEVMState s1.evm) ∧
              (∃ keccak,
                  Finmap.lookup [↑↑(Address.ofUInt256 (s₀["var_from"]!!)), 0] s1.evm.keccak_map = some keccak ∧
                    s1.store = s₀⟦"_4"↦0⟧⟦"_5"↦keccak⟧.store) ∧
                s1.evm.hash_collision = false ∨
          s1.evm.hash_collision = true) ∧
        (s₀⟦"_4"↦0⟧.evm.hash_collision = true → s1.evm.hash_collision = true))
  (if308 :
    s2.isOk ∧
      (s1⟦"_6"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                          (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
                      (s1⟦"_6"↦sload s1.evm
                                (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                        s1⟦"_6"↦sload s1.evm
                                (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                                  (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧.evm.hash_collision =
            false →
          preservesEvm
                (s1⟦"_6"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                          (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
                      (s1⟦"_6"↦sload s1.evm
                                (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                        s1⟦"_6"↦sload s1.evm
                                (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                                  (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧)
                s2 ∧
              s2.evm.reverted = true ∧
                s1⟦"_6"↦sload s1.evm
                            (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                              (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
                          (s1⟦"_6"↦sload s1.evm
                                    (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                                      (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                            s1⟦"_6"↦sload s1.evm
                                    (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                                      (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧["_7"]!! ≠
                  0 ∨
            preservesEvm
                  (s1⟦"_6"↦sload s1.evm
                          (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                            (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
                        (s1⟦"_6"↦sload s1.evm
                                  (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                          s1⟦"_6"↦sload s1.evm
                                  (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                                    (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧)
                  s2 ∧
                s1⟦"_6"↦sload s1.evm
                            (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                              (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
                          (s1⟦"_6"↦sload s1.evm
                                    (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                                      (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                            s1⟦"_6"↦sload s1.evm
                                    (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                                      (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧["_7"]!! =
                  0 ∨
              s2.evm.hash_collision = true) ∧
        (s1⟦"_6"↦sload s1.evm
                        (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                          (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
                      (s1⟦"_6"↦sload s1.evm
                                (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                        s1⟦"_6"↦sload s1.evm
                                (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                                  (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧.evm.hash_collision =
            true →
          s2.evm.hash_collision = true))
  (mapping2 :
    s3.isOk ∧
      (preservesEvm (s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧) s3 ∧
            (isEVMState s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧.evm → isEVMState s3.evm) ∧
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
        ((∃ slot value, preservesEvm (Ok (sstore s₀.evm slot value) s₀.store) s₉) ∧ s₉.evm.hash_collision = false ∨
            preservesEvm s₀ s₉ ∧ s₉.evm.hash_collision = false) ∨
          preservesEvm s₀ s₉ ∧ s₉.evm.hash_collision = false ∨ s₉.evm.hash_collision = true) ∧
      (s₀.evm.hash_collision = true → s₉.evm.hash_collision = true) := sorry











end

end ERC20Shim.Common
