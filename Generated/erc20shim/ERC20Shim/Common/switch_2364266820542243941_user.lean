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

def A_switch_2364266820542243941 (s₀ s₉ : State) : Prop :=
  s₉.isOk ∧

  (--Case 1: No initial collision
    s₀.evm.hash_collision = false →
  (
    ( -- Case 1.1 : _3 = 0
      (-- Case 1.1.1: _7 = 1 (Reversion)
        preservesEvm s₀ s₉ ∧
        s₉.evm.reverted = true ∧
        s₉.evm.hash_collision = false
      )
      ∨
      (-- Case 1.1.2 _7 =/ 0 (Non Reversion)
        preservesEvm s₀ s₉ ∧
        s₉.evm.hash_collision = false
      )
    )
    ∨
    ( -- Case 1.2 : Default
      preservesEvm s₀ s₉ ∧
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

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000

lemma switch_2364266820542243941_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2364266820542243941_concrete_of_code s₀ s₉ →
  Spec A_switch_2364266820542243941 s₀ s₉ := by

  unfold switch_2364266820542243941_concrete_of_code A_switch_2364266820542243941

  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

  apply spec_eq

  rintro hasFuel ⟨s1, mapping1,
                  ⟨s2, if308,
                    ⟨s3, mapping2,
                      ⟨s4, update1,
                        ⟨s5, add,
                          ⟨s6, update2, code⟩⟩⟩⟩⟩⟩

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *
  have s0_ok : s₀.isOk := by aesop

  by_cases _3 : s₀["_3"]!! = 0

  · simp[_3] at code
    clear update2 add
    clr_varstore mapping1,
    clr_varstore mapping2,
    clr_varstore update1,
    unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping1
    unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping2
    unfold A_if_3989404597755436942 at if308
    unfold A_update_storage_value_offsett_uint256_to_uint256 at update1

    rw[←code] at hasFuel
    have s3_hasFuel: ¬❓ s3 := by
      apply not_isOutOfFuel_Spec update1 hasFuel
    have s2insert_hasFuel : ¬❓ (s2⟦"expr_4"↦s2["_6"]!! - (s2["var_value"]!!)⟧⟦"_15"↦s2["_4"]!!⟧) := by
      apply not_isOutOfFuel_Spec mapping2 s3_hasFuel
    have s2_hasFuel : ¬❓ s2 := by aesop

    have s1insert_hasFuel : ¬❓ (s1⟦"_6"↦sload s1.evm
                  (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                    (s1["_5"]!!)⟧["_6"]!!⟧⟦"_7"↦(decide
                (s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm (s1["_5"]!!)⟧["_6"]!!⟧["_6"]!! <
                  s1⟦"_6"↦sload s1.evm
                          (s1["_5"]!!)⟧⟦"var_fromBalance"↦s1⟦"_6"↦sload s1.evm
                            (s1["_5"]!!)⟧["_6"]!!⟧["var_value"]!!)).toUInt256⟧) := by
      apply not_isOutOfFuel_Spec if308 s2_hasFuel
    have s1_hasFuel : ¬❓ s1 := by aesop

    -- These all work, sorrys for speed
    apply Spec_ok_unfold (by sorry) (by sorry) at mapping1
    apply Spec_ok_unfold (by sorry) (by sorry) at if308
    apply Spec_ok_unfold (by sorry) (by sorry) at mapping2
    apply Spec_ok_unfold (by sorry) (by sorry) at update1

    clr_varstore if308,

#exit
  · clear update1 if308 mapping1 mapping2

    have : 0 ≠ s₀["_3"]!! := by aesop
    simp[this] at code
    clear this

    unfold A_checked_add_uint256 at add
    unfold A_update_storage_value_offsett_uint256_to_uint256 at update2
    clr_varstore,

    clr_spec at add
    clr_spec at update2
    sorry












end

end ERC20Shim.Common
