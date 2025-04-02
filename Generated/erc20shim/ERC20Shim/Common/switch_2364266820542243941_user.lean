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

lemma switch_2364266820542243941_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_2364266820542243941_concrete_of_code s₀ s₉ →
  Spec A_switch_2364266820542243941 s₀ s₉ := by

  unfold switch_2364266820542243941_concrete_of_code A_switch_2364266820542243941

  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]

  apply spec_eq

  rintro hasFuel ⟨s1, call_mapping1,
                  ⟨s2, call_308,
                    ⟨s3, call_mapping2,
                      ⟨s4, call_update1,
                        ⟨s5, call_add,
                          ⟨s6, call_update2, code⟩⟩⟩⟩⟩⟩

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold A_mapping_index_access_mapping_address_uint256_of_address at call_mapping1
  unfold lookup! State.insert at call_mapping1
  simp[←s0_all] at call_mapping1


end

end ERC20Shim.Common
