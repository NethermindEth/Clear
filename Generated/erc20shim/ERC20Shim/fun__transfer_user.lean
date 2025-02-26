import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.Common.if_9141570808380448040
import Generated.erc20shim.ERC20Shim.abi_encode_tuple_address
import Generated.erc20shim.ERC20Shim.Common.if_2395397427938978657
import Generated.erc20shim.ERC20Shim.fun_update

import Generated.erc20shim.ERC20Shim.fun__transfer_gen

import Generated.erc20shim.ERC20Shim.Predicate


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities ERC20Shim.Common Generated.erc20shim ERC20Shim

def A_fun__transfer  (var_from var_to var_value : Literal) (s₀ s₉ : State) : Prop :=
  let from_addr := Address.ofUInt256 var_from
  let to_addr := Address.ofUInt256 var_to
  let transfer_value : UInt256 := var_value -- in wei
  s₉.isOk ∧
  (
    ∀ {erc20}, (IsERC20 erc20 s₀ ∧ s₀.evm.isEVMState ∧ s₀.evm.reverted = false) →
    -- Case: _transfer succeeds
    (
      let balances := update_balances erc20 from_addr to_addr transfer_value
      IsERC20 ({ erc20 with balances }) s₉ ∧ preservesEvm s₀ s₉ ∧
      s₉.evm.reverted = false ∧ s₉.evm.hash_collision = false
    )
    ∨
    -- Case: _transfer fails
    (
      IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧ s₉.evm.hash_collision = false ∧
      (to_addr = 0  ∨ balanceOf s₀.evm from_addr < transfer_value) ∧
      s₉.evm.reverted = true
    )
    -- Case: Hash collision
    ∨ s₉.evm.hash_collision = true
  )

lemma fun__transfer_abs_of_concrete {s₀ s₉ : State} { var_from var_to var_value} :
  Spec (fun__transfer_concrete_of_code.1  var_from var_to var_value) s₀ s₉ →
  Spec (A_fun__transfer  var_from var_to var_value) s₀ s₉ := by
  unfold fun__transfer_concrete_of_code A_fun__transfer
  sorry

end

end Generated.erc20shim.ERC20Shim
