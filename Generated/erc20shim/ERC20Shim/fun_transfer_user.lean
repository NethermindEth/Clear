import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.fun_msgSender
import Generated.erc20shim.ERC20Shim.fun__transfer

import Generated.erc20shim.ERC20Shim.fun_transfer_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_transfer (var : Identifier) (var_to var_value : Literal) (s₀ s₉ : State) : Prop :=
  let recipient := Address.ofUInt256 var_to
  let amount : UInt256 := var_value
  let sender := fun_msgSender
  (∀ {erc20}, (IsERC20 erc20 s₀ ∧ s₀.evm.isEVMState) →
  -- Transfer succeeds
    (let balances := update_balances erc20 sender recipient amount
     IsERC20 ({ erc20 with balances }) s₉ ∧ preservesEvm s₀ s₉ ∧
        s₉.evm.hash_collision = false
    )
    ∨
  -- Transfer Fails
    (IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧ s₉.evm.hash_collision = false
      --  ∧ (amount > callers balance ∨ recipient == zero address)
    )
    -- Hash Collision
    ∨ s₉.evm.hash_collision = true
  )



lemma fun_transfer_abs_of_concrete {s₀ s₉ : State} {var var_to var_value} :
  Spec (fun_transfer_concrete_of_code.1 var var_to var_value) s₀ s₉ →
  Spec (A_fun_transfer var var_to var_value) s₀ s₉ := by

  unfold fun_transfer_concrete_of_code A_fun_transfer
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  rintro hasFuel ⟨s, mapping, ⟨s', mapping', code⟩⟩
  clr_varstore,




end

end Generated.erc20shim.ERC20Shim
