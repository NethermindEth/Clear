import Clear.ReasoningPrinciple

-- import Generated.erc20shim.ERC20Shim.mapping_index_access_mapping_address_uint256_of_address
import Generated.erc20shim.ERC20Shim.fun_balanceOf_gen

import Generated.erc20shim.ERC20Shim.Predicate

namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_fun_balanceOf (var : Identifier) (var_account : Literal) (s₀ s₉ : State) : Prop :=
  ∀ {erc20}, IsERC20 erc20 s₀ →
  let account := Address.ofUInt256 var_account
  IsERC20 erc20 s₉ ∧ preservesEvm s₀ s₉ ∧
  s₉[var]!! ∈ erc20.balances.lookup account

lemma fun_balanceOf_abs_of_concrete {s₀ s₉ : State} {var var_account} :
  Spec (fun_balanceOf_concrete_of_code.1 var var_account) s₀ s₉ →
  Spec (A_fun_balanceOf var var_account) s₀ s₉ := by
  unfold fun_balanceOf_concrete_of_code A_fun_balanceOf

  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  intro hasFuel ⟨s, keccak, code⟩ erc20 is_erc20

  clr_varstore

  unfold A_mapping_index_access_mapping_address_uint256_of_address at keccak
  simp at keccak
  clr_spec at keccak

  have : Address.ofUInt256 var_account ∈ erc20.balances := sorry
  obtain ⟨address, hasAddress, hasBalance⟩ := is_erc20.hasBalance this
  obtain ⟨preserves, is_ok, lookup⟩ := keccak hasAddress
  obtain ⟨evmₛ, varstareₛ, ok_state⟩ := State_of_isOk is_ok

  unfold reviveJump at code
  simp [ok_state] at code lookup

  rw [ ← State.insert_of_ok,  ← State.insert_of_ok, lookup ] at code
  clr_varstore

  have preserves_final : preservesEvm (Ok evm varstore) (Ok evmₛ varstore⟦var↦sload evmₛ address⟧) := by
    -- preservesEvm s₀ s₉ := by
    sorry
  apply And.intro
  rw [← code]
  exact IsERC20_of_preservesEvm preserves_final is_erc20

  apply And.intro
  rw [lookup, ok_state] at code
  rw [← code]

  unfold State.lookup!
  simp
  have : sload _ bal_addr = sload s.evm bal_addr := sload_eq_of_preservesEvm (by simp) is_ok preserves
  symm
  rw [ok_state] at this
  simp at this
  exact this

end

end Generated.erc20shim.ERC20Shim
