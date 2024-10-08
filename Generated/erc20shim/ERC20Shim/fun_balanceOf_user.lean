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
  intro hasFuel ⟨s, mapping, code⟩ erc20 is_erc20

  clr_varstore

  -- what we can get right now from mapping function
  unfold A_mapping_index_access_mapping_address_uint256_of_address at mapping
  simp at mapping
  clr_spec at mapping
  obtain ⟨preservesEvm, s_isOk, keccak⟩ := mapping  
  obtain ⟨evmₛ, varstoreₛ, s_eq_ok⟩ := State_of_isOk s_isOk

  -- simplify contract
  unfold reviveJump at code
  simp [s_eq_ok] at code
  rw [ ← State.insert_of_ok,  ← State.insert_of_ok, ← s_eq_ok ] at code
  clr_varstore

  -- get underlying Preserved from preservesEvm
  rw [ s_eq_ok, preservesEvm_of_insert, preservesEvm_of_insert ] at preservesEvm
  have Preserved := Preserved_of_preservesEvm_of_Ok preservesEvm

  -- have : Address.ofUInt256 var_account ∈ erc20.balances := sorry
  -- obtain ⟨address, hasAddress, hasBalance⟩ := is_erc20.hasBalance this
  -- obtain ⟨preserves, is_ok, lookup⟩ := keccak hasAddress
  -- obtain ⟨evmₛ, varstoreₛ, ok_state⟩ := State_of_isOk is_ok

  apply And.intro
  -- IsERC20 for the final state
  exact IsERC20_of_preservesEvm (by aesop) is_erc20

  rw [← code]
  apply And.intro
  -- preservesEvm s₀ s₉
  rw [ preservesEvm_of_insert' ]
  exact preservesEvm_of_preserved _ _ Preserved

  -- lookup balance
  clr_varstore
  by_cases mem : Address.ofUInt256 var_account ∈ erc20.balances
  -- there is such account in balances
  obtain ⟨address, has_address, balance⟩ := is_erc20.hasBalance mem
  have lookup := keccak has_address
  rw [lookup] at code ⊢
  rw [ Finmap.mem_lookup_iff (s := erc20.balances), ← Finmap.lookup_eq_some_iff
     , ← sload_eq_of_preserved Preserved
     ]
  have := State.get_evm_of_ok ▸ balance
  exact this

  -- there is *no* such account in balances
  rw [this]
    simp
    rw [hasBalance]
    have hPreserved : preserved (Ok evm varstore).evm evmₛ := by
      unfold preservesEvm at preserves_final
      aesop
    have : sload (Ok evm varstore).evm address = sload evmₛ address := by
      unfold EVMState.sload EVMState.lookupAccount
      rw [ preserves_account_map hPreserved
        , preserves_execution_env hPreserved
        ]
    rw [this]

end

end Generated.erc20shim.ERC20Shim
