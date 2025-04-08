import Clear.ReasoningPrinciple

import Generated.erc20shim.ERC20Shim.abi_encode_uint256_to_uint256

import Generated.erc20shim.ERC20Shim.abi_encode_uint256_gen


namespace Generated.erc20shim.ERC20Shim

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities Generated.erc20shim ERC20Shim

def A_abi_encode_uint256 (tail : Identifier) (headStart value0 : Literal) (s₀ s₉ : State) : Prop :=
  --Case of no collision
  s₉.isOk ∧
  ( --Case 1 : no initial collision
    s₀.evm.hash_collision = false →
    (
      let s := s₀⟦tail ↦ headStart + 32⟧
      ( -- Case 1.1 : no collision in function
        preservesEvm s₀ s₉ ∧
        (Ok (EVMState.mstore s₀.evm headStart value0) s.store) = s₉ ∧
        s₉.evm.hash_collision = false
      )
      ∨
      -- Case 1.2 : Collision in function
    s₉.evm.hash_collision = true
    )
  )
  ∧
  (-- Case 2: existing initial collision
     s₀.evm.hash_collision = true →
    s₉.evm.hash_collision = true
  )

lemma abi_encode_uint256_abs_of_concrete {s₀ s₉ : State} {tail headStart value0} :
  Spec (abi_encode_uint256_concrete_of_code.1 tail headStart value0) s₀ s₉ →
  Spec (A_abi_encode_uint256 tail headStart value0) s₀ s₉ := by

  unfold abi_encode_uint256_concrete_of_code A_abi_encode_uint256
  rcases s₀ with ⟨evm₀, varstore₀⟩ | _ | _ <;> [simp only; aesop_spec; aesop_spec]
  apply spec_eq
  clr_funargs
  rintro hasFuel ⟨s1, encode, code⟩
  generalize s_inhabited_all :
  (Ok evm₀ Inhabited.default⟦"value0"↦value0⟧⟦"headStart"↦headStart⟧⟦"_1"↦32⟧) = s_inhabited at *
  have sinhab_ok : s_inhabited.isOk := by aesop

  generalize s0_all :
  (Ok evm₀ varstore₀) = s₀ at *

  unfold A_abi_encode_uint256_to_uint256 at encode
  clr_spec at encode

  clr_varstore,
  have s1_ok : s1.isOk := by aesop
  obtain ⟨s1_evm, ⟨s1_varstore, s1_all⟩⟩ := State_of_isOk s1_ok

  unfold reviveJump at code
  simp[s1_all, ←s0_all] at code

  obtain ⟨s1_ok, no_collision, collision⟩ := encode

  split_ands
  · aesop
  · by_cases s0_collision : s₀.evm.hash_collision = false
    · simp[s0_collision]
      simp at no_collision
      have : s_inhabited.evm.hash_collision = false := by aesop
      simp[this] at no_collision
      cases no_collision
      · left
        rw[←code]
        split_ands
        ·
          unfold lookup!
          simp
          have : preservesEvm s1 (Ok s1_evm (Finmap.insert tail (Finmap.lookup "tail" s1_varstore).get! varstore₀)) := by
            simp[s1_all]
            unfold preservesEvm
            aesop

          have : preservesEvm (s_inhabited⟦"tail"↦s_inhabited["headStart"]!! + (s_inhabited["_1"]!!)⟧) s1 := by aesop
          have sinhab__ok : (s_inhabited⟦"tail"↦s_inhabited["headStart"]!! + (s_inhabited["_1"]!!)⟧).isOk := by aesop
          have : preservesEvm s_inhabited (s_inhabited⟦"tail"↦s_inhabited["headStart"]!! + (s_inhabited["_1"]!!)⟧) := by
            simp[←s_inhabited_all]
            unfold preservesEvm State.insert lookup!
            aesop
          have : preservesEvm s₀ s_inhabited := by aesop
          have : preservesEvm s₀ (Ok s1_evm (Finmap.insert tail (Finmap.lookup "tail" s1_varstore).get! varstore₀)) := by
            apply preservesEvm_trans s1_ok
            · aesop
            · aesop
          aesop
        · aesop
        · aesop
      · aesop
    · aesop
  · aesop

end

end Generated.erc20shim.ERC20Shim
