module Optics

"""
    Optic{C,S,A,T,B,M}

A generic optic in a monoidal category `C`:
  - forward : S ⟶ M ⊗ A
  - backward: M ⊗ B ⟶ T
The residual/complement object `M` is existential at the level of the coend,
but we represent it explicitly here for simplicity.
"""
struct Optic{C,S,A,T,B,M}
    C        :: C        # base category
    forward  :: Any      # morphism in C: S → M ⊗ A
    backward :: Any      # morphism in C: M ⊗ B → T
end

# TODO: restrict from ANY using AJ morphism type(s)


# TODO: left_unitor() and right_unitor()
# TODO: inv()
# TODO: associator()
# TODO: tensor
# TODO: id

"""
    id_optic(C, S, T)

Identity optic on (S,T) in the optic category built over C.
"""
function id_optic(C, S, T)
    I = monoidal_unit(C) # e.g. from the monoidal interface

    # Structural (unitor) isos in C:
    ρS = right_unitor(C, S) # S ≅ I ⊗ S
    λT = left_unitor(C, T)  # I ⊗ T ≅ T

    forward  = inv(ρS) # S → I ⊗ S
    backward = λT      # I ⊗ T → T

    return Optic{typeof(C),S,S,T,T,typeof(I)}(C, forward, backward)
end


"""
    compose_optic(o2, o1)

Compose optics (o1 : (S,T)->(A,B)) and (o2 : (A,B)->(U,V))
to get an optic (S,T)->(U,V).
"""
function compose_optic(o2::Optic, o1::Optic)
    C = o1.C
    @assert C === o2.C  "Base categories must match" # TODO: does this have to hold...?

    # Aliases to make things moe clear
    l1, r1 = o1.forward, o1.backward
    l2, r2 = o2.forward, o2.backward
    M1, M2 = o1.M, o2.M  # Could store M as field or recompute from morph domains

    # Build residual / structural isos
    M  = tensor(C, M1, M2)  # M = M1 ⊗ M2

    # forward: S → M ⊗ U
    f1 = l1                          # S → M1 ⊗ A
    f2 = tensor(C, id(C,M1), l2)     # M1 ⊗ A → M1 ⊗ (M2 ⊗ U)
    α  = associator(C, M1, M2, o2.A) # (M1 ⊗ (M2 ⊗ U)) → (M1 ⊗ M2) ⊗ U
    forward  = α ∘ f2 ∘ f1

    # backward: M ⊗ V → T
    α⁻¹      = inv(associator(C, M1, M2, o2.B))
    b1       = α⁻¹                            # (M1 ⊗ M2) ⊗ V → M1 ⊗ (M2 ⊗ V)
    b2       = tensor(C, id(C,M1), r2)        # M1 ⊗ (M2 ⊗ V) → M1 ⊗ B
    backward = r1 ∘ b2 ∘ b1

    return Optic{typeof(C),o1.S,o1.A,o2.T,o2.B,typeof(M)}(C, forward, backward)
end


end # module Optics