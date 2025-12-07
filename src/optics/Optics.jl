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

end # module Optics