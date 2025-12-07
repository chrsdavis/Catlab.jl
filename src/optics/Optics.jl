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

end # module Optics