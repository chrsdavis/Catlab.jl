module Optics

using Theories

"""
    Optic{S,A,T,B,M,L,R}

A generic optic in a (strict) symmetric monoidal category `C`.

It bundles:
  - objects  S, A, T, B, M :: ObExpr
  - forward  :: HomExpr (S ⟶ M ⊗ A)
  - backward :: Homexpr (M ⊗ B ⟶ T)

The residual/complement object `M` is existential at the level of the coend,
but we represent it explicitly here for simplicity.

We do not store the particular SMC theory C as a parameter; all the
structure comes from `Catlab.Theories` (⊗, ⋅, id, munit, …).
"""
struct Optic{S<:ObExpr,A<:ObExpr,T<:ObExpr,B<:ObExpr,M<:ObExpr,
             L<:HomExpr,R<:HomExpr}
    S::S
    A::A
    T::T
    B::B
    M::M
    forward::L    # morphism in C: S → M ⊗ A
    backward::R   # morphism in C: M ⊗ B → T
end


# TODO: left_unitor() and right_unitor()
# TODO: inv()
# TODO: associator()
# TODO: tensor
# TODO: id
# TODO: product
# TODO: diagonal_pairing

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


"""
    OpticCategory(C::MonoidalCategory)

Build the category whose objects are pairs (S,T) of objects in C and
whose morphisms are Optics over C.
"""
struct OpticCategory{C}
    base :: C
end

# Objects: maybe literally pairs?
struct OpticObject{S,T}
    source :: S
    target :: T
end

# TODO: catlab cat interface

# dom(o::Optic) = OpticObject(o.S, o.T)
# codom(o::Optic) = OpticObject(o.A, o.B)

# id(CO::OpticObject, OC::OpticCategory) =
#    id_optic(OC.base, CO.source, CO.target)

# compose(o2::Optic, o1::Optic, OC::OpticCategory) =
#    compose_optic(o2, o1)



include("Lens.jl")  # Lens specializaton

# TODO: LensOptic

"""
    lens_to_optic(L::Lens)

Convert a Lens (in a cartesian category) into a generic Optic.
"""
function lens_to_optic(L::Lens)
    C, S, A, T, B = L.C, L.S, L.A, L.T, L.B

    M = S

    prod      = product(C, S, A)          # S × A
    pair      = diagonal_pairing(C, S, A, L.view)   # ⟨id_S, view⟩ : S → S × A
    forward   = pair
    backward  = L.update                  # S × B → T

    return Optic{typeof(C),S,A,T,B,typeof(M)}(C, forward, backward)
end

# Convenience type alias
const LensOptic{C,S,A,T,B} = Optic{C,S,A,T,B,S}

end # module Optics