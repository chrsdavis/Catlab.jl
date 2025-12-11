module Optics

using Theories

import Theories: HomExpr, ObExpr

"""
    Optic{S,A,T,B,M,L,R}

A generic optic in a (strict) symmetric monoidal category (SMC) `C`.

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

"""
    Optic(S, A, T, B, M, forward, backward)

Type-checked constructor: enforces the optic typing in the underlying SMC.
"""
function Optic(S::ObExpr, A::ObExpr, T::ObExpr, B::ObExpr, M::ObExpr,
               forward::HomExpr, backward::HomExpr)
    # Type checks in the monoidal category
    @assert dom(forward) == S
    @assert codom(forward) == (M ⊗ A)
    @assert dom(backward) == (M ⊗ B)
    @assert codom(backward) == T

    return Optic{typeof(S),typeof(A),typeof(T),typeof(B),typeof(M),
                 typeof(forward),typeof(backward)}(
        S, A, T, B, M, forward, backward
    )
end


# TODO: left_unitor() and right_unitor()
# TODO: inv()
# TODO: associator()
# TODO: tensor
# TODO: id
# TODO: product
# TODO: diagonal_pairing

"""
    id_optic(S, T)

Identity optic on the object pair (S,T) in the optic category.
The residual is the monoidal unit `I = munit()`.

Using strictness of the SMC, we implement the
isos `S ≅ I ⊗ S` and `I ⊗ T ≅ T` as identities.
"""
function id_optic(S::ObExpr, T::ObExpr)
    I = munit()

    # In a *strict* monoidal category we have I ⊗ S ≡ S, I ⊗ T ≡ T,
    # so we can take these to be identities (i.e., λ and ρ are ids).
    forward  = id(S)  # S ⟶ S  (≅ I ⊗ S)
    backward = id(T)  # T ⟶ T  (≅ I ⊗ T)

    return Optic(S, S, T, T, I, forward, backward)
end


"""
    compose_optic(o2, o1)

Compose optics
  o1 : (S,T₁) → (A,B)
  o2 : (A,T₂) → (U,B)

to obtain an optic
  (S,T₁) → (U,B)

The residuals M₁ and M₂ are combined as M = M₁ ⊗ M₂.

TODO:
We currently require that the “output B” objects agree syntactically;
this matches the typical lens-like case. But, we can generalize to the
full profunctor encoding later for different B₁,B₂.
"""
function compose_optic(o2::Optic, o1::Optic)
    # Ensure the middle matches
    @assert o1.A == o2.S  "Inner focus objects must match (A)."
    @assert o1.B == o2.B  "Update object B must currently agree for composition."

    # Aliases for readability
    S, A, U = o1.S, o1.A, o2.A
    T1, B, T2 = o1.T, o1.B, o2.T
    M1, M2 = o1.M, o2.M
    l1, l2 = o1.forward,  o2.forward
    r1, r2 = o1.backward, o2.backward

    # New residual is tensor of residuals
    M = M1 ⊗ M2

    # Forward:
    #   S ──l1──▶ M1 ⊗ A
    #        id(M1)⊗l2
    #     ───────────▶ M1 ⊗ (M2 ⊗ U)
    #
    # Using (strict) associativity, this is a morphism S → M ⊗ U.
    forward = (id(M1) ⊗ l2) ⋅ l1

    # Backward:
    #   M1 ⊗ (M2 ⊗ B) ── id(M1)⊗r2 ──▶ M1 ⊗ B ──r1──▶ T1
    #
    # Again, (strict) associativity lets us view the domain as (M1 ⊗ M2) ⊗ B.
    backward = r1 ⋅ (id(M1) ⊗ r2)

    return Optic(S, U, T1, B, M, forward, backward)
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