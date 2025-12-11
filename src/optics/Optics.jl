module Optics

using ...Theories
import ...Theories: HomExpr, ObExpr, dom, codom, id, compose, ⊗, ⋅, munit

export Optic, OpticCategory, OpticObject, dom, codom, id, compose,
       otimes_optic, parallel_optic, optic_lens, optic_prism,
       lens_to_optic, prism_to_optic


#--------------------------------------------------------------------
# Generic Optic Types
#--------------------------------------------------------------------

"""
    Optic{S,A,T,B,M,L,R}

A generic optic in a (strict) symmetric monoidal category (SMC) `C`.

Mathematically, an optic from (S,T) to (A,B) is an element of the coend:
  ∫ᴹ C(S, M⊗A) × C(M⊗B, T)

It bundles:
  - objects in the base category  S, A, T, B, M :: ObExpr
  - forward  :: L (S ⟶ M ⊗ A)
  - backward :: R (M ⊗ B ⟶ T)

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
    # Type checking in the base category
    @assert dom(forward) == S "Forward domain mismatch"
    @assert codom(forward) == (M ⊗ A) "Forward codomain mismatch"
    @assert dom(backward) == (M ⊗ B) "Backward domain mismatch"
    @assert codom(backward) == T "Backward codomain mismatch"

    return Optic{typeof(S),typeof(A),typeof(T),typeof(B),typeof(M),
                 typeof(forward),typeof(backward)}(
        S, A, T, B, M, forward, backward
    )
end

# TODO: product
# TODO: diagonal_pairing

#--------------------------------------------------------------------
# Optic Category Structure
#--------------------------------------------------------------------

struct OpticObject{S,T}
    source :: S
    target :: T
end

Base.show(io::IO, obj::OpticObject) = print(io, "($(obj.S), $(obj.T))")

# Domain and codomain for optics (S,T) → (A,B)
dom(o::Optic) = OpticObject(o.S, o.T)
codom(o::Optic) = OpticObject(o.A, o.B)

"""
    id_optic(S, T)

Identity optic on the object pair (S,T) in the optic category.
The residual is the monoidal unit `I = munit()`.

Using strictness of the SMC, we implement the
isos `S ≅ I ⊗ S` and `I ⊗ T ≅ T` as identities, and thus
don't need to deal with unitors or associators.
"""
function id_optic(S::ObExpr, T::ObExpr)
    I = munit()

    # In a *strict* monoidal category we have I ⊗ S ≡ S, I ⊗ T ≡ T,
    # so we can take these to be identities (i.e., λ and ρ are ids).
    forward  = id(S)  # S ⟶ I ⊗ S (≅ S)
    backward = id(T)  # I ⊗ T ≅ T

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
    # Check compatibility of foci
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

    # Forward: S → M1⊗A → M1⊗(M2⊗U) ≅ (M1⊗M2)⊗U
    # Using (strict) associativity, this is a morphism S → M ⊗ U.
    forward = compose(l1, id(M1) ⊗ l2)

    # Backward: (M1⊗M2)⊗B ≅ M1⊗(M2⊗B) → M1⊗B → T1
    # Again, (strict) associativity lets us view the domain as (M1 ⊗ M2) ⊗ B.
    backward = compose(id(M1) ⊗ r2, r1)

    return Optic(S, U, T1, B, M, forward, backward)
end

# Monoidal product of optics
function otimes_optic(o1::Optic, o2::Optic)
    S1, A1, T1, B1, M1 = o1.S, o1.A, o1.T, o1.B, o1.M
    S2, A2, T2, B2, M2 = o2.S, o2.A, o2.T, o2.B, o2.M
    
    M = M1 ⊗ M2
    
    # Forward: (S1⊗S2) → (M1⊗A1)⊗(M2⊗A2) ≅ (M1⊗M2)⊗(A1⊗A2)
    forward = compose(braid(S1, S2), 
                      o1.forward ⊗ o2.forward,
                      braid(M1 ⊗ A1, M2 ⊗ A2))
    
    # Backward: (M1⊗M2)⊗(B1⊗B2) ≅ (M1⊗B1)⊗(M2⊗B2) → T1⊗T2
    backward = compose(braid(M ⊗ B1, B2),
                       o1.backward ⊗ o2.backward)
    
    Optic(S1 ⊗ S2, A1 ⊗ A2, T1 ⊗ T2, B1 ⊗ B2, M, forward, backward)
end

#-------------------------------------------------------------------------------
# Optic Category
#-------------------------------------------------------------------------------

"""
    OpticCategory(C::SymmetricMonoidalCategory)

Build the category whose objects are pairs (S,T) of objects in C and
whose morphisms are Optics over C.
"""
struct OpticCategory{C} <: Category
    base :: C
end

Base.show(io::IO, OC::OpticCategory) = print(io, "OpticCategory($(OC.base))")

# Category interface
ob(OC::OpticCategory, pair::Tuple) = OpticObject(pair...)
hom(OC::OpticCategory, o::Optic) = o

# Identity and composition in the optic category
id(OC::OpticCategory, X::OpticObject) = id_optic(X.S, X.T)
compose(OC::OpticCategory, g::Optic, f::Optic) = compose_optic(g, f)

#-------------------------------------------------------------------------------
# Convenience Constructors
#-------------------------------------------------------------------------------

"""
    optic(forward::HomExpr, backward::HomExpr)

Creates an optic from explicit forward and backward maps.
Inferred types: S = dom(forward), A = right factor of codom(forward),
T = codom(backward), B = right factor of dom(backward),
M = left factor of both.
"""
function optic(forward::HomExpr, backward::HomExpr)
    S = dom(forward)
    MA = codom(forward)
    M = left(MA)
    A = right(MA)
    
    MB = dom(backward)
    @assert left(MB) == M "Residual M doesn't match"
    B = right(MB)
    T = codom(backward)
    
    Optic(S, A, T, B, M, forward, backward)
end

# TODO: Need helper to extract left/right factor
# Helper functions to extract left/right factors (simplified)
left(expr::ObExpr) = expr  # In actual implementation, need to parse ⊗
right(expr::ObExpr) = expr

#-------------------------------------------------------------------------------
# Special Optics
#-------------------------------------------------------------------------------

# TODO: add more

# Reindexing optic (adapter)
function reindex_optic(f::HomExpr, g::HomExpr)
    S = dom(f)
    A = codom(f)
    T = codom(g)
    B = dom(g)
    M = munit()
    
    forward = f  # S → A ≅ I⊗A
    backward = g # B → T ≅ I⊗B → T (with unitor)
    
    Optic(S, A, T, B, M, forward, backward)
end

end # module Optics