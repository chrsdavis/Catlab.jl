module Prism

using ..Optics
import Catlab.Theories: HomExpr, ObExpr, dom, codom, id, compose, ⊗, ⋅, munit, 
                        copair, inj1, inj2, plus, zero

export Prism, optic_prism, prism, preview, review, prism_laws

# TODO: braiding

"""
    Prism{S,A,T,B,P,R}

A prism in a cocartesian category (where ⊗ = +).

Fields:
  - preview::P: S → A + B
  - review::R: B → T
"""
struct Prism{S<:ObExpr,A<:ObExpr,T<:ObExpr,B<:ObExpr,P<:HomExpr,R<:HomExpr}
    S::S
    A::A
    T::T
    B::B
    preview::P
    review::R
    
    function Prism(S::ObExpr, A::ObExpr, T::ObExpr, B::ObExpr,
                   preview::HomExpr, review::HomExpr)
        @assert dom(preview) == S "Preview domain must be S"
        @assert codom(preview) == (A ⊗ B) "Preview codomain must be A+B"
        @assert dom(review) == B "Review domain must be B"
        @assert codom(review) == T "Review codomain must be T"
        new{typeof(S),typeof(A),typeof(T),typeof(B),
            typeof(preview),typeof(review)}(S,A,T,B,preview,review)
    end
end

# Convenience constructor
prism(preview::HomExpr, review::HomExpr) = Prism(dom(preview), 
                                                 left(codom(preview)),
                                                 codom(review),
                                                 right(codom(preview)),
                                                 preview, review)

# Accessors
preview(P::Prism) = P.preview
review(P::Prism) = P.review

"""
    optic_prism(P::Prism)

Convert a prism to a generic optic in a cocartesian category.
The residual M = B.
"""
function optic_prism(P::Prism)
    S, A, T, B = P.S, P.A, P.T, P.B
    M = B
    
    # Forward: S → A + B → B + A via braiding
    forward = compose(P.preview, braid(A, B))
    
    # Backward: B + B → B → T via [id, id]; review
    backward = compose(copair(id(B), id(B)), P.review)
    
    Optics.Optic(S, A, T, B, M, forward, backward)
end

"""
    prism_optic(o::Optic)

Convert a generic optic to a prism if possible (requires M = B).
"""
function prism_optic(o::Optics.Optic)
    @assert o.M == o.B "Optic is not a prism (M ≠ B)"
    # Extract preview: S → B+A → A+B via braiding
    preview = compose(o.forward, braid(o.B, o.A))
    # Review is obtained from backward: B+B → T
    # We need B → T, which we get by B → B+B → T
    review = compose(inj1(zero(), o.B), o.backward)
    Prism(o.S, o.A, o.T, o.B, preview, review)
end

# Prism composition
function compose_prism(P1::Prism, P2::Prism)
    @assert P1.A == P2.S "Focus objects must match"
    @assert P1.B == P2.B "Review objects must match"
    
    # New preview: S → A1+B → A2+B
    new_preview = compose(P1.preview, 
                          copair(compose(inj1(P2.A, P2.B), P2.preview),
                                 inj2(P2.A, P2.B)))
    
    # New review: B → T1 → T2
    new_review = compose(P1.review, P2.review)
    
    Prism(P1.S, P2.A, P1.T, P1.B, new_preview, new_review)
end

# Prism laws
function prism_laws(P::Prism)
    S, A, B = P.S, P.A, P.B
    
    # Preview-Review law
    law1 = compose(P.review, P.preview) == 
           compose(inj2(A, B), P.preview)
    
    # Matching law
    law2 = compose(P.preview, copair(id(A), P.review)) == id(S)
    
    (; preview_review=law1, matching=law2)
end

# Special prisms
function identity_prism(X::ObExpr)
    preview = inj1(X, zero())  # X → X + 0
    review = id(zero())  # 0 → X (via zero morphism)
    prism(preview, review)
end

function tag_prism(X::ObExpr, tag::HomExpr)
    preview = copair(tag, id(X))  # X → A + X
    review = id(X)  # X → X
    prism(preview, review)
end

end # module Prism