module Lens

using ..Optics
import ...Theories: HomExpr, ObExpr, dom, codom, id, compose, ⊗, ⋅, munit, pair, proj1, proj2

export Lens, optic_lens, lens, view, update, lens_laws

# TODO: wrap this as theories

"""
    Lens{S,A,T,B,V,U}

A lens in a cartesian category (where ⊗ = ×).

Fields:
  - view::V: S → A
  - update::U: S × B → T
"""
struct Lens{S<:ObExpr,A<:ObExpr,T<:ObExpr,B<:ObExpr,V<:HomExpr,U<:HomExpr}
    S::S
    A::A
    T::T
    B::B
    view::V
    update::U
    
    function Lens(S::ObExpr, A::ObExpr, T::ObExpr, B::ObExpr,
                  view::HomExpr, update::HomExpr)
        @assert dom(view) == S "View domain must be S"
        @assert codom(view) == A "View codomain must be A"
        @assert dom(update) == (S ⊗ B) "Update domain must be S×B"
        @assert codom(update) == T "Update codomain must be T"
        new{typeof(S),typeof(A),typeof(T),typeof(B),
            typeof(view),typeof(update)}(S,A,T,B,view,update)
    end
end

# Convenience constructor
lens(view::HomExpr, update::HomExpr) = Lens(dom(view), codom(view),
                                            codom(update), 
                                            right(dom(update)),
                                            view, update)

# Accessors
view(L::Lens) = L.view
update(L::Lens) = L.update

"""
    optic_lens(L::Lens)

Convert a lens to a generic optic in a cartesian category.
The residual M = S.
"""
function optic_lens(L::Lens)
    S, A, T, B = L.S, L.A, L.T, L.B
    M = S
    
    # Forward: S → S × A via ⟨id, view⟩
    forward = pair(id(S), L.view)
    
    # Backward: S × B → T via update
    backward = L.update
    
    Optics.Optic(S, A, T, B, M, forward, backward)
end

"""
    lens_optic(o::Optic)

Convert a generic optic to a lens if possible (requires M = S).
"""
function lens_optic(o::Optics.Optic)
    @assert o.M == o.S "Optic is not a lens (M ≠ S)"
    # Extract view: S → M×A → A via projection
    view = compose(o.forward, proj2(o.M, o.A))
    # Update is directly the backward map
    Lens(o.S, o.A, o.T, o.B, view, o.backward)
end

# Lens composition
function compose_lens(L1::Lens, L2::Lens)
    @assert L1.A == L2.S "Focus objects must match"
    @assert L1.B == L2.B "Update objects must match"
    
    # New view: S → A1 → A2
    new_view = compose(L1.view, L2.view)
    
    # New update: (S × B) → (A1 × B) → T
    new_update = compose(pair(compose(proj1(L1.S, L1.B), L1.view),
                             proj2(L1.S, L1.B)),
                        L2.update)
    
    Lens(L1.S, L2.A, L1.T, L1.B, new_view, new_update)
end

# Lens laws (verification)
function lens_laws(L::Lens)
    S, A, B = L.S, L.A, L.B
    
    # GetFirst: view after pairing with update gives original
    law1 = compose(pair(id(S), L.view), proj1(S, A)) == id(S)
    
    # PutGet: update with view doesn't change view
    law2 = compose(pair(id(S), L.view), L.update) == 
           compose(pair(id(S), L.view), proj1(S, B))
    
    # GetPut: setting with current view does nothing
    law3 = compose(pair(id(S), L.view), 
                   pair(proj1(S, B), 
                        compose(L.view, proj1(S, B)))) == id(S ⊗ B)
    
    (; getfirst=law1, putget=law2, getput=law3)
end

# Special lenses
function identity_lens(X::ObExpr)
    view = id(X)
    update = id(X ⊗ X)
    lens(view, update)
end

function constant_lens(X::ObExpr, Y::ObExpr)
    view = compose(terminal(X), id(Y))  # X → 1 → Y
    update = proj2(X, Y)  # X × Y → Y
    lens(view, update)
end

end # module Lens