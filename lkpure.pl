%%%%% Symbols %%%%%

:- op(490, fx, not).
:- op(500, xfy, and).
:- op(510, xfy, or).
:- op(520, xfy, implies).

%%%%% System LK %%%%%

% These rules define the System LK, with the implicit structural rules PL and PR
% (permutation).  A list of propositions is an ordered bag.  Weakening and contraction
% must be applied explicitly.

%%%%% Axiom %%%%%

rule(axiom, sequent([P], [P]), [], [], [P]) :-
    !.   % Optimisation: if axiom applies, stop trying other rules!


%%%%% Left logical rules %%%%%

rule(and_L1, sequent(Ps, Qs), [Prem1], [], [A and B]) :-
    select(A and B, Ps, NewPs),
    add_left(A, sequent(NewPs, Qs), Prem1).

rule(and_L2, sequent(Ps, Qs), [Prem1], [], [A and B]) :-
    select(A and B, Ps, NewPs),
    add_left(B, sequent(NewPs, Qs), Prem1).

rule(or_L, sequent(Ps, Qs), [Prem1, Prem2], [], [A or B]) :-
    select(A or B, Ps, NewPs),
    divide(NewPs, NewPsL, NewPsR),
    divide(Qs, NewQsL, NewQsR),
    add_left(A, sequent(NewPsL, NewQsL), Prem1),
    add_left(B, sequent(NewPsR, NewQsR), Prem2).

rule(implies_L, sequent(Ps, Qs), [Prem1, Prem2], [], [A implies B]) :-
    select(A implies B, Ps, NewPs),
    divide(NewPs, NewPsL, NewPsR),
    divide(Qs, NewQsL, NewQsR),
    add_right(A, sequent(NewPsL, NewQsL), Prem1),
    add_left(B, sequent(NewPsR, NewQsR), Prem2).

rule(not_L, sequent(Ps, Qs), [Prem1], [], [not A]) :-
    select(not A, Ps, NewPs),
    add_right(A, sequent(NewPs, Qs), Prem1).


%%%%% Right logical rules %%%%%

rule(or_R1, sequent(Ps, Qs), [Prem1], [], [A or B]) :-
    select(A or B, Qs, NewQs),
    add_right(A, sequent(Ps, NewQs), Prem1).

rule(or_R2, sequent(Ps, Qs), [Prem1], [], [A or B]) :-
    select(A or B, Qs, NewQs),
    add_right(B, sequent(Ps, NewQs), Prem1).

rule(and_R, sequent(Ps, Qs), [Prem1, Prem2], [], [A and B]) :-
    select(A and B, Qs, NewQs),
    divide(Ps, NewPsL, NewPsR),
    divide(NewQs, NewQsL, NewQsR),
    add_right(A, sequent(NewPsL, NewQsL), Prem1),
    add_right(B, sequent(NewPsR, NewQsR), Prem2).

rule(implies_R, sequent(Ps, Qs), [Prem], [], [A implies B]) :-
    select(A implies B, Qs, NewQs),
    add_left(A, sequent(Ps, NewQs), sequent(NewPs1, NewQs1)),
    add_right(B, sequent(NewPs1, NewQs1), Prem).

rule(not_R, sequent(Ps, Qs), [Prem1], [], [not A]) :-
    select(not A, Qs, NewQs),
    add_left(A, sequent(Ps, NewQs), Prem1).


%%%%% Structural rules %%%%%

rule(wl, sequent(Ps, Qs), [sequent(NewPs, Qs)], [], [P]) :-
    select(P, Ps, NewPs).

rule(wr, sequent(Ps, Qs), [sequent(Ps, NewQs)], [], [Q]) :-
    select(Q, Qs, NewQs).

rule(cl, sequent(Ps, Qs), [sequent(NewPs, Qs)], [], [P]) :-
    duplicate(P, Ps, NewPs).

rule(cr, sequent(Ps, Qs), [sequent(Ps, NewQs)], [], [Q]) :-
    duplicate(Q, Qs, NewQs).

% Helpers

duplicate(H, [H], [H,H]) :- !.
duplicate(H, [H|T], [H,H|T]).
duplicate(X, [H|T], [H|NewT]) :-
    duplicate(X, T, NewT).

divide([], [], []).
divide([H|T], [H|T1], T2) :-
    divide(T, T1, T2).
divide([H|T], T1, [H|T2]) :-
    divide(T, T1, T2).
