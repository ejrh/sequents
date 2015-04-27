%%%%% Symbols %%%%%

:- op(490, fx, not).
:- op(500, xfy, and).
:- op(510, xfy, or).
:- op(520, xfy, implies).
:- op(480, xfy, oneof).

latex_name(not, '\\lnot').
latex_name(and, '\\land').
latex_name(or, '\\lor').
latex_name(implies, '\\to').
latex_name(oneof, '\\in').

latex_name(RN, S) :-
    \+integer(RN),
    split_string(RN, '_', '', [A,B]),
    atom_string(Atom, A),
    format(atom(S), '~l{}~w', [Atom,B]).

%%%%% Axiom %%%%%

rule(axiom, sequent(Ps, Qs), [], [], [P]) :-
    member(P, Ps),
    member(P, Qs),
    !.   % Optimisation: if the axiom applies, stop trying other rules!

%%%%% Left logical rules %%%%%

rule(and_L1, sequent(Ps, Qs), [Prem1], [], [A and B]) :-
    member(A and B, Ps),
    add_left(A, sequent(Ps, Qs), Prem1).

rule(and_L2, sequent(Ps, Qs), [Prem1], [], [A and B]) :-
    member(A and B, Ps),
    add_left(B, sequent(Ps, Qs), Prem1).

% Multi-and
rule(and_L/N, sequent(Ps, Qs), [Prem], [], [And]) :-
    member(And, Ps),
    And =.. [and|AndPreds],
    length(AndPreds, N),
    N > 2,
    member(Pred, AndPreds),
    add_left(Pred, sequent(Ps, Qs), Prem).

rule(or_L, sequent(Ps, Qs), [Prem1, Prem2], [], [A or B]) :-
    member(A or B, Ps),
    add_left(A, sequent(Ps, Qs), Prem1),
    add_left(B, sequent(Ps, Qs), Prem2).

% Multi-or
rule(or_L/N, sequent(Ps, Qs), Prems, [], [Or]) :-
    member(Or, Ps),
    Or =.. [or|OrPreds],
    length(OrPreds, N),
    N > 2,
    maplist(make_or_prem(sequent(Ps, Qs)), OrPreds, Prems).

make_or_prem(sequent(Ps, Qs), OrPred, sequent(NewPs, Qs)) :-
    add_left(OrPred, sequent(Ps, Qs), sequent(NewPs, Qs)).

% One-of
rule(oneof_L, sequent(Ps, Qs), [sequent([ValuesOr|Ps], Qs)], [], [oneof(F, Values)]) :-
    member(oneof(F, Values), Ps),
    findall(Prop, (member(V, Values), Prop = (F=V)), Props),
    ValuesOr =.. [or|Props].

% One-of
rule(oneof_not_L, sequent(Ps, Qs), [sequent(NewPs, Qs)], [], [(F=V), oneof(F, Values)]) :-
    member(oneof(F, Values), Ps),
    member((F=V), Ps),
    select(V, Values, Others),
    findall(not OtherProp, (member(OtherV, Others), OtherProp =(F=OtherV)), NotOtherProps),
    ((NotOtherProps = [NotOtherProp]) -> NotPred = NotOtherProp; NotPred =.. [and|NotOtherProps]),
    add_left(NotPred, sequent(Ps, Qs), sequent(NewPs, Qs)).

rule(implies_L, sequent(Ps, Qs), [Prem1, Prem2], [], [A implies B]) :-
    member(A implies B, Ps),
    add_right(A, sequent(Ps, Qs), Prem1),
    add_left(B, sequent(Ps, Qs), Prem2).

rule(not_L, sequent(Ps, Qs), [Prem1], [], [not A]) :-
    member(not A, Ps),
    add_right(A, sequent(Ps, Qs), Prem1).

%%%%% Right logical rules %%%%%

rule(or_R1, sequent(Ps, Qs), [Prem1], [], [A or B]) :-
    member(A or B, Qs),
    add_right(A, sequent(Ps, Qs), Prem1).

rule(or_R2, sequent(Ps, Qs), [Prem1], [], [A or B]) :-
    member(A or B, Qs),
    add_right(B, sequent(Ps, Qs), Prem1).

rule(and_R, sequent(Ps, Qs), [Prem1, Prem2], [], [A and B]) :-
    member(A and B, Qs),
    add_right(A, sequent(Ps, Qs), Prem1),
    add_right(B, sequent(Ps, Qs), Prem2).

rule(implies_R, sequent(Ps, Qs), [sequent(NewPs, NewQs)], [], [A implies B]) :-
    member(A implies B, Qs),
    \+((member(A, Ps), member(B, Qs))),
    append([A], Ps, NewPs),
    append([B], Qs, NewQs).

rule(not_R, sequent(Ps, Qs), [Prem1], [], [not A]) :-
    member(not A, Qs),
    add_left(A, sequent(Ps, Qs), Prem1).
